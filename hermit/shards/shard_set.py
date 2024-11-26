import bson
import os
import textwrap
from hermit import shamir_share
from prompt_toolkit import print_formatted_text, HTML
from hermit.config import HermitConfig
from hermit.errors import HermitError
from typing import List, Dict, Optional
from mnemonic import Mnemonic
from .interface import ShardWordUserInterface
from .shard import Shard
from hermit.rng import RandomGenerator


RNG = RandomGenerator()
shamir_share.set_random_bytes(RNG.random)

def check_satisfaction_criteria(shards):
    """check_satisfaction_criteria(shards)

    Given an interable collection of shards, this function determines
    both which of the group member thresholds have been satisfied by
    the selecton and whether the overall group threshold has been met.
    This function returns a pair of elements, the first item is a boolean
    representing whether or not the overall group threshold is met and the
    second is a set of group indexes whose thresholds have been met.
    """

    groups = {}
    filled = set()
    satisfied = False

    for s in shards:
        (group_idx, _) = s.shard_id
        if not group_idx in groups:
            groups[group_idx] = 0
        groups[group_idx] += 1
        if groups[group_idx] >= s.member_threshold:
            filled.add(group_idx)
        satisfied = (len(filled) >= s.group_threshold)

    return (satisfied, filled)


class ShardSet(object):
    def __init__(self,
                 interface: Optional[ShardWordUserInterface] = None) -> None:
        self.shards: Dict = {}
        self._shards_loaded = False
        self.config = HermitConfig.load()
        if interface is None:
            self.interface = ShardWordUserInterface()
        else:
            self.interface = interface

    def _ensure_shards(self, shards_expected: bool = True) -> None:
        if not self._shards_loaded:
            bdata = None

            # If the shards dont exist at the place where they
            # are expected to by, try to restore them with the externally
            # configured getPersistedShards command.
            if not os.path.exists(self.config.shards_file):
                try:
                    os.system(self.config.commands['getPersistedShards'])
                except TypeError:
                    pass

            # If for some reason the persistence layer failed to  create the
            # the shards file, we assume that we just need to initialize
            # it as an empty bson object.
            if not os.path.exists(self.config.shards_file) or os.stat(self.config.shards_file).st_size == 0:
                with open(self.config.shards_file, 'wb') as f:
                    f.write(bson.dumps({}))

            with open(self.config.shards_file, 'rb') as f:
                bdata = bson.loads(f.read())

            for name, shard_bytes in bdata.items():
                self.shards[name] = Shard(
                    name, shamir_share.mnemonic_from_bytes(shard_bytes))

            self._shards_loaded = True

        if len(self.shards) == 0 and shards_expected:
            raise HermitError("No shards found.  Create some by entering 'shards' mode.")

    def initialize_file(self) -> None:
        if self.interface.confirm_initialize_file():
            with open(self.config.shards_file, 'wb') as f:
                f.write(bson.dumps({}))

    def to_bytes(self):
        data = {name: shard.to_bytes()
                for (name, shard) in self.shards.items()}
        return bson.dumps(data)

    def save(self) -> None:
        with open(self.config.shards_file, 'wb') as f:
            f.write(self.to_bytes())

    def _needed_entropy_bytes(self, group_threshold, groups):
        # Every group needs a couple of random bytes for the identifier
        identifiers = 1

        digests = 0

        # If the group threshold is greater than 1, the group has a digest in it
        # somewhere, which reduces the amount of random bytes that it needs.
        if group_threshold > 1:
            digests += 1

        # The polynomial for the group secret share has its threshold
        # independent parameters, but one of them is effectively the master
        # secret, so we dont count it here.
        degrees_of_freedom = group_threshold - 1

        for (threshold, _) in groups:
            # For the member shares, if the threshold is more than 1, there is
            # another digest.
            if threshold > 1:
                digests += 1
            # And again, for the member shares, the polynomial has the same
            # number of independent coefficients as the threshold, but one of
            # them is actually the group secret, so we dont count it here.
            degrees_of_freedom += threshold - 1

        return (degrees_of_freedom * 32) - (digests * 4) + (identifiers*2)

    def create_share_from_wallet_words(self, wallet_words=None):
        (group_threshold, groups) = self.interface.enter_group_information()
        if wallet_words is None:
            wallet_words = self.interface.enter_wallet_words()
        mnemonic = Mnemonic('english')
        secret = mnemonic.to_entropy(wallet_words)

        RNG.ensure_bytes(self._needed_entropy_bytes(group_threshold, groups))
        mnemonics = shamir_share.generate_mnemonics(
            group_threshold, groups, secret)

        self._import_share_mnemonic_groups(mnemonics)

    def create_random_share(self):
        (group_threshold, groups) = self.interface.enter_group_information()

        RNG.ensure_bytes(self._needed_entropy_bytes(
            group_threshold, groups) + 32)
        mnemonics = shamir_share.generate_mnemonics_random(
            group_threshold, groups, strength_bits=256)
        self._import_share_mnemonic_groups(mnemonics)

    def _import_share_mnemonic_groups(self, mnemonic_groups: List[List[str]]) -> None:
        for group in mnemonic_groups:
            for mnemonic in group:
                (share_id, _, group_index, group_threshold, groups, member_identifier,
                 member_threshold, _) = shamir_share.decode_mnemonic(mnemonic)
                name = self.interface.get_name_for_shard(
                    share_id, group_index, group_threshold, groups, member_identifier, member_threshold, self.shards)
                password = self.interface.confirm_password()
                shard = Shard(name, shamir_share.encrypt_mnemonic(
                    mnemonic, password), self.interface)
                self.shards[name] = shard

    def wallet_words(self) -> str:
        # This is a little retrograde, but at the moment, the walled code wants
        # a set of wallet words to start with. Here we are using the master
        # secret from the shamir share as the entropy that feeds into the the
        # wallet words - this is the only way that I can see that the shamir
        # code is going to be compatible with bip39 wallets.
        seed = self.secret_seed()
        mnemonic = Mnemonic('english')
        return mnemonic.to_mnemonic(seed)

    def secret_seed(self) -> bytes:
        self._ensure_shards()

        selected : Dict[str, Shard]= {}
        selected_share_id : Optional[int]= None
        selected_shard_ids : set = set()
        selected_shards : set = set()

        satisfied = False
        filled_groups = set()

        while not satisfied:
            shards = [shard
                      for (name, shard)
                      in self.shards.items()
                      if (name not in selected)
                      and (selected_share_id is None or shard.share_id == selected_share_id)
                      and (shard.shard_id not in selected_shard_ids)
                      and (shard.group_id not in filled_groups)
                      ]

            if selected_share_id is not None:
                (enough_shards,_) = check_satisfaction_criteria(selected_shards.union(shards))
                if not enough_shards:
                    print([shard.to_str() for shard in shards])
                    raise HermitError("There are not enough shards available to unlock this secret.")

            name = None

            try:
                name = self.interface.choose_shard(shards)
            except:
                # catch end-of-input style exceptions
                pass

            if name is None:
                raise HermitError("Not enough shards selected to unlock secret.")

            shard = self.shards[name]
            if selected_share_id is None:
                selected_share_id = shard.share_id

            selected_shard_ids.add(shard.shard_id)
            selected[name] = shard.words()
            selected_shards.add(shard)

            (satisfied, filled_groups) = check_satisfaction_criteria(selected_shards)

        unlocked_mnemonics = list(selected.values())
        return shamir_share.combine_mnemonics(unlocked_mnemonics)

    def reveal_shard(self, shard_name: str) -> None:
        self._ensure_shards(shards_expected=True)
        shard = self.shards[shard_name]
        words = shard.encrypted_mnemonic
        print_formatted_text(HTML(
            "Encrypted SLIP39 phrase for shard <i>{}</i>:\n".format(shard_name)))
        print_formatted_text("\n".join(textwrap.wrap(words, 80)), "\n")
        self.interface.get_line_then_clear()

    def reveal_wallet_words(self) -> None:
        self._ensure_shards(shards_expected=True)

        words = self.wallet_words()
        print_formatted_text(
            "- WARNING -\n" +
            "The wallet words for this secret are about to be revealed.\n"
        )
        self.interface.get_line_then_clear()

        print_formatted_text("\n".join(textwrap.wrap(words, 80)), "\n")

        self.interface.get_line_then_clear()

    def reshard(self) -> None:
        self.create_share_from_wallet_words(self.wallet_words())

    def qr_shard(self, shard_name: str) -> bytes:
        self._ensure_shards(shards_expected=True)
        shard = self.shards[shard_name]
        return shard.to_qr_bson()

    def import_shard_qr(self, name: str, shard_data: bytes) -> None:
        if name in self.shards:
            err_msg = ("Shard exists. If you need to replace it, "
                       + "delete it first.")
            raise HermitError(err_msg)

        shard_dict = bson.loads(shard_data)
        old_name = list(shard_dict.keys())[0]
        print_formatted_text(
            "Importing shard '{}' from qr code as shard '{}'".format(old_name, name))
        shard = Shard(name, None, interface=self.interface)
        shard.from_bytes(shard_dict[old_name])

        self.shards[name] = shard

    def input_shard_words(self, name) -> None:
        self._ensure_shards(shards_expected=False)

        if name in self.shards:
            err_msg = ("Shard exists. If you need to replace it, "
                       + "delete it first.")
            raise HermitError(err_msg)

        shard = Shard(name, None, interface=self.interface)
        shard.input()

        self.shards[name] = shard

    def copy_shard(self, original: str, copy: str) -> None:
        self._ensure_shards()
        if original not in self.shards:
            raise HermitError("Shard {} does not exist.".format(original))

        if copy in self.shards:
            err_msg = (
                "Shard {} exists. If you need to replace it, delete it first.".format(copy))
            raise HermitError(err_msg)

        original_shard = self.shards[original]
        copy_shard = Shard(
            copy, original_shard.encrypted_mnemonic, interface=self.interface)
        copy_shard.change_password()
        self.shards[copy] = copy_shard

    def clear_shards(self) -> None:
        self.shards = {}

    def wallet_words_shard(self, name: str) -> None:
        self._ensure_shards()
        return self.shards[name]

    def delete_shard(self, shard_name: str) -> None:
        self._ensure_shards()
        if self.interface.confirm_delete_shard(shard_name):
            del self.shards[shard_name]

    def list_shards(self) -> None:
        self._ensure_shards(shards_expected=False)
        if len(self.shards) > 0:
            for shard in self.shards.values():
                print("     {}".format(shard.to_str()))
        else:
            print("No shards.")

    def persist(self) -> None:
        # TODO: check to see that everything is saved
        os.system(self.config.commands['persistShards'])

    def backup(self) -> None:
        os.system(self.config.commands['backupShards'])

    def restore(self) -> None:
        os.system(self.config.commands['restoreBackup'])

    def reload(self) -> None:
        self.shards = {}
        self._shards_loaded = False
        self._ensure_shards()
