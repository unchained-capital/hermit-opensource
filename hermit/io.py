from datetime import datetime
from typing import Optional
from time import sleep

from prompt_toolkit import print_formatted_text
from prompt_toolkit.shortcuts.progress_bar.base import ProgressBar, ProgressBarCounter

from .errors import (
    HermitError,
    InvalidQRCodeSequence,
)
from .config import get_config
from .qr import (
    create_qr_sequence,
    detect_qrs_in_image,
    GenericReassembler,
)


def display_data_as_animated_qrs(data: str) -> None:
    io = get_io()
    io.display_data_as_animated_qrs(data)


def read_data_from_animated_qrs() -> Optional[str]:
    io = get_io()
    return io.read_data_from_animated_qrs()


_io = None


def get_io() -> "IO":
    global _io

    if _io is None:
        io_config = get_config().io
        _io = IO(io_config)

    return _io


class IO:
    def __init__(self, io_config):

        camera_mode = io_config.get("camera", "opencv")
        if camera_mode == "opencv":
            from .camera.opencv import OpenCVCamera

            self.camera = OpenCVCamera()
        elif camera_mode == "imageio":
            from .camera.imageio import ImageIOCamera

            self.camera = ImageIOCamera()
        else:
            raise HermitError(
                f"Invalid camera mode '{camera_mode}'.  Must be either 'opencv' or 'imageio'."
            )

        display_mode = io_config.get("display", "opencv")
        if display_mode == "opencv":
            from .display.opencv import OpenCVDisplay

            self.display = OpenCVDisplay(io_config)
        elif display_mode == "framebuffer":
            from .display.framebuffer import FrameBufferDisplay

            self.display = FrameBufferDisplay(io_config)
        elif display_mode == "ascii":
            from .display.ascii import ASCIIDisplay

            self.display = ASCIIDisplay(io_config)
        else:
            raise HermitError(
                f"Invalid display mode '{display_mode}'.  Must be one of 'opencv', 'framebuffer', or 'ascii'."
            )

    def display_data_as_animated_qrs(
        self, data: Optional[str] = None, base64_data: Optional[str] = None
    ) -> None:
        return self.display.animate_qrs(
            create_qr_sequence(data=data, base64_data=base64_data)
        )

    def read_data_from_animated_qrs(self, title: Optional[str] = None) -> Optional[str]:
        if title is None:
            title = "Scanning QR Codes..."

        with ProgressBar(title=title) as progress_bar:
            try:
                self.camera.open()
                self.display.setup_camera_display(title)
                self.reassembler = GenericReassembler()

                counter = ReassemblerCounter(progress_bar, self)
                progress_bar.counters.append(counter)

                for c in counter:
                    image = self.camera.get_image()
                    mirror, data = detect_qrs_in_image(image, box_width=20)

                    if not self.display.display_camera_image(mirror):
                        break

                    # Iterate through the identified QR codes and let the
                    # reassembler collect them.
                    for data_item in data:
                        if self.reassembler.collect(data_item):
                            c.advance()

                    # await asyncio.sleep(0.05)

            except InvalidQRCodeSequence as e:
                print_formatted_text(f"Invalid QR code sequence: {e}.")
                return None
            finally:
                self.display.teardown_camera_display()
                self.camera.close()

        return self.reassembler.decode()


class ReassemblerCounter(object):
    def __init__(self, progress_bar, io):
        self.start_time = datetime.now()
        self.progress_bar = progress_bar
        self.data = None
        self.current = 0
        self.label = ""
        self.remove_when_done = True
        self.done = False
        self.io = io

    def __next__(self):
        if self.io.reassembler.is_complete():
            self.done = True
            if self in self.progress_bar.counters:
                self.progress_bar.counters.remove(self)
            raise StopIteration
        else:
            return self

    def __iter__(self):
        return self

    def advance(self):
        self.current += 1
        self.progress_bar.invalidate()

    @property
    def total(self):
        return self.io.reassembler.total

    @property
    def percentage(self):
        if self.total is None:
            return 0
        else:
            return self.current * 100 / max(self.total, 1)

    @property
    def time_elapsed(self):
        """
        return how much time has been elapsed since the start.
        """
        return datetime.now() - self.start_time

    @property
    def time_left(self):
        """
        Timedelta representing the time left.
        """
        if self.total is None or not self.percentage:
            return None
        else:
            return self.time_elapsed * (100 - self.percentage) / self.percentage