#!/usr/bin/env python3
"""Publish and select one checkpoint generation, pausing after a named cut.

The pause is the `faults.at("checkpoint:<name>")` site itself: the real
syscall before it has returned, the parent kills this process group while
the read blocks, so the death is ordered after the boundary and before the
next one, exactly the window the model's crash choice describes.
"""
import argparse
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import checkpoint, run_store  # noqa: E402


class PausingFaults(run_store.FaultPoints):
    __slots__ = ("point", "control_fd")

    def __init__(self, point, control_fd):
        self.point = point
        self.control_fd = control_fd

    def at(self, point):
        if point != self.point:
            return None
        sys.stdout.write("POINT {}\n".format(point))
        sys.stdout.flush()
        os.read(self.control_fd, 1)
        return None


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--store", required=True)
    parser.add_argument("--point", required=True)
    parser.add_argument("--control-fd", required=True, type=int)
    args = parser.parse_args(argv)
    faults = PausingFaults(args.point, args.control_fd)
    store, bridge, records = run_store.open_live_store(args.store, writable=True)
    try:
        generation = checkpoint.publish(store, bridge, records, faults)
        checkpoint.select(store, bridge, generation, faults)
        print("DONE generation={}".format(generation))
        return 0
    finally:
        bridge.close()
        store.close()


if __name__ == "__main__":
    try:
        sys.exit(main())
    except BaseException as error:
        print("child: {}".format(error), file=sys.stderr, flush=True)
        raise
