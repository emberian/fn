#!/usr/bin/env python3
"""Run one real store post and pause after a selected publication boundary.

The parent test owns the control pipe and kills this process group while the
child is paused.  The wrappers call the real syscall/ACL2 entry point first;
the pause therefore represents a process death after that boundary, rather
than an injected exception or a simulated power loss.
"""
import argparse
import os
from pathlib import Path
import sys
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402


def _pause(control_fd, point):
    sys.stdout.write("POINT {}\n".format(point))
    sys.stdout.flush()
    # The parent normally kills the process group while this read is blocked.
    # Keeping the read here closes the race between reporting and continuation.
    os.read(control_fd, 1)


def _install_boundary(point, store_root, control_fd):
    """Wrap one existing operation and pause after its successful call."""
    if point == "frontier-replace":
        real_replace = run_store.os.replace

        def replace(source, target):
            real_replace(source, target)
            if (Path(source).name.startswith(".allocation-")
                    and Path(target) == store_root / "allocation-frontier.json"):
                _pause(control_fd, point)

        run_store.os.replace = replace
        return

    if point == "frontier-dir-barrier":
        real_replace = run_store.os.replace
        real_fsync_dir = run_store.fsync_dir
        replaced = False

        def replace(source, target):
            nonlocal replaced
            real_replace(source, target)
            if (Path(source).name.startswith(".allocation-")
                    and Path(target) == store_root / "allocation-frontier.json"):
                replaced = True

        def fsync_dir(path):
            real_fsync_dir(path)
            if replaced and Path(path) == store_root:
                _pause(control_fd, point)

        run_store.os.replace = replace
        run_store.fsync_dir = fsync_dir
        return

    if point == "staged-data-barrier":
        real_fsync_file = run_store.fsync_file
        calls = 0

        def fsync_file(fd):
            nonlocal calls
            real_fsync_file(fd)
            calls += 1
            # The child starts with an already initialized store.  The first
            # file barrier is the allocation frontier staging file; the
            # second is the complete transaction staging file.
            if calls == 2:
                _pause(control_fd, point)

        run_store.fsync_file = fsync_file
        return

    if point == "final-link":
        real_link = run_store.os.link

        def link(source, target, *args, **kwargs):
            result = real_link(source, target, *args, **kwargs)
            if Path(target).parent == store_root / "transactions":
                _pause(control_fd, point)
            return result

        run_store.os.link = link
        return

    if point == "directory-barrier":
        real_link = run_store.os.link
        real_fsync_dir = run_store.fsync_dir
        link_done = False

        def link(source, target, *args, **kwargs):
            nonlocal link_done
            result = real_link(source, target, *args, **kwargs)
            if Path(target).parent == store_root / "transactions":
                link_done = True
            return result

        def fsync_dir(path):
            real_fsync_dir(path)
            if link_done and Path(path) == store_root / "transactions":
                _pause(control_fd, point)

        run_store.os.link = link
        run_store.fsync_dir = fsync_dir
        return

    if point == "core-durable":
        real_complete = run_store.Acl2Store.complete

        def complete(bridge, status):
            result = real_complete(bridge, status)
            if status == "durable" and result == "durable":
                _pause(control_fd, point)
            return result

        run_store.Acl2Store.complete = complete
        return

    raise ValueError("unknown crash point: {}".format(point))


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--store", required=True)
    parser.add_argument("--message-id", required=True)
    parser.add_argument("--payload", required=True)
    parser.add_argument("--point", required=True)
    parser.add_argument("--control-fd", required=True, type=int)
    args = parser.parse_args(argv)

    store_root = Path(args.store).absolute()
    _install_boundary(args.point, store_root, args.control_fd)
    command = SimpleNamespace(
        store=store_root,
        message_id=args.message_id,
        payload=Path(args.payload),
        group=["fn.letters"],
        charge=None,
        inject_fault=None,
    )
    return run_store.command_post(command)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except BaseException as error:
        print("child: {}".format(error), file=sys.stderr, flush=True)
        raise
