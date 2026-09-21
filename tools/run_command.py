#!/usr/bin/env python3
"""Run one development command in a bounded, cleaned-up POSIX task group.

Example:
  python3 tools/run_command.py --timeout 120 -- python3 -m unittest tests.test_feed -v

Timeout, TERM, and INT stop the child shell and descendants in its inherited
process group.  This cannot clean descendants that intentionally call setsid
or otherwise escape that group, and SIGKILL of this supervisor prevents its
cleanup handler from running.
"""
from __future__ import annotations

import argparse
import sys

from process_supervisor import (DEFAULT_GRACE_SECONDS, DEFAULT_OUTPUT_TAIL_BYTES,
                                run)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, required=True,
                        help="maximum command runtime in seconds")
    parser.add_argument("--grace", type=float, default=DEFAULT_GRACE_SECONDS,
                        help="TERM grace period before SIGKILL, in seconds")
    parser.add_argument("--output-tail", type=int,
                        default=DEFAULT_OUTPUT_TAIL_BYTES,
                        help="retain and print at most this many final output bytes")
    parser.add_argument("command", nargs=argparse.REMAINDER,
                        help="command after --")
    args = parser.parse_args()
    command = args.command
    if command[:1] == ["--"]:
        command = command[1:]
    if not command:
        parser.error("supply a command after --")
    try:
        result = run(command, timeout_seconds=args.timeout,
                     grace_seconds=args.grace,
                     output_tail_bytes=args.output_tail)
    except (ValueError, RuntimeError) as error:
        print("run_command: {}".format(error), file=sys.stderr)
        return 2
    if result.output_tail:
        sys.stdout.buffer.write(result.output_tail)
    if result.output_truncated:
        print("run_command: transcript limited to final {} bytes".format(
            args.output_tail), file=sys.stderr)
    if result.timed_out:
        print("run_command: timed out after {}s; task process group stopped and "
              "direct child reaped".format(args.timeout), file=sys.stderr)
    elif result.cancelled_by is not None:
        print("run_command: cancelled by {}; task process group stopped and "
              "direct child reaped".format(result.cancelled_by), file=sys.stderr)
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
