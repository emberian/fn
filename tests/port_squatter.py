"""Hold kernel-assigned loopback ports, the way a busy box does, for a while.

The fixture that reproduces NATIVE-HARNESS-PORT-RACE on a native gate: while
it runs, COUNT sockets at a time are bound to port 0 on 127.0.0.1 (the kernel
picks each from its ephemeral range, as it does for any client connect or
probe) and each is closed and replaced every HOLD seconds, so the set of taken
ports keeps moving.  A node configured with a probed-and-released ephemeral
port then meets EADDRINUSE at its bind with probability about COUNT / (size of
the range); a port reserved below the range (tools/ports.py) never does.  It
stops by itself after SECONDS.

    python3 tests/port_squatter.py --count 5000 --hold 2 --seconds 3600
"""
import argparse
import collections
import resource
import socket
import time


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--count", type=int, default=5000)
    ap.add_argument("--hold", type=float, default=2.0)
    ap.add_argument("--seconds", type=float, required=True)
    args = ap.parse_args(argv)
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    want = args.count + 64
    if soft < want:
        resource.setrlimit(resource.RLIMIT_NOFILE, (min(want, hard), hard))
    end = time.monotonic() + args.seconds
    held = collections.deque()
    taken = 0
    while time.monotonic() < end:
        now = time.monotonic()
        while held and held[0][0] <= now:
            held.popleft()[1].close()
        while len(held) < args.count:
            s = socket.socket()
            s.bind(("127.0.0.1", 0))
            held.append((now + args.hold, s))
            taken += 1
        time.sleep(0.05)
    for _, s in held:
        s.close()
    print("port_squatter: %d kernel-assigned ports taken over %.0f s" % (taken, args.seconds), flush=True)


if __name__ == "__main__":
    main()
