#!/usr/bin/env python3
"""Fake host: the owner entry point's shape, for tests/test_deploy_gate.py.

The gate selects `tools/run_owner.py` whenever bin/fn's `run` takes no
--store, so the fake tree needs an owner of its own: without one the real
owner starts against the fake store CLI, dies on an import, and the gate
falls back to the reader it did not claim to drive.  It lives beside
tests/deploy_gate_fake, not in it: the two-node and scale gates share that
overlay and drive owner behaviour (feeds, peering) this fake does not have,
so there the honest outcome stays the pinned fallback.  This serves the fake
store with POST on and every connection concurrent, announces itself in its
greeting so the evidence shows which entry point answered, and accepts the
owner's arguments.  It touches nothing but the fake store it is given, and
it is evidence of nothing but the gate's own logic.
"""
import argparse
import socket
import sys
import threading

from run_reader import Server, serve


class OwnerServer(Server):
    greeting = "201 fn-nntp fake owner ready"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--store", required=True)
    parser.add_argument("--port", type=int, default=0)
    parser.add_argument("--control", required=True)
    parser.add_argument("--max-connections", type=int, default=8)
    args = parser.parse_args()
    server = OwnerServer(args.store, True)
    listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    listener.bind(("127.0.0.1", args.port))
    listener.listen(args.max_connections)
    print("LISTENING {}".format(listener.getsockname()[1]), flush=True)
    while True:
        client, _ = listener.accept()
        threading.Thread(target=lambda c=client: (serve(server, c), c.close()),
                         daemon=True).start()


if __name__ == "__main__":
    sys.exit(main())
