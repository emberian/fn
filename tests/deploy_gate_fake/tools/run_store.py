#!/usr/bin/env python3
"""Fake host: the store CLI's shape without ACL2, for tests/test_deploy_gate.py.

Only the surface tools/deploy_gate.py depends on is here -- the subcommands it
calls, the three distinct exit codes, and a JSON store the fake reader can
serve.  Nothing here models fn's semantics and nothing here is evidence.
"""
import argparse
import base64
import json
import os
import sys

OK, REFUSED, UNCERTAIN = 0, 1, 3


def load(root):
    with open(os.path.join(root, "store.json")) as handle:
        return json.load(handle)


def save(root, state):
    tmp = os.path.join(root, "store.json.tmp")
    with open(tmp, "w") as handle:
        json.dump(state, handle)
    os.replace(tmp, os.path.join(root, "store.json"))


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--store", required=True)
    sub = parser.add_subparsers(dest="command", required=True)
    init = sub.add_parser("init")
    init.add_argument("--group", action="append")
    post = sub.add_parser("post")
    post.add_argument("--message-id", required=True)
    post.add_argument("--payload", required=True)
    post.add_argument("--group", action="append", required=True)
    post.add_argument("--charge", type=int)
    post.add_argument("--inject-fault")
    post.add_argument("--owner")
    inspect = sub.add_parser("inspect")
    inspect.add_argument("--message-id", required=True)
    for name in ("config", "recover", "status"):
        sub.add_parser(name)
    args = parser.parse_args(argv)

    if args.command == "init":
        os.makedirs(args.store, exist_ok=True)
        save(args.store, {"groups": args.group or ["fn.letters", "fn.test"],
                          "articles": [], "uncertain": []})
        print("initialized {}".format(args.store))
        return OK
    state = load(args.store)
    if args.command == "config":
        print("generation=1 served={} domain=".format(",".join(state["groups"])))
        return OK
    if args.command == "status":
        print("transactions={} articles={}".format(
            len(state["articles"]) + len(state["uncertain"]), len(state["articles"])))
        return OK
    if args.command == "recover":
        state["uncertain"] = []
        save(args.store, state)
        print("recovered transactions={} articles={} orphans=0".format(
            len(state["articles"]), len(state["articles"])))
        return OK
    if args.command == "inspect":
        for article in state["articles"]:
            if article["msgid"] == args.message_id:
                sys.stdout.buffer.write(base64.b64decode(article["payload"]))
                return OK
        return REFUSED
    with open(args.payload, "rb") as handle:
        payload = handle.read()
    if args.inject_fault == "postpublish":
        state["uncertain"].append(args.message_id)
        save(args.store, state)
        print("store: indeterminate injected failure after final publication",
              file=sys.stderr)
        return UNCERTAIN
    if any(a["msgid"] == args.message_id for a in state["articles"]):
        print("duplicate")
        return OK
    state["articles"].append({"msgid": args.message_id, "groups": args.group,
                              "payload": base64.b64encode(payload).decode()})
    save(args.store, state)
    print("committed sequence={} charge={}".format(len(state["articles"]), len(payload)))
    return OK


if __name__ == "__main__":
    sys.exit(main())
