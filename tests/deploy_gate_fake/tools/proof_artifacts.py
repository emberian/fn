#!/usr/bin/env python3
"""Fake artifact acquisition for the deploy harness's local dry run."""
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("action", choices=("acquire", "roots", "validate"))
parser.add_argument("--profile", required=True)
parser.add_argument("--root")
parser.add_argument("--cache")
parser.add_argument("--acl2")
args = parser.parse_args()

if args.action == "roots":
    print("books/acceptance")
elif args.action == "validate":
    print("profile={} image=build/fn-host roots=1 result=loaded".format(args.profile))
else:
    print("profile={} image=build/fn-host artifact-set=fake-coherent-set "
          "origin=/fake/farm/run books=1 source=fake-source "
          "toolchain=fake-acl2 rejected=0".format(args.profile))
