#!/usr/bin/env python3
"""Plan native certification with the selected tree's certify_books planner."""

import argparse
from pathlib import Path
import sys

CERTIFY_REFUSED = 16


def plan(planner, roots, mode, toolchain, acl2):
    """Use exactly the closure and installed-pair selection of --incremental."""
    closure = planner.with_dependencies(roots)
    installed = (planner.install_from_cache(roots, toolchain, acl2).installed_from
                 if mode == "incremental" else {})
    return closure, [book for book in closure if book not in installed]


def guard(closure, pending, mode, allow, box):
    print(f"== certify plan: {len(pending)} books to certify of "
          f"{len(closure)} in the roots' closure", flush=True)
    if pending and not allow:
        print(f"hbox_native: refused {mode} certify: {len(pending)} books "
              f"(first: {', '.join(pending[:5])}). "
              f"python3 tools/farm.py submit {box} --affected-by ... certifies "
              "through the farm and publishes to the cache; rerun after it, "
              "or pass --allow-certify. Native runs do not coordinate with "
              "farm's per-mirror locks.", flush=True)
        return CERTIFY_REFUSED
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tree", type=Path, required=True)
    parser.add_argument("--mode", choices=("incremental", "closure"), required=True)
    parser.add_argument("--toolchain-identity", required=True)
    parser.add_argument("--acl2", type=Path, required=True)
    parser.add_argument("--box", required=True)
    parser.add_argument("--allow-certify", action="store_true")
    parser.add_argument("roots", nargs="+")
    args = parser.parse_args(argv)
    # This helper is shipped beside run.sh even for a historical revision.
    # The planner and installer must belong to the tree being certified.
    sys.path.insert(0, str(args.tree.resolve() / "tools"))
    import certify_books
    try:
        closure, pending = plan(certify_books, args.roots, args.mode,
                                args.toolchain_identity, args.acl2)
    except (OSError, ValueError) as error:
        print(f"hbox_native: cannot plan certify: {error}", file=sys.stderr)
        return 2
    return guard(closure, pending, args.mode, args.allow_certify, args.box)


if __name__ == "__main__":
    sys.exit(main())
