#!/usr/bin/env python3
"""Run the native v0 transit/feed accounting over an already staged tree.

This is intentionally narrower than ``tools/v0_matrix.py``'s complete native
slice.  It is for an immutable saved image and a task-local checkout on the
execution host: it runs the same ``V0Matrix.native_peering_suite`` method and
emits the complete row document, leaving every unrelated row explicitly
``not-exercised``.  It neither deploys a Git revision nor publishes the
current matrix.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
from pathlib import Path
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

from deploy_gate import LocalHost
import v0_matrix


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worktree", required=True,
                        help="task-local checkout on this host")
    parser.add_argument("--image", required=True,
                        help="immutable native image to execute")
    parser.add_argument("--runtime", required=True,
                        help="expected executable runtime path")
    parser.add_argument("--native-openssl-prefix", default=None,
                        help="OpenSSL prefix required by the saved native image")
    parser.add_argument("--source", required=True,
                        help="declared image source/content identity; recorded separately")
    parser.add_argument("--commit", required=True,
                        help="declared immutable image source commit")
    parser.add_argument("--tree", default="frozen-native-915",
                        help="human-readable source-tree label")
    parser.add_argument("--json", required=True, help="new output document path")
    args = parser.parse_args(argv)

    worktree = Path(args.worktree).resolve()
    if not (worktree / "tools" / "v0_matrix.py").is_file():
        parser.error("--worktree does not contain tools/v0_matrix.py: {}".format(worktree))
    target = Path(args.json).resolve()
    if target.exists():
        parser.error("--json already exists: {}".format(target))

    started = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    clock = time.monotonic()
    stopped = None
    with tempfile.TemporaryDirectory(prefix="fn-native-matrix-home-") as home:
        gate = v0_matrix.V0Matrix(
            LocalHost(Path(home)), worktree, args.commit, args.commit[:12], args.tree,
            backend=v0_matrix.NATIVE_BACKEND, native_image=args.image,
            native_image_source=args.source, native_runtime=args.runtime,
            native_openssl_prefix=args.native_openssl_prefix,
            campaign=False)
        # native_peering_suite runs its exact command through `cd deploy`; this
        # staged directory is the subject and is never rewritten by this tool.
        gate.deploy = str(worktree)
        gate._evidence_name = str(target)
        gate._matrix_name = str(target)
        try:
            gate.probe_native_subject()
            gate.native_peering_suite()
        except v0_matrix.GateError as error:
            stopped = "native peering accounting stopped: {}".format(error)
            gate.blocked(
                tuple(spec.key for spec in v0_matrix.PLAN
                      if spec.feature in ("F-TRANSIT", "F-FEED")),
                stopped, invocation="packaging/fn-native operator /not-opened help run")
        finally:
            gate.backfill()
        doc = gate.document(started, time.monotonic() - clock)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(doc, indent=2) + "\n")
    errors = v0_matrix.validate(doc)
    if errors:
        print("invalid matrix slice: {}".format("; ".join(errors)), file=sys.stderr)
        return 1
    selected = [row for row in doc["rows"] if row["feature"] in ("F-TRANSIT", "F-FEED")]
    print(json.dumps({"summary": doc["summary"], "rows_digest": doc["rows_digest"],
                      "selected_rows": selected}, sort_keys=True))
    if stopped:
        print(stopped, file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
