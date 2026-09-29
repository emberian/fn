#!/usr/bin/env python3
"""Synthesize a large format-10 store by writing its record log directly.

    tools/synth_log_store.py SEED OUT N [--batch B] [--check-only] [--image IMAGE]

SEED is a real format-10 store with no checkpoint whose journal/000001.log holds
article records written by the owner (a POSTed fixture: tools/fixtures.py's
n1k-2k).  OUT (must not exist) gets SEED's files except journal/, the seed's
genesis (journal/000000.log, copied unchanged, so OUT is the seed's node: its
identity, history salt and profile digest), and a journal/000001.log of N
article records renumbered from SEED's.

Every byte of that log is written by ACL2: tools/synth-log-store.lisp, `ld'd
into a developer image's own session (`fn acl2 session'; IMAGE, default
$FN_NATIVE_DEVELOPER_HOST), verifies the seed (its genesis, every entry's
chain and trailer, every record's encoding and content identities) and writes
the entries with the books' own functions: the identities
(fn-id-subject-of-payload, fn-id-obligation-of), the records
(fn-record-encode), the frames, trailers and padding (fn-lg-frame,
fn-lg-trailer, fn-lg-pad-len).  This file lays out the directory, starts the
session and fsyncs; it computes no identity, frame or trailer.

The seed's profile and configuration must hold N: a 2 KiB article is charged
2 units of the store's capacity (fn-charge-for-payload), and the default
capacity (1,048,576) refuses the replay past ~524k articles.  For 1M: import
the seed's export with --max-transactions 4000000 --max-history-octets
8000000000, run it once and set `capacity 4000000`; the record's
planning/evidence/snapshot-open-2-2026-09-27.md section 5 has the commands.

A TEST FIXTURE writer: it decides nothing the node relies on.  The node's own
open verifies every frame, chain link and record.
"""
import argparse
import os
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tests.native_harness import Acl2Session, acl2_result  # noqa: E402

PROGRAM = ROOT / "tools" / "synth-log-store.lisp"


def lisp_string(path):
    return '"' + str(path).replace("\\", "\\\\").replace('"', '\\"') + '"'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("seed"); ap.add_argument("out"); ap.add_argument("n", type=int)
    ap.add_argument("--batch", type=int, default=1)
    ap.add_argument("--check-only", action="store_true")
    ap.add_argument("--image", default=None,
                    help="a developer image (default: $FN_NATIVE_DEVELOPER_HOST)")
    a = ap.parse_args()
    journal = Path(a.seed) / "journal"
    listing = sorted(os.listdir(journal))
    checkpoint = Path(a.seed) / "store-checkpoint.fnsc"
    if checkpoint.exists() or listing != ["000000.log", "000001.log"]:
        raise SystemExit("seed: expected the genesis and one segment (journal/000000.log, "
                         "000001.log; format 10) and no checkpoint; found journal/ %s%s (a seed "
                         "whose owner checkpointed has rotated its log: initialize it with "
                         "--max-open-suffix above its record count)"
                         % (listing, " and store-checkpoint.fnsc" if checkpoint.exists() else ""))
    out_log = Path(a.out).resolve() / "journal" / "000001.log"
    if not a.check_only:
        if os.path.exists(a.out):
            raise SystemExit("out exists")
        shutil.copytree(a.seed, a.out, ignore=shutil.ignore_patterns("journal", "writer.lock"))
        os.mkdir(os.path.join(a.out, "journal"), 0o700)
        shutil.copy2(journal / "000000.log", Path(a.out) / "journal" / "000000.log")
        os.close(os.open(out_log, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600))
    # 100 ms a record is far above the rate: a hang detector, not a budget.
    timeout = 600 + a.n // 10
    with Acl2Session(a.image, timeout=600) as acl2:
        acl2.call('(ld {} :ld-prompt nil :ld-verbose nil :ld-pre-eval-print nil '
                  ':ld-post-eval-print nil :ld-error-action :error)'.format(
                      lisp_string(PROGRAM)))
        reply = acl2_result(acl2.call("(synth-log-store {} {} {} {} {} {} state)".format(
            lisp_string(journal.resolve() / "000000.log"),
            lisp_string(journal.resolve() / "000001.log"),
            lisp_string(out_log), a.n, a.batch, "t" if a.check_only else "nil"),
            timeout=timeout)).decode("ascii", "replace")
    words = reply.strip("()").split()
    if not words or words[0].upper() not in (":CHECKED", ":WROTE"):
        raise SystemExit("synth-log-store refused: " + reply)
    if a.check_only:
        print("seed: %s records verified, identities recompute" % words[1])
        return
    fd = os.open(out_log, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)
    print("wrote %s records, %s octets of entries" % (words[1], words[2]))


if __name__ == "__main__":
    main()
