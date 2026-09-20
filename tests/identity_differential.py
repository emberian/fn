"""Differential: the ACL2-derived content identity against the host's old SHA-256.

`books/crypto-attach.lisp` attaches an executable SHA-256 to `fn-frame-digest`,
so `fn-id-subject-of-payload` and `fn-id-obligation-of` now run in logic and
`tools/frame_bridge.py` no longer hashes.  This script is the evidence that the
move changed no octet: for each random payload it derives the identity BOTH
ways through one live ACL2 session --

  new: (fn-store-subject-id-of-payload payload)      -- preimage and digest
                                                        both in ACL2
  old: (fn-store-subject-id <sha256(prefix || payload)>) with the prefix from
       (fn-store-subject-prefix <len>)               -- the split the host used

-- and compares them.  A disagreement is a defect in `books/sha256.lisp`, not
a tolerable difference: these are the same bytes or the identity changed.

Run on a box with ACL2 and a certified `host/store-host`:

    python3 tests/identity_differential.py [--cases 100] [--seed 20260920]
"""

from __future__ import annotations

import argparse
import hashlib
import random
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import frame_bridge  # noqa: E402
from tools.frame_bridge import _as_bytes, _octets  # noqa: E402


def payloads(count: int, seed: int) -> list[bytes]:
    """Random payloads, with the boundaries a padding defect hides behind."""
    rng = random.Random(seed)
    fixed = [b"", b"a", bytes(range(56)), bytes(range(64)), bytes(range(65)),
             b"\x00" * 119, b"\xff" * 120, bytes(range(256)) * 128]
    rest = count - len(fixed)
    return fixed + [bytes(rng.randrange(256) for _ in range(rng.randrange(0, 4096)))
                    for _ in range(max(0, rest))]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cases", type=int, default=100)
    parser.add_argument("--seed", type=int, default=20260920)
    args = parser.parse_args()

    session = frame_bridge.session()
    cases = payloads(args.cases, args.seed)
    mismatches = []
    acl2_seconds = 0.0
    try:
        for index, payload in enumerate(cases):
            started = time.monotonic()
            new = session.subject_id(payload)
            acl2_seconds += time.monotonic() - started

            prefix = _as_bytes(session.call(
                "(fn-store-subject-prefix {})".format(len(payload))))
            old = _as_bytes(session.call(
                "(fn-store-subject-id "
                + _octets(hashlib.sha256(prefix + payload).digest()) + ")"))
            if new != old:
                mismatches.append(("subject", index, len(payload)))

            msgid = b"<" + hashlib.sha256(payload).hexdigest().encode() + b"@fn.invalid>"
            new_ob = session.obligation_id(msgid, new)
            preimage = _as_bytes(session.call(
                "(fn-store-obligation-preimage " + _octets(msgid) + " "
                + _octets(new) + ")"))
            old_ob = _as_bytes(session.call(
                "(fn-store-obligation-id "
                + _octets(hashlib.sha256(preimage).digest()) + ")"))
            if new_ob != old_ob:
                mismatches.append(("obligation", index, len(payload)))
    finally:
        frame_bridge.close()

    total = sum(len(p) for p in cases)
    print("cases {} payload-octets {} acl2-identity-seconds {:.3f}".format(
        len(cases), total, acl2_seconds))
    if mismatches:
        for kind, index, length in mismatches:
            print("MISMATCH {} case {} payload {} octets".format(kind, index, length))
        return 1
    print("agreement: every ACL2-derived identity equals the host's SHA-256 derivation")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
