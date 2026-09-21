# Native anchor wire component evidence — 2026-09-21

## Subject

This component run covers the ACL2-owned deployed RoughTime v1 response parser
in `books/anchor-wire.lisp`, its captured-response tests, and the independent
load of `host/anchor-wire-host.lisp`.  The input Git revision was `88f4145`
with these new files present as a dirty working-tree packet:

| file | SHA-256 |
| --- | --- |
| `books/anchor-wire.lisp` | `55e33031f5f320bbb859eee036a771cd22fd2d267b017852c7997d959f1c7432` |
| `tests/acl2/anchor-wire-tests.lisp` | `a56919d977ec4609629ae899540c2cffc014f605b178247d8aa8a0d45f67d300` |
| `host/anchor-wire-host.lisp` | `51fb0fc53f678053db1440658fe929ef54fb1162525d5b15ec7ca1522597f82d` |

The committed manifests carry the complete source-closure digests, runner
digest, executable digest, environment, timestamps, and results.

## ACL2 certification

Host `nextop.local`, ACL2 8.7 built on SBCL 2.6.8:

```sh
python3 tools/certify_books.py --jobs 1 books/anchor-wire
python3 tools/certify_books.py --jobs 1 tests/acl2/anchor-wire-tests
```

Both passed.  The parser book took 1.025 seconds and the test book took 0.977
seconds.  Exact manifests:

- `planning/evidence/manifests/certify-20260921T082532Z-84838.json`

The test book evaluates exact committed int08h packet octets for one empty
PATH and one real one-node PATH, and negative nonce, tag order/duplication,
offset, truncation and hard-bound cases.  It makes no network call.

## Host bridge load

```sh
FN_ACL2=/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2 \
  python3 tools/host_check.py --timeout-seconds 120 \
    --log-dir tests/evidence/native-anchor-wire-host \
    host/anchor-wire-host.lisp
```

Result: `1/1` host files loaded alone and restored the logic-mode prompt.  The
complete ACL2 transcript is
`tests/evidence/native-anchor-wire-host/host_anchor-wire-host.lisp.log`
(SHA-256 `a8fd9972a82d1436a7f59e6bd1b0280ee73ace34c307f9262254f19eaf51b22a`).

## Limits

This is component evidence.  It proves neither Ed25519 nor SHA-512 security
and does not exercise UDP acquisition, request encoding, nonce generation,
native crypto composition, FNAN persistence/recovery, or CLI outcomes.  A
nonempty PATH is parsed and retained but remains `:uncertain
:unmodelled-tree` in the existing anchor acceptance machine.
