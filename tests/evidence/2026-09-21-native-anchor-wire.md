# Native anchor wire component evidence — 2026-09-21

## Subject

This component run covers the ACL2-owned deployed RoughTime v1 response parser
in `books/anchor-wire.lisp`, its captured-response tests, and the independent
load of `host/anchor-wire-host.lisp`.  The input Git revision was `1e8955c`
with the guard/request follow-on present as a dirty working-tree packet:

| file | SHA-256 |
| --- | --- |
| `books/anchor-wire.lisp` | `e25dd673c38a03b5d395e07a8830aab4d384520bd9d3ba6fad2c05fefd9501cc` |
| `tests/acl2/anchor-wire-tests.lisp` | `e627dd0527484f996fbb5a457cb177f45028ca54af89e50ef5fe142ed600483d` |
| `host/anchor-wire-host.lisp` | `a969eacfbfe7decbb4efe6f514cde118ab0bd69bf175b4d2d617c022af5decd7` |

The committed manifests carry the complete source-closure digests, runner
digest, executable digest, environment, timestamps, and results.

## ACL2 certification

Host `nextop.local`, ACL2 8.7 built on SBCL 2.6.8:

```sh
python3 tools/certify_books.py --jobs 1 \
  books/anchor-wire tests/acl2/anchor-wire-tests
```

Both passed.  The parser book took 1.061 seconds and the test book took 1.020
seconds.  Exact manifests:

- `planning/evidence/manifests/certify-20260921T083217Z-92112.json`

The parser book contains 34 `defun` events.  Its archived certification log
`tests/evidence/native-anchor-acquisition/anchor-wire-guards.certify.log`
records 34 guard-conjecture checks, no guard failure, and successful
certification; in particular `fn-anchor-wire-request` and the host-called
`fn-anchor-wire-parse-response` are guard-verified executable functions.

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
(SHA-256 `045a94a7dc1956e4252d13ed5a74a145f1c35c57aa8611f7b76cd815e31d309d`).

## Limits

This is component evidence.  It proves neither Ed25519 nor SHA-512 security
and does not exercise FNAN persistence/recovery or CLI outcomes.  Native
request, CSPRNG, UDP and crypto composition evidence is recorded separately in
`tests/evidence/2026-09-21-native-anchor-acquisition.md`.  A
nonempty PATH is parsed and retained but remains `:uncertain
:unmodelled-tree` in the existing anchor acceptance machine.
