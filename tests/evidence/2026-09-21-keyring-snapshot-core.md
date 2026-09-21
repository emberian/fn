# Keyring snapshot and ordered identity replay — 2026-09-21

Source revision `b0f1afa13f184ddd10bec6fb10ba0709c10d5ac9`, branch
`w25/identity-authority-statement`, clean tree. The bounded invocation was:

```text
python3 /Users/ember/dev/fn/tools/run_command.py --timeout 240 --output-tail 12000 -- python3 tools/certify_books.py --jobs 1 books/stx-keyring-records tests/acl2/stx-keyring-records-tests
```

Both requested roots passed on `nextop.local` using ACL2 8.7 at
`/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2` (SHA-256
`36519682f97e83f1aadf9d092f46cb944d6621751595b8abf6b27b74309df324`)
and SBCL 2.6.8. Exact source and certificate digests, per-root results,
runner digest, timestamps, and environment are archived in
`planning/evidence/manifests/certify-20260921T162533Z-41050.json`.

Covered scope: the codec and replay definitions admit with verified guards.
`fn-stxk-apply-snapshot-does-not-regress-current-generation` is a certified
general theorem for contexts carrying a natural current generation, with an
evaluated counterexample when that hypothesis is removed. Named `assert-event`
witnesses evaluate exact kind-3 encode/decode equality, snapshot-before-verdict,
strict sequence, profile binding, conflicting bytes, immediate generation
succession, G7 to G8 followed by duplicate G7 without rollback, fresh older-G6
refusal, and preservation of one historical verdict across rotation. These
witness evaluations are tests, not general codec or replay theorems. Unknown
profile bytes are retained in the witness, while the current-trust projection
remains empty because D09 has not selected a profile.

Limitations: this run does not establish integration of kinds 2 and 3 into the
shared Store dispatcher, file recovery, checkpoint compaction, or the native
writer. It does not select a signature/keyring profile, establish cryptographic
unforgeability or key custody, expose a served historical query, or close D09
or D11. The shared recovery lane owns the dispatcher and physical replay join;
adding a native sidecar here would violate the one ordered Store-history
contract.
