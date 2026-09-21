# Keyring snapshot and ordered identity replay — 2026-09-21

Source revision `51def2363381d84d0df62fe2e3d05d6989fcf7fa`, branch
`w25/identity-authority-statement`, clean tree. The bounded invocation was:

```text
python3 /Users/ember/dev/fn/tools/run_command.py --timeout 240 --output-tail 12000 -- python3 tools/certify_books.py --jobs 1 books/stx-keyring-records tests/acl2/stx-keyring-records-tests
```

Both requested roots passed on `nextop.local` using ACL2 8.7 at
`/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2` (SHA-256
`36519682f97e83f1aadf9d092f46cb944d6621751595b8abf6b27b74309df324`)
and SBCL 2.6.8. Exact source and certificate digests, per-root results,
runner digest, timestamps, and environment are archived in
`planning/evidence/manifests/certify-20260921T161712Z-37175.json`.

Covered scope: the bounded `fn-e` version-0 kind-3 codec round-trips an opaque
keyring snapshot byte-exact; identity-local replay orders kind-3 snapshots and
kind-2 verdicts by their common Store sequence; a snapshot generation must
precede a verdict that names it; an identical generation/profile/payload repeat
is idempotent; a differing repeat faults; and later rotation leaves recorded
historical verdicts unchanged. Unknown profile bytes survive replay, while the
current-trust projection remains empty because D09 has not selected a profile.

Limitations: this run does not establish integration of kinds 2 and 3 into the
shared Store dispatcher, file recovery, checkpoint compaction, or the native
writer. It does not select a signature/keyring profile, establish cryptographic
unforgeability or key custody, expose a served historical query, or close D09
or D11. The shared recovery lane owns the dispatcher and physical replay join;
adding a native sidecar here would violate the one ordered Store-history
contract.
