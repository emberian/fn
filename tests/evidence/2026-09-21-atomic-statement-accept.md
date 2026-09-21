# Atomic statement acceptance event — 2026-09-21

Source revision `ffdb406f`, branch `w25/identity-authority-statement`, clean
tree. The bounded invocation was:

```text
python3 /Users/ember/dev/fn/tools/run_command.py --timeout 240 --output-tail 12000 -- python3 tools/certify_books.py --jobs 1 books/stx-accept-records tests/acl2/stx-accept-records-tests
```

Both requested roots passed on `nextop.local` with ACL2 8.7 and SBCL 2.6.8.
Exact source/certificate digests, per-root results, executable digest,
timestamps, and environment are in
`planning/evidence/manifests/certify-20260921T163920Z-50012.json`.

Covered scope: the fn-e version-0 kind-4 definitions and guards admit. Named
`assert-event` witnesses evaluate exact parent encode/decode equality and one
non-degenerate `fn-stxa-bindsp` case. Separate negative witnesses substitute
the parent sequence, transaction, generation, keyring generation, profile,
Message-ID and content-subject, and supply malformed article or verdict child
bytes; each is refused. The valid event retains the exact canonical legacy
fn-r bytes and exact canonical kind-2 bytes under one parent.

These are evaluated witnesses, not a general round-trip, injectivity,
acceptance-refinement or crash theorem. The content-subject binding proves
equality among fields supplied to this event; the existing acceptance path
must establish that subject from the exact payload before construction. The
shared dispatcher, one-step replay, framed append/fsync, native writer and
crash cuts remain outside this run. Until those land, standalone kind 2 is
inert evidence and no durable historical-acceptance claim follows. D09 and
D11 remain open.
