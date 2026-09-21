# Statement verdict core certification — 2026-09-21

Source revision `a8f4522260fc0cb4994e848a61a9061be93f60d7`, branch
`w25/identity-authority-statement`, clean tree. Command:

```text
python3 tools/certify_books.py --jobs 1 books/stx-lace books/stx-index books/store-node books/store-node-invariants books/stx-evidence-records tests/acl2/store-node-index-tests tests/acl2/stx-evidence-records-tests
```

All seven requested roots passed on `nextop.local` using ACL2 8.7 at
`/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2` (SHA-256
`36519682f97e83f1aadf9d092f46cb944d6621751595b8abf6b27b74309df324`)
and SBCL 2.6.8. The exact source and certificate digests, per-root exit codes,
runner digest, timestamps and environment are archived in
`planning/evidence/manifests/certify-20260921T160840Z-31394.json`.

Covered scope: acceptance records a statement verdict with its keyring
generation; later in-memory keyring replacement preserves that historical
verdict; the bounded `fn-e` version-0 kind-2 codec round-trips a concrete
event and refuses corrupt envelopes and excess input. Unknown profile tags
are retained and explicitly unsupported as authority.

Limitations: this run does not establish durable keyring replay, integration
of kind 2 into the Store event dispatcher, NNTP reader exposure, a production
signature profile, cryptographic unforgeability, D09 custody, or D11 portable
authority.
