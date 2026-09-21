# Handoff: W14 native configuration profile

The executable profile is `books/native-config.lisp`; its public subject is
`fn-native-config-load`. The raw host must provide only bounded file octets to
`fn-native-config-host-load` in `host/native-config-host.lisp`. The parser,
normalization, defaults, bounds, paired TLS rule, loopback policy, and native
consumer availability decision are all ACL2 definitions. `host/native/config.lisp`
contains a raw diagnostic verb but no saved image loaded it at this handoff.
There is therefore no native runtime-parity claim.

Local certification was run from this worktree with:

```
python3 tools/certify_books.py --jobs 1 books/native-config tests/acl2/native-config-tests
```

The source-pinned manifest is
`planning/evidence/manifests/certify-20260921T082423Z-83774.json`. It
records ACL2 8.7 / SBCL 2.6.8 on macOS, executable SHA-256
`36519682f97e83f1aadf9d092f46cb944d6621751595b8abf6b27b74309df324`, both
requested roots passed, `ACL2_CUSTOMIZATION=NONE`,
`ACL2_BOOK_HASH_ALISTP=NIL`, and the exact source digests. The run began from
`b8d760f` with a dirty worktree; the manifest's source digests, rather than
that revision label, identify the certified `c322da5` config correction.

The test root has a minimal profile, every documented table/key, parser and
semantic refusal teeth, and the 512-octet derived-default boundary: a store
path at the path bound is refused when its derived auth/control defaults would
exceed that bound, and accepted with explicit bounded alternatives.
