# Native operator grammar packet

Source: `w15/native-operator` commit `73f93e8`; the hbox tree was an isolated
`rsync --exclude .git` copy of that commit at
`/tank/fn/gates/w15-native-operator`. The manifest carries the source digests;
`books/native-operator.lisp` is SHA-256
`8dcc1054b11406557834b3b55e6ab0e295228db50f1288b4df30aa77d0c5c97c`.

`fn-native-operator-run` is the ACL2 command-plan subject. It receives bounded
configuration and argv octets, delegates configuration syntax/defaults to
`fn-native-config-load`, gates unavailable profiles through
`fn-native-config-operator-availablep`, and returns one five-tag result with
accessors for status, reason, command, config, and normalized arguments. Its
exit-code projection is accepted 0, refused 1, uncertain 3, fault 4, usage 5.
The accepted tag means only that a bounded plan was normalized; no host effect
or service-start success is claimed.

The usable increment normalizes `help`, `run [--once]`, `post --message-id ID
--payload PATH --group NAME... [--charge N]`, `status`, and `recover`. Repeated
singletons, missing post operands, repeated `--once`, stray status arguments,
and every other current `bin/fn` verb are named usage, never ignored. A parsed
nondefault posting profile is `usage :unsupported-profile` until the native
owner consumes one ACL2 posting projection for control and served admission.
The raw `--fn` diagnostic protocol remains separate.

Hbox ACL2 8.7 / SBCL 2.6.8 command:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 FN_CERT_CACHE=/tank/fn/certcache \
python3 tools/certify_books.py --jobs 1 --closure \
  books/native-operator tests/acl2/native-operator-tests
```

It passed in 4.608 seconds. The test book exercises normalized run/post/status/
recover plans, malformed port and ACL2-slot types, out-of-range port, repeated
configuration keys, repeated/conflicting command options, and explicit
unsupported-profile/verb outcomes. Exact tool inputs and per-book result are
in [the manifest](manifests/certify-20260921T083733Z-1869941.json).
