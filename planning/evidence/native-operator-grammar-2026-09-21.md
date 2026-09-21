# Native operator grammar packet

Source: `w15/native-operator` corrected commit pending certification; the hbox tree is an isolated
`rsync --exclude .git` copy at
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

The usable increment normalizes `help`, `run [--once]`, `status`, and `recover`.
`post` is explicit `usage :shared-submission-unavailable`: the former direct
payload/message-id/group grammar is not a native operator compatibility surface.
Repeated `--once`, stray status arguments, and every other current `bin/fn` verb
are named usage, never ignored. Malformed configuration syntax, type, range, or
repetition is also usage at this operator boundary, while native-config retains
its diagnostic refusal result internally. A parsed nondefault posting profile is
`usage :unsupported-profile` until the native owner consumes one ACL2 posting
projection for control and served admission. The raw `--fn` diagnostic protocol
remains separate.

Hbox ACL2 8.7 / SBCL 2.6.8 command:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 FN_CERT_CACHE=/tank/fn/certcache \
python3 tools/certify_books.py --jobs 1 --closure \
  books/native-operator tests/acl2/native-operator-tests
```

The prior command passed before the boundary correction; the corrected closure
and source digest are recorded in the follow-up evidence committed with this
report. The tests exercise normalized run/status/recover plans, explicit post
unavailability, quoted nonnumeric port and ACL2-slot types, out-of-range port,
repeated configuration keys, repeated/conflicting command options, and explicit
unsupported-profile/verb outcomes.
