# Handoff: W19 BP application maintained fast invariant

Functional range is `9be78520^..e94f0e2f` followed by the focused config
projection commit after that range.  Commit `51a0b1a3` is omitted from
integration because current `dev` already contains its patch-equivalent
coherent-certificate tooling as `6708e238`.

Successful FNRJ recovery remains the deep validation boundary.
`fn-bpaj-successful-replay-has-statep` establishes the joined receiver
invariant, and `fn-bpaj-apply-record-fast-preserves-statep` carries it through
every successful live journal application.  The host calls the fast ACL2
functions for request status, dispatch, record lookup, journal application,
receipt projection and configuration status.  Their correspondence theorems
equate them to the checked functions under the maintained joined-state and,
where used, owner Store invariants.

The packet removes whole joined-state and Store recognizers from served BP
application actions.  It still validates the current untrusted request or
journal record.  Message-ID candidate lookup and retained intent/context
lookup remain linear searches; maintained indexes are separate work.

The recovered persvati manifest
`certify-20260921T112405Z-3238708.json` is a failed stale-source attempt, not
qualification of the branch tip.  Its test digest
`f0a4ea881800f9d53094686c8253d63a76526ef964c5072b3fa7563ea1c1a1fe`
is exactly the parent of `e94f0e2f`; certification failed because the local
include hid `*BPAJ-CONTEXT-REPLAY*`.  The branch-tip fixture digest after
changing that include to exported is
`953aeaa316c4bae9f2b9e09882f411de15ae98ba58524ee7cd739d8e0f5bd6b5`.
The manifest did certify `books/bp-native-app-fast`, but the failed test means
there is no passing packet result to claim.

Once process containment is available, the focused source-matched request is:

```sh
python3 tools/farm.py --jobs 4 --closure --timeout-seconds 900 submit HOST \
  books/bp-native-app-fast tests/acl2/bp-native-app-fast-tests
```

Do not reuse the stale manifest or infer success from its passing model book.
After certification, the composed native image still needs a scoped runtime
test on the same integrated source; this packet alone is not a service or DTN
release result.
