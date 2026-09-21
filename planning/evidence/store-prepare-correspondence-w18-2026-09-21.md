# Evidence: live-store prepare correspondence (W18)

Date: 2026-09-21. This is evidence for the served native store prepare
projection. It is not a whole-store complexity bound, a deployment
qualification, or native-owner adoption evidence.

## Subject and contract

The source packet is commit `41dfd024b2edbf4916a8a3394c269950ab3e877e`
on branch `w18/store-prepare-correspondence`, based on `76901c1`. The native
call chain is:

```
fnn-call
  -> fnn-bridge-prepare
  -> fn-store-sn-prepare
  -> fn-spc-prepare
```

`host/store-node-host.lisp` is the line-level caller of the new ACL2 subject.
The keystone `fn-spc-prepare-equals-specification-under-relation` states exact
equality with `fn-sn-prepare` under `fn-snt-relation`.
`fn-spc-related-candidate-is-recoverable` is the semantic bridge that derives
the omitted appended-history replay from that relation, the exact candidate
predicate, and the pending-node binding. `fn-spc-prepare-preserves-relation`,
`fn-spc-step-preserves-relation`, `fn-spc-run-preserves-relation`, and
`fn-spc-observed-open-run-maintains-relation` establish the maintained
post-open invariant through prepare, I/O observations, finish, reservation
refusal, known abort, keyring adoption, and staging sweep.

The executable preparation body still checks the reserved phase,
`fn-record-p`, `fn-sf-candidatep`, the empty node stage, and
`fn-sn-record-bindsp`. It does not execute `fn-sf-history-recoverablep`,
`fn-sf-replay-node`, `fn-snt-relation`, `fn-sf-statep`, or `fn-node-statep`.
Recovery still performs authoritative complete-history replay.

## ACL2 certification

The exact committed source was certified with:

```
FN_ACL2=/opt/homebrew/bin/acl2 \
python3 tools/certify_books.py --jobs 2 \
  books/store-prepare-correspondence \
  tests/acl2/store-prepare-correspondence-tests
```

Run `certify-20260921T094728Z-56739` passed both requested roots from clean
revision `41dfd024b2edbf4916a8a3394c269950ab3e877e`. The manifest records ACL2
8.7, SBCL 2.6.8, macOS 26.6.1 arm64, the full source closure, unchanged source
digests, and no lexical occurrence of the forbidden facilities. The book
digest is
`278bc5a4da320b34a67b5c84fc702c6416139e810b491a71d713b1ce1363cc79`;
the test-book digest is
`27118bb3131c2e11813dfdbc856a656fa9011878946bf788fa8dea3d729cd573`.

The test book includes a reachable reserved state with one committed record,
exact fast/specification equality for the next record, exact candidate bytes,
wrong-sequence refusal, and pending-binding refusal. Its relation-hypothesis
tooth constructs a structurally valid state with the real nonempty files and
a stale empty node: the projection stages a duplicate while the replaying
specification refuses it, so the equality assertion is a real `must-fail`
when `fn-snt-relation` is removed.

For the join audit, the source and test books plus the two host edits were
overlaid on integrated revision `399d4730d247309ce9e49d24c1d52609aa1d4cc6`.
Run `certify-20260921T094840Z-57318` passed the 36-book closure, including the
new staging-observation limit in `books/store-sweep.lisp`; targeted
`tools/host_check.py host/store-node-host.lisp` reported `1/1` loaded. The
overlay was dirty by construction, and the manifest records the exact source
digests.

## Actual saved image

The production image built from the clean source packet with:

```
FN_ACL2=/opt/homebrew/bin/acl2 sh tools/build_native_host.sh
```

The launcher/core SHA-256 values were respectively
`ddcbd3eea50cc784c3e93217724bd68a907dc4ca3cd5a9961766ba2000b0025f`
and
`b5ab2ca86a9950f680ba1b5830eff4891e14481e7eb178d08602a0cb02ad41ab`.
With `FN_NATIVE_HOST` naming that image,
`python3 -m unittest tests.test_native_storage_codec` ran seven tests in
24.299 seconds and passed. Those tests exercise native/Python cross-open,
native posting and inspection, malformed metadata refusal, frontier
exhaustion refusal, ambiguous publication recovery, and allocator/record
barrier recovery. They are saved-image component evidence, not native-owner
service evidence.

## Matched cost probe

For comparison with W16 commit `4e8fef7`'s native-store-cost evidence record,
a test-only image made the same two probe-local changes:
`fnn-command-probe` initialized the ACL2
`:scale` profile and generated a fixed 1,024-octet payload. It changed no book,
public command, deployed image, or ACL2 policy. The modified raw I/O and build
scripts had SHA-256 values
`601833cd757367b4e15d0dfc3f58d52c794d0ee062ced8610dcacc1b94d30137`
and
`1929a07c52dcb340acd0664b5aecd0c5106a751bcc0fb24cf0825590de56cdfc`.
The resulting launcher/core hashes were
`92ffe96442120447dea2a9d861c631697b1883eb9bfa79a62b87c22ee58dc04f`
and
`58de7bef3224f71ff6e30fd5a2b653669ce88a86c4c67ce4db9285a66fffab84`.

Fresh roots were measured with the same in-process command shape:

```
build/fn-host-store-cost-probe --fn store ROOT probe 50
build/fn-host-store-cost-probe --fn store ROOT probe 400
```

The JSON `payload_bytes` field is the profile's 32,768-octet ceiling, as in
W16; the generated payload was the fixed 1,024 octets stated above.

| committed records | in-process commit total | mean per record | reopen | process real/user/sys |
| ---: | ---: | ---: | ---: | ---: |
| 50 | 3.5060 s | 70.12 ms | 0.0876 s | 4.13 / 0.11 / 0.17 s |
| 400 | 31.1020 s | 77.76 ms | 0.6542 s | 31.87 / 0.89 / 0.75 s |

The eightfold state increase made the commit total 8.87 times larger and the
mean commit time 1.11 times larger. W16's pre-change probe on a different
Linux host measured 0.0950 and 9.3681 seconds total, a 98.6-fold increase and
means of 1.90 and 23.42 ms. Absolute times are not comparable across the two
hosts: this Mac run is dominated by durable filesystem waits, as the low user
times show. The within-run shape is the useful result. It is consistent with
removal of the profiled repeated replay and does not prove an asymptotic bound;
the retained candidate and node checks may still scan existing state.

## Limits and remaining integration

The source packet changes the native store wrapper only. Native owner
embedding is a separate caller/composition obligation. The integration join
must regenerate the ledger and resolve additive registry prose against current
main. Physical byte/effect correspondence, full native service parity, and
platform qualification remain open. Refused, uncertain, and durable outcomes
are unchanged because the new subject is exactly equal to the specification
on the maintained relation and no host outcome branch changed.
