# Evidence: shared native-owner prepare correspondence (W18)

Date: 2026-09-21. This packet adopts the live-store prepare projection in the
shared native owner. It is scoped to that owner POST prepare/pending-byte
boundary; it is not whole-host equivalence, a whole-path complexity bound, or
physical durability qualification.

## Actual call and exact correspondence

The clean source revision is
`8cbeda97081b38b638b42aeee204f2e7e887bb1b` on
`w18/native-owner-fast-prepare`, based on integrated revision `ef6a0177`.
The durable POST path reaches the changed subject through:

```
fnn-owner-handle-chunk
  -> fnn-owner-serialized
  -> fnn-owner-drain-one
  -> fnn-owner-attempt
  -> fn-owner-prepare
  -> fn-opc-prepare
```

`fn-opc-prepare-equals-owner-event-under-relation` proves that the new subject
is exactly the former
`fn-ocfg-step oc '(:store (:prepare record))` result under the sole premise
`fn-own-relation (fn-ocfg-owner oc)`. The inner theorem
`fn-opc-owner-prepare-equals-owner-store-step-under-relation` lifts
`fn-spc-prepare-equals-specification-under-relation` through the owner's exact
store replacement and refresh. Only the outer equality and the separately
host-called standalone-store equality are registered for PRF-014; the semantic
helper and projection corollaries are not registered as keystones.

The actual executable chain does not call `fn-sf-history-recoverablep`,
`fn-sf-replay-node`, `fn-snt-relation`, `fn-own-relation`, `fn-sf-statep`,
`fn-sn-statep`, or `fn-node-statep`. It retains the reserved phase,
`fn-record-p`, exact candidate counters, empty node stage, and pending-node
binding checks already present in `fn-spc-prepare`. Recovery continues to use
authoritative complete-history replay.

## Maintained owner premise and effects

`fn-opc-observed-open-configured-owner-has-relation` follows the actual
recovery construction: successful `fn-sn-open-observed`, `fn-own-start`, then
`fn-own-configure`. `fn-opc-configured-step-preserves-owner-relation` and
`fn-opc-configured-run-preserves-owner-relation` cover configured-owner events.
The direct host entries `fn-ocfg-open`, `fn-ocfg-open-peer`, `fn-ocfg-read`,
`fn-ocfg-read-step`, and `fn-ocfg-fault` are covered separately by
`fn-opc-direct-configured-entries-preserve-owner-relation`, rather than being
inferred from the uncalled run helper. Existing owner preservation theorems
cover the raw owner transformations used by the remaining host wrappers.

`fn-opc-prepare-keeps-configured-owner-context` proves the live configuration,
pin table, and staged configuration record are exact. The owner projection
copies the next connection id, connection table, pending transaction, ledger,
clock, facts, posting configuration (including path identity), submission
queue, in-flight submission, and feed table before applying the same owner
refresh as the prior event. `fn-opc-pending-octets` is the logical pending-byte
projection now called by `fn-owner-pending-octets`; its equality after prepare
is a corollary of the outer keystone.

## Teeth and certification

The test scenario reaches a second reservation through configured-owner events
after committing one real record. It checks exact old/new owner equality,
nonempty pending bytes, and preservation of the owner allocation/configuration/
feed fields. Wrong sequence and a correct-counter conflicting Message-ID are
both refused by both subjects.

The sole-premise tooth retains the real nonempty file history and every outer
configured-owner field but replaces the node with a stale empty node. The
result remains a well-shaped owner/configured-owner value. The fast subject
stages the conflicting Message-ID while the former replaying event refuses it;
the equality assertion is therefore a real `must-fail` without
`fn-own-relation`, rather than a malformed-shape counterexample.

The clean revision was certified with:

```
FN_ACL2=/opt/homebrew/bin/acl2 \
python3 tools/certify_books.py --jobs 2 \
  books/owner-prepare-correspondence \
  tests/acl2/owner-prepare-correspondence-tests
```

Run `certify-20260921T101506Z-81697` passed both roots with ACL2 8.7,
SBCL 2.6.8 and macOS 26.6.1 arm64. The manifest records a clean git tree,
the full source closure, unchanged runner/source digests, and no lexical
occurrence of the forbidden proof facilities. The book, test, and host source
SHA-256 values are respectively
`ee2e94a0e4ba3c8e959cf020710114c3a265be2931c858e460788d0c471fda7d`,
`b750ef835a36c21db532f243ddb829f7fbbdc26ca7415bd48efe709d9a737c3c`,
and `858c2560a40ad287f6c9cce762330f52f2e5ca26611203836077b400e44deb49`.
Targeted host loading reported `1/1` for `host/owner-host.lisp`.

## Saved-image owner result

A production native image was built from the clean revision with
`FN_ACL2=/opt/homebrew/bin/acl2 sh tools/build_native_host.sh`. The launcher
and core SHA-256 values were respectively
`4348c9da44983ff67412b8abb5dcc3a7da50cb2fba62d23294a299c27dbd1b23`
and `09dae2b8f67d313c4cab62fb991ff040a3bfb9c8622a3085a83baffd2e3a8098`.
The build log contained the ready marker and no uncertified-book or error
marker.

With `FN_NATIVE_HOST` naming that image,
`python3 -m unittest -v tests.test_native_owner` passed all six tests in
9.340 seconds. The exercised cases include a durable post readable after
owner exit, two-client uncertainty fencing before later mutation, uncertain
commit/feed-intent reconciliation on restart, disconnect isolation, invalid
feed evidence faulting, and preservation of conflicting empty-feed evidence.
This is actual shared-owner saved-image evidence, but it does not replace the
full native service/deployment gate or physical power-loss evidence.

No matched Linux cost run was performed in this packet. The earlier W16 Linux
and W18 Mac figures are on different hosts and remain unsuitable for absolute
before/after comparison; this packet prioritizes the actual owner caller and
invariant join.
