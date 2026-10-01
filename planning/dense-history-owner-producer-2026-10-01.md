# Dense history owner producer: one semantic decision, late file completion

Status: execution contract for the missing owner seam, 2026-10-01 UTC.
The coordinator ratified the semantic-writer lease and current-owner overlay.
This is a design/source handoff, not an existing reachable semantic producer,
certificate, runtime qualifier or native activation.

Inspected source cohort: integration `14c31f82a`; snapshot `3cecbfe19`;
`gpt61-canonical-size/books/replay-produced-size.lisp`;
portfolio's `consumer-configured-authority-replay.lisp` and new
`consumer-configured-control-event.lisp`; backing `2cc62f`;
owner-completion source through `c1da018f8`. Follow-up executors own their
exact source/proof coordinates. The earlier epoch contract remains applicable.

## The concrete missing producer

`fn-ris-produced-step-with-effects(ctx,fields,event,snapshot-carry)` returns
the actual MV6 `(checked,next-fields,status,effect,child,sizes)`. It can still
execute whole decoders, so a fuel argument on an outer wrapper would not make
it a bounded scheduling action. The exact event is a separate row, not its
child field. `fn-ssrp-intern-row` returns that exact row at MV6 of its MV8.

`fn-capr-event-step` produces `(:advanced,state17,full7-or6)` after actual
node/control/account decisions. Typed C produces full8. Neither is a Store
or an OCFG. State17 contains next configured node, ORIGINAL context and size
fields, CP, metadata, preparation, publication root, begin sequence,
withdrawals, visible rows, verdicts and C/E cursors. It lacks some Store
projections and the complete reader/obligation views.

Portfolio's additive `fn-cape-after-node` now consumes the actual retained
next configured node without re-running `fn-cpr-apply-event`. Recovery's
`fn-cape-begin` may call that interpreter once and delegate. Its bounded live
successor must get the node from the registered producer. The existing
`fn-cpr-apply-event`, visibility finalization and several account/projection
helpers still contain variable work. They are reference subjects to refine,
not approved one-tick calls. There is no complete bounded semantic producer
in this inspected cohort; its absence is independent of runtime qualification.

## One owner operation and phase order

Introduce a single STATE continuation `fn-owner-history-semantic-state`.
The actual APR token is its operation identity. Backing's producer token is
the SAME registered token, not a host nonce or another shadow counter.
`fn-owner-history-produce-step(fuel,fn-arena,fn-history-backing,
fn-page-read-pool,state)` resumes this current operation and returns word,
remaining fuel, those updated stobjs and state. Every phase checks its
registered token/base association before its bounded action. No host may
submit a semantic result or a continuation tagged done.

1. **Begin before semantic preparation.** At actual SF `:reserved`, capture
   actual base Store, original configured policy, view, CP/account sidecars,
   canonical context/fields, obligation view and source association. Read
   actual expected sequence/transaction from reservation and compare with the
   existing APR token. Retain these references under that current allowance.
   Index's intent8 is `(tag,token,epoch,predecessor-count,expected-pair,
   actual-base-Store,canonical,current-APR)`. Its predecessor version started
   at `:record-staged`; that was too late to recover the true prefix node.
   Never derive a prefix by clearing a prepared node or replaying history.
2. **Row and identity.** Drive the actual bounded intern/identity continuation
   once, retaining the SAME row and six results. Each decoder, identity
   lookup and size traversal must yield within its own phase; a missing
   continuation returns `:semantic-preparation-unavailable`. The old whole
   `fn-ris-produced-step-with-effects` remains the equality target. Offer the
   exact row/MV6 to the registered backing builder. Candidate reads at old F
   return that row, and lower positions use the retained old source.
3. **Node decision.** Drive one bounded version of the existing node/event
   interpreter, retaining both any prepared node needed for actual staging
   and its completed semantic result. Do not execute legacy node prepare and
   then replay the event again to obtain a second result. For recovery, the
   reference is `fn-cpr-apply-event`; for live submission the staged-node
   result must also refine its actual prepare/completion relation.
4. **Control and paired account result.** Call the internal
   `fn-cape-after-node` with the registered node result and SAME MV6. Its
   historical lookups use the private candidate prefix. Continue per row,
   target, verdict/config cell and comparison fragment. Split its remaining
   variable visibility/account finalization into resumable phases. Retain the
   literal returned full7/full8; never re-run `fn-acj-stage`, `fn-acj-commit`
   or `fn-carfc-event-step` to reconstruct its metadata or root.
5. **Complete the semantic projections.** Produce the missing Store fields,
   full reader view, posting policy where C changes it, and obligation view
   through the bounded cursors below. Each output is retained once. Until
   all are present, neither APR's `:produced` phase nor persistence is enabled.
6. **Prepare backing and seal the operation.** All page/directory operations,
   frame construction, canonical sizing and lifetime allowances must also
   finish. Join the actual semantic result and backing preparation7 under the
   SAME token. Write the actual APR packet10 once. This is the missing writer,
   not a tuple that a caller is allowed to supply.
7. **Stage and persist.** Stage the retained candidate using its prepared
   results without rerunning semantic preparation. Existing physical I/O
   transitions may proceed only under this operation's actual stage identity.
   Before record persistence, assert the semantic source lease still matches.
8. **Complete and publish.** Consume actual durable completion, perform only
   fixed-field assembly with the current owner shell, publish backing once,
   and install Store/CP/config/canonical/obligation/source together. No replay,
   history scan, view refresh or account decision runs here.

An internal preparation can evaluate a predicted semantic node before
durability, but it cannot manufacture successful file observations. Success
file state is obtained only from the actual completing file kernel in step 8.
Raw escape during an allocating semantic call retains its pre-call intent;
re-entry fences rather than repeating that call. A normal yield saves the
exact successor phase and resumes it.

## Field ownership and the remaining cursor work

| Retained value | One source and required implementation |
| --- | --- |
| Exact row and identity MV6 | Actual intern/identity producer; source refinement to `fn-ssrp-intern-row` and `fn-ris-produced-step-with-effects`; no second parser. |
| Next configured node | Same bounded node interpreter in phase 3; retain its intermediate staged node as needed. |
| CP, metadata5, root/fence/carry, authority preparation | Literal paired full7/full8 returned by portfolio. |
| Withdrawals, visible rows, verdicts | Same portfolio control continuation; finish any variable visible-row work before declaring semantic completion. |
| Topic projection | Cursor refining `fn-th-prefix-step`/carried equivalent over the SAME row; not another entire Store replay. |
| Statement index, keyring, key generation, snapshots and identity-next | Same identity result and exact accepted/composite delta. Reproduce the branches of `fn-ccar-sn-finish-enabled`/`fn-sn-finish-identity` with retained parser values. Snapshot/key/index walks need their own cursors; never call `fn-sn-finish-identity` and decode again. |
| Reader archive/raw, withdrawn list, Message-ID and group indexes | Finish equivalents of `fn-ctl-visible-state-of`, `fn-ctl-refresh-withdrawn`, `fn-midx-refresh`, `fn-gidx-refresh` using the already computed old/new visible rows; no `fn-own-refresh` at completion. |
| Configuration and config history for C | Actual paired typed-C or ordinary config decision, preserving config-first ordering. Refine `fn-oclc-configure` and paired CP result, including changed Store domain/capacity. |
| Posting config for C | Preproduce the actual `fn-oag-post-config(next-config,max-octets)` result used by `fn-oclc-publish`. |
| Obligation view | Same node mutation emits the typed delta below; a resumable path update produces the new view. |
| File state | Actual SF transitions; bind at completion, never supplied by the semantic producer. |

The node producer adds an internal readout:

```
fn-hpn-result(current-job) -> (mv :node-ready next-configured-node delta)
delta = (:same) | (:arrival exact-pin) | (:release exact-matched-pin)
```

This is a proposed actual producer interface, not an existing function.
Arrival is emitted by the SAME successful retention-admit mutation using its
new pin. Release retains the pin it actually matched before deleting it.
Neutral paths emit `:same`. A record kind alone is not proof that a mutation
succeeded. Do not classify by whole-graph equality in `fn-rov-update-arm`, or
invoke a second interpreter. Portfolio does not need this delta as a host
argument: the registered owner job retains it beside nextCN.

The obligation cursor refines `fn-rov-arrive`/`fn-rov-retract`. Its trie walk
reads a character in place, visits/rebuilds one branch/list cell per step,
and retains a charged path. Calling `fn-vdc-put`, which coerces the complete
key and traverses its path, inside one tick is not this cursor. All these
missing semantic cursors remain explicit implementation obligations; a
constructor qualifier cannot establish their existence or cost.

## Frozen result ABI and the one APR writer

Keep ownerResult10, correcting slot 4 from an old whole-owner snapshot to an
install plan:

```
(:history-owner-ready canonical-epoch predecessor-event-count expected-pair
  install-plan6 metadata5 root-sidecar canonical10 obligation-view parent6)

(:history-install-plan kind store-fields14 prepared-view10
                       prepared-config prepared-posting-config)

(:history-store-fields groups capacity node keyring index keyring-generation
                       verdicts snapshots identity-next config-history
                       consumer topic event-index)
```

Kind is `:E` or `:C`. Store-fields14 is exactly the `fn-sn-make-v6` operands
except FILES, with a tag. Prepared-view10 is the complete
`fn-own-view-make-visible` result, including its keyring/control projection.
Parent6 is `(:history-installed source-id concrete-epoch root-id
owner-publication-id canonical-owner-epoch)`; Source9 is unchanged.

Only the actual final semantic dispatcher writes:

```
(:history-semantic-done token SAME-row SAME-produced6 ownerResult10)
```

New internal `fn-owner-history-seal-produced(backing,state)` fetches that
STATE slot, intent8 and CURRENT APR. It checks the same registered operation
and the independently completed backing preparation, not just the tag.
It derives prefixNode from the intent's actual base Store and nextPrefixNode
from store-fields14's node. Then it calls existing `fn-apr-operation-packet`
with row, the six identity results, ownerResult10 and those two nodes, followed
by `fn-apr-produced` on CURRENT. It stores the resulting current5 back to
`fn-owner-canonical-admission-pending`. There is no native packet argument.
Backing preparation7's owner-result field retains this SAME ownerResult10.
An unreachable shaped `:done` fixture is not an establishment theorem.

## Exact E completion over current owner fields

The current owner-completion lane implements these fixed-field operations:

```
nextFiles = fn-sf-emit-success(
              fn-sf-core-completion(actualFiles,seq,txid),seq,txid)
nextStore = fn-sn-make-v6(prepared store fields with FILES=nextFiles)
nextOwner = fn-own-make(nextStore,preparedView,
  current.conns,current.next-id,current.max-conns,NIL,
  fn-sl-snoc(current.ledger,actualCompletionPair),
  current.clock,current.facts,current.config,current.queue,current.inflight,
  current.feeds,current.node-secret,current.refused)
nextOCFG = fn-ocfg-make(nextOwner,preparedConfig,current.pins,NIL)
```

The actual source is `host/history-owner-completion-host.lisp` with
`fn-odhc-store-from-plan`, `fn-odhc-owner-current-shell`, and
`fn-owner-history-complete-current`. It is currently internal source work,
not a admitted or activated boundary. Its checks must use parent6 and actual
canonical epoch, including the repeated-published branch. Prepared view's
count/frontier must match the actual final file scalars.

Before these stores, validate the actual SF phase `:completing`, pair,
predecessor count, semantic lease, prepared backing, canonical coordinate and
source association. Register backing completion3 only from this actual
transition. Publish once and put nextOCFG, retained obligation view, CP
metadata/root, canonical result and parent6 in the same serialized call.
`fn-owner-install-ocfg` is not used because it recomputes `fn-rov-update`.
An already published matching operation returns `:consumed`; another
completion cannot append again.

C is a distinct follow-on action, not a fake E with unchanged ordinal. It
preserves actual SF files and owner completion ledger/pending, overlays its
prepared Store/view/config and posting configuration, installs paired CP,
and replaces source-id/publication-id with F and event root unchanged.
It requires the actual config-journal durable receipt bound to staged C
sequence/txid and operation, plus a no-append backing publication branch.
The E completion3 and `fn-hep-publish-current`'s F+1 arm do not authorize C.
Until that real receipt/branch exists, C at this new seam remains unavailable.

## Source stability: implementation obligations, not an assumption

The semantic writer owns CURRENT APR token plus base Source9 source-id,
owner-publication-id and canonical epoch. Every semantic publisher must use
the same gate. The already existing single Store/config writer checks are
useful but do not cover direct installers automatically.

| Mutation family | Actual inspected gate/call sites to join |
| --- | --- |
| Article and transit submission | `fn-own-begin`/`fn-ocfg-step` begin/take; `fn-owner-prepare`, `fn-owner-prepare-buffer`, sealed catalog preparation and all three finish entries. Keep the same pending writer through the new prepare/persist/complete chain. |
| Retention, consumer, topic | `fn-owner-prepare-retention`, `fn-owner-prepare-consumer`, `fn-owner-prepare-topic`; Store reserved/pending phase is necessary but must also name CURRENT token. |
| Keyring/composite identity | `books/owner-retain-transitions.lisp:fn-owner-prepare-identity`; use the same current operation, no legacy refresh/prepare bypass in bounded mode. |
| Ordinary and typed account configuration | `fn-ocfg-reconfig-okp/refusal` already requires no pending owner, no staged config and SF ready; `fn-owner-reconfigure-deltas`, `fn-owner-reconfigure-complete`, `fn-ccp-publish`/typed account publication must additionally join the lease. |
| Recovery, reset, import and reclaim swap | `fn-owner-recover-*`, actual install boundary, `fn-owner-log-reopen`, `fn-owner-orcp-swap-word`/finish and column/source replacement are independent replacement paths. Refuse or drain CURRENT semantic operation and history custody before mutation; invalidate canonical epoch on actual replacement. |
| Direct policy/secret/profile changes | `fn-owner-install-node-secret`, `fn-owner-install-profile`, `fn-owner-posting-configure`, `fn-owner-set-auth-config` bypass ordinary Store record staging. They must be startup-only while no writer is present or join the same semantic gate/publication identity. |

There is no verified central currentpending check covering every row today.
The concrete new `fn-owner-history-writer-gate` is a fixed CURRENT-token/source
check used at these semantic entry points and publication boundaries. Do not
put a blanket gate in `fn-owner-install-ocfg`: that generic function is also
used by permitted connection/I/O transitions. Completion coverage must be
established for the bounded-mode dispatch set; any unmigrated entry is refused
before mutation. This finite coverage is part of enabling the new mode.

During the lease, current transaction SF physical phases may evolve under the
carried stage relation. No other operation changes semantic Store node,
CP/account roots, configured authorization, keyring, visibility/catalog root,
obligation view, injection policy or source epoch. Connection/session/pin,
next-ID, clock/facts, queue, inflight, feed and refusal bookkeeping may evolve
and are read from the current owner at final assembly. They cannot replace
or clear the shared semantic pending operation. Closing its response channel
records cancellation separately; it cannot erase a possibly durable request.
The accepted row retains its original observation/context even if clock changes.

Pre-persistence mismatch holds or refuses the operation and performs joined
cleanup before any commit. After durable success or ambiguous persistence,
mismatch fences recovery with candidate, receipts and aliases retained; it
never refuses and resumes mutation or rolls back accepted bytes. Comparison
of fixed source identities and carried phase invariants replaces whole-object
equality. Reader allocations may advance the shared PRS nonce; they do not
change this operation's current affine token or semantic source.

## Sol execution ownership and proof boundary

Index owns begin-before-stage intent, the sole APR packet writer and internal
registration; snapshot owns exact row/identity continuation; portfolio owns
after-node control/account/paired result; owner-union owns fixed-field final
assembly; backing owns page/directory/preparation/completion custody. The
missing node interpreter, Store projection, reader-view and obligation cursors
need explicit execution ownership before claiming a reachable semantic finish.

Required theorem is full-result equivalence of the actual producer+completion
to the selected Store/config completion, with its old source relation, exact
candidate, durable completion and semantic writer invariants. It includes
current-shell preservation, CP/root/metadata/canonical/ROV and Source9 effects.
Witnesses include connection and clock changes during I/O, stale source before
commit, source change discovered after durability, repeated callback, typed C
without an E append, and exact nonarticle events. A prepared tuple or passing
shape check proves none of these. No new trust assumption is introduced.

This handoff ran source inspection and whitespace validation only. Semantic
production remains missing in the inspected source; runtime constructor and
lifetime qualification independently remain unavailable. Preserve both facts.
