# W13 feed correspondence checkpoint

This is a partial implementation and proof checkpoint, not closure of K5 or a new registry keystone. Parent requested this bounded checkpoint before Terra continuation. Physical PRF-043 remains the separate W12 scanner/fence claim.

## Source and ownership

Branch `w13/feed-correspondence`, worktree `build/lanes/w13-feed-correspondence`, baseline `d235b49`. Submission's schema commit `a191689` is cherry-picked as `2392cf1`. Actual emitting-transition repair is `4994e0d`; certifiable prefix, fixed driver signatures and reachable regressions are `eded80c`. Root owns registrations/IDs. Do not cherry-pick the schema twice if submission already landed it.

The new `books/feed-events.lisp` supplies ACL2 record emissions for the actual enqueue, tick, observe, loss and restart transitions. The new `books/feed-correspondence.lisp` contains the completed proof prefix. `planning/lanes/W13-feed-correspondence-continuation.lsp` is explicitly **unproved**, outside certification roots. Its observe theorem failed; subsequent draft statements were not attempted. Do not register them as proved.

Submission owns `:feed-intent`, `:feed-commit`, `:feed-abort` (codes 7/8/9), and all `fn-own-feed-intent-*`, `fn-own-feed-resolution-*`, `fn-own-submission-*` functions. This checkpoint leaves them unchanged. Auth is replacing direct `fn-owner` accesses with canonical owner-config helpers and will preserve the new `obs` arguments. Wire-block owns command rendering; this checkpoint changes no command API.

## Concrete repair

* New code 10 `:feed-retry`: peer, Message-ID, attempt, response code (431/436), monotonic tick. Replay invokes the original `fn-feed-back-off`; an explicit `:feed-drop :retry-bound` follows when actual observe drops.
* New code 11 `:feed-lost`: peer, monotonic tick. Replay invokes original `fn-feed-lost`. A loss emits this even without an in-flight entry, since the backoff deadline changes anyway.
* Actual enqueue emitter suppresses duplicate/full-queue no-ops. Actual sent emitter suppresses repeated go-ahead while already sent or disconnected. The old helper `fn-own-feed-reply-records-of` remains only for compatibility fixtures and is documented as such.
* `fn-own-feed-reply-records(o, peer, octets, obs)` and `fn-own-feed-lost-records(o, peer, obs)` now use the same observation as their live transitions. Host calls updated. Table helper loss signature is `(peer, tbl, obs)`.

The durable projection clears only connection identity. Queue entries, entry ticks, retry counts, drop reasons, next attempt, backoff, contact and limits are retained. The proof prefix establishes reconstruction for enqueue, actual `fn-feed-tick-step`, loss and restart. It does not yet establish observe, arbitrary live histories, or that generated histories satisfy `fn-feed-drivenp`.

## Reachable evidence

The new test book executes open → enqueue → offer → 431 and shows the legacy outcome loses both entry tick and deadline. Another reachable queued → loss witness shows the old empty emission loses deadline. Repeated 238 after sending demonstrates that the old duplicate sent record is not driven. A two-Message-ID finite trace exercises send, retries, retry-bound drop, loss, restart, reconnect and final acceptance; its complete generated record history is checked for drivenp and exact durable projection, with attempts/deadline/allocation values asserted. These are executable witnesses, not a universal finite-history proof.

The owner-feed loss fixture now checks complete durable projection, replacing the old comparison that omitted timing. It checks loss records also for queued and done feeds.

## Exact certification evidence

Final farm run `run-20260921T064626Z-aee4` **passed** all requested roots and their closure. Exact machine manifest: `planning/evidence/manifests/certify-20260921T064629Z-1674937.json`. Every manifest source SHA-256 was checked against the final local source at `eded80c` and matched. Narrow farm command:

```
python3 tools/farm.py submit hbox books/feed-correspondence tests/acl2/feed-correspondence-tests tests/acl2/owner-feed-tests --closure --jobs 4 --remote-root /tank/fn/lanes/w13-feed-correspondence
```

Farm uses ACL2 8.7 with SBCL 2.6.8. Remote trees have no Git revision; machine manifests bind input source SHA-256 and tool hashes. The final run was submitted just before `eded80c`; requested book sources are the committed `eded80c` contents. No blanket certification, simulator, process-cut campaign or INN run is claimed for this successor.

Failed development history is retained:

* `run-20260921T063332Z-aa19`, manifest `certify-20260921T063341Z-1659254`: peer-feed/invariants passed; feed-events guard proof needed the feed vocabulary enabled.
* `run-20260921T063747Z-1dff`: runner rejected an extra close parenthesis in the test; no certification manifest for that lexical failure.
* `run-20260921T064148Z-a7e2`, manifest `certify-20260921T064151Z-1669936`: peer-feed/invariants passed with new kinds. Feed-events failed because executable `mv-nth` violated ACL2 multiple-value signature; changed driver to `mv-let`.
* Local `certify-20260921T064411Z-95016`: stale peer-feed certificate rejected; no semantic result.
* Local `certify-20260921T064435Z-95219`: feed-events and reachable test book passed; correspondence stopped at tick, missing explicit numeric consequences of closed feedp.
* Local `certify-20260921T064549Z-95918`: tick/loss/restart prefix admitted after numeric lemma; observe proof failed. Unproved suffix moved to the continuation draft.

## Required continuation before K5 claim

1. Complete observe reconstruction. Current draft residuals include the no-inflight back-off identity and normalization of arbitrary observations. Keep queue vocabulary closed, add targeted lemmas rather than unrestricted dispatcher expansion.
2. Prove replay respects projection and finite actual generated histories reconstruct live execution. Draft induction needs a two-state/projection congruence lemma; the current single-state replay-on-projection induction is not established.
3. Prove real emitted batches and finite histories satisfy drivenp. `fn-feed-live-serializablep` checks only field grammar at actual steps, not drivenp; it is intended as an explicit encodability hypothesis, not a substitute for proving state admissibility. Actual successful frame encoding also checks the payload bound. Naturals in feedp are unbounded while FNFD nat fields are uint64; do not equate feedp with successful serialization.
4. Add named equality bridges to host-called owner emitters and transitions, including table enqueue with repeated peer names. Existing tick/lost bridges can be reused. Certify changed `books/owner.lisp` and composed host after other lanes merge; the narrow owner-feed test does not cover this whole owner wrapper.
5. Audit hypothesis teeth before promoting a keystone. Some prefix reconstruction hypotheses may be redundant because invalid feeds no-op; strengthen/remove rather than manufacture false teeth. Ground counterexamples here target repaired omissions, not every final theorem hypothesis.
6. Define and implement safe legacy timing recovery. Existing old `:feed-outcome` retry/loss frames still decode/apply as before, omitting timing. They cannot establish exact correspondence and must not be silently represented as supporting the new claim. A conservative operational policy would retain evidence and fence until explicit migration supplies a defensible new baseline. That policy is **not implemented** in this checkpoint.
7. State clock domain explicitly. Numeric tick replay is exact but monotonic timestamps across machine reboot are not generally comparable. Current process restart within one boot is the intended observation domain. No reboot liveness or epoch migration is proved or implemented here; use existing clock reset/epoch machinery when composing it.
8. Check new served-path validation cost. The emitter checks feedp in addition to the existing transition's check. No per-byte scan was added, but carry and reuse the owner invariant rather than claim a no-revalidation performance result.

Overall submission acceptance → durable intent → committed article → offer composition remains conditional on the submission lane's separate protocol. No physical byte-survival or peer-honesty claim follows from these logical proofs/tests.
