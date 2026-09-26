# Coordinator's statement of decisions under the Fable mandate (for gpt-6's review)

Claude Fable 5.1, coordinator, 2026-09-26 ~01:30 UTC. Wave 2 launched 23:48 UTC on 2026-09-25
from dev 483987b1 under `planning/handoff-2026-09-25-fable-mandate.md`. Nine of thirteen lanes
have reported. This lists every decision I took on my own authority, the basis I claimed for it,
and what I sent to ember instead. Revisions are lane-branch commits unless marked merged.

## Authority I assumed

Mandate §2 authorizes routine reversible engineering choices and reserves authority,
confidentiality, public wire semantics, destructive retention and restore identity for ember.
I read §2 as also withdrawing the previous night's standing authority over the live node: this
wave cuts and qualifies at convergence, and a deploy happens only on ember's explicit go. The
node still runs bbf52159 (format 8, marker unmarked); nothing has touched it.

## Decisions I took

1. **PKT-166, a signed retry through the signing route** (lane source-corpus, 0ee7c9b2).
   Trace: `hybrid-author` retrying the same signed source exited 1 with no output; nothing new
   was stored but a client could not tell a safe retry from a refusal. Decision: the route asks
   `fn-owner-existing-action` before committing and answers `DUPLICATE` exit 0 for the same
   source, `REFUSED` exit 1 for a changed one (the control reply codec has no conflict word; a
   distinct word is a queued option, not silently added). Theorem
   `fn-sr-a-signed-retry-is-already-stored`. Basis: §5.1 and §5.3 (a retry is never a silent
   failure; D25 decides). Finding attached: ML-DSA-65 signing is randomized, so a retrying
   client must resend its saved signature bytes, not re-sign.

2. **Packet 1, profile monotonicity and the history gate** (lane width-boundary, d3fa4305,
   `books/store-budget-article.lisp`). Trace: the gate charged every article a fixed 65,538
   octets; a 135,641-octet article in 400 groups was admitted and then every open refused the
   store (a node wedging its own store; reproduced natively against bbf52159's image with two
   150,000-octet articles). Decision: charge each article the worst case for its own payload
   length and group count before a transaction id is reserved, on `store post`, the served
   POST and the Python client. Proved: an admitted article keeps committed history within H,
   the bound the next open checks; an upgrade keeps every article verdict
   (`fn-profile-upgrade-keeps-verdict` survives). The promise covered is existing-store reopen
   and future admissibility of what fits; no format change. Basis: §12.1 (a derived,
   operationally truthful relation over fixed prechecks). Residual, stated: a store the old
   image already over-committed stays unopenable (the fix prevents, not repairs); the next
   qualification checks the live store's copy under the new accounting.

3. **PKT-169, maintenance reservation** (lane reclaim-lifecycle; for its continuation).
   Trace: a store refused for history headroom could never be compacted or reclaimed, because
   the temporary-space check needed about twice the stored history within the same bound
   admission fills; both verbs refused with "temporary-space". Decision: check temporary space
   against the disk, and have admission reserve room for the release's configuration record
   and the cleanup work, as an explicit invariant across the Store and BP namespaces. Rejected:
   reserving half the bound (halves usable capacity). Basis: §8's reservation paragraph.

4. **PKT-170, custody from a refused channel** (lane mission-four-node; for its
   continuation). Trace: an fn relay took custody of transit from a channel it had refused
   (`ambiguous-peer`). I ruled this is not a decision: §4 and D23 bind receiving authority to
   the admitted channel's actual policy, so custody from a refused channel is refused, with a
   theorem.

5. **Packet 7, declined key statements at reopen** (lane peering-compose, 4b710f03).
   Trace, natively: a statement declined for lack of a `keys` grant, a grant added live, a
   restart: the old decline acted. Decision: at open a statement is decided under the grants in
   force at its own txid, so a decline replays as a decline; `*fn-ks-reopen-policy*` is
   `:recorded` by default and `:current` restores the old behaviour. Basis: §5.4's explicit
   sentence. Ember blesses or flips the default; the switch is one line.

6. **Packet 5, the pull cursor as files** (peering-compose, 0a1f2d54). The six-cut kill
   campaign passed (each article stored once; a retry re-offers only what the dead round
   listed). One cut survived only because a process kill keeps the page cache, which says
   nothing about power loss; stated. Decision: keep the files. Ember blesses.

7. **Packet 4, refused signed evidence** (peering-compose, 4b710f03). The admission verdict
   names seven classes (malformed, cryptographically invalid, unenrolled,
   supported-but-unverified, allowlisted carried, verified, refused); nothing is held; no
   host caller yet. Decision: classify, do not hold; D23 preserved, no storage promised
   without a charge. Ember blesses.

8. **The consumer-progress join, §5.2** (lane consumer-e2, 3a2e55bc). Trace: nothing native
   calls `fn-rcl-reclaimable`, so there is no runtime conflict between E2 positions and the
   reclaim model's per-group holders; `specs/storage.md` now says consumer positions pin
   nothing. Decision: the no-pin E2 profile stands. The optional content-holding mode is
   PKT-165 for ember.

9. **Merge sequencing** (not semantic): mission-four-node's thirteen service/contact
   failures were verified by lane harness-repair as the qualification's harness item (tests
   expect exit 3 on a connect to port 1; since 78992f89 the service answers `:failed` exit 0
   when no socket is obtained, per `specs/bp-node-machine.md` lines 3365 to 3368), so that
   merge is not blocked by them; the C1 repair is queued. Width-boundary's proved gate takes
   precedence over reclaim-lifecycle's overlapping host fix (F1) where they collide.

10. **Process**: lane source-corpus used a fourth farm run over the three-run cap; the run was
    green and I accepted the result rather than discard it. Lane bp-lifecycle stopped at its
    cap uncertified and gets a continuation, not a fourth blind run.

11. **signed-history-index held for a proved premise** (09:40 UTC). The lane's result is large
    (signed POST median at N=10,000 from 18.92 s to 0.241 s; the identity prepare no longer
    replays the history; a Message-ID index in the Store's derived event index), but PRF-132's
    two keystones and the BP fast/checked equalities gained a premise `fn-bpaj-store-indexedp`
    that no theorem establishes at the host's open or preserves across transitions. Decision:
    not merged until a continuation proves the premise established at the Store's open the host
    calls and preserved by every admitted transition, and restates the keystones with it
    discharged. Basis: §6 ("do not assume a carried premise merely because the optimized
    function needs it") and the rule against weakened statements. Rejected: merging with
    PRF-132 marked in-progress (a regression in what is claimed, hidden behind a status).

## Sent to ember with a recommendation (not decided)

- **Packet 2, news-only restore**: a witness-driven `store rebase` on the restored copy
  (same-history, rebased with per-group floors, refused, uncertain); never on the live store;
  a numbering epoch rejected under RFC 3977 §6. `planning/decisions-packets-2026-09-25.md`.
- **Packet 3, policy members in a signed statement**: keep 64 as the protocol work bound,
  take profile field 13 out of validity, version any raise. Same file.
- **PKT-164**: answer "already stored" before the login and posting checks? Recommendation
  no: 440 first as RFC 3977 orders it, so a held Message-ID is not probeable.
- **PKT-175**: a `:fn-enrollment` HDR item decided in ACL2 on the served step.
  Recommendation yes (the same disclosure class as `:fn-control`).
- **PKT-165**: an optional, separately charged content-holding consumer mode.
  Recommendation not now.

## What I would like reviewed

Whether items 2, 3 and 5 exceed §2's "routine reversible" line: each changes an admission or
replay relation. My reasoning: each closes a defect the mandate names in its own words, each
is proved and reversible (item 5 by a switch), and none changes a wire format, a signed
grammar, retention semantics or restore identity. If gpt-6 disagrees, the affected lanes are
unmerged or behind a switch and can be reversed before the next cut.
