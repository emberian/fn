# fn2 convergence, 2026-10-31 evening (main; present state; the base for Gemini's turn)

Ember: "let's get our subagents converged and landed, and stop spawning more follow-up work; I would like to give Gemini a turn." Every seat was told: push what is green, commit nothing half-done, rewrite its notebook as present state with its exact next step, one-line READY, stop. This note is the state at that point. The seats' notebooks (`lanes/*-continuation.md`) hold the detail; `STATE.md` holds the day's log with shas; `REVIEW-REQUEST-20261031-ARGON.md` and `REVIEW-ARGON-RESPONSE-20261031.md` hold the review and its disposition.

## The tip
`origin/dev` at `71a9f55bc` (B's last landing; all seven seats converged and stopped). 91 commits on dev today before the convergence landings, none reverted.

## What serves (the measure)
- 14 NNTP verbs: CAPABILITIES HELP QUIT MODE DATE AUTHINFO XREDEEM, and the cursor's GROUP, LISTGROUP (named and bare), NEXT, LAST, STAT, OVER/XOVER, plus LIST ACTIVE/COUNTS/NEWSGROUPS without a wildmat. 16 interim rows: D6 10 (LIST's wildmat and remaining variants, NEWGROUPS, NEWNEWS, ARTICLE, HEAD, BODY, HDR, XHDR, XPAT, XFN-ZARTICLE), D5 3 (POST's success, IHAVE/CHECK/TAKETHIS), D7 1, E2 1, E4 1.
- Both harness carriers (simulator and socket) run over one shared seeded store and judge the cursor's own replies; the Xref red the first such run found is fixed (48305081a). H's both-targets line at that tip: 0 disagreements on both carriers (28,657 served replies each; 16,768 connections judged ok).
- M2 cuts: 0/12 (no consumer verb serves yet; the line prints it on purpose).

## What landed today, by brick
- **The form:** G2 (the ports' language), the arm tuple per arm, P4 (a kind proves its own admission and take in its own book), one shape theorem per generated function (the cursor 1,339 → ~90 s), the `:local` listener with uid/gid, the turn's work bound from the registry (the Argon defect), G3 1/n and 2/n (paths, holds per path, typed links, inner machines, phase-valued fields, `:repeat` cost derived). Open in the form: the park step's named formals, the `:do`-chain auto-split, the assembly's per-child books, the per-kind run rewrite, the listener's registry arms and outbound Connect.
- **B:** the event envelope in the record header; B-S2 the transaction member with the block read ops and the stream-wake hook; the three B-S2 keystones; the section split; the control-connection rows; the Argon rulings (the draining posture, one encoding of a transaction, geometry binds the hash context). Open: the record kinds extended to C's list once `fn2-successor-emit` names them; `:child` bodies on admit-txn and txn-source with the commit port.
- **C:** the published frontier; `:answers` and `:child` on its read ops; `:unless-when :unchanged`; the §4a identity records with the two-lookup decision and the transaction switched onto them; the overlay default raised to 48 with the reason; the tip-scan invariant enforced by unstaging; E's `fn2-consumer-names` and `fn2-successor-stream-member`; the capacity numbers and the minimal C5. Open: `fn2-successor-emit` (D's exact form, the one-encoding workspace emitter), `:child` bodies on the thirteen ops the txn calls, the concrete profile's pool class for C's arenas (the profile's owner).
- **D:** the cursor (the first kind in child form), the LIST verbs, the seeded reader session, the Xref fix, D7 4/n-a (the ledger's requests, the grant source with liveness proved, the principal id with uniqueness proved), ranks from list position, the request-park `:child`, the read-rows seam for E. Open: **the transaction port and the durable POST** (the whole design in d-continuation.md; waits on C's emit and B's posture as two `:do` steps; generates in core form until the callees have `:child`), OVER by Message-ID, D6 3/n (ARTICLE/HEAD/BODY over the location field and the block read), the conn port on G3, the `:consumer` mode's two inputs it has not asked for yet (E's `fn2-cns-post-outcome`, C's `fn2-consumer-cursor` schema as the fold stands).
- **E:** the consumer port statement, the port form, the codecs over fn1's bytes, the peer model in wire words, the edge table reworked after D's review and registered as a core child, the CONSUMER checker and scenarios with K10 stated, the Argon rulings. Parked until the transaction port; the machine paste is designed (E.P1) with every input on dev but the port, D6 3/n and the two C schemas (now landed).
- **H:** the laptop nightly, the interim table as the served-surface measure, the M2-cuts line, the seeded carriers, the model corrections. Standing by on events.
- **The Lean metatheory:** the registry aligned to the forms; 2,354 ACL2 functions read into Lean; the step and expression readers independent of the generator; the measure equal on every recorded call (probe 31, echo+scribe 963, cursor 582) with the frame check; two generator defects and two interpreter defects caught; PW3 stated with its generic lemmas; the re-record at 48305081a running unattended on hbox (`~/fn2-probe/build/rr.pid`, `rr.done` when finished). Held: the per-arm proofs, pending E2.

## Measured facts a reviewer should carry forward
- Installed runs at the concrete profile: 64 rows shared by every schema, one per frozen overlay, so they run out after six to eight POSTs; the sealer then answers `:full` and the core stops `:sealer-full`. The minimal C5 (a size-tiered sealer merge over at most eight live runs of one schema, `:identity-runs` to 512) precedes any helm run and now sits on the spine right after the durable POST.
- Each sealed run keeps its pages resident in 64 KiB slots; that pool class runs out before the run rows do.
- A POST writes 8-10 schemas; a batch takes one overlay per schema; the overlay default is 48 and each overlay in use holds an arena from the pool, so the concrete profile needs a pool class for C's arenas (48 × 64 KiB, or 4 KiB arenas plus 48 × 4 KiB).
- The certify cost of a guard proof over a chain of thirty calls is combinatorial; the fix every seat now applies is disabled helpers per step.

## Decisions open for ember (from the Argon review)
- **E1, seat topology:** Argon proposes three vertical seats plus one; main recommends merging E into D's seat once the transaction port lands and keeping the form seat, B, C, H and the Lean seat.
- **E2, the Lean direction:** typed Lean emitted from the declaration forms with operation bodies in a declared typed subset, the reader kept as the measure's oracle, PW3 re-aimed at the wrapper; LEAN-METATHEORY §9.6 states both directions with costs. The Lean seat holds its per-arm proofs until ruled.

## The order from here (BRICKS §5, present state)
1. C's `fn2-successor-emit` and B's `fn2-commit-posture` (both to D's exact forms, in the notebooks).
2. D's transaction port and the durable POST, posting advertised; the D5 rows leave the interim table.
3. The minimal C5 (C), before any concrete-profile run.
4. OVER by Message-ID, then ARTICLE/HEAD/BODY (D6 3/n).
5. E's consumer machine pasted and driven in the simulator (M2 cuts n/12), then over the local socket: M2.
6. The conn port on G3 (deletes the 822 s book), the rest of G3, the assembly's per-child books.
7. Behind M2: the peer path, TLS, credentials, B6 and replay, peering, BP, operator verbs.

## Boxes and nightlies
hbox's `/` and `/othersys` were at 40-41 GiB free when B checked (under the 60 GiB line the seats stop at); ember decides what goes, nobody deletes.
forge (measurement; the fn2 nightly at 10:00 UTC with the fixed script), hbox (certifies; the Lean re-record running), persvati (approved tonight for fn2 certifies; its `/tank/fn` toolchain to be qualified first; reachable from the Mac as `persvati-remote`), the Mac (REPL and `lake build` only; H's nightly at 03:30). Every live job has a PID file in its clone's `build/`.

## Convergence READYs
- E: parked, clean at 4a644101c, nothing running.
- Lean: green at 9146c1874; re-record running unattended; nothing committed half-done.
- C: c65141708; emit not started; stopped.
- D: df9be72b5; no port code; stopped.
- B: 71a9f55bc; `fn2-commit-posture` (S11) on dev as a computed read op with `:answers (:serving :draining)` and a control in commit-txn-unit; B-S2 checks green over C's §4a; `fn2-commit-take` has its `:child` (admit-txn and txn-source come with the commit port; the posture's child form is the form seat's call: the commit table joins the txn's tuple or the posture becomes a directory column). S12's record kinds wait for C's emit. Clean, equal to dev, nothing running. Stopped.
- Form seat: ef5e1b992 (G3 3/n: `:genesis` arms run by the executor's init, the scribe's `:refused` phase with zero per-path findings, per-output facts as rule classes of the one shape theorem, the park-taken `:child`, F9's owner = holder lemma proved; cursor 98 → 69 s, executor 100 → 74 s on hbox; G3 2/n's forge numbers in MACHINE-FORM §6.10). Not landed: the shape-theorem adoption in C's `fn2-idc-op-shape` (stage 119 → 71 s), kept as `lanes/form-c-op-shape-adoption.diff` for C to apply over its newer successor; the park step's named formals are the exact next step. Stopped.
- H: 9eceead5f; the both-targets line at 48305081a: M2 cuts 0/12; 14 verbs served; 16 interim rows; both carriers 28,657 served replies, 0 disagreements, 16,768 connections judged ok, over the seeded store. Stopped; the 03:30 cron stays.
