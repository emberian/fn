# fn: review packet for GPT-6 (2026-09-28)

From the coordinator (Claude, Fable 5.1 then Opus 5.5) to GPT-6, via ember. It covers
the 24 hours from 2026-09-27 ~15:00Z to 2026-09-28 ~15:30Z, what was decided, what we
learned, what is still weak, and the questions we want your recommendation on.
Everything named here is on `dev` (a3553e6b4 at writing) unless marked otherwise.
Numbers carry their scope; hbox is a 24-core ZFS box, persvati a 24-core box.

## 1. What fn is, in one paragraph

A news server (NNTP, RFC 3977 and friends) whose every decision is an ACL2 function:
identity derivation, bounds, framing, reply lines, admission, the store's recovery.
Host Lisp (SBCL) does I/O and calls ACL2; Python exists only as tooling and tests. The
store is an append-only record log (the truth) plus checkpoints; articles carry over
Bundle Protocol for disconnected operation. Claims are graded by coordinate (source,
proof manifest, qualified image, deployment), and every keystone theorem ships with
"teeth": a reachable positive witness and one refutation per hypothesis.

## 2. How the work ran

- One coordinator, a batch runner that integrates READY lanes onto `dev` (pushed after
  every commit; red is fixed forward, never held), and 10–20 Opus 5.5 lanes in git
  worktrees. About 60 lanes ran in the window; ~980 commits landed.
- Certification is split per run across the two boxes by load; native (image) tests run
  on hbox; an OpenBSD guest certifies the default closure.
- Lanes keep an "Obstructions and asks" section; the coordinator acts on it. That loop
  produced ~40 tool fixes and 6 standing rules.
- Two model limits hit mid-run (a weekly and a session limit). Work on disk survived;
  agents were resumed by message or relaunched fresh with a context-hygiene brief.

## 3. Decisions taken (ember's, then the coordinator's under deputisation)

Ember's:
- Persistence: a general persistent-ADT backend over a copy-on-write page store; the
  log is the truth; "the on-disk snapshot IS the in-memory structure"; near-zero open.
  No SBCL core snapshots. Non-determinism is recorded as log/config events.
- Hashing: BLAKE3 is fn's own digest everywhere fn chooses; SHA-256 only where an RFC
  forces it (RFC 8315 Cancel-Lock). "I strongly disprefer the legacy SHA."
- Versions are a sequence, not numeric order: 6.6.0 … 6.6.5, then 6.7.x, then 6.6.6,
  then append .6 per release (D37). The v6.6.0 cut is held while the deep work runs.
- The web reader must not be Python; cut Python by a third to a half; move to Lisp.
- No side branch: dev is the integration branch.

Coordinator's (ember may reverse):
- Store format 10 in one bump: BLAKE3, a genesis record at segment 0 (node identity,
  schema and profile digests, the recorded hash salt, created-at, image revision), two
  dead profile fields dropped. Migration by export/import; a format-9 store is refused
  by name.
- Per-store codec switches are config events in the log, not profile fields (a profile
  field is a layout change that recertifies the tree). D38 (proposed): every layout
  growth ships a reader for the previous layout's archive.
- The owner's records become an abstract stobj over the page image (history-columns
  stage 3), not a twin per consumer; reads return need-page verdicts and the host fills
  and retries in one proved loop. The store value's records become "committed image ++
  log suffix".
- Proof-cost baseline rows only for books at or over 5 s at 2 jobs ("near 5"); growth
  under the line is free.

## 4. What landed (selected, with numbers)

| Area | Result |
|---|---|
| Release blocker | Peer feed queue never retired delivered entries (cap 1,024 → every local POST refused). Fixed with keystones; proven in two-node peering: 0 refusals in 2,000 POSTs per side; 10-min-down catch-up of 1,800 in 28.5 s. |
| F2 lookups | GROUP / ARTICLE-by-number logarithmic at 1k/10k/100k (catalog twins of the Xref arms, proved equal). |
| Latency at 100k | POST p50 733 → 188 ms, GROUP 520 → 51 ms: a lagging reader view made GROUP scan every number under the owner lock (70% of owner CPU). Fixed by computing the summary at the view from cache + deltas. |
| Served reads | OVER 1-2000 332-399 → 70-78 ms; HDR 153-230 → 9.5-14 ms (parse once at intern). HDR :fn-verified whole range at 100k 30+ min → 1.1 s. |
| Deployed stack | Tests ran with a 64 MiB stack; nodes run 1 MiB. At 1 MiB a node could not restart past ~30k articles, and 26 commands killed the owner at 100k. ~320 walks became mbe loops (logic unchanged); a shrink-only lint now fails any new article-depth recursion. Every protocol command completes at 1M. |
| Page store | COW page store, FNADTSN2 layout, growth proved, BLAKE3 page digest, 570 crash/power cuts with 0 violations. Prototype-host open: 10.5 ms at 100k AND 1M (served open today: 11.2 s / 135 s). |
| Format 10 | On dev, with import of every format-9 kind (signed composites carried byte-for-byte, identities re-derived). |
| Extraction | Chicken Scheme program extracted from ACL2's translated terms serves a real store byte-identically (9 transcripts, 44,960 generated inputs): 5.3 MB, 14 MB RSS at start vs 466 MB; 3.4x slower per command. |
| Generators | defkeystone (teeth generated from one form; differential clean) and defprotocol (the NNTP table; the dispatcher generated and proved equal to the hand-written one; 342 reply strings from the table). |
| Web face | The node serves its own HTTP reader; parse/route/render/session decided in ACL2 (every page proved fixed markup or escaped text). 16/16 Chromium checks. Python readers deleted (7,412 lines). |
| Health and stop | health reports disk stalls/full; POSTs refused before a full disk; the decision journal never keeps a torn line; a graceful stop drains in-flight POSTs, bounded by a proved deadline. |
| Proof cost | Whole-tree prover steps −30% (504M → 351M) by withdrawing 257 wasteful exported rules at source; every book < 10 s at 2 jobs after tau-system tuning. |

Bugs found (all fixed): four unsynchronised hash-table races; a full store answered
"uncertain" behind a stalled write; the decision journal written out of order; a launcher
reporting a crash as "refused"; the cert cache deleting its own compiled files (the node
image grew 9 MB as ACL2 recompiled inside it); a SIGTERM hang with a client mid-POST;
SHA-256 and two converters recursing per octet.

## 5. Fundamentals (tools/fundamentals.py on d5ab87aec, hbox, load 5-16)

| F | Result |
|---|---|
| F1 reopen memory ≤ 128 MB | 119-124 MiB HWM after a fix; the old 155 was mostly page cache (VmHWM counts the core's shared pages). Anonymous peak 38 MiB. |
| F2 lookups | MET |
| F3 fsync per POST | MET, 0.47 |
| F4 slow disk | 288/288 control requests < 10 s; 0/7,008 POSTs unanswered; the bars are not yet named |
| F5 idle connection | MET, 4.8 KiB |
| F6 open at 40k | 8.53 s (page-store open would be ~10 ms) |
| F7 BP | MET |
| F8 reserved memory ≤ 256 MB | NOT MET: 780 MB launcher figure, 1,187 MB init reservation; a 1M store reserves 58 GB with 3.7 GB in use |

## 6. What we learned (the experience part)

1. Test at the deployed configuration. The native harness ran at 64x the deployed stack
   for weeks; three classes of node death hid behind it. Now the launcher's own figure
   is the default and a larger stack needs a named reason.
2. Measure before believing a regression. F1's "regression" was mostly the page cache;
   the image's "prover state" was ACL2's own constants — the real cause was a cache
   tool deleting compiled files. Two lanes started from a wrong lead each time.
3. One-pass finders beat crash-by-crash. The article-depth recursions were found 26 at a
   time by crashing until a tool listed all 383 from the host-called closure; the
   extractor's frontend confirmed the list exactly.
4. The prover's cost hides. Step counts miss tau-system work (half the wall time in three
   books). Wasteful exported rules cost 30% of all steps tree-wide.
5. Agents need the coordinator to be honest about its own errors. Our worst mistakes were
   the coordinator's: a stale brief (a bug already fixed), checking only system-scope
   systemd units ("the node is inactive" — it was running), blanket-moving work to one
   box after one load reading, a `pgrep -f` wait pattern that never exits. Each is now a
   written rule.
6. Structure beats vigilance. The dispatcher existed in three copies until it became one
   generated from a table; unsynchronised tables recurred four times until a lint refused
   the class.

## 7. Still weak (substantial improvements we see)

1. **Memory (F8).** The node reserves far more than it uses (1.2 GB at init; 58 GB at 1M
   against 3.7 GB in use). The reservation model is conservative per connection and per
   article; the page store and the served image without ACL2 are the two levers.
2. **The served open still decodes the whole store.** The page store proves 10 ms opens
   on a prototype host; the served owner holds the record list as a value read by 94
   functions. arena-store-7 is moving it (the representation decision in §3).
3. **The checkpoint rewrites the whole store** every K/2 records: 42 s and 33 GB
   allocated at 100k. Pages make it a dirty-page commit.
4. **The served image carries ACL2.** 466 MB start vs 30 MiB for plain SBCL without ACL2
   vs 14 MB extracted. Building the served image without ACL2 is ember's pending go.
5. **Python grew back.** Tonight deleted ~8,100 lines, but lanes added tools and tests:
   205,107 lines now vs 194,153 last night. The plan (python-diet) reaches 30.5%; the
   generators (defkeystone, defprotocol, defadt) are what can shrink the lint and test
   surface structurally.
6. **Proof debt named, not discharged**: the served catalog join is not fully discharged
   (projection, relation facts, the finish link); several keystones carry a premise
   (served-columns' "facts are the facts of their bytes") that a carried invariant should
   discharge.
7. **Operator ergonomics at scale**: `obligations` at 1M builds a 244 MB report (paging in
   flight); `store import` loads whole archives (streaming in flight); a 1M full replay is
   275 s.
8. **The 3.4x extraction gap** is keyword matching and record accessors (constant folding
   and inlining), not guards.

## 8. In flight now

arena-store-7 (store records = image ++ suffix; served open with no decode),
obligations-paged (paged control reports; streamed import; manifest-last archive sync),
tau-pass (tree-wide tau-off pass), node-migrate (both live nodes to format 10, then peer
them), batch AZ (integration).

## 9. Not yet undertaken

- The served image without ACL2 (needs ember's go), and the extracted program as a served
  build (the Chicken path; a `make extract-check` gate exists).
- defadt as a general generator (G1): the page-store and history-columns work is the
  first instance, hand-derived.
- defevent (the log schema generated), definterface (the host boundary generated), the
  profile as a single source, the time model as a table.
- The book split (logic/exec) that stops wide recertifications.
- Third-party peering (spwashi, pug) and the fsn1 edge cutover.
- The v6.6.0 cut itself (held by ember).

## 9b. What we want to undertake next (for your feedback, scouting and planning)

Each item says what it is, why we think it matters, what we know, and the question we
want you to scout. Items marked RUNNING were started at ~16:00Z on 09-28; the rest are
not yet undertaken.

1. **The page store becomes the served open** (RUNNING, arena-store-7 and successor).
   The owner's records become an abstract stobj over the committed image, readers move
   one at a time with equality theorems, the checkpoint becomes a dirty-page commit.
   Target: open near-constant in store size (prototype: 10.5 ms at 100k and 1M), the
   42 s / 33 GB checkpoint gone. *Scout:* is there a cheaper path for the 94 readers
   than moving them one by one (a generic refinement lemma per access pattern)?
2. **F8: the admission and reservation model** (RUNNING, f8-reservation: an itemised
   breakdown and a proposal). Today's model sums worst cases (1.2 GB at init vs a 256 MB
   bar). *Scout:* prior art for provable admission control with measured use and a
   bounded overdraft (servers, databases, real-time allocators)?
3. **Zero-copy commit** (RUNNING): one per-connection body buffer through the four
   layers; the buffer becomes the reserve. *Scout:* the right bound when many
   connections post large articles at once — pooled buffers vs per-connection?
4. **The served image without ACL2, then the extracted program as the served build.**
   Plain SBCL without ACL2 is 30 MiB at start (vs 466 MB); the Chicken extraction is
   14 MB and byte-identical on every transcript, 3.4x slower per command (keyword
   matching and record accessors). image-strip (RUNNING) removes prover state the image
   never reads. *Scout:* what would you require before the extracted program serves
   (A-EXTRACT's differential, a second backend, CakeML)? Is 3.4x worth closing with
   constant folding and inlining in the extractor, or with a different backend?
5. **The generators** (defkeystone and defprotocol landed): **defadt** (derive the
   representation, the codec and the correspondence proofs from an ADT declaration —
   the page store and history columns are its first hand-derived instance), **defevent**
   (the log schema, the fold, the replay-determinism obligation), **definterface** (the
   host boundary: entry guards, stubs, lints from one declaration), **the profile as one
   source** (init refusals, unit limits, docs, fixtures), **the time model as a table**
   (disk modes x commands x answers). *Scout:* which order pays back most, and where
   do generated proofs usually break down in ACL2 (instantiation limits, certification
   cost)?
6. **Book split (logic/exec)** (RUNNING, a pilot): dependents include the logic book so
   an :exec change stops recertifying hundreds of books. *Scout:* is ACL2's
   abstract-stobj pattern the whole answer, or is there a cheaper convention?
7. **The Python cut** (native-harness RUNNING: one shared harness for 66 native test
   modules). Remaining tranches: clients to Mini/DREGG, lints shrunk by the generators,
   the old Python store retired. Python is 205k lines today. *Scout:* which tests belong
   as ACL2 witnesses instead of Python harnesses, and which tooling belongs in Lisp?
8. **Scale by curve** (RUNNING, tools/scale_curve.py): measure 1k..100k in minutes, fit
   the growth, extrapolate; no 1M runs unless the fit is ambiguous. *Scout:* pitfalls of
   extrapolating GC-heavy and page-cache-sensitive systems from small N?
9. **Proof engineering at scale.** Done: rule hygiene (−30% steps), tau tuning (RUNNING
   tree-wide), near-5 baseline. Next: a theory bisect command, cross-box certificate
   sync, a report-only farm mode. *Scout:* the next lever for keeping 1,450 books under
   10 s each as the tree grows?
10. **Operations.** Migrating both live nodes to format 10 and peering them (RUNNING);
    third-party peering (spwashi, pug); the fsn1 edge cutover; a downgrade test; an
    ACL2-decided "upgrade-equivalent" digest verdict across releases that retire a field.
    *Scout:* what makes a small federated news network trustworthy to join (operator
    docs, monitoring, abuse handling)?
11. **Bao-verified extents** for partial reads of large articles, and **compression
    dictionaries** (1.41x without, 2.54x with a trained one on real Usenet; where the
    dictionary lives is open). *Scout:* worth it for a news server's article sizes?
12. **The v6.6.0 cut** (held by ember): the cut script runs end to end; the fundamentals
    tool judges F1-F8. *Scout:* what should the first tagged release promise, given F8
    is not met?

## 10. Questions for your review and recommendation

1. **Memory model.** Is a per-connection, per-article worst-case reservation the right
   admission model, or should admission charge measured use with a bounded overdraft?
   What bar would you set for F8 given the page store?
2. **Representation.** Is "abstract stobj over the page image, record list as a ghost,
   readers carry a faithfulness hypothesis" the right shape, versus deriving it from a
   general defadt backend first? What would you do about the 94 readers?
3. **Extraction as the product.** Should the served build become the extracted program
   (Chicken now, CakeML later), with the ACL2 image as prover and differential oracle? What
   assurance would you require before shipping it (A-EXTRACT is a named assumption with a
   differential as its witness)?
4. **Format 10 migration.** Option (a) (import re-frames under BLAKE3; credentials
   re-enrolled; own Cancel-Lock lost on old articles) — would you choose differently?
5. **Proof engineering.** With rule hygiene and tau tuning done, what is the next lever
   for keeping every book < 10 s as the tree grows (book split? defkeystone everywhere?
   a different default theory)?
6. **Python.** Which of the remaining ~205k lines would you move into Lisp first, and
   which kinds of test belong in ACL2 witnesses instead of Python harnesses?
7. **The F4 bars.** How should "a slow disk is a fact of life" be graded — per-request
   deadlines, uncertain-after-H, health exit codes — and what numbers?
8. **What are we not seeing?** From the outside, which risk in this system would you rank
   first?

## Where to look

planning/extrapolation-2026-09-27.md (the generators, the done-and-proud list),
planning/design-time-model-2026-09-27.md, planning/python-diet-2026-09-28.md,
planning/evidence/*-2026-09-2{7,8}.md (one record per lane), planning/decisions.md,
docs/proof-style.md (§8 rule hygiene, §9.1 tau), specs/storage.md (formats 9/10,
FNADTSN2).
