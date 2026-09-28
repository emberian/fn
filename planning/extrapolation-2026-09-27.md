# fn at the end of 2026-09-27: what is partial, what is unlaunched, what metaprogramming collapses

Written by the coordinator (Fable 5.1) at 23:10Z on 2026-09-27, at ember's ask:
"think back to everything that got launched that failed for lack of agent
slots, and anything else we talked about ... a coherent extrapolation ... what
still remains partial ... or could be massively simplified AND improved via
metaprogramming". This file is tracked so it survives the coordinator's
context. Heads and ids age; verify with `git log` and the lane LANEDUMPs.

Counts below are from batch/ay at 4c3ea3c4a (21 READY lanes over dev
18a7137a3) and are stated to show scale, not as gates.

## 0. Where the notes are

| What | Where | Tracked? |
|---|---|---|
| The day's handoff: decisions, live agents, the live node, prototype verdicts, open work | build/coordinator/HANDOFF-2026-09-27-evening.md | no (build/ is ignored) |
| Per-lane rows, newest first, every result and decision | build/coordinator/WAVE-STATE.md | no |
| Closeout rules every lane reads | build/coordinator/queue/closeout-common.txt, BRIEF-COMMON.md | no |
| The time/event model design (F4) | planning/design-time-model-2026-09-27.md | yes |
| The first cut's plan and gates | planning/release-v6.6.0.md, planning/release-sequence.json | yes |
| Decisions D25 to D37 | planning/decisions.md | yes |
| Lane records (measurements, findings) | planning/evidence/*-2026-09-27.md, some still in build/lanes/*/planning/evidence/ | yes once merged |
| Prototype records (adt, pagestore, extract, runtime floor) | the lane/proto-* worktrees under build/lanes/ | branch only |
| The public node runbook and deploy record | planning/runbook-public-node-2026-09-27.md; evidence/public-node-deploy-2026-09-27.md (in batch/ay, code redacted) | yes |
| Astra's upstream reply (unsent) | ~/dev/minidregg/docs/FN-UPSTREAM-REPLY-2026-09-27.md | other repo |
| Claude memory pointers | ~/.claude/projects/-Users-ember-dev-fn/memory/fn-state-2026-09-27-evening.md | no |

The gap this file closes: the handoff is not in the repo, and no single tracked
file said what is partial across the whole system or what should be generated
instead of written.

## 1. What is happening right now (23:10Z)

Ten lanes (Opus 5.5) and one batch runner. The batch runner holds 21 READY
lanes (247 commits) on batch/ay and is authorised to push dev at the first
green tranche (both boxes plus the OpenBSD guest); the live lanes go in the
next tranche.

| Lane | Doing | Blocks |
|---|---|---|
| batch AY | merging site-newsgroup; certify; push at green | every landing |
| feed-queue | RELEASE BLOCKER: peer feed queue never retires delivered entries (cap 1,024), then every local post gets 441; `obligations` stack death near 1,029 | v6.6.0, peering |
| release-machinery | cut script gates 09/13/04, tools/fundamentals.py; tarball test in the VM | the cut |
| sca-join-5 (replaces sca-join-4, done 23:12Z) | F2 lookup counts: catalog arm before Xref, re-pin without the archive walk; then the discharge residue | F2, F8 |
| served-columns (+2 forks) | parse once at intern; OVER from columns; records.lisp double check; second parse; verify-once | served cost, 1M replay |
| digest-native | native SHA-256 attachment; hash-once; BLAKE3+Bao prototype | replay walk, extent digests |
| log-leftovers (+slow-disk) | M5, reclaim event, IHAVE 436 while slow, DTN build | time-model slices 3+ |
| arena-store-finish | three check-lane findings, page 0 in the model, the m5 brief | arena-store-2 |
| public-node-3 | D1 AUTHINFO after STARTTLS, D3 cert-sync first run, D4 branch default, account delete, docs-login narrowing | node hygiene |
| host-lints | host_check rule for unsynchronised globals; the three-copy reader dispatcher | a class of races |

## 2. What remains partial, by subsystem

Legend: LANDED = on dev; BATCH = in batch/ay, not pushed; FLIGHT = a lane owns
it; PROTO = proved on a lane/proto-* branch, not in the served path; OPEN =
nobody owns it; EMBER = a decision.

### 2.1 Store and persistence
- Format 9 record log, arena off-heap, paged arena, checkpoints over the log,
  streaming open, compaction as checkpoint plus segment drop, recovery barriers
  proved minimum three. LANDED / BATCH.
- Log corruption: one flipped bit with valid successors is refused by name;
  torn tail recovers; repair verb with quarantine. BATCH.
- Copy-on-write page store (LMDB shape, one barrier, root slots inline, fork =
  new root): m1 to m4 and m6 done on lane/arena-store; three check-lane findings
  and page 0 in the model are FLIGHT (arena-store-finish). Books live under
  books/, not proto.
- fn-hist on pages (FNADTSN1 layout). OPEN: arena-store-2. This is the step that
  makes "the on-disk snapshot IS the in-memory structure" true for history.
- Per-record state to defadt columns (target at most 200 bytes per record;
  today reserved 586 to 887 MB against the 256 MB bar). OPEN; depends on
  arena-store-2 and the defadt generator (section 3, G1).
- The next format bump bundle: the reclaim event (PKT-857), dropping profile
  fields 1 and 14 (meaningless on format 9), and the genesis event that records
  seeds, nonces and salts at position 0. OPEN; ember said one bump for all three.
- Compressed records: the ACL2 half is BATCH (compression-extents); host wiring
  and vendoring lz4 are OPEN (compression-extents-2); dictionary persistence is
  EMBER.
- Replay determinism: proved by test on dev (fold identical across boxes and
  across checkpoint versus replay). LANDED. Remaining non-determinism sources:
  the checkpoint carrying the image revision (compare table digests instead) and
  reclaim's unrecorded clock (FLIGHT, log-leftovers).
- Whole-node check at open (M3, 0.6 s at 100k) waits on the column invariant.
  OPEN.

### 2.2 Served path
- Entry guards: payload handle and octets are distinct types at every host
  call; zero waivers; the spec cache race fixed. BATCH.
- Parse once at intern, columns for the served header fields and NOV, OVER as a
  column scan, HDR/XPAT from the column, records.lisp's double payload check,
  the second served parse, signature verify-once. FLIGHT (served-columns).
- Zero-copy commit: the article body through the four layers in one
  per-connection octet buffer; the 383 MB per-connection reserve at the 11 MiB
  limit becomes the buffer size. OPEN.
- Reader dispatcher in three text-identical copies. FLIGHT (host-lints).
- Wire bounds after QUIT and on IHAVE/TAKETHIS bodies. LANDED (fuzz found them).
- Durability: served key statements acknowledged only after their barrier; EIO
  at the fence is uncertain, not a fault. LANDED.

### 2.3 Join, catalog, indexes (F2, F8)
- sca-join-2 and -3: join at every open and through both finishes. BATCH.
- sca-join-4 (reported 23:12Z, READY 1e748656c): steps 3 to 5 composed; the
  chain keystone no longer needs fn-scr-owner-catalogp (it takes the carried
  invariant fn-scj-invp, held at every open and kept by every host entry, the
  refresh, every connection arm, pinned readers, the article and identity
  finishes); a verdict-only refresh cannot move the view (no host fix needed).
  NOT discharged: the view archive's fn-nntp-projectionp, the finished owner's
  relation facts, the finish link and the rows' composite/clear facts (true on
  the T2 owner, not proved), the signed composite's two equations, fn-own-reopen
  and crash/recover. fn-midx not retired.
- F2 lookup counts NOT MET at N = 1k and 10k: GROUP and LISTGROUP make 2N to 3N
  number-table probes and walk the whole archive when re-pinning; ARTICLE by
  number walks the archive because the Xref arm runs before the catalog arm.
  Constant: OVER and ARTICLE by Message-ID. Logarithmic: the pinned-view
  bisection. Counter: FN_NATIVE_COUNT_LOOKUPS. → sca-join-5 (launched 23:15Z).
- Batch blocker found by sca-join-4: books/nntp-auth-fold does not certify on
  either box; fn-auth-fold-command-pinned-offers-only-post fails at peer-catchup's
  new XFNCATCHUP arm, which stops catalog-entries-tests and every T2 fixture
  book. served_cost still expects fn-orr-read-span (now fn-otm-read-span).
- history-columns-3 retired the event index. BATCH. Still counted against F8:
  the checkpoint's copy of the index (about eight books), fn-held-p at append
  (ACL2 forbids the correspondence to depend on an attached function; the
  workaround is in that record's section 9.4), the fn-own-relation witness.

### 2.4 Time, I/O and health (F4)
- The design (requests with one completion event; time as recorded events;
  barrier deadline 5 s, stall 30 s, clock event 1 s; disk modes ok/slow/stalled/
  failed/full; uncertain answers after the stall; 440/436/431 while slow; the
  decision journal). Written; slices 1 and 2 BATCH (time-model, time-model-2).
- Slices 3 and up: IHAVE/CHECK 436 while slow and the 440/441 reason. FLIGHT
  (log-leftovers, slow-disk).
- The F4-R and F4-W bars, the defaults as profile fields, and the health exit
  code while stalled. EMBER (proposed, not adopted).
- The decision journal moved to STORE/decisions/ (the record log's journal/
  broke a segment). BATCH.

### 2.5 Memory (F8) and the runtime floor
- Today's served image is about 90 MiB at start: 70 MiB of core pages, of which
  ACL2 accounts for most and about 9 MiB is ever touched. fn without ACL2 on
  plain SBCL is 30 MiB at start, 45 after 1k posts, byte-identical replies
  (191,423 recorded calls). PROTO (runtime-floor). Building the served image
  without ACL2 is EMBER (2 to 4 lane-days; needs an A-TARGET-COMPILER assumption
  row, a stack-depth test, and a ruling on non-guard-verified host wrappers).
- Thread stacks are 64 MiB each; size them to the proved recursion depth
  (PKT-693). OPEN.
- The 8 MB static Chicken binary (section 2.7) is the other floor.

### 2.6 Hashing
- fn-digest is a constrained attached function. digest-native landed the native
  digest seam with a startup self-check (READY) and vendored BLAKE3; ember chose
  BLAKE3 as fn's own digest (SHA-256 only for Cancel-Lock). blake3-digest:
  FLIGHT — the ACL2 definition, the attachment, the C library behind the seam,
  Bao for large extents, and the digest half of format 10.

### 2.7 Extraction (the target compiler)
- An extractor over ACL2's translated :exec terms with pluggable backends.
  Chicken: 1,572 functions, zero hand-rewritten, 35 shims, byte-identical
  replies on all nine transcripts, 113,958 guard-derived inputs agreeing on
  98.1 percent of functions, 95 checks erased by proved guards, 5.95 MB static
  binary, 8.4 MB RSS at start. PROTO (lane/proto-extract).
- Missing before it can serve: boundary guard checks (the one semantic
  difference), the two extent primitives (stubs), the A-EXTRACT assumption row
  in books/assumptions.lisp, wider guards-as-types (the 3.3x per-command gap).
  OPEN.
- ECL is dead (16 to 45x slower). CakeML (verified) and C with per-request
  arenas are future backends; what CakeML's input needs is in the record.
- N-version differential execution (SBCL versus Chicken on recorded
  transcripts) is the test that makes the extractor trustworthy without a
  verified backend. It exists as the prototype's check; it is not yet a make
  target. OPEN.

### 2.8 Release (v6.6.0)
- The version sequence (D37), VERSION 6.6.0, release-sequence.json and its
  tool. BATCH.
- The cut script gates 09/13/04 and tools/fundamentals.py (F1 to F8 judged by
  the tool, not by hand). FLIGHT (release-machinery).
- feed-queue. FLIGHT, blocker.
- The OpenBSD friend rehearsal reruns after feed-queue lands (everything else
  passed; reserved heap 847 to 887 MiB against the 256 MiB bar is the F8 gap).
- One qualification of a quiet candidate, then the tag. Not started; the
  coordinator tags.
- Peering with spwashi and pug: commands in the deploy record; blocked on
  feed-queue and on their node names, host:port, certificates and shared groups.

### 2.9 The public node and the site
- fn.fg-goose.online is live (fsn1 anchor, native, systemd, LE, invitation
  only, about 46 MiB RSS) on the rehearsal build, not a cut. fn.docs holds the
  13 FAQ articles. Open on the node: D1, D3, D4, account delete, docs-login
  narrowing (all FLIGHT, public-node-3); the cutover and the LE renewal clash
  near October 1 (EMBER; the migration plan's section 6); the dregg-infra
  firewall commit is not pushed.
- planning/current.md needs the DEPLOYMENT coordinate for the node. OPEN
  (small).
- The site: 13 articles at a fifth of the words, a static newsreader, Pages
  live. emberian.github.io/fn/ still shows the old site until the tranche with
  site-newsgroup lands.

### 2.10 Tooling and debts
- Exists: proof_repl (send-range, probe, --host), the id claims ledger,
  host_check with --load and the macro-order check, must-fail-checked,
  payload_kind_check (zero waivers), harness stubs generated from host defs,
  format-9 fixtures to 1M, the steps ratchet, the NNTP fuzzer, the replay
  determinism test and `store digest`, release_sequence, tools/extract,
  tools/runtime_floor, post_docs, the static site builder.
- In flight: the unsynchronised-globals rule and the dispatcher unification
  (host-lints), fundamentals.py (release-machinery).
- Open: about 110 uncalled host defuns (a calm per-function sweep; never
  bulk-delete: flip-cleanup nearly removed a function run_store.py calls);
  about 660 untracked .cert/.port files from history-columns-3 (AY cleans);
  toolchain unification between hbox and persvati (two ACL2 builds, caches do
  not transfer; costs one box's cache); the definition/implementation book
  split to stop 700-book recertifications; the 1Password tofu state bundle is
  stale.

## 3. What metaprogramming should collapse

The size of the thing, on batch/ay:

| Surface | Count |
|---|---|
| ACL2 books / lines | 756 / 370,002 |
| ACL2 test books / must-fail forms | 574 / 2,161 |
| Theorems (defthm) | 17,688 |
| Definitions (defun) / mbe forms | 11,260 / 588 |
| Macros (defmacro) in books | 56 |
| Concrete stobjs / abstract stobjs / attachments | 13 / 16 / 9 |
| Codec-shaped defuns (encode, decode, parse, render, format) | 423 |
| Distinct 4xx/5xx reply strings in books | 100 |
| Host Lisp lines | 38,434 |
| Python tools and tests, lines | 172,393 |
| Theorem families by name: -corr / round-trip / -unfolds / -by-definition / -preserved / -bound | 211 / 81 / 79 / 178 / 59 / 725 |

Fifty-six macros in 370,000 lines is the finding. Nearly every theorem and
every test is a hand-written instance of one of about eight schemas, and each
schema already has a prototype or a tool proving the instance can be derived.
The proposal is not "write less"; it is that the derivation becomes the
artefact, so a change to a schema re-derives every instance, the proof follows
by instantiation, and the counts in the registries stop being maintained by
hand. Ordered by leverage for the 6.6.x series:

### G3 first: `defkeystone` (keystones with teeth, generated)
What it replaces: 2,161 must-fail forms in 574 test books, the hand-written
positive and hypothesis-removal witnesses, the ledger and proofs.json entries,
the reach_check subject binding, and the four lints that police them
(ledger --check, must_fail_check, reach_check, current_view).
Form: the theorem, the host caller it is the subject of, a witness state and
inputs. Generated: the positive witness asserting the complete antecedent and
conclusion; one hypothesis-removal witness per hypothesis (retained ones
checked, the omitted one failing, the conclusion failing); the must-fail
registration; the proofs.json row with its subject; the ledger citation. A
theorem with no reachable positive witness is refused at definition, which is
AGENTS.md's rule made structural.
Evidence: entry-guards-2 generated the harness stubs from host defs; the
counts are already generated. Cost: a macro plus a registry emitter; the books
it touches are the test books, not the store. Risk: certification time of the
generated witnesses (they are cheap forms; the ratchet judges).

### G4 second: `defprotocol` (the NNTP table)
What it replaces: the dispatcher (three copies today, host-lints is unifying
them by hand), the 100 reply-string sites, the per-command argument parsers,
the RFC citations scattered in prose, the accepted/refused/uncertain
classification per command, the fuzzer's grammar in fuzz_nntp.py, and the
command section of the operator FAQ (docs_check.py reads the articles today;
invert it so the table writes that section).
Form: one row per command: name, argument grammar, the RFC section, the reply
codes it may emit with their class, the model function it calls. Generated: the
dispatcher, the reply constructors, the fuzz grammar, the article text, and the
theorem that every emitted reply code is in the table for that command. The
"uncertain, refused and accepted stay distinct" rule becomes a column.

### G1 third: `defadt` (the persistence direction, already decided)
What it replaces: the concrete twins and their 211 correspondence theorems and
81 round-trip theorems, the per-stobj accessor and invariant boilerplate for 13
concrete and 16 abstract stobjs, the codec-shaped defuns for stored state, and
the format machinery.
Form: ADT-level types only (products, sums, sequences, keyed maps, pools).
Derived by a versioned backend: columns and the byte pool (FNADTSN1 pages),
per-constructor correspondence proofs by instantiation (proto-adt-2 proved
this works in ACL2 8.7 with no trust tags), canonical bytes with a digest per
page, pool compaction, and the logic-only book for dependents (G9). A format is
the version of the derivation; a bump is a re-derivation plus a proved
migration per constructor, which is how the reclaim event, the dropped profile
fields and the genesis event ship as one bump.
Known limits from the prototype: unbounded int columns, per-type exec
compaction and serialisers, octets crossing the boundary as lists, multimaps
and nested sequences and non-tag sums uncovered, rules that cannot match
computed indices (a library over ops, not rewriting), :congruent-to export
lists, and 18 s versus 6 s to certify an instance declared in a book that
includes the model. First target: fn-hist on pages (arena-store-2), then the
per-record state.

### G6 with G1: `defevent` (the log schema)
What it replaces: per-event encode/decode/fold code, the hand-kept list of
what the fold must not read (the clock, the environment), and the registry
driver's union of events (it re-unioned a renamed event silently this week).
Form: each event's fields and its fold step. Generated: the codec (through
G1), the replay-determinism obligation (the step reads only the event and the
state), the fold's case, the migration at a bump, and the genesis event's
fields. Config events that set seeds and nonces are ordinary rows.

### G5: the profile as the single source
What it replaces: the profile validation in init, the systemd MemoryMax and
heap sizing, the health thresholds, the time-model defaults, the released
tarball's requirements text, and the representability check between profile
and codecs (which must agree today by discipline).
Form: the profile fields with their types and bounds. Generated: init's
refusal by name, the unit file's limits, the FAQ's storage requirements
section, the fixtures that test the bars. Memberships charged to the history
budget already follow this shape.

### G7: `definterface` (the host boundary), then its disappearance
What it replaces: fnn-call entry guards (36 sites), harness stubs,
payload_kind_check and host_check's load rules, all generated today from host
definitions in three separate tools.
Form: one declaration per host-callable function: argument kinds (handle,
octets, parsed field, identity, local number as distinct types), the effect,
the model function. Generated: the guard, the stubs, the lints. In the
extracted image (G2) the boundary is inside the extracted program and the
declaration is what the extractor reads.

### G2: the extractor as the only executable path
What it replaces: the 38,434 lines of host Lisp become the two byte
primitives, sockets and an event loop extracted from a modelled scheduler
(the time model's requests with one completion each). The served image is the
extracted program; the ACL2 image is the prover and the differential oracle.
Evidence: Chicken serves byte-identical replies on every transcript at 8 MB
RSS; guards already erase 95 checks; plain SBCL without ACL2 is 30 MiB. Needed:
boundary guard checks, the extent primitives, A-EXTRACT (an assumption row
with its witness), a stack-depth test, the N-version differential as a make
target, and later a verified backend (CakeML) or C with per-request arenas.
Profile specialisation (compile a profile's constants in) and work bounds as
theorems (the extractor refuses a function without a proved step bound) come
for free once the extractor reads the world.

### G8: the time model as a table
Disk modes, deadlines and the answer for each command in each mode are a table
today in prose. Generate the mode machine, the decision-journal rows and the
tests for each cell from it; the bars F4-R and F4-W become rows ember adopts.

### G9: the definition/implementation split
Every generated type and every keystone gets a logic-only book (definitions,
correspondence statements) that dependents include, and an exec book the image
loads. Abstract stobjs already showed zero dependents recertify on an exec
change. This is what turns 700-book recertifications into tens, and it is
what makes the steps ratchet meaningful per book.

### Order and what each costs
1. G3 and G4 during the 6.6.x series: test books and dispatch only; no store
   change; both remove lints by making the rule structural. About two
   lane-weeks each; each lands behind a differential (same replies, same
   theorem set).
2. G1 and G6 as arena-store-2 and the format bump: already the decided
   direction; the prototype numbers are in section 2.1 and 2.7.
3. G7 folds into G1's landing; G5 is a lane-week and pays back at every
   profile question.
4. G2 after ember's go on the served image without ACL2; the Chicken path is
   the cheaper first step (8 MB) and the SBCL-without-ACL2 path (30 MB) the
   safer one; both are extraction, so they share G7's declarations.
5. G8 with the F4 adoption; G9 as G1 lands.

Risks named: macro hygiene in ACL2 (generated names must be predictable and
the ledger must read them); certification cost of generated books (the 18 s
finding; the ratchet judges); rewriting cannot see computed indices (the
library-over-ops shape); and the extractor is a trusted component until a
verified backend exists, so it gets an assumption row and a differential, not
a claim.

## 4. Unlaunched work, ready to brief (nothing here needs re-deriving)

In rough priority. Each is one focused lane; base on batch/ay.
- arena-store-2: fn-hist on pages, FNADTSN1 layout; the brief is at the top
  of arena-store's LANEDUMP once arena-store-finish writes it.
- compression-extents-2: host wiring for compressed records; vendor lz4;
  dictionary persistence waits on ember.
- uncalled-host-defuns: the ~110, one at a time, each with its caller search
  (tools included) in the commit message.
- zero-copy-commit: the per-connection octet buffer through the four layers;
  input-loop-2's record section 9 has the path.
- thread-stacks: 64 MiB to the proved depth (PKT-693); a test that the depth
  bound holds at the article limit.
- format-bump-10: reclaim event, drop profile fields 1 and 14, the genesis
  event; one bump, one migration, fixtures regenerated; after log-leftovers.
- extract-2: boundary guard checks, the two extent primitives, A-EXTRACT row,
  the differential as `make extract-check`; then guards-as-types widening.
- served-without-acl2: only on ember's go (section 2.5).
- defkeystone (G3) and defprotocol (G4): section 3; each starts with a
  differential over the existing test books and dispatcher.
- book-split (G9): a pilot on the records book (six includers) to measure the
  recertification saving before the general split.
- toolchain-unify: one ACL2 build on both boxes after the flip converges.
- current-md-deployment: the node's DEPLOYMENT entry in planning/current.md.
- astra-reply: send ~/dev/minidregg/docs/FN-UPSTREAM-REPLY-2026-09-27.md
  (PKT-255 consumer inbox) once ember has read it.
- PKT-673 (consumer socket for non-owner peers) and PKT-322 (uncertain post
  from a revoked author): ember decisions first.

## 5. Decisions waiting on ember (compact)
1. Adopt F4-R and F4-W, the time-model defaults as profile fields, and the
   health exit code while stalled.
2. Build the served image without ACL2 (A-TARGET-COMPILER row; 2 to 4
   lane-days), and A-EXTRACT as an assumption row.
3. BLAKE3: decided by ember at 00:20Z on 2026-09-28. BLAKE3 is fn's own digest
   everywhere fn chooses the algorithm; SHA-256 survives only where an RFC
   forces it on the wire (Cancel-Lock, RFC 8315). digest-native's measurement
   (about 35 ms saved per million-record open) was read by the coordinator as
   a "no"; ember's preference is about the algorithm, not the microseconds.
   Lane blake3-digest owns it, as the digest half of store format 10.
4. Compression dictionary persistence.
5. MemoryMax fixed by store size, or by profile.
6. Persist the hbox ARC cap (24 GiB at runtime today).
7. The fsn1 cutover (migration plan section 6) and the LE renewal clash near
   October 1; push the dregg-infra firewall commit.
8. spwashi and pug peering details, after feed-queue.
9. PKT-673 and PKT-322.

## 6. The path to v6.6.0 from here (the cut is HELD — ember 23:30Z)
1. AY pushes green tranches as they come (21 lanes plus site-newsgroup first).
2. feed-queue lands; the OpenBSD friend rehearsal reruns clean.
3. release-machinery lands the cut script's gates and fundamentals.py as
   tooling that judges F1 to F8 on any head; no qualification, no tag.
4. The deep work of section 7 runs now: G3/G4 (defkeystone, defprotocol), G1/G6
   (arena-store-2, then the format bump), extraction (extract-2, then the served
   image without ACL2 on ember's go), F2 (sca-join-5).
5. The cut happens when ember says; then the node moves from the rehearsal
   build to it.

## 7. "Put it down and be done and proud of it" (ember, 23:25Z; the coordinator's answer)

Ember's read: most data structures are non-pathological and the
representations are not naive. Agreed, with two exceptions that both
surfaced today and are both owned: the served path walked the archive list
for GROUP, LISTGROUP and ARTICLE-by-number because two dispatch arms answer
the same commands and the slow one runs first (sca-join-5); and open rebuilt
the whole history at every install (arena-store-2).

The pathological part is the runtime, not the structures: about 90 MiB of
SBCL and ACL2 core plus 64 MiB thread stacks to serve a few thousand
articles, against 8 MB for the same program extracted to Chicken with
byte-identical replies.

Done and proud, with rough lane-weeks at today's cadence:
1. v6.6.0 tagged with tools/fundamentals.py judging F1 to F8; F8 reported red
   if it is. (days)
2. F2 and F8 met: one served path per command; per-record state under 200
   bytes; open near zero. (2 to 3)
3. The served image is the extracted program, or plain SBCL without ACL2,
   with the N-version differential as a make target. Ember's go. (2 to 4)
4. defkeystone and defprotocol landed: teeth, registry rows, the dispatcher
   and the reply lines derived; four lints retire. (3 to 4)
5. Format 10 with the genesis event; the two dead profile fields go; replay
   determinism total. (1)
6. Two real peers (the OpenBSD friend; spwashi or pug) feeding for a week
   with no operator touch. (1, after feed-queue)
7. The Python surface cut: 172,393 lines of tools and tests is a second
   implementation that can drift even under the rule that Python never
   computes what ACL2 computes. (2)

Total 12 to 16 lane-weeks: two to three weeks of a ten-lane swarm. Ember
(23:30Z): "we don't have to wait until after the cut! i'm gonna hold off the
cut for a decent amount of time" — so items 2 to 7 start NOW, in parallel with
the release-critical lanes; the cut script and fundamentals tool finish as
tooling; no qualification or tag until ember says. Launched at 23:35Z:
extract-2 (e1 boundary guards, e2 extent primitives, e3 A-EXTRACT row, e4 `make
extract-check`, e5 measure) and defkeystone (G3 pilot with a differential on
one keystone family); defprotocol (G4) is briefed in
build/coordinator/queue/defprotocol.txt for the next free slot. Complecting to add on purpose: the time model (requests with one
completion each) and the carried join invariant. Complecting to remove: the
twin-per-representation hand proofs, the three boundary generators, the two
dispatch paths, the two ACL2 builds. The swarm holds at ten lanes.
