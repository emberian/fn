# fn2 sprint C/D: Astra's verdict

## Summary

INTEGRATE: **0 pieces**.  
HARVEST: **6 pieces** — P1, P2, P3, P6, P7, P8.  
DISCARD: **3 pieces** — P4, P5, P9.  
**C monitor:** build C1–C6 as briefed, carrying forward the encoded-page tests, bounded-search findings, and corrected foundation dependencies.  
**D monitor:** build the separate declared machines through A’s repaired core, harvesting the wire fixtures and parser boundary cases without adopting the sidecar architecture.

## Fences

This is a source-and-evidence verdict. I ran neither ACL2 nor certification and wrote no files. The reason for withholding integration is architectural fit and concrete defects, not the sprint’s explicitly permitted deferral of proofs or use of a disclosed POST stand-in.

Decision-document references below resolve under `/Users/ember/dev/fn/build/coordinator/fn2/`; brief references resolve under `/Users/ember/dev/fn/build/coordinator/briefs/`.

- **No source edits outside `fn2/sprint/` found.** Both status checks returned only `?? fn2/sprint/`; `git diff --stat HEAD` was empty. This establishes the visible working-tree scope, not a historical audit of ignored scratch files. The sprint prompt expressly allowed scratch logs under `build/`.
- **Two direct includes violate the literal “no include-book outside fn2/” fence:** `fn2/sprint/c/runs.lisp:5` and `fn2/sprint/d/parser.lisp:4` include `std/util/bstar` with `:dir :system`. These are ACL2 toolchain dependencies, not old-fn quarry imports; the foundation itself uses them. Nevertheless, the sprint fence at `SOL.prompt:37` contains no system-book exception. Remove redundant direct includes or explicitly settle that exception.
- **No served-path byte lists or `(coerce ... 'list)` found.** Runtime article and Message-ID bytes remain pool ranges. Lists in `fn2/sprint/tests/d-exchange.lisp:9` are fixtures; byte views in `fn2/sprint/c/runs.lisp:230` occur in a non-executable owed statement.
- **No `skip-proofs`, `defaxiom`, trust tag, or `:program` found in the sprint books.** Deferred guards are disclosed and were allowed by `SOL.prompt:30`.
- **No new machine or column declaration macro found.** D uses A’s `defmachine`. Its expansion surgery at `fn2/sprint/d/connection.lisp:380` changes the fallback, not the generated state arms. That is an explicitly disclosed scout workaround, not a second DSL.
- **C’s proposed sealer does not keep the derived-machine path.** `fn2/sprint/c/seal.lisp:17` declares raw phase storage, and `:76` hand-dispatches numeric phases. Its start operation resizes an offsets array to the complete resident record count at `:29`, outside the claimed incremental seal work. A reusable served sealer must be a declared machine with preallocated, bounded workspace.
- **The reported D charges are not conservative bounds on actual work.** Write submission charges zero bytes at `fn2/sprint/d/connection.lisp:79`; command decoding can examine a 510-byte keyword at `:126` and return 64 bytes at `:171`; scanning followed by `:need-input` loses the scan charge at `:246`. This contradicts the characterization in `fn2/sprint/FOUNDATION-GAPS.md:72` and `REPORT.md:71`. Bounded loops alone do not repair the accounting.
- **The report discloses an earlier shared-slot violation:** the cold retry initially used a private lock path (`fn2/sprint/FOUNDATION-GAPS.md:44`). Reserving a global slot afterward mitigated the ongoing job; it does not make the initial launch compliant. The replacement launcher uses the ordinary lock directory and exclusive locks (`fn2/sprint/acl2-readonly-slot.py:27`, `:35`).

The sidecar and volatile persistence stand-ins were authorized by the scout prompt. Their existence is not itself misconduct. Their suitability for promotion is judged below.

## Per piece

### P1 — FOUNDATION-GAPS.md: HARVEST

The document is useful because it locates actual seams and names the substitutes. Its distinctions between volatile sealing, ordinary pool ownership, and durable acceptance are substantially sound (`fn2/sprint/FOUNDATION-GAPS.md:52`, `:55`, `:67`).

It is not an implementation backlog to adopt unchanged:

- GC3 does not establish a missing B capability: the generic codec already interprets C-owned layouts.
- GD1 is a consequence of the sidecar’s return signature, not evidence that the production dispatcher needs a multi-stobj ABI.
- G1 omits the distinct non-machine core-child registration problem.
- GC4 overlooks the codec’s resident u60 destinations.
- GD3 overstates the conservatism of the handwritten charges.
- Several important needs are already commissioned in A’s and B’s quests.

**Harvest and destination:** carry the corrected gap table below into the C and D briefs; attach the specific amendments to A’s R5a/R5b/R5c/R6 and B’s relevant quests. Do not create ten independent blockers.

**Brief amendments:**

> Foundation dependencies are tracked by capability and existing quest, not by the sprint’s gap count. C-owned schemas use B’s generic codec directly. Production machines and their auxiliary tables enter the single generated core; sprint sidecar return shapes are not an ABI requirement.

### P2 — C page encoding, sealing, and exact Message-ID lookup: HARVEST

There is a worthwhile composition here. C supplies layout data to B’s codec (`fn2/sprint/c/seal.lisp:9`), hashes the actual encoded page (`:128`), and obtains an output lease when sealing completes (`:140`). Lookup decodes the page’s actual directory and inline identities rather than consulting the original resident table (`fn2/sprint/c/page-lookup.lisp:10`). The tests release the original identity and body buffers before that lookup (`fn2/sprint/tests/c-examples.lisp:144`).

That supports harvesting the experiment, not adopting the engine:

1. **Sealer reuse is broken by inspection.** `fn2-sc-seal-init` resets position and row but not phase (`fn2/sprint/c/seal.lisp:26`). Generated column initialization resizes columns; it does not clear existing elements (`fn2/books/columns.lisp:403`). After one successful seal, reinitializing the same sealer leaves phase 7, and the next step returns `:sealed-volatile` without constructing the new page (`fn2/sprint/c/seal.lisp:147`). This is a statically derived defect, not a claimed executed counterexample.
2. **The one-page limit has no implemented continuation to another page.** `:page-full` preserves the row at `fn2/sprint/c/seal.lisp:92`, but the surrounding API supplies neither completed-page finalization nor a next-page transition. Merely retaining a row is not the complete exhaustion protocol.
3. **The format is a fixture, not the identity schema.** It stores a scalar article tag and always writes conflict zero (`fn2/sprint/c/seal.lisp:46`, `:51`), with fixed physical identity fields (`:55`). It lacks the content identity, acceptance binding, version/value semantics, and checked references required by C’s brief.
4. **Header placement is fixture-specific.** Payload starts at offset 64 (`fn2/sprint/c/seal.lisp:62`, `:116`), although B’s page-header layout has maximum encoded size 69 (`fn2/books/format.lisp:48`). The current small fixture values fit; general identifiers cannot simply replace them.
5. **Physical integrity is not schema validity.** Lookup checks each offset against broad bounds but not the directory’s ordering, entry partitioning, or schema relationships (`fn2/sprint/c/page-lookup.lisp:16`, `:61`). B expressly does not establish application semantics (`fn2/docs/b-durability.md:259`).

**Harvest and destination:**

- `fn2/sprint/c/page-lookup.lisp:17`: schema-sized bounds on decoding malformed varints → **C1 brief**.
- `fn2/sprint/tests/c-examples.lisp:132`: seal/check/lease/corrupt/release-source experiment → **C1/C2 acceptance fixtures**, rewritten against the real schema.
- `fn2/sprint/c/runs.lisp:103`: exact comparison’s two-range requirement → **A R6**, including separate ownership authorities.

**Brief amendments:**

> C1’s sealer is an A-declared machine with reusable initialization, profile-reserved workspace, computed header placement, and an explicit multi-page exhaustion continuation. Test two successive seals using the same row. Validate run-schema structure separately from B’s physical integrity check.

> C2 retains exact Message-ID bytes independently of body placement and tests lookup after reclamation. Equal fixture tags test resistance to replacing byte equality with tag equality; they do not test a source-content conflict.

### P3 — Ordered `(group, number)` runs and XOVER-shaped cursor: HARVEST

The sparse-key algorithm is useful. Binary seek walks stored keys, not absent article numbers (`fn2/sprint/c/runs.lisp:161`). Seek and output share structural fuel; unfinished seek retains `(lo, hi, phase)` (`:189`). The fixture exercises numbers 2, 900, and 1,000,000 and checks exact yield/resume results (`fn2/sprint/tests/c-examples-driver.lsp:21`).

The representation is not the ordered-run engine C3 would build:

- It is one resident append-sorted table. Appending to group 7 after group 8 is rejected even when that group’s own number increases (`fn2/sprint/c/runs.lisp:84`). That is an input-sorting precondition, not a general active overlay.
- The cursor has no logical version or visibility cut. Its returned result is a contiguous resident row slice (`fn2/sprint/INTERFACE.md:25`), not a leased result over pageable, overlapping runs.
- Its byte charge is a synthetic projection, `22 + Message-ID length` (`fn2/sprint/c/runs.lisp:171`), not an encoded overview row. When a row exceeds the caller’s byte budget, it returns `:entry-budget` without a partial-row continuation (`:181`).
- It exercises neither cold page reads nor overlapping-run work, both required by C acceptance (`FN2-LAYER-C-ORDERED-RUNS.md:12`).

**Harvest and destination:** `fn2/sprint/c/runs.lisp:159` and `:186`, plus the sparse cursor assertions at `fn2/sprint/tests/c-examples-driver.lsp:21` → **C3 brief and tests**. Preserve the shared-budget and zero-output-seek findings, not the row-slice API.

**Brief amendment:**

> A cursor carries a logical view and exclusive last-examined key. Its retained continuation also represents unfinished seek and partial rendering. Charge directory, overlapping-run, comparison, and output work together. Test zero-output yields, oversized rows, compaction between calls, and sparse cold groups; no resident row index is a persistent cursor identity.

### P4 — C overlay, filters, folds, and compaction remainder: DISCARD

There is no additional engine here to integrate.

The “sealed prefix and append tail” share one table; `fn2-sc-sealed` is initialized and later assigned, but the searches and insertion rule do not implement separate immutable-run and mutable-overlay behavior (`fn2/sprint/c/runs.lisp:12`, `:72`; `fn2/sprint/c/seal.lisp:145`). Filters and compaction are explicitly absent (`fn2/sprint/REPORT-C.md:11`).

The fold is addition of scalar tags over resident rows (`fn2/sprint/c/runs.lisp:215`). Its cut equation and summary-plus-one control are real tests of that sum, but provide no interpretation, initialization, coverage, versioned selection, or observational equivalence for the required folds. The function also traverses its whole requested interval without a continuation; it is only used by the scout’s tests and owed statement, not a demonstrated served path.

**Brief amendments:** none. Keep C2’s overlay/filter work, C4’s declared fold semantics, C5’s reserved compaction, C6’s measured perfect hashing, and the inbox amendments. Do not translate the scalar sum into an engine-summary milestone.

### P5 — D connection declaration, machine structure, and registry workaround: DISCARD

The declaration is genuinely A’s DSL (`fn2/sprint/d/machine.lisp:9`), and the report correctly says that `fn2-turn` cannot reach it (`fn2/sprint/REPORT.md:42`). The temporary registry workaround was permitted.

The resulting machine is nevertheless the wrong starting structure. It combines connection, upload, query, and commit phases in one row (`fn2/sprint/d/machine.lisp:10`), while the brief assigns them separate resource ownership, lifetimes, and scheduling contracts (`FN2-LAYER-D-MACHINES-NNTP.md:9`–`:12`). Most continuations ignore `id` and operate on row zero. All pool access and issued operations use the shared fixture owner `(250,0,1)`.

There are concrete consequences beyond missing features:

- The driver ignores `runnable` and invokes the machine every round (`fn2/sprint/tests/d-exchange.lisp:90`). It therefore cannot validate production scheduling or wakeup behavior.
- Full C capacity returns runnable without a progress-enabling transition (`fn2/sprint/d/connection.lisp:348`). The admission test actually requires that runnable result (`fn2/sprint/tests/integration.lisp:33`).
- Draining moves to `done` even when releases fail; the upload release result is ignored (`fn2/sprint/d/connection.lisp:33`).
- Failed storage observation renders reply bytes directly (`fn2/sprint/d/connection.lisp:415`), outside the scheduled-run work discipline of `EXECUTION-MODEL-ROUND2-ASTRA.md:283`.

These are reasons to rebuild the machine boundaries, not extend the sidecar until it resembles them.

**Brief amendments:**

> D1 extends A’s existing declaration system through A-owned changes; it does not create a replacement machine DSL. Register machine declarations before core assembly and auxiliary tables through the core-child seam.

> D3 acceptance drives the connection through the real turn, router, scheduler, and resource grants. Exhaustion parks on a named resource; failed release preserves draining state. Observation handlers record outcomes and wake work, while reply construction occurs in scheduled runs.

### P6 — NNTP parser, grammar table, and pool reply renderer: HARVEST

The scanner retains a CR awaiting LF, distinguishes bare CR/LF, and bounds each scan (`fn2/sprint/d/parser.lisp:25`). The full-window retained-tail case is valuable: two bounded copies preserve the tail and rebase the scanner (`fn2/sprint/d/connection.lisp:206`; `tests/d-exchange.lisp:174`). Rendering writes directly to pool storage.

The grammar claim is too broad. `*fn2-sd-grammar*` contains argument types (`fn2/sprint/d/parser.lisp:6`), but its interpreter reads only keyword and numeric tag (`:48`). Argument parsing and command semantics are manually dispatched in `fn2-sd-command` (`fn2/sprint/d/connection.lisp:119`). There is no table-derived parser/renderer/generator/mutator family.

The byte helpers also repeat checked scalar pool operations and hardcode one owner. R6 is already intended to replace precisely this class of loops. The work accounting defects mean the scanner’s local bound cannot be treated as a composed parser cost bound.

**Harvest and destination:**

- `fn2/sprint/d/parser.lisp:25` → **D2**, as a scanner behavior reference.
- `fn2/sprint/d/connection.lisp:206` and `tests/d-exchange.lisp:174` → **A R6 and D2**, as the retained-prefix progress requirement and regression fixture.
- `fn2/sprint/tests/d-exchange.lisp:23` → **D2/D3**, as independently specified reply bytes.

**Brief amendments:**

> Grammar argument types must drive parsing and fixture generation; unused type annotations do not constitute a grammar interpreter. Test arbitrary octets and every split position, including CR/LF separation and a retained command tail at a full RX window.

> R6’s range API must support a bounded consumed-prefix operation with correct fill and scan rebasing, or an explicitly accounted equivalent. A copy primitive alone does not reduce the RX fill.

### P7 — GROUP, ARTICLE, POST, and the persistence stand-in: HARVEST

The exchange uses real A descriptors and simulator storage. POST enters uncertainty after successful Write issue (`fn2/sprint/d/connection.lisp:75`), advances on Write/Fence completion (`:410`), and publishes before emitting 240 only after reaching the publish phase (`:365`). Fresh ordinal-based intervals avoid overwriting an earlier article within this one-connection fixture (`:53`). This is a useful experiment in completion ordering.

It is not a transaction or query implementation to promote:

- GROUP and ARTICLE use resident metadata directly, without a selected logical view or acquired B object lease. The comment claiming source acquisition at `fn2/sprint/d/parser.lisp:97` has no corresponding acquisition in `fn2-sd-article-render` (`connection.lisp:288`).
- POST checks only Message-ID presence and length before lookup (`fn2/sprint/d/connection.lisp:335`). For example, `Message-ID: x` satisfies that check; Newsgroups does not determine publication, which always inserts into group 1 (`:369`).
- Same-ID admission does not distinguish duplicate from contradictory source binding. There is no operation identity, reserved identity record, dependency manifest, batch membership, or recovered outcome.
- A count comparison before Write is not a reservation against another transaction (`fn2/sprint/d/connection.lisp:345`). Its justification is explicitly the fixture’s single connection.
- Ordinal-derived storage locations are not allocator-issued durable identities and have no restart lifecycle.

**Harvest and destination:**

- `fn2/sprint/d/connection.lisp:48`, `:365`, `:410` → **D5 brief**, as the small completion-order experiment to replace with B3 notifications.
- `fn2/sprint/tests/integration.lisp:26` → **D0/D5**, preserving the “no irreversible action without successor capacity” assertion while replacing polling with actual reservation and wakeup.
- `fn2/sprint/tests/d-exchange.lisp:109` → **B3/D5**, as a durable-image fixture technique, not a recovery oracle.

**Brief amendments:**

> D5’s first POST scenario uses B3 and the real transaction identity/reservation protocol. Assert at every transition that no success or visible C mutation precedes the required durability evidence. Include two competing transactions, disconnect after submission, duplicate/conflicting retry identities, and failed fences with bytes that may nevertheless survive.

> D6 acquires the version/object lease before emitting success and tests relocation or reclamation while the response is stalled.

### P8 — Tests, drivers, and verbatim evidence: HARVEST

The examples are real executable checks, not unconditional pass prints.

- C’s driver asserts exact lookup/cursor results, immutability refusal, corruption rejection, source-buffer reclamation, and malformed decoding (`fn2/sprint/tests/c-examples-driver.lsp:10`).
- D compares every received reply byte with separate fixtures (`fn2/sprint/tests/d-exchange.lisp:23`, `:52`) and checks row count, outcome, one Write, one Fence, and durable bytes (`:139`).
- The integration driver checks a full-C no-write case and an actual invariant-removal control (`fn2/sprint/tests/integration.lisp:29`).
- The Python runner requires successful exit, no recognized ACL2 error, and an emitted pass marker rather than its echoed source (`fn2/sprint/tests/run-examples.py:39`).

The recorded semantic outputs are consistent with these paths: C reports 45 seal calls and the expected sparse cursor results; D reports 441 reply bytes on success, 103 on fence failure, and the retained-tail control succeeds (`fn2/sprint/evidence/c-examples-driver.out:42`; `evidence/d-exchange-driver.out:36`). I did not independently reproduce execution or the printed digest.

Their limits matter:

1. **The harness would pass materially broken production designs.** It bypasses the real turn and ignores runnable status. It checks reported work, not independently observed work. OWN’s real read hook is absent from `fn2-core-read` (`fn2/books/core.lisp:178`), so the OWN label is not evidence that every parser read was observed.
2. **Three feed quanta are not arbitrary fragmentation coverage.** The driver uses 1, 7, and 4096, plus one failed-fence run (`fn2/sprint/tests/d-exchange-driver.lsp:7`). It does not cover every split, delayed output borrows, cancellation, resource wakes, or process-death cuts.
3. **The failed-fence oracle must not be generalized.** It requires the new article *not* to be durable (`fn2/sprint/tests/d-exchange.lisp:145`). That matches this injected failure, but the required general contract is uncertainty even when some or all bytes survive.
4. **Final-state checks do not establish publication ordering.** A deliberately early C publication could escape the final count/durability assertions. Assert the temporal condition at every prefix.
5. **The report and linked artifacts are not one identical final capture.** Reported driver times are 0.730/3.525/3.649 seconds (`REPORT.md:195`, `:260`, `:319`); `evidence/examples.json:5`, `:14`, `:23` records 0.945/4.989/3.762. The embedded C include time differs from the raw transcript. The owed-book timing in `REPORT.md:175` also lacks its corresponding entry in `evidence/certification.txt:60`. These discrepancies do not refute the semantic pass lines, but weaken the “complete final rerun, verbatim” provenance claim.

**Harvest and destination:**

- C fixture checks → **C1/C2/C3 acceptance**, with the replacements specified above.
- D wire and compaction fixtures → **D2/D3/D5 acceptance**.
- Runner error/marker checks → **C and D driver conventions**.
- Read-only shared-lock technique in `fn2/sprint/acl2-readonly-slot.py:22` → **A5r tooling review**, not a second permanent launcher.

**Brief amendment:**

> Preserve independently authored expected bytes and destructive controls. Execute them through the real composed driver and existing checkers. Store report excerpts and machine-readable results from the same capture; distinguish supplied execution evidence, local certificates, and current-closure certification.

### P9 — D’s T1/T6/T8/T9/T10 statement packet: DISCARD

The packet is candidly scoped and uses real function names. It does not falsely admit theorems. Nevertheless, these are not the intended keystones’ starting statements:

- T1 preserves a small shape predicate and returned counters, without reached-call guard closure (`fn2/sprint/d/owed.lisp:6`, `:15`).
- T6 concerns `fn2-sd-run` but excludes the observation transition that supplies storage completion evidence (`:23`).
- T8 compares scan quanta over one unchanged core, not equivalent fragmented input/observation histories or privacy (`:35`).
- T9 restates exact comparison for a resident lookup, without source binding or reclamation (`:46`).
- T10 preserves row counts, not the profile’s total resident allocation (`:55`).

These are narrower auxiliary facts. Calling them scoped does not make them replacements for the obligations at `FN2-LAYER-D-MACHINES-NNTP.md:16`. Rebuilding the machine boundaries changes their subjects anyway.

**Brief amendment:**

> Reserve T1/T6/T8/T9/T10 for the briefed semantic obligations over the composed subjects. Name auxiliary shape, scan-quantum, and lookup facts for what they state. Theorems may remain owed; their statements must retain the intended property.

## Foundation gaps audited

Quest references below resolve under `/Users/ember/dev/fn/build/coordinator/fn2/lanes/`. “Planned” means commissioned in the inspected prompt, not implemented in this checkout.

Priority: **P0** before composing the affected served path; **P1** before the corresponding layer milestone; **P2** tooling or documentation.

| Gap | Real / not real, with foundation evidence | Correct owner | Already planned / new | Priority |
|---|---|---|---|---|
| **G1** | **Real assembly and observation seams.** `fn2/books/machines-a.lisp:93` fixes machine indexing; `core.lisp:16` assembles children; `machines-a-run.lisp:14` hand-routes observations. This does not require a dynamically open runtime registry. | **A** owns mechanisms; C/D register through them. | `a-quests/R5a.prompt:11` and `R5a.amend.msg:8` generate observation routing; `R5c.prompt:10` adds core children. `b-quests/B3.final.prompt:113` already specifies compile-time machine include seams. Extend that assembly convention to C/D. | **P0** |
| **G2** | **Real tooling restriction.** `tools/acl2_slots.py:286` opens locks read-write before its diagnostic-write exception handler at `:309`. The read-only lock technique addresses that particular restriction. | **A tooling** | `a-quests/A5r.prompt:17` already reviews this workaround and excludes it from the seat’s acceptance path. No new runtime quest. | **P2** |
| **GC1** | **Real missing range primitive.** `fn2/books/pool.lisp:344` and `:353` provide scalar checked access; the sprint implements comparison itself. | **A** | `a-quests/R6.prompt:9` commissions bounded compare/copy/scan/fold. Add explicit authorities for both compared ranges and an independently checked byte charge. | **P1** |
| **GC2** | **Real missing orchestration, not missing allocator primitives.** The registered kinds end at scribe (`fn2/books/machines-a.lisp:83`, `:93`). B’s existing release predicate is real (`alloc.lisp:310`); its callers still owe persistence composition (`fn2/docs/b-durability.md:437`). | **B** for commit/recovery/reclamation lifecycle; **C** for run roots and schemas. | `b-quests/B3.final.prompt:164`, `B5.prompt:13`, `B6.prompt:13`, `B7.prompt:9`. B4b’s retirement-FIFO repair is already represented in this foundation, not a future missing allocator. | **P0** |
| **GC3** | **Not a demonstrated foundation gap.** B has a closed catalogue (`fn2/books/format.lisp:283`), but `layout.lisp:272` and `:404` interpret supplied valid layouts. The sprint successfully uses that interface. | **C**, for its schema definitions. B only if a concrete discovery consumer later requires registration. | Existing **C1/C2**, not a new B quest. | **P2** correction |
| **GC4** | **Real missing native kind, but the audit is incomplete.** `fn2/books/columns.lisp:440` excludes u64. B also stores decoded values in u60 (`layout.lisp:6`) and rejects high u64 bits (`:169`). Native columns alone do not change that. | **A** for column widths; **B** for codec destinations; C chooses justified schema widths. | `a-quests/R5a.amend.msg:1` explicitly supersedes the original width ruling. B3’s prompt recognizes it at `b-quests/B3.final.prompt:148`; the older `B2f.final.prompt:12` required the opposite codec behavior. **Add a B codec-width follow-up.** | **P1** |
| **GD1** | **Real hardwired fallback, not a required new ABI capability.** `fn2/books/machines.lisp:101` assumes `(id fn2-core)`, as the single-core execution model intends. The seven-value sidecar creates the mismatch. | **A** resolves assembly under G1; **D** removes its adapter. | G1/R5c and the existing machine include seam. **No generic multi-stobj dispatcher quest.** | **P0**, duplicate dependency |
| **GD2** | **Real, substantially GC2 again.** `fn2/books/merkle.lisp:240` hashes leaves; it does not commit transactions. The machine registry has no B commit kind. | **B** | `b-quests/B3.final.prompt:164`–`:167`, then B5/B6. D replaces the stand-in with B’s outcome interface. | **P0** |
| **GD3** | **Real.** The generated charge checks supplied numbers (`fn2/books/machines.lisp:96`); obligations are names stored in table data (`:107`); the declaration has no arm cost/frame contract (`:114`). | **A** owns DSL mechanisms; **D** supplies arm contracts and uses them. | `a-quests/R5b.prompt:8` repairs charging and independent observation. R5a repairs related declaration behavior. **Restricted arm vocabulary and actual cost/frame obligation emission remain an explicit A-owned extension, coordinated with D1.** | **P0** for machine promotion |
| **GD4** | **Real missing convenience/primitive, not inability to implement bounded progress.** `fn2/books/pool.lisp:368` resets fill to zero; ordinary writes only increase fill (`:363`). Scalar access permits the demonstrated two-buffer solution. | **A** for range/fill operations; **D** for parser continuation semantics. | `a-quests/R6.prompt:9` covers overlap-safe copy and scanning. **Add consumed-prefix/fill semantics explicitly**; overlap-safe copy alone is insufficient. | **P1** |

### Unrecorded or underrecorded gaps

1. **Non-machine tables cannot enter the core merely by registering a machine.** G1 discusses the machine registry, but C’s table and B’s codec/checker state need child registration too. `fn2/books/core.lisp:18` hardcodes the non-machine children; D passes C separately at `fn2/sprint/d/connection.lisp:384`. This is precisely **A R5c** (`a-quests/R5c.prompt:7`), already planned. Add it explicitly to G1; **P0**.

2. **Complete admission bundles, resource waits, and protected release capacity are missing from the composed proposal.** The sprint substitutes a single-connection count check and runnable retry (`fn2/sprint/d/connection.lisp:159`, `:348`). A already has an operation wait queue, but only a singleton pool waiter (`fn2/books/machines-a-access.lisp:76`, `:109`). Route the foundation requirement to **A R6** (`R6.prompt:10`), and the C/D bundles to **D0**; **P0**. Existing parking must not be described as wholly absent.

3. **OWN does not observe these real reads.** The sprint relies on `fn2-check-own` at round boundaries (`fn2/sprint/tests/d-exchange.lisp:106`), while `fn2-core-read` has no read-monitor call (`fn2/books/core.lisp:178`). This is **A R5b**, explicitly planned at `R5b.prompt:10`; **P1**. A6’s checker/accounting work does not substitute for installing this hook.

4. **Column-expansion cost was encountered but omitted from the gap register.** The report records 401.929 seconds for the connection declaration and about 85.1 GB cumulative allocation (`fn2/sprint/REPORT.md:185`). Isolating the declaration avoids repeated work but does not fix the generator. Route that measurement to **A R5a’s existing generic-proof repair** (`R5a.prompt:14`); **P1**.

5. **The codec-width mismatch needs its own cross-layer entry.** It is described under GC4 above. A’s new u64 destination kind must not leave B silently governed by the superseded blanket u60 ruling. **B width follow-up; P1.**

The fake shared owner is disclosed in `fn2/sprint/INTERFACE.md:44`, but it is not evidence that A lacks ownership transfer: `fn2/books/pool.lisp:321` and `:330` already provide hand/accept operations. Likewise, the unused grammar argument types, absent logical views, handwritten sealer phases, and weak summary are C/D implementation shortcuts, not additional foundation gaps.

## What the C monitor should read first, and what the D monitor should read first

**C monitor — in order:**

1. `FN2-LAYER-C-ORDERED-RUNS.md`, `STORAGE-DESIGN.md`, and the concrete-format section of `STORAGE-DESIGN-ASTRA.md`; retain `FILTERS-2026.md` and `INBOX-DELIVERY.md` §4–5 as requirements.
2. `fn2/sprint/FOUNDATION-GAPS.md`, with this verdict’s corrected ownership and quest mapping.
3. `fn2/sprint/tests/c-examples.lisp`, `tests/c-examples-driver.lsp`, and `evidence/c-examples-driver.out` — read the useful experiment before its claimed engine API.
4. `fn2/sprint/c/page-lookup.lisp`, then `c/seal.lisp`, then `c/runs.lisp`, whole, as harvest material.
5. `fn2/books/layout.lisp`, `format.lisp`, `format-check.lisp`, `alloc.lisp`, and the relevant B durability documentation.
6. `a-quests/R5c.prompt`, `R5a.amend.msg`, `R6.prompt`; then `b-quests/B3.final.prompt`, `B5.prompt`, `B6.prompt`.
7. `fn2/sprint/INTERFACE.md` and `REPORT-C.md`, as a record of fixture constraints—not the C/D production contract.

**D monitor — in order:**

1. `FN2-LAYER-D-MACHINES-NNTP.md`, `FN2-SEAT-COMMON.md`, `REVIEW-20261028.md`, and `EXECUTION-MODEL-ROUND2-ASTRA.md` §A.3–F.
2. `a-quests/R5a.prompt` together with `R5a.amend.msg`, then `R5c.prompt`, `R5b.prompt`, `R6.prompt`, and `A6.prompt`.
3. `fn2/sprint/tests/d-exchange.lisp`, `tests/d-exchange-driver.lsp`, and `evidence/d-exchange-driver.out` — harvest the independent wire fixtures and retained-tail case.
4. `fn2/sprint/d/parser.lisp`, then `d/connection.lisp` and `d/machine.lisp`, whole, to understand both the useful boundary handling and the architecture being discarded.
5. `fn2/sprint/tests/integration.lisp` and `d/owed.lisp`, to distinguish the demonstrated local properties from D’s actual obligations.
6. `b-quests/B3.final.prompt` and `B5.prompt`, followed by the current B commit/outcome interface when it lands.
7. `fn2/sprint/FOUNDATION-GAPS.md`, `INTERFACE.md`, and `REPORT.md`, reconciled against this verdict and the raw evidence.
---

## Monitor's note (appended by the Opus monitor; not part of Astra's verdict)

Astra's P8 provenance point 5 (driver times in `evidence/examples.json` differing from `REPORT.md`) was caused by the monitor, not Sol: the monitor's own rerun of the three drivers ran while Astra was reading and overwrote `evidence/`. Sol's original capture (0.730 / 3.525 / 3.649 s, matching REPORT.md) is restored in `evidence/`; the monitor's rerun (exit 0, all three passing, identical semantic lines) is kept in `evidence/seat-rerun/`. The `std/util/bstar` system-book includes (Fences, second bullet) are ACL2 toolchain books that the foundation itself includes; the monitor accepts them.
