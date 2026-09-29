# The resource contract

Ember asked (2026-09-28): do we have actual worst-case bounds on resource
consumption; is this an enforced and deterministic property of the system
under load; could it have a warranty? This document is that warranty,
written so that it cannot overclaim. Every row says what is bounded, what
enforces it, what the evidence is and of what kind, what happens when
reality exceeds the model, and what the row does not bound. A row that
rests on a measured constant or on a theorem no host line calls says so in
that row.

The short answer, so nobody has to read the rows to learn it: the memory,
work-per-step and admission bounds are deterministic functions of the
operator's profile and are refused by name at the boundary; several of them
are theorems about a model whose host subject is real (the host calls the
function the theorem is about); every book they live in is green at its
current bytes by the day's union cites, while in the registry's own sense
all but one of them (PRF-257) are uncertified at the current digest (see
"The coordinates" below); the
time rows guarantee classification only, never latency; the stack row is a
lint with a counted debt, not a proof; TLS has no bound of its own; disk has
no growth theorem; and the "Not bounded" list at the end is not empty.

## The coordinates

A claim names its coordinate (AGENTS.md): source revision, proof (a committed
manifest), qualified image, deployment. This document is a claim about a
source revision only. It names theorems and the books that hold them; whether
those books are certified at their current bytes is asked of
`tools/green_check.py` every time `make check` runs
(`python3 tools/resource_contract.py --check`) and is never written into this
file, because an archived manifest or an edited book would put it out of
date. Two notions of "certified" exist in the tree and the tool prints
both, because they disagree. `tools/green_check.py` judges a BOOK at its
current bytes against every held manifest: at the revision this document
was written against (origin/dev `1922efe84`, 2026-09-29) every book this
contract cites was green, certified within the previous day by the batch's
union cites on persvati and hbox (`--table` names the run for each).
`planning/proofs.json` judges a PROOF against the manifests its own entry
cites, which are the manifests the lane that wrote it recorded: at the same
revision it marked 5 of 360 proofs `certified` and 327
`uncertified-at-current-digest`, and of the 30 registered proofs this
contract cites only PRF-257 (the LZ4 decoder, row **W5**) was among the
five. A row's theorem is therefore certified at these bytes in the first
sense and, in the registry's sense, certified only by an older run until
the entry cites the newer one. Both are strictly more than a commit message
says and strictly less than "the served image runs these bytes": no row
here claims an image or a deployment.

Three kinds of evidence appear, and a row is labelled with exactly one:

- **THEOREM**: a named event in a named book, about the function the host
  calls (the host subject is named). Green is not true: the row is a claim
  about the model, and the boundary theorems that connect the model to
  octets and files are the ones the row names, not others.
- **MEASURED**: a record under `planning/evidence/` with its scope (machine,
  image, workload) and margin. A measurement is a fact about one run; it is
  never authority for admission.
- **OPEN**: no theorem and no measurement. The row says what it would take.

Some rows cite what another lane is delivering, so that the contract states
the figure as it will be; the generated block marks those `landing` with the
lane and sha, and `--check` treats their citations as pending until they
land. Nothing pending is claimed.

## The profile P

Every bound below is a function of the operator's supported profile, never
of a constant in the code (D27, `planning/decisions.md`: "a constant that
bounds data is a defect"). The profile's fields that enter the bounds: T
`max-transactions`, H `max-history-octets`, R `max-record-octets`, A
`max-article-octets`, G `max-groups-per-article`, K `max-open-suffix`, the
header limits (fields, lines, octets), the connection capacity, and the
runtime limits of `books/profile-limits.lisp` (the control stack, the
control clients, the nursery, the fixed threads). The worked instance in this
document is the **small preset** (`*fn-heap-small-request*`, generated
below), the preset the 2 GB friend node and the public node's sizing are
judged against. There is no "public" preset: the public node is sized by a
2 GB memory cap with T 32,768 (`planning/decisions.md`). Where a row's
number depends on A, the row gives the small preset's A (32 KiB), the
development default (64 KiB) and 1 MiB, because the last is what a public
node must allow.

## How to read a row

Each row has five fields. *Bounded*: the quantity and the profile terms it
is a function of. *Mechanism*: the code path that refuses or yields, and the
host subject (the function the host calls) when there is one; "no host
subject" means the theorem is about a model the served path does not yet
run. *Evidence*: THEOREM (events; the generated block lists them with their
books and proof ids), MEASURED (record, scope, margin) or OPEN. *Exceeded*:
the named outcome when reality passes the model, with its exit code or wire
reply; never a degraded mode. *Not bounded*: what this row leaves out.

## Memory

**M1** — the process heap.
- Bounded: the SBCL dynamic space, `--dynamic-space-size`, is the profile's
  figure `fn-heap-figure-octets` (a function of T, H, R, A, the header
  limits, the observed core and the nursery), and the node refuses to start
  on a machine that cannot hold the figure plus every thread it runs.
- Mechanism: `fn-heap-reserve-operation-decide` at start;
  `fn-heap-init-decide` at `init` (the operator's budget against the figure
  and the machine). Host subjects: `fnn-heap-init-decision`,
  `fnn-heap-reservation` (`host/native/heap.lisp`); the launcher `exec`s
  SBCL with the number (`packaging/fn`), so the cap is the runtime's.
- Evidence: THEOREM (PRF-198): a start is refused exactly when the figure
  exceeds the machine; a refusal exits 1; the reservation holds every
  thread. MEASURED: `heap=1012 MB profile=small machine=2048 MB` accepted
  and the development preset refused at 2,681 MB under a 2 GB cap
  (heap-from-profile, hbox, 2026-09-26). The small preset's first-run
  reservation is 1,872 MB on the release image (1,906 MB on the image-floor
  core; lane heap-bounds-2, merged 2026-09-29), which a 1,500 MB budget
  refuses by name: planning/release-v6.6.0.md records the bar "the small
  profile fits 1.5 GB" UNMET until **M2b**.
- Exceeded: at start, `:machine-cannot-hold-profile` or
  `:machine-cannot-hold-threads`, exit 1 (`:refused`). At run time the cap is
  SBCL's: a `storage-condition` is re-signalled globally
  (`host/native/owner.lisp`), reaches the serious-condition handler and
  exits 4 (`:fault`); "Heap exhausted, game over" inside the collector is
  SBCL's own death and is not classified. Heap exhaustion is therefore a
  fault, not a refusal: the model's job is that admission never reaches it.
- Not bounded: about 104 MiB of virtual address space outside the dynamic
  space (text, fixed objects; f8-reservation record); older collector
  generations (F4 measured 181 to 218 MB of garbage against the model's
  two-nursery collector term); kernel and socket memory; the foreign
  library's allocations (**T1**); a live raise of the connection capacity
  past the start reservation (PKT-605).

**M2** — the state term: every store the profile admits fits the figure.
- Bounded: the heap the accepted history occupies, from T records of at most
  R octets, H history octets (payload and memberships share H), and the
  open's transient (chunk lists, suffix vectors, the per-record build).
- Mechanism: the terms are the figure's; admission refuses at T and H by
  name (**D1**). Host subject: the same start decision as **M1**; the
  per-record term is the model's, no host line measures a record.
- Evidence: THEOREM (PRF-198, PRF-314): a store within T and H needs at most
  the figure, memberships are charged to H. The octet-list factor
  `*fn-heap-list-octets-per-octet*` (16 octets per octet) is a modelled
  representation cost. MEASURED: the 100k synthetic store opens at its
  figure with VmHWM 2.19 GB; the 50k store with a 20k suffix exhausted 2,048
  and 3,072 MB before B3 and opened at VmHWM 986,136 and 1,218,364 kB after
  (heap-bounds record, hbox). OPEN: the reopen across the large-T range (F1)
  is not re-proved after B3; measure at convergence.
- Exceeded: a store the figure does not hold is not admitted, so the
  exceeding case is a modelling error, and it presents as **M1**'s fault.
- Not bounded: the posted state exceeds the reopened state (F3, a measured
  gap); the checkpoint's own transient (**D3**).

**M2b** — the reservation as it will be (B9, landing).
- Bounded: the same quantities, restructured as a base, plus charges for
  the persisted records, plus a credited pool sized from the operator's
  budget, instead of the worst-case sum that puts the small preset at
  1,872 MB. Lane heap-pool's working pins (not a claim) put the small preset
  at 924 MB on a 2,048 MB machine.
- Mechanism: fn-heap-record-charge (pending) as the per-record charge; the pool of
  **M5** and **M6** funded from the budget.
- Evidence: PENDING, lane heap-pool (heap-bounds-2 resumed): the theorems
  are named in the generated block and are checked once they land.
- Exceeded: as **M1**.
- Not bounded: as **M1**.

**M3** — the itemised reservation.
- Bounded: nothing new; the row exists so the figure is never hand
  arithmetic. Every term of the model is named and the terms sum to exactly
  the number `init` prints.
- Mechanism: `tools/f8_breakdown.py` evaluates `fn-heap-breakdown`; no host
  subject (a reporting tool).
- Evidence: THEOREM (PRF-375). The book's header still quotes a stale
  figure ("1,187 MB"); the theorem, not the comment, is the claim.
- Exceeded: not applicable.
- Not bounded: not applicable.

**M4** — the collector's trigger while a store opens.
- Bounded: the nursery trigger during an open is at least 8 MiB and at most
  the larger of 8 MiB and four times the history on disk, and the figure
  still holds every store at that trigger.
- Mechanism: `fnn-open-nursery` (`host/native/io.lisp`) reads the bound.
- Evidence: THEOREM (PRF-364).
- Exceeded: a trigger is a collector parameter, never an admission; an
  exceeding case is **M1**'s fault.
- Not bounded: the collector's pause (see "Not bounded").

**M5** — articles in flight: the credited article pool.
- Bounded: the number of connections in article mode at once. One article
  credit is 2 x 16 x (512 + A + HDR) octets (the octet-list factor and the
  collector's copy), and the pool is `*fn-heap-article-slot-budget*`
  (64 MiB) capped at `*fn-heap-article-slots-most*` slots. Small preset:
  1,589,248 octets a credit, 32 slots. Development default at A 64 KiB:
  2,637,824, 25 slots. At A 1 MiB: 34,095,104 octets, ONE slot (lane
  credits-stall). The coordinator's decision (B8): the pool stays; B6
  (chunked bodies) removes the x16 and is the fix, and must land before the
  cut so the public node's profile allows concurrent large uploads.
- Mechanism: `fn-oas-read-span` admits a connection into article mode only
  within the slots; a read of one connection leaves every other connection's
  article mode unchanged (the frame, `books/owner-article-held.lisp`). Host
  subject: `fn-owner-chunk-span-at` (`host/owner-host.lisp`).
- Evidence: THEOREM (PRF-377) for the admission, whose host subject is
  `fn-oas-read-span`. The two figure events, `fn-heap-article-slots-are-held`
  and `fn-heap-article-slots-bounds`, are about `fn-heap-article-slots`,
  which no host line reaches at the merged revision (`tools/reach_check.py`
  reports the second as a NEW unreachable subject there): they bound the
  model's slot count, and the running server exercises them only through
  the figure the launcher is handed. MEASURED: the in-flight count under
  the small preset, 32 admitted and not 33 (credits record).
- Exceeded: `440 posting not permitted now; the articles in flight fill the
  memory, try again later` on POST, or `400` and close on a transfer
  (`fn-oas` refusal lines); the process continues; there is no exit code
  for an exhausted pool.
- Not bounded: queue growth from the control channel and BP deliveries is
  outside the slots (the book's header says so).

**M5b** — a disk stall is classified before slot or credit admission (B8).
- Bounded: nothing new; the ordering of two refusals. Under a stalled disk a
  POST is refused with the disk's reason (`440 ... the disk is stalled|slow
  (a write has waited N ms, deadline D ms)`), never with the memory reason.
- Mechanism: `fn-oas-refusal-line` follows `fn-otm-admit-post`.
- Evidence: THEOREM by name only (an event of PRF-377; lane credits-stall,
  merged 2026-09-29): the cited event is an `-unfolds` lemma (a definition
  restated), not a keystone; the keystone that the stall is classified
  first is the time model's (**C1**). MEASURED: the lane's natives
  (`tests.test_native_slow_disk` 10 of 10, `tests.test_native_owner_scheduler`
  8 of 8, hbox).
- Exceeded: as **C1**.
- Not bounded: as **C1**.

**M6** — memory admission by credits.
- Bounded: the ledger M_base + M_cache + sum(U_i + R_i) + E_completion +
  E_runtime <= B. An operation acquires its whole credit (owned and
  reserved) before it allocates; growth within the reserve is never refused;
  a retained credit moves to the cache and is returned only by what is
  actually evicted; an overdraw draws only from the separately funded
  completion reserve. The initial ledger's free credit is exactly the
  article pool and its budget is exactly the figure.
- Mechanism: the review's model (planning/review-2026-09-28-gpt6.md,
  "Memory and zero-copy calls"). Host subjects: `fn-mca-read-span`,
  `fn-mca-take`, `fn-mca-close`, `fn-mca-initial` (`host/owner-host.lisp`),
  `fn-mca-settle`, `fn-mca-batch-done`, `fn-mca-stop`
  (`host/native/owner.lisp`).
- Evidence: THEOREM (PRF-380): every admitted transition from a funded
  ledger is funded. What the theorem is NOT: the credit follows the
  article-slot buffer only; `fn-mcr-retain`, `fn-mcr-evict` and
  `fn-mcr-overdraw` have no host subject; parser and decompressor scratch,
  crypto scratch, dirty pages and the foreign library are not credited
  (the review names all of them as things to budget). A credit that is
  never acquired for an allocation is exactly the case the ledger cannot
  see, so **M6** bounds the credited allocations, not the process.
- Exceeded: `:memory-budget-exhausted` by name, the ledger unchanged; on
  the wire, **M5**'s reply.
- Not bounded: every allocation site that does not acquire a credit.

**M7** — a served connection's memory, named.
- Bounded: per-connection native octets (buffers, the TLS context) times the
  configured capacity against the machine; a capacity the machine cannot
  hold is refused by name at start, and a read step's octets are bounded.
- Mechanism: `fn-cbud-run-decide`; the refusal line
  `refused connections-exceed-memory capacity=... per-connection=K KiB`.
- Evidence: THEOREM over MEASURED constants (PRF-223): the theorem's
  arithmetic is proved; its inputs (`*fn-cbud-tls-octets*` 128 KiB; 1,458 KiB
  a connection with TLS, 1,330 KiB without) are measurements of the runtime's
  and the kernel's allocations (connection-multiplexing record, hbox), and
  the record says no ACL2 transition preserves them. This row is as strong
  as those measurements.
- Exceeded: exit 1 (`:refused`) at start; at run time an over-measurement
  presents as **M1**'s fault.
- Not bounded: the library's allocations past the constant (**T1**).

**M8** — the F8 split.
- Bounded: three measures, adopted 2026-09-28 (f8-reservation record):
  *virtual address space* (reported, never a bar; **M1**'s figure plus the
  ~104 MiB unmodelled); *accountable physical memory*, target 256 MiB;
  *working set*, target at most 128 MiB under a named small profile and an
  active-request mix.
- Mechanism: none yet; the accountable and working-set figures have no
  admission subject.
- Evidence: MEASURED, and the bars UNMET or unmeasured: the old
  reserved-memory verdict is recorded UNMET at 1,179 MiB (the image and
  threads alone are 354 MiB); after 1,000 posts VmRSS 165.7 MiB (83.3 MiB
  anonymous) with 11 threads live against 30 reserved (hbox, developer
  image). The 256 MiB and 128 MiB targets are targets, not evidence that
  the runtime meets them (the review's words); measure at convergence,
  under the release checklist (planning/release-v6.6.0.md, F8).
- Exceeded: nothing refuses on these measures.
- Not bounded: all three, until measured; then bounded only as measured.

## Work per step

The rule (AGENTS.md, D27): bound the work and allocation one request may
cause before consuming it; a quantum that runs out yields or resumes, it
never truncates. The rows below are the places a theorem says so. The
admitted exceptions, where a served step is linear in the store, are listed
under "Not bounded".

**W1** — a wire line and the retained body, per byte.
- Bounded: after any byte the line under construction is at most the line
  limit and the retained body at most the body limit; a command line is
  `*fn-nntp-max-initial-line-octets*` (510) octets.
- Mechanism: `fn-wire-feed-byte`; past a limit the connection closes with
  `:line-overlimit` or `:body-overlimit`. Host subject: the served read step
  that feeds bytes (`fn-own-open` passes the limits).
- Evidence: THEOREM. The event `fn-wire-feed-byte-retained-input-is-bounded`
  is not listed in any proof's events in the registry (the row cites
  PRF-218, the book's proof, for the coordinate); a registry gap, not a
  proof gap.
- Exceeded: the connection closes by name; no article is retained.
- Not bounded: the per-octet representation cost of what is retained (a
  cons per octet) is **M5**'s credit, not this row's.

**W2** — a transit article is bounded before its verdict.
- Bounded: the body an IHAVE/TAKETHIS retains is at most the profile's body
  limit; the connection is refused 437/439 and closed past it (fuzz F2,
  PKT-846).
- Mechanism: `fn-served-run` under `fn-tb-limit`. Host subject: the served
  transit step.
- Evidence: THEOREM (PRF-313). The book says it does not bound the
  per-octet representation cost.
- Exceeded: 437/439 and close.
- Not bounded: as **W1**.

**W3** — a POST past the article bound is refused exactly there.
- Bounded: a POST whose payload exceeds A is refused with `:payload-bound`
  and nothing else in the boundary refusal set; the served bound is the
  installed profile's.
- Mechanism: `fn-sbud-post-boundary`; `fn-osb-install`.
- Evidence: THEOREM (PRF-110, PRF-095).
- Exceeded: refused by name; the reservation may consume a durable
  allocator number (specs/host.md, code 1).
- Not bounded: nothing further.

**W4** — a served read step.
- Bounded: a counted step consumes at most the octets it was given and
  carries at most one submission to the owner; a drain's result does not
  depend on where the octets were cut.
- Mechanism: the served drain. Host subject: the mux's read.
- Evidence: THEOREM (PRF-213).
- Exceeded: not applicable (a structural bound).
- Not bounded: the length of the step's own work inside the owner (**W7**).

**W5** — the LZ4 payload decoder.
- Bounded: the decoder is total and guard-verified; its output is at most
  the recorded length (the only allocation); it runs in quanta whose budget
  strictly decreases per advance, so a call does at most its budget's
  iterations.
- Mechanism: `fn-lz-run` (budgeted, answers `:more` when the budget is
  spent) and `fn-lz-decode-buf` (a whole block on one budget of
  3|c| + n + 2). Host subjects: `fn-lzr-read-step`, `fn-lzr-intern-step`
  (`host/native/io.lisp`), one block per record.
- Evidence: THEOREM (PRF-257, the one cited proof the registry marks
  `certified` at the writing digest). NOT proved: that the block budget
  suffices for every well-formed block (only the literal block is), and no
  split-and-resume theorem exists for `fn-lz-run` (compare **W6**).
- Exceeded: a spent block budget answers `:budget`, a refusal of that
  record, never a truncated value.
- Not bounded: the compressed size of a record is R, the profile's; the
  decoder has no input-size bound of its own (`payload-lz-append` says so).

**W6** — the DEFLATE inflater (COMPRESS, landing).
- Bounded: per call, output at most the limit; a spent quantum answers
  `:yield` with a state that, resumed, equals the unsplit call; total output
  is at most 256 times the input plus 64 KiB, past which the stream is
  refused `(:refused :bomb)` and the connection closes (RFC 8054 §2.2.2).
- Mechanism: fn-zin-feed (pending).
- Evidence: PENDING, lane compress `d90102b90` (PRF-909, PRF-910). The
  per-iteration bound is the definition's measure; a Huffman table build is
  one action whose cost no theorem states (it is bounded by the 320 code
  lengths by construction).
- Exceeded: `:yield` (never truncates) or `(:refused :bomb)`.
- Not bounded: the table build's constant.

**W7** — the owner's quantum order.
- Bounded: a waiting control request is served after at most
  `*fn-osch-bound*` (3) quanta of other classes.
- Mechanism: `fn-osch` gate. Host subject: `fnn-owner-gate-pick`.
- Evidence: THEOREM (PRF-248). It counts quanta, not their length: "the
  quantum's length is the step's own work, bounded per step by the books
  that define it" (the book), which is exactly what "Not bounded" lists
  where it is not.
- Exceeded: not applicable.
- Not bounded: the wall time of a quantum.

**W8** — fairness under sustained POST load.
- Bounded: a waiting control request is admitted within 22 counted quanta
  and 6 sealed batches (`*fn-ocp-pass-bound*` 4 passes), from any scheduler
  value satisfying the invariant.
- Mechanism: the commit pipeline. Host subject: `fnn-owner-commit-pipeline`.
  Native: `tests.test_native_owner_scheduler` (SCN-195).
- Evidence: THEOREM (PRF-901). Counted quanta exclude `:inspect`, in-flight
  `:reader` and empty START-NEXT quanta, so the bound is over the counted
  ones; the excluded ones are bounded by **W7** and **C1**, not here.
- Exceeded: not applicable.
- Not bounded: time (**C1**).

**W9** — a commit batch.
- Bounded: an open batch holds at most `log-batch-records` members
  (`*fn-owb-default-batch-records*`, 64) and `log-batch-octets`
  (`*fn-olr-batch-octets-default*`, 16 MiB), both live config rows; a take
  beyond either leaves the state unchanged.
- Mechanism: `fn-olr-take` is the host's twin (`books/store-log-route.lisp`);
  `fn-owb-boundedp` over `fn-owb-members` is the model's. The book says no host line calls
  `owner-batch`; START loops `fnn-log-bmax` times (`host/native/owner.lisp`)
  and leaves the rest queued, which is host code with no theorem.
- Evidence: THEOREM (PRF-254) for the model; the host-twin event is named;
  the "left queued, not truncated" step is OPEN.
- Exceeded: not applicable.
- Not bounded: the queue's length between STARTs.

**W10** — public exposure, a rate.
- Bounded: steps per address per quantum, from the profile row
  `exposure-steps-per-second`; exhaustion waits and never closes.
- Mechanism: `fn-exp-charge`.
- Evidence: THEOREM (PRF-161). A rate, not work per step.
- Exceeded: the address waits.
- Not bounded: aggregate work across addresses.

**W11** — control waiters.
- Bounded: `fn-cwait-capacity` = control clients minus reserved workers
  (16 - 4 = 12), fixed, not a profile field (PKT-700 is open: the capacity
  from the operator profile); past it a wait is refused by name.
- Mechanism: `fn-cwait`.
- Evidence: THEOREM (the capacity is positive); the capacity's origin is a
  constant, and PKT-701 (wake only the waiters a commit concerns, at most
  12 polls per commit) is open.
- Exceeded: refused by name.
- Not bounded: the polls per commit until PKT-701.

## Stack

**S1** — the depth lint.
- Bounded: no ACL2 function on the host-called closure recurses outside tail
  position without a named bound. The lint (`tools/depth_check.py`, a
  failing `make check` step) reads every raw host file for the ACL2 names it
  calls, closes over the call graph, finds the recursive groups, reads the
  `mbe :exec` branch, and refuses any recursion in neither class of
  `tools/depth_baseline.json`; the `debt` class may only shrink. The count
  is generated below.
- Mechanism: a lint over source, not a runtime check.
- Evidence: MEASURED (the baseline's counts) and, per entry, a named bound
  or a named debt. The consequences of the debt are measured: at 100k
  articles the open died at 30,527 frames in `fn-retain-obligation-ids`
  (about 30,000 retained articles is the limit at the 1,024 KiB stack;
  open-depth record), 26 NNTP commands killed the owner in
  `fn-nntp-group-low` (serve-depth record), and 1,100 principals reached
  about 90,000 frames in `fn-napb-before-last` (peer-list-depth record).
  Those are the debt entries' cost, not a bound.
- Exceeded: **S2**.
- Not bounded: recursion the lint does not see: ACL2's own functions
  (`binary-append` recursed 40,721 frames in the BP persist), defuns a macro
  writes in any other shape, the `:logic` body of a function whose guards
  are not verified (read as `:exec` on this tree; fixed on lane depth-debt),
  raw host Lisp (unlinted on this tree; **S1b**), foreign code and the
  reader.

**S1b** — the debt driven to zero (landing).
- Bounded: lane depth-debt `fdb14fb80` takes the baseline to 9 debt
  entries (the D27 walks 116 to 0; the nine left are functions whose guards
  are not verified: `fn-bs-take`, `fn-bs-zeros`, `fn-lg-log`, `fn-lg-pack`,
  `fn-lg-unpack`, `fn-srs-decode`, `fn-ores-sealed-plan`,
  `fn-bpnr-retired-names`, `fn-bpnrb-dec`), and adds
  `tools/raw_depth_check.py` over the 1,506 raw host functions (11 bounded,
  0 debt).
- Mechanism: the same lint, plus the raw one.
- Evidence: PENDING. Even at zero the row stays MEASURED: a lint that finds
  nothing is not a theorem that the stack suffices, and no document says the
  lint becomes a different gate at zero.
- Exceeded: **S2**.
- Not bounded: raw recursion through `funcall`, `apply` or a function
  value; everything in **S1**'s list.

**S2** — the control stack.
- Bounded: every thread's control stack is `:stack-kib` (1,024 KiB,
  `books/profile-limits.lisp`), the same for every profile
  (`fn-heap-stack-kib` ignores its profile argument), and the reservation
  holds stack plus 4 MiB runtime for every thread the node runs. The
  measured minimum need is 142 KiB (served-line-iterative), about 7x below
  the constant.
- Mechanism: `--control-stack-size` in every launcher (`packaging/fn`,
  `tools/build_native_host.sh`).
- Evidence: THEOREM (PRF-198) for the reservation; the constant itself is
  a chosen number, and its sufficiency is what **S1**'s lint approximates.
- Exceeded: a control stack exhaustion is re-signalled as global and exits 4
  (`:fault`), the fault line naming the ACL2 function it happened in; some
  deaths are SBCL's "fatal (pseudo-atomic)" with no clean exit at all (serve-depth
  record). There is no dedicated code; a stack exhaustion is a crash, and
  the model's job (**S1**) is that a served path never reaches it.
- Not bounded: the OpenBSD guest's constants were never run under this row.

## TLS

**T1** — TLS has no bound of its own.
- Bounded: only the plaintext prefix a read consumes before STARTTLS
  (consumed <= the octets given; PRF-213) and the memory constant per
  connection (**M7**). The brief's `tools/tls_check.py` does not exist; the
  "25% build gate" is `tools/throughput_gate.py`, whose baseline is
  plaintext (no TLS metric; its only TLS call is `fnn-tls-initialize` before
  the allocation probe); `tls64k` in the toolchain name is SBCL's
  `--tls-limit` (thread-local storage symbols, `:tls-limit` in
  `books/profile-limits.lisp`), not Transport Layer Security.
- Mechanism: the system libssl/libcrypto (OpenSSL 3.0+ or LibreSSL 3+)
  through SBCL's FFI (`host/native/tls.lisp`); handshakes are bounded by
  host constants, not theorems: a 10 s handshake deadline, at most 8
  handshakes per loop, a queue of at most 256 waiting at most 10 s, then
  `busy` or `timeout`, and "TLS never waits inside OpenSSL"
  (specs/host.md). The refusal line `tls refused reason={handshake|timeout|
  closed|refused|busy|other}` is `fn-cbud-tls-refusal-line` (PKT-640).
- Evidence: THEOREM for the prefix (PRF-213); MEASURED for the memory
  (`*fn-cbud-tls-octets*`, 128 KiB, connection-multiplexing record, hbox,
  OpenSSL 3.3.1); the library itself is TRUSTED, stated in
  `host/native/tls.lisp` and HST-016 (specs/host.md), and it has no `A-*`
  row in specs/failures.md and no encapsulate: a gap this contract names.
- Exceeded: a handshake past its deadline is `timeout`; a peer stalling
  mid-record is `:timeout`, the same as an idle socket; a certificate that
  does not verify is `fnn-tls-verify-error`; nothing degrades to plaintext.
- Not bounded: the library's CPU; its allocations beyond the measured
  constant; the certificate parse and the chain and hostname check behind
  `:tls-up` (trusted integration evidence); LibreSSL on OpenBSD (never
  exercised, tls-reload record); peer client contexts cannot be reloaded;
  TLS throughput (never measured).

## Time

Time is classification, never latency (planning/design-time-model-2026-09-27.md):
every POST is told exactly one of *accepted* (`240`), *refused* (`440`/`441`
with its reason) or *uncertain* (`441 posting failed; the outcome is
uncertain, do not repost`, then close), and a deadline is a notification,
never a cancellation. The barrier keeps running past D and past H. The F4
bars (planning/release-v6.6.0.md §2b) are numbers measured once, at
convergence; this document states what is guaranteed about each outcome
class and quotes what has been measured with its scope.

**C1** — the disk's mode and what a member is told.
- Bounded: with D = `*fn-otm-deadline-default-ms*` (5,000 ms, `slow`) and
  H = `*fn-otm-stall-default-ms*` (30,000 ms, `stalled`; both live config
  rows, H never below D): a barrier pending at least D sheds new POSTs by
  name (**M5b**'s reply); a barrier pending at least H tells every member
  *uncertain* at a reading at most since + H + L, where L is the lateness of
  one committer wake; a stall tells no member its outcome; a failed barrier
  answers every member uncertain; readers never wait on the barrier
  (`fn-otm-barrier-reader-bound`).
- Mechanism: `fn-otm-admit-post`, the committer's clock events. Host
  subjects: `fnn-owner-disk-event`, `fnn-owner-disk-wait-ms`,
  `fnn-owner-disk-admit`, `fnn-owner-commit-event` (`host/native/owner.lisp`).
- Evidence: THEOREM (PRF-311, PRF-255) under stated hypotheses that are NOT
  proved: the committer is not blocked on the device (the syncer is); L
  bounds the scheduler's lateness of one timed wait and the adopted bar is
  L <= 1,000 ms, a host scheduling assumption measured at convergence; the
  host's CPU is not starved; the barrier's completion event or the tick
  reaches the committer. MEASURED (hbox, developer and production images,
  `tests.test_native_slow_disk`): during a 30.4 s barrier stall, 98 reads
  with max 0.003 s and 49 status calls with max 0.168 s; a shed POST refused
  in 0.001 s; a held POST answered 240 0.008 s after the device returned
  (time-model record); with D 2,000 and H 6,000 the posters were told
  uncertain at 6.003 s (time-model-2 record).
- Exceeded: an uncertain publication is the fence, exit 3; nothing turns
  a timeout into a failure or into absence ("a timeout is never evidence
  that a write failed", the review).
- Not bounded: the device's latency ("unbounded in latency", the design;
  HST-026); CPU starvation; wall time of any quantum; a cold extent read
  under a stalled device holds the owner, health included, for as long as
  the `pread` takes, until A4 (**C3**); mutating control's tail; the
  told-uncertain article may still be stored (the documented ambiguity).

**C2** — the health verdict.
- Bounded: `health` holds the disk state exactly when the disk is stalled or
  full, and its exit code (0 all clear, 19 unobserved, 20 to 27 the first
  held state) is 0 or past every outcome code, so the two tables cannot
  overlap.
- Mechanism: `operator CONFIG health`.
- Evidence: THEOREM (PRF-358, PRF-172). The disk state's exit 28 is
  PROVISIONAL (specs/host.md; PKT-853 (b) open: health's exit while
  `stalled`).
- Exceeded: the verdict is the exit.
- Not bounded: the latency of the verdict itself (the F4 bar: cached health
  p99 <= 250 ms, <= 1 s under the injected stall; at convergence).

**C3** — the time bars (landing).
- Bounded: a member is answered once; a late completion is consumed once;
  a deadline keeps the I/O owned (the credit is not freed because a client
  timed out); a page that is late past `read-dependency-ms` (5,000 ms) is
  `403 article temporarily unavailable`, never `430`/`423`; a restart forgets
  the previous clock domain.
- Mechanism: `fn-otb-issue`, `fn-otb-answer-early` and `fn-otb-complete` in
  the commit pipeline; the late-page bar has no host call site until A4.
- Evidence: THEOREM (PRF-384; lane time-bars, merged 2026-09-29). Its
  natives are classification, not timings: the held poster was told
  uncertain at 30.002 s (hbox).
- Exceeded: as **C1**.
- Not bounded: as **C1**.

**C4** — the outcome classes.
- Bounded: every native command exits with the code of its outcome class
  from one table (generated below); the codes are disjoint; a fence is
  never masked and a refusal is never reported as one.
- Mechanism: `fn-outcome-code`; the host's `+fnn-exit-*+` constants are
  read from it when the image is built.
- Evidence: THEOREM (PRF-143).
- Exceeded: a process ended by a signal exits 128 plus the signal, outside
  the table; SBCL's own deaths (**M1**, **S2**) are outside it too.
- Not bounded: nothing further.

## Disk

**D1** — no data cap.
- Bounded: nothing by the code. The size of an article, the groups it
  names, the transactions a store holds and the bytes it may reach are the
  operator's (T, H, A, G); admission refuses at the operator's own bound by
  name, and reclaim keeps the record count (`fn-rclp-events-keep-the-length`):
  it frees bytes, never transactions, so a count-full store stays count-full
  (Q11; ember's choice between (a) as is and (b) an INN-style `remember`
  window is pending in the expiry packet).
- Mechanism: the capacity vector; `store reclaim`.
- Evidence: THEOREM (PRF-138, PRF-119).
- Exceeded: refused by name at T, H or A (code 1).
- Not bounded: growth under no release: "every class grows monotonically
  until admission refuses" (specs/storage.md).

**D2** — a full disk.
- Bounded: before an append the owner checks `statvfs` against
  `fn-otm-space-need` (the maintenance reserve, plus twice
  `log-batch-octets`, plus `disk-reserve-octets`, default 64 MiB); below it
  the disk is `full`: POST `440`/`441 ... the disk is full`, health
  `disk mode=full`, exit 28 (provisional). A journal append that meets
  ENOSPC is truncated or the journal closed, and the file agrees with the
  replay or shows the gap.
- Mechanism: `fn-otm-admit-post`; the journal writer. Host subject:
  `fnn-owner-disk-admit`.
- Evidence: THEOREM (PRF-359, PRF-360). An unobserved figure is never
  `full`.
- Exceeded: an ENOSPC that surfaces on the append itself, or at `fsync`
  under delayed allocation, is the recovery event: every member uncertain,
  exit 3 (`:fenced`), never a silent rollback and never further mutation
  (specs/crash-model-v2.md; a failed fsync fences nothing).
- Not bounded: the filesystem's accounting of free space; a second writer
  (A-HOST-EXCLUSIVE-READ assumes none).

**D3** — the checkpoint and the maintenance reserve.
- Bounded: a checkpoint is deferred when its estimate exceeds the budget or
  the free space; an admitted profile starts reserved and room is within
  the bound.
- Mechanism: `fn-ockp-decide`; `fn-smr-roomp`.
- Evidence: THEOREM (PRF-200, PRF-129). The checkpoint's own space check
  has no keystone in PRF-129 yet (specs/storage.md); the estimate is what is
  proved, not the written size.
- Exceeded: deferred, by name; an ENOSPC during the write is **D2**'s
  recovery event.
- Not bounded: the checkpoint's transient (a second copy beside the log),
  estimate-checked only; a compaction's memory is not yet bounded by the
  step (PKT-842).

**D4** — on-disk growth per accepted article.
- Bounded: the record log, per article and at every crash point. An
  accepted article's record is in the bytes on disk: the kernel recovered
  from every admissible crash image of every cut of the host's append, of
  its fence (the barrier `:ok`, or failed after landing the environment's
  selection), of the segment's extension and of recovery holds the
  acknowledged record, with no trailer assumption
  (`fn-lgu-acknowledged-article-is-recoverable-at-every-crash-point` and
  its recovery half; the tear keeps the prefix below the frontier and the
  scan reads a complete prefix's entries first). The log grows per batch by
  its entries, each a whole number of write units
  (`fn-lg-entry-len-is-units`; the frontier advances by the batch's log
  length at the fence, `fn-lgk-fence`), and the segment file grows only to
  the extension target: whole units past the old extent, at least twice it
  so extensions are logarithmic in the log's size
  (`fn-olr-extension-target-is-an-extent`).
- Mechanism: P-BATCH's one positioned write per batch at the frontier; the
  extension's zeros past the end (`posix_fallocate`, then one barrier).
- Evidence: THEOREM (PRF-936; PRF-244, PRF-268). Not bounded here: the
  checkpoint's growth per article (**D2**'s transient, PKT-842), the
  indexes', the service log (append-only, never rotated; docs/operator.md)
  and the Message-ID history kept forever (D13). MEASURED example, unchanged:
  40,000 articles of 2 KiB gave a 268 MB log and a 129 MB checkpoint
  (specs/storage.md).
- Exceeded: **D2**.
- Not bounded: this row. What it would take: a bytes-per-record theorem
  over the log frame and the checkpoint encoding (the frame's fixed
  overhead plus the record's octets plus the index rows), with the
  checkpoint's estimate proved an upper bound of its written size.

**D5** — expiry releases only what no holder keeps; online compaction
(landing in part).
- Bounded: a per-group expiry policy releases through the one reclaim path,
  and an article a holder keeps is never expired (RET-008, PRF-918; lane
  expiry, merged 2026-09-29); `store compact` on a live owner served as
  bounded batches off the mutex (PKT-868, lane operations `baec98157`,
  PRF-908).
- Mechanism: `store reclaim`, offline on this tree (it refuses while an
  owner runs: Q16, the R1 list); online reclaim is approved and not
  started in code (operations record, design 3b).
- Evidence: THEOREM for the policy (PRF-918: what the operator sets reads
  back, the age instant stays within the keep and purge bounds, a held
  article is not expired; none of its events is a work or space bound, so
  this row cites it for the release path, not for a bound); PENDING for
  online compaction.
- Exceeded: as **D2**.
- Not bounded: the transient of **D3**; expiry's own pass is offline on this
  tree, so its work per step is the offline reclaim's, and at the merged
  revision `tools/hot_path_check.py` and `tools/depth_check.py` report two
  new recursions on that path (`fn-xpy-walk`, `fn-xpy-header-block` in
  books/expiry.lisp): a walk over the article set per reclaim, unbounded by
  a theorem.

## When reality exceeds the model

The rule in every row: a named outcome, never a degraded mode. The outcomes
are the seven classes of `*fn-outcome-codes*` (generated below; specs/host.md
"CLI exit codes"), the health verdicts (0, 19 to 27, and the provisional
28), and the wire replies (`240`, `440`, `441`, `400`, `403`, `436`,
`437`/`439`, `431`). Two outcomes are NOT named and this document does not
pretend they are: SBCL's own death when the dynamic space (**M1**) or the
control stack (**S2**) is exhausted, which reaches exit 4 when the
condition is catchable and is a runtime crash when it is not. The model's
claim is that the admission rows keep a served path from reaching either;
the measured stack deaths in **S1** are the cases where it did not.

## The trust boundary

The rows rest on the named assumptions of specs/failures.md (the `A-*` rows,
counted below) and the encapsulates of `books/assumptions.lisp`, and on
nothing unnamed except the two gaps this document names. The resource rows
use: A-DURABILITY and A-WRITE-ISOLATION (**D2**, the barrier), A-HOST and
A-HOST-EXCLUSIVE-READ (every host subject), A-DURABLE-EXTENT and
A-DURABLE-LZ (**W5**), A-PGS-HOST-IO (the page store's reads), and A-EXTRACT
(the extracted image, a deployment coordinate). Two things the rows depend
on have no `A-*` row: the TLS library (**T1**) and the SBCL runtime itself
(its collector, its dynamic-space cap, its control-stack guard page), which
every memory and stack row's "exceeded" field runs into. Naming them would
take one row each with the qualification evidence that stands in for a
proof, as A-CRYPTO-NATIVE does for BLAKE3.

## Not bounded

The list, and what each would take. Nothing here is accepted; it is stated.

1. **The process's physical memory** (**M8**): accountable physical and
   working set are targets, unmeasured. Takes: the convergence measurement
   under the named small profile and request mix; then admission subjects
   for the terms the review names (parser and decompressor scratch, crypto
   scratch, dirty pages, foreign allocations) so the ledger of **M6** sees
   them.
2. **Allocations that acquire no credit** (**M6**): cache, evict and
   overdraw have no host subject; the credit follows the article-slot
   buffer only. Takes: a host subject per allocation site, each with its
   `fn-mcr-acquire`.
3. **The collector's pause and its older generations** (**M1**, **M4**):
   no file admits or bounds them; F4 measured 181 to 218 MB of garbage
   against the model's two-nursery term. Takes: a generation term in the
   figure with a measurement behind it, and a pause figure in the time
   model's hypotheses.
4. **Served steps linear in the store**, admitted in the evidence records:
   the status render is O(N) under the owner gate as an `:inspect` quantum
   (0.2 to 0.3 s at 100k; health-truth-status record) and quadratic in the
   signed count; a live reconfigure runs three full replays plus an O(n)
   refresh (owner-scheduler-2 record, "whole-state revalidation on a served
   path"); a worst-case hash bucket is an O(N) lookup (catalog-columns,
   proto-adt records); the header fold is quadratic per field (deferred,
   header-limits-profile record); the pins are scanned linearly per POST
   (post-identity-index record); BP offers are linear per offer and the
   drain quadratic (PKT-653, bp-cursors record); `poll` is O(n) in
   descriptors (connection-multiplexing record); lane reports add the
   per-POST fold over the budget's used length, `fn-lgk-fence` O(N) per
   batch, and `fnn-owner-publish-captured` O(store) on the POST that makes
   it due. Takes: each one either an indexed access with a bounded-cursor
   refinement (the review's classification) or a `D27:` debt entry with an
   owner, so the list can only shrink.
5. **The queue between STARTs** (**W9**) and **the polls per commit**
   (**W11**): host code with no theorem; PKT-700 and PKT-701 open.
6. **Stack recursion the lint does not see** (**S1**): builtins, macro
   shapes, raw Lisp on this tree, function values. Takes: lane depth-debt's
   raw lint landing, and a builtin-recursion class in the baseline.
7. **The TLS library** (**T1**): CPU, allocation past 128 KiB, the
   certificate and chain checks, LibreSSL. Takes: an `A-*` row with its
   qualification, and a measurement of the library's allocation under the
   connection capacity.
8. **Time** (**C1**): the device, CPU starvation, L, the cold read before
   A4, the mutating control tail. Takes: the F4 measurements at convergence
   (numbers, with their scope), and A4 (asynchronous page faults outside the
   owner mutex) for the cold read.
9. **Disk growth per article** (**D4**) and **the checkpoint's transient**
   (**D3**): no theorem. Takes: the bytes-per-record theorem and the
   estimate-is-an-upper-bound theorem named in those rows.
10. **Growth under no release** (**D1**): the Message-ID history forever,
    the service log never rotated, transactions never reclaimed (Q11).
    Takes: ember's D13 decision, then a summary structure with its own
    bound, and a rotation policy for the service log.

## Closure (X)

What the bounds above assume of the state they are entered in, and what a
refusal leaves behind (lane closure-theorems, after B10: a configuration
record on a transaction-full store after a checkpoint left a store no open
accepted, because refused POSTs had consumed ids no reader accounted for).

- **X1** Refusal is effect-free, or says what it consumes. Per host
  refusal entry, the ACL2 function and the theorem are `books/refusal-effect`'s
  header table. An unserved group, an unaffordable budget and a configuration
  request the owner does not admit leave the owner they were given (by
  definition). The full-store POST refusal is NOT effect-free, by design:
  the reservation is taken before the prepare decides, and the refusal
  consumes it; the composed theorems say exactly what: the records, the
  groups and the capacity are what they were, the files' frontier and the
  node's next txid are one higher. The readers of ids account for it: the
  configuration record takes the node's next txid; the open joins the
  records' and the configuration records' next ids (lane limits-live-2's
  `fn-ofr-loop-ok-within-frontier`, landing); the export carries the frontier
  (PRF-205). Scope: the store node model; the host's routes are the named
  functions. When reality exceeds the model: a reader that computes a frontier
  from one record kind alone is B10 again, and section X2's check is what
  catches a new kind.
- **X2** The alphabets agree, and the premises are listed.
  `tools/alphabet_check.py` (a `make check` step) reads the configuration
  deltas' declared kinds, encoder, decoder, dispatcher and every writer, and
  the store events' encoder, decoder, kind reader and the replay's dispatch,
  from the source; it fails when a writer produces a kind a reader lacks.
  `tools/premise_audit.py` lists every hypothesis `(R v)` of a theorem whose
  subject a host line reaches that no hosted theorem establishes (never
  concluded, preserved only, or established only by a model), against a
  shrink-only baseline (planning/premise-baseline.json): 1,011 of 1,528 at
  dev 1922efe84, 114 of them relation-shaped. Neither is a bound; both are
  the contract's own premises made visible.

## Generated

The block below is written by `python3 tools/resource_contract.py --write`
and checked by `--check` in `make check`: every theorem it names exists in
its book, every proof id is in the registry, every record is in the tree,
the constants are the books' current values, and no cited book is red at
its digest. `--table` prints each cited book's certification verdict from
the held manifests and each proof's registry status; `--check --strict`
(the release form) fails a cited book that no held manifest certifies at
its current bytes.

<!-- BEGIN resource-contract: generated by tools/resource_contract.py --write; do not edit -->

Rows, with what each cites. `landing` names a lane whose books are
not on this tree yet; its citations are checked once they land.

| Row | Theorems (book: events) | Proofs | Records | Landing |
| --- | --- | --- | --- | --- |
| M1 | `books/heap-figure`: `fn-heap-decide-refuses-exactly-past-the-machine`, `fn-heap-decision-exit-code-of-a-refusal`, `fn-heap-operation-decide-holds-the-store`; `books/heap-reservation`: `fn-heap-init-decide-fits-the-budget-and-the-machine`, `fn-heap-init-decide-refuses-the-operators-request-past-the-budget`, `fn-heap-reserve-decide-holds-every-thread-the-node-runs`, `fn-heap-reserve-thread-refusal-exits-1` | PRF-198 | `planning/evidence/heap-from-profile-2026-09-26.md`, `planning/evidence/heap-bounds-2026-09-28.md` |  |
| M2 | `books/heap-store-figure`: `fn-heap-store-figure-holds-every-store`, `fn-heap-store-history-holds-payload-and-memberships`, `fn-heap-records-retained-within-the-terms` | PRF-198, PRF-314 | `planning/evidence/heap-bounds-2026-09-28.md` |  |
| M2b | `books/heap-store-figure`: fn-heap-record-charge-is-the-budgets-charge (pending), fn-heap-record-charge-covers-the-state (pending) | none | none | lane/heap-pool (heap-bounds-2 resumed; uncommitted WIP on 2026-09-28, sha at merge) |
| M3 | `books/heap-breakdown`: `fn-heap-breakdown-sums-to-the-reservation`, `fn-heap-breakdown-is-inits-reservation` | PRF-375 | `planning/evidence/f8-reservation-2026-09-28.md` |  |
| M4 | `books/heap-open-nursery`: `fn-heap-open-nursery-trigger-bounds`, `fn-heap-store-figure-holds-every-store-at-the-open-trigger` | PRF-364 | none |  |
| M5 | `books/owner-article-slots`: `fn-oas-read-span-admits-within-the-slots`; `books/owner-article-held`: `fn-oah-read-span-leaves-the-others-article-mode`; `books/heap-store-figure`: `fn-heap-article-slots-are-held`, `fn-heap-article-slots-bounds` | PRF-377 | `planning/evidence/zero-copy-commit-2026-09-28.md` |  |
| M5b | `books/owner-article-slots`: `fn-oas-refusal-line-follows-the-disk-unfolds` | PRF-377 | `planning/evidence/credits-stall-2026-09-28.md` |  |
| M6 | `books/memory-credits`: `fn-mcr-transitions-keep-funded`, `fn-mcr-acquire-refuses-exactly-past-the-budget`, `fn-mcr-grow-within-the-reserve-is-admitted`, `fn-mcr-overdraw-is-within-the-completion-reserve`; `books/owner-credits`: `fn-mca-read-span-keeps-funded`, `fn-mca-commit-steps-keep-funded`, `fn-mca-initial-funds-exactly-the-articles` | PRF-380 | `planning/evidence/f8-reservation-2026-09-28.md`, `planning/evidence/credits-2026-09-28.md` |  |
| M7 | `books/connection-budget`: `fn-cbud-run-decide-refuses-exactly-past-the-limit`, `fn-cbud-step-read-octets-is-bounded`, `fn-cbud-deltas-refusal-keeps-the-capacity-held` | PRF-223 | `planning/evidence/connection-multiplexing-2026-09-26.md` |  |
| M8 | none (measured or open) | none | `planning/evidence/f8-reservation-2026-09-28.md` |  |
| W1 | `books/wire`: `fn-wire-feed-byte-retained-input-is-bounded` | PRF-218 | none |  |
| W2 | `books/transit-bound`: `fn-tb-served-run-retains-at-most-the-body-limit` | PRF-313 | none |  |
| W3 | `books/store-budget-naming`: `fn-sbud-post-boundary-refuses-exactly-past-the-profile-bound`; `books/owner-served-bound`: `fn-osb-install-serves-the-profile-bound` | PRF-110, PRF-095 | none |  |
| W4 | `books/served-tls-prefix`: `fn-served-step-counted-consumed-is-bounded`, `fn-served-step-counted-carries-at-most-one-submission`, `fn-served-drain-run-is-boundary-independent` | PRF-213 | none |  |
| W5 | `books/payload-lz`: `fn-lz-run-out-len-bound`, `fn-lz-decode-buf-out-len-bound`, `fn-lz-seq-budget`, `fn-lz-advance-budget` | PRF-257 | none |  |
| W6 | `books/deflate-inflate`: fn-zin-feed-out-bound (pending), fn-zin-loop-stops (pending), fn-zin-loop-split-budget (pending), fn-zin-feed-bomb-bound (pending) | PRF-909, PRF-910 | none | lane/compress d90102b90 |
| W7 | `books/owner-scheduler`: `fn-osch-control-waits-at-most-the-bound` | PRF-248 | none |  |
| W8 | `books/owner-commit-fairness`: `fn-ocf-control-waits-at-most-the-bound`, `fn-ocf-potential-at-most-twenty-two`, `fn-ocf-seal-potential-at-most-six` | PRF-901 | none |  |
| W9 | `books/owner-batch`: `fn-owb-batch-within-bounds`; `books/store-log-route`: `fn-olr-take-keeps-the-bounds` | PRF-254 | none |  |
| W10 | `books/public-exposure`: `fn-exp-charge-bounds-steps-per-quantum`, `fn-exp-charge-waits-and-never-closes` | PRF-161 | none |  |
| W11 | `books/consumer-wait`: `fn-cwait-capacity-is-positive` | none | none |  |
| S1 | none (measured or open) | none | `tools/depth_check.py`, `tools/depth_baseline.json`, `planning/evidence/open-depth-2026-09-28.md`, `planning/evidence/serve-depth-2026-09-28.md`, `planning/evidence/peer-list-depth-2026-09-28.md` |  |
| S1b | none (measured or open) | none | `tools/raw_depth_check.py`, `tools/raw_depth_baseline.json` | lane/depth-debt fdb14fb80 |
| S2 | `books/heap-reservation`: `fn-heap-reserve-decide-holds-every-thread-the-node-runs` | PRF-198 | none |  |
| T1 | `books/owner-tls-prefix`: `fn-own-read-tls-prefix-consumed-is-bounded`; `books/served-tls-prefix`: `fn-served-step-counted-consumed-is-bounded` | PRF-213, PRF-223 | `planning/evidence/connection-multiplexing-2026-09-26.md`, `planning/evidence/tls-reload-2026-09-26.md` |  |
| C1 | `books/owner-time-model`: `fn-otm-stall-tells-no-member-its-outcome`, `fn-otm-shed-iff-slow`, `fn-otm-wait-stays-within-the-stall`, `fn-otm-f4w-stall-within-h`, `fn-otm-barrier-reader-bound`; `books/owner-batch`: `fn-owb-fence-failed-answers-uncertain` | PRF-311, PRF-255 | `planning/evidence/time-model-2026-09-27.md`, `planning/evidence/time-model-2-2026-09-27.md` |  |
| C2 | `books/owner-time-model`: `fn-otm-health-disk-held-iff-stalled-or-full`; `books/native-health`: `fn-nh-exit-code-is-zero-or-past-the-outcome-codes` | PRF-358, PRF-172 | none |  |
| C3 | `books/owner-time-bars`: `fn-otb-a-member-is-answered-once`, `fn-otb-a-late-completion-is-consumed-once`, `fn-otb-a-deadline-keeps-the-io-owned`, `fn-otb-a-late-page-is-unavailable-never-absent` | PRF-384 | none |  |
| C4 | `books/outcome-class`: `fn-outcome-code-separates-the-classes`, `fn-outcome-code-is-fenced-iff-fenced` | PRF-143 | none |  |
| D1 | `books/store-capacity-vector`: `fn-cvec-roomp-is-within-the-profile`, `fn-cvec-held-row-within-its-figure`; `books/store-reclaim-pack`: `fn-rclp-events-keep-the-length` | PRF-138, PRF-119 | none |  |
| D2 | `books/owner-time-model`: `fn-otm-admit-keeps-the-space-need`; `books/owner-time-journal-writer`: `fn-otm-jw-file-reads-agrees-or-gap` | PRF-359, PRF-360 | none |  |
| D3 | `books/owner-checkpoint-writer`: `fn-ockp-decide-defers-by-the-estimate`; `books/store-maintenance-reserve`: `fn-smr-roomp-is-within-the-bound` | PRF-200, PRF-129 | none |  |
| D4 | `books/store-log-durable`: `fn-lgu-acknowledged-article-is-recoverable-at-every-crash-point`, `fn-lgu-acknowledged-article-is-recoverable-at-every-cut-of-recovery`; `books/store-log-crash`: `fn-lg-entry-len-is-units`; `books/store-log-extend`: `fn-olr-extension-target-is-an-extent` | PRF-936, PRF-244, PRF-268 | `planning/evidence/byte-model-2026-09-29.md` |  |
| D5 | `books/expiry-verdict`: `fn-xpy-releasablep-is-rule-or-expired-and-unheld`, `fn-xpy-held-article-is-not-expired` | PRF-918 | `planning/evidence/expiry-q11-2026-09-28.md` | lane/operations baec98157 (PKT-868, PRF-908: online compaction) |
| X1 | `books/refusal-effect`: `fn-rfx-unserved-prepare-is-unchanged-by-definition`, `fn-rfx-unaffordable-prepare-is-unchanged-by-definition`, `fn-rfx-refused-reconfigure-is-unchanged-by-definition`, `fn-rfx-refused-post-keeps-records`, `fn-rfx-refused-post-keeps-configuration`, `fn-rfx-refused-post-consumes-one-txid`, `fn-rfx-config-record-txid-is-the-node-next-by-definition` | none | `planning/evidence/closure-theorems-2026-09-29.md` |  |
| X2 | none (measured or open) | none | `planning/evidence/closure-theorems-2026-09-29.md` |  |

Constants the rows quote, read from the books that define them.

| Constant | Value | Meaning | Defined in |
| --- | --- | --- | --- |
| `*fn-heap-list-octets-per-octet*` | 16 | octets per octet of an octet list | `books/heap-store-figure.lisp` |
| `*fn-heap-article-slot-budget*` | 67,108,864 | octets, the article pool | `books/heap-store-figure.lisp` |
| `*fn-heap-article-slots-most*` | 32 | slots at most | `books/heap-store-figure.lisp` |
| `*fn-cbud-tls-octets*` | 131,072 | octets per TLS connection, MEASURED | `books/connection-budget.lisp` |
| `*fn-nntp-max-initial-line-octets*` | 510 | octets, a command line | `books/nntp-syntax.lisp` |
| `*fn-osch-bound*` | 3 | other-class quanta before a control quantum | `books/owner-scheduler.lisp` |
| `*fn-ocp-pass-bound*` | 4 | passes | `books/owner-commit-pipeline.lisp` |
| `*fn-owb-default-batch-records*` | 64 | records per batch, default | `books/owner-batch.lisp` |
| `*fn-olr-batch-octets-default*` | 16,777,216 | octets per batch, default | `books/owner-log-route.lisp` |
| `*fn-otm-deadline-default-ms*` | 5,000 | ms, D (disk slow) | `books/owner-time-model.lisp` |
| `*fn-otm-stall-default-ms*` | 30,000 | ms, H (disk stalled) | `books/owner-time-model.lisp` |
| `*fn-otm-cadence-default-ms*` | 1,000 | ms, the committer's clock cadence | `books/owner-time-model.lisp` |
| `:stack-kib` | 1,024 | KiB, every thread's control stack | `books/profile-limits.lisp` |
| `:tls-limit` | 65,536 | symbols, SBCL thread-local storage (not Transport Layer Security) | `books/profile-limits.lisp` |
| `:max-connections` | 32 | served connections, default | `books/profile-limits.lisp` |
| `:control-clients` | 16 | control clients | `books/profile-limits.lisp` |
| `:gc-nursery-mib` | 64 | MiB, the collector's nursery | `books/profile-limits.lisp` |
| `:fixed-threads` | 12 | threads the node always runs | `books/profile-limits.lisp` |

The small preset (`*fn-heap-small-request*`, books/heap-figure.lisp);
A, the article bound, is inherited from the development preset.

| Field | Value |
| --- | --- |
| T max-transactions | 16,384 |
| H max-history-octets | 8,388,608 |
| R max-record-octets | 196,608 |
| G max-groups-per-article | 16 |
| K max-open-suffix | 128 |

The outcome classes and their codes (`*fn-outcome-codes*`, books/outcome-class.lisp).

| Class | Code |
| --- | --- |
| `:accepted` | 0 |
| `:refused` | 1 |
| `:fenced` | 3 |
| `:fault` | 4 |
| `:usage` | 5 |
| `:interrupted` | 6 |
| `:not-connected` | 7 |

Counts.

- Depth lint baseline (tools/depth_baseline.json): 193 debt entries (data-sized recursion on a host-called path with no bound), 170 bounded.
- Named assumptions: 16 `A-*` rows in specs/failures.md, 13 encapsulates in books/assumptions.lisp.
- The throughput gate's tolerance (tools/throughput_gate.py, planning/throughput-baseline.json): 25% over the baseline per operation, plaintext.

<!-- END resource-contract -->
