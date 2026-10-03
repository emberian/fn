# Whole-system correctness: Astra's independent answer (w01, gpt-6-astra, read-only at 4aa332295, 2086 s)

Written WITHOUT reading build/coordinator/ (brief: build/lanes/codex-w01-wholesystem/build/codex/w01/CONSULT.md). Pasted verbatim by codex-liaison-11; liaison fact-check and Astra's reconciliation with decisions/whole-system-correctness-2026-10-03.md follow at the end when done.

1. Diagnosis: the sequential semantic machine is substantial; its refinement is not yet connected to the host's concurrent ownership transfers (§1, §3).
2. Diagnosis: local locks and carried invariants do not establish publication, exception containment, lifetime, or shutdown composition (§3–4).
3. The theorem should be crash-aware, snapshot-labelled observational trace refinement, including command continuations and effect receipts (§5).
4. Prove the abstract concurrent machine; check its generated host realization; name runtime, I/O and cryptographic assumptions instead of assuming “the host is correct.”
5. First: land one declared, generated connection handoff/stop protocol, with a forced adopt-versus-stop witness (§6.1).
6. Next: generate fault containment and capture/execute/settle boundaries, retaining resources until physical return (§6.2–3).
7. Then: connect that concurrent action model to the existing owner, served-chain and crash refinements (§6.4–6).
8. Generate coordination and ownership transfers, with checked handwritten leaves; generating mutex acquisition alone is insufficient (§7).
9. Worst defects: committer silently catches core faults (host/native/owner.lisp:3704; io.lisp:75–89); adoption can enqueue after mux shutdown (mux.lisp:1382–1397,1312–1334).
10. Third: publication drops its worker registration before final shared cleanup (owner.lisp:5147–5162), although close relies on an empty worker roster (4804–4811,6258–6285).

# Independent whole-system consultation

Source coordinate: `4aa332295c85f03f5a97d7b0ac2228f9b95ab1e9`. This is a source review, not a new certification, runtime qualification, or deployment claim. I read the consultation and AGENTS guidance, inspected the four central native files and relevant callers, books, declarations, gates and specifications. I ran only read-only source/git inspections and small standard-library Python inventories, and wrote this answer. I did not read the other deputy's answer or any file in `build/coordinator/`; references to that directory inside permitted source were not followed. No ACL2, build, test campaign, remote command or tracked edit was performed.

Line references are relative to this worktree and this revision. Quotes are excerpts, sometimes identifiers or single expressions; ellipses in explanatory prose do not change a theorem's hypotheses. “BUG” below means a source-level counterexample or fault path, **not** an observed production incident. Dynamic reachability and frequency are explicitly separated. **UNVERIFIED** labels a missing establishment, including completeness of indirect call/effect analysis. The appendices inventory every requested Lisp file and explicit synchronization site; they are not represented as a semantic race detector.

## 1. What is actually composed today

There is considerably more than isolated parser correctness here. There is also considerably less than a theorem about the running concurrent node. The distinction is the *subject* of the theorem and the relation between successive calls.

`planning/current.md:5–10` distinguishes “implemented”, “proved”, “qualified”, and “deployed”; the capability table at lines 29–43 says “no: closure moved” for its proof coordinate. That is the recorded current view, not a fresh verdict from this consultation. A theorem statement found below is not new evidence that its current include closure has certified. The deployment prose is historical source information, not a live observation.

### Existing statement families

| Source and short quote | Statement, subject, and limit |
|---|---|
| `books/node-traces.lisp:198`, `fn-node-trace-preserves-state` | The node trace preserves its logical state predicate. The subject is the recursive logical trace, not SBCL threads. Each recursive successor is explicitly the preceding result. |
| `books/store-node-traces.lisp:635,641`, the step/trace relation theorems; `:684` mixed trace ready-state replay | The composed store/node transitions retain their relation and ready states agree with replay. These are substantive composition results, but the trace is a sequence of supplied model events. Host completion identity, event order and real disk effects must realize those events. |
| `books/store-node-traces.lisp:734,939,980`, acknowledged retention, admissible crash recoverability, recovery admissibility | Durable modeled history survives permitted crashes. An arbitrary raw-host interleaving is not automatically an admissible model trace. |
| `books/store-node-resolution.lisp:617,625,636,671,701`, mixed trace relation/replay/acknowledgment results | Completion/resolution composition relates new success to its matching durable completion. The subject is the store-node-resolution machine. This supplies an important acceptance lemma for a future host simulation. It does not prove that the host cannot duplicate, lose or misroute the completion. |
| `books/owner-invariants-step.lisp:816,833,839`, “fn-own-step-preserves-relation”, “fn-own-run-preserves-relation”, “fn-own-run-preserves-store-relation” | Owner steps and runs preserve the owner/store relation. Earlier read/store/complete/reopen proofs are at 219,366,389,416. The machine serializes these operations by definition; no thread lock is an argument of `fn-own-run`. |
| `books/owner-invariants-served.lisp:175`, “fn-own-read-is-served-step-on-pinned-prefix”; `:215`, “…after-any-trace” | Under `fn-own-relation` and an existing connection, the effects of `fn-own-read` equal `fn-served-step` over the connection's replay prefix and pinned view. This is the central *meaning* of a read, not a guarantee that a raw arena pointer remains valid after a mutex is released. |
| `books/owner-invariants-served.lisp:541,573,645`, pinned-prefix survival, reclaim-floor/pins, completed-post survival | Other legal owner events preserve the reader prefix; modeled reclaim respects pins; completed posts persist through later owner traces. These prove properties of modeled pins and files, not fd integers, worker registrations, or SBCL vectors. |
| `books/owner-served-carried.lisp:230`, “fn-scar-ocfg-read-tls-prefix-is-reference-under-ocl-relation” | The carried implementation agrees with the configuration/reference read under the owner/config relation and indexed-view condition. It is a bridge, not the top raw entry itself. |
| `books/served-catalog-dispatch.lisp:365`, “fn-nntp-archive-command-cat-is-pinned” | Catalog commands equal pinned archive commands under article-view equality, archive validity, index correspondence, freshness and the other stated premises. This is exactly the kind of representation-boundary equality worth composing; dropping its correspondence hypotheses would invalidate the claim. |
| `books/served-catalog-chain.lisp:1993,2547,2565`, span equations and “fn-scr-ocfg-read-span-is-reference-under-ocl-relation” | Span implementation agrees with the reference octet slice, including consumed count/state/repin, and effects after cursor expansion. Premises at 2566–2571 include cache validity, owner/config relation, indexed view, catalog correspondence, `fn-scol-okp`, and natural slice bounds. A caller's pointer to `fn-cat` is not itself a proof of those premises. |
| `host/owner-host.lisp:4240–4277`, “fn-orr-read-span”, “fn-otm-read-span”, “fn-oas-read-span”, actual `(RC (fn-mca-read-span ...))` | This is the actual wrapper chain: reader capture, time admission, article slots, credit accounting, then catalog/reference behavior. Admission can refuse before the underlying read. The comments cite several `-unfolds` equations: useful routing equations, not new correctness keystones. Installation of RC into live globals is separate at 4281ff. The whole host entry must include both pieces and their state threading. |
| `books/owner-credits.lisp:331,357,440,457`, funded reads, “never-blocks-what-is-held”, retained commit ownership | Logical credit accounting is carried through operations. “Never blocks” here is a resource-admission statement, not a bound on mutex wait or `pread` latency. Physical buffers, stale callbacks, allocator cost and cleanup must correspond to the ledger. |
| `books/served.lisp:2781,2812,2822,2965,3082`, partition/concatenation/pipelining/bounded-chunk results | Stream chunking and sequential dispatch have logical equivalences. Socket partial writes must preserve the corresponding byte-prefix order. Command boundaries and input-consumption receipts matter. |
| `books/served-plan-cursor.lisp:355,413,474`, drain expansion, unbounded reply, cursor-step validity | A bounded continuation can produce an arbitrarily long logical reply. Host yields may stutter; the continuation and response hold must survive until completion or abort. The proof is not a theorem that the mux eventually resumes it. |
| `books/owner-reader-view.lisp:166,185,202`, “fn-ocvm-step-preserves-inv”, “fn-ocvm-run-preserves-inv”, “fn-ocvm-reader-view-is-the-completed-prefix” | The legal start/next/complete/drop count machine maintains its invariant and exposes the completed prefix. Its `legalp` protocol is meaningful concurrency-related modeling, but it is not a machine of native mutex ownership or actual workers. |
| `books/byte-store-k0-recovery.lisp:495,572,585`, recovery-program every-cut relation and host-reopened kernel | These connect modeled byte effects, recovery, and open results. The every-cut theorem quantifies membership in `fn-bs-run` and admissible crash images, not every machine instruction of host code. “host” in a theorem name still names a logical function/model result. |
| `books/recovery-refinement-concurrent.lisp:303`, “fn-rrc-recovery-refines-a-prefix-with-every-acknowledged-record”; `:450`, “fn-rrc-checkpoint-crash-point-refines-with-a-batch-in-flight” | Stronger than an isolated checkpoint proof: recovered history is an allowed committed/inflight sequence and retains every acknowledged record, even with a batch in flight. Hypotheses explicitly include log relation, crash image, platform tears, and equality to the captured checkpoint. At 456 the checkpoint state is a member of `fn-bs-run`. This does not enumerate concurrent host `close`, fd reuse, queue insertion, or shared-stobj mutation. |
| `books/arena-reader-pins.lisp:429,442,455`; `books/response-plan-pins.lisp:94,125,137` | Generation release follows all live pins; response acquisition holds the captured generation and release targets only the named response. These are ready-made resource lemmas. The missing step is enforcing the same token protocol on every concrete borrow. |

**The UC-shaped layer is an intention, not a finished node theorem.** `specs/node-functionality.md:398–420` separates the ideal-reader result from the host's event/effect obligations; 431ff discusses equality for environments and UC vocabulary. `books/ideal.lisp:1` says “SKELETON ONLY”; 14–21 says other ports return `(:todo <port>)`; 149ff lists missing parts of the invariant; 224ff labels proposed theorems “OPEN”. It would be incorrect to cite this as universal composability of NNTP + BP + store + operator + hostile environment. Even a completed deterministic I/O trace equality needs an explicitly defined observation/adversary/composition model before it is a UC claim.

Registry cross-check: `planning/proofs.json:2940` (PRF-067, “Pinned group buckets and OVER ranges refine the committed archive”), `:10424` (PRF-288, readers at the durable view while a barrier is in flight), and `:20924` (PRF-1214, checkpoint with a batch in flight) are marked `uncertified-at-current-digest` in the checked-in registry. PRF-1214 explicitly lists `A-CRYPTO-TRAILER`, `A-DURABILITY`, `A-WRITE-ISOLATION`. In contrast the pin rows PRF-941 (`:16827`) and PRF-1059 (`:17825`) are marked `certified`. These are registry observations; I did not independently resolve their archived manifest bytes or recompute green status. The exact subject and coordinate remain necessary even for a row marked certified.

### The missing host premises, precisely

| Required connection | Written where? | Present proof scope / gap |
|---|---|---|
| Atomic owner semantic step | `host/native/owner.lisp:1–9` says calls/store mutation are serialized; `:1573–1610` implements gate plus O mutex | It is true of the wrapped region, not all core calls. Offlock publication calls `fn-owner-sco-next` at 5066. The logical step theorem presumes an indivisible transition; a host simulation must identify its actual linearization/publication point and exception behavior. |
| Serial execution and correct successor state | `books/owner-invariants-step.lisp:833` recursively threads owner state; `host/owner-host.lisp:4281ff` installs the result | Explicit in logical recursion, implemented by convention and wrappers in host. No named assumption found stating an executable concurrent state-threading relation. **UNVERIFIED** for every raw entry/global write. |
| Consistent offlock snapshot | `owner.lisp:5035–5041` says the generation was pinned before thread creation; `:5240–5257` captures and pins | Intent and local mechanism exist. Pinning a generation proves retention only when every mutation/close honors it; it does not by itself make concurrent reads of an in-place arena coherent. |
| Honest outcome and event order | `specs/failures.md:15`; `books/assumptions.lisp:154–181` constrains host report/events, including `(equal (nth n (fn-assume-host-events events)) (nth n events))` | Named A-HOST exists, but the specification explicitly says no theorem uses those functions as a hypothesis yet. It is not a proof of event production by the host. |
| Exact effect order, nonduplication, no hidden mutation | `specs/node-functionality.md:408–420`; A-HOST | Broadly written in prose. The constrained event identity function does not model outstanding effect tokens, retries, partial writes or duplicate completions. “Exactly once” must mean authorized completion consumption and byte offsets, not an OS syscall magically executed exactly once across crashes. |
| Lifetime of fd/vector/stobj borrow | Local `extent.lisp:403–475`, `owner.lisp:4849–4923`, pin books | Several explicit local protocols exist. No global host-pointer/resource assumption or checked universal borrow rule found. A-PGS-HOST-IO presumes faithful words, not an fd lease; both are needed. |
| Crash placement | `specs/failures.md:65–79`: “between any modeled write/barrier/publication actions”; byte-program theorems | A named-cut correspondence exists for selected paths. Physical crashes can occur anywhere. Intermediate instructions must either refine a named cut or be shown observationally equivalent to one; excluding all unnamed instructions from reality would be circular. |
| SBCL memory ordering and logical execution | `specs/failures.md:25`, A-SBCL-RUNTIME; `io.lisp:16–21` “host/model correspondence is an assurance obligation” | Written trust boundary, not an ACL2 constraint or a multithreaded stobj theorem. Synchronization of a hash table does not synchronize unrelated state fields. |
| Fairness/time | `specs/failures.md:93–96`, A-FAIRNESS and explicit clock/age semantics | Appropriate separate assumptions. Safety should not require eventual scheduling; bounded service requires much more than functional refinement. |

I found no executable ACL2 machine whose state includes *all* native threads, their program counters, O/G/K/E/M locks, pending syscall continuations and ownership transfers, and whose transition roster generates/checks the running host. This is a scoped negative result from the cited books/declarations and synchronization inventory, **UNVERIFIED as an exhaustive theorem about every file in the repository**. The reader-view and concurrent-recovery machines are real partial models and should be reused, not described away.

## 2. The trusted base between theorems and bytes

### Size and responsibility

The reproducible physical-line inventory is Appendix A: **112 `host/*.lisp` files / 25,909 lines; 78 `host/native/*.lisp` files / 40,939 lines; 190 / 66,848 total**. Comments, blank lines, declarations, parked code and build drivers are included. This is not a count of reachable TCB instructions. The four central native files alone total **17,779 lines**. The per-file table classifies logical/program adapters, declaration/build infrastructure, raw I/O/FFI, raw orchestration/decisions, and parked runtime adapters; mixed files are marked mixed rather than called “just glue.”

`host/native/io.lisp:3–6` is unusually clear: “Nothing here is proved.” `host/native/build.lisp:320–401` loads the ACL2-mode wrappers and interfaces; 425–574 loads the raw adapters; 579ff parks runtime-participant/collector machinery; 614 strips the world. Thus (1) a book included in the image, (2) a host wrapper loaded, (3) a raw file loaded, and (4) a startup path actually exercised are different reachability questions. Do not inflate the live TCB with parked code, or count parked proofs as served coverage.

ACL2-mode `host/*-host.lisp` is not automatically proved just because it calls books. Its state/global sequencing and `:program` wrappers can lie outside guard-verified logic. `io.lisp:16–18`: “:program host wrappers are not guard-verified caller proofs”. The raw orchestration interprets results, chooses when to invoke entries, carries identities across queues, schedules retries, performs cleanup and classifies exceptions. Those are correctness decisions even when all domain policy is correctly delegated to ACL2.

### Execution boundary

* `io.lisp:1180–1247` derives raw dispatch from the loaded `fn-interfaces` world, checking the declaration and `:common-lisp-compliant` status. `:raw-with` moves invariant checks into establishment/preservation proofs; it does not discharge host interleaving obligations.
* `io.lisp:1286–1308` extracts recognized unary kind conjuncts for non-stobj formals; `:1354–1370` checks arity/kinds. Relational state predicates and lifetime premises are not generically checked here. At 1378, `fnn-entry-guard` runs **before** `fnn-call`'s `handler-case`; callers must correctly contain its condition too.
* `io.lisp:1381–1394` catches `raw-ev-fncall`, invokes raw or `ACL2_*1*_ACL2` counterpart, and maps execution escapes to faults. `:1397–1428` supports fixed startup-selected compiled callbacks and scalar MVs; this does not establish the carried invariant. No `call-in-core` symbol was found in the searched host tree: the relevant names here are `fnn-call`, `fnn-core`, `fnn-core-state`, fixed callbacks, and direct declared applications.
* `io.lisp:329–419` obtains live stobjs from `user-stobj-alist`, caches them, supplies trailing arguments, and relies on destructive update while discarding returned stobj/state positions. The obligation is stronger than “the same object is supplied”: no concurrent observer may see a torn or invalid intermediate representation, and no live borrow may outlast a swap.
* Raw replacement and counterpart replacement are both part of the TCB. Examples: `extent.lisp:1039–1061` durable octets, `:1122–1134` arena storage, `:1145–1192` page fill/frame; both normal and `acl2_*1*_acl2` names are redefined. Calling a *1* name does not restore the logical implementation of a replaced function.
* `books/def-carried.lisp:22–27`: “THE STATEMENTS ARE GENERATED”, and named proofs are used as hints to generated obligations. This is materially stronger than accepting a proof name. `books/definterface.lisp:516` explicitly distinguishes a literal declaration lint, “occurrence, not proof”; carried rows have stricter checks. Keep this distinction in any concurrency generator.

### Runtime, libraries and physical storage

The proof-side trusted base also includes ACL2's soundness, its host Lisp/compiler, and the admitted logical world/attachments at the cited certification coordinate. A trust-tagged raw realization is outside those logical proofs. This review did not re-audit the entire included community-book closure or re-certify it; those properties are **UNVERIFIED by this consultation**, rather than silently inherited from a source theorem name. `io.lisp:3–6` explicitly identifies the raw `:fn-native-host` trust boundary.

`specs/failures.md:22–25,31–36` names native crypto, signatures, TLS, SBCL, durable extents, decompression, arena storage, extraction/compiler, and page I/O assumptions. Examples include BLAKE3/C ABI, PQClean ML-DSA-65 and its raw/*1* realization, libssl/libcrypto behavior, and the compiler/runtime implementation of threads, arrays, stobjs and FFI. `host/native/{crypto,digest,signatures,deflate,tls}.lisp` are concrete realization code, not discharged cryptographic or compiler proofs. The appendix counts them separately; library versions/ABI behavior were not queried dynamically.

The explicit dynamic-library loads are `crypto.lisp:88` (libsodium; candidates at39ff), `digest.lisp:126` (vendored `libfn-blake3`), `signatures.lisp:98` (`libfn-mldsa65`), `deflate.lisp:73` (`libfn-deflate`), and the matched `tls.lisp:312–313` libcrypto/libssl pair. `deflate.lisp:12–17` says “vendored zlib 1.3.2” and distinguishes outbound foreign compression from inbound ACL2 inflation (5–10). `bpsec-crypto.lisp:67` says “Use the already selected TLS libcrypto pair; never load another version.” The dynamic loader, libc/syscall bindings and ABI layout are additional realization trust, not cryptographic theorems.

The kernel/filesystem side includes file identity, exclusive store access, coherent reads, write-unit isolation, permitted tears, barriers and namespace durability. `io.lisp:471–486` realizes platform barriers and directory sync; `:6356` realizes positional log writing via seek/write, which requires exclusion on that descriptor; `extent.lisp:151ff` uses positional reads. `specs/failures.md:65–79,100–105` explicitly refuses to equate process kills with power-loss evidence. It would be misleading to replace this collection with an assumption named “disk works.”

The extracted product has an additional compiler/runtime boundary, not fewer host concurrency obligations: A-TARGET-COMPILER at `specs/failures.md:35` says it loads the same host/native implementation. `strip-world.lisp:168–180,256` retains/resizes hons/memoize infrastructure and clears tables at build/strip time; this is not evidence of thread safety during serving.

### Which gates establish what

| Gate | Evidence from source | What it can and cannot establish |
|---|---|---|
| ACL2 certification / carried generators | `def-carried.lisp:22–47`, generated preservation/establishment/reachability formulas | Logical semantic proof under the actual hypotheses; not native lock correctness. |
| `tools/green_check.py:27–46` | Current digest/include closure plus success marker, certificate digest and exit 0 | Evidence coordinate and certification freshness. It neither proves a new property nor transfers green to changed source. |
| `tools/coverage.py:5–10,24–40` | “from a dump … inside an ACL2 session”; translated theorem conclusions vs hypotheses/callers | Reads semantic world facts and classifies attribution. A theorem mentioning a caller is not automatically a boundary equality. No thread/alias analysis. |
| `tools/interface_emit.py:29–52` and `raw_dispatch_rule.py` named there | Checks raw-host dispatch/binding declarations and forbids undeclared reachability routes | Valuable source/binding checks; ACL2 world checks run at build. Does not interpret effect ordering or check snapshots across lock release. |
| `tools/reach_check.py:121–126,580ff,992ff` | Parses definitions/call paths and named equality bridges | Stronger than a prose/name grep, but a structural reachability/attribution check, not a proof of feasible native schedules or shared-memory safety. |
| `tools/native_program_check.py:7–32` | Compares syscall/model-step kinds/order and error-arm observations | A restricted syntactic/effect-sequence correspondence check. At 34–43 it explicitly cannot decide runtime control flow, callbacks, syscall semantics or callers; at 71–74 the direct PROGRAM_HOSTS map contains finish and staging cleanup. Log-route checks are delegated, as its comments say. Not a general concurrency or all-crash-instruction verifier. |
| `tools/theory_check.py:38–40,139ff` | Audits top-level theory openings and guard ordering | Proof-engineering hygiene, not native behavior. |
| Ledger/current-view/generated registries | `planning/current.md:3–10`; `AGENTS.md`, “Counts are generated” | Provenance, scope and statement hygiene. Useful fail-closed bookkeeping; not evidence that an fd remains open. |
| Native/differential campaigns | `specs/failures.md:34–35` specifies per-input equality and fault transcripts | Executed semantic evidence for tested inputs/schedules/platforms. This consultation ran none. Exhaustive schedule coverage is **UNVERIFIED**. |

Calling all these “prose scanners” would be unfair. Calling their aggregate a theorem about concurrent host behavior would be equally wrong.

### Decisions still made by raw host

The important violations are not all protocol arithmetic. Some are missing execution policy:

* `owner.lisp:3704–3706` decides that *every* `fnn-store-error` means a normal stop, although faults and uncertainty subclass it (`io.lisp:75–91`). That duplicates/overrides the outcome distinction the logical model preserves.
* `mux.lisp:1378–1397` chooses a loop and when transfer becomes visible; `:1133–1185` computes due timers and the next poll deadline; `:1244–1248` turns that into an OS wait. These are host scheduling decisions. If time/service policy is meant to belong to ACL2, expose observations to a core action rather than maintain a second policy here.
* `owner.lisp:5518ff` uses a fixed number of reclaim swap rounds. It may be a work/retry policy, but its relationship to the operator's admitted profile and core decision is **UNVERIFIED**. It must not become a data ceiling by accident.
* `extent.lisp:1149–1169` assembles a 16,384-byte page into 2,048 u64 words; `:1183ff` checks frame bounds and puts those words. This is a raw representation realization explicitly covered by A-PGS-HOST-IO, not a second independent article-policy implementation. Still, codec constants and bounds should come from the representation declaration, with qualification against the logical realizer.
* `io.lisp:1336–1351` walks up to a million conses merely to describe a bad argument. That is bounded host diagnostic policy but an unnecessarily large failure-path quantum. A bounded kind tag is enough.
* Raw errno mapping, pointer/null checks, partial-write bookkeeping and foreign length validation remain necessary realization checks. The instruction “ACL2 owns every decision” should mean semantic/admission/outcome decisions, with checked realizers for representation effects. Moving every OS return-value test into ACL2 would add boundary traffic without proving the runtime.

## 3. Actual concurrency structure

### 3.1 Threads and lifetimes

There are **13 textual `sb-thread:make-thread` call sites** in the requested two directories, not thirteen runtime threads. Several instantiate per worker/client/service. Runtime-internal threads are separate assumptions. All 13 are listed here; native startup reachability varies by profile/module.

| Creator / entry | Loop, transfer and termination |
|---|---|
| `io.lisp:1078`, `fnn-log-writer-loop` | Persistent diagnostic/journal writer; Q-protected enqueue/dequeue, actual write off Q (1047–1067); stop queued under Q and join outside at 1090–1104. |
| `extent.lisp:534`, `fnn-extent-executor-loop` | Persistent cold workers started before listeners (`owner:6093ff`); E-protected job/CV, private execution outside E (512–522); cancel/wake then join off E (546–564). Token debt survives cancellation until actual return. |
| `owner.lisp:3344`, syncer lambda | One issued log barrier job; off-O sync, C-protected result publication at 3352, roster cleanup 3355; committer joins outside O/C at 3582. |
| `owner.lisp:3714`, `fnn-owner-committer-loop` | Persistent batching worker; C waits, gate/O start and complete separated by off-O sync. Fault handler at 3704 is defective; shutdown joins at 6217. |
| `owner.lisp:5257`, `fnn-owner-publish-captured` | O-captured immutable metadata plus A pin, registered under R before execution; off-O checkpoint, gated completion and reseat; removes roster at 5147–5150 before unpin/nursery/reconsideration. |
| `owner.lisp:5307`, exporter | O capture plus A pin and R registration; off-O export at 5331ff; removes roster at 5410–5413 before unpin at 5415. Same lifetime pattern needs repair. |
| `owner.lisp:5934`, listener lambda | Additional plain/implicit-TLS accept loop; checks stop flags, accepts, calls launch/adopt; self-removes under R on exit. Main plain accept is the caller thread (`:5959ff`), not another make-thread site. |
| `mux.lisp:1373`, `fnn-mux-run` | Fixed I/O loops, connection state confined to one loop; R registers threads; inbox/arrived via M. Stop drains at 1306ff, closes wake pipe and removes worker at 1353ff. |
| `control.lisp:456` | Per accepted control connection thread; control roster manages socket/worker lifetime. Control logic can enter owner and uses a shared control-buffer lock. No complete transitive lock proof was established for this module. |
| `control.lisp:529`, `fnn-control-accept-loop` | Local control listener; stop signals/closes, close hook joins module threads. Source at 534ff contains stop/close handling. |
| `feed-service.lisp:596`, `fnn-feed-worker-guarded` | Feed runtime thread; global/runtime mutexes protect its roster/state, sockets execute outside owner, stop/join at 602–623. |
| `pull-service.lisp:568`, `fnn-pull-worker-guarded` | Analogous pull runtime; own mutex at 564, close/join through 589. |
| `web-host.lisp:312`, listener/serve lambda | Web face worker in owner roster, stop flags and accept loop, handles accepted web socket; no separate per-web-client make-thread site here. |

Signals: `io.lisp:8578` ignores SIGPIPE; 8581 records SIGHUP; 8585ff records SIGTERM/wakeup behavior. These are asynchronous flag observations, not owner transitions. `owner.lisp:5960–5965` explicitly explains why nonblocking accept/poll is used. GC/finalizers are not user-created thread sites. The parked `runtime-participants.lisp` finalizer/interrupt machinery is inventoried in Appendix B but not treated as running by `build.lisp:579ff`.

### 3.2 Synchronization objects and protected state

Names below are abbreviations used only in this report. Counts are lexical call sites, not lock instances. The quoted expressions make the inventory checkable. Appendix B expands the site inventory, including equivalent wrappers and other modules.

| Lock/object | Protected state, operations, explicit sites in the four files |
|---|---|
| **O**, service owner/store mutex | Live owner/config/credits/access cache, mutable reader/catalog/arena changes, core state globals and semantic admission. Constructed `owner:1209`, `(make-mutex :name "fn owner/store")`. Direct sites 1590,1593,1746,4358,4884,6120,6284; most callers enter through gated/serialized wrappers. “All calls” in the opening comment is too broad: private/pure and pinned read calls execute elsewhere. |
| **G**, owner gate mutex and ready CV | Waiting classes, tickets, holder, scheduler/time/disk events. Constructor `owner:1257–1258`. Sites 1280,1284,1336,1372,1438,1457,1484,1496,1507,1519,1531,1539,1566,3306,3324. Wait at1362 releases G; it does not hold G while acquiring O. |
| **R**, owner roster | Workers, clients, publisher/exporter bookkeeping, mux selection, terminal stop publication. Macro `owner:1246`: `(sb-thread:with-mutex ((fnn-owner-service-roster ,service)) ...)`. 19 invocations in owner, 5 in mux; exact sites in appendix. Cross-thread reads of some service fields are nevertheless outside R. |
| **C**, commit mutex and ready CV | queued/synced/awaiting/done/sparing/drain-release and commit coordination; fields documented `owner:169ff`. Owner sites 1711,1732,3020,3035,3046,3054,3062,3088,3133,3239,3352,3478,3521,3692,6001,6050; mux1303. CV waits3491,3494,3695,3700. The mux pass/polling fields used by those waits are not written under C. |
| **W**, consumer wait mutex/CV | commits/waiters; `owner:144–145,268`, local `lock` sites2815,2831,2847,2856; wait2850 and explicit release2854. The manual lock path must retain unwind semantics when generated. |
| **L**, payload lifecycle mutex | Phase, arena instance, owning service; `io:1555–1567`, owner1612,1624,1637,1645,1655,1672,1680. Some functions are staging infrastructure; startup actually calls lifecycle start at6121. |
| **A**, arena/response-pin mutex | Generation stamp, live pins and pending page retirement; response hold state. `io:6768,6787`; `owner:504`. The primitive acquires/releases A within the call; callers must separately own O when capture/reseat requires it. |
| **E**, extent mutex | fd/path/base/incarnation tables, read tokens and results, cache/pool, cold worker phase/free list, shared read/page-window stobjs. `extent:48`; 41 acquire sites enumerated below; owner4276,4312,4872,4885,4898,4917,4922,4964,4979. Retired/pending groups are explicitly O-protected (`extent:1208ff`), not all extent-named state belongs to E. |
| **K**, log kernel recursive mutex and sync CV | kernel, inflight/fenced/sealed and sync-state. `io:6306–6315`, macro6346; 19 wrapper invocations in io; direct mutex sites8010,8069,8079. Recursive acquisition is intentional at finish/ack. Not every log struct field is K-protected. |
| **S**, log spare mutex | Serializes spare preparers, held during creation/preallocation/fence, `io:6333–6337,7299`. Rotation consumes the spare under O without S (`:7325ff`). Safety of this split is a protocol obligation, not ordinary one-lock field protection. |
| **Q**, log queue recursive mutex/CV | Queue cells, writer lifecycle/sink accounting, owner run-authority/reservation and journal settlement. `io:916–917`; sites948,971,1049,1065,1072,1090,1104,1113; owner648,653,668,676,699,4794,5830. Wait1051. A function of the queue must not secretly become a callback into O. |
| **J**, fallback service-log recursive mutex | Fallback fd writes/swap after writer inactive, `io:863,1117,1142`. Blocking write/finish-output possible here. Separate from durable store log K. |
| **M**, per-mux inbox mutex | inbox, arrived, unsent; conn fields otherwise loop-confined. `mux:72`; sites678,1189,1213,1241,1280,1292,1312,1393. A “loop is alive” transfer predicate is missing from adopt. |
| Random mutex | Shared random state, `io:740,744`; used for raw randomness realization. Does not replace cryptographic assumptions. |
| Four synchronized hash-table creation sites | Owner measurement table345; io trailing-stobj table352, guard-spec table1278, staged guard-cache1320. A synchronized table protects table operations, not compound read/modify/write on a stored value or the object reached through it. At1320 the cache is startup/staged, **not per call**. |
| Three atomic increment sites | `io:6184,6190,6193`, lookup counters. These are measurements, not publication barriers for the owner state. |
| Semaphore | `mux:1408` once-mode completion, wait1410; signals313 and1386. This completion must occur on both adopted and refused/closed paths. |

Exact E acquire lines: 70,91,109,118,147,224,232,282,298,332,350,363,425,449,459,504,512,520,536,546,564,581,624,628,756,892,915,942,956,992,1043,1056,1089,1099,1106,1147,1155,1219,1228,1266,1272. These include both `with-mutex` spellings with/without `:wait-p t`. Waits at515 and630 release E. `extent:616` joins only after observing the worker dead, while E is held; that needs the runtime join-after-death contract, although it is not a live-worker I/O wait.

Outside these four files: control roster and control buffer (`control-transport:10–25`), feed/pull runtime and global mutexes, TLS initialization/context/reload locks (`tls:66,77`, `tls-reload:64,72`), crypto/digest/signature initialization locks, decompressor pool (`deflate:532,537,560`), BP session (`bp-app:342,352`), and parked snapshot/runtime locks. Their exact sites are in Appendix B. **UNVERIFIED:** complete semantic read/write sets and cross-module lock ordering for BP, control, web, feed/pull and parked runtime code; I inspected their thread and synchronization entry points, not every transitive body.

Dynamic specials are execution context, not mutual exclusion: `*fnn-log-batch*`, `*fnn-owner-deferred*`, `*fnn-extent-no-io*`, per-window borrow contexts and fault selectors. A thread-local binding can make a route safe for that thread; it cannot prevent another thread from closing a shared fd. `*fnn-owner-reserving-thread*` (`owner:659–664`) is an authority identity compared under Q, not a substitute for Q. There is no explicit compare-and-swap site in the requested files; the lexical census also covers interrupt/finalizer constructs outside the central four.

### 3.3 Nested acquisition and waits

The following is the observed order graph, distinguishing nesting from release-then-acquire. References to a callee are included where nesting is transitive.

| Outer → inner | Sites / explanation |
|---|---|
| O → G | `owner:1593–1605` gate check/leave inside O; 3306 commit event under O. Admission acquires G, releases it, then O. The exceptional enter path explicitly says “gate's mutex has unwound before taking the owner” (1588). **Not a G→O inversion.** |
| O → R | Stop1703, clients snapshot1726; publication5214/5253; export5300; other roster calls listed in appendix. |
| O → C | Stop1711/1732; note-queued3020 from read; commit-start3088/3133; complete3239. |
| O → W | signal-commit268 called from completion1993 and stop1736; consumer waiter registration2815. Wait itself occurs after O release. |
| O → L | lifecycle recover/start/drain/join/capture/live/release1612–1680; direct startup6120 and joined6284. |
| O → A | response capture504, publication pin5255, export pin5305, reclaim capture5661, retirement checks4849ff. |
| O → E | cold issue4212→extent892; cold-result4276; root/snapshot leases4872–4922; release4849→extent1228. |
| O → K → E | commit-start/drain→log append `io:6729–6760`: append holds K, and member-file registration reaches E; O is held by the caller. |
| O → K | completion/finish `owner:3206ff`→`io:6908ff/7986`; seal owner3142→io8015/8022. |
| K → K | `io:7986` finish/ack calls the recursive kernel wrapper; declared recursive, not a two-lock cycle. |
| O → R → A | publication5253–5255 and export5300–5305. Thread creation is also inside O/R. |
| C → G → Q | commit wait3478 calls wake selection3324 and disk event3504→1457→journal offer1476; G-protected journal-note1484 also queues under Q. |
| O → G → Q | gate/commit observations that emit journal entries through the same queue. |
| O → Q | owner journal/run settlement and deferred log offer; e.g. stop/completion logging and owner5830. The queue's writer performs disk I/O after releasing Q. |
| R → pipe/fcntl/thread creation | `mux:1360–1375`; not another project mutex, but a blocking/runtime leaf inside roster exclusion. |
| E → E, staged callers only | `owner-control-turn.lisp:28,33,51`, `receiver-parser-turn.lisp:20` use recursive E around callbacks. Loaded helper ≠ active served startup. Exact dynamic reentrancy/callee sets **UNVERIFIED**; don't mix an ordinary mutex acquisition of E into a recursive callback without checking. |
| P → O (parked snapshot action lock) | `snapshot-producer.lisp:11,45,60,113–119`; not a served lock-order edge at this startup coordinate. |

No definite pair acquired in both opposite nested orders was established for the **active four-file paths traced here**. This is not a deadlock-freedom proof. Unrestricted callbacks and cross-module hooks make the full graph **UNVERIFIED**. Important nonedges: delivery releases C before calling the mux callback (`owner:3035–3041`, `mux:678`); cold release drops E before retrying O (`owner:4300`, `4849–4865`); W's snapshot is released before the owner poll (`:2831–2847`); S is documented never taken under O (`io:6336`). Promoting any of these sequential transfers into nested locking would introduce new obligations.

### 3.4 Blocking and unbounded work under exclusion

“May block” must include waiting for another lock, allocator/GC, FFI and kernel work, not just functions named `read`. Separate the safety question from the desired latency budget.

| Exclusion | Blocking/work site and consequence |
|---|---|
| O | Inline commit `owner:3269–3282` executes START/BARRIER/COMPLETE in one quantum, including `fnn-owner-commit-sync`; `io:6875–6893` performs the durability calls. Deliberately reachable nonbatch path, not fixed by offlock syncer support elsewhere. |
| O | Statement-bearing batches explicitly call `fnn-owner-statement-barrier` (`owner:2453–2458,2473`), whose `*fnn-log-batch*` arm runs `fnn-log-commit-open-batch` synchronously. The comment at2444–2450 says it first awaits a batch already in flight. This is a concrete blocking exception even when ordinary commits use the pipeline; key-statement verification/identity commit follows at2379–2412. |
| O/K | Log append at `io:6729–6742` executes `fnn-log-pwrite` (seek/write6356) under K and usually O; extent registration may open/fstat. A split barrier does not make the append nonblocking. |
| O | `io:8022` awaits log sync with K CV; condition-wait releases K but **not O** in the caller. Whether a legal schedule reaches this wait with an outstanding sync depends on the pipeline protocol; **UNVERIFIED absence**. |
| O | Cursor quantum `owner:518–523` calls `fn-splan-cursor-step` with live arena/catalog, without a local `*fnn-extent-no-io*` binding. Cold realizers can block when invoked. Exact cursor-to-cold-read reachability for each command/profile needs a focused witness; don't assert it solely from an arena parameter. |
| E, possibly O→E | `extent:689–700` entry read and `:791–815` synchronous cache-miss path perform `pread`; raw octet wrappers at1043/1056 hold E across cache fill/copy. E also serializes allocation and full-entry validation. `:1228–1245` closes files under E. |
| O | Rotation `io:7367` rename,7385 head write,7389 close under owner callers5234/5657. Comment “only renames” at6335 and owner5169 is incomplete. |
| S | `io:7299–7323`: old spare close/unlink, new open, preallocate and fsync under spare mutex; expensive but intentionally off O. Other preparers block. |
| O | Reclaim swap `owner:5745–5768` installs checkpoint/files and recovery barriers while excluded. Candidate building is offlock; installation still has disk latency. Developer cut hold/yield at5777 can amplify it in a test image. |
| O | Deferred feed resolution flush `owner:3254` can reach journal I/O; stop1721/1730 issues socket shutdown and 1739 calls arbitrary stop hooks documented “nonblocking.” That annotation is not mechanically enforced. |
| J | `io:1117–1119,1142–1149`: close/swap/write and stream finish in fallback logging. Normal running writer path queues instead, but fallback is a real mode. |
| G/C/W/E/Q | CV waits: owner1362,2850,3491,3494,3695,3700; extent515,630; io1051,8012. Each releases its designated mutex, not any outer mutex. Generated await must state and check the remaining lockset. |
| E | Dead-worker join `extent:616`; runtime may allocate/lock internally. Only a join-after-proven-termination leaf should be admitted in this class. |
| R (sometimes O→R) | make-thread at owner3344/5257/5307/5934 and mux1373, plus mux pipe/fcntl1366. Runtime allocation/scheduling is outside an ACL2 cost bound unless explicitly modeled/assumed. |

Mux socket/TLS/compression work generally runs on the loop outside O. This is good separation, but can stall *that loop*: `mux:642` peek-consume can use a ten-second timeout; `:433ff` flush/work loops can do multiple local operations before yielding. Publication/checkpoint writing, export, reclaim construction and log sync are also mostly off O. “Off O” is not “private”: their inputs and outputs still need ownership and synchronization contracts.

### 3.5 Values crossing synchronization boundaries

This is the central missing interface. The table groups equivalent sites by transfer protocol; it includes the four central files' explicit shared-state handoffs and the important indirect realizers. Completeness of hidden aliases and arbitrary callback effects remains **UNVERIFIED**; the proposed checker should turn this from a reviewer-maintained table into generated data.

| Boundary / sites | Captured value and post-release use | Protection / gap |
|---|---|---|
| Gate admit → owner acquire (`owner:1336–1364,1573–1605`) | class ticket/admission, waited time | G-owned holder protocol, recheck under O; stopping/gate abort must remain visible. No G held while waiting for O. |
| G snapshot → read/commit (`1438–1539,3324`) | immutable scheduler/time/limit value | Value snapshot; it is intentionally an observation at a named time, not a license to reread mutable G fields offlock. |
| O → offlock space/read policy (`owner:125,159,3438`) | `space-need`, `read-octets` and immutable config-derived numbers | Scalar/value capture; refresh visibility and which generation a decision uses are not encoded in a shared-memory theorem. |
| O/R → accept/loop (`owner:1703`, `mux:1337ff`) | stopping, exit code, listener, mux vector | Stop written under locks, many reads outside. Assumed runtime visibility; publish-once objects vs changing flags need distinct contracts. |
| O → read plan (`owner:483–514,534ff`; `mux:426ff`) | plan/cursor + arena generation | Response pin under O/A, immutable continuation; mux owns continuation and partial output offset. Completion/abort must unpin exactly once. |
| O cursor → mux resume (`owner:518–527`, `mux:403–419`) | next plan, output window, after-continuation | Private next value; response hold deliberately retained over yield. Timer next-deadline mismatch described below. |
| C → callback (`owner:3035–3041`) | removed awaiting callback + completion | Single removal under C; callback outside C; M enqueues owned completion. Socket lifetime is not supplied by that removal alone. |
| C done table → registering mux (`owner:3062ff`) | completion stored before callback registration | Atomic consume-or-register under C avoids a normal lost completion. Need connection epoch if IDs can be reused before stale completion cleanup; **UNVERIFIED globally**. |
| Syncer local result → C notification → join (`owner:3344–3358,3478–3582`) | `(word, generation)`/result cell and `synced` | C publication plus join after physical syscall return; generation ledger rejects stale completion. This protocol should be the reusable pattern. |
| M/loop fields → committer (`mux:1254,1284`; `owner:3663–3701`) | passes and polling observed for batching targets | Written outside C, read while C is held. C alone does not publish those writes; memory visibility and coherent pair observation **UNVERIFIED**. |
| R → M adoption (`mux:1382–1397`) | chosen loop, socket and completion semaphore | **Nothing keeps inbox admission open across the gap.** R registration allows shutdown, but does not make M insertion happen before stop's last drain. Defect B2. |
| M inbox/arrived → loop (`mux:1189–1220`) | detached lists of connections/completions | Destructive queue detach transfers list ownership; conn processing confined to loop. Producers must stop before final detach. |
| M unsent → drain (`mux:1280–1294`; owner6001) | scalar count | M snapshot; combined with C awaiting count at different times. Core drain must accept this as a sampled observation, not an atomic global count. |
| R roster → join (`owner:4804–4811`) | copied thread list | Join outside R is good. Empty roster is only sound quiescence if removal occurs after *all* shared cleanup. Publisher/exporter violate that ordering. |
| O/R/A → publisher (`owner:5240–5257,5014ff`) | captured history/config/frontier/position plus live arena pin | Metadata is captured; pin retains old generation. Concurrent arena reads vs reseat need a representation-specific consistency lemma, not just retention. |
| O/R/A → exporter (`owner:5300–5415`) | immutable export capture, output target, arena pin | Same retention pattern; export uses dedicated execution but live arena. Final unpin after roster removal is unsafe for shutdown accounting. |
| O → reclaim build → O swap (`owner:5651–5788`) | captured records/position, own generation pin, private rebuilt catalog/history | Expensive work off O; final eligibility rechecked; `1- reader-count` at5745ff correctly discounts own pin. Current code repairs the “counts itself” example. Pin count is not yet a common typed capability across all jobs. |
| O → E cold issue → worker (`owner:4212`, `extent:890–910`) | fd, incarnation, exact request token, worker slot | Token inserted before release; close checks ownership. Do not report this current path as bare-fd borrowing. |
| E worker capture → pread (`extent:282–310,942–956`) | fd/incarnation and private buffer | Issued token/worker lease remains until actual return; cancellation only marks intent. Incarnation validation adds identity checking. |
| E cancel → later settlement (`extent:449–475,546–564`; owner4351ff) | cancelled job whose syscall can still be running | Correctly distinct from completed/refunded: physical return/join precedes release. This is an existing abstraction worth extending. |
| E result → owner cache install (`owner:4228–4300`) | worker-owned result vector/status/token | E protects validation/transfer; result cleared once consumed; pending-close retry happens after E release. Don't let a pooled buffer alias survive refund. |
| O/E snapshot source → offlock read (`owner:4867–4923`) | root/file lease, fd+offset+token | Explicit lease cleanup under E in unwind-protect. Some callers are staged; don't transfer this assurance to older raw realizers automatically. |
| E → raw page fill (`extent:1145–1155`) | fd and base copied, `pread` later | **No local pin acquired.** It can be safe if every caller holds O or a suitable arena/file lease. Universal caller lifetime establishment is **UNVERIFIED**; the local contract does not say it. Diagnose a claim-gap pending a reachable close-overlap witness, not automatically a demonstrated UAF. |
| E cache → decoder → E install (`extent:1089–1110`) | immutable compressed/list value, decoded result | Copy/list immutability protects value; decompressor checkout is separately locked. Physical cache charge/lifetime correspondence **UNVERIFIED**. |
| E register reserve → open/fstat → E install (`extent:91–118`) | reserved unique file identity/path and new fd | Registration protocol keeps identity reserved; failed fd closed and reservation removed. `register-at` installs base under E later147, before returning to its caller. |
| O/A retirement check → E close (`owner:4849–4860`, `extent:1228–1245`) | quiet retired group/generation | O keeps retirement state stable; A test then E token test guards actual close. A is released before E. Correctness requires every borrow to appear in one of those ledgers. |
| K detach → O arena reseat (`io:6845–6861`) | fenced member list | K transfers list; O serializes arena mutation; A defers old staged-page release. Offlock readers must retain representations that the reseat leaves readable. |
| K/seal → offlock fence → K result (`io:6875–6905,8043–8074`) | active log fd, sealed range, members | `sync-state` protocol is intended to prevent rotating/closing active fd. fd/dir fields themselves are not all read under K; a checked lease/epoch would make this obligation explicit. |
| S spare creation → O rotation (`io:7299–7397`) | spare `(index,path,fd)` | Preparers serialized by S, consumer by O, not a common mutex. Need uniqueness and matching-index revalidation; simultaneous preparer/consumer safety **UNVERIFIED** from field locks alone. |
| Offlock make-durable (`io:7403–7416`) | pending directory and current log fd | Two callers allowed (“Two callers may both fence; that is harmless”). Concurrent rotation/clear of pending dir needs an epoch/lease proof; duplicate fsync alone is harmless only when both refer to the intended segment. |
| Q dequeue → write → Q receipt (`io:1047–1067`) | queue item owns payload/fd swap intent | Single writer; queue mutation does not hold Q across I/O. Stop joins outside Q. Failure receipt classification is part of the protocol. |
| Q authority reservation → install/settle (`owner:648–699,4794,5830`) | reserved owner/run identity | Thread identity and retained authority are explicitly compared; nested unwind paths must preserve debt on ambiguous close. Not an ordinary local variable. |
| Read-only external observer (`io:8104ff`) | checkpoint/config/log directory and file observations while an owner may run | Source explicitly says “Read only, no lock, nothing renamed”. This diagnostic/test observation is not an atomic owner snapshot and cannot lend a production pin guarantee; namespace change during the scan must be treated within its observational scope. |
| Live stobj lookup → execution (`io:329–419`) | raw stobj object reference cached globally | Owner-only mutators and worker-private stobjs coexist with shared pinned reads. Synchronized lookup table does not protect object contents. See next subsection. |
| Signal handler → accept/stop (`io:8581ff`, owner5938/5961) | count/flag/wakeup fd | Minimal signal actions; cached fd lifetime deliberately retained through cleanup at owner6223ff. Runtime signal visibility/reentrancy is assumed, not ACL2-proved. |

### 3.6 ACL2 state in multiple native threads

The important question is not whether a function is written in ACL2; it is what mutable runtime cells it can touch. At `io.lisp:319–327` the old “one thread owns arena” explanation is too broad for the current pinned offlock readers. Publication explicitly calls `fn-owner-sco-next ... (fnn-live-arena)` outside O (`owner:5066`), export reads it (`:5357`), reclaim builds from captured data/arena, and cold workers use shared realizer state under E plus private executor storage.

The intended partition appears to be:

* O: live semantic owner/state globals, parser/read state, catalog updates and mutable arena transitions.
* E: shared raw extent read buffers/page pool and token/worker records (`extent:183–221,330–363`).
* Q/G/K/A: each core value state serialized by its corresponding host mutex, even though the ACL2 function is pure over that value.
* Worker-exclusive: checkpoint publication buffer (`io:250–295`, owner5103), cold execution buffers, rebuilt reclaim catalog/history, connection transport buffers.
* Shared read-only/pinned: captured lists, old view contents, and selected live-arena portions.

This partition is not an ACL2-wide concurrency theorem. A read of mutable arena metadata racing a reseat can fail even when both old and new byte payloads are retained. Need a concrete guarantee: immutable descriptor captured under O, or atomic publication of a descriptor whose fields are immutable, or a read protocol with version validation. “Generation pinned” alone does not select among them.

`io:366–379` reads world properties for dispatch/stobj metadata; serving assumes the world is frozen. Synchronized caches permit multiple readers/populators, but do not prove safe ACL2 world traversal if anything mutates it. `owner:1864` explicitly sets `*the-live-state*` in a staged control-turn epilogue outside O; do not activate that route without deciding the state-threading contract. `owner:5738–5741` calls owner key/salt accessors off O during reclaim construction; immutability of those globals during the whole operation needs a declared capture (or a proof), not a naming convention.

Hons and memoization are not excluded by use of pure logical functions: `books/served-catalog.lisp:2428,2439–2441,2478` uses `hons-acons`/`hons-get`; `strip-world:168–180` manipulates runtime hons/memoize structures. Whether these calls use safe thread-local spaces, runtime synchronization, or shared mutable tables in the selected ACL2/SBCL build is **UNVERIFIED** from this worktree. Likewise *1* guard execution may traverse a shared structure whose invariants are temporarily broken by another raw mutation. A-SBCL-RUNTIME is a named trust note, not an answer to alias ownership.

### 3.7 Ranked findings

**B1 — BUG, fault containment / stalled service.** `io:75–89` makes `fnn-entry-guard-fault` a subtype of `fnn-store-fault`, itself a `fnn-store-error`. `owner:3704` catches that parent and returns nil with comment “The service stopped between the wake-up and the gate.” No condition requires `service-stopping`. A fault from the off-O `fn-otb-issue` call at3460, for example, reaches this handler and can terminate the committer without fencing the service. The static exception path is established; occurrence without injected corruption/runtime error is **UNVERIFIED**. Fix: contain fault/indeterminate before the ordinary stopped/refused case, and require a stopped observation for the latter. Separately `owner:5011,5130,5141` logs and suppresses serious conditions; at5135–5141 the gated body mutates publication state without `fnn-owner-shared-action`. These are the same architectural fault: mutex release is not failure containment.

**B2 — BUG, adoption/stop transfer race.** Schedule: adopter registers socket/selects loop under R at `mux:1382–1391`; pause before M insertion. Stop sets stopping (`owner:1703–1707`) and shuts registered clients down (1730). Mux exits, drains its empty inbox (1312), closes wake fds (1333–1334). Resume adopter: pushes into a dead inbox (1393–1396), then wakes a closed fd (1397). No loop remains to finish that connection, close it and signal done313. Shutdown is not close, by the explicit comment at owner1723–1725. This is a concrete source-level schedule; forced execution on this revision is **UNVERIFIED**. Atomic “admit-to-live-inbox or close” under a shared lifecycle protocol repairs it; merely holding another lock around `push` does not.

**B3 — BUG, quiescence accounting.** Publisher removes itself from workers at `owner:5147–5150`, then unpins at5152, changes nursery at5153 and calls maybe-publish at5162. Export removes at5413 then unpins5415. `fnn-owner-wait-workers` returns when its R-protected snapshot is empty (4804–4811); shutdown uses empty roster among its predicates before store settlement and lifecycle joined (6258–6285). Thus an empty roster can coexist with a running thread still accessing shared pin/service state. A concrete damaging interleaving with reopen/reset is **UNVERIFIED**, but the advertised join predicate is already false. Keep registration through the outermost final shared cleanup, or let the owner reap terminated threads; do not self-unregister before return. Termination should be a receipt, not a prediction.

**B4 — BUG, mux timer busy-poll window.** `mux:1169–1175` excludes plan/resume-held connections from idle action, but `:1182–1185` still contributes their stale `idle-at` to the next deadline, excluding only out/input/await. `fnn-mux-plan-yield` at403–419 leaves idle-at unchanged. Once that deadline is past while resume is future, `:1244–1248` can select zero-time poll repeatedly until resume. This is a predicate mismatch, not proof that every yielded reply times out or loses data. Witness should put a cursor across an expired idle deadline with a future resume tick. Repair by using the same eligibility predicate for timer execution and scheduling (preferably core-owned).

**G1 — CLAIM-GAP, concrete borrow lifetime.** Bare page fd capture at `extent:1147` followed by pread1153 has no local lease. Some callers may correctly supply O/pins; other staged helpers explicitly acquire file leases. Establish caller-wide coverage before claiming a live UAF or claiming safety. Incarnation checks detect some identity changes but cannot prevent a syscall using a recycled integer.

**G2 — CLAIM-GAP, state/runtimes.** Shared arena consistency, world/global state access, hons/memoization and mux passes/polling publication are not discharged by the pin theorems or synchronized tables. See §3.5–6. This is a whole-system proof obligation, not evidence that SBCL is broken.

**G3 — CLAIM-GAP / availability defect relative to a latency claim.** Inline commit, append, rotate, reclaim installation and potentially cold realization perform disk/allocator work under O. Some are deliberate. No source-independent latency bound follows. The exact production profile and per-command cold route need measurement; do not label every such operation a functional data-corruption bug.

**G4 — CLAIM-GAP, offlock log fields.** S/O spare transfer and fd/dir-pending durability transfer have distinct locking domains (`io:7299–7416`). Protocol constraints may make them safe, but no declared common lease/epoch check connects them. Force rotation against both preparer and durability callers before proposing a lock inversion fix.

**N1 — NIT with real review cost.** Stale comments (“all calls”, “only renames”) obscure what the current code does. Generated lock/effect summaries should replace these manually maintained universal statements. Correct prose does not fix B1–B4.

Several examples in the question are already repaired or too broad at this coordinate: direct cold pread retains its token until physical return (`extent:449–475,942–956`); reclaim subtracts its own reader (`owner:5745ff`); guard cache1320 is staged startup allocation, not per-call allocation. Idle rearming exists on ordinary completion (`mux:500ff,748ff`), but the next-deadline mismatch remains. These distinctions matter: do not turn old findings into timeless project facts.

## 4. Why these issues keep recurring

My diagnosis is a missing *realization contract*, not a shortage of invariants in the core.

The project already has semantic decomposition: owner, store, served reference, representations, batch reader views, generations, response holds, crash programs and outcome classes. Each is useful. What is handwritten between them is when a fact becomes visible to another thread, which physical object realizes a logical resource, and which exception can escape between updating that object and recording its receipt. The committer handler, adoption race and premature roster removal are three manifestations of that missing layer (§3.7). None needs a broken ACL2 theorem to fail.

The hypotheses of a carried invariant are established at call boundaries, but host code can invalidate the *correspondence* between boundaries: return a pooled buffer while a worker still uses it, replace the state global before consumers finish, publish a completion under one lock while its reader watches another field, or catch a structural fault as refusal. `def-carried.lisp:84–95` already distinguishes stobj result facts from host-threaded value-state assertions. That is the right conceptual boundary to extend.

Several locking conventions **are written down**. Examples: roster ownership (`owner:108–123`), log kernel fields (`io:6306–6323`), extent pool exclusion (`extent:197`), and O-before-E retirement (`owner:4849–4852`). “Nobody wrote the lock discipline down” is therefore an inaccurate diagnosis. It is fragmented, incompletely executable, and sometimes stale. There is no single declaration connecting a field's protecting lock, its offlock capability, the failure scope, and the physical end-of-life receipt.

Likewise, “there is no concurrency model” is too broad. `fn-ocvm` models completed/working batch views; the recovery concurrent book reasons about a checkpoint with a batch in flight; issued read generations model cancellation/return. The missing model is the *composition of those protocols with actual host actor steps*. A crash-cut list is not a list of legal thread interleavings. `native_program_check.py:34–43` expressly excludes runtime control flow and callers. Enlarging the cut list alone cannot catch adopt after stop or exception swallowing.

Pins are not the wrong abstraction. They are multiple partially connected abstractions: arena generation pins, response holds, issued I/O tokens, file leases, batch generations, worker roster registrations and publication flags. Each may be locally correct while the translation from one to another is missing. The fix is a common capability/receipt discipline with typed kinds, not a single global reference count or an even larger owner critical section.

Review-by-reading found the problems because it follows control flow across the boundaries that current checks do not model. Reading remains necessary, particularly for specifications and FFI. It should stop being the only way to discover a broad parent exception handler, a raw resource escaping without a lease, or a last queue drain racing a producer. Those are finite mechanical obligations.

Finally, proof-oriented optimization and runtime-oriented optimization have drifted apart at some boundaries. Raw dispatch removes expensive invariant walks correctly *when* the invariant is carried. Offlock I/O reduces O hold time correctly *when* a capability survives. Neither optimization should be validated only by throughput or by a theorem about its inner helper. Require its boundary relation, exceptional transitions and physical ownership receipts together. That is consistent with AGENTS.md's “Behaviour and its invariants land together,” not a new process gate.

## 5. The whole-system statement I would adopt

### 5.1 Use trace refinement of a stateful snapshot interface

I would not start with “every reply and durable state equals the reference at some serial order of atomic commands.” It conflates command-level linearization, snapshot acquisition, durability, interrupted byte streams and incremental computation.

A pinned reader **can** be linearizable against a reference object whose state includes that reader's pinned view: linearize the pin/acquire operation, then evaluate subsequent commands against the retained view until a specified repin. It need not read the current archive at the time a later byte is sent. That is more precise than saying the whole node must provide database snapshot isolation, which carries additional transaction semantics not established here. `fn-own-read-is-served-step-on-pinned-prefix` (`owner-invariants-served:175`) already supplies the right reference vocabulary.

Define an executable concurrent machine **C** with:

* Core semantic state: the actual carried owner/config/credits/read-view state and concrete representation abstractions needed by served entries.
* Actor records: main/acceptor, each mux, committer, syncer, publisher, exporter, cold workers and enabled module actors. Each has a finite control phase and private state. Input-proportional data is in admitted resumable structures, not a fixed state-size cap.
* Lock ownership and waiting state; resource capabilities `(kind, object, incarnation, generation, holder)`; explicit queues; lifecycle state open/draining/closed; outstanding effect requests and completion receipts.
* Storage state: the byte-store/crash model, volatile versus durable contents, in-flight batches, checkpoint captures, namespace changes and barrier receipts.
* Environmental observations: bounded input chunks, socket/kernel outcomes, clock readings, signal requests, and scheduling choices. Host does not silently decide a logical outcome from an observation the core never sees.

Define a reference **R** with article/store/config semantics, connection and command state, pinned read epochs, accepted obligations, pending writes and recovery. Reuse the existing owner/store/served semantics; fill the ideal ports before calling R the *whole node*. The reference may nondeterministically choose among admissible recovery outcomes for an interrupted unacknowledged operation. It must not nondeterministically excuse arbitrary host misbehavior.

Define observations **Obs**:

1. Per-connection ordered bytes actually accepted by the transport boundary, plus connection termination and operation identifiers. For the network-facing claim distinguish “TLS accepted application bytes” from “remote application read them.” On reset/crash the emitted stream may be a prefix of the planned reply. There is no promise to undo bytes already sent.
2. Semantic outcomes: accepted, refused, uncertain/fenced, and execution fault remain distinct. A timeout is not a refusal. A lost success reply may leave a committed operation.
3. A logical abstraction of recoverable durable content and retained obligations, not equality of checkpoint/log byte layouts. Compaction and encoding may change physical bytes while preserving the abstract store.
4. Optional resource/lifecycle observations for the safety theorem: a borrow starts/ends, an effect is issued/settled, a close/forget/reclaim occurs. These are hidden from protocol clients but visible to the proof/checker.

For every **finite execution prefix** `c0 --a0--> ... --an--> cn` admitted by C, every initial pair satisfying relation `J(c0,r0)`, and every environment satisfying named platform/realizer assumptions, there exists a reference execution prefix `r0 --e0--> ... --em--> rm` such that:

```
Obs(C-prefix) = Obs(R-prefix)
J(cn, rm)
OwnershipSafe(C-prefix)
DurableAcceptanceSafe(C-prefix)
```

The matching map from concrete actions to zero or more reference actions is prefix-consistent. Internal work, polls, partial rendering and legal yields may stutter. Input consumption and externally visible actions preserve connection order and causal dependencies. The proof constructs a simulation; it does not choose a fresh unrelated serial history after seeing each reply. Distinct connections may interleave, but a response's bytes cannot be recomputed against a newer view halfway through a cursor.

The corresponding running-host claim is conditional on an additional realization relation **H↝C**: each emitted wrapper/handwritten leaf invocation implements its declared action, with correct memory publication, byte/identity observation and effect receipt. Do **not** put H↝C into a vague A-HOST hypothesis and declare victory. Generate its coordination skeleton, mechanically check the residual language, and qualify the small trusted leaves. The remaining runtime/OS assumptions must be individually named.

### 5.2 Durability and uncertainty

The durability property is: whenever an accepted outcome is exposed at the specified external boundary, a matching operation's durable obligation exists in the modeled persistent state, and every subsequent admissible crash/recovery retains it **until the reference authorizes its release/forget/replacement**. Reclaim cannot turn ordinary acknowledged permanence into deletion simply because no current thread holds a pointer. Conversely, after an authorized forget, retaining a thread pin protects memory safety, not a promise that the article remains logically visible forever.

An indeterminate effect leaves a pending obligation/fence. Recovery chooses among the model's allowed outcomes; no host rollback may erase a possibly durable operation and continue mutating. A refused operation can be proved absent only under its particular prepublication/known-failure conditions. A transport ACK is not a durable commit. This reuses the substance of `store-node-resolution.lisp:701`, `recovery-refinement-concurrent.lisp:303` and `specs/failures.md:75–79`.

Allow a crash between **every abstract primitive host action**, not just developer-instrumented `fnn-at` calls. Show that each such state abstracts to one of the existing permitted byte-program cuts or an equivalent stuttering state. Partial syscall effects belong to the device model. After crash, discard volatile sessions and unresolved worker executions, retain the permissible durable image, and reopen under the recovery relation. New boot/incarnation identities prevent stale completion receipts from a prior epoch being consumed as current work.

### 5.3 Resources and cost

OwnershipSafe should state, with typed capabilities rather than an untyped count:

* A physical resource is read/written only with the required live capability; shared read borrows are immutable/versioned or use a declared coherent read protocol.
* Every outstanding syscall/worker retains the file/buffer/generation capabilities it can still touch, including after logical cancellation. Settlement requires actual return or a declared definite termination receipt.
* Close/reuse/refund/reclaim requires no conflicting capability; successful close and resource settlement are distinguished when the syscall outcome is ambiguous.
* A completion can be consumed at most once, by the matching object incarnation/operation generation; retries have explicit idempotence or offset rules.
* Shutdown admission and queue transfer are atomic at the protocol level; quiescence requires no admitted producer, no runnable/shared-state worker, and all required cleanup receipts, not merely an empty host list.
* Mutable stobj fragments have one writer or a proved disjoint-update protocol; every concrete mutation preserves the relation required by the next host-called entry.

Use `fn-arpn` and response-plan pins as lemmas inside this invariant. Do not replace them with new helper-specific twins. The first resource instance should be an existing live handoff, so the theorem cannot silently describe a parked route.

Cost is a **separate companion theorem**, not an accidental clause of linearizability. For each admitted profile P and atomic scheduling quantum q, prove a bound on semantic steps, bytes touched, fresh allocation and retained-resource delta in terms of P, bounded input and the quantum's declared work budget. A command of unbounded output length must make bounded progress or yield with an exact continuation, never truncate to make the bound true. Prove that no O-held phase invokes a `may-block` leaf except explicitly scoped maintenance modes whose latency is excluded from a served-response claim. This follows D27 (`planning/decisions.md:1182ff`) and the cursor semantics, but is not yet established for the current native implementation (§3.4).

A physical wall-clock or RSS bound additionally needs runtime allocation/GC, syscall and scheduler assumptions plus matched measurements. Formal operation count is not fsync latency. Liveness requires fairness and resource availability; state them separately, with bounded-posture/deadline theorems only where the environment actually supplies bounds.

### 5.4 What is proved, assumed and checked

| Layer | Obligation |
|---|---|
| **Proved in ACL2** | C invariant initialization/preservation over *every enabled actor action*, simulation into R, snapshot/cursor response equality, completion identity/nonduplication, crash/recovery refinement, capability conservation and safe retirement; logical per-quantum work/space bounds. Generated obligations must include reachable witnesses and hypothesis-removal teeth. |
| **Named assumptions** | SBCL/compiler faithfully executes the approved subset; mutex publication/atomic primitives have specified memory semantics; FFI/syscall observations are faithful; storage obeys the chosen tear/barrier/namespace model; TLS/crypto/decompression realizers meet their scoped contracts; immutable offlock data really remains immutable under the checked realization. Avoid assuming the safety property itself. |
| **Mechanically checked against host source/build** | Every live core entry/realizer is declared, generated wrapper identity and actual call binding, exact state/result routing, effect ordering/receipt transitions, lockset/await rules, capability creation-transfer-release, no undeclared raw aliases or synchronization, exceptional exits and final cleanup, complete crash-action mapping. A restricted language can reject unknown constructs rather than pretending to understand arbitrary Lisp. |
| **Qualified on the immutable image** | Compiler/FFI/runtime leaves, raw vs logical boundary equality, forced scheduling/fault traces, socket partial I/O, descriptor reuse, durability platform scope, representative resource/time measurements. Qualification adds evidence; it does not prove all schedules. |

## 6. A landable path from this tree

These are estimates and proposed acceptance criteria, **UNVERIFIED estimates**, not a claim that the work has already been done. I would keep each step connected to a served path and reuse matching certification evidence at convergence, as `AGENTS.md`/`planning/how-we-work.md` require. No full closure builds per small edit and no new permanent audit lane.

### 6.1 First piece: atomic connection transfer and stop

I would take **B2 myself first**. Add a small declaration/protocol for loop admission: acquire a live-loop capability, enqueue ownership of socket+done, or return the socket for definite close/refusal. Stop closes admission, waits for/settles admitted producers, drains ownership, then closes wake handles. Choose a single serialization point rather than two independent R/M updates; avoid holding R while executing general connection cleanup. A closing inbox flag checked under M plus an admitted-transfer count/receipt is one plausible implementation; the exact protocol should be chosen against current shutdown flow, not prescribed by a generic macro.

Land the live fix, one executable protocol book, generated transition/wrapper declarations for this path, and a forced pause between R selection and enqueue. **Acceptance:** both orderings either deliver to a running loop or close and signal exactly once; no socket/pipe capability remains after joined; the old code has a failing witness; the new invariant admits and proves through its live entry. Include B3's worker completion receipt in this lifecycle vocabulary if it can stay a small coherent patch; otherwise the next piece must consume it. Estimate: 1 book, 300–700 logical lines, 150–350 host/generator lines, a focused test; low/medium proof effort. Approximately several working days, not an entire-system proof.

### 6.2 Second piece: typed failure scopes and physical termination receipts

Extend existing entry declarations with failure scope: pure/private, connection-local, shared-state, durability-ambiguous. Generate the wrapper that places guards, core call, result installation, cleanup and fence **inside the same exclusion boundary**. Preserve `fnn-owner-shared-action`'s correct distinctions (`owner:1771–1805`), and eliminate the broad committer swallow and publication completion suppression. A normal stopped exit must affirm the stop predicate. Make worker registration last through final shared cleanup; owner reaps a physical-return receipt before joined.

**Acceptance:** injected entry guard/raw escape at each start/complete/cleanup boundary produces the correct fault/uncertain outcome and no subsequent shared mutation; connection-only failures still cost one connection. The exception hierarchy is mechanically checked or generated so a parent catch cannot consume fault/uncertain unintentionally. Estimate: expand 1 protocol book, 300–700 logical lines, 300–700 host/declaration/checker lines; medium proof effort. Avoid turning every diagnostic write failure into a store fence: failure scope is explicit.

### 6.3 Third piece: one capability interface for physical reads and retained views

Use the already correct issued-cold-token route (`extent:890ff,449ff`) and snapshot file-lease helpers (`owner:4867ff`) as the implementation pattern. Make fd/page/window borrows opaque to host orchestration; raw syscall leaves require a capability with file incarnation and allowed byte range. Adapt the old page realizer, response pins and publisher/exporter captures to that interface. Reuse `fn-arpn`, response pins and existing pool accounting; do not create a second global resource authority.

**Acceptance:** pause a read after capture, cancel it, attempt close/reclaim/reuse, then return the worker; close/refund stays blocked until physical settlement. Duplicate/stale settlement is rejected without double release. A page fill cannot escape with a naked fd. A pinned arena read has a stated consistency mechanism, not just storage retention. Estimate: 1–2 books, 700–1,800 proof/model lines and 400–900 host/declaration lines; medium/high proof effort because representations matter.

### 6.4 Compose concurrent actor actions with the existing owner chain

Introduce C incrementally: owner entry, read capture/resume, enqueue, batch issue/return/complete, pin/release, shutdown. The scheduler is nondeterministic selection among enabled actions, not a simulator of SBCL's scheduling heuristics. The actor control phases and capabilities come from declarations used for wrappers. Prove each action preserves the global invariant and either stutters or takes a reference step; use `def-carried` to generate the closure obligations. Reuse the current `fn-own-run`, `fn-ocvm`, `fn-scr`/`fn-mca`, response cursor and credit lemmas.

**Acceptance:** the model generates/validates the actual live wrapper roster; omitted actor transition makes the completeness check fail; the read theorem reaches the host-called wrapper including result installation and refusal arms, not just `fn-own-read`. Positive and hypothesis-removal witnesses exercise valid operations with overlapping publication/reads/commits. Estimate: 2–3 books, 1,500–3,500 lines, 300–800 declaration/generator changes; high composition proof effort. Do not promise that this is just one induction: defining a useful noncircular invariant is the hard part.

### 6.5 Refine effect programs and arbitrary crashes

Extend the existing cut/program correspondence to split-phase effects, outcome arms, named callback leaves and every C action where a crash can change recovery. Keep byte-store/log/recovery theorems; add the simulation from effect issue/partial completion/receipt to their events. `native_program_check` can remain the small straight-line checker, while generated action programs provide the stronger control-flow coverage. Don't retrofit arbitrary Common Lisp into its current source-order scan and call that a proof.

**Acceptance:** checkpoint+batch in-flight, append, rotate, finish, recovery and reclaim-install have complete phase/effect maps; accepted output follows a matching durable receipt; arbitrary action-prefix crashes are covered, including after durable completion before response. Known refusal, uncertain and fault produce distinct traces. Estimate: 1–2 books plus existing-book bridges, 800–2,000 lines; high proof effort; reuse current byte-model evidence where bytes/closure match.

### 6.6 Make nonblocking owner phases and cost explicit

Split append/rotate/install phases where needed, preallocate outside O, and classify any remaining maintenance-only blocking phase honestly. Turn the mux timer action/next-deadline eligibility into one source of truth; preserve per-quantum cursor ownership and exact output. Add declarations for work/allocation budgets and generated rejection of `may-block` leaves in O-held served phases. Prove budget transitions and measure physical cost under matching scenarios.

**Acceptance:** stalled cold reads/barriers cannot hold O in the declared nonblocking mode; owner-held operations have a finite declared call graph; long replies/storage sizes yield rather than hit a hidden cap; guards do not traverse total store state each quantum; timer witness no longer busy-polls. Estimate: 1–2 books or extensions, 700–1,800 model/proof lines, 500–1,200 host lines; medium/high engineering and proof effort. Changing persistence ordering is not a cosmetic unlock and requires Step 6.5's relation.

### 6.7 Extend the same interface to all enabled modules, then qualify one candidate

Control/feed/pull/web/BP actors become declared participants, with modules omitted by a profile excluded from that profile's theorem. Complete the still-stubbed ideal ports as needed. Use the generated world/entry coverage and current-view machinery to report precise inclusion. Qualify one immutable source/image/profile at convergence and keep newer work separate; do not transfer a verdict to changed bytes.

**Acceptance:** zero undeclared live shared-state/realizer entries for the claimed profile, closed transition enumeration, no pending unknown lock/effect edges, all named assumptions attached to their actual subjects, required roots certified at the candidate's digest, focused interleaving/FFI/durability evidence archived. Estimate for module integration is **UNVERIFIED** until the inventory of enabled profiles and external hooks is complete; plausibly comparable to the first core composition rather than a final afternoon of bookkeeping.

A useful first core envelope is likely **4–8 new/extended books and roughly 5–12k net logical/declaration/host lines**, with some handwritten coordination deleted. That is an order-of-magnitude estimate, not a request to add a new 12k-line framework. Proof/integration effort is high, roughly multiple engineer-weeks (perhaps 4–12 for the core envelope, excluding full BP/ideal-port completion and platform qualification). A narrow lifecycle fix should land within days. Measurements and the first two proofs should revise the estimate.

### Stop doing these things

* Stop treating a named preserved predicate as evidence that the host supplies a coherent successor state. Check the concrete ownership and result route that establishes that premise.
* Stop adding isolated pin/holder counters for each new worker without a transfer/settlement map into the existing authorities.
* Stop catching `fnn-store-error` to mean “stopped” without inspecting the stopped state and preserving fault/uncertain subclasses.
* Stop self-removing workers before their final shared cleanup, and stop equating logical cancellation with physical completion.
* Stop using whole-state guard walks as the default safety repair on a served quantum. Use establishment/preservation plus bounded external kind/range checks, exactly as D40 and `def-carried` intend.
* Stop reporting every historical locking example as live. Retain a regression witness and current reachability coordinate for each.
* Stop calling the all-port ideal skeleton a whole-system result, or waiting for that entire ideal to be completed before fixing concrete handoff bugs.
* Stop expanding source scanners into an implicit general Lisp verifier. Restrict the coordination language, reject unknown constructs, and give the remaining handwritten leaves small explicit contracts.

## 7. Generate locking, or audit it?

**Generate the protocol, including locking; audit/check the leaves.** A declaration that says only `:lock owner` and `:guard foo` is insufficient. The bugs here are often between lock regions or in their failure cleanup. Generating the existing region boundaries unchanged would faithfully regenerate the bugs.

The exact lexical inventory, excluding comments/strings, is:

| File set | `with-mutex` | `with-recursive-lock` | explicit `grab-mutex` | Total explicit acquisition sites |
|---|---:|---:|---:|---:|
| native owner | 60 | 7 | 1 | 68 |
| native io | 7 | 11 | 0 | 18 |
| native extent | 41 | 0 | 0 | 41 |
| native mux | 9 | 0 | 0 | 9 |
| Four-file total | 117 | 18 | 1 | 136 |
| Other native Lisp | 88 | 7 | 0 | 95 |
| All requested Lisp | 205 | 25 | 1 | 231 |

There are also **26 `fnn-with-roster`, 21 `fnn-log-with-kernel`, 21 `fnn-owner-gated`, 66 `fnn-owner-serialized` call forms** across native Lisp. The four-file subset contributes 24,19,20,33 respectively. These are source call sites that expand/use some of the acquisitions above, **not additional independent physical lock sites to add to 231**. Macro definitions contain acquisitions counted above. A separate parked `sb-thread::with-system-mutex` is outside the 231 count and appears in Appendix B; the restricted count must not be advertised as every runtime lock.

Classification of fit, rather than a fabricated migration percentage:

* **135 of the 136 central sites are lexically scoped acquisitions.** They fit a generated scope *syntactically*. That does not make 135 semantically independent entry wrappers.
* **At least 41 extent sites** are instances of a common E-protected resource protocol: table update/snapshot, borrow/cancel/settle, cache acquire/release or worker mailbox. Those can be declared as protocol actions. Multi-phase register/open/install and read/return need multiple generated phases, not one lock wrapper.
* **Owner's 68 sites** include 15 G sites, 16 C sites, 7 Q sites, 7 L sites, 9 E sites, 7 direct O sites, 1 A, 1 roster macro body, 4 scoped W sites and 1 manual W acquisition. These are families, not 68 different generator features. Gate waits, commit waits, shutdown and exception cleanup need a small workflow/action language.
* **I/O's 18** are 8 Q,2 J,4 K (including macro),1 A,1 L,1 S,1 random; generate the serialization/transfer envelope, leave the syscall/FFI leaves handwritten and declared.
* **Mux's 9** are 8 M and1 C. Keep the event loop and per-connection private computation handwritten initially; generate inbox admission/drain, completion handoff, stop lifecycle and owner-entry calls. One manual W wait path needs a generated `await` with unwind, not “ban grab-mutex” without replacement.
* **Other 95** include initialization, foreign-context, worker-runtime, module and parked prototype locks. All scoped acquisitions are syntactic candidates. The count that fits *one-shot core-entry wrappers* is **UNVERIFIED** without transitive effect/alias declarations; I will not label an initialization lock or TLS context lock a semantic owner entry just to claim 100% coverage.

The source counts above are established; a “95% generatable” estimate would not be. Most coordination can plausibly be generated with a few reusable protocols, but all effects do not belong inside a mutex.

### Required declaration language

Build on `definterface`/`fn-interfaces`, not an unrelated registry. `def-carried` already knows actual stobj formals/results and generates proved obligations (`def-carried:22–95`); keep one source of truth for those. Add:

```
operation: actual host-called subject + wrapper/phase identity
state: read/write regions; carried relation; successor/result projection
actor: allowed actor kinds; private state; connection/store/boot epoch
locks: required/obtained/released; recursive permission; order class
inputs: scalar | immutable value | owned buffer | borrowed capability
outputs: copy | transfer | retained borrow; capability derivation
resources: acquire/retain/transfer/cancel/settle/refund/close receipts
blocking: pure | bounded-compute | may-allocate | may-block-I/O | await
workflow: capture -> execute -> settle; explicit revalidation conditions
failure: connection | shared-fault | durability-uncertain | private-job
       + cleanup obligations and fence-before-unlock requirements
persistence: effect program, operation ID, completion generation, crash map
cost: bounded input/work/allocation; yield/continuation contract
callbacks: finite declared targets with effects; no opaque semantic callback
```

This is a proposal, not syntax already accepted by the tree. Generation should emit (a) C transition definitions, (b) invariant/simulation proof obligations, (c) raw host coordination wrappers, and (d) a compact inventory/call binding for checking. A declared proof name is only a hint; generated exact obligations must prove, following `def-carried`'s successful design. Failure paths count as transitions. Resource roles should be typed; do not permit an arena-generation token to satisfy a file-incarnation borrow just because both are integers.

Handwritten trusted leaves remain: kernel/FFI calls, bounded copies/encoding realizers, transport polling/read/write, TLS context ownership operations, private compression, clock/signal observation, runtime joins/allocations. Their return values are observations, and generated code handles ownership/outcome transitions. The mux event loop can remain ordinary Lisp as long as it manipulates only its private state and invokes declared operations for shared state. Offlock workers can remain handwritten private computation with declared capabilities, completion publication and terminal cleanup. This is substantially smaller than proving an arbitrary Common Lisp interpreter.

### A checker first is useful—with a closed scope

Use a first checker to enforce the declared migrated enclave immediately: no direct O/R/M access outside its primitives; no naked socket/worker transfer; no unknown callback; no `may-block` call in a nonblocking phase; no lock-order edge outside the graph; no state/result discard where a successor must be installed; no resource escape other than copy/immutable/capability. Refuse ambiguous indirect calls rather than bless them from a regex.

It is a distraction if it only greps for `with-mutex`, prints a large baseline of exceptions, and declares the problem solved. It is also a distraction if implementing whole-program alias analysis delays the first live fix. Migrate a closed, small handoff first, prove/check it, then expand. Generated code can be inspected and qualified; generation does not itself remove the compiler/runtime trust boundary.

## 8. What this statement would not cover

| Exclusion | Separate statement or evidence needed |
|---|---|
| Wall-clock performance / p99 latency | Per-quantum logical cost plus runtime/GC/syscall scheduling bounds and measured profile workloads. Safety trace refinement permits arbitrarily slow stuttering. |
| Starvation / termination / useful service | Fair scheduling, available resources, transport/disk progress assumptions, and a well-founded progress/ranking argument for workflows. Absence of a lock-order cycle alone does not imply fairness. |
| Kernel/filesystem/device honesty | Scoped syscall and durability model qualification, including errors, tears, write isolation and namespace barriers; `specs/failures.md:65–105`. Process-kill tests alone do not establish power-loss behavior. |
| TLS confidentiality/authentication | Native TLS/crypto assumptions and configuration/identity policy. Correct byte routing does not prove OpenSSL, certificate trust or side-channel resistance. |
| Hash/signature strength and peer honesty | Computational assumptions and concrete implementation evidence; an abstract cryptographic model proves neither. Preserve conflicting evidence and provenance. A malicious peer remains an allowed input source. |
| External programs, OS resource exhaustion, administrator actions | Explicit modeled actions/permissions and deployment limits. A root user replacing store files is not an ordinary client event unless modeled. Operator misuse and legitimate repair need their own semantics. |
| Wall-clock truth | Treat time as observations with named policy/clock assumptions. Timeout cannot establish remote nonacceptance; expiry needs the chosen age/clock model (`failures:93–96`). |
| Cross-node end-to-end convergence | A network/peer/route model and liveness assumptions, especially disconnected BP operation. The local node theorem can provide a compositional component without claiming eventual delivery in an arbitrary partition. |
| All ideal ports before they are implemented | The theorem is profile/entry-roster scoped; missing ideal semantics remain explicit obligations. `ideal.lisp:1,14–21` is a skeleton, not an axiom allowing arbitrary results. |
| Arbitrary native memory corruption or an incorrect compiler | Named runtime/compiler assumptions, defensive isolation/qualification. Host discipline can eliminate avoidable races, not prove SBCL/C/kernel correct by declaration. |

The proposal **does cover** memory/resource lifetime errors and logical time-policy errors in its modeled host coordination. Those should not be hidden under “runtime excluded.” It also covers losing or duplicating accepted obligations, even when the immediate symptom is a worker disappearing rather than a wrong reply.

## 9. Measurements I want; framing I reject

These are requests for the liaison, not commands run in this consultation. Record source digest, enabled image/profile, platform and input scenario with each. Start with tests capable of refuting the concrete findings, not another full performance or proof sweep.

1. **Force adopt versus final inbox drain.** Pause exactly after R selection in `fnn-mux-adopt` and before M insertion. Stop/drain the loop, then resume. Observe socket close count, completion semaphore, client/inbox ownership and wake-fd behavior. Repeat both orderings. This establishes B2 dynamically with a tiny schedule.
2. **Fault the off-O committer entry.** Inject `fnn-entry-guard-fault` at `fn-otb-issue`, and a raw callback fault after commit START. Observe committer liveness, service-stopping, queued/done/awaiting and whether later owner mutations are admitted. Repeat publication-done and extent-close failures; distinguish pre-effect, partial-effect and cleanup faults. Do not settle for “thread ended with exit 0.”
3. **Pause publisher/exporter after roster removal.** Start shutdown, observe whether store/lifecycle reaches joined before unpin/final cleanup. Test reentry if run authority permits it. Record retained pins, worker alive status and lifecycle instance identity. This resolves B3's concrete consequence without assuming it.
4. **Timer predicate witness.** Use a yielded cursor with expired idle-at and future resume-at. Count poll calls/timeouts and owner quanta over that interval. It should sleep until relevant readiness/deadline, not spin on an ineligible timer. Include sparse/empty-progress windows and completion rearming.
5. **Raw page-fill lifetime.** Enumerate actual callers of the loaded `fn-pgs-fill-realize`/frame realizer. For each, identify O, generation pin or file lease. Pause after fd capture while publication/reclaim/retirement runs; force fd-number reuse where retirement is legally allowed. A helper unit test without its real caller is insufficient to classify G1.
6. **Pin/return conservation.** For direct cold workers, preserve the currently repaired behavior: stall `pread`, cancel and request close, check that credits/fd remain held; release the syscall and check single settlement/refund. Include stale generation, duplicate result and failed/ambiguous close.
7. **Owner lock hold/call graph.** Instrument O enter/leave and blocking leaf entry with held-lockset, operation/phase and current profile. Measure inline versus pipelined commits, cold/ warm reads, cursor quanta, rotate, checkpoint completion and reclaim swap. Report worst/percentile hold times and allocation per quantum with matched inputs; classify deliberate maintenance pauses separately. Do not infer “free memory” from a single OS counter.
8. **Log rotation overlap.** Pause spare preparation before install, rotation before/after fd replacement, and each make-durable caller before clearing dir-pending. Record segment identity and exact fd incarnation for each fsync. Confirm the no-rotate-while-sync protocol with an executable assertion, or produce the missing schedule.
9. **Runtime state access.** In the selected ACL2/SBCL image, enumerate runtime world writes after listeners start, actual hons/memoized functions reached by offlock workers, and their thread-local/synchronized backing. Audit `*the-live-state*` and `user-stobj-alist` mutation sites, including any staged route activated by profile. No generic claim that “ACL2 is single-threaded” substitutes for this inventory.
10. **Guard/allocation cost.** Count entry-guard calls, cache construction, recognized kind predicate traversal and failure-description allocation per quantum. Compare current raw/carried dispatch with counterpart only under matched inputs and invariants. Specifically verify that the staged cold cache is prepared once when activated, rather than repeating the historical per-call allocation claim.
11. **Model/host coverage coordinate.** Generate the current live profile's actual dispatch/actor/realizer roster from the built image and compare it with source declarations; classify parked helpers separately. Request existing matching manifests first. Certify only new/affected roots during development and the agreed immutable candidate at convergence.
12. **Cost of the proposed abstraction.** Before broad rollout, measure generated handoff/capability wrapper overhead, allocation and lock contention against its predecessor with the same interleaving tests. A safer abstraction should simplify the state machine and remove duplicate bookkeeping, not add a second ledger on every byte.

I reject five parts of the implied framing:

* There is not *no* whole-system work: the serial owner/store trace, pinned served chain and concurrent recovery results are substantial. The missing host simulation is specific and bridgeable.
* A bigger theorem over the existing serial machine will not find races in code it does not describe. Conversely, a scheduler model with no generated/checked host connection would be another orphan model.
* “Some serial order” is inadequate unless it fixes operation identities, real-time/causal constraints, pinned snapshots, multi-quantum continuations, partial byte output and durable uncertainty. A stateful snapshot reference can express these without pretending every read sees the newest archive.
* The right alternative to auditing is not “all mutexes generated from entry names.” Generate capture/execute/settle and admission/stop protocols, and mechanically constrain the handwritten boundary. Continue reviewing the small TCB and the *meaning* of declarations.
* The historical example list is not a current defect inventory. This source already retains cold-read tokens through physical return and discounts reclaim's own pin. Preserve those repairs, connect their consumers, and use counterexamples to determine what remains.

The first useful result is a running live handoff whose invariant and realization are tied together. Repeating that pattern across the existing protocols is a plausible route to the requested whole-system statement; another detached audit, another scalar “green” count, or another theorem about a helper is not that route.

## Supplemental boundary: GC pinning is not resource ownership

`sb-sys:with-pinned-objects` keeps a Lisp object stationary during an FFI call; it does not keep the fd open, charge the buffer, freeze its contents against another thread, or authorize reuse after the call. Concrete four-file sites are listed in Appendix C. In particular `extent.lisp:161,264` pins the destination vector around foreign pread, and `mux.lisp:150,227,234` pins poll/wake buffers. These scopes must be nested inside the operation's resource capability, not used as substitutes for generation/file/worker ownership. No explicit `without-gcing` scope was found in the central four-file search. Runtime-internal GC synchronization remains part of A-SBCL-RUNTIME and the measurement request in §9.

## Appendix A. Every requested Lisp file: physical size and responsibility

Counts use `len(Path.read_text().splitlines())` at the source coordinate above. **L** = ACL2-mode semantic/state adapter (often `:program`, not automatically proved); **D** = declaration registry; **B** = build/world transformation; **F** = raw foreign realization plus boundary checks; **M** = mixed raw I/O and scheduling/lifecycle/outcome decisions; **G** = relatively thin raw realization/dispatch adapter, still includes boundary decisions; **P** = runtime/staged/prototype adapter, activation must be checked separately. P is not a blanket claim that every such file is unloaded; `build.lisp:499,510–512,579ff` makes finer distinctions. Neither G nor F means “decision-free.”

The table quotes a representative declaration from each file so its structural classification can be checked. This is **not** a claim to have semantically audited every line of all 66,848 lines. Per-file decision responsibility outside the detailed four-file review is a conservative classification; precise live reachability, all domain-policy duplication and proof coverage remain **UNVERIFIED** until linked to the built profile.

| File | Lines | Class | Representative source declaration (line: quote) |
|---|---:|---|---|
| `host/account-admission-semantic-host.lisp` | 159 | L | 6: `(include-book "admission-semantic-node-host")` |
| `host/account-adoption-begin-source-host.lisp` | 48 | L | 5: `(include-book "account-adoption-turn-host")` |
| `host/account-adoption-collection-host.lisp` | 29 | L | 4: `(include-book "account-durable-completion-host")` |
| `host/account-adoption-host.lisp` | 144 | L | 4: `(include-book "account-adoption-turn-host")` |
| `host/account-adoption-interfaces.lisp` | 10 | D | 1: `; Declarations are checked by the actual build world. PROGRAM entries have` |
| `host/account-adoption-operation-host.lisp` | 85 | L | 5: `(include-book "owner-host")` |
| `host/account-adoption-publication-host.lisp` | 89 | L | 6: `(include-book "account-adoption-operation-host")` |
| `host/account-adoption-return-host.lisp` | 102 | L | 5: `(include-book "account-adoption-turn-host")` |
| `host/account-adoption-turn-host.lisp` | 134 | L | 3: `(include-book "../books/account-adoption-turn-state")` |
| `host/account-config-continuation-host.lisp` | 155 | L | 4: `(include-book "account-config-preparation-host")` |
| `host/account-config-journal-host.lisp` | 137 | L | 4: `(include-book "account-config-source-host")` |
| `host/account-config-preparation-host.lisp` | 147 | L | 7: `(include-book "account-config-source-host")` |
| `host/account-config-source-host.lisp` | 116 | L | 4: `(include-book "owner-host")` |
| `host/account-durable-alias-clear-host.lisp` | 74 | L | 5: `(include-book "account-durable-completion-host")` |
| `host/account-durable-completion-host.lisp` | 113 | L | 6: `(include-book "owner-host")` |
| `host/account-preparation-admission-host.lisp` | 27 | L | 3: `(include-book "../books/admission-preallocation-resources")` |
| `host/account-replay-operation-host.lisp` | 35 | L | 3: `(include-book "account-adoption-host")` |
| `host/admission-authority-dispatch-host.lisp` | 54 | L | 4: `(include-book "admission-preparation-host")` |
| `host/admission-authority-preparation-host.lisp` | 120 | L | 5: `(include-book "admission-history-tail-host")` |
| `host/admission-history-tail-host.lisp` | 137 | L | 4: `(include-book "admission-semantic-node-host")` |
| `host/admission-preparation-host.lisp` | 52 | L | 8: `(include-book "owner-host")` |
| `host/admission-semantic-census-host.lisp` | 182 | L | 4: `(include-book "admission-semantic-node-host")` |
| `host/admission-semantic-node-host.lisp` | 99 | L | 3: `(include-book "admission-preparation-host")` |
| `host/allocation-epoch-host.lisp` | 124 | L | 5: `(include-book "../books/allocation-epoch-collection-request")` |
| `host/anchor-host.lisp` | 101 | L | 20: `(include-book "../books/anchor-invariants")` |
| `host/anchor-server-host.lisp` | 13 | L | 4: `(include-book "../books/anchor-servers")` |
| `host/anchor-wire-host.lisp` | 49 | L | 9: `(include-book "../books/anchor-wire")` |
| `host/bp-controller-checkpoint-directory-host.lisp` | 36 | L | 3: `(include-book "../books/bp-controller-checkpoint-directory-fuel")` |
| `host/bp-controller-checkpoint-payload-host.lisp` | 11 | L | 3: `(include-book "../books/bp-controller-checkpoint-payload-directory")` |
| `host/bp-native-app-host.lisp` | 454 | L | 8: `(include-book "../books/bp-channel-ingress")` |
| `host/bp-node-host.lisp` | 168 | L | 15: `(include-book "../books/bp-node")` |
| `host/bp-node-machine-host.lisp` | 65 | L | 6: `(include-book "../books/bp-node-host-machine")` |
| `host/bp-receipt-journal-host.lisp` | 148 | L | 2: `(include-book "../books/bp-native-app-fast")` |
| `host/bp-receive-evidence-host.lisp` | 36 | L | 3: `(include-book "../books/bp-receive-evidence")` |
| `host/bp-release-owner-host.lisp` | 105 | L | 4: `(include-book "../books/bp-release")` |
| `host/checkpoint-host.lisp` | 307 | L | 6: `(include-book "../books/checkpoint-publish")` |
| `host/config-host.lisp` | 108 | L | 14: `(include-book "../books/node-config")` |
| `host/connection-receiver-source-host.lisp` | 102 | L | 5: `(include-book "index-connection-owner-host")` |
| `host/consumer-remote-host.lisp` | 189 | L | 4: `(include-book "../books/consumer-remote-dispatch")` |
| `host/consumer-remote-reader-host.lisp` | 172 | L | 6: `(include-book "consumer-remote-host")` |
| `host/consumer-remote-report-host.lisp` | 104 | L | 4: `(include-book "consumer-remote-reader-host")` |
| `host/feed-filename-host.lisp` | 24 | L | 4: `(include-book "../books/feed-filename")` |
| `host/history-admission-producer-host.lisp` | 118 | L | 7: `(include-book "admission-preparation-host")` |
| `host/history-operation-observation-host.lisp` | 3 | L | 3: `(include-book "../books/history-operation-observation")` |
| `host/history-owner-completion-host.lisp` | 178 | L | 6: `(include-book "owner-host")` |
| `host/history-owner-view-host.lisp` | 20 | L | 3: `(include-book "owner-host")` |
| `host/hybrid-signature-host.lisp` | 84 | L | 3: `(include-book "../books/hybrid-store")` |
| `host/index-connection-owner-host.lisp` | 133 | L | 6: `(include-book "owner-host")` |
| `host/index-connection-pins-host.lisp` | 46 | L | 4: `(include-book "../books/index-connection-issuer")` |
| `host/index-connection-repin-prepare-host.lisp` | 17 | L | 4: `(include-book "../books/index-connection-repin-prepare")` |
| `host/index-incoming-request-host.lisp` | 149 | L | 7: `(include-book "../books/index-incoming-request")` |
| `host/index-publication-host.lisp` | 83 | L | 3: `(include-book "../books/owner-report-owner-accessors")` |
| `host/index-reader-request-host.lisp` | 183 | L | 5: `(include-book "../books/index-reader-request")` |
| `host/index-writer-begin-host.lisp` | 63 | L | 2: `(include-book "index-publication-host")` |
| `host/index-writer-operation-host.lisp` | 282 | L | 4: `(include-book "index-writer-begin-host")` |
| `host/interfaces-extract.lisp` | 18 | D | 10: `(include-book "../books/definterface")` |
| `host/interfaces-raw.lisp` | 7 | D | 4: `(include-book "../books/definterface")` |
| `host/interfaces.lisp` | 4,992 | D | 22: `(include-book "../books/definterface")` |
| `host/journal-publish-host.lisp` | 42 | L | 3: `(include-book "../books/journal-publish")` |
| `host/native-admin-host.lisp` | 281 | L | 3: `(include-book "../books/native-admin")` |
| `host/native-auth-admin-host.lisp` | 83 | L | 7: `(include-book "../books/native-auth-admin")` |
| `host/native-auth-host.lisp` | 32 | L | 3: `(include-book "../books/native-auth-profile")` |
| `host/native-config-host.lisp` | 25 | L | 4: `(include-book "../books/native-config")` |
| `host/native-control-host.lisp` | 318 | L | 3: `(include-book "../books/native-control")` |
| `host/native-hybrid-control-host.lisp` | 46 | L | 2: `(include-book "../books/native-hybrid-control")` |
| `host/native-live-status-host.lisp` | 277 | L | 8: `(include-book "../books/native-health")` |
| `host/native-operator-host.lisp` | 391 | L | 7: `(include-book "../books/native-operator")` |
| `host/ninep-mount-host.lisp` | 65 | L | 4: `(include-book "../books/ninep-mount")` |
| `host/ninep-mounted-directory-host.lisp` | 43 | L | 5: `(include-book "../books/ninep-mounted-directory")` |
| `host/ninep-protocol-host.lisp` | 78 | L | 3: `(include-book "../books/ninep-header")` |
| `host/ninep-session-host.lisp` | 45 | L | 2: `(include-book "../books/ninep-dispatch")` |
| `host/ninep-stat-stream-host.lisp` | 17 | L | 4: `(include-book "../books/ninep-stat-stream")` |
| `host/ninep-transport-host.lisp` | 34 | L | 2: `(include-book "../books/ninep-transport")` |
| `host/owner-connection-callbacks.lisp` | 4 | L | 4: `(include-book "../books/owner-connection-callbacks")` |
| `host/owner-exposure-host.lisp` | 32 | L | 5: `(include-book "../books/owner-state-accessors")` |
| `host/owner-host.lisp` | 5,239 | L | 26: `(include-book "../books/owner-report-capture")` |
| `host/owner-report-writer-host.lisp` | 3 | L | 3: `(include-book "../books/owner-report-writer-entry")` |
| `host/page-executor-host.lisp` | 37 | L | 4: `(include-book "page-read-host")` |
| `host/page-file-lease-host.lisp` | 74 | L | 3: `(include-book "page-read-host")` |
| `host/page-read-host.lisp` | 467 | L | 6: `(include-book "../books/page-read-ownership")` |
| `host/page-window-executor-host.lisp` | 239 | L | 3: `(include-book "page-read-host")` |
| `host/page-window-lease-host.lisp` | 43 | L | 4: `(include-book "page-read-host")` |
| `host/payload-view-host.lisp` | 60 | L | 5: `(include-book "../books/payload-view-lease")` |
| `host/peer-invite-host.lisp` | 143 | L | 4: `(include-book "../books/peer-invite")` |
| `host/post-identity-captured-host.lisp` | 195 | L | 4: `(include-book "../books/post-identity-captured-holder")` |
| `host/query-payload-scalar-host.lisp` | 41 | L | 3: `(include-book "../books/index-backing-provider")` |
| `host/query-publication-arena-host.lisp` | 17 | L | 4: `(include-book "../books/index-backing-generations")` |
| `host/reader-host.lisp` | 194 | L | 3: `(include-book "../books/owner-report-capture")` |
| `host/receiver-capacity-current-host.lisp` | 183 | L | 4: `(include-book "../books/receiver-capacity-current")` |
| `host/receiver-repin-source-host.lisp` | 40 | L | 3: `(include-book "receiver-source-gate-host")` |
| `host/receiver-resource-host.lisp` | 60 | L | 5: `(include-book "../books/receiver-provider")` |
| `host/receiver-source-gate-host.lisp` | 32 | L | 4: `(include-book "runtime-receiver-source-host")` |
| `host/receiver-turn-resource-host.lisp` | 37 | L | 6: `(include-book "receiver-resource-host")` |
| `host/recovery-initial-operation-host.lisp` | 28 | L | 4: `(include-book "recovery-initial-source-host")` |
| `host/recovery-initial-source-host.lisp` | 74 | L | 4: `(include-book "../books/recovery-source-authority")` |
| `host/recovery-payload-view-host.lisp` | 55 | L | 4: `(include-book "snapshot-initial-host")` |
| `host/recovery-payload-view-state.lisp` | 16 | L | 3: `(include-book "../books/recovery-payload-view")` |
| `host/recovery-source-host.lisp` | 55 | L | 5: `(include-book "../books/recovery-source-authority")` |
| `host/runtime-receiver-source-host.lisp` | 16 | L | 5: `(include-book "../books/runtime-operation-source")` |
| `host/snapshot-initial-constructor-host.lisp` | 19 | L | 4: `(include-book "snapshot-initial-host")` |
| `host/snapshot-initial-host.lisp` | 49 | L | 4: `(include-book "../books/snapshot-initial-custody")` |
| `host/snapshot-initial-root-host.lisp` | 48 | L | 4: `(include-book "page-file-lease-host")` |
| `host/store-checkpoint-context-host.lisp` | 49 | L | 5: `(defun fn-store-sco-current (state)` |
| `host/store-host.lisp` | 542 | L | 15: `(include-book "../books/replay")` |
| `host/store-node-host.lisp` | 1,844 | L | 8: `(include-book "../books/store-observed")` |
| `host/store-open-host.lisp` | 672 | L | 35: `(defmacro fn-hx-stub (name)` |
| `host/store-write-host.lisp` | 1,901 | L | 51: `(defun fn-hx-getenv (name) (declare (xargs :mode :program) (ignore name)) (fn-hx-stub fn-hx-getenv))` |
| `host/tcpcl-host.lisp` | 185 | L | 16: `(include-book "../books/tcpcl-session")` |
| `host/tls-reload-host.lisp` | 62 | L | 5: `(include-book "../books/tls-reload")` |
| `host/topic-history-metadata-host.lisp` | 3 | L | 3: `(include-book "../books/topic-history-authorship")` |
| `host/web-host.lisp` | 104 | L | 7: `(include-book "../books/web-session-keystones")` |
| `host/workflow-host.lisp` | 330 | L | 3: `(include-book "../books/bp-workflow-constructors")` |
| `host/native/account-adoption.lisp` | 62 | P | 10: `(defun fnn-account-retain-control-effects (service result)` |
| `host/native/acl2-session.lisp` | 44 | G | 21: `(defun fnn-command-acl2 (command args)` |
| `host/native/admin.lisp` | 672 | M | 11: `(defun fnn-admin-plan-acceptedp (plan)` |
| `host/native/admission-preallocation.lisp` | 14 | P | 7: `(defun fnn-account-preparation-admit (job-source work-descriptor)` |
| `host/native/anchor.lisp` | 448 | M | 13: `(defun fnn-anchor-csprng-nonce (nonce-octets)` |
| `host/native/auth-admin.lisp` | 537 | M | 11: `(defvar *fnn-native-auth-admin-secret-reader* nil)` |
| `host/native/auth-adoption-parked.lisp` | 80 | P | 17: `(defun fnn-native-auth-adopt-config (service config bindings)` |
| `host/native/auth-read.lisp` | 14 | G | 4: `(defun fnn-native-auth-read (path maximum)` |
| `host/native/auth.lisp` | 120 | M | 22: `(defvar *fnn-owner-startup-hooks* nil)` |
| `host/native/bp-app.lisp` | 396 | M | 4: `(defun fnn-bpapp-core-record (name &rest args)` |
| `host/native/bp-contact.lisp` | 84 | M | 6: `(defun fnn-bpc-u64-argument (text label)` |
| `host/native/bp-control-client.lisp` | 19 | G | 4: `(defun fnn-bpnc-status-unavailable (path kind)` |
| `host/native/bp-control.lisp` | 196 | M | 4: `(defstruct fnn-bpnc control model owner listeners)` |
| `host/native/bp-listener-control.lisp` | 96 | M | 3: `(defstruct fnn-bplc model mode (owned nil) (live nil))` |
| `host/native/bp-node.lisp` | 1,165 | M | 5: `(defun fnn-bpnode-observed-channel (socket)` |
| `host/native/bp-obligation.lisp` | 382 | M | 8: `(defvar *fnn-bpo-carry-journal* nil)` |
| `host/native/bp-service.lisp` | 1,548 | M | 10: `(defstruct fnn-bps` |
| `host/native/bp.lisp` | 904 | M | 36: `(defun fnn-bp-eid (text)` |
| `host/native/bpsec-crypto.lisp` | 298 | F | 22: `(defparameter *fnn-bpsec-required-symbols*` |
| `host/native/build-dtn.lisp` | 448 | B | 35: `(include-book "books/image-world-dtn")` |
| `host/native/build-store-test.lisp` | 145 | B | 16: `(include-book "books/image-world-store-test")` |
| `host/native/build.lisp` | 622 | B | 22: `(include-book "books/image-world")` |
| `host/native/checkpoint.lisp` | 494 | M | 22: `(defun fnn-checkpoint-require-mutation-ready (store)` |
| `host/native/config.lisp` | 30 | G | 11: `(defun fnn-command-config-profile (path)` |
| `host/native/consumer-local.lisp` | 177 | M | 5: `(defun fnn-consumer-say (json operation status word &optional counts summary)` |
| `host/native/consumer-remote.lisp` | 73 | G | 5: `(defun fnn-remote-read-exact (channel count seconds)` |
| `host/native/control-transport.lisp` | 287 | M | 8: `(defstruct (fnn-control-state (:constructor %make-fnn-control-state))` |
| `host/native/control.lisp` | 936 | M | 11: `(defvar *fnn-hybrid-control-handler* nil)` |
| `host/native/crypto.lisp` | 243 | F | 30: `(defvar *fnn-crypto-state* :uninitialized)` |
| `host/native/deflate.lisp` | 632 | F | 28: `(defvar *fnn-deflate-state* :uninitialized)` |
| `host/native/digest.lisp` | 554 | F | 102: `(defun fnn-digest-library-name ()` |
| `host/native/extent-decoded.lisp` | 71 | G | 6: `(defun fnn-extent-decoded-window-drive` |
| `host/native/extent.lisp` | 1,274 | M | 48: `(defvar *fnn-extent-lock* (sb-thread:make-mutex :name "fn extent realizer"))` |
| `host/native/feed-filename.lisp` | 71 | G | 10: `(defun fnn-feed-filename-component-p (component)` |
| `host/native/feed-service.lisp` | 623 | M | 30: `(defstruct (fnn-feed-link (:constructor %make-fnn-feed-link))` |
| `host/native/heap.lisp` | 361 | M | 32: `(defun fnn-heap-sysconf (name)` |
| `host/native/hybrid-control.lisp` | 346 | M | 3: `(defun fnn-hybrid-control-enroll (service request)` |
| `host/native/immutable-publish.lisp` | 125 | G | 8: `(defun fnn-immutable-test-fault (point path operation-label)` |
| `host/native/index-writer-turn.lisp` | 128 | P | 5: `(defstruct (fnn-index-writer-binding` |
| `host/native/io.lisp` | 8,649 | M | 83: `(defun fnn-fixed-callback-fail (subject tag cause)` |
| `host/native/keys.lisp` | 104 | G | 19: `(defun fnn-keys-owner-redecide (service msgid)` |
| `host/native/login-bindings.lisp` | 66 | G | 18: `(defun fnn-login-bindings-owner-reload (service)` |
| `host/native/mux.lisp` | 1,464 | M | 70: `(defstruct (fnn-mux-loop (:constructor %make-fnn-mux-loop))` |
| `host/native/ninep.lisp` | 77 | G | 6: `(defun fnn-ninep-copy-observed (octets buffer)` |
| `host/native/operator-control-client.lisp` | 77 | G | 5: `(defun fnn-operator-status-detail (status word)` |
| `host/native/operator-live.lisp` | 275 | M | 20: `(defun fnn-operator-execute-run (result)` |
| `host/native/operator.lisp` | 1,169 | M | 26: `(defun fnn-operator-action-surface (action)` |
| `host/native/owner-control-turn.lisp` | 113 | G | 5: `(defstruct (fnn-owner-control-binding` |
| `host/native/owner.lisp` | 6,392 | M | 29: `(defvar *fnn-owner-start-hooks* nil)` |
| `host/native/peer-invite.lisp` | 517 | M | 22: `(defun fnn-pinv-path (directory name) (fnn-join directory name))` |
| `host/native/post-captured-parked.lisp` | 96 | P | 17: `(defstruct (fnn-owner-pic-runtime (:constructor %make-fnn-owner-pic-runtime))` |
| `host/native/pull-service.lisp` | 589 | M | 42: `(defstruct (fnn-pull-runtime (:constructor %make-fnn-pull-runtime))` |
| `host/native/reader-model-host.lisp` | 41 | G | 22: `(defun fn-reader-model-octets (chunks fn-arena state)` |
| `host/native/receiver-parser-turn.lisp` | 36 | G | 7: `(defun fnn-owner-receiver-turn-parser-locked (service cid node sched ticket)` |
| `host/native/receiver-turn-parked.lisp` | 504 | P | 17: `(defun fnn-owner-receiver-runtime-make` |
| `host/native/recovery-payload-view.lisp` | 63 | P | 4: `(defun fnn-snapshot-recovery-payload-view-acquire (service maintenance source)` |
| `host/native/recovery-profile-read.lisp` | 55 | P | 7: `(defun fnn-recovery-profile-perform (effect binding)` |
| `host/native/runtime-bootstrap.lisp` | 204 | P | 3: `(defstruct (fnn-runtime-bootstrap` |
| `host/native/runtime-collector.lisp` | 62 | P | 13: `(defstruct (fnn-runtime-collection` |
| `host/native/runtime-construction-inventory.lisp` | 117 | P | 4: `(defstruct (fnn-runtime-construction-inventory` |
| `host/native/runtime-construction-recipe.lisp` | 73 | P | 6: `(defun fnn-runtime-construction-owned-roots (source-owned)` |
| `host/native/runtime-image-policy.lisp` | 75 | P | 4: `(defparameter *fnn-runtime-bootstrap-ordinary-signals*` |
| `host/native/runtime-participants.lisp` | 246 | P | 4: `(defstruct (fnn-runtime-participants` |
| `host/native/runtime-profile-envelope.lisp` | 71 | P | 4: `(defstruct (fnn-runtime-profile-envelope-binding` |
| `host/native/runtime-recovery-file.lisp` | 121 | P | 5: `(defun fnn-recovery-profile-retain-effects (bootstrap slots pool)` |
| `host/native/runtime-u64-request-source.lisp` | 18 | P | 4: `(defun fnn-runtime-u64-primary-request-unit ()` |
| `host/native/signature-command.lisp` | 272 | M | 4: `(defun fnn-hsig-command-read-exact (path width label)` |
| `host/native/signatures.lisp` | 383 | F | 17: `(defun fnn-hsig-max-message-octets ()` |
| `host/native/snapshot-initial-reader.lisp` | 35 | P | 11: `(defun fnn-snapshot-initial-reader-begin` |
| `host/native/snapshot-producer.lisp` | 631 | P | 7: `(defstruct (fnn-snapshot-job (:constructor %make-fnn-snapshot-job))` |
| `host/native/snapshot-startup.lisp` | 149 | P | 6: `(defstruct (fnn-snapshot-initial-workspace` |
| `host/native/strip-world.lisp` | 334 | B | 20: `(defparameter *fnn-world-execution-properties*` |
| `host/native/tcpcl.lisp` | 773 | M | 49: `(defstruct (fnn-tcl-conn (:conc-name fnn-tclc-))` |
| `host/native/tls-reload.lisp` | 171 | M | 18: `(defvar *fnn-tls-reload-mutex* (sb-thread:make-mutex :name "fn tls reload")` |
| `host/native/tls.lisp` | 1,073 | F | 64: `(defstruct (fnn-tls-context (:constructor fnn-tls-context-make))` |
| `host/native/topic-local.lisp` | 32 | G | 5: `(defun fnn-command-topic-local (command argv)` |
| `host/native/web-host.lisp` | 360 | M | 34: `(defstruct (fnn-web-face (:constructor %make-fnn-web-face))` |
| `host/native/workflow.lisp` | 733 | M | 10: `(defstruct fnn-app-journal` |

## Appendix B. Explicit synchronization and coordination site census

This census scans all 190 files after masking strings and line comments. It records every line with an `sb-thread` form/reference, synchronized-table declaration, atomic/interrupt/finalizer/deadline form, or the roster/kernel/gated/serialized and module synchronization wrappers named below. Original source is quoted; the nearest definition is navigation assistance, not a parsed lexical-containment proof. Backquoted macro bodies count as source sites; comments and docstrings do not. Every direct acquisition in owner/io/extent/mux is included, as are waits, notifications, joins, semaphores, thread identities and equivalent wrappers. Runtime-internal locking, indirect callbacks and arbitrary alias effects are **UNVERIFIED** by this lexical method. See §3 for the semantic protection/transfer tables.

### `host/native/account-adoption.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 11 | `fnn-account-retain-control-effects` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 24 | `fnn-account-adoption-begin` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 29 | `fnn-account-adoption-tick` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 34 | `fnn-account-adoption-status` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 42 | `fnn-account-adoption-epilogue` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 48 | `fnn-account-adoption-collect` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 57 | `fnn-owner-account-publication-locked` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |

### `host/native/admin.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 331 | `fnn-owner-compaction-request` | `(word (fnn-owner-serialized` |
| 350 | `fnn-owner-inspect-request` | `(found (fnn-owner-serialized` |
| 365 | `fnn-owner-export-request` | `(word (fnn-owner-serialized` |
| 403 | `fnn-owner-reclaim-request` | `(word (fnn-owner-serialized` |
| 418 | `fnn-owner-reclaim-request` | `(fnn-owner-serialized` |
| 491 | `fnn-owner-limit-serialized` | `(fnn-owner-serialized` |
| 587 | `fnn-owner-live-admin-serialized` | `(fnn-owner-serialized` |

### `host/native/admission-preallocation.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 11 | `fnn-account-preparation-admit` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |

### `host/native/auth-adoption-parked.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 23 | `fnn-native-auth-adopt-config` | `(fnn-owner-serialized-with-control-turn` |
| 44 | `fnn-native-auth-adopt-config` | `(fnn-owner-serialized-with-control-turn` |

### `host/native/auth.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 104 | `fnn-native-auth-install` | `(unless (eq (fnn-owner-serialized` |

### `host/native/bp-app.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 342 | `fnn-command-bp-app-receive` | `(sessions-lock (sb-thread:make-mutex :name "bp-app sessions")))` |
| 352 | `fnn-command-bp-app-receive` | `(sb-thread:with-mutex (sessions-lock)` |

### `host/native/bp-control.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 90 | `fnn-bpnc-execute` | `(fnn-owner-serialized` |
| 123 | `fnn-bpnc-handle` | `(fnn-with-control-buffer ()` |

### `host/native/consumer-remote.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 54 | `fnn-remote-ingress` | `(fnn-owner-serialized service nil` |
| 63 | `fnn-remote-installed-entry` | `(fnn-owner-serialized service nil` |
| 65 | `fnn-remote-installed-entry` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |

### `host/native/control-transport.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 10 | `fnn-control-state` | `(lock (sb-thread:make-mutex :name "fn local control"))` |
| 16 | `fnn-with-control` | `\`(sb-thread:with-mutex ((fnn-control-state-lock ,control)) ,@body))` |
| 19 | `*fnn-control-buffer-lock*` | `(sb-thread:make-mutex :name "fn local control buffer")` |
| 25 | `fnn-with-control-buffer` | `\`(sb-thread:with-mutex (*fnn-control-buffer-lock*) ,@body))` |

### `host/native/control.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 143 | `fnn-control-answering` | `(fnn-with-control (control)` |
| 169 | `fnn-control-live-status-legacy-answer` | `(fnn-owner-serialized` |
| 215 | `fnn-control-live-status-answer` | `(fnn-owner-serialized-with-control-turn` |
| 248 | `fnn-control-live-pages-answer` | `(fnn-owner-serialized` |
| 281 | `fnn-control-handle-client` | `(let ((d (fnn-with-control-buffer ()` |
| 434 | `fnn-control-client-done` | `(fnn-with-control (control)` |
| 438 | `fnn-control-client-done` | `(delete sb-thread:*current-thread*` |
| 443 | `fnn-control-launch-client` | `(fnn-with-control (control)` |
| 456 | `fnn-control-launch-client` | `(sb-thread:make-thread` |
| 477 | `fnn-control-accept-loop` | `(when (fnn-with-control (control)` |
| 485 | `fnn-control-accept-loop` | `(unless (fnn-with-control (control)` |
| 497 | `fnn-control-start` | `(fnn-owner-serialized` |
| 507 | `fnn-control-start` | `(let* ((bounds (fnn-owner-serialized` |
| 529 | `fnn-control-start` | `(sb-thread:make-thread` |
| 537 | `fnn-control-stop` | `(fnn-with-control (control)` |
| 558 | `fnn-control-close` | `(when accept-thread (sb-thread:join-thread accept-thread)))` |
| 561 | `fnn-control-close` | `(fnn-with-control (control)` |
| 564 | `fnn-control-close` | `(dolist (worker workers) (sb-thread:join-thread worker))))` |

### `host/native/crypto.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 34 | `*fnn-crypto-initialize-lock*` | `(sb-thread:make-mutex :name "fn native crypto initialization"))` |
| 111 | `fnn-crypto-initialize` | `(sb-thread:with-mutex (*fnn-crypto-initialize-lock*)` |
| 135 | `fnn-crypto-reset` | `(sb-thread:with-mutex (*fnn-crypto-initialize-lock*)` |

### `host/native/deflate.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 30 | `*fnn-deflate-lock*` | `(defvar *fnn-deflate-lock* (sb-thread:make-mutex :name "fn DEFLATE initialization"))` |
| 64 | `fnn-deflate-initialize` | `(sb-thread:with-mutex (*fnn-deflate-lock*)` |
| 93 | `fnn-deflate-reset` | `(sb-thread:with-mutex (*fnn-deflate-lock*)` |
| 532 | `*fnn-pzd-lock*` | `(defvar *fnn-pzd-lock* (sb-thread:make-mutex :name "fn payload decoder buffers"))` |
| 537 | `fnn-pzd-buffers` | `(or (sb-thread:with-mutex (*fnn-pzd-lock*) (pop *fnn-pzd-pool*))` |
| 560 | `fnn-pzd-decode` | `(sb-thread:with-mutex (*fnn-pzd-lock*)` |

### `host/native/digest.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 227 | `*fnn-digest-lock*` | `(defvar *fnn-digest-lock* (sb-thread:make-mutex :name "fn native digest"))` |
| 413 | `fnn-digest-reset` | `(sb-thread:with-mutex (*fnn-digest-lock*)` |
| 422 | `fnn-digest-initialize` | `(sb-thread:with-mutex (*fnn-digest-lock*)` |

### `host/native/extent.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 48 | `*fnn-extent-lock*` | `(defvar *fnn-extent-lock* (sb-thread:make-mutex :name "fn extent realizer"))` |
| 70 | `fnn-extent-pool-storage-start` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 91 | `fnn-extent-register` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 109 | `fnn-extent-register` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 118 | `fnn-extent-register` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 147 | `fnn-extent-register-at` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 224 | `fnn-extent-pool-open-context` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 232 | `fnn-extent-pool-funded-p` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 246 | `fnn-cold-worker` | `(ready (sb-thread:make-waitqueue :name "fn cold job")))` |
| 282 | `fnn-extent-window-run` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 298 | `fnn-extent-window-run` | `(unless (sb-thread:with-mutex (*fnn-extent-lock*)` |
| 332 | `fnn-extent-window-byte` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 350 | `fnn-extent-window-outcome` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 363 | `fnn-extent-window-byte-at` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 425 | `fnn-extent-window-release` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 441 | `fnn-extent-window-release` | `(sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))` |
| 449 | `fnn-extent-window-cancel` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 459 | `fnn-extent-window-settle-cancelled` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 475 | `fnn-extent-window-settle-cancelled` | `(sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))` |
| 504 | `fnn-extent-executor-job` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 512 | `fnn-extent-executor-loop` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 515 | `fnn-extent-executor-loop` | `(sb-thread:condition-wait (fnn-cold-worker-ready worker) *fnn-extent-lock*))` |
| 520 | `fnn-extent-executor-loop` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 522 | `fnn-extent-executor-loop` | `(sb-thread:condition-broadcast (fnn-cold-worker-ready worker)))))` |
| 534 | `fnn-extent-executor-start` | `(sb-thread:make-thread (lambda () (fnn-extent-executor-loop worker))` |
| 536 | `fnn-extent-executor-start` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 546 | `fnn-extent-executor-stop` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 558 | `fnn-extent-executor-stop` | `(sb-thread:condition-broadcast (fnn-cold-worker-ready worker))))` |
| 561 | `fnn-extent-executor-stop` | `(sb-thread:join-thread (fnn-cold-worker-thread worker) :default nil)))` |
| 564 | `fnn-extent-executor-stop` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 575 | `fnn-extent-executor-enqueue` | `(sb-thread:condition-broadcast (fnn-cold-worker-ready worker))` |
| 581 | `fnn-extent-issue-window` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 615 | `fnn-extent-executor-observe-returned` | `(not (sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))) :settle)` |
| 616 | `fnn-extent-executor-observe-returned` | `(sb-thread:join-thread (fnn-cold-worker-thread worker) :default nil)` |
| 624 | `fnn-extent-executor-returned-p` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 628 | `fnn-extent-executor-wait` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 630 | `fnn-extent-executor-wait` | `(sb-thread:condition-wait (fnn-cold-worker-ready worker) *fnn-extent-lock* :timeout seconds))))` |
| 644 | `fnn-extent-executor-commit` | `(sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))` |
| 756 | `fnn-extent-end-recovery-cache` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 892 | `fnn-extent-issue-read` | `(sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 915 | `fnn-extent-cancel-read` | `(sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 942 | `fnn-extent-prefetch` | `(sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 956 | `fnn-extent-prefetch` | `(sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 992 | `fnn-extent-issue-direct` | `(sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 1029 | `fnn-extent-direct-settle` | `(sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))` |
| 1043 | `fn-durable-realize-octet` | `(sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 1056 | `fn-durable-realize-octets` | `(sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 1089 | `fn-durable-realize-lz` | `(hit (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 1099 | `fn-durable-realize-lz` | `(let ((where (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 1106 | `fn-durable-realize-lz` | `(sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 1147 | `fn-pgs-fill-realize` | `(sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 1155 | `fn-pgs-fill-realize` | `(let ((path (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 1219 | `fnn-extent-ids-of-paths` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 1228 | `fnn-extent-close` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 1266 | `fnn-extent-open-count` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 1272 | `fnn-extent-stats-line` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |

### `host/native/feed-service.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 47 | `*fnn-feed-runtime-lock*` | `(sb-thread:make-mutex :name "fn outbound feed runtimes"))` |
| 56 | `fnn-feed-runtime-get` | `(sb-thread:with-mutex (*fnn-feed-runtime-lock*)` |
| 60 | `fnn-feed-runtime-put` | `(sb-thread:with-mutex (*fnn-feed-runtime-lock*)` |
| 65 | `fnn-feed-runtime-drop` | `(sb-thread:with-mutex (*fnn-feed-runtime-lock*)` |
| 70 | `fnn-feed-stoppingp` | `(sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))` |
| 74 | `fnn-feed-links` | `(sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))` |
| 93 | `fnn-feed-refresh-links` | `(sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))` |
| 341 | `fnn-feed-publish-socket` | `(sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))` |
| 355 | `fnn-feed-close-link` | `(sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))` |
| 592 | `fnn-feed-service-start` | `:lock (sb-thread:make-mutex :name "fn outbound feed runtime")` |
| 596 | `fnn-feed-service-start` | `(sb-thread:make-thread (lambda () (fnn-feed-worker-guarded runtime))` |
| 608 | `fnn-feed-service-wake` | `(sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))` |
| 621 | `fnn-feed-service-close` | `(when worker (sb-thread:join-thread worker)))` |

### `host/native/hybrid-control.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 6 | `fnn-hybrid-control-enroll` | `(fnn-owner-serialized` |
| 23 | `fnn-hybrid-control-revoke` | `(fnn-owner-serialized` |
| 42 | `fnn-hybrid-control-enroll-next` | `(fnn-owner-serialized` |
| 59 | `fnn-hybrid-control-revoke-next` | `(fnn-owner-serialized` |
| 76 | `fnn-hybrid-control-author` | `(fnn-owner-serialized` |

### `host/native/io.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 352 | `*fnn-trailing-stobjs*` | `(defvar *fnn-trailing-stobjs* (make-hash-table :test 'eq :synchronized t))` |
| 740 | `*fnn-random-state-lock*` | `(defvar *fnn-random-state-lock* (sb-thread:make-mutex :name "fn native random state"))` |
| 744 | `fnn-random-state` | `(sb-thread:with-mutex (*fnn-random-state-lock*)` |
| 863 | `*fnn-owner-log-mutex*` | `(defvar *fnn-owner-log-mutex* (sb-thread:make-mutex :name "fn service log"))` |
| 916 | `*fnn-log-queue-mutex*` | `(defvar *fnn-log-queue-mutex* (sb-thread:make-mutex :name "fn log queue"))` |
| 917 | `*fnn-log-queue-ready*` | `(defvar *fnn-log-queue-ready* (sb-thread:make-waitqueue :name "fn log queue ready"))` |
| 937 | `fnn-log-queue-push` | `(sb-thread:condition-notify *fnn-log-queue-ready*)))` |
| 948 | `fnn-log-offer` | `(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 971 | `fnn-log-sink-snapshot` | `(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 1049 | `fnn-log-writer-loop` | `(let ((item (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 1051 | `fnn-log-writer-loop` | `do (sb-thread:condition-wait *fnn-log-queue-ready*` |
| 1065 | `fnn-log-writer-loop` | `(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 1072 | `fnn-log-writer-start` | `(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 1078 | `fnn-log-writer-start` | `(sb-thread:make-thread #'fnn-log-writer-loop` |
| 1090 | `fnn-log-writer-stop` | `(let ((thread (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 1097 | `fnn-log-writer-stop` | `(sb-thread:join-thread thread` |
| 1104 | `fnn-log-writer-stop` | `(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 1113 | `fnn-log-swap-fd` | `(unless (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 1117 | `fnn-log-swap-fd` | `(sb-thread:with-recursive-lock (*fnn-owner-log-mutex*)` |
| 1142 | `fnn-log-line` | `(sb-thread:with-recursive-lock (*fnn-owner-log-mutex*)` |
| 1278 | `*fnn-entry-guard-specs*` | `(defvar *fnn-entry-guard-specs* (make-hash-table :test 'eq :synchronized t))` |
| 1320 | `fnn-cold-guard-cache-prepare` | `:rehash-size 1 :rehash-threshold 1.0 :synchronized t))` |
| 1556 | `*fnn-payload-lifecycle-lock*` | `(sb-thread:make-mutex :name "fn payload arena lifecycle"))` |
| 1567 | `fnn-payload-startup-reset` | `(sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)` |
| 6120 | `fnn-stack-exhaustion-report` | `(sb-thread:thread-name sb-thread:*current-thread*))` |
| 6184 | `fnn-lookup-counter` | `(sb-ext:atomic-incf (aref (the (simple-array sb-ext:word (*)) *fnn-lookup-counts*) i))` |
| 6190 | `fnn-lookup-walk-counter` | `(sb-ext:atomic-incf (aref counts i))` |
| 6193 | `fnn-lookup-walk-counter` | `(sb-ext:atomic-incf (aref counts len-i) (length walked)))))` |
| 6313 | `fnn-log` | `(lock (sb-thread:make-mutex :name "fn log kernel"))` |
| 6315 | `fnn-log` | `(sync-cv (sb-thread:make-waitqueue :name "fn log sync"))` |
| 6337 | `fnn-log` | `(spare nil) (spare-lock (sb-thread:make-mutex :name "fn log spare"))` |
| 6346 | `fnn-log-with-kernel` | `\`(sb-thread:with-recursive-lock ((fnn-log-lock ,log)) ,@body))` |
| 6726 | `fnn-log-prepare` | `(fnn-log-with-kernel (log)` |
| 6734 | `fnn-log-append` | `(fnn-log-with-kernel (log)` |
| 6768 | `*fnn-arena-pins-lock*` | `(defvar *fnn-arena-pins-lock* (sb-thread:make-mutex :name "fn arena pins")` |
| 6787 | `fnn-arena-pins-step` | `(sb-thread:with-mutex (*fnn-arena-pins-lock*)` |
| 6845 | `fnn-log-reseat-fenced` | `(let ((fenced (fnn-log-with-kernel (log)` |
| 6869 | `fnn-log-member-files` | `(fnn-log-with-kernel (log)` |
| 6895 | `fnn-log-fence` | `(fnn-log-with-kernel (log)` |
| 6899 | `fnn-log-fence` | `(fnn-log-with-kernel (log)` |
| 6908 | `fnn-log-finish` | `(fnn-log-with-kernel (log)` |
| 7299 | `fnn-log-prepare-spare` | `(sb-thread:with-mutex ((fnn-log-spare-lock log))` |
| 7543 | `fnn-log-committed-count` | `(fnn-core 'fn-lgc-count (fnn-log-with-kernel (log) (fnn-log-kernel log)))))` |
| 7554 | `fnn-log-read-active-segment` | `(ks (fnn-log-with-kernel (log) (fnn-log-kernel log)))` |
| 7800 | `fnn-log-reserve` | `(fnn-log-with-kernel (log)` |
| 7818 | `fnn-log-take` | `(when (eq (fnn-log-with-kernel (log) (fnn-core 'fn-lgc-phase (fnn-log-kernel log))) :fault)` |
| 7823 | `fnn-log-take` | `(fnn-log-with-kernel (log)` |
| 7892 | `fnn-log-commit-open-batch` | `(fnn-log-with-kernel (log)` |
| 7899 | `fnn-log-commit-open-batch` | `(fnn-log-with-kernel (log)` |
| 7986 | `fnn-log-ack` | `(fnn-log-with-kernel (log)` |
| 7994 | `fnn-log-batch-finish` | `(fnn-log-with-kernel (log)` |
| 8010 | `fnn-log-await-sync` | `(sb-thread:with-mutex ((fnn-log-lock log))` |
| 8012 | `fnn-log-await-sync` | `do (sb-thread:condition-wait (fnn-log-sync-cv log) (fnn-log-lock log)))` |
| 8032 | `fnn-log-seal-open-batch` | `(fnn-log-with-kernel (log)` |
| 8037 | `fnn-log-seal-open-batch` | `(fnn-log-with-kernel (log)` |
| 8063 | `fnn-log-sync-sealed-batch` | `(fnn-log-with-kernel (log)` |
| 8069 | `fnn-log-sync-sealed-batch` | `(sb-thread:with-mutex ((fnn-log-lock log))` |
| 8074 | `fnn-log-sync-sealed-batch` | `(sb-thread:condition-broadcast (fnn-log-sync-cv log)))` |
| 8079 | `fnn-log-sync-collected` | `(sb-thread:with-mutex ((fnn-log-lock log))` |
| 8578 | `fnn-main` | `(sb-sys:enable-interrupt sb-unix:sigpipe :ignore)` |
| 8581 | `fnn-main` | `(sb-sys:enable-interrupt sb-unix:sighup` |
| 8585 | `fnn-main` | `(sb-sys:enable-interrupt sb-unix:sigterm` |

### `host/native/keys.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 20 | `fnn-keys-owner-redecide` | `(fnn-owner-serialized` |

### `host/native/login-bindings.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 19 | `fnn-login-bindings-owner-reload` | `(fnn-owner-serialized` |

### `host/native/mux.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 72 | `fnn-mux-loop` | `(lock (sb-thread:make-mutex :name "fn mux inbox"))` |
| 250 | `fnn-mux-tls-log` | `(fnn-with-roster (service)` |
| 282 | `fnn-mux-finish` | `(fnn-owner-serialized` |
| 290 | `fnn-mux-finish` | `(fnn-owner-serialized` |
| 295 | `fnn-mux-finish` | `(fnn-owner-serialized` |
| 308 | `fnn-mux-finish` | `(fnn-with-roster (service)` |
| 313 | `fnn-mux-finish` | `(sb-thread:signal-semaphore (fnn-mux-conn-done conn)))` |
| 556 | `fnn-mux-install-compress` | `(fnn-owner-serialized` |
| 678 | `fnn-mux-await` | `(sb-thread:with-mutex ((fnn-mux-loop-lock loop))` |
| 776 | `fnn-mux-handshake-ask` | `(let ((answer (fnn-owner-serialized` |
| 793 | `fnn-mux-handshake-release` | `(fnn-owner-serialized` |
| 890 | `fnn-mux-handshake-step` | `(fnn-owner-serialized` |
| 949 | `fnn-mux-proxy-or-admit` | `(let ((path (fnn-owner-serialized` |
| 969 | `fnn-mux-proxy-expired` | `(let ((line (fnn-owner-serialized` |
| 992 | `fnn-mux-proxy-readable` | `(let ((r (fnn-owner-serialized` |
| 1010 | `fnn-mux-proxy-handover` | `(answer (fnn-owner-serialized` |
| 1046 | `fnn-mux-admit` | `(fnn-owner-serialized` |
| 1189 | `fnn-mux-take-inbox` | `(let ((new (sb-thread:with-mutex ((fnn-mux-loop-lock loop))` |
| 1213 | `fnn-mux-take-arrived` | `(let ((arrived (sb-thread:with-mutex ((fnn-mux-loop-lock loop))` |
| 1241 | `fnn-mux-iterate` | `(sb-thread:with-mutex ((fnn-mux-loop-lock loop))` |
| 1280 | `fnn-mux-iterate` | `(sb-thread:with-mutex ((fnn-mux-loop-lock loop))` |
| 1292 | `fnn-mux-unsent` | `sum (sb-thread:with-mutex ((fnn-mux-loop-lock loop))` |
| 1303 | `fnn-mux-signal-committer` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 1304 | `fnn-mux-signal-committer` | `(sb-thread:condition-broadcast (fnn-owner-service-commit-ready service))))))` |
| 1312 | `fnn-mux-stop-loop` | `(sb-thread:with-mutex ((fnn-mux-loop-lock loop))` |
| 1355 | `fnn-mux-run` | `(fnn-with-roster (service)` |
| 1357 | `fnn-mux-run` | `(delete sb-thread:*current-thread*` |
| 1362 | `fnn-mux-start` | `(fnn-with-roster (service)` |
| 1373 | `fnn-mux-start` | `(let ((thread (sb-thread:make-thread (lambda () (fnn-mux-run loop))` |
| 1382 | `fnn-mux-adopt` | `(fnn-with-roster (service)` |
| 1386 | `fnn-mux-adopt` | `(when done (sb-thread:signal-semaphore done)))` |
| 1393 | `fnn-mux-adopt` | `(sb-thread:with-mutex ((fnn-mux-loop-lock loop))` |
| 1408 | `fnn-mux-serve-once` | `(let ((done (sb-thread:make-semaphore :name "fn owner once")))` |
| 1410 | `fnn-mux-serve-once` | `(loop until (or (sb-thread:wait-on-semaphore done :timeout 1)` |
| 1446 | `fnn-mux-budget-install` | `(fnn-owner-serialized` |

### `host/native/operator-live.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 140 | `fnn-operator-execute-run` | `(sb-thread:with-recursive-lock (*fnn-owner-log-mutex*)` |

### `host/native/operator.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 261 | `fnn-operator-log-run-line` | `(sb-thread:with-recursive-lock (*fnn-owner-log-mutex*)` |

### `host/native/owner-control-turn.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 28 | `fnn-owner-control-fault` | `(sb-thread:with-recursive-lock (*fnn-extent-lock*)` |
| 33 | `fnn-owner-control-enter` | `(sb-thread:with-recursive-lock (*fnn-extent-lock*)` |
| 51 | `fnn-owner-control-finish` | `(sb-thread:with-recursive-lock (*fnn-extent-lock*)` |

### `host/native/owner.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 112 | `fnn-owner-service` | `(gate nil) (roster (sb-thread:make-mutex :name "fn owner roster"))` |
| 144 | `fnn-owner-service` | `(wait-lock (sb-thread:make-mutex :name "fn consumer wait"))` |
| 145 | `fnn-owner-service` | `(wait-queue (sb-thread:make-waitqueue :name "fn consumer commit"))` |
| 169 | `fnn-owner-service` | `(commit-lock (sb-thread:make-mutex :name "fn owner commit"))` |
| 170 | `fnn-owner-service` | `(commit-ready (sb-thread:make-waitqueue :name "fn owner commit ready"))` |
| 268 | `fnn-owner-signal-commit` | `(sb-thread:with-mutex ((fnn-owner-service-wait-lock service))` |
| 270 | `fnn-owner-signal-commit` | `(sb-thread:condition-broadcast (fnn-owner-service-wait-queue service))))` |
| 345 | `*fnn-owner-measure-table*` | `(make-hash-table :test 'eq :synchronized t))` |
| 504 | `fnn-owner-response-pin-step` | `(sb-thread:with-mutex (*fnn-arena-pins-lock*)` |
| 518 | `fnn-owner-cursor-step` | `(fnn-owner-serialized` |
| 648 | `fnn-owner-run-admission` | `(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 653 | `fnn-owner-claim-run-authority` | `(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 659 | `fnn-owner-claim-run-authority` | `(eq *fnn-owner-reserving-thread* sb-thread:*current-thread*)` |
| 664 | `fnn-owner-claim-run-authority` | `*fnn-owner-reserving-thread* sb-thread:*current-thread*` |
| 668 | `fnn-owner-retain-run-authority` | `(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 676 | `fnn-owner-store-settlement` | `(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 699 | `fnn-owner-store-settlement` | `(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 1209 | `fnn-owner-install` | `:lock (sb-thread:make-mutex :name "fn owner/store")` |
| 1246 | `fnn-with-roster` | `\`(sb-thread:with-mutex ((fnn-owner-service-roster ,service)) ,@body))` |
| 1257 | `fnn-owner-gate` | `(mutex (sb-thread:make-mutex :name "fn owner gate"))` |
| 1258 | `fnn-owner-gate` | `(ready (sb-thread:make-waitqueue :name "fn owner gate ready"))` |
| 1277 | `fnn-owner-gate-abort-locked` | `(sb-thread:condition-broadcast (fnn-owner-gate-ready gate)))` |
| 1280 | `fnn-owner-gate-abort` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1284 | `fnn-owner-gate-check` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1328 | `fnn-owner-gate-pick` | `(sb-thread:condition-broadcast (fnn-owner-gate-ready gate))))` |
| 1336 | `fnn-owner-gate-enter` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1342 | `fnn-owner-gate-enter` | `(when (eq (fnn-owner-gate-holder gate) sb-thread:*current-thread*)` |
| 1357 | `fnn-owner-gate-enter` | `(fnn-owner-gate-holder gate) sb-thread:*current-thread*` |
| 1362 | `fnn-owner-gate-enter` | `(sb-thread:condition-wait (fnn-owner-gate-ready gate)` |
| 1372 | `fnn-owner-gate-leave` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1426 | `fnn-owner-space-prime` | `(fnn-owner-serialized service nil` |
| 1438 | `fnn-owner-sched-snapshot` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1457 | `fnn-owner-disk-event` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1484 | `fnn-owner-journal-note` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1496 | `fnn-owner-disk-admission` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1507 | `fnn-owner-gate-sched-value` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1519 | `fnn-owner-peer-read-class` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1531 | `fnn-owner-disk-stalled-p` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1539 | `fnn-owner-disk-wait-ms` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1566 | `fnn-owner-shed-queued-locked` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 1590 | `fnn-owner-gated` | `(sb-thread:with-mutex ((fnn-owner-service-lock ,s))` |
| 1593 | `fnn-owner-gated` | `(sb-thread:with-mutex ((fnn-owner-service-lock ,s))` |
| 1612 | `fnn-payload-lifecycle-recover` | `(sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)` |
| 1624 | `fnn-payload-lifecycle-start` | `(sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)` |
| 1637 | `fnn-payload-lifecycle-drain` | `(sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)` |
| 1645 | `fnn-payload-lifecycle-joined` | `(sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)` |
| 1655 | `fnn-snapshot-payload-view-acquire` | `(sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)` |
| 1672 | `fnn-snapshot-payload-view-live-p` | `(sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)` |
| 1680 | `fnn-snapshot-payload-view-release` | `(sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)` |
| 1703 | `fnn-owner-stop-service-locked` | `(fnn-with-roster (service)` |
| 1711 | `fnn-owner-stop-service-locked` | `(let ((sparing (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 1726 | `fnn-owner-stop-service-locked` | `(dolist (socket (fnn-with-roster (service)` |
| 1732 | `fnn-owner-stop-service-locked` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 1733 | `fnn-owner-stop-service-locked` | `(sb-thread:condition-broadcast (fnn-owner-service-commit-ready service)))` |
| 1746 | `fnn-owner-stop-service` | `(sb-thread:with-mutex ((fnn-owner-service-lock service))` |
| 1764 | `fnn-owner-fault-service` | `(fnn-owner-gated (service :control)` |
| 1821 | `fnn-owner-serialized` | `(fnn-owner-gated (service class)` |
| 1836 | `fnn-owner-serialized-with-control-turn` | `(fnn-owner-gated (service class)` |
| 1872 | `fnn-owner-transit-serialized` | `(fnn-owner-serialized service cid thunk :transit))` |
| 1876 | `fnn-owner-consume-connection-fault` | `(fnn-with-roster (service)` |
| 1907 | `fnn-owner-abandon-connection` | `(fnn-owner-gated (service :control)` |
| 2635 | `fnn-owner-topic-local-serialized` | `(fnn-owner-serialized` |
| 2679 | `fnn-owner-consumer-local-serialized` | `(fnn-owner-serialized` |
| 2812 | `fnn-owner-consumer-local-wait` | `(fnn-owner-serialized` |
| 2815 | `fnn-owner-consumer-local-wait` | `(sb-thread:with-mutex (lock)` |
| 2831 | `fnn-owner-consumer-local-wait` | `(let* ((seen (sb-thread:with-mutex (lock)` |
| 2833 | `fnn-owner-consumer-local-wait` | `(step (fnn-owner-serialized` |
| 2847 | `fnn-owner-consumer-local-wait` | `(sb-thread:grab-mutex lock)` |
| 2850 | `fnn-owner-consumer-local-wait` | `(sb-thread:condition-wait queue lock` |
| 2853 | `fnn-owner-consumer-local-wait` | `(when (sb-thread:holding-mutex-p lock)` |
| 2854 | `fnn-owner-consumer-local-wait` | `(sb-thread:release-mutex lock)))))` |
| 2856 | `fnn-owner-consumer-local-wait` | `(sb-thread:with-mutex (lock)` |
| 3020 | `fnn-owner-note-queued` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 3022 | `fnn-owner-note-queued` | `(sb-thread:condition-notify (fnn-owner-service-commit-ready service))))` |
| 3035 | `fnn-owner-deliver` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 3046 | `fnn-owner-take-done` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 3054 | `fnn-owner-awaiting-sockets` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 3062 | `fnn-owner-await-register` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 3088 | `fnn-owner-commit-start-locked` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 3133 | `fnn-owner-commit-start-locked` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 3239 | `fnn-owner-commit-complete-locked` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 3306 | `fnn-owner-commit-event` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 3324 | `fnn-owner-commit-wake` | `(sb-thread:with-mutex ((fnn-owner-gate-mutex gate))` |
| 3342 | `fnn-owner-start-syncer` | `(fnn-with-roster (service)` |
| 3344 | `fnn-owner-start-syncer` | `(sb-thread:make-thread` |
| 3352 | `fnn-owner-start-syncer` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 3354 | `fnn-owner-start-syncer` | `(sb-thread:condition-notify (fnn-owner-service-commit-ready service))))` |
| 3355 | `fnn-owner-start-syncer` | `(fnn-with-roster (service)` |
| 3357 | `fnn-owner-start-syncer` | `(delete sb-thread:*current-thread*` |
| 3427 | `fnn-owner-commit-pipeline` | `(fnn-owner-serialized` |
| 3478 | `fnn-owner-commit-pipeline` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 3491 | `fnn-owner-commit-pipeline` | `(sb-thread:condition-wait (fnn-owner-service-commit-ready service)` |
| 3494 | `fnn-owner-commit-pipeline` | `(sb-thread:condition-wait (fnn-owner-service-commit-ready service)` |
| 3521 | `fnn-owner-commit-pipeline` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 3529 | `fnn-owner-commit-pipeline` | `(fnn-owner-gated (service :reader)` |
| 3542 | `fnn-owner-commit-pipeline` | `(fnn-owner-gated (service :commit)` |
| 3582 | `fnn-owner-commit-pipeline` | `(sb-thread:join-thread syncer :default nil)` |
| 3594 | `fnn-owner-commit-pipeline` | `(fnn-owner-gated (service :commit)` |
| 3692 | `fnn-owner-committer-loop` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 3695 | `fnn-owner-committer-loop` | `do (sb-thread:condition-wait (fnn-owner-service-commit-ready service)` |
| 3700 | `fnn-owner-committer-loop` | `do (sb-thread:condition-wait (fnn-owner-service-commit-ready service)` |
| 3714 | `fnn-owner-start-committer` | `(sb-thread:make-thread (lambda () (fnn-owner-committer-loop service))` |
| 3969 | `fnn-owner-moderation-serialized` | `(let ((plan (fnn-owner-serialized` |
| 4007 | `fnn-owner-control-submit-serialized` | `(fnn-owner-serialized` |
| 4081 | `fnn-owner-redeem-quantum` | `(fnn-owner-serialized` |
| 4276 | `fnn-owner-cold-result-locked` | `(sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 4312 | `fnn-owner-cold-ready-p` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 4324 | `fnn-owner-cold-settle` | `(fnn-owner-serialized service nil` |
| 4335 | `fnn-owner-cold-reap` | `(fnn-owner-serialized` |
| 4358 | `fnn-owner-cold-shutdown` | `(sb-thread:with-mutex ((fnn-owner-service-lock service))` |
| 4408 | `fnn-owner-unavailable-line` | `(fnn-owner-serialized` |
| 4431 | `fnn-owner-resource-unavailable-line` | `(fnn-owner-serialized` |
| 4472 | `fnn-owner-handle-chunk-read` | `(fnn-owner-serialized` |
| 4639 | `fnn-owner-exposure-idle` | `(let ((answer (fnn-owner-serialized` |
| 4720 | `fnn-owner-retire-begin` | `(fnn-with-roster (service)` |
| 4769 | `fnn-owner-maybe-retire` | `(fnn-owner-serialized` |
| 4794 | `fnn-owner-log-settlement` | `(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 4808 | `fnn-owner-wait-workers` | `(fnn-with-roster (service)` |
| 4811 | `fnn-owner-wait-workers` | `(dolist (worker workers) (sb-thread:join-thread worker)))))` |
| 4864 | `fnn-owner-release-pending-extents` | `(fnn-owner-gated (service :control)` |
| 4872 | `fnn-snapshot-source-root-acquire` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 4884 | `fnn-snapshot-source-root-release` | `(sb-thread:with-mutex ((fnn-owner-service-lock service))` |
| 4885 | `fnn-snapshot-source-root-release` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 4897 | `fnn-snapshot-source-read-page` | `(fnn-owner-gated (service :control)` |
| 4898 | `fnn-snapshot-source-read-page` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 4917 | `fnn-snapshot-source-read-page` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 4922 | `fnn-snapshot-source-page-release` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 4948 | `fnn-owner-release-extents` | `(fnn-owner-gated (service :control)` |
| 4964 | `fnn-owner-release-extents` | `(sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 4967 | `fnn-owner-release-extents` | `(fnn-owner-gated (service :control)` |
| 4979 | `fnn-owner-release-extents` | `(sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)` |
| 4981 | `fnn-owner-release-extents` | `(fnn-owner-gated (service :control)` |
| 5135 | `fnn-owner-publish-captured` | `(fnn-owner-gated (service :control)` |
| 5147 | `fnn-owner-publish-captured` | `(fnn-with-roster (service)` |
| 5150 | `fnn-owner-publish-captured` | `(delete sb-thread:*current-thread*` |
| 5212 | `fnn-owner-maybe-publish-quantum` | `(fnn-owner-gated (service :control)` |
| 5214 | `fnn-owner-maybe-publish-quantum` | `(fnn-with-roster (service) (fnn-owner-service-publisher service)))` |
| 5253 | `fnn-owner-maybe-publish-quantum` | `(fnn-with-roster (service)` |
| 5257 | `fnn-owner-maybe-publish-quantum` | `(setq made (sb-thread:make-thread` |
| 5264 | `fnn-owner-maybe-publish-quantum` | `(fnn-with-roster (service)` |
| 5295 | `fnn-owner-export-observation` | `(fnn-with-roster (service)` |
| 5304 | `fnn-owner-export-start` | `(fnn-with-roster (service)` |
| 5307 | `fnn-owner-export-start` | `(setq made (sb-thread:make-thread` |
| 5311 | `fnn-owner-export-start` | `(fnn-with-roster (service)` |
| 5408 | `fnn-owner-export-captured` | `(fnn-with-roster (service)` |
| 5413 | `fnn-owner-export-captured` | `(delete sb-thread:*current-thread*` |
| 5465 | `fnn-owner-reclaim-dry-run` | `(fnn-owner-gated (service :control)` |
| 5506 | `fnn-owner-reclaim-dry-run` | `(fnn-owner-gated (service :control)` |
| 5593 | `fnn-owner-reclaim-intern` | `(done (fnn-owner-gated (service :control)` |
| 5651 | `fnn-owner-reclaim-pass` | `(fnn-owner-gated (service :control)` |
| 5745 | `fnn-owner-reclaim-pass` | `(let ((sw (fnn-owner-gated (service :control)` |
| 5777 | `fnn-owner-reclaim-pass` | `(sb-thread:thread-yield))` |
| 5797 | `fnn-owner-reclaim-pass` | `(fnn-owner-gated (service :control)` |
| 5830 | `fnn-owner-journal-open` | `(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)` |
| 5906 | `fnn-owner-maybe-reopen-log` | `(let ((decision (fnn-owner-serialized` |
| 5932 | `fnn-owner-start-tls-accept` | `(fnn-with-roster (service)` |
| 5934 | `fnn-owner-start-tls-accept` | `(sb-thread:make-thread` |
| 5949 | `fnn-owner-start-tls-accept` | `(fnn-with-roster (service)` |
| 5951 | `fnn-owner-start-tls-accept` | `(delete sb-thread:*current-thread*` |
| 6001 | `fnn-owner-drain-observation` | `(list (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 6018 | `fnn-owner-drain-service` | `(fnn-owner-serialized` |
| 6050 | `fnn-owner-drain-service` | `(sb-thread:with-mutex ((fnn-owner-service-commit-lock service))` |
| 6052 | `fnn-owner-drain-service` | `(sb-thread:condition-broadcast (fnn-owner-service-commit-ready service))))` |
| 6120 | `fnn-owner-run` | `(sb-thread:with-mutex ((fnn-owner-service-lock service))` |
| 6146 | `fnn-owner-run` | `do (sb-thread:thread-yield)))` |
| 6217 | `fnn-owner-run` | `(ignore-errors (sb-thread:join-thread committer :default nil))))` |
| 6221 | `fnn-owner-run` | `(when (or (null worker) (not (sb-thread:thread-alive-p worker)))` |
| 6243 | `fnn-owner-run` | `(when (fnn-with-roster (service)` |
| 6251 | `fnn-owner-run` | `(not (sb-thread:thread-alive-p worker)))))` |
| 6255 | `fnn-owner-run` | `(when (and worker (sb-thread:thread-alive-p worker))` |
| 6260 | `fnn-owner-run` | `(null (fnn-with-roster (service)` |
| 6266 | `fnn-owner-run` | `(not (sb-thread:thread-alive-p worker)))))` |
| 6269 | `fnn-owner-run` | `(or (null worker) (not (sb-thread:thread-alive-p worker)))))` |
| 6284 | `fnn-owner-run` | `(sb-thread:with-mutex ((fnn-owner-service-lock service))` |

### `host/native/peer-invite.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 98 | `fnn-pinv-owner-issue` | `(fnn-owner-serialized` |
| 123 | `fnn-pinv-owner-accept` | `(fnn-owner-serialized` |
| 199 | `fnn-pinv-owner-confirm` | `(fnn-owner-serialized` |

### `host/native/post-captured-parked.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 32 | `fnn-owner-pic-runtime-install-locked` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 69 | `fnn-owner-captured-precheck-locked` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |

### `host/native/pull-service.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 48 | `*fnn-pull-runtime-lock*` | `(defparameter *fnn-pull-runtime-lock* (sb-thread:make-mutex :name "fn pull runtimes"))` |
| 53 | `fnn-pull-runtime-get` | `(sb-thread:with-mutex (*fnn-pull-runtime-lock*) (gethash service *fnn-pull-runtimes*)))` |
| 56 | `fnn-pull-stoppingp` | `(sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))` |
| 357 | `fnn-pull-round` | `(sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))` |
| 449 | `fnn-pull-round` | `(sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))` |
| 564 | `fnn-pull-service-start` | `:lock (sb-thread:make-mutex :name "fn pull runtime"))))` |
| 565 | `fnn-pull-service-start` | `(sb-thread:with-mutex (*fnn-pull-runtime-lock*)` |
| 568 | `fnn-pull-service-start` | `(sb-thread:make-thread (lambda () (fnn-pull-worker-guarded runtime))` |
| 575 | `fnn-pull-service-wake` | `(sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))` |
| 586 | `fnn-pull-service-close` | `(when worker (sb-thread:join-thread worker)))` |
| 587 | `fnn-pull-service-close` | `(sb-thread:with-mutex (*fnn-pull-runtime-lock*)` |

### `host/native/receiver-parser-turn.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 20 | `fnn-owner-receiver-turn-parser-locked` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |

### `host/native/receiver-turn-parked.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 38 | `fnn-owner-connection-open-locked` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 153 | `fnn-owner-receiver-startup` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 193 | `fnn-owner-receiver-current-startup` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 272 | `fnn-owner-receiver-turn-copy` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 311 | `fnn-owner-receiver-turn-start` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 354 | `fnn-owner-receiver-fill` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 402 | `fnn-owner-admission-input-action` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 452 | `fnn-owner-connection-settle-locked` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 483 | `fnn-owner-connection-close-locked` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |

### `host/native/recovery-payload-view.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 5 | `fnn-snapshot-recovery-payload-view-acquire` | `(sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)` |
| 20 | `fnn-snapshot-recovery-payload-view-live-p` | `(sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)` |
| 29 | `fnn-snapshot-recovery-payload-view-release` | `(sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)` |
| 47 | `fnn-snapshot-recovery-root-acquire` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |
| 58 | `fnn-snapshot-recovery-root-release` | `(sb-thread:with-mutex ((fnn-owner-service-lock service))` |
| 59 | `fnn-snapshot-recovery-root-release` | `(sb-thread:with-mutex (*fnn-extent-lock*)` |

### `host/native/runtime-collector.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 34 | `fnn-runtime-geometry-into` | `(sb-sys:without-interrupts` |

### `host/native/runtime-image-policy.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 31 | `fnn-runtime-image-policy-source-quiet-p` | `(or (eq thread sb-thread:*current-thread*)` |
| 33 | `fnn-runtime-image-policy-source-quiet-p` | `(sb-thread:list-all-threads))))` |
| 47 | `fnn-runtime-image-policy-restore` | `(sb-sys:enable-interrupt signal :default))` |

### `host/native/runtime-participants.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 7 | `fnn-runtime-participants` | `(lock (sb-thread:make-mutex :name "runtime-participants"))` |
| 8 | `fnn-runtime-participants` | `(changed (sb-thread:make-waitqueue :name "runtime-participants"))` |
| 19 | `fnn-runtime-finalizer-entry` | `(sb-thread:with-mutex ((fnn-runtime-participants-lock gate))` |
| 21 | `fnn-runtime-finalizer-entry` | `(sb-thread:condition-broadcast (fnn-runtime-participants-changed gate))` |
| 23 | `fnn-runtime-finalizer-entry` | `do (sb-thread:condition-wait` |
| 33 | `fnn-runtime-finalizer-stop-entry` | `(sb-thread:with-mutex ((fnn-runtime-participants-lock gate))` |
| 37 | `fnn-runtime-finalizer-stop-entry` | `(sb-thread:condition-broadcast (fnn-runtime-participants-changed gate)))` |
| 48 | `fnn-runtime-participants-install-for-image` | `(sb-thread::with-system-mutex (sb-thread::*make-thread-lock*)` |
| 64 | `fnn-with-runtime-participants-parked` | `(eq sb-thread:*current-thread* sb-impl::*finalizer-thread*)` |
| 65 | `fnn-with-runtime-participants-parked` | `(eq sb-thread:*current-thread*` |
| 68 | `fnn-with-runtime-participants-parked` | `(sb-thread:with-mutex ((fnn-runtime-participants-lock ,g))` |
| 82 | `fnn-with-runtime-participants-parked` | `(sb-thread:condition-wait` |
| 95 | `fnn-with-runtime-participants-bootstrap` | `\`(sb-sys:without-interrupts` |
| 100 | `fnn-with-runtime-participants-bootstrap` | `(when (or (sb-thread:holding-mutex-p` |
| 103 | `fnn-with-runtime-participants-bootstrap` | `(eq sb-thread:*current-thread* sb-impl::*finalizer-thread*)` |
| 104 | `fnn-with-runtime-participants-bootstrap` | `(eq sb-thread:*current-thread*` |
| 107 | `fnn-with-runtime-participants-bootstrap` | `(sb-thread:with-mutex ((fnn-runtime-participants-lock ,g) :wait-p nil)` |
| 125 | `fnn-runtime-participants-stop-and-join` | `(sb-thread:with-mutex ((fnn-runtime-participants-lock gate))` |
| 129 | `fnn-runtime-participants-stop-and-join` | `(sb-thread:condition-broadcast (fnn-runtime-participants-changed gate)))` |
| 130 | `fnn-runtime-participants-stop-and-join` | `(sb-thread::with-system-mutex (sb-thread::*make-thread-lock*)` |
| 150 | `fnn-runtime-participant-cleanup-one` | `(sb-thread:with-mutex ((fnn-runtime-participants-lock gate))` |
| 157 | `fnn-runtime-participant-cleanup-one` | `(fnn-runtime-participants-active-owner gate) sb-thread:*current-thread*))` |
| 181 | `fnn-runtime-participant-cleanup-one` | `(sb-thread:with-mutex ((fnn-runtime-participants-lock gate))` |
| 189 | `fnn-runtime-participant-cleanup-one` | `(sb-thread:with-mutex ((fnn-runtime-participants-lock gate))` |
| 193 | `fnn-runtime-participant-cleanup-one` | `(sb-thread:with-mutex ((fnn-runtime-participants-lock gate))` |
| 196 | `fnn-runtime-participant-cleanup-one` | `(sb-thread:condition-broadcast` |
| 203 | `fnn-runtime-participants-save-hook` | `(sb-thread:with-mutex ((fnn-runtime-participants-lock gate))` |
| 207 | `fnn-runtime-participants-save-hook` | `(sb-thread:condition-broadcast (fnn-runtime-participants-changed gate)))))` |

### `host/native/runtime-recovery-file.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 73 | `fnn-recovery-profile-start` | `(sb-thread:with-recursive-lock (*fnn-extent-lock*)` |
| 114 | `fnn-recovery-profile-next` | `(sb-thread:with-recursive-lock (*fnn-extent-lock*)` |

### `host/native/signatures.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 39 | `*fnn-hsig-mldsa-lock*` | `(sb-thread:make-mutex :name "fn ML-DSA-65 initialization"))` |
| 127 | `fnn-hsig-mldsa-initialize` | `(sb-thread:with-mutex (*fnn-hsig-mldsa-lock*)` |
| 150 | `fnn-hsig-reset` | `(sb-thread:with-mutex (*fnn-hsig-mldsa-lock*)` |

### `host/native/snapshot-producer.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 11 | `fnn-snapshot-job` | `(action-lock (sb-thread:make-mutex :name "snapshot action"))` |
| 43 | `fnn-snapshot-recovery-census-step` | `(sb-thread:with-mutex ((fnn-snapshot-job-action-lock job))` |
| 45 | `fnn-snapshot-recovery-census-step` | `(current (sb-thread:with-mutex ((fnn-owner-service-lock service))` |
| 60 | `fnn-snapshot-recovery-census-step` | `(sb-thread:with-mutex ((fnn-owner-service-lock service))` |
| 113 | `%fnn-snapshot-job-row-step` | `(sb-thread:with-mutex` |
| 119 | `%fnn-snapshot-job-row-step` | `(sb-thread:with-mutex` |
| 287 | `%fnn-snapshot-job-emission-step` | `(word (sb-thread:with-mutex (*fnn-extent-lock*)` |
| 424 | `fnn-snapshot-job-restart-source` | `(sb-thread:with-mutex ((fnn-snapshot-job-action-lock job))` |
| 432 | `fnn-snapshot-job-source-step` | `(sb-thread:with-mutex ((fnn-snapshot-job-action-lock job))` |
| 485 | `fnn-snapshot-job-cleanup` | `(sb-thread:with-mutex ((fnn-snapshot-job-action-lock job))` |
| 494 | `fnn-snapshot-job-cleanup` | `(sb-thread:with-mutex ((fnn-owner-service-lock service))` |
| 533 | `fnn-snapshot-job-freeze-log` | `(fnn-log-with-kernel (log) (fnn-log-rotate store))` |
| 551 | `fnn-snapshot-job-log-durable` | `(sb-thread:with-mutex ((fnn-snapshot-job-action-lock job))` |
| 579 | `fnn-owner-snapshot-capture` | `(fnn-owner-gated (service :control)` |
| 591 | `fnn-owner-snapshot-capture` | `(unless (fnn-log-with-kernel (log)` |
| 627 | `fnn-owner-snapshot-capture` | `(sb-thread:with-mutex ((fnn-owner-service-lock service))` |

### `host/native/snapshot-startup.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 58 | `fnn-snapshot-startup-open` | `(sb-thread:with-mutex ((fnn-owner-service-lock service))` |
| 130 | `fnn-snapshot-startup-measure` | `(sb-thread:with-mutex ((fnn-owner-service-lock service))` |
| 145 | `fnn-snapshot-startup-measure` | `(sb-thread:thread-yield)))` |

### `host/native/tcpcl.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 505 | `fnn-tcl-session` | `(sb-thread:thread-yield))` |
| 508 | `fnn-tcl-session` | `(sb-thread:thread-yield))` |

### `host/native/tls-reload.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 18 | `*fnn-tls-reload-mutex*` | `(defvar *fnn-tls-reload-mutex* (sb-thread:make-mutex :name "fn tls reload")` |
| 64 | `fnn-tls-served-facts` | `(sb-thread:with-mutex ((fnn-tls-context-lock context))` |
| 72 | `fnn-tls-owner-reload` | `(sb-thread:with-mutex (*fnn-tls-reload-mutex*)` |

### `host/native/tls.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 66 | `fnn-tls-context` | `(lock (sb-thread:make-mutex :name "fn native TLS context"))` |
| 77 | `*fnn-tls-initialize-lock*` | `(sb-thread:make-mutex :name "fn native TLS initialization"))` |
| 323 | `fnn-tls-initialize` | `(sb-thread:with-mutex (*fnn-tls-initialize-lock*)` |
| 358 | `fnn-tls-reset` | `(sb-thread:with-mutex (*fnn-tls-initialize-lock*)` |
| 488 | `fnn-tls-context-swap` | `(sb-thread:with-mutex ((fnn-tls-context-lock context))` |
| 588 | `fnn-tls-close-context` | `(sb-thread:with-mutex ((fnn-tls-context-lock context))` |
| 628 | `fnn-tls-accept` | `(sb-thread:with-mutex ((fnn-tls-context-lock context))` |
| 749 | `fnn-tls-accept-begin` | `(sb-thread:with-mutex ((fnn-tls-context-lock context))` |

### `host/native/web-host.lisp`

| Line | Nearest declaration | Quoted source |
|---:|---|---|
| 77 | `fnn-web-open` | `(fnn-owner-serialized` |
| 96 | `fnn-web-open` | `(fnn-owner-serialized` |
| 136 | `fnn-web-close` | `(fnn-owner-serialized service cid (lambda () (fnn-owner-action 'fn-owner-close cid)) :reader))` |
| 138 | `fnn-web-close` | `(fnn-owner-serialized service nil` |
| 241 | `fnn-web-request` | `(fnn-owner-serialized` |
| 310 | `fnn-web-start` | `(fnn-with-roster (service)` |
| 312 | `fnn-web-start` | `(sb-thread:make-thread` |
| 327 | `fnn-web-start` | `(fnn-with-roster (service)` |
| 329 | `fnn-web-start` | `(delete sb-thread:*current-thread*` |

Census: 521 source lines with matching synchronization/coordination constructs. This count is intentionally broader than the 231 explicit acquisition sites in §7 and is not a runtime operation count.

## Appendix C. Central-file GC/FFI pin scopes

These are additional physical-pointer scopes, not mutex acquisitions; they are excluded from the 231 count. Original source is quoted. Lifetime across thread/lock boundaries still needs the capabilities in §3.5.

| File:line | Quoted scope |
|---|---|
| `host/native/io.lisp:506` | `(sb-sys:with-pinned-objects (buffer)` |
| `host/native/io.lisp:5748` | `(sb-sys:with-pinned-objects (buf)` |
| `host/native/extent.lisp:161` | `(let ((got (sb-sys:with-pinned-objects (octets)` |
| `host/native/extent.lisp:264` | `(got (sb-sys:with-pinned-objects (octets)` |
| `host/native/mux.lisp:150` | `(sb-sys:with-pinned-objects (buf)` |
| `host/native/mux.lisp:227` | `(sb-sys:with-pinned-objects (one)` |
| `host/native/mux.lisp:234` | `(sb-sys:with-pinned-objects (buffer)` |

---

# Round 2: Astra's reconciliation with the COMPOSITION deputy's answer (same session, after delivery; verbatim)

# w01 reconciliation: one lock-discipline check, then a connected host model

Source: `4aa332295c85f03f5a97d7b0ac2228f9b95ab1e9`. A = `ANSWER.md`; D = the supplied `DEPUTY.md` copy. This round changes my position where stated; A remains unchanged. No implementation, certification, native test or tracked edit was performed. Historical finding IDs not established by the supplied material are labelled UNVERIFIED.

## 1. AGREE

- **Diagnosis:** useful serial, snapshot, resource and crash proofs exist; their concrete host transfers are not composed. A §§1,4; D §§0,1a. “No concurrency model” is too broad: the missing object is the composition with native actors.
- **Top-level statement:** an executable concurrent machine, forward simulation to a snapshot-aware reference, resource lifetime safety and crash refinement; progress is separate. A §5; D §3 T1–T3.
- **Trusted base:** logical certificates do not prove SBCL, FFI, disk, TLS or the source-to-image relationship; these need named, scoped assumptions and qualification. A §§2,5.4,8; D §§1b,5.
- **Path:** reuse the existing owner, reader-view, issued-read, response-pin, generation and crash books; one checked/generated coordination interface and a model-driven harness. A §§6–7; D §§4,6.2.
- **First practical artifact:** ONE `tools/lock_discipline_check.py`, with declared scope and reproducible findings; it must neither call Lisp's evaluator nor claim that zero unbaselined findings proves concurrency safety. A §7; D §6.1, reconciled below.

## 2. DIFFER: decisions and their evidence

### D1. First landing — I ADOPT THE DEPUTY'S, with a bounded claim

D §6 puts the checker first; A §6.1 puts the live adopt/stop protocol first. I accept t41 first because even the current explicit scopes can be checked without inventing a complete scheduler. `tools/ledger.py:4–8` already supplies a non-evaluating reader; `owner.lisp:4849–4852` explicitly requires owner-before-extent, and `extent.lisp:1145–1153` exposes the missing local lease contract.
The first landing must include positive/negative structural fixtures and actual findings, especially r31 F1's pattern. It does not establish “T2 on every handwritten line today” (D §6 table). Unknown callbacks, macros and aliases remain enumerated unresolved obligations. The live handoff/fault fixes follow immediately; a large baseline must not become the destination.

### D2. Top theorem and linearization — I HOLD MINE, while adopting the owner's section order

D §3(a) equates bytes written at every schedule with replies emitted by its sections; A §5 allows partial output and pending continuations. `mux.lisp:433–469` retains a partially written window, and `:503–513` releases the response only after all windows drain. A schedule stopping after a read section but before its first write refutes literal equality to all generated reply bytes.
Use the mutation sections' actual order as the reference mutation order, with pin acquisition and command/continuation identities fixed in that order; compare the **emitted prefix** plus retained output state, not the complete planned reply. Snapshot-aware reference state makes pinned reads compatible with linearizability of that interface. Not every command has one section, and direct stop/startup sections are not ordinary gate admissions (`owner:1746,6120`).
D's failed-label “refused no-op (the host faults there)” conflates two outcomes: an invalid actor action must be disabled or take an explicit fault/fence transition. `io.lisp:75–91` distinguishes faults, refusals and indeterminate conditions. Crash labels must cover all abstract effect prefixes, with a map to named cuts, rather than assume physical death occurs only at instrumented cuts (A §5.2; `specs/failures.md:65–79`).

### D3. Progress and deadline outcomes — NEITHER, PROPOSE scoped progress contracts

D T3 says every request is answered or refused within its deadline under fairness; A §5.3 separates liveness but did not spell out the counterexamples sufficiently. `owner.lisp:3467–3495` retains an in-flight barrier while waiting; `extent.lisp:449–475` distinguishes cancellation from physical return. Fair scheduling alone bounds neither fsync nor client drain, and a deadline can yield uncertain/unavailable, not known refusal.
State: deadline **observation** and named posture/outcome are bounded under a clock-observation/dispatch bound; physical settlement requires an I/O-return assumption. Reclaim progress additionally requires conflicting holds to end, or a specified cancellation/continuation-transfer policy. Bounded deferral is already meaningful progress; it is not successful swap progress.

### D4. Host-is-model assumption — I HOLD MINE

D §5 proposes A-HOST-IS-THE-MODEL backed by lint/load/native evidence; A §§5.4,7 decomposes the realization obligation. Keep an explicit *unproved correspondence claim*, but do not use a broad assumption that already asserts the desired coordination correctness as the final assurance result. Source identity plus a lock lint does not establish correct result installation, error arms or effect receipts.
`native_program_check.py:34–43` explicitly cannot decide runtime control flow/callbacks; `def-carried.lisp:22–27` instead generates actual proof obligations. Generate the coordination skeleton and prove its abstract obligations; retain narrowly named runtime/I/O assumptions and check remaining handwritten bindings. Qualification is evidence, not a proof of all schedules.

### D5. R1, mixed callers and “caller holds” — NEITHER, PROPOSE contextual contracts

D §6.1 classifies whole functions SECTION/OFF-LOCK/BOTH and lets a “caller holds” docstring resolve BOTH; A §7 requires declared effects/capabilities. A docstring cannot discharge callers: it is a precondition each call site must satisfy. `io.lisp:6784–6805` legally uses the pin ledger outside O under A, and `extent.lisp:197,330–363` uses private/E-protected stobjs outside O.
R1 therefore tracks **which** state region, mutex, phase and capability apply at each call. `fnn-core-state` or a live-stobj getter is not automatically “must hold O”: recovery-exclusive, E-protected, L-protected and worker-private instances need distinct contracts. A pin authorizes specified reads, never arbitrary mutation. Comments seed declarations but cannot silently exempt an unresolved caller.

### D6. R2 and R6 — NEITHER, PROPOSE effect-sensitive boundaries

Adopt D's R2 closure through raw replacements/attachments; A was too cautious about supplying the source-level OVER route: `served-plan-cursor.lisp:146,161` → `over-window.lisp:56–64` → `served-catalog.lisp:778–784` → catalog/arena reads, called under O at `owner:518–523`. Dynamic cold reachability still needs a native witness.
A lexical `*fnn-extent-no-io*` binding suppresses only effects of realizers proved/declared to honor that mode; it cannot excuse an unrelated fsync or page realizer. Explicit `:io` is a scoped blocking exception, not evidence of bounded response time (`owner:2453–2458` is a deliberate synchronous statement barrier).
D's literal R6 follows everything `fnn-call` calls, which would forbid legitimate A/E/K locking inside declared entries: `owner:504–510` calls `fn-rpin-step` under A; raw extent realization locks E (`extent:1043,1056`). R6 instead checks **dispatch administration**, stopping at declared target invocation; R2/R5 govern the target. Include the trailing-stobj cache (`io:352–379`), not just guard specs, in the allowed startup/read-mostly inventory.

### D7. Lock order and unlocked flags — I HOLD MINE, adopting the deputy's additional edges

D T2 asks for an acyclic *total* order; A §3 uses a partial order and distinguishes release-then-acquire. A checked DAG is sufficient. G admission releases G before O (`owner:1588–1593`); a gate token is a capability, not another physical mutex. Timed wait may return without its mutex (`owner:3496–3499`); context must change accordingly.
D §1c says C protects mux pass counters, but `mux:1284` increments passes outside C; C merely protects notification at1303. R1b must report the publication protocol gap. “Word-sized, single writer, polled” is not by itself a memory-order guarantee, and visibility cannot be inferred from a lock held only by the reader.
I adopt O→M (delivery callback at `owner:3035–3041`, `mux:678`, while the outer completion may still hold O), E→Q (`extent:920,1255,1261` → diagnostic queue), and A→Q (`owner:510–512`) as edges my table omitted. C is released before the delivery callback; there is still no demonstrated C→M edge there.

### D8. Current bugs versus missing declarations — I HOLD MINE

D §2 calls the bare page realizer an open close/reuse bug; D §7 F1 also says its callers make it safe today. A §3.7 G1 correctly separates the **missing checked lease contract** from a demonstrated live UAF. `extent:1147–1153` proves the local gap, not that a retirement can overlap every caller. R3 should fail the unsupported borrow and request a scoped caller capability; neither blanket “safe” nor blanket “reachable UAF” is established.
Likewise the current direct cold line is repaired: `extent:988–1032,1228–1245` retains issued ownership through return and prevents close. t41 must pass that declared protocol and fail a mutation that removes its hold; it must not rediscover repaired r31 F1 on every offlock pread.

### D9. Dispatcher/proof scope and factual corrections — I ADOPT THE DEPUTY'S additions, not all conclusions

A omitted the strongest actual-subject discovery theorem and understated historical recovery scope. `productive-read.lisp:5–9,71–100` names `fn-mca-read-span`, conditions and missing qualification; `byte-store-programs.lisp:236–240` explicitly calls the per-file layout unreachable. The current log route must anchor the recovery claim, not P10's historical program alone. `owner-retain-carried.lisp:52–74` says the served-state carry is unfinished: it cannot simply be assumed as HM's established invariant.
D's universal “hypothesis gap” needs narrowing: `owner-served-carried.lisp:230–235` already proves reference equality under `fn-ocl-relation` plus indexed view. The further lift to static pinned-prefix replay, full caller premises and all installers still needs establishment; absence of an unconditional `ocl → own` implication does not erase that bridge. Eleven installer omissions from a prose coverage table are leads, not proof that eleven preservation theorems do not exist.
`interfaces.json:9–11` has zero raw-dispatched entries; `allocation-epoch-host.lisp:116–124` has raw declarations, but `interface_emit.py:85–86` reads selected declaration files and `build.lisp:401` loads the principal interface file. No load/reference to allocation-epoch-host was found in the searched host/books/tools. Production drift is **UNVERIFIED**; distinguish staged declarations from actual image dispatch rather than “fix” the zero blindly.
D says the syncer fsync holds K; `io.lisp:6879–6885` explicitly says the barrier runs **outside** K, with kernel updates at6895/6899 and8070 under K. D also says fnn-call rewraps entry-guard faults; `io:1378` runs that guard before its handler. These details change R5/R7's path model.

## 3. WHAT EACH MISSED, verified at this source

- **D → A: productive read and recovery scope.** The discovery theorem, unreachable per-file recovery, unfinished carry and coverage table are at the sources in D9. Add their scope to the composition plan; do not treat the discovery header as fresh certification.
- **D → A: activity accounting differs from timer scheduling.** `public-exposure.lisp:789–803` uses `entry-last`; `mux:503–513` rearms locally after draining without an exposure activity event. My B4 was the separate stale-next-deadline busy-poll defect (`mux:1169–1185,1244–1248`). Both need witnesses; the intended idle-policy correction is not proved merely by moving the timer.
- **D → A: other response holders still defer reclaim.** `owner:504–510` shares response and arena pins; `:5747` subtracts only reclaim's own pin. My “own reader repaired” observation does not resolve slow-client holds. Eight attempts (`:5518`) bound the pass, not eventual successful swap.
- **D → A: actual unlocked writers.** `retire` is written under R at `owner:4724` and without it at4778; stats at4298 differs from E-protected updates; `io:7403–7416` clears dir-pending offlock. The declarations must name all writers, not accept a “single writer” rationale by assertion.
- **D → A: existing harness assets.** `tools/resilience/contract.py:1–8` is a theorem-transcription oracle; `scenario.py:75–94` and `schedule_points.py:36–39` mark pending page/read and reclaim coordinates. Reuse this infrastructure; do not create another Python semantic oracle.
- **D → A: assumption misattribution.** PRF-1234 (`planning/proofs.json:21406ff`) says “Host thread/mutex/table fidelity is A-HOST”; `assumptions.lisp:154–181` constrains reports/events, not mutex semantics. A-CRASH-IMAGE has an explicit constrained realizer at342–350; it deserves a separate scope in the physical bridge.
- **A → D: parent catch swallows core faults.** `io:75–89` defines the subtype hierarchy; off-O issue at `owner:3460` can reach parent catch3704 without a stop predicate. Publication completion at5135–5141 also catches shared failures after a gated, not shared-action, body. R7 must cover guard and cleanup faults, not just make-thread ownership.
- **A → D: transfer-to-dead-inbox race.** `mux:1382–1397` releases R before enqueue under M; stop's last drain is1312 and wake-fd close1333–1334. R4's “registry plus join site” alone misses this producer/admission boundary. Add R8.
- **A → D: deregistration is not physical return.** Publisher removes its worker at `owner:5147–5150` before unpin/nursery/reconsideration5152–5162; exporter removes at5413 before unpin5415. `wait-workers:4804–4811` can return on the empty roster. R4 must include terminal cleanup/receipt order.
- **A → D: broad claims need scope.** The writer has per-item `error → :failed` handling (`io:1030–1045`), but sink-step faults at1066 can escape the loop; joining a dead thread is not necessarily successful queue settlement. Preserve the diagnostic-versus-store failure distinction instead of claiming every writer failure fences the store.

**Finding-ID crosswalk:** r31 F1/F2 is corroborated by PRF-1234. The supplied A uses B1–B4/G1–G4; neither supplied answer nor searched source/tracker text supplies the definitions of **r71 F4/F6/F7/F8**. Their exact mapping is **UNVERIFIED**, and I will not manufacture aliases. t41 fixtures below cover the concrete committer, publication, adopt/stop, worker-tail and timer findings by function name. Attach the coordinator's r71/sweep locators when available; this is bookkeeping for the coordinator, not a product decision for ember.

## 4. THE RECONCILED RULE SET FOR t41

### Common contract: what the checker actually decides

Use the existing non-evaluating reader with source spans, a contextual call graph, and small structured contracts: state regions/protectors; allowed actors/phases; lock requirements/effects; raw-realizer/attachment bindings; bounded modes; resource argument/result identities; callbacks; thread start/terminal/join; exception scope; I/O exceptions. Keep one contract schema. Initial explicit metadata can later be emitted from entry/program declarations; never maintain two independent authoritative copies.
Recognize existing wrappers with explicit syntax summaries rather than evaluating macro expansion. Quoted data is not executed. An async lambda starts with a fresh lockset and only explicitly transferred capabilities; it does not inherit its creator's O lock. Known synchronous callbacks are analyzed in their caller context. Unknown callable values, macros or alias transformations produce **unresolved**, not “safe.”
Output three categories: structural violation, unresolved contract/analysis, and declared scoped exception; also print analyzed/total sites and legacy baseline counts. Report-only initially; first gated scope rejects new/unbaselined violations **and unresolved sites**. Baseline entries identify rule, function/site, reason and source fingerprint, not a wildcard function exemption; zero-new-findings is not zero-total-findings. Parked/build/offline code is inventoried under separate reachability/phase roots.
The decisive first regression is **R3's r31 F1 shape**, then fault/transfer/lifecycle regressions. Keep D's R-numbers; additions follow R6. For each rule below, “declaration” closes a structural analysis gap, not the independent obligation to prove that contract's meaning.

### R3. Every physical read has a surviving resource authority — FIRST

**Decide:** at each declared read sink (`pread`, window pread, durable/page realizers), every possible analyzed caller context supplies either an unbroken exclusion preventing retirement or a capability tied to that fd/file incarnation and range. Check acquisition before lock release/worker dispatch, transfer into the worker, and no declared release before return/settlement on supported paths.
**Catches:** first r31 F1's naked offlock pread; current `fn-pgs-fill-realize` (`extent:1147–1153`) has no locally established lease. Pass issued-token `prefetch:942–956` and snapshot lease `owner:4898–4917` only with their full contracts, not a function-name allowlist.
**Cannot decide:** aliasing hidden in arbitrary data, immutable disk contents or actual fd lifetime. Require typed borrow/transfer/settlement and caller-supplied lease contracts; unknown origins fail unresolved. A generation pin counts only if its resource-coverage relation includes this file. **False positives:** startup-exclusive reads and helper-supplied holds; explicit phase/precondition summaries resolve these. Full arbitrary-path linear capability analysis is later; first landing checks the finite existing borrow patterns and rejects other shapes in the gated scope.

### R1. State access uses its declared protector and access mode — FIRST

**Decide:** derive read/write effects from recognized struct/global/stobj operations and declared callee summaries; each use must satisfy its region's lock, private-owner, immutable-snapshot or startup-exclusive contract. Check actual arguments/results where identity is syntactically trackable. A “requires O” callee called off O is a finding regardless of its docstring.
**Catches:** reclaim's off-O owner key/salt access (`owner:5738,5741`) until captured or declared immutable for the relevant epoch; staged live-state swaps cannot borrow unrelated locks as permission. **Cannot decide:** hidden aliases or semantic immutability; declare instance/epoch and mutation roster, then prove the invariant separately. **False positives:** E/L-protected and worker-private stobjs; precise region contracts avoid a universal O requirement. First landing covers explicit source accesses/known wrappers; unsupported mutation forms remain unresolved.

### R1b. Every unlocked cross-actor publication has a protocol — FIRST

**Decide:** collect syntactic reads/writes with actor contexts; for each cross-actor field not protected consistently, require a protocol row naming writer set, reader set, publication primitive/phase, allowed stale observations, and any multi-field consistency requirement. Reject additional writers or accesses outside that row.
**Catches:** `retire`'s two writer contexts (`owner:4724,4778`), stats' mixed locks4298, mux passes/polling (`mux:1254,1284`; `owner:3663ff`), and dir-pending (`io:7403–7416`). **Cannot decide:** SBCL memory visibility or validity of a racy algorithm; use explicit atomic/acquire-release or phase confinement plus named runtime assumptions, not “word-sized therefore safe.” **False positives:** publish-once immutable configuration; declare the startup barrier and immutable epoch. First landing reports all observed writers; semantic two-writer *overlap* is not inferred merely from two setter sites.

### R2. No undeclared blocking effect in a protected quantum — FIRST, with conservative closure

**Decide:** propagate may-block/may-allocate effects through source calls, declared callbacks, ACL2 executable branches and selected raw replacements/attachments. Report a may-block sink while O is held unless the exact phase/effect is a scoped exception. Model condition-wait's released mutex and any retained outer locks; no “wait releases all locks” shortcut.
**Catches:** OVER cursor attachment route (`owner:518–523`), inline commit3269–3282, statement barrier2453, seal/append (`io:8015–8028,6734–6742`), reclaim install (`owner:5756–5768`). **Cannot decide:** cache warmth, arbitrary branch feasibility, unknown/mode-dependent attachments or time bounds. A no-I/O mode is accepted only for listed sinks that honor it; missing executable closure is unresolved, never purity. **False positives:** unreachable arms and deliberate maintenance commit points; require a justified narrower summary/phase. First landing can overapproximate both executable alternatives and mark unknowns; deeper path precision follows, not a blanket waiver.

### R4. Threads retain ownership until terminal shared cleanup — FIRST

**Decide:** every make-thread has a declared start/capture contract, owning registry/slot, fault policy, terminal-cleanup phase and join/reap site. Scan supported control flow for deregistration/refund followed by shared effects; await/timeout/cancel cannot be declared physical return. Registry mutation sites must match the row.
**Catches:** historical r31 F2's unowned per-miss thread; publisher/exporter premature removal (`owner:5150–5162,5413–5415`); undeclared accept/web failure policy (`owner:5934ff`, `web-host:312ff`). **Cannot decide:** eventual termination, native stack reclamation or successful cleanup after join. Declare physical-return and cleanup receipts, consume them in the model. **False positives:** self-terminating/private threads and startup failures; declare their unwind owner. First landing checks explicit tail/shared-call ordering and registry coverage; full lifecycle simulation is step 2 below.

### R5. Every nested lock edge is declared and acyclic — FIRST

**Decide:** propagate held-locksets through recognized synchronous calls/wrappers; construct edges only for simultaneous holdings, including implicit synchronized-table locks and registered callback effects. Verify a declared DAG, recursive-self exceptions, and exact direct-O exception sites. Diagnose unknown lock objects/targets separately.
**Catches:** any future reverse of O→E (`owner:4884–4885`) and hidden call edges such as E→Q (`extent:1255`); **no existing active AB/BA cycle was established**, so do not invent a deadlock to justify this rule. **Cannot decide:** foreign/runtime lock internals, arbitrary object aliasing or fairness; require primitive effect/identity summaries. **False positives:** G-release-then-O and dead-worker joins; model phase transitions. The direct O list has five nonmacro sites1746,4358,4884,6120,6284, not D's “four”; macro O acquisitions1590/1593 are separate generated-wrapper sites.

### R6. No undeclared shared synchronization/allocation in dispatch administration — FIRST

**Decide:** trace dispatch/guard/stobj-resolution bookkeeping up to the target invocation, reporting lock acquisition, synchronized-table access, mutation and table construction against an explicit startup/hot-path cache policy. Track both normal and fixed callback routes. Target effects are checked under R1/R2/R5 instead.
**Catches:** the proposed per-call synchronized trap-table pattern (not landed here); current lazy guard/trailing-stobj caches (`io:1278–1308,352–379`) remain explicit cost exceptions or migration findings. The staged cache creation1320 is startup, not per-call. **Cannot decide:** contention or predicate traversal cost; declare eager immutable cache readiness and bounded guard kinds, then measure. **False positives:** initialization, error-only diagnostics and legitimate target locks; phase and invocation boundary distinguish them. First landing must include fixtures proving those distinctions.

### R7. Failure scope and fence-before-unlock are structural obligations — FIRST

**Decide:** derive condition subtype relationships from `define-condition`; inspect supported handler-case order and the boundary enclosing guard, target, result installation and cleanup. A broad catch that can consume fault/indeterminate needs explicit class-specific propagation/fencing or a private-failure contract. Shared mutation paths cannot leave exclusion before their declared fault fence.
**Catches:** committer parent catch (`owner:3704`; `io:75–91`), publication-done suppression5135–5141, and shared cleanup outside the containment wrapper. These cover A's B1 concrete faults; r71 aliases remain unverified. **Cannot decide:** arbitrary computed handlers or post-error state validity; require finite failure-scope summaries and generated envelopes. **False positives:** logging's intentional failed-line result (`io:1030–1045`); its private diagnostic contract differs from shared store mutation. First landing diagnoses supported handler forms and unresolved others, not all possible exception behavior.

### R8. Cross-lock handoff requires admission and terminal settlement — FIRST contracts/report; model next

**Decide:** a value escaping one protected region into a queue/callback/worker must be declared copied, immutable, capability-borrowed or ownership-transferred; a stoppable recipient additionally needs an admission token/atomic enqueue-or-reject contract and terminal cleanup on both outcomes. Check recognized enqueue/drain/stop/close sites against that protocol row and token flow.
**Catches:** R→M adoption without a live-inbox transfer receipt (`mux:1382–1397` versus1312–1334); deferred completion callbacks and wake-fd lifetime are also inventoried. **Cannot decide:** all interleavings from an annotation; the actual adopt/stop safety theorem and forced schedule are required in step 2. **False positives:** loop-private lists and copied immutable snapshots; declare confinement/copy explicitly. First landing reports absence/mismatch of the contract, **not** “proved race-free after an annotation is added.”

### R9. Observations, continuation effects and crash coordinates share one declared program — LATER

**Decide:** compare emitted/consumed event names, continuation capture/resume/finish and crash/effect labels against an explicit operation program; reject an undeclared transition, missing named receipt or mismatched literal cut. For timers require one declared eligibility/activity source used by fire and next-deadline computation. Do not attempt arbitrary semantic predicate equivalence.
**Catches:** undeclared cursor-drain activity (`mux:503–513` vs `public-exposure:793–803`), mismatched timer eligibility1169–1185, and mirrored reclaim cuts (`owner:5515ff`) once converted to program declarations. **Cannot decide:** byte/effect semantic equality, liveness or arbitrary formulas; generated programs plus ACL2 simulation close that gap. **False positives:** permitted stuttering/diagnostics and historical cuts; classify visibility and reachability. t41 initially inventories these as later obligations, not falsely claims R1–R8 already detect them.

### Relation to generation

When a declared entry/program generates its lock scopes, capabilities, state/result routing, failure envelope and terminal receipts, R1/R3/R4/R5/R7/R8 are correct-by-construction **for that coordination syntax**, conditional on generator/leaf contracts. Their local handwritten-pattern lints become unnecessary there; the tool still checks declaration coverage, emitted-source identity, calls bypassing wrappers, and all remaining handwritten boundaries. R1b publication primitives, R2 leaf effects, R6 dispatch/runtime cost and R9 host-observation binding still need checking/qualification. Syntax by construction is not a proof that the declared invariant is true.
This is why t41 is worth landing before generation: it identifies the exact operations/contracts the generator must own, catches the next unsupported borrow, and supplies regression fixtures. It must not freeze the handwritten architecture or grandfather semantic defects permanently.

## 5. THE RECONCILED FIRST THREE STEPS

1. **Land t41's bounded structural checker and one contract vocabulary.** Implement R1/R1b/R2/R3/R4/R5/R6/R7 and R8 contract coverage with source spans, contextual summaries and explicit unknowns; prioritize R3's existing borrow patterns. Report against all native roots, gate only the declared analyzed scope with exact legacy findings. Reuse the reader and binding/attachment infrastructure; no evaluator or general macro execution.
   **Acceptance:** naked-fd regression fails; issued/cancelled/returned cold route and snapshot lease pass; removing a hold or moving release before return fails; committer catch, premature deregistration and unsupported inbox handoff are named findings. Fixtures distinguish E/private state from O, async from sync callbacks, released G from nested G, and dispatcher bookkeeping from target locks. Print total/baselined/new/unresolved/excepted separately. Do not require a new whole-tree ACL2 run to validate a Python source checker.
2. **Repair live handoffs/failure envelopes and compose the first resource model.** Fix adopt/stop admission, worker terminal accounting and core-fault containment; model their actor/capability/receipt actions using existing pin/read/worker ledgers. Generate or centralize the small wrappers that perform those exact protocols, with R1–R8 checking every call site. Include the raw page-fill lease/caller contract rather than hiding it behind a name exemption.
   **Acceptance:** forced adopt-before/after-stop schedules close or deliver exactly once; publication/export cannot be considered joined before final cleanup; guard/raw/cleanup faults fence correctly; cancelled I/O cannot refund before physical return; duplicate/stale settlement changes nothing. Certify the affected model/consumer roots with reachable witnesses and archive matching evidence. This is the live complete slice A advocated, now immediately after t41.
3. **Lift the actor model through actual served and durable programs.** Establish the carried invariant across the real installer roster, reuse productive-read/reader-view/cursor and log-route recovery bridges, and generate capture/execute/settle programs for commits/publication/reclaim. Add R9 and drive the existing resilience harness from executable ACL2 labels rather than another semantic transcription.
   **Acceptance:** one prefix-consistent simulation covers partial replies, pinned epochs, yields, refusal/fault/uncertainty, physical holds and arbitrary abstract-effect crashes; the theorem names the actual wrapper/result route and log open. Resolve timer activity and reclaim progress with explicit contracts; qualify one immutable candidate, with profile/assumptions/current-proof coordinates kept distinct. Costs/liveness remain separate theorems and measurements.

## 6. Needs ember

**none.** No product preference blocks t41 or the safety fixes. Treat reclaim's current named deferral as the implemented policy, not an implicit promise of bounded successful swap; any later proposal to disconnect slow clients for maintenance must state that user-visible policy explicitly. Missing r71/sweep locators belong to coordinator evidence reconciliation, not a request for ember to decide engineering details.
