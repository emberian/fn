# Whole-system correctness: the top-level theorem and the smallest path to it

Decision note, 2026-10-03. Author: the COMPOSITION deputy (Claude Fable 5.1). Status: DRAFT for
reconciliation with Astra's independent answer (decisions/README.md step 4); no code until reconciled,
except the inventory tooling named in section 6. Every path is relative to /Users/ember/dev/fn at
origin/dev 4aa332295. Line numbers are of that revision and go stale; names do not.

ember's challenge (2026-10-03): "our assurance story must not be very convincing if we are still
finding LOCKING ISSUES; how do we not have whole-system compositional correctness statements yet?"

## 0. The one-sentence diagnosis

Every theorem in the tree is about ONE call: `(state, event) -> (state', effects)` or a serial run of
such calls (`fn-own-run`, `fn-ocfg-run`, `fn-bs-*-program`), under the hypothesis that the host calls
it atomically, on a related state, and performs its effects in the modelled order; the HOST is the
program that makes those hypotheses true, 67k lines of SBCL with ~290 lock/thread sites, and it is
covered by prose (specs/host.md HST-002, -005, -023, -033) and by reviewers, not by any theorem, any
model or any check. The six locking defects of this month are all in the glue BETWEEN atomic
sections: a value captured under a lock and used after release without a pin (r31 F1,
`fn-pgs-fill-realize`), a thread spawned and never owned (r31 F2), I/O performed inside a section
(r67 F2), a host timer deciding what ACL2's exposure model should decide (the idle deadline), a
liveness condition no one stated (the reclaim swap behind undrained responses), and a lock on the
per-call path (the trap). None of these is a false theorem. Each is a missing STATEMENT about the
host and a missing CHECK that the host is what the statement says.

The answer is therefore in two halves that must land together: (1) a MODEL of the host as a
labelled transition system whose atomic sections are the owner's quanta and whose off-lock steps are
the existing ownership protocols, with ONE theorem over all its schedules; (2) a BRIDGE that makes
the host be that model: generated glue where a declaration can carry it (def-entry's successor), a
fail-closed lock-discipline check where hand-written code remains, and the model as the schedule
enumerator and oracle of the native fault harness. Sections 3 to 6 give the theorem, the choice, the
order and the first slice. Section 1 is the inventory ember asked for; section 2 classifies the six
defects against it; section 5 names what stays trusted.

## 1. Inventory (PART 1, sent to the coordinator the same day)

### 1a. Whole-system statements that exist today

"Whole-system" here means: composes more than one subsystem end to end, or quantifies over a
SEQUENCE of events rather than one. Each line: the statement; what it assumes about the host.

READER REPLY vs REFERENCE SEMANTICS (per connection, serial)
- `fn-own-read-is-served-step-on-pinned-prefix` (books/owner-invariants-served.lisp:175) and
  `fn-scar-ocfg-read-span-is-reference-under-ocl-relation` (books/served-span.lisp): the host-called
  read span `fn-mca-read-span` (host/owner-host.lisp:4272) answers what the reference served step
  answers at the connection's pinned view. HOST: one call per read, under the mutex, on a state
  satisfying the carried relation `fn-lgoc-invariantp`; the octets in `fn-octets` are this read's.
- `fn-own-pinned-view-survives-other-post` (books/owner-served-invariants.lisp:438, P3),
  `fn-own-reader-tls-read-depends-only-on-its-connection-clock-and-view` (:362),
  `fn-ocfg-read-step-without-selection-depends-only-on-its-connection-and-clock` (:390),
  `fn-ocfg-writer-run-keeps-every-connection` (:342, over `fn-ocfg-run` of writer events): a
  connection's reply depends only on its own pinned view, its clock and its own events; writer
  events change no connection. HOST: these are the commutativity facts a linearization argument
  needs; nothing applies them to an interleaved host run.
- `fn-splan-cw-drain-is-the-expanded-reply` (books/served-plan-cursor.lisp): the render windows and
  cursor quanta of ONE connection, however the socket paced them, write exactly the serial reply.
  HOST: the plan is immutable; the cursor quantum runs under the mutex on the generation the
  response pinned; nothing says the catalog it reads is the one the plan was built on except the
  response pin (books/response-plan-pins.lisp) and the swap word.
- `fn-served-step-list-counts-is-the-archive-counts` (books/owner-list-counts-read.lisp:186, M6),
  `fn-nntp-archive-command-pinned-msgid-arms-are-the-scan` (books/nntp-pinned-msgid.lisp:36, T17),
  `fn-served-dispatch-of-a-gated-command-is-480-and-changes-nothing` (books/nntp-auth-invariants.lisp:612, P1):
  single-step, reference-equality keystones over the dispatcher. HOST: one call, the pinned view.
- `fn-own-read-is-served-step-on-pinned-prefix-after-any-trace` (books/owner-invariants-served.lisp:215)
  and `fn-own-reader-sees-pinned-prefix-replay-after-any-trace` (:300): the same after `fn-own-run o
  events` for ANY event list -- the one family stated over a SEQUENCE. HOST: the sequence is applied
  to one value by one caller; and the hypothesis is the STATIC `fn-own-relation`, which no theorem
  derives from the relation the host carries (`fn-lgoc-invariantp` / `fn-ocl-relation`): the chain
  host call -> pinned-prefix replay has a hypothesis gap at its first link (also P2, M6, P8).
- `fn-pcr-served-read-is-the-reference-read` (books/productive-read.lisp:71): the host-called
  `fn-mca-read-span` (credits -> slots -> admission -> no capture -> span) equals `fn-own-read` of the
  consumed prefix, under NAMED premises: the cold page completed, the credit resize answered :ok, the
  read is within its slots, admission did not shed, no committer capture is live, the relation and
  view-index and catalog predicates hold. Its header calls the host's routing of `:serve` back to
  the span "an external host I/O routing boundary; no ACL2 twin" and the book "DISCOVERY ADMISSIONS,
  NOT CERTIFICATION". The closest thing to a composed read theorem, and it says itself where it stops.
- `fn-served-reply-stream-is-partition-independent` (books/served.lisp:2822): the reply depends on
  the concatenated input, not on how the socket split it. HOST: one step per read, in order.

DURABLE ACCEPTANCE (the POST path, serial)
- `fn-own-240-follows-consumed-completion` (books/owner-served-invariants.lisp:242, P2): after the
  owner consumes a completion, the reply is 240 or uncertain. HOST: the events arrive as
  (:take) (:begin) (:store ...) (:complete) in that order, each a separate host call; the completion
  consumed is the one for this submission's generation (books/owner-time-bars.lisp's ledger says so
  for the barrier; the host's committer calls it: fn-otb-issue/-answer-early/-complete).
- `fn-pb-same-article-is-answered-already-stored` (books/poster-bytes-invariants.lisp:557, P4),
  `fn-sbud-prepare-refuses-at-budget` (books/owner-store-budget.lisp:37, P9): single-step.
- The reader view during a barrier: `fn-ocvm-reader-view-is-the-completed-prefix`,
  `fn-ocl-relation-of-a-view-captured-before-appends`, `fn-olr-take-never-joins-the-batch-in-flight`
  (books/owner-reader-view.lisp): along every legal START / START-NEXT / COMPLETE sequence a reader
  quantum sees exactly the completed records. HOST: the host captures the view at those three
  points (host/owner-host.lisp fn-owner-reader-views-capture) and puts it in place for reader quanta.
  This IS a sequence theorem over the commit pipeline's events; it is the closest thing to a
  concurrency theorem in the tree, and it is stated over ACL2's event order, not the host's threads.

RECOVERY and THE CRASH MODEL (serial programs, every cut)
- `fn-bs-recover-program-keeps-relation-at-every-cut` (books/byte-store-k0-recovery.lisp:495, P10),
  `fn-bs-host-reopened-kernel-is-the-recovered-kernel` (:572), `fn-bs-scp-program-crash-is-old-or-new`,
  `fn-rrc-checkpoint-crash-point-refines-with-a-batch-in-flight` (books/recovery-refinement-concurrent.lisp,
  PRF-1214: the publication off the mutex while a batch is in flight -- the ONE concurrent crash
  point modelled, by projecting the pending writes per inode). HOST: the syscall sequence of the host
  function equals the program's steps (tools/native_program_check.py, statically over io.lisp's text,
  for `fnn-finish` and `fnn-sweep-staging` only; reclaim's cuts are mirrored by hand at
  host/native/owner.lisp:5515); every death is at a cut (the natives); the OS tears as the byte model
  says (A-CRASH-IMAGE, A-DURABILITY, A-WRITE-ISOLATION, crash-model-v2 section 1). CAVEATS: P10's
  keystone is over `fn-bs-recover-program`, the PER-FILE recovery, which books/byte-store-programs.lisp:236
  itself calls unreachable since the log format; the served open is `fn-lg-open-program` /
  `fnn-recover-log` (io.lisp:3525; tests/campaign/native_cuts.py RECOVERY_CUTS), covered by
  `fn-lg-open-suffix-keeps-the-relation` (books/store-log-route-programs.lisp:97) and the recovery
  refinement, which is MODEL-LEVEL (PRF-1212: the store instance "WRITTEN, NOT ADMITTED"); the marker
  program `fn-bs-marker-program` has no source left (only a .cert/.port), so planning/current.md's P10
  "latest positive result" is stale.

THE OWNER STEP FUNCTIONS and THE CARRIED RELATION
- `fn-own-step` / `fn-own-run` (books/owner.lisp:3119/:3167) and `fn-ocfg-step` / `fn-ocfg-run`
  (books/owner-config.lisp:699/:720): THE serial reference machine over 33 event kinds.
- books/owner-host-relation.lisp COVERAGE table (:15-:62): host entry -> the ACL2 function it installs
  -> the theorem that `fn-lgoc-invariantp` is established (the two opens) or preserved across it, for
  every host transition of the owner value `fn-owner`. HOST: each entry is one atomic call; the
  value is `(fn-owner-ocfg state)` and nothing else writes it (tools/owner_globals_check.py counts the
  globals; nothing checks who writes them off the mutex). Eleven host installers of `fn-owner` are
  NOT in the table: fn-owner-live-post-config, -replace-core, -authority-publication-install,
  -sasl-context, -exposure-health, -chunk-span-install-result, -unavailable-line-at,
  -resource-unavailable-line-at (host/owner-host.lisp), -index-reader-request-complete
  (host/index-reader-request-host.lisp), -history-complete-current (host/history-owner-completion-host.lisp),
  -account-outcome (host/native-admin-host.lisp). The def-carried row of books/owner-retain-carried.lisp
  covers the open and three prepares and says of the rest (:62-70) "the relation is not an invariant
  of the served state".
- `fn-osch-control-waits-at-most-the-bound` (books/owner-scheduler.lisp, HST-023, PRF-248),
  `fn-ocs-in-flight-admits-only-inspect-commit-and-reader` (books/owner-commit-steps.lisp),
  `fn-otm-next-is-ocp-next` (books/owner-time-model.lisp): the GATE's pick, fold and disk mode are
  ACL2's over host observations (waiting counts per class, hold/wait ms, clock readings). HOST: the
  gate mutex is held for the list update and one ACL2 call (owner.lisp:1248-1256); the admitted
  thread then takes the owner mutex (owner.lisp:1575-1606 `fnn-owner-gated`).

CONNECTION ISOLATION and FAULTS
- `fn-ocfg-fault-keeps-every-other-connection` (books/owner-served-invariants.lisp:499, P5),
  `fn-owner-callback-fault-complete-effects` (books/owner-connection-callback-refinement.lisp:99),
  `fn-ocl-no-reader-observes-a-half-change` (books/config-owner-publish.lisp:180, P6). HOST: the
  fault envelope maps failures in exactly the off-mutex scopes to the connection (host.md:155-161);
  nothing states that the host calls `fn-owner-fault` at every point where it can fault (PRF-040's own
  text: "a code property, not a theorem").

OFF-LOCK READS and READERS (the pieces of a concurrency model that exist)
- books/page-read-ownership.lisp (fn-pio: one issued read = a row naming the file INCARNATION and the
  whole extent identity; cancel revokes publication, not ownership; only actual completion settles),
  books/page-read-executor.lisp (fn-pxe: a persistent worker's job incarnation; a late return is
  :stale-job), books/page-read-direct.lisp (fn-pio-direct-admit / -settle; keystone
  `fn-pio-direct-cancelled-read-still-pins-its-file`): the unfunded cold line's protocol. HOST:
  host/native/extent.lisp `fnn-extent-issue-direct` (:988) and `fnn-extent-direct-settle` (:1016)
  are the two transitions; the row is kept in `*fnn-extent-issued*` under `*fnn-extent-lock*`; the
  close `fnn-extent-close` (:1225) asks `fn-pio-file-clear-p` first.
- books/arena-reader-pins.lisp (fn-arpn, epoch-based reclamation; keystone
  `fn-arpn-release-postdates-every-live-pin`) and books/response-plan-pins.lisp (fn-rpin: one hold
  per connection's response plan). HOST: `*fnn-arena-pins*` under `*fnn-arena-pins-lock*`
  (host/native/io.lisp:6768); readers pin under the owner mutex before their thread exists
  (owner.lisp:5035, 5247, 5301); the swap word counts them (owner.lisp:5747).
- books/owner-time-bars.lisp (fn-otb: the unresolved operation's ledger (G OPEN TOLD): a completion
  is consumed exactly once into its own generation; another generation's is :stale, a second one
  :consumed; the read's page dependency deadline; the restart's clock domain). HOST: the committer
  calls fn-otb-issue / -answer-early / -complete; the cold await calls fn-otb-dependency-step
  (owner.lisp:4337-4365) OFF every lock.
- books/owner-cold-line.lisp, books/served-plan*.lisp: the per-line re-run after a cold abort; the
  immutable plan and its windows. HOST: `*fnn-extent-no-io*` is bound ONLY in
  `fnn-owner-chunk-span-no-io` (owner.lisp:4160-4177); the cursor quantum (owner.lisp:514-527) and
  every other section run the realizer in its I/O mode (r67 F2's finding, still open).

THE INTERFACE REGISTRY, REACH and THE CHECKS
- `definterface` (books/definterface.lisp; host/interfaces.lisp; planning/interfaces.json: 1,411
  entries, `raw_dispatched: []` although host/allocation-epoch-host.lisp:116-124 declare
  `:raw-with` -- a drift to fix): a declaration asserts the entry's class, its arity and kind guards
  (what `fnn-entry-guard` evaluates, io.lisp:1255-1370) and, with `:raw-with`, the NAMED preservation
  argument for raw dispatch (D40). It says nothing about the thread, the lock or the order it is
  called in.
- tools/reach_check.py `--strict 0`: every keystone's subject is reached, in a static call graph seeded
  from the loaded host files, from a host dispatch -- "0" means 0 UNBASELINED orphans (the current
  summary: 3,822 events, 364 unreached, 0 unbaselined). It is a graph over source text; it knows no
  thread, no lock, no section, and a callee of a hosted function counts as hosted.
- tools/host_check.py (the files load in the image's order; declared vs dispatched entries; counterparts
  in the world), tools/native_program_check.py (the durable syscall sequences of two io.lisp functions
  vs their byte programs), tools/owner_globals_check.py (the owner's state globals only shrink),
  tools/harness_check.py, tools/hot_path_check.py: none reads a `with-mutex`.
- tools/resilience/: the scenario IR with faults at NAMED boundaries (version 2 adds an `interleave`
  action and `deliver-stale-completion`), a whole-history checker ("does ONE legal execution of the
  contract explain ALL the observations"; inconclusive past its budget, never valid), adapters for the
  native cuts, page I/O, response holds, reclaim holds, the simulator, power loss, INN. The schedule
  points without a host coordinate are listed by name (`PENDING_BOUNDARIES`:
  `page-read-outstanding` = exactly r31's race; `reclaim-candidate-selected`). The contract model is
  Python transcriptions of named theorems (tools/resilience/contract.py), each citing its theorem.

What NO theorem states (the gap, in the inventory's words): nothing relates two threads; nothing
states that a section's input state is the state the previous section left (no sequence theorem
over HOST entries on `state`; `fn-own-run` is a pure fold); nothing states that an off-lock step
reads what it was issued for except inside the three protocol books, and nothing states that every
off-lock read of the host is an instance of those books; nothing states that the host applies a
section's several global puts (owner, effects, output, credits, exposure) as one unit; nothing
states that a host timer or counter is an event of the model; no two-connection theorem has a
re-pin, a cold completion or another connection's open/close/advance between A's steps (P3 covers
writer events and the outcome only); nothing states a liveness property of the host beyond
`fn-osch-control-waits-at-most-the-bound` (in quanta) and the disk deadline (in recorded time); the
one concurrent crash point proved (PRF-1214) is one of six off-mutex programs; the named
assumptions A-HOST, A-DURABILITY, A-WRITE-ISOLATION are encapsulates that no dependent theorem
takes as a hypothesis (books/assumptions.lisp:23-26 says so); `fn-sched-step`, `fn-relay-crash-recover`,
`fn-ibp-*`, `fn-pwif-*` are models no host line calls.

### 1b. The trusted base, made explicit (what a claim silently relies on that is not proved)

Named, with an ACL2 constraint (`encapsulate` + local witness): the assumptions books. In
`books/assumptions.lisp`: A-DURABILITY (:78, cited by 1 book: its own; crash-model-v2 calls it a
strawman), A-WRITE-ISOLATION (:115, 1 book), A-HOST (:154, `fn-assume-host-report` / `-events`: "the
adapter preserves event identity/order" -- cited by NO theorem; PRF-1234 cites it for "thread/mutex/
table fidelity", which it does not say), A-PEER (:200), A-IDENTITY (:229), A-POLICY (:263),
A-FAIRNESS (:295, liveness only: a natp contact index), A-CRASH-IMAGE (:342, `fn-assume-physical-crash`:
the platform's crash is one the byte model admits -- the real crash assumption; no failures.md row),
A-CRYPTO-TRAILER (:363), A-HOST-EXCLUSIVE-READ (:402: no other writer between range reads under the
store lock), A-BP-CONTACT (:449). `books/assumptions-durable.lisp`: A-DURABLE-EXTENT (:48, the extent
realizer answers the durable octets; `fn-durable-realize-octets` is HOST code, extent.lisp:1052),
A-DURABLE-LZ (:133). `books/assumptions-pgs-host-io.lisp`: A-PGS-HOST-IO (:83, :181; `fn-pgs-fill-realize`
and `fn-pgs-fill-frame` are host code, extent.lisp:1145). Registered outside the closure:
A-CHECKPOINT-PUBLICATION, A-CARRIED-PAIR (assumptions-publication.lisp), A-RECOVERED-OPEN
(assumptions-recovery.lisp), A-ARENA-STORED (assumptions-stored.lisp). Constrained seams with no
assumptions book: `fn-digest` (crypto-seam.lisp:85, 45 books; attached to BLAKE3), `fn-sig-*`
(:106; the ML-DSA-65 verifier is a raw `(defun fn-sig-verify ...)` in host/native/signatures.lisp:363,
A-SIG-NATIVE), `fn-anchor-leaf-digest` / `fn-anchor-sig-verify` (anchor.lisp:193/:220; realized by
the host, no attachment), `pgs-digest` (pagestore.lisp:61, 44 books; NO realizer attached).
`defattach` everywhere discharges its constraints (crypto-attach, frame-digest-buffer, records-attach,
statement-attach, byte-store-frame, byte-store-txn-name). No `skip-proofs`, no `defaxiom`, no trust
tag under books/; `defttag :fn-native-host` only in the image builds (build.lisp:415-589), under
which crypto.lisp, io.lisp, extent.lisp, deflate.lisp load raw and digest.lisp replaces the BLAKE3
function (A-CRYPTO-NATIVE).

Named in prose only (specs/failures.md rows without an encapsulate): A-CRYPTO-NATIVE, A-SIG-NATIVE,
A-TLS-NATIVE, A-SBCL-RUNTIME ("threads" in one word), A-EXTRACT, A-TARGET-COMPILER, A-SBCL-INTERNALS
(parked). Named only in a spec: A-BP-PERSIST, A-MEDIA, A-FIRMWARE, A-POSIX, Freshness (crash-model-v2
:1967-1988); the OS facts the byte model assumes (:100-106, :506-512, :720-729: fsync drains exactly
its inode, rename atomic per entry and durable only after the directory fence, failed fsync lands a
torn subset and a retry fences nothing, one inode's data never shares a write unit, no auto_da_alloc).

NOT NAMED ANYWHERE (neither encapsulate nor row), by class:
- HOST ATOMICITY: every ACL2 owner entry is called as one section under `fnn-owner-serialized`
  (host.md:112, :1448 prose; D40: "a raw dispatch is not a proof about the host's other globals";
  PRF-040: the host calls fn-owner-fault wherever it can fault is "a code property").
- LOCK DISCIPLINE: owner state is read only under the owner mutex; a value used off the mutex is
  pinned; no I/O under the mutex (HST-023, HST-033 prose; r31, r67, `fn-pgs-fill-realize`; PRF-272
  "kernel updates are serialized by the log's lock" is a host claim).
- EFFECT ORDERING: the host performs a section's effects in the modelled order and feeds each
  completion back as the event of its own generation (r25's "host-order standing question: a documented
  host obligation" that no document names; current.md:139 "the published completion record is not
  proved to be the event ACL2 built"; host.md:191, :1604).
- THE DISPATCHER: `fnn-call` applies the counterpart or the raw definition under `guard-checking-on`
  = t (host.md:421-427, asserted); the D40 checker "is a declaration lint, not proof that a theorem's
  premises hold at a host call"; the entry-guard fault re-wrapped by fnn-call's handler (r69 F1).
- SBCL: mutex and condition-variable semantics; the memory model for the flags read without a lock
  (`stopping`, `retire`, `read-octets`: plain slot reads from other threads); `:synchronized` hash
  tables; `get-internal-real-time`; thread creation and join. A-SBCL-RUNTIME says "threads".
- CLOCK: the monotonic reading taken under the gate mutex (HST-026; regression is counted, so weak);
  the timer lateness bound L (host.md:753, assumed).
- CRYPTO/LIBRARY without a row: libsodium Ed25519 and the SHA-512 Roughtime leaf (architecture.md:160-168
  "a trusted correspondence"), `/dev/urandom`, the outbound zlib (build.lisp:430 "untrusted").
- DEPLOYMENT: no archived manifest certifies the current closure of any capability keystone
  (planning/current.md, every row); the live nodes run a release build of a3553e6b, not a qualified
  image; hbox's ZFS is not a qualified filesystem profile.

### 1c. The host's concurrency structure, read from source

ONE MUTATION OWNER. Every semantic transition runs in a section: a thunk passed to
`fnn-owner-serialized` (owner.lisp:1810), `fnn-owner-transit-serialized` (:1868),
`fnn-owner-serialized-with-control-turn` (:1826) or `fnn-owner-gated` (:1575): the thread names its
class, waits at the GATE (gate mutex "fn owner gate", owner.lisp:1257; ACL2's `fn-otm-next` picks the
class under it, :1314; the gate mutex is released before the owner mutex is taken), takes the owner
mutex `fnn-owner-service-lock` ("fn owner/store", :1209), runs the thunk, and on any serious condition
installs the exit-3/4 fence BEFORE releasing (:1796-1808). ~110 section sites across 19 native files
(owner.lisp 43, mux.lisp 14, admin 7, feed-service 7, control 5, hybrid-control 5, pull-service 5,
web-host 5, ...). The ACL2 calls inside sections go through `fnn-owner-core` / `fnn-core-state` /
`fnn-core-buffer-state` (io.lisp:392-420, :1429-1440), which append the LIVE stobjs and
`*the-live-state*`; `fnn-call` (io.lisp:1372) runs the entry guard then `fnn-dispatch-function`
(:1249: the raw definition when `:raw-with` is declared and the counterpart selector is off; 0 raw
entries in the production table today).

LOCKS and what each protects (defining site; "guarded-by" when the source says so):
1. owner/store mutex (owner.lisp:1209): the ACL2 live state (`fn-owner`, `fn-owner-retain-carry`,
   every `fn-owner-*` global), the live stobjs (`fn-arena`, `fn-cat`, `fn-hist`, `fn-octets`,
   `fn-hrecs$c`), the Store struct and its log kernel's owner-side phase, the feeds, the service's
   cold-read queue (`cold-head`/`cold-tail`), `space-need`, `response-pins` capture,
   `*fnn-extent-retired*`/`-pending` (extent.lisp:1208-1215). Taken through the gate, and DIRECTLY
   (no gate token) at owner.lisp:1746 (stop-service), :4358 (cold-shutdown), :4884 (root-release),
   :6120/:6284 (lifecycle), safe only because none of them waits on the gate. I/O INSIDE IT, by
   rule none (HST-023, HST-033 prose), by FACT: the inline commit for a logical connection (no
   socket: the pull feed, bound submissions, BP transit) seals, pwrites and fdatasyncs under the
   owner (owner.lisp:4581 -> `fnn-owner-commit-queued-locked` :3269 -> `fnn-owner-commit-sync`
   :3156 "or inline inside a quantum"); `fnn-log-await-sync` condition-waits for the syncer under
   owner + kernel lock (io.lisp:8007-8013, reached from seal / take :full / commit-open-batch);
   `fnn-log-ensure-extent` preallocates + fdatasyncs at seal (io.lisp:7866); `fnn-log-append`
   pwrites (io.lisp:6734-6739); `fnn-log-members-in-flight` -> `fnn-extent-register` open(2)+fstat
   (io.lisp:6760); the FNFD feed append write+fsync (owner.lisp:897-901, from flush :1054 and
   commit-complete :3247); `fnn-log-rotate` rename (owner.lisp:5234, :5657); the reclaim swap's
   `fnn-state-checkpoint-install` and recovery barriers (:5756-5768, the declared commit point);
   `fnn-extent-close` close(2) via release-pending-extents (extent.lisp:1245, owner.lisp:4849); the
   realizer's SYNCHRONOUS pread for any cache miss not under `*fnn-extent-no-io*`
   (extent.lisp:791-830 `fnn-extent-entry-direct` -> `fnn-extent-read-entry` :700, under owner +
   extent): the OVER/XOVER cursor quantum (owner.lisp:518-523), consumer polls (:2701-2706),
   drain-one/attempt, control quanta -- r67 F2's shape is LIVE for OVER today, not only in the
   unmerged NEWNEWS; the consumer entropy read of /dev/urandom (:2659-2683); socket shutdowns in
   stop (:1714-1730). statvfs alone was moved off the mutex (:1411). The barrier of a SERVED POST
   runs off the owner in the syncer (the design's claim); the rest of this list does not.
2. gate mutex (owner.lisp:1257): waiting/next-ticket/serving per class, busy, holder, turn, aborted,
   sched. Held for a list update and one ACL2 call; never across a step or I/O (:1255).
3. roster mutex (owner.lisp:112): workers, clients, publisher, exporter, export-outcome, export-dir,
   the stop flag's publication, `retire` (set once; read without it by the accept loops, :166).
4. wait-lock + wait-queue (owner.lisp:144): consumer waits (commits, waiters). Order: owner then
   wait-lock; a waiter never sleeps holding the owner (:141-143).
5. commit-lock + commit-ready (owner.lisp:169): awaiting, done, sparing, queued, drain-release, the
   mux loops' pass counters; the committer thread waits on it (:3686-3702); mux loops notify
   (mux.lisp:1303).
6. `*fnn-extent-lock*` "fn extent realizer" (extent.lisp:48): `*fnn-extent-fds*`, `-paths`,
   `-incarnations`, `-bases`, `-next-id`, `-cache`, `-cache-tokens`, `-stats`, `-issued` (the fn-pio
   rows), `-lz-last`, `-direct-next`, the cold workers' rows and free stack. Nested INSIDE the owner
   mutex (owner.lisp:4270 "Owner->extent", :4884-4885, :4898). The cold worker's pread runs with
   NEITHER lock (extent.lisp:942-958 `fnn-extent-prefetch`: lock to find the fd, release, pread,
   re-lock to decide).
7. `*fnn-arena-pins-lock*` "fn arena pins" (io.lisp:6768): `*fnn-arena-pins*` (fn-arpn) and the
   service's `response-pins` (fn-rpin), one ACL2 step per event (owner.lisp:500-512). Taken inside
   sections (:4549 via :483) and off them (mux.lisp:274, 505; pull-service; web-host).
8. `*fnn-payload-lifecycle-lock*` (io.lisp:1556; owner.lisp:1612-1680): the snapshot and recovery
   payload-view leases.
9. the record log kernel `fnn-log-lock` (recursive, io.lisp:6313) + `sync-cv`: batches, the fence
   bit; the syncer thread's append+fdatasync runs under it with the owner RELEASED (owner.lisp:3344-
   3360; books/owner-commit-pipeline.lisp SYNC); `spare-lock` (:6337) the rotation spare.
10. the service log: `*fnn-log-queue-mutex*` (recursive) + `*fnn-log-queue-ready*` (io.lisp:916) feed
    the writer thread (:1049-1078); `*fnn-owner-log-mutex*` (:863) the file write.
11. per-loop mux inbox lock "fn mux inbox" (mux.lisp:72): adopted sockets and wakes.
12. `:synchronized` hash tables: `*fnn-trailing-stobjs*` (io.lisp:352), `*fnn-entry-guard-specs*`
    (:1278: filled lazily by whichever thread first calls an entry; unsynchronized it stopped the
    owner under load), the cold guard cache (:1320), owner.lisp:345. The rd3-trap's `call-in-core`
    table (not landed) added a synchronized write+remhash per `fnn-call` (r69 L1).
13. others: `*fnn-random-state-lock*` (io.lisp:740), the TLS context's lock (tls.lisp: the pair is
    swapped under the lock `SSL_new` takes), the control socket's accept/worker lists (control.lisp),
    runtime-participants' lock + SBCL's `*make-thread-lock*` (runtime-participants.lisp:7, :48, :130;
    parked with A-SBCL-INTERNALS), `flock(2)` on the store (writer LOCK_EX; the retire sweep).

THREADS (every `make-thread`, who joins it, what a fault does): the main owner thread (accept loop
owner.lisp:5957: cold-reap, maybe-publish, reopen-log, maybe-retire each tick; stop, join, close);
+fnn-mux-loops+ = 2 I/O loops (mux.lisp:1373; joined through the workers list owner.lisp:4811; a
loop defect calls fault-service mux.lisp:1350); the committer (owner.lisp:3714; joined :6217 without
timeout; a non-store condition -> fault-service, exit 4); one syncer per sealed batch (:3344; joined
by the committer :3582; its error returns as (:failed e) and is re-signalled under the owner at
COMPLETE :3601); the service-log writer (io.lisp:1078; joined with a timeout :1097; NO handler-case:
a fault kills it silently, lines then drop by ACL2's bound and the join answers :joined); the cold
workers, `:cold-workers` of the profile, default 4 (extent.lisp:534; joined :561/:616; a job error
becomes an fnn-extent-fault result; thread death is detected by fn-pio-worker-death-step); the
checkpoint publisher (owner.lisp:5257) and the exporter (:5307), one each under the roster, joined
through the workers list (publisher errors are logged and serving continues); the extra accept
threads, TLS or plain (:5934) and the web face (web-host.lisp:312): only socket-error is handled, any
other error kills the thread with no fault-service; the feed workers (feed-service.lisp:596; joined
:621; guarded -> fault-service) and pull workers (pull-service.lisp:568; :586); the control accept
thread and up to the ACL2 ceiling of client workers (control.lisp:529, :456; joined :558/:564;
clients unwind by unwind-protect only) -- the control clients RUN the consumer waits (owner.lisp:2792),
the reclaim passes (:5622) and TLS reloads. BP and TCPCL make no threads (bp-app runs on the accept
loop). specs/host.md:536 reserves 12 fixed + 2 + 16 + 4 = 34; the syncer and the exporter are not
obviously among the "fixed" 12. The per-miss cold thread of r31 F2 is gone (page-read-direct's
persistent workers replaced it, merged 0dce73ae5).

STATE THAT CROSSES A LOCK BOUNDARY (captured under a lock, used after release), and what pins it:
- the render PLAN of a served step (owner.lisp:4451 docstring; mux.lisp `fnn-mux-queue-plan` /
  `fnn-mux-flush` :421-461): an immutable value; the arena generation it reads is pinned by the
  response pin taken in the same section (:4549 -> :483 -> fn-rpin) and released when the output
  drains or the connection cancels. Pinned.
- the cursor quantum (owner.lisp:514-527): the plan re-enters a section with the LIVE `fn-arena` and
  `fn-cat`; the swap is excluded by `:readers` while the response pin lives (:5747). Pinned, but
  by a pin whose lifetime the CLIENT controls (section 7, F2).
- the cold line: the entry captured in the read's section (:4536-4541 -> `fnn-owner-cold-issue-locked`
  :4213: issue the fn-pio row and bind a worker under extent BEFORE the owner mutex is released) ->
  pread with no lock (extent.lisp:955) -> await with no lock (owner.lisp:4337: fn-otb-dependency-step)
  -> settle under owner->extent (:4270-4300). Pinned by the row (the file incarnation) and the worker
  row; a timeout cancels the row and keeps the pin (`fn-pio-direct-cancelled-read-still-pins-its-file`).
- the commit barrier: sealed in a START section; appended and fenced by the syncer under the log lock
  off the owner; its completion consumed in a COMPLETE section through the fn-otb ledger (generation;
  :stale/:consumed for a late or second one). Pinned by the ledger.
- the checkpoint publication and the export (owner.lisp:5247-5270, :5301-5315): pin the arena
  generation under the mutex before the thread exists, write off it, finish in a section. Pinned.
- the reclaim pass (owner.lisp:5620-5800): capture section (credit, log rotation, pin) -> off-lock
  walk/rewrite/stage; tombstones interned in owner quanta; rebuild off-lock -> the swap section
  (`fn-owner-orcp-swap-word` with the reader count: :swap only with nothing committed since the
  capture, the pipeline idle and no other reader; the install, the swap and the recovery barriers in
  that one section) -> off-lock extent release. Pinned by the generation; the swap's correctness
  rests on `fn-orcp-swap-word`'s premises being the host's (nothing committed since the capture is
  ACL2's count; "no other reader" is the arena pin count).
- `fn-pgs-fill-realize` (extent.lisp:1145): fd under the extent lock, pread off it, NO row, NO lease.
  Reached from `fn-store-sco-image-open` at the open (io.lisp:2631, before serving) and from the
  history-records readers of `store export`; safe today by circumstance (no retirement runs at the
  open; export holds a generation pin that keeps the file's extents, not the page file), checked by
  nothing. The one off-lock read outside the protocols. (def-holder F1; this note F1.)
- the snapshot page lease (owner.lisp:4898-4915): a ledger :file-pin token under owner->extent,
  then the pread with no lock, released under extent. Pinned (the correct shape).
- the publication, export and reclaim threads read the LIVE arena off the mutex under a generation
  pin, relying on "below the captured count" (append-only) with no lock (owner.lisp:5253-5270,
  :5304-5315, :5469, :5661); the reclaim's rebuilt cat/hist are installed at the swap, validated by
  `fn-owner-orcp-swap-word` (delta / readers).
- the completion handed from the committer to a loop through the mux inbox under the mux lock
  (owner.lisp:3035-3041, mux.lisp:675-683), validated by the connection's phase (mux.lisp:1217).
- disk-free and clock observations taken off-mutex and installed in the next quantum (:5211, :5462,
  :5638); the syncer's result cell read after join and consumed through the ledger (:3340-3355, :3582-3589).
- CROSS-THREAD STATE WITH NO LOCK: `*fnn-sigterm-requested*` (io.lisp:5908; the handler writes,
  loops poll), `*fnn-sighup-count*`, `stopping` (written under roster + owner :1702; read unlocked at
  mux.lisp:716, 1346, 1383, owner.lisp:3637, 3692, 4760, 5939, 5964), `retire` (written under the
  roster :4724 and ALSO unlocked by the accept thread :4778; read unlocked :4478, :4684, :4759),
  `read-octets` (:397 / mux.lisp:189), `queued` (guarded by commit-lock, read unlocked mux.lisp:1301,
  owner.lisp:3612), `synced` (:3340 unlocked / :3353 under commit-lock), `space-need`, the mux loops'
  pass counters (written unlocked mux.lisp:1254-1284, read under commit-lock owner.lisp:3663),
  `*fnn-owner-last-fault*` (check-then-set from any thread :1760, :4302), `*fnn-extent-stats*`
  (incf under the OWNER at :4298, under the extent lock everywhere else: a data race), the log's
  `dir-pending` (io.lisp:7403-7415, read and cleared by the syncer, publisher and snapshot with no
  lock), `*the-live-state*` itself (setf under the extent lock at account-adoption.lisp:17 or in a
  quantum, read everywhere). The only atomic in the tree is `sb-ext:atomic-incf` on the lookup
  counters (io.lisp:6184); no compare-and-swap anywhere. All of this rests on word-sized stores and
  polling; A-SBCL-RUNTIME says "threads".
- the service log: lines produced in sections, written by the writer thread in queue order.

LOCK ORDER, read from the nesting (A held while taking B), with sites: the gate TOKEN (logical,
HST-023) is held from gate-enter to gate-leave AROUND the owner; the gate MUTEX is taken under the
owner at leave (owner.lisp:1599) and at :1566, :3306, :4500; owner -> roster (:1702, :5214, :5253,
:5304); owner -> commit-lock (:1711, :1732, :3020 from :4599, :3035-:3239); owner -> wait-lock (:268
from :1736, :2815); owner -> payload-lifecycle (:1612-:1680, :6120, :6284); owner -> arena-pins
(:504 from :4549; io.lisp:6845-6860; :4854); owner -> extent (:4276, :4312, :4539, :4885, :4898;
every realizer miss inside a quantum; account-adoption.lisp:11-57, consumer-remote.lisp:65,
receiver-parser-turn.lisp:20); owner -> log kernel (io.lisp:6726-8079, all but the syncer's fence
and await); kernel -> extent (io.lisp:6760); owner -> mux-loop (mux.lisp:678's closure from
commit-complete-locked :3254, :3604); owner -> feed/pull runtime locks (the stop hooks :1740 ->
feed-service.lisp:608, pull-service.lisp:575); commit-lock -> gate mutex (:3480-3505); gate ->
log-queue (:1478, :1487); extent -> log-queue (extent.lisp:919, :1255, :1260); roster ->
arena-pins (:5255, :5305); reload -> TLS context (tls-reload.lisp:72 -> :64); every lock -> the
synchronized tables (leaves). Composite: gate-token < owner < { roster, commit-lock < gate-mutex <
log-queue, wait-lock, lifecycle, arena-pins, kernel < extent < log-queue, mux-loop, feed/pull }.
No reverse edge found: nothing takes the owner while holding gate, commit, extent, kernel, roster
or pins. ACYCLIC, by reading; nothing in the tree checks it (F3). Two caveats: the direct owner
acquisitions above bypass the gate token; the owner waits on the syncer (io.lisp:8012) while the
syncer takes kernel and commit-lock but never the owner.

ACL2 CALLED OFF THE OWNER MUTEX: the gate's `fn-otm-*` (under the gate mutex, owner.lisp:1314-1545);
the ledger's `fn-otb-*` in the committer (:3378-3589); `fn-rpin-step` / `fn-arpn-step` (under
arena-pins); `fn-pio-*` / `fn-pxe-*` / `fn-owner-page-*` and `fn-arx-entry-verdict-buffer` on the
shared `fn-octets-rd` (under extent, extent.lisp:320-675); `fn-otb-dependency-step` (no lock,
owner.lisp:4345); `fn-splan-window`, `-window-size`, `-at-cursorp`, `-donep`, `-step-plan`,
`-cursor-resume-ms`, `fn-zc-render-window-size`, the inflater (no lock: pure over the plan and
private buffers; owner.lisp:427-460, mux.lisp:406, :529, :700); the control frame decode under the
control-buffer lock; the log writer's `fn-log-sink-take`; the publication / export / reclaim
threads' `fn-owner-sco-*`, `fn-owner-orc-*`, `fn-owner-orcp-rebuild` / `-load-columns` over the
pinned live arena (:5066-5107, :5441-5737); the accept thread's `fn-ort-window-step` (:4766).
All pure over values the thread owns or a table under its own lock -- EXCEPT: the reclaim pass
reads OWNER STATE off the mutex through `fnn-owner-core 'fn-owner-orcp-key` and `'-salt`
(owner.lisp:5738, :5741, on the control-client thread, between the capture and the swap sections),
and the guard-spec cache reads the world of `*the-live-state*` from every thread (io.lisp:1293;
immutable after build, undeclared). `fnn-call` (io.lisp:1372) takes no lock and checks nothing
about who holds the owner: exclusion is caller discipline only.

## 2. The six defects against the inventory: five kinds, not one

| defect | kind | state today | what was missing |
|---|---|---|---|
| r31 F1: `:direct` cold read, fd pread off-lock, no row, retirement closes it mid-read | OWNERSHIP SAFETY of an off-lock read | FIXED (0dce73ae5): fn-pio row + persistent worker bound under owner+extent before release; close refuses while a row names the file | an issued row (the model: fn-pio); a check that every off-lock pread holds one |
| r31 F2: timed-out direct threads orphaned | RESOURCE OWNERSHIP of a thread | FIXED: the per-miss thread is gone | a worker row (fn-pxe); a check that every make-thread has an owner and a join |
| `fn-pgs-fill-realize` preads off-lock with no row and no pin (extent.lisp:1145-1167) | OWNERSHIP SAFETY | OPEN; a concurrent `fnn-extent-close` (:1245) can close the fd and the number be reused | the same check; it reports this site today |
| r67 F2: cold I/O (the tombstone probe) under the owner mutex in the NEWNEWS continuation | DISCIPLINE (no I/O in a section) | NEWNEWS unmerged; the SAME shape LIVE for OVER/XOVER: `fnn-owner-cursor-step` (owner.lisp:518-523) runs `fn-splan-cursor-step` under the owner with no no-I/O binding; a miss preads under owner+extent (extent.lisp:797/815 -> :700) | a check that a section's ACL2 closure reaches no attached realizer unless the no-I/O mode is bound or `:io` is declared |
| the idle deadline not refreshed by a cursor reply | A HOST OBSERVATION THAT IS NOT A MODEL EVENT | OPEN: `fn-exp-idle` compares `entry-last` (books/public-exposure.lisp:793-803), updated only by a step's charge/observe; cursor quanta and renders never touch exposure; the mux suppresses its timer while a plan is pending (mux.lisp:1170-1176) but re-arms after the reply (:513, :367), so `fnn-mux-idle` (:748-760) can close at once | the render loop's "reply written" fed to the exposure model; a theorem "a connection answered within T is not idle-closed" over the HOST model |
| the reclaim swap blocked by any undrained response | LIVENESS | OPEN: `(1- (fnn-arena-reader-count))` at owner.lisp:5747 counts response pins (same table, :501-513); 8 yields then DEFERRED-READERS (:5518, :5774) | a stated progress property and a schedule enumerator that finds the starving schedule |
| the image-level trap: a global synchronized table per core call | COST on the per-call path | the trap is not landed; the guard-spec cache is synchronized (io.lisp:1278, after an unsynchronized version stopped the owner under load) and still a hidden lock inside every ACL2 call, under the gate and extent locks too | a check: no shared lock on the `fnn-call` path unless declared |

Three kinds (ownership, discipline, cost) are STATIC properties of the host text and are caught by a
fail-closed check (section 4, option iii). Two (observation-as-event, liveness) are properties of a
MODEL with schedules (option i) and are found by enumerating schedules (option iv). None is caught
by more single-call theorems, which is why 636k lines of them did not.

## 3. The top-level theorem fn should be able to state

Three statements, in decreasing order of what they buy; the first is THE theorem.

T1 (REFINEMENT WITH ONE LINEARIZATION; safety). Let HM be the host model: a labelled transition
system whose state is `(SM . H)`, SM the serial owner state (`fn-ocfg` with its Store, the live
catalog and history columns) and H the host's bookkeeping (the gate's scheduler value, the arena
and response pins, the issued read rows and worker rows, the barrier ledger, the captured plans per
connection, the written octets per connection, the retirements pending, the cut of the durable
program in progress). Its labels:

    (:section TID CLASS EVENTS)      the gate admitted TID as CLASS; the section applies EVENTS, a
                                     list of SM events, as `fn-ocfg-run`, and the H updates the same
                                     section performs (pin acquire, row issue, ledger issue, plan
                                     capture) -- one quantum
    (:gate TID CLASS)                enter / leave: `fn-otm-next` / `fn-otm-observe`
    (:render CID)                    one window of CID's plan off-lock: `fn-splan-window`
    (:write CID OCTETS)              the socket took the window (observable)
    (:io-complete TOKEN OUTCOME)     an issued read or barrier completes: :ok | :failed | late (after
                                     cancel) | stale (after settle), through fn-pio / fn-otb
    (:timer CID KIND)                a host timer fires; it is an SM event in the next section
    (:retire S ITEMS) / (:release)   the generation table (fn-arpn)
    (:crash CUT)                     process death at CUT of the durable program in progress

A SCHEDULE is any list of labels; a label whose precondition fails is a refused no-op (the host
faults there). The theorem, over every schedule from a related initial state:

  (a) REPLIES: for every connection, the octets written to it along the schedule are exactly the
      replies `fn-ocfg-run` emits to it over the schedule's sections' events in schedule order
      (the serial order IS the section order; the linearization point of every operation is its
      section, because there is one mutation owner);
  (b) OWNERSHIP: every :io-complete that publishes delivered the bytes of the file incarnation and
      arena generation its token was issued under, and every retirement the table releases postdates
      every live pin (the three protocol keystones, now composed with sections and retirements
      interleaved arbitrarily);
  (c) CRASH: the durable image at every :crash is a crash image of the program at CUT applied to the
      SM state at the schedule's prefix, so the open after it reaches a related SM state (the byte
      crash model composed with the sections that ran before the cut).

Proof shape: a forward simulation with invariant `fn-hm-invp` = the carried relation on SM
(`fn-lgoc-invariantp`) and the H invariants of the component books (pins cover live readers; rows pin
files; the ledger's open generations; plans are projections of the SM state at their capture; the
section order equals the gate's admission order). A :section step is `fn-ocfg-run` of its events,
preserving the relation by books/owner-host-relation.lisp's COVERAGE theorems chained by induction;
every other label is a STUTTER step of SM that preserves `fn-hm-invp` by the component keystones
(`fn-arpn-release-postdates-every-live-pin`, `fn-pio-direct-cancelled-read-still-pins-its-file`,
fn-otb's consumed-once, `fn-splan-cw-drain-is-the-expanded-reply`). No commutativity argument is
needed for (a); the existing per-connection independence theorems (P3 and its siblings) become
PROPERTIES of the serial order T1 delivers, stated once over `fn-ocfg-run`.

T2 (DISCIPLINE; a property of the host text, checked, not proved). Every access to SM state is
inside a section; every value used off a section is immutable or pinned by a row/pin/lease the
same section acquired; no I/O inside a section except the declared commit points; the lock order is
acyclic and total; every thread has an owner and a join; no shared lock on the per-call path. This
is what makes the host BE the HM; it is the bridge, not a theorem about replies.

T3 (LIVENESS; a model property found by schedules, stated under A-FAIRNESS). Every issued request is
answered or refused by name within its deadline in recorded time (fn-otb: exists per request);
every retirement is released once its readers end (fn-arpn: exists); every requested swap proceeds
within B quanta once nothing commits -- which is FALSE today under a client that never drains its
response window (section 7, F2), and the schedule enumerator finds it.

What T1 does NOT say (section 5 names the base): that SBCL's `with-mutex` is mutual exclusion and a
plain slot read sees a prior write; that the image executes the source the check read; that `pread`
on an fd another thread closed is refused rather than answered from a reused descriptor (the row
exists so that this never happens, under POSIX's fd semantics); that fsync means what the byte model
says; anything about the OS scheduler's fairness.

## 4. The four options, and the choice

(i) A MODEL OF THE HOST in ACL2 over all interleavings. Buys: the only place T1 can be STATED; the
schedule enumerator and oracle for (iv); T3. Costs: a new book family (prefix fn-hm-, see section 6)
of a few thousand lines composing books that exist; the theorem over schedules is a simulation
invariant, the usual shape here (fn-ocvm, fn-arpn, fn-otb are each already that shape for one
component). Misses on its own: EVERYTHING, unless the host is the model -- the r31 race was not a
model theorem's failure, it was a host line that never called the model (the :direct line spawned
threads with no row). A model alone would have changed nothing that day.

(ii) THE HOST AS A REFINEMENT BY CONSTRUCTION: generate the section glue from declarations. Buys:
hand-written locking disappears at the ~110 section sites and the six off-lock programs; T2's first
four rules hold by construction; the declaration IS the model's label (a def-entry row with
`:section CLASS :pins (...) :issues (...) :io (...)` is `(:section ...)`'s shape), so the bridge is
syntactic. Costs: def-entry (lane def-entry, Fable; sketch in lanedumps/def-entry.md) must land
first and gain `:section`; a second form `def-off-lock-program` (capture section, off-lock steps with
their pins, install section) for the committer, the publication, the export, the reclaim pass, the
cold line and the cursor drain; the conversion of each site is a lane's work with the natives as the
control. Misses: what is not an entry (the mux loop's timers, the stop path, the services' own
threads) and whatever a generator cannot see (a lambda stored and funcalled elsewhere).

(iii) A MECHANICAL LOCK-DISCIPLINE CHECK over the host text, fail closed, in the fast checks. Buys:
T2 for everything hand-written, today, at the cost of one tool; it reports r31 F1 and F2,
`fn-pgs-fill-realize`, r67 F2 and the trap's lock by rule (section 2); it reads the `guarded-by:`
and "caller holds" annotations the source already carries (extent.lisp 9+17, owner.lisp 1+27) as
its declarations and refuses an unannotated shared slot. Costs: ~1 week for the report-first
version; a shrink-only baseline for today's findings (the tree's ratchet pattern); the ACL2-closure
rule needs tools/ledger.py's call graph (exists, reach_check uses it). Misses: liveness, the
observation-as-event class, and anything dynamic (which arm runs; a thunk captured and run later --
the check refuses that shape instead of guessing, as native_program_check refuses what it cannot
decide).

(iv) A MODEL-DRIVEN INTERLEAVING AND FAULT HARNESS. Buys: the only way to observe T3 and the
observation-as-event defects on the real executable; tools/resilience already has the IR, the
checker and the hold selectors (FN_NATIVE_PAGE_IO_HOLD, FN_NATIVE_RECLAIM_HOLD,
FN_NATIVE_OVER_TEST_PAUSE_AFTER_QUANTUM, FN_NATIVE_PAGE_READ_HOLD); what it lacks is the schedule
GENERATOR and an ORACLE that is not a Python transcription -- both are HM executed (guard-verified,
runs in the image: tools/run_simulator.py's deterministic backend is the seed). Costs: coordinates for
the `PENDING_BOUNDARIES`; HM first. Misses: it is testing; it establishes the schedules it ran.

THE CHOICE: all four, as ONE stack, in the order (iii) -> (i) -> (ii) -> (iv), because each is the
precondition of the next's value: the check makes the host the model's shape today and keeps it so
while the model is written; the model gives the statement; the generator makes the check's rules
unnecessary at the sites it owns (the check keeps policing the rest); the harness needs the model's
schedules. Choosing (i) alone repeats the tree's mistake at a larger scale (a true theorem about a
function the host does not call). Choosing (iii) alone leaves "the host is correct because a lint
passed", with no statement of what correct means. Choosing (ii) alone waits months for def-entry's
successor while the next r31 lands.

## 5. What the theorem would not cover: the trusted base after T1 (name it, do not hide it)

- A-SBCL-RUNTIME, extended by one row A-SBCL-THREADS: `sb-thread:with-mutex` is mutual exclusion
  with release-acquire visibility; `condition-wait` returns only by notify, timeout or abort (and
  "a timed-out condition-wait may return without the mutex", owner.lisp:2852, is handled);
  word-sized slot writes are atomic and eventually visible (the flags read without a lock);
  `make-thread`/`join-thread` as documented. One row, cited by the discipline check's doc.
- A-HOST-IS-THE-MODEL (replacing the unused A-HOST): the host's sections, pins, rows, ledger
  events and plans are the HM's labels in the HM's order. EVIDENCE: the discipline check (T2) on the
  source + host_check --load (the image loads that source) + the image identity + the natives on
  the qualified image. Never a theorem.
- The OS: A-CRASH-IMAGE and the byte model's platform rows (fsync, rename, write units); POSIX fd
  semantics (`pread` on a closed-and-reused descriptor is why the row exists; the row is proved to
  keep the fd open, the OS is trusted to honour an open fd); `poll(2)`, sockets, `flock`.
- A-FAIRNESS for T3 only (the OS runs every runnable thread; the gate's own fairness is ACL2's).
- The dispatcher: HST-001 (raw execution is the logical function where the guard holds: ACL2's own
  premise) and D40's named preservation argument for the entries that skip their carried guard.
- Crypto, TLS, libsodium, the CSPRNG: unchanged rows; two missing rows to add (libsodium Ed25519 and
  the SHA-512 leaf; `/dev/urandom`).
- The reading: the check and native_program_check read SOURCE TEXT with a non-evaluating reader; a
  macro that hides a `with-mutex` is refused, not expanded.

## 6. Ranking by assurance gained per effort; the first slice; the pieces that exist

| rank | work | assurance | effort | catches |
|---|---|---|---|---|
| 1 | tools/lock_discipline_check.py (section 6.1) report-first, then fail-closed with a shrink-only baseline | T2 on every hand-written line, today | ~1 week, one lane | r31 F1, r31 F2, fn-pgs-fill-realize, r67 F2, the trap lock; and the NEXT one of each class |
| 2 | books/host-model*.lisp (fn-hm-): the HM over the component books; T1(b) first (issued reads vs retirement over all schedules), then T1(a) (replies = serial replies with render/cursor interleaved), then T1(c) (reuse recovery-refinement-concurrent) | T1 stated and proved for the model | 3-5 weeks, one Fable lane | the statement; T3's starving schedule as a counter-model |
| 3 | def-entry `:section` + the generated `fnn-owner-gated` wrapper and pin/issue calls; `def-off-lock-program` for the six programs | T2 by construction at ~110 sites; the bridge becomes syntactic | after def-entry lands; 2-4 weeks across lanes, natives as control | every future hand-written section |
| 4 | the HM as schedule generator and oracle for tools/resilience (coordinates for PENDING_BOUNDARIES; the `interleave` action driven by HM labels) | T3 and observation-as-event defects observed on the executable | 2-3 weeks after rank 2's first theorem | the idle-deadline class, the swap starvation |
| 5 | the registry rows: A-SBCL-THREADS, A-HOST-IS-THE-MODEL, the two crypto rows; retire A-HOST's unused encapsulate; fix interfaces.json's raw_dispatched | honesty | days | nothing new; stops PRF-1234's misattribution |

### 6.1 The first slice: the lock-discipline check, and why it would have caught the cold-read race

`tools/lock_discipline_check.py`, over host/native/*.lisp and host/*.lisp with tools/ledger.py's
reader (no evaluation), classifying every function as SECTION (the thunk of fnn-owner-serialized /
-gated / -transit-serialized / -with-control-turn, and every function reachable only from one),
OFF-LOCK (reachable only outside), or BOTH (refused unless its docstring says "caller holds" --
owner.lisp carries 27 such sentences; the check makes them declarations). The inventory of section
1c was produced by reading; the check reproduces it mechanically on every push, which is the point:
an inventory read once is stale by the next batch. Rules, each a named refusal with file:line:

- R1 OWNER STATE UNDER THE OWNER: `fnn-owner-core`, `fnn-core-state`, `fnn-core-buffer-state`,
  `fnn-live-stobj`, `fnn-live-octets`, `*the-live-state*` globals and every struct slot annotated
  `guarded-by: LOCK` are touched only in SECTION context (or under LOCK). Today's annotations are
  the declarations; an unannotated slot of `fnn-owner-service` read from two classes is refused.
- R2 NO I/O IN A SECTION: `fnn-extent-pread`, `fnn-read`/`fnn-write`/`fnn-fsync*`/`fnn-rename`,
  socket recv/send, `sleep`, `condition-wait` on another lock, and -- through the ACL2 call graph --
  any entry whose closure reaches an attached realizer (`fn-durable-realize-*`, `fn-pgs-fill-*`,
  `fn-arena-stored`) is refused in SECTION context unless `*fnn-extent-no-io*` is bound around the
  call or the section is declared `:io (...)`. Section 1c's list says what the first report will
  hold: the inline commit of logical connections, `fnn-log-await-sync`, the seal's preallocate and
  pwrite, extent-register's open, the FNFD append+fsync, the rotation rename, the swap's install
  and barriers, `fnn-extent-close`, the realizer's synchronous miss in every quantum without the
  no-I/O binding (the OVER cursor first), /dev/urandom, the stop's shutdowns. Each becomes a
  DECLARED `:io` (a commit point the design wants under the owner: the swap, START's seal) or a
  finding with an owner (the cursor miss; the inline commit for logical connections, which the
  syncer exists to avoid). r67 F2 is this rule: `fnn-owner-cursor-step` dispatches
  `fn-splan-cursor-step`, whose closure reaches the realizer through `fn-ovw-step`'s arena read,
  with no no-io binding.
- R3 AN OFF-LOCK READ HOLDS A LEASE: `fnn-extent-pread` and `fn-durable-realize-octets` outside a
  section are reachable only from a function that holds an issued row token (fnn-extent-prefetch), a
  window lease (fnn-extent-window-run) or a ledger file pin (the snapshot page lease,
  owner.lisp:4898). `fn-pgs-fill-realize` (extent.lisp:1153) fails it today; r31 F1's per-miss
  lambda failed it then. This is the rule that would have caught the cold-read race: not a theorem
  about reads, a refusal of a read that is not an instance of the theorem's protocol.
- R4 EVERY THREAD HAS AN OWNER: each `make-thread` site names its registry slot and its join site
  (a table in the check, declared once); r31 F2's per-miss thread had neither.
- R5 LOCK ORDER: the declared order of section 1c (gate-token < owner < { roster, commit-lock <
  gate-mutex < log-queue, wait-lock, lifecycle, arena-pins, kernel < extent < log-queue, mux-loop,
  feed/pull }, synchronized tables as leaves); every syntactic nesting of `with-mutex` (and of a
  call to a function annotated "takes LOCK") must respect it; a nesting the check cannot classify is
  refused; an owner acquisition outside `fnn-owner-gated` must be in the declared list of four.
- R1b UNLOCKED CROSS-THREAD STATE is declared: a slot or global written by one thread and read by
  another with no lock is listed with its justification (word-sized, single writer, polled); the
  check refuses an unlisted one and a listed one with two writers (`retire` at :4724 vs :4778,
  `*fnn-extent-stats*` at :4298, `dir-pending` are today's findings).
- R6 NO SHARED LOCK ON THE CALL PATH: `fnn-call` and everything it calls take no lock and touch no
  `:synchronized` table except the declared read-mostly spec cache; the trap's per-call table is
  refused by name.

Report-first for one batch (the expected findings are F1, r67 F2, and whatever R1/R5 find that no one
has read), then fail-closed in `make check-fast` with a shrink-only baseline, like
owner_globals_check. Honest limit: the classification is syntactic; a function the check marks BOTH
and cannot resolve is a refusal to be resolved by an annotation, never a guess.

### 6.2 Which existing books already ARE pieces of the model (the HM is a composition, not a rewrite)

| HM component | the book that is it today | what the HM adds |
|---|---|---|
| SM, the serial reference | `fn-own-step`/`-run`, `fn-ocfg-step`/`-run` (books/owner.lisp, owner-config.lisp) | nothing; the section applies it |
| the section preserves the relation | books/owner-host-relation.lisp (COVERAGE), owner-retain-carried.lisp | the run over a quantum's event list |
| the gate / section order | books/owner-scheduler.lisp, owner-commit-steps.lisp, owner-commit-pipeline.lisp, owner-time-model.lisp | the admitted order is the linearization |
| the reader's view under a barrier | books/owner-reader-view.lisp | its event sequence becomes HM labels |
| issued reads: begin / cancel / complete / late / stale / fault | books/page-read-ownership.lisp, page-read-executor.lisp, page-read-direct.lisp (+ ledger, pool-state) | retirement interleaved: `fnn-extent-close` as a label |
| off-lock readers vs retirement | books/arena-reader-pins.lisp, response-plan-pins.lisp | sections that pin and release interleaved with swaps |
| asynchronous completions with generations | books/owner-time-bars.lisp (fn-otb), owner-commit-pipeline.lisp | the syncer as a label pair |
| the immutable plan, windows, cursor quanta | books/served-plan.lisp, served-plan-cursor.lisp (`fn-splan-cw-drain-is-the-expanded-reply`) | many connections' renders interleaved with sections |
| the cold line's answer by name | books/owner-cold-line.lisp, fn-otb-dependency-step | the deadline as recorded time in the schedule |
| timers as events | books/public-exposure*.lisp (fn-exp-charge, -idle; `fn-exp-effects-scan`) | the render loop's written replies as the exposure's "answered" (the idle-deadline fix is a model edit) |
| the swap's enabling condition | books/owner-reclaim-pass.lisp (`fn-orcp-swap-word`) | a label whose guard is the pin count; T3's counter-model |
| crash at a cut | books/byte-store-*.lisp, store-log-crash.lisp, recovery-refinement-concurrent.lisp | the cut as a label with the section prefix |

Missing: the one book that composes them (fn-hm-), its invariant, and T1.

## 7. Findings along the way (each verified in source; owners to be named by the coordinator)

- F1 `fn-pgs-fill-realize` (host/native/extent.lisp:1145-1170) preads a page file with no issued row
  and no lease; the fd is looked up under the extent lock and used after it. Safe today only
  because its callers run at the open or under the export's generation pin; nothing checks it.
  (def-holder F1 found the same.)
- F2 A response pin's lifetime is the CLIENT's: the pin is taken in the read's section (owner.lisp:4549)
  and released when the socket drains the plan (mux.lisp:274, 505); the reclaim swap waits on the
  reader count (:5747) for 8 yields, then defers. One client that stops reading its window holds a
  generation and starves every swap. The swap's own tolerance (`:readers` -> `DEFERRED-READERS`)
  makes it a named deferral, not a hang; still a liveness defect to state and decide (pin only plans
  with a cursor; or let the swap re-pin cursors as `fn-orcp-repin-conn` does for connections).
- F3 No tool checks the lock order; it is in comments (owner.lisp:141, :4270, :4538) and in reading.
- F4 A-HOST (`fn-assume-host-report`/`-events`, books/assumptions.lisp:154) is cited by no theorem;
  PRF-1234 cites it for "thread/mutex/table fidelity", which its constraint does not say.
- F5 planning/interfaces.json reports `raw_dispatched: []` while host/allocation-epoch-host.lisp:116,
  :120, :124 declare `:raw-with`; interface_emit --check passes, so either the emitter skips that
  file or the entries are not in the image world: resolve before the next raw entry lands.
- F6 `*fnn-entry-guard-specs*` is filled lazily by whichever thread calls first (io.lisp:1278); it
  is synchronized now, after an unsynchronized version stopped the owner under load. The spec cache
  belongs to image build time (fill from the world once; no lock at all on the call path).
- F7 The crash-cut registry is mirrored by hand at host/native/owner.lisp:5515 (`+fnn-reclaim-cuts+`
  vs `*fn-orcp-cuts*`) and `fnn-log-at` validates no name (def-holder F2); native_program_check walks
  two of the six durable programs.
- F8 Blocking I/O under the owner mutex is SYSTEMATIC, not an exception (section 1c's list): the
  inline commit of logical connections runs the batch's pwrite + fdatasync in the quantum; the seal
  preallocates and fdatasyncs; the FNFD feed appends and fsyncs; rotation renames; retired extents
  close; every cache miss of a quantum without the no-I/O binding preads synchronously under
  owner+extent. HST-023/HST-033 describe the served POST's barrier (the syncer) and the greeting /
  capture; the rest of the tree does not match the prose. Each site is a decision (declared commit
  point or defect) the discipline check forces to be made by name.
- F9 The reclaim pass reads owner state OFF the mutex: `(fnn-owner-core 'fn-owner-orcp-key)` and
  `'fn-owner-orcp-salt` at owner.lisp:5738/:5741 run on the control-client thread between the capture
  and the swap sections, reading `*the-live-state*` while quanta mutate it. Benign if those globals
  are constant after the open; nothing says so.
- F10 Two-writer races on unlocked state: `retire` is written under the roster (:4724) and unlocked
  by the accept thread (:4778); `*fnn-extent-stats*` is incremented under the owner alone at :4298
  and under the extent lock elsewhere; the log's `dir-pending` (io.lisp:7403-7415) is read and
  cleared by three threads with no lock (lost only if two rotations overlap a make-durable).
- F11 Threads that die silently: the service-log writer has no handler-case (a fault stops logging;
  lines drop by ACL2's bound; the join answers :joined); the extra accept threads (owner.lisp:5934)
  and the web face (web-host.lisp:312) handle socket-error only and die on anything else without
  fault-service. R4's registry makes each thread's fault policy a declaration.
- F12 P10's keystone `fn-bs-recover-program-keeps-relation-at-every-cut` is over the per-file
  recovery program, unreachable since the log format (books/byte-store-programs.lisp:236); the served
  open's program is `fn-lg-open-program`; the marker program's source is gone; planning/current.md's
  P10 row needs re-pointing at the log route's theorems (and PRF-1212's MODEL-LEVEL status named).
- F13 The hypothesis gap at the first link: P2, M6 and P8's reference equalities are stated under the
  static `fn-own-relation`; the host carries `fn-lgoc-invariantp` (`fn-ocl-relation` and
  `fn-cstp-carriedp`); no theorem derives the former from the latter. (section 1a.)
- F14 Eleven host installers of `fn-owner` are outside books/owner-host-relation.lisp's COVERAGE
  table (section 1a's list); the def-carried row covers the open and three prepares.
- F15 `reach --strict 0` means 0 unbaselined of 364 unreached events; the reports should print the
  three numbers.
- F16 Of the 34 reserved threads (host.md:536) the syncer and the exporter are transient and not in
  the "12 fixed"; the reservation arithmetic should be derived from the thread registry (R4), not
  prose.

## 8. For the reconciliation with Astra

Where I expect disagreement, and what would change my mind:
- Astra may put the model first (its "fallible-I/O rows" framing: every completion of an issued
  read preserves identity and ownership). I put the check first because the race was a host line
  outside the model, not a model gap; a convincing argument that the check's rules cannot be stated
  without the model's labels would reorder 1 and 2 (I think the opposite: the rules are what
  page-read-direct's header already says in prose).
- Whether T1(a) should be stated as linearizability (exists a serial order) or as the stronger
  "the section order is the order". With one mutation owner the second is true and simpler; if a
  second mutation owner is ever planned (a per-group writer), the weaker form is the one to keep.
- Whether `:section` belongs on def-entry or on a separate `def-section` that names entries.
- What A-HOST-IS-THE-MODEL may honestly claim as evidence (a check on the text + the image's load
  identity) and whether ember accepts that a bridge is evidence, never a proof.

## 9. DECISION

PENDING: reconciliation (decisions/README.md step 3). The coordinator decides after Astra's answer is
beside this one. No code until then, except tools/lock_discipline_check.py in report-only mode
(inventory tooling: it produces the findings list of section 7 mechanically and is useful whichever
way the design goes).

## 10. Reconciliation with Astra's answer (written after reading
## decisions/whole-system-correctness-astra-2026-10-03.md; every "verified" below was re-read in source)

### 10.1 Where I now agree (ADOPT)

- A1 THE OBSERVATION MODEL. Astra's section 5.1 (trace refinement of a stateful snapshot reference:
  the pin/acquire is linearized, later commands are evaluated against the retained view until a
  repin; observations are per-connection byte PREFIXES plus the four outcome classes plus an
  abstraction of durable content plus resource/lifecycle events; the matching map is
  prefix-consistent, a forward simulation, never "a fresh serial history after each reply") is the
  careful statement of my T1. We do not differ on substance: my "the section order is the
  linearization" IS a forward simulation whose reference state includes each connection's pinned
  view (`fn-own-read` evaluates against it). Astra's framing adds what mine left implicit: partial
  output on reset/crash is a prefix; operation identifiers and continuations across quanta are part
  of Obs; a timeout is not a refusal. ADOPT Astra's Obs and wording for T1; keep "section order" as
  the simulation's matching, not as a claim that every read sees the newest archive.
- A2 TYPED CAPABILITIES. OwnershipSafe as capabilities `(kind, object, incarnation, generation,
  holder)` with acquire/retain/transfer/cancel/settle/refund/close receipts (Astra 5.3), instead of
  my per-protocol list. My R3's "issued row / window lease / file pin" are its kinds; `fn-arpn` and
  `fn-rpin` stay lemmas inside it. ADOPT; it is the H component of the HM.
- A3 FAILURE SCOPE IS PART OF THE PROTOCOL ("mutex release is not failure containment"). I MISSED
  THIS CLASS ENTIRELY. Verified: `fnn-owner-committer-loop` (owner.lisp:3704-3706) catches
  `fnn-store-error` as "stopped" while `fnn-store-fault` and `fnn-store-indeterminate` are its
  subclasses (io.lisp:77, :92), so a fault from the off-owner `fn-otb-issue` (:3460) ends the
  committer with no fence and a batch left in flight (= sweep S016); `fnn-owner-release-extents`
  (:5011) and the publisher (:5130, :5141) log and continue on serious conditions; the reclaim swap's
  gated body (:5745-5768) is not inside `fnn-owner-shared-action-locked`, so an indeterminate after
  the install escapes with STOPPING nil (= r71 F1, S017); the mirror image is the sweep's
  node-stopping class (S001/S004/S006/S007/S010/S036: a connection-local or capacity event reaches
  `fnn-owner-fault-service`). One defect kind, two symptoms: the exception HIERARCHY decides the
  process outcome in hand-written handler clauses. ADOPT as rule R7 (10.5) and as Astra's step 6.2.
- A4 B2 AND B3, verified: `fnn-mux-adopt` (mux.lisp:1378-1398) registers the socket under the roster,
  releases it, then pushes into the loop's inbox under the mux lock with no "loop still alive"
  check, while `fnn-mux-stop-loop` (:1306-1335) drains the inbox once and closes the wake fds -- the
  push can land after the final drain (r71 F9, S021). `fnn-owner-publish-captured` (owner.lisp:5147-5150)
  deletes itself from the worker roster, THEN unpins (:5152) and calls `fnn-owner-maybe-publish`
  (:5162), while the stop's quiescence predicate is "workers empty" (:4804-4811, :6258-6285) (r71
  F10, S018). Both absent from my inventory. ADOPT Astra's 6.1 as the first GENERATED protocol.
- A5 "GENERATING MUTEX ACQUISITION ALONE IS INSUFFICIENT; generate capture -> execute -> settle and
  admission/stop protocols; check the hand-written leaves" (Astra section 7). This refines my (ii):
  def-entry's `:section` covers only the one-shot entry; the six off-lock programs and the lifecycle
  need Astra's declaration language (operation / state / actor / locks / inputs / outputs /
  resources / blocking / workflow / failure / persistence / cost / callbacks). def-entry already
  carries operation, state, persistence, cost (lanedumps/def-entry.md); the missing fields are
  actor, locks, inputs/outputs, resources, blocking, workflow, failure, callbacks. ADOPT the
  vocabulary; one source of truth with definterface/def-carried, as Astra says.
- A6 COST AS A COMPANION THEOREM with the blocking classification (pure | bounded-compute |
  may-allocate | may-block-I/O | await) per leaf, and "no O-held phase invokes a may-block leaf
  except declared maintenance modes". This is my R2 + T2 stated better. ADOPT the classification;
  R2 becomes "a section's reachable leaves are all declared non-blocking or the section is declared
  `:io`".
- A7 CRASH BETWEEN EVERY ABSTRACT HOST ACTION, not only `fnn-at` cuts: every C action either is a
  named cut or stutters to one (Astra 5.2). ADOPT for T1(c).
- A8 Astra's measurements 1-12 (section 9) are the acceptance witnesses for steps 1-3 below. ADOPT.
- A9 Two findings of Astra's I did not have, verified: the STATEMENT BARRIER runs
  `fnn-log-commit-open-batch` synchronously inside the batch quantum (owner.lisp:2440-2458), a
  second deliberate I/O-under-owner path beside the inline commit; and `*the-live-state*` is setf
  outside the owner in the staged control-turn epilogue (owner.lisp:1864). Also the S/O split of the
  log spare (G4), hons/memoize thread safety (G2), and `with-pinned-objects` being GC pinning, not
  ownership. Added to section 1c's trusted-base list.

### 10.2 Where I still differ, and why (HOLD)

- H1 ORDER OF THE FIRST STEP. Astra: a generated connection handoff/stop protocol (6.1) first; a
  checker first "is a distraction if it only greps for with-mutex, prints a large baseline of
  exceptions, and declares the problem solved". I agree with the warning and hold the order, for
  the tally in 10.4: the check with the rules of 10.5 catches 25 of this week's 30 defects
  statically; the handoff/stop protocol catches 4, and of those B2 is the one the check cannot catch
  reliably (an ordering race across two locks). The check is not the fix for any of them; it is
  the ratchet that refuses the NEXT instance of each class while the generated protocols remove
  the existing ones, and it runs in every push from the day it lands. Astra's "closed-scope
  checker over the migrated enclave" and my "whole-host check with a shrink-only baseline" are the
  same tool with two scopes: strict inside the enclave, baselined outside, the baseline only
  shrinking. The coordinator has in any case already queued the check as Astra's own t41 after t40.
- H2 "A STATEMENT EVERY REPLY EQUALS THE REFERENCE AT SOME SERIAL ORDER IS INADEQUATE." Agreed, and
  I did not propose it: the reference state carries the pinned views, the order is the section
  order, and continuations keep their response hold. What I HOLD is that with one mutation owner
  the linearization is the section order and need not be existentially quantified; if a second
  mutation owner is ever planned, Astra's weaker form is the one to keep. No substantive
  disagreement remains once A1 is adopted.
- H3 WHAT A-HOST-IS-THE-MODEL MAY CLAIM. Astra: "Do not put H -> C into a vague A-HOST hypothesis and
  declare victory." Agreed; my section 5 row says the same (evidence: the check on the source, the
  image's load identity, the natives; never a theorem). HOLD the row's existence: the realization
  relation must be NAMED somewhere a claim can cite, with its evidence listed, precisely so that it
  is not vague. Retire the unused `fn-assume-host-report`/`-events` encapsulate either way.
- H4 EFFORT. Astra's envelope (4-8 books, 5-12k lines, 4-12 engineer-weeks for the core, excluding
  BP/ideal ports and platform qualification) supersedes my 3-5 weeks, which covered the HM book
  alone. ADOPT Astra's numbers; HOLD that the first theorem (T1(b), issued reads vs retirement over
  all schedules) is a 1-2 week slice that should land before the rest is estimated again.

### 10.3 What each answer missed (verified in source)

Astra's answer missed (each verified by me):
- The hypothesis gap at the first link: P2, M6, P8 are stated under the static `fn-own-relation`; the
  host carries `fn-lgoc-invariantp`; the only bridge, books/owner-served-carried.lisp:156-171, goes
  the OTHER way (`fn-own-relation` implies the carried conjuncts). Those keystones must be restated
  under the carried relation, as `fn-scar-ocfg-read-span-is-reference-under-ocl-relation` is (F13).
- P10's keystone is over the per-file `fn-bs-recover-program`, which books/byte-store-programs.lisp:234-240
  says is unreachable (every opened store is format 9; the open is `fn-lg-open-program`); the marker
  program's source is gone; planning/current.md's P10 row is stale (F12). Astra cites :495 as a
  live connection.
- Eleven host installers of `fn-owner` outside owner-host-relation.lisp's COVERAGE table (F14).
- `reach --strict 0` is 0 UNBASELINED of 364 unreached events (F15); interfaces.json's
  `raw_dispatched: []` against host/allocation-epoch-host.lisp:116-124 (F5).
- The ACL2 side of the idle defect: `fn-exp-idle` (books/public-exposure.lisp:793-803) compares
  `entry-last`, which only a step's charge/observe advances (owner.lisp:4515, :4621); the cursor
  quantum (:514-527) and the renders never touch exposure, so after a reply longer than the idle
  limit the first idle tick closes the connection. Astra's B4 is the host-timer half (busy-poll);
  the ACL2 half is open too, and Astra's "idle rearming exists on ordinary completion" is the host
  timer, not `entry-last`.
- Two-writer state: `retire` is written under the roster at :4724 and under the OWNER at :4778 (two
  different locks for one slot, read unlocked at :4478, :4684, :4759); `*fnn-extent-stats*` is
  incremented under the owner alone at :4298 and under the extent lock elsewhere (F10).
- The service-log writer thread (io.lisp:1047-1067) has no handler-case; a serious condition outside
  `fnn-log-write-item`'s own `(error () :failed)` escapes the thread, and the image runs with
  `--disable-debugger` (build.lisp:622; the sweep's S030 skeptic note), so the process exits 1,
  outside the 3/4 fence discipline (F11).
- The sweep's answer to Astra's measurement 5: `fn-pgs-fill-realize`'s loaded callers are
  `fn-store-sco-image-open` at the open (io.lisp:2631, before serving) and the history-records
  readers of `store export` and the publication, which hold the arena-generation pin only; nothing
  holds a file lease (section 1c).

My answer missed (each Astra's, verified by me in 10.1): the exception-routing class (A3) and
therefore the sweep's whole node-stopping family; B2 (adopt vs stop); B3 (roster self-removal); B4
(timer predicate); the statement barrier under the owner; the spare/rotation S-vs-O split; hons and
memoize thread safety as an open question; `with-pinned-objects` not being ownership; the staged
`*the-live-state*` write off the owner; that `ideal.lisp` is a skeleton and must not be cited as the
UC layer. My rule set had nothing for handlers, lifecycle or actors; 10.5 adds R7-R9 for them.

### 10.4 Which first step catches more of this week's defects (the coordinator's question)

Classes: CHECK = the lock-discipline check of 10.5 (static, fail-closed, R1-R9); HANDOFF = Astra's
6.1 (generated admission/adopt/stop/join with receipts); SCOPES = Astra's 6.2 (generated failure
scopes); CAPS = Astra's 6.3 (one capability interface); MODEL/HARNESS = the HM and its schedules.

| defect set | CHECK catches | HANDOFF catches | needs |
|---|---|---|---|
| r31 F1 (no row across the pread), F2 (orphan threads) | 2/2 (R3, R4) | 0 | CAPS removes the class |
| r67 F2 / S022 / S010's cold half (I/O in a section) | 1/1 (R2) | 0 | 6.6 removes the class |
| r71 F1 F2 (unfenced gated bodies, swallowed uncertainty) | 2 (R7) | 0 | SCOPES |
| r71 F4 F6 (I/O under extent / owner) | 2 (R2) | 0 | 6.6 |
| r71 F5 (inline commit in a :reader quantum, batch in flight) | 1 (R2 + the class rule R9) | 0 | MODEL (the pipeline invariant the host violates) |
| r71 F7 F8 (a cold await parks an I/O loop; cold-reap parks the accept/SIGTERM loop at the gate) | 2 (R9 per-actor blocking/gate rules) | 0 | MODEL (actor structure) |
| r71 F9 (B2 adopt after drain) | 0 (an ordering race across two locks: R8 flags the shape, cannot prove it) | 1 | HANDOFF |
| r71 F10 (B3 roster self-removal), F12 (NIL in the roster) | 2 (R4: registration is the last act; the registered value is the thread) | 2 | HANDOFF |
| r71 F3 (TLS suffix fault: a missing yield), F11 (B4 timer predicate), F13 (unadmitted sockets unbounded) | 0 | 0 | MODEL/HARNESS (trace witness; timer as event; admission capacity) |
| r71 F14 F15 (cost; a host decision) | 0 | 0 | def-entry :cost; "ACL2 owns the word" |
| sweep node-stopping: S001 S004 S006 S007 S036 (connection-local or capacity -> fault-service); S015 S016 S017 S019 S020 S023 S028 S030 S031 (fault/indeterminate swallowed or misreported) | 13/14 (R7; S001's NIL-from-accept half is input validation) | 1 (S021 only) | SCOPES removes the class |
| TOTAL of the 30 | 25 | 4 | |

The check first, then. But the honest reading of the table is Astra's point: the check REFUSES the
classes, it does not REMOVE them; 13 of the 30 are one class (exception routing) that Astra's
generated failure scopes remove by construction, and the only defect the check cannot see (B2) is
exactly the one Astra's first protocol fixes. So the reconciled order is the check, then Astra's
6.1 and 6.2 as ONE generated protocol, then the capability interface with the model's first theorem.

### 10.5 The reconciled rule set (R1-R9, my numbering; for the merge with Astra's)

- R1 OWNER STATE UNDER THE OWNER (unchanged): `fnn-owner-core`, `fnn-core-state`, `fnn-core-buffer-state`,
  `fnn-live-stobj`, `fnn-live-octets`, `*the-live-state*` reads and writes, and every slot/global
  annotated `guarded-by: LOCK`, only in SECTION context or under LOCK; unannotated shared state
  refused. (Findings today: owner.lisp:5738/5741, :1864.)
- R1b DECLARED UNLOCKED STATE (unchanged): one writer, word-sized, polled, listed; two writers or
  two locks for one slot refused (`retire` :4724/:4778; `*fnn-extent-stats*` :4298; `dir-pending`).
- R2 NO BLOCKING LEAF UNDER EXCLUSION (generalized per A6): every leaf is classified pure |
  bounded-compute | may-allocate | may-block-I/O | await (the syscall and FFI leaves by a declared
  table; ACL2 entries by whether their call-graph closure reaches an attached realizer); a section,
  or any `with-mutex` body, that reaches a may-block or await leaf is refused unless declared `:io`
  (the commit points: the swap's install and barriers, START's seal, the statement barrier) or the
  realizer is bound no-I/O. (Findings today: section 1c's list; r71 F4, F5, F6; S022; S014.)
- R3 AN OFF-LOCK READ HOLDS A TYPED CAPABILITY (per A2): `fnn-extent-pread`, `fn-durable-realize-*`,
  `fn-pgs-fill-*` outside a section are reachable only from a function holding an issued-row token,
  a window lease or a file pin of the SAME object kind; a generation pin does not satisfy a file
  borrow. (Finding today: `fn-pgs-fill-realize`.)
- R4 EVERY THREAD IS DECLARED: each `make-thread` names its registry slot, its join site, its fault
  policy (R7) and the rule that de-registration is the thread's LAST shared action; the registered
  value is the `make-thread` result. (Findings: B3 = r71 F10, F12; the log writer; the extra
  accept and web threads.)
- R5 LOCK ORDER (unchanged, with the composite order of section 1c); the four direct owner
  acquisitions declared.
- R6 NO LOCK ON THE `fnn-call` PATH except the declared read-mostly spec cache, which moves to image
  build time.
- R7 FAILURE SCOPE IS DECLARED (new, Astra's class): every `handler-case` / `ignore-errors` in a
  thread's top level, a gated body or a section wrapper declares its scope (connection-local |
  shared-fault | durability-uncertain | private-job); a clause catching `fnn-store-error` or
  `serious-condition` must be preceded by clauses that route `fnn-store-fault` and
  `fnn-store-indeterminate` to the fence (`fnn-owner-fault-service`, exit 3/4) unless the scope is
  private-job; a connection-local scope may route only the connection-local classes to the
  connection; a gated body that performs a durable effect must run inside
  `fnn-owner-shared-action-locked`. Refuses by name. (Findings: S015-S020, S023, S028, S030, S031,
  B1 = S016, r71 F1 F2; and the inverse S004 S006 S007 S036.)
- R8 HANDOFF LIFECYCLE (new, partial): a resource transferred between two locks (roster -> mux inbox;
  spare -> rotation; C done-table -> mux arrived) must be admitted under the RECEIVING lock with a
  lifecycle check (open/draining/closed) or go through a generated protocol; a push into a queue
  with no such check is refused. Flags B2's shape; cannot prove its absence: that is HANDOFF's job.
- R9 ACTOR RULES (new, Astra's actor language): per declared actor (accept/SIGTERM loop, mux loop,
  committer, syncer, cold worker, publisher, exporter, control client, feed/pull worker): which
  gate classes it may enter (the accept loop: none), which leaves it may block in (an I/O loop: no
  await on a cold read), which sections it may run (a :reader quantum: never the commit pipeline).
  (Findings: r71 F5, F7, F8.)

### 10.6 The reconciled first three steps

1. THE CHECK (t41, Astra's, scope = R1-R9 above): report-first over the whole host, then fail-closed
   in `make check-fast` with two scopes -- strict inside the migrated enclave (Astra's closed scope),
   a shrink-only baseline outside. Acceptance: the report reproduces section 1c, 10.3 and 10.4's
   findings mechanically; r31 F1/F2's old code (git show) and `fn-pgs-fill-realize` fail R3; the
   committer handler fails R7; `fnn-mux-adopt` is flagged by R8; a reverted fix re-fails. ~1 week.
2. ONE GENERATED LIFECYCLE + FAILURE-SCOPE PROTOCOL (Astra's 6.1 and 6.2 merged, Astra owns it, with
   the t43/t45 close-fence work as its first consumer): a declaration per actor and per section
   carrying `failure:` and `workflow:` (capture -> execute -> settle) from which the wrapper
   (`fnn-owner-gated`/`-serialized` become generated), the thread registration with its receipt, the
   admit-to-live-inbox-or-close handoff and the stop/join are emitted; the exception hierarchy is
   mechanically bound to the scopes so a parent catch cannot consume fault/uncertain. Acceptance:
   Astra's measurements 1, 2, 3 as witnesses (forced adopt-vs-drain both orderings; injected fault at
   `fn-otb-issue` and after START; publisher paused after roster removal); R7/R8/R9 report 0 inside
   the enclave; the 13 node-stopping sweep findings close by construction. Days to two weeks.
3. THE CAPABILITY INTERFACE + THE MODEL'S FIRST THEOREM (Astra's 6.3 + my rank 2, one lane): the
   typed capability `(kind, object, incarnation, generation, holder)` with its receipts as the HM's
   H component; `fn-pgs-fill-realize`, the publisher/exporter captures and the response pins moved
   onto it; T1(b) proved over ALL schedules (issued reads and generation pins vs retirement, close
   and reclaim swap interleaved), reusing fn-pio/fn-pxe/fn-arpn/fn-rpin as lemmas; R3's kinds are
   its bridge. Acceptance: Astra's measurements 5 and 6 (pause after fd capture while retirement runs;
   cancel-then-close stays blocked until physical return); a page fill cannot escape with a naked
   fd; the HM's first keystone certified with teeth. 2-3 weeks.
Then, in Astra's order: 6.4 (compose the actor actions with the owner chain = my HM book proper and
T1(a)), 6.5 (every action a cut = T1(c)), 6.6 (nonblocking phases and cost: the inline commit, the
statement barrier, the cursor miss, the feed fsync, the timer predicate), 6.7 (every module, then
one qualified candidate), with the HM as tools/resilience's schedule generator and oracle alongside.

### 10.7 Open for the coordinator and Astra to settle

- Whether R7-R9 belong in the SAME tool as R1-R6 (my lean: yes, one reader, one baseline, one
  report; Astra may prefer the scope checker to live with the generator).
- Whether step 2 is one declaration family or two (lifecycle vs failure scope); I merged them because
  the committer/publisher/web findings need both at the same site.
- The name and evidence list of the realization row (H3): A-HOST-IS-THE-MODEL or Astra's "H -> C";
  what it may cite.
- Whether `fn-own-relation`-based keystones (P2, M6, P8) are restated under the carried relation now
  (my lean) or after step 3.

## DECISION (coordinator, 2026-10-03; recorded by codex-liaison-11; ember may overturn)

Settled without a third round, because Codex hit its usage limit (until 2026-10-08 18:49) before Astra's final-position
round could run. The two positions on record are this file's section 10 (the COMPOSITION deputy) and Astra's round 2,
appended to decisions/whole-system-correctness-astra-2026-10-03.md ("Round 2: Astra's reconciliation").

- AGREED: the first landing is ONE lock-discipline check. Astra adopted it (round 2, D1, with a bounded claim: zero
  unbaselined findings is not concurrency safety). Rules: R1-R9 of section 10.5, merged with Astra's round-2 section 4.
- ORDER (ember, 2026-10-03): PARALLEL, not sequential.
  - New Opus lane LOCK-CHECK implements the check (former t41).
  - New Fable deputy FAILURE-SCOPE owns the generated lifecycle/failure-scope protocol (section 10.6 step 2). Its first
    concrete consumer is t45, briefed at build/lanes/codex-t45-fence-boundary/build/codex/t45/.
  - This deputy starts the host-model book with T1(b), and restates P2/M6/P8 under the carried relation.
  - OWNER-OFFLOCK fixes blocking-under-lock with one queued-work+receipt helper.
- OPEN: Astra's remaining HOLDs. They are recorded and revisited when Codex returns:
  - its top theorem's linearization;
  - the host-is-model assumption;
  - lock order;
  - bugs versus missing declarations.
  Also open: the 10.4 tally recount and the four 10.7 points, for which Astra's final-position brief is ready
  (build/lanes/codex-w01-wholesystem/build/codex/w01/ROUND3.md). Nothing being built now forecloses any of them.
