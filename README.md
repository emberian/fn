# fn

`fn` is a persistent event log, NNTP server, and durable stream engine built with ACL2-verified components, a Lean 4 metatheory, and a translation-validation bridge under development. End-to-end assurance remains incomplete; the [assurance audit](docs/design/ASSURANCE-AUDIT-20261113.md) identifies the missing proof and implementation links.

Current integration evidence and unfinished implementation/proof work are tracked in
[`docs/design/FINISH-20261113.md`](docs/design/FINISH-20261113.md).

Every protocol, framing, storage, accounting, and authorization decision is owned by guard-verified `:logic`-mode ACL2 functions operating over a single-threaded nested stobj (`fn2-core`). A minimal SBCL + C host adapter (`host/`, ~1.9 KLOC) performs only non-blocking socket and file I/O (`epoll`/`kqueue`, `pread`/`pwrite`, `fsync`/`F_FULLFSYNC`, Unix peer credentials, and BLAKE3 FFI) and feeds bounded completion batches into `fn2-turn`.

---

## 1. Assurance Posture

- **ACL2 owns every decision (`books/`, 201 books, ~91 KLOC):** Wire framing, non-Lisp-reader protocol parsing, capability/generation pool slices, fair calendar scheduling, BLAKE3-authenticated epoch-fenced journal commits, LSM ordered-run indexing and bounded compaction, durable principals and grants, and exact wire reply bytes are computed exclusively inside ACL2. Neither the Common Lisp host nor the Python CLI recomputes or overrides values decided by `fn2-core`.
- **Zero axiomatic shortcuts:** The book closure contains **zero `skip-proofs`**, **zero `defaxiom`**, **zero trust tags (`defttag`)**, and **zero `:program`-mode runtime functions**. External assumptions (such as cryptographic collision resistance) are isolated as `encapsulate` specifications with explicit local witnesses.
- **Recorded obligations (`books/owed.lisp`, [`docs/OWED.md`](docs/OWED.md)):** Top-level claims are registered in the guarded world table `fn2-squares` via `defthm-owed` and discharged via `fn2-owed-discharge`. Registration is not proof. Named executable witnesses are checked by `fn2-assert-owed-teeth`; the current machinery does not itself establish that they witness the full antecedent or a meaningful hypothesis removal. Unproved keystones remain `:owed`. The generated ledger needs a fresh export from the converged certified world.

---

## 2. Five-Layer `fn2-core` Stobj Architecture

At assembly time (`books/core.lisp`, `books/assembly*.lisp`), `make-event` synthesizes `(defstobj fn2-core ...)` over `*fn2-core-children*`—**57 child stobjs** (31 domain tables declared via `defcorechild` plus 26 generated per-machine state tables)—together with the rectangular read-over-write frame matrix across all children.

Books are organized into five strict acyclic layers enforced by `(fn2-book-layer :a .. :e)`:

| Layer | Scope | Key Books & Docs |
| :--- | :--- | :--- |
| **`:a` — Execution & Pool** | Capability/generation byte pool (`fn2-pool`), weighted principal calendar (`fn2-sched`), host op outbox/inbox (`fn2-ops`), bounded `fn2-turn` executor, sticky stop-reason boundary | `books/pool*.lisp`, `books/sched.lisp`, `books/core.lisp`, `books/executor.lisp` — [`docs/a-pool-host-sim.md`](docs/a-pool-host-sim.md) |
| **`:b` — Durability & Crash** | Crash-cut model, BLAKE3 Merkle journal commits (`fn2-commit`), dual-anchor writer-epoch fencing, extent allocator (`fn2-extents`), bounded startup/recovery (`fn2-boot`) | `books/commit*.lisp`, `books/boot*.lisp`, `books/recovery*.lisp` — [`docs/b-durability.md`](docs/b-durability.md) |
| **`:c` — Ordered Runs** | Write-ahead overlays, immutable sorted runs, prefix-compressed pages, fold reductions (`:unique`, `:latest`), Message-ID/content-identity engine, background sealer/compactor | `books/runs*.lisp`, `books/folds*.lisp`, `books/identity.lisp`, `books/machines-c*.lisp` — [`docs/c-ordered-runs.md`](docs/c-ordered-runs.md) |
| **`:d` — NNTP & Transactions** | Declarative RFC 3977 / 5536 / 5537 grammar, streaming header scanner, connection/cursor/upload/transaction state machines (`fn2-conn`, `fn2-cursor`, `fn2-upload`, `fn2-txn`), account ledger | `books/nntp-grammar.lisp`, `books/conn*.lisp`, `books/upload*.lisp`, `books/txn*.lisp`, `books/accounts*.lisp` — [`docs/d-machines-nntp.md`](docs/d-machines-nntp.md) |
| **`:e` — Streams & Authority** | `FNCT` framed local control/consumer carrier (`fn2-ctl`, `fn2-cns`), `fncu` durable cursors, parked edge waiters, served principal directory and CAS grant chains (`fn2-auth`) | `books/consumer-codec.lisp`, `books/cns*.lisp`, `books/authority*.lisp` — [`docs/e-surface.md`](docs/e-surface.md), [`docs/design/AUTHORITY-20261105.md`](docs/design/AUTHORITY-20261105.md) |

Because lower layers cannot include higher layers, upward callbacks (`fn2-turn` dispatching into layers `:b`–`:e`, or commit replay notifying higher-layer indices) are declared via constrained `encapsulate` hooks with explicit child-footprint (`KIDS`) and well-formedness contracts, and bound at `books/assembly-callbacks*.lisp` via `defattach`.

### Core Engineering Laws

1. **Zero Lisp reader on untrusted input:** External network and disk bytes reside in `fn2-pool` `(unsigned-byte 8)` slices addressed by `(slot, generation)` capabilities (`fn2-core-pool-write-frame` in `books/assembly-core.lisp` proves that writing one carved pool row preserves every other row's octets). `read` and `read-from-string` are banned from served and host paths (`tools/host_check.py --read`).
2. **Bounded per-step work, never silent truncation:** Every machine visit declares static `:bytes`, `:steps`, and `:descriptors` budgets (`fn2-turn-bounds` in `books/executor.lisp`). Operations that exceed a single quantum yield a continuation cursor and resume on a subsequent turn.
3. **Distinct `accepted`, `refused`, and `uncertain` outcomes:** Durable acceptance is emitted only after storage fence completion. Transport or crash interruptions after submission surface explicitly as `uncertain` (with idempotent 60-bit operation IDs for replay reconciliation), never as silent rollback or last-writer-wins wall-clock tie-breaking.

---

## 3. Macro & Proof-Generator Architecture

Maintaining guard proofs, stobj well-formedness (`wfp`) invariants, and `O(N²)` cross-stobj frame lemmas by hand across 57 child stobjs is intractable in raw ACL2. In `fn`, **generators are the design of record**: domain declarations expand via `make-event` into both the served stobj code and its preservation theorems, while recording canonical AST metadata in world tables (`books/declare.lisp`).

### `defcolumns` — Typed Columnar Stobj Tables (`books/columns.lisp`)
Generates unboxed parallel array fields (`:bool`, `:u8`, `:u16`, `:u32`, `:u60`, `:link`, `:enum`) inside a child stobj, emitting `wfp` and `shapep` predicates, guard-verified row readers/writers, read-over-write theorems, and `fn2-<table-name>-preserves` proof macros:

```lisp
;; books/cns-edges.lisp
(defcolumns fn2-cns-edges
  ((used :bool) (stream :u60) (waiter :u32) (gen :u60) (from :u60)
   (enext :link) (eprev :link)
   (bhead :link) (btail :link) (bcur :link) (bpos :u60) (bpend :bool)
   (bpnext :link) (bpprev :link))
  :extra-fields
  ((fn2-cns-free-head :type (unsigned-byte 32) :initially 4294967295
    :why "The free list of released edges, threaded through ENEXT.")))
```

### `defmachine`, `defmachine-arms`, and `defcost` — Total Step DSL (`books/machines.lisp`, `books/machine-arms.lisp`, `books/arms.lisp`)
Each state machine declares its phases, row fields, resource holdings (`:holds`), and per-visit `:budget`. Phase bodies are written in a total step language (`:let`, `:if`/`:cond`, `:set`, `:next`, `:do`, `:issue`, `:commit`, `:wake-row`, `:charge`, `:yield`, `:stop`, `:goto`) whose primitive operations carry `defcost` footprint and effect contracts. `defmachine-arms` compiles each arm into a guard-verified `fn2-core` transformer, automatically discharging child-frame (`KIDS`), resource-accounting, and budget-bound obligations:

```lisp
;; books/boot-kind.lisp
(defmachine fn2-boot
  :states (:free :prepare :write :write-result :read :read-result :verify :advance
           :anchor :recover :recover-wait :epoch :epoch-fence :epoch-result :release :ready :failed)
  :fields ((pending :u32) (stopped :bool) (pool-slot :u32) (pool-gen :u60)
           (rx-slot :u32) (rx-gen :u60) (create :bool) (image-size :u60) ...)
  :holds ((:prepare :storage-window) (:write :storage-window) ...)
  :budget (:bytes 32768 :steps 32 :descriptors 4)
  :stops (:geometry :configuration :io :anchor :recovery :epoch :bounds)
  :capacity (if (fn2-profile-get :image-boot profile) 1 0) ...)
```

### `deflayout`, `defrunschema`, and `defgrammar` — Codecs, LSM Folds, and Wire Parsers
- **`deflayout` (`books/layout.lisp`):** Compiles fixed/LEB128/big-endian binary record specs (`(:id ...)`, `:varint`, `(:octets16 N)`, `:digest`, `:enum`) into zero-allocation pool encoders/decoders paired with pure octet-list specifications (`fn2-layout-octets`, `fn2-layout-parse`).
- **`defrunschema` (`books/runs-schema.lisp`):** Declares typed LSM schemas, merge disciplines (`:unique`, `:latest`), and event-driven fold projections:
  ```lisp
  ;; books/authority-schema.lisp
  (defrunschema fn2-grant-current :id 18
    :key ((grantee (:id principal)) (right :u8) (scope :u8) (target (:id stream)))
    :value ((grant (:id grant)))
    :merge :latest
    :fold (:events ((:grant (grantee right scope target g) :set ((grant g))))
           :init :empty :coverage :history-start :observe (grant)))
  ```
- **`defgrammar` (`books/grammar.lisp`, `books/nntp-grammar.lisp`):** Compiles command syntax, line/argument caps, connection-state masks, and status-code tables directly into the served parser and reply emitter.

### `defthm-owed` and `defsquare` — Refinement Squares & Obligation Store (`books/owed.lisp`, `books/squares.lisp`)
`defsquare` binds concrete stobj transitions against pure reference specifications across the machine registry's case catalogue (`:g0`, `:g1`, `:g2`, `:route`, `:crash`, `:bound`, `:invariant`), rejecting vacuous `T` translations or unused contract roles at macroexpansion time.

---

## 4. What Role Lean 4 Serves (`meta/` — ~18.8 KLOC Handwritten + ~413 KLOC Emitted, Zero `sorryAx`)

Rather than translating ACL2 theorems into Lean as unchecked `axiom` declarations (contrast [`docs/design/LEAN-ACL2-SURVEY-20261112.md`](docs/design/LEAN-ACL2-SURVEY-20261112.md)), `meta/` consists of **~18.8 KLOC of handwritten Lean 4** (43 files covering the metatheory, deep ACL2 evaluator, and `Fn2.Arms` operational semantics and combinators) paired with **~413 KLOC of mechanically emitted Lean 4** (322 files in `meta/Fn2/Instances/` plus `Fn2/Arms/CoreValidation.lean`, generated from the live certified ACL2 world by `meta/emit/`). Every theorem is checked under `meta/AxiomCensus.lean` to depend only on Lean's standard logical foundation (`propext`, `Quot.sound`, `Classical.choice`), with **zero custom axioms and zero `sorryAx`** across 802 `#print axioms` checks in the Lean tree.

Lean 4 serves three specific roles alongside ACL2:

1. **Higher-Order Metatheory (`Fn2.Square`, `Fn2.Coherence`, `Fn2.Conservative`, `Fn2.Param`, `Fn2.TypedModel` — [`docs/design/LEAN-METATHEORY.md`](docs/design/LEAN-METATHEORY.md)):**
   ACL2's first-order logic instantiates generator correctness *per machine* at `make-event` time, whereas Lean 4 quantifies universally *over all machines, schemas, and double-categorical refinement squares*—proving paste/interchange coherence, Diamond commutation from disjoint footprints, revision conservativity across schema extensions, parametricity, and typed `BitVec`/array storage refinements (`Fn2.TypedModel`).
2. **Live Two-Kernel Translation Validation (`books/translation-validation.lisp`, `meta/emit/`, `Fn2.ACL2`, `Fn2.Arms` — [`docs/design/BRIDGE-CERTIFICATE.md`](docs/design/BRIDGE-CERTIFICATE.md), [`docs/design/BRIDGE-GENERATED.md`](docs/design/BRIDGE-GENERATED.md)):**
   `books/translation-validation.lisp` and `meta/emit/print-served-certificate.lsp` extract the live certified `fn2-turn` call graph (~12,000+ ACL2 function bodies, guards, stobj signatures, and `defattach` bindings, failing closed on any unattached stub). Lean's deep ACL2 S-expression evaluator (`Fn2.ACL2.Translation.evalExport`) and mechanical arm combinators (`Fn2.Arms`) verify **Whole-Arm Bridge Certificates** proving that evaluating the exported ACL2 `unnormalized-body` produces the exact state transitions of `Fn2.Arms` operational semantics.
3. **Independent Execution & Standalone Compilation Target:**
   Having executable operational models and mechanically bridged arm semantics in Lean 4 enables differential testing and a path to standalone verified native code generation independent of Common Lisp and SBCL.

---

## 5. Certifying, Simulating, and Running `fn`

### ACL2 Certification, Proof REPL, Simulator, and Lean Build

```sh
# Certify specific books (and stale dependencies) with the ACL2 8.7 toolchain
sh tools/certify.sh books/node-profile.lisp tests/boot-unit.lisp

# Sub-second interactive lemma iteration against a cached world
python3 tools/proof_repl.py

# Deterministic fault-injecting simulator (sim/): checks OWN, WORK, TRACE,
# ACCOUNT, IDENTITY, WIRE, HISTORY, RECOVERY, RECLAIM, DEATH, DEADLOCK, ENVELOPE
tools/acl2 < tests/sim-layer-a-a4-smoke.lsp

# Build the Lean 4 metatheory & bridge certificates and run the axiom census
cd meta && lake build && lake env lean AxiomCensus.lean
```

### Operating a Live Node (`./fn`)

After certifying `books/node-profile.lisp`:

```sh
# 1. Initialize a preallocated store image (O_EXCL; never truncates an existing file)
./fn init build/node.img --size-mb 32 --group ops.alerts --group ops.audit

# 2. Recover committed state, fence the new writer epoch, and serve both
#    TCP NNTP (--port) and the 0600 FNCT Unix-domain socket (--control-sock)
./fn serve build/node.img --port 1119 --control-sock /tmp/fn2-ctl.sock

# 3. Create durable principals and manage grants over --control-sock
./fn principal create watcher --control-sock /tmp/fn2-ctl.sock
./fn grant set watcher consume --control-sock /tmp/fn2-ctl.sock
./fn grant set watcher read ops.alerts --control-sock /tmp/fn2-ctl.sock
./fn grant set watcher append ops.alerts --control-sock /tmp/fn2-ctl.sock
./fn grant set anonymous append ops.alerts --control-sock /tmp/fn2-ctl.sock
./fn grant get watcher read ops.alerts --control-sock /tmp/fn2-ctl.sock

# 4. Register a durable consumer cursor and append/wait/read/ack over --control-sock
./fn stream register --as watcher --consumer inbox1 --cursor-file build/watcher.cur --control-sock /tmp/fn2-ctl.sock
./fn stream append --as watcher --group ops.alerts --subject "Ready" --body "hello" --control-sock /tmp/fn2-ctl.sock
./fn stream wait --as watcher --cursor-file build/watcher.cur --seconds 10 --control-sock /tmp/fn2-ctl.sock
./fn stream read --as watcher --cursor-file build/watcher.cur --control-sock /tmp/fn2-ctl.sock
./fn stream ack 2 --as watcher --consumer inbox1 --cursor-file build/watcher.cur --control-sock /tmp/fn2-ctl.sock
./fn stream status --as watcher --consumer inbox1 --control-sock /tmp/fn2-ctl.sock

# 5. List groups, post, and fetch articles over NNTP TCP (--port / $FN_PORT)
./fn groups --port 1119
./fn post ops.alerts --subject "Notice" --from "op@fn2.invalid" --body "line 1" --port 1119
./fn article ops.alerts 1 --port 1119
```

The `principal`, `grant`, `stream`, `groups`, `post`, and `article` client commands support `--json` (plus `$FN_CONTROL_SOCK`, `$FN_PORT`, `$FN_HOST` environment defaults) and preserve outcome classes at the process exit boundary:
- `0` — `accepted`
- `1` — `refused` (protocol, grammar, CAS head, or authorization refusal decided by ACL2)
- `2` — local CLI usage, transport connect, or startup bind refusal
- `3` — `uncertain` (post-send disconnect or ambiguous commit boundary; retry with `--op`)

Live end-to-end black-box suites (`python3 tests/native-image-restart.py` and `python3 tests/test_fn2_user_surface.py`) exercise real TCP + `0600` Unix sockets through immediate `SIGKILL` crash and restart recovery.

---

## 6. Further Reading

- **Layer architecture & invariants:** [`docs/a-pool-host-sim.md`](docs/a-pool-host-sim.md), [`docs/b-durability.md`](docs/b-durability.md), [`docs/c-ordered-runs.md`](docs/c-ordered-runs.md), [`docs/d-machines-nntp.md`](docs/d-machines-nntp.md), [`docs/e-surface.md`](docs/e-surface.md), [`docs/h-harness.md`](docs/h-harness.md)
- **Served authority & capability model:** [`docs/design/AUTHORITY-20261105.md`](docs/design/AUTHORITY-20261105.md)
- **Obligation ledger & teeth:** [`docs/OWED.md`](docs/OWED.md)
- **Lean 4 metatheory & ACL2 bridge:** [`docs/design/LEAN-METATHEORY.md`](docs/design/LEAN-METATHEORY.md), [`docs/design/BRIDGE-CERTIFICATE.md`](docs/design/BRIDGE-CERTIFICATE.md), [`docs/design/BRIDGE-GENERATED.md`](docs/design/BRIDGE-GENERATED.md), [`docs/design/LEAN-ACL2-SURVEY-20261112.md`](docs/design/LEAN-ACL2-SURVEY-20261112.md)
