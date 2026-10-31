# Q1's honest classification (decision 1 applied to Q1, with DM10's oracles): the statement (DSL seat)

Accepted by main on 2026-10-30, and revised after Astra's read-only pass the same day. Astra's corrections
are taken: the sharing map, the oracles' subjects, the mutation sites, and the four-way harness. Main's
rulings: one control per kind, not per case; fn2-commit's control waits for B5 and is reported by name
until then; the three new independent rows are defthm-owed with teeth; the control of the control lives
in the same evidence book.

## 1. What a Q1 case row establishes
`fn2-ref-transition` (reference.lisp:124-180) executes the concrete side's handlers. The independent part
is selection (calendar, principal FIFOs and service flags as lists) and the loop's accounting. A case
row's G1 therefore states: *with these handlers shared, the concrete scheduler and executor refine the
list scheduler and executor for this transition.*

That is a representation refinement of the scheduler: `:claim :representation`, schema `:g1`. The same
holds for `fn2-turn-refinement`, the composition row. Sharing does not invalidate the refinement; it
limits what the refinement establishes. What the handlers do is claimed only by the independent rows of §3.

## 2. The sharing map, per label: behavioural dependencies, recorded as declarations

| label | shared behaviour (both sides execute it) | `:shared` |
|---|---|---|
| `(:observe K E)` | fn2-harvest-one, fn2-machine-observe, K's selected handler | `((:operation-set fn2-core-harvest) (:operation-set fn2-machine-router) (:machine K))` |
| `(:run K P)` | fn2-machine-run, K's arm and its dependencies, fn2-exec-charge-run, fn2-machine-take-wake (no harvest); the listener's arms also reach the admission and ledger operations | `((:machine K) (:operation-set fn2-machine-dispatch) (:operation-set fn2-executor-charge))`, plus `(:operation-set fn2-machine-resources)` and the ledger's set for K = listener |
| `(:router :fallback)` | harvest, the router's fallback | `((:operation-set fn2-core-harvest) (:operation-set fn2-machine-router))` |
| `(:executor :clock)` | fn2-take-clock, fn2-exec-clock | the executor's clock set |
| `(:executor :signal)` | fn2-take-signal, fn2-core-stop | the executor's signal set (shared, though its branching is written twice) |
| `(:executor :service 1)` | fn2-machine-grant-one, fn2-exec-arm, fn2-exec-charge-run | `fn2-machine-resources` and the charge set |
| `(:executor :service S)`, S other than 1 | the charging | the charge set |
| `(:executor :empty-principal)` | none (state readers and eligibility predicates only) | nil |

The operation-set names in the table are placeholders where the code registers no such set; the build
uses the declaration that actually generates each function, found from the registry
(`fn2-decl-definition` over `fn2-decl-all-rows`).

Two rules for the build:
- `:shared` records declarations of behavioural dependencies, not the whole call closure; state readers
  are not listed.
- `:sides` stays the formula's direct endpoints, so squares.lisp:23's role check is unchanged. The
  transitive provenance goes in a separate key, `:shared-provenance` (the shared functions by name),
  which the export prints.

owed.lisp gains a metadata role for `:contract (:independent C)`, so the independent contract is not an
unused formula role.

## 3. The independent contracts: one per kind; each of K's case rows names it

| kind | contract | independent of the shared handler because | status |
|---|---|---|---|
| fn2-echo | `fn2-echo-replies-its-input` | the expected bytes are built from the client's own input (echo-scenario.lisp:29) | new row |
| fn2-scribe | `fn2-scribe-reads-back` | an external sector-format oracle plus a write/fence/read journal of the adapter's octets; the scribe's own verifier shares fn2-scribe-byte with its writer (machines-a-scribe.lisp:24), and OWN checks provenance, not intended contents | new row and new oracle |
| fn2-listener | `fn2-listener-admits-within-ledger` | booking, transfer and release events observed at the ledger, plus conservation; "never admit after refusal" would be false, because a refused booking admits an unbooked connection that answers 400 (machines-a-run.lisp:154) | new row |
| fn2-conn | `fn2-conn-wire-correct` | WIRE's model oracle over client octets; T1 (safe execution) and T8 (fragmentation/privacy) are not WIRE correctness | new row binding WIRE (WIRE is permissive: codes and framing, not exact text; the row says so) |
| fn2-upload | `fn2-upload-judged-and-hashed` | the judgement and the decoded article are H's model's (tests/upload-model-export.py over tests/model/nntp_model.py, pinned in tests/evidence/upload-model.lisp); the digest reference is B's list-level `fn-blake3`; WIRE's two-phase POST read | built (D4 2/n); one open disagreement listed by name (`from-duplicate`: the catalogue's "From appears more than once" names none of the model's duplicate reasons) |
| fn2-commit | B's rows | the crash-model differential and HISTORY | reported by name as waiting for B5 |
| fn2-recovery-machine | `fn2-recovery-machine-recovers` (tests/q1-contracts-b.lisp) | B's RECOVERY checker over the harness's own decoding of the durable image, and the death control; recovery driven through fn2-turn (B's own runner steps the executor's parts, outside TRACE) | built after B5; control: `fn2-recovery-witness-match` never matches |

The three rows main named, as statements (helper names are new; the runners execute the served path,
the predicates read external evidence only):

```lisp
(defthm-owed fn2-echo-replies-its-input (input chunks schedule)
  (implies (fn2-echo-completion-domain-p input chunks schedule)   ; admitted, octets, lossless transport, enough service
           (equal (fn2-echo-run-output input chunks schedule) input))
  :schema :invariant :claim :semantic
  :teeth (fn2-echo-replies-positive fn2-echo-replies-without-service))
(defthm-owed fn2-scribe-reads-back (sequence schedule)
  (implies (fn2-scribe-reliable-cycle-p sequence schedule)       ; completed cycles, reliable device
           (fn2-scribe-cycle-matches-p sequence (fn2-scribe-served-cycle sequence schedule)))
  :schema :invariant :claim :semantic
  :teeth (fn2-scribe-reads-back-positive fn2-scribe-reads-back-without-reliable-io))
(defthm-owed fn2-listener-admits-within-ledger (profile events)
  (implies (fn2-listener-domain-p profile events)                 ; initialised, booking relation in force
           (fn2-listener-ledger-prefixes-p profile (fn2-listener-served-run profile events)))
  :schema :invariant :claim :semantic
  :teeth (fn2-listener-ledger-positive fn2-listener-ledger-without-initial-booking))
```

- Each positive tooth runs the served path on a fixture and asserts the antecedent and the conclusion.
- Each negative tooth supplies a concrete counterexample once its named hypothesis is removed.
- The listener's conclusion holds on every prefix of the run: credits, booking ownership, capacity,
  transfers, and the refusal's 400.

## 4. The controls: a four-way harness per kind, in one evidence book
Each kind's harness is a raw-Lisp driver in the hooks' pattern. It runs one short scenario four times and
writes one evidence record per run, keyed by revision, mutant, scenario, the mutant's invocation count on
each core, the labels reached, and the failure reason. It records TRACE's and the oracle's verdicts
separately from the aggregate.

1. **Baseline:** TRACE passes and the oracle passes.
2. **Shared mutation** (the mutant runs on both cores): TRACE passes and this oracle fails, with the named
   reason.
3. **Concrete-only mutation** (the mutant runs on the concrete core alone): TRACE fails. This shows the
   lockstep is wired to the handler.
4. **Restoration:** TRACE passes and the oracle passes.

Mutant invocations must be greater than 0 on both cores in run 2, and on the concrete core in run 3.
Otherwise the control fails loudly: a mutation that never ran proves nothing. If TRACE catches the
shared mutation, that also fails loudly, but it does not mean the handler was unshared; the consequences
may reach selection. The fix is then a different site.

Sites (Astra's), each an observable semantic change:
- echo: `fn2-echo-observe-receive`'s initial offset 0 -> 1 (machines-a-run.lisp:60);
- scribe: the checksum byte in `fn2-scribe-patch-loop` (machines-a-scribe.lisp:164), against the new
  format oracle (OWN alone passes);
- listener: in `fn2-listener-accept` (machines-a-run.lisp:172), a refused booking's `*fn2-none*` becomes
  `principal`, with ledger refusal forced while physical credits remain;
- conn: the greeting is produced as 900 before its loan is issued, which WIRE rejects (an arbitrary wrong
  digit can stay admissible).
- upload: `fn2-upload-hash-step` fed one octet short at the start of each chunk, the octet still counted
  hashed (the verdict is unchanged; the digest oracle catches it, TRACE sees the concrete-only digests).

The rows' `:shared-handler-mutation` names CTRL-K, a zero-argument checker in the evidence book that reads
the four records. One control per kind demonstrates one blind spot, not coverage of every arm; the export
says so beside it.

## 5. Acceptance
- The export:
  - every Q1 row is `:representation` with `:shared` and `:shared-provenance`;
  - each case row of K names CONTRACT-K and CTRL-K;
  - kinds without them are listed by name: fn2-commit until B5, and fn2-upload when D lands it.
- fn2-square-rowp accepts the rows. Controls: a Q1-shaped `:semantic` row with `:shared` and no
  independent contract is refused; a `:sides` endpoint shared but undeclared is refused (exists).
- The four harnesses record the four verdicts as stated, and their invocation counts are above 0.
- Drivers unchanged (113 A4 blocks); sim-layer-d-evidence passes; OWED regenerated in the one commit that
  changes the rows.

## 6. Order of the build
1. owed.lisp's `:independent` metadata role and `:shared-provenance`; defsquare binds the per-label
   `:shared` from the registry.
2. The four contract rows with teeth (echo, listener, conn first; scribe after its format oracle).
3. The harness and its evidence book, one kind at a time, conn first (D's scenario is the cheapest).
4. Then the rows name CONTRACT-K and CTRL-K, OWED is regenerated, and the commit lands.
