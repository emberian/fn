# Successful fence return cuts

The source now connects a successful storage Fence's physical return to an
unposted simulator continuation and a native trace/replay event. The actual scheduled Fence cut/replay controls pass in a Forge proof REPL;
record certification and the complete native/model relation remain pending. The default
`tools/native_program_check.py` still refuses incomplete cut mapping;
`--source-only --json` reports the bounded source contracts separately.

The actual worker calls `fn2-device-perform device job` between
`device-syscall` and `device-syscall-return`. Its return cut precedes insertion
into the device completion queue. `fn2-n-storage-completions` checks the same
operation generation, decodes the syscall result through
`fn2-device-io-observation`, records Fence `(:physical-return PACKET N ERRNO)`,
then exposes `device-return` before `fn2-n-complete` normalizes a terminal.
The four-field event retains the actual syscall return and errno. Native
schedule word/time/fault coordinates are explicitly neutral (0/0/no-fault);
the checker claims no correspondence of those environmental coordinates.

The real `fn2-sim-advance-flight` calls `fn2-sim-step-completion`. For the Fence
pilot, it invokes the existing `fn2-sim-native-stage`, which uses the same
`fn2-sim-physical` → `fn2-sim-physical-act` → `fn2-storage-fence-complete`
implementation as atomic completion. The stage retains the raw 11-field packet
in generated per-row columns and sets active=4. It sends no terminal. The next
scheduled step resumes through `fn2-sim-native-post` and the existing
`fn2-sim-complete-result`, without another physical operation. Raw code/count/
auxiliary result, original schedule word/time/fault, and slot/generation/kind/
event/length remain distinct from normalized terminal fields. Atomic completion
captures the same raw fields so the existing whole-state staged/atomic equality
obligation remains meaningful; it is not weakened to ignore those columns.

`fn2-sim-native-packetp` binds posting to the current operation incarnation.
`fn2-sim-find-write` selects active=1, so a returned active=4 write cannot be
reissued by crash. Active=2/3 retain their Send release meanings and are
unreachable for the fresh Fence incarnation in this domain. Other storage
operations retain their atomic scheduler path; their external cut-driver
packets must not be mistaken for scheduler-owned Fence continuations.

`fn2-envelope-prefix` accepts raw Fence returns while preserving TAKEN in its
continuation. It checks descriptor identity, acknowledgement, absence of a
prior return/post, and—on native four-field events—the actual ACL2 decoder.
Later posting must agree with the shared `fn2-host-result` normalization and
consumes the retained packet once. Legacy traces without physical-return events
remain regression inputs and contribute no physical-return evidence. The
success pilot uses shared `:ok`; simulator `:io` versus native `:failed` error
abstraction remains outside this slice.

The source checker binds exact worker/harvest/scheduler blocks, enclosing AST
positions, argument/result flow, raw field storage/reconstruction, and actual
model snapshot commit. Its evidence records function, AST path, contract and
semantic role rather than line hashes. Missing or terminal-post-attributed
physical cuts, dead branches, scheduler bypass, discarded raw scalars and
changed native raw returns fail the source audit. This evidence is not proof
admission, execution or native/model refinement.

The executable controls are:

- `tests/scheduled-fence-cut-unit.lisp`: drive the real advance, observe durable
  byte 17 with no Fence post, crash or resume without another physical stamp,
  and replay the packet produced by that advance; reject changed generation or
  terminal outcome or raw retained packet. All five controls executed and
  returned true in the same model world. The nine operation-level cut controls
  also returned true.
- `tests/native-fence-return-unit.lsp`: one real fd Fence through the actual
  performer/harvest; inspect the actual death boundary before normalization.
  This raw-host fixture remains unexecuted.
- `tests/envelope-prefix-unit.lisp`: issued Fence, raw-return prefix/resume,
  duplicate/stale incarnation/wrong post/raw-syscall mutations. The separate
  four-field native controls remain unexecuted.

Source validation passes 28 focused Python controls, strict source reading,
secrets and diff checks. Forge REPL admissions cover the generated schema,
physical adapter, retained raw helpers, stage/post/completion guards, and their
original carrier-preservation statements. The actual four scheduler advance
functions are guard-verified in that world. The stage preservation package takes
7.24 s/133,497 steps; post/atomic-complete/scheduled-completion carrier packages
take 27.33 s/562,554 steps in aggregate. The original whole-state
`fn2-sim-native-finish-is-atomic` theorem also admits in 4.04 s/138,626 steps,
with its supported-storage antecedent and every output/raw column unchanged.
Its saved raw-packet roundtrip admits in 0.94 s; the physical Fence specialization
in 0.30 s; save idempotence in 0.12 s; and complete-result absorption in 0.10 s.
These admissions are not record certification. The replay checker retains its pre-existing unverified-guard
status; ACL2 reports recursive guard inhibition while executing that checker.

The first world hit the shared 2 GiB cap while loading the old physical leaf's
whole assembled checker dependency. That is prover-world loading, not node
resource behavior. The physical leaf now names its actual pool/OWN dependencies;
the adapter still includes the same served `assembly-init`. Six unchanged core
OWN projections moved to `check-core`. The narrowed transfer leaf admits in
4.90 s/1,165,525 steps; the physical adapter block takes
159.53 s/5,760,590 steps, an outstanding proof-cost defect. The retained world
then loaded exact cached host-boundary dependencies for actual packet replay.

The existing positive whole-formula witness's all-function-theory hint did not
finish within the proof tool's 45.1 s hard sentinel limit; the tool killed its
own retained session. This is a proof-cost failure, not a counterexample or an
OOM result. The hypothesis-removal witness was not reached. Its deliberate
active=0 mutation tests the theorem's pending-flight premise; it contributes no
evidence that this branch is reachable in the composed scheduler.

Remaining obligations include the complete keystone witness package,
initialized incarnation and effect/crash preservation,
record certification of changed closures, raw-host load/real-fd control, native
FIFO snapshot coverage, FFI/OS contracts, reads/writes/errors/cancellation/
concurrent workers, and universal trace correspondence. Native SIGKILL controls
do not establish power-loss persistence assumptions. The default cut-mapping
gate remains incomplete and fails closed.
