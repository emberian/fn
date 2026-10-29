# Experiment E1 pass 2 premeasurement manifest

Base commit: 4f2a101e4. Pass-1 evidence and the six frozen mutation definitions
are retained unchanged. No new book is needed: this driver uses the certified
pass-1 choices/checks books and the same layer-A closure. Qualification probes
are separate from the measured campaign set.

- Seeds remain 1, 20261028, 314159265; random trials remain 128 choices and use
  the same LCG and domain. Choice order and seven fault classes are unchanged.
- Every measured campaign has 120 seconds wall time, excluding loading, and
  200,000 combined concrete/reference transitions including all G1, TRACE,
  replay, both G2 routes and inline original counterfactual checks. Counters
  for original counterfactuals are separately named CONTROL-*. Validation
  that cannot finish within budget is censored, not a finding.
- Configuration 3 starts at horizon 0, completes every prefix through h, then
  restarts at h+1. No deduplication or pruning in 3. Every prefix replay and
  repeat G2 check is charged. The deepest complete horizon, current partial
  horizon and per-horizon prefix/state counts are retained, including at a
  first-failure stop. Horizons count suffix choices for supplied-prefix rows.
- Additional 3b uses the same iterative deepening but memoizes exact keys:
  remaining depth, full copied core/ref/sim/OWN/client/cursor/queue state,
  and ordered byte/close histories. Hash collisions are resolved by EQUALP;
  no hash-only equality or identifier renaming. Keys are copied and immutable.
  This is exact-state deduplication, not a checkpoint/restore implementation.
  Retention is bounded to 64 exact keys; on saturation the table is cleared.
  Eviction only causes re-exploration, never an additional prune. The first
  unbounded prototype exhausted its heap and is retained as development
  evidence, excluded from final timings. Interrupted G1 dispatches are
  reported separately and excluded from completed per-label counts.
- Main matrix profile is unchanged C=1, accept-credits=1. Extra data-declaration
  rows use C=2 and QA=8, otherwise the same tiny profile: two live echo
  capabilities can coexist, and min(O,QA)=8 exceeds 2*C+credits+1=6. Compare
  search modes only within the same profile/declaration/start prefix.
- Third declaration: receive/send terminal completions or their borrow-release
  cells on different echo capabilities, no accept/close, under the unchanged
  E1-CLIENT-OWN-STOP-v1 contract. Posted FIFO sharing is explicitly allowed.
  Delays and wake-intercepted choices remain excluded as non-completions.
  Count equal legal diamonds, equal diamonds with client bytes, rejected
  candidates and illegal residuals separately; save the first positive route
  pair as well as every first refutation. Equality is finite observation, not
  a theorem of future independence.
- Main rows: ORIGINAL and M1..M6, baseline/random (three seeds each), iterative
  and 3b (one deterministic order each). Additional local-claim rows: iterative
  from the supplied listener and send prefixes for ORIGINAL/M1..M6. These are
  never credited as reachability from initialization.
- Additional data rows: ORIGINAL/M2/M4, random (three seeds), iterative and 3b,
  from initialization and from a supplied C=2 prefix with two pending Sends.
  The latter is explicitly a local claim. Payloads remain the existing client
  constructor applied to words 0/1; C=2 includes both capability indices.
- Baseline controls run first. Each ORIGINAL campaign records the first
  contract/boundary per trial seed, including the checked boundary attained in
  its final partial trial. The known A4 liveness failure is recorded and the
  next trial begins. Mutants use those exact seed controls: an equal first
  contract/boundary is a known-original result and search continues. A changed
  signature is credited only when the original ran through that boundary (or
  already failed differently). Missing control coverage is not a finding.
- Explicit candidates are checked inline against preserved original raw and
  executable-counterpart function objects, on fresh state, with wrappers on
  both. A same contract/boundary is recorded as original, not a mutation hit.
  Occurrence correspondence preserves slot, generation, cell state, kind,
  capability, fault and word. Range/retained-result fields are descriptor
  outputs: differences are recorded explicitly when replaying the same input
  choice against ORIGINAL. If no matching original occurrence exists, the
  candidate is unqualified. M1 is checked as a changed declaration: ORIGINAL's
  conservative declaration rejects its pair, not a changed runtime.
- A G2 refutation on ORIGINAL stops and is reported as an original declaration
  defect. An equal refutation on a mutant is recorded as known-original and
  search continues. G1/client failures shared with ORIGINAL likewise are not
  mutation hits. No initial input or mutation is changed in response to timing.
- Runtime: same laptop ACL2/SBCL, tools/acl2, six-slot /tmp pool. At most two
  campaign processes, each detached with PID file and timeout -k 5 600.
  Disk below 60 GiB stops new launches; no files are deleted. No commit/push.

## Postmeasurement implementation record

The premeasurement hashes remain in `measurement-freeze.json`; the original
unbounded-cache prototype is recorded separately in
`measurement-freeze-initial.json`. Final source hashes are in
`final-source-hashes.json`, explicitly a postmeasurement record, not a new
mutation freeze. All six mutation files still match the original freeze.

The frozen measurement runner is preserved whole as
`development-runner-before-invalid-fix.lsp`. Its subsequent changes were:

1. Classify all four invalid-original return tags as unqualified candidates,
   as the manifest already required. Four random cells had stopped with
   CONTROL-ERROR; `retry-jobs.json` names their replacements. Both attempts
   are retained, and only the replacements enter the final table.
2. Use last-boundary minus one for an interrupted baseline control: its raw
   boundary is an entered, not fully checked, turn. Every measured baseline
   hit uses a completed original trial, so this conservative repair changes
   no credited hit or measured baseline path.
3. Add the postmeasurement positive-replay command, which is not executed
   by any measured configuration.

The reported final matrix merges controls/main/local/data process manifests,
then replaces the four retry stems. Development attempts are excluded.
Reporting scripts subsequently received formatting and audit changes only.
The six mutation definitions, declared inputs, seeds and budgets never changed.
