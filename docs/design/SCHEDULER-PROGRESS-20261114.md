# Served scheduler progress

The integration companion based on `498f26130` excludes `books/executor.lisp`:
the budget lane owns the shared loop emitter and its H=1 policy removal.
The companion additionally mirrors the budget lane's registry-derived
descriptor reservation in reference stopping and Q1 continuation. Its new
compound H=1/minimum-supported-quantum fixture must issue the real listener
action, then stop both schedulers at the short residual while retaining the
signal. This integration adaptation and its execution-profile witnesses are
source-only until the composed gates below run; prior evidence does not
certify that new composition.

Integration gates: fresh source admission of `tests/executor-progress-trace`
and `books/executor-progress`; the former includes the actual initialized
unit assertions, normal H=1 clock/signal case and minimum-quantum residual
case. Run `tests/executor-progress-control.lsp` against that same world for
old-stop mutation/restoration. Record the narrow changed reference/Q1/TRACE
and progress roots against the integrated shared emitter, reusing qualified
parents. The historical literal-executor record below is not transferable
to the new macro closure without requalification.

The native host posts a clock before every `fn2-turn` (`host/adapter.lisp`).
The original supported profile accepts H=1, while its `fn2-concrete-loop-stop-p` stops as
soon as observations reach H. This can leave already runnable work untouched
on every host iteration. This is distinct from `fn2-sched-starvation`, whose
owed statement counts actual calendar visits rather than turns.

The actual initialized witness in `tests/executor-progress-unit.lisp` ran on
qualified frozen A (`a5212f4c2`) in a private tree, cached dependencies only.
All eight H=1 clock/turn iterations satisfied the supported-profile and
core type/WFP, runnable, available-credit and nonstopped predicates. Each
returned `(:more observations=1 visits=0 actions=0)`, with scheduler cursor
0 and runnable count 2 unchanged. H=2 with the same clock, and H=1 without
clock posting, each returned eight visits and one action. This is source
execution evidence, not current-B record certification. The node default H=16
is not implicated by this particular witness. Clock generation eventually
exhausts its u60 range, so no infinite nonstopped execution is claimed.

The repair supplies a conditional progress guarantee for the actual loop:
when observation admission is exhausted but visit, action and work capacity
remain and internal work is eligible, execute a calendar visit. The existing
`allow-observation` argument already separates observation admission from
calendar selection. Reference scheduling, Q1 case selection and TRACE
controls mirror the policy while retaining quantitative limits and pending
observations. A missing fresh quantum is an explicit negative control.

Observation-class fairness is separate: posted completions precede clock,
which precedes sticky signals. Replenishing an earlier class may postpone a
later one, including H=1 clock traffic postponing a signal. Changing that
ordering requires an explicit arbitration policy; calendar progress alone
must not be advertised as clock/signal or external-dependency fairness.

## Repair candidate and claim boundary

The repair removes only the standalone observation-count stop. The real
loop still checks visit, action, work, stop state, and availability of allowed
work. Reference transition/selection and the generated Q1 case formulas now
receive the same observation-admission bit. This includes the after-H case
where a signal remains pending while the calendar is visited. Existing
observation priority is unchanged.

`books/executor-progress.lisp` states a conditional theorem over the real
`fn2-concrete-loop`: positive fuel, natural counters, exhausted observation
allowance, eligible work, and a false actual stop predicate imply an increased
calendar-visit count. An empty calendar entry counts as a visit. This is not
a per-row fairness theorem, and the theorem does not itself prove that a
fresh turn reaches the observation boundary. Actual initialization/clock
fixtures connect that boundary to execution for the supported H=1 profile.

Controls:

- `tests/executor-progress-unit.lisp`: H=1 clock turn, H=2/no-clock controls,
  whole conditional antecedent after one actual clock transition, and a
  zero-fuel hypothesis-removal witness.
- `tests/executor-progress-control.lsp`: restore the original stop disjunct,
  reproduce eight zero-visit turns, reject the progress oracle, then restore
  the repaired function and rerun the oracle.
- `tests/executor-progress-trace.lisp`: clock and signal pending together;
  independent reference/TRACE must agree on calendar visitation after H,
  leave the signal pending, and never label it as consumed.

The repair source proof and runtime controls have now passed their qualified
pilots below, including the full B independent TRACE composition. The actual
repaired executor and theorem now have qualified records; the full reference
closure still needs its composed record gate.
Q1 continuation already omits work-room capacity and is not claimed here to
be an exact characterization of the concrete stop predicate. Completing that
composition contract remains separate from this policy correction.

## Executed repaired-A gates

The conditional progress theorem passed in a fresh qualified-A source world
with the repaired executor loaded from source. Main theorem: 2,813 prover
steps; visit monotonicity: 36,289; transition visitation: 414. This is source
proof admission, not current-closure record certification.

A full repaired host-boundary source load exceeded its 2 GiB scope while
re-admitting assembly attachments (systemd recorded a 2 GiB OOM). Instead,
execution-only controls used the unchanged qualified-A host-boundary cache
and structurally extracted the exact repaired stop body into raw Lisp.
`tests/executor-progress-pilot.py` emits that driver from committed source;
no logical theorems are proved in the raw-patched world.

All five committed assertions passed: initialized H=1 with clock now returns
eight visits and one action; H=2/no-clock controls are unchanged; the actual
post-clock boundary satisfies the entire conditional antecedent and gains a
visit; zero fuel retains the other premises and makes no visit. Restoring
the old observation-stop disjunct reproduces eight zero-visit turns and
fails the progress oracle; restoring the repair passes again. Both process
exit and explicit success markers were checked.

Evidence is on forge: `/tmp/assurance-progress-repair-pilot.log` (source
proof), `/tmp/assurance-progress-raw-pilot.log` and
`/tmp/assurance-progress-raw-acl2.log` (runtime control), all successful jobs
exited 0. The failed full source runtime load is
`/tmp/assurance-progress-runtime-pilot.log` (143, OOM). The later B gate below
used an explicitly allocated 4 GiB slot for the complete source composition.

Native readiness fairness is also separate. `fn2-n-ready` scans operation
slots from low to high and serves at most one waiting operation per
capability in an iteration. Capability readiness therefore does not imply
fair visitation among operations sharing it. TLS readiness/kick migration
must address that arbitration explicitly; neither this calendar theorem nor
an environmental socket-readiness premise supplies the missing guarantee.

## Full repaired-B source composition

A fresh private tree at `6e07e62f3` plus this lane's exact executor, reference,
Q1 and TRACE patch passed `tests/executor-progress-trace`. The qualified
unchanged dependency set comprised 156 books. Changed executor, actual
assembly attachments, host boundary, unit fixtures, reference, Q1 and TRACE
were loaded from source in dependency order; no old upper facts or raw
function substitutions were used. This is patched-B source execution, not
the frozen B certificate identity or a new full-closure certificate.

All unit assertions passed. The independent clock-plus-signal case returned
`(T NIL NIL NIL 1 8 1 8 NIL T ...)`: supported profile; no before/step/after
differences; concrete/reference each consumed one observation and made eight
visits; core not stopped; signal still pending. The case tally reached the
real listener `:accepting` transition, three empty principal visits and four
service visits, with one clock label and no signal label.

Log: `forge:/tmp/assurance-progress-trace-pilot.log`; runner exit 0, session
explicitly stopped. Source admission cost was 174.30 seconds and 6,125,184
prover steps. The shared 4 GiB slot was released to the CNS Q1 lane.

The budget lane separately carried the policy into the single shared loop
emitter (`e0cede4b0`) and record-certified its integrated descriptor-reserve,
actual-turn and H=1 issued-action fixture (44-book closure, 41 reused, 3 new;
`run033917Z-82cc`, `cert033953Z-3646662`). That record is distinct from this lane's conditional theorem record below
and does not certify the full independent reference/TRACE closure. The latter
record gate remains outstanding for convergence; no duplicate executor
implementation should survive integration.

## Qualified actual-executor progress record

The actual repaired executor and `books/executor-progress` passed the named
record gate `run-20261114T054516Z-1710`, certification
`certify-20261114T054550Z-3771811`. Its 137-book closure reused 135 qualified
parents and built only those two books. Triage reported zero failures;
source hashes were unchanged and qualified cache entries were verified at
the current closure keys:

- Executor: `72d429c8fb2b1dc7a679efc3a036d18ee2e1007671520db0a306f9e79c06db09`.
- Progress: `a0b105d50d94f74be1ea3c051f48e8a93ce91a48cfd062ade2f31820de1b1ecd`.

Both entries use record toolchain
`8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`,
origin suffix `04d2cec868ec1cca`. This certifies the actual loop called by
`fn2-turn` in this patched B source, not a separate policy model. It does not
certify the later descriptor-reservation/emitter integration automatically.

Named local evidence is under `build/assurance-progress-record/`, including
the manifest, logs, current-key audit, exact task-local farm wrapper and its
generated commands. Preflight and runner used sequential 4 GiB scopes,
images off, one worker, per-book timeout 900 and outer timeout 1800. The run
exited 0, its lock was free, and the named slot was explicitly released.

Total certification wall time was 72.788 seconds. Executor wall time was
44.828 seconds; progress wall time 27.913 seconds, with its costliest proof
0.31 seconds/36,289 steps. Whole-book load cost still exceeds the D26 target;
this gate does not close that performance obligation.
