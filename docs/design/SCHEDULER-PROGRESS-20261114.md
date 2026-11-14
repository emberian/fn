# Served scheduler progress

The native host posts a clock before every `fn2-turn` (`host/adapter.lisp`).
The supported profile accepts H=1, while `fn2-concrete-loop-stop-p` stops as
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

The repair target is a conditional progress guarantee for the actual loop:
when observation admission is exhausted but visit, action and work capacity
remain and internal work is eligible, execute a calendar visit. The existing
`allow-observation` argument already separates observation admission from
calendar selection. Mirror the policy in reference scheduling, Q1 case
selection and TRACE controls; retain all quantitative limits and pending
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

`books/executor-progress.lisp` proposes a conditional theorem over the real
`fn2-concrete-loop`: positive fuel, natural counters, exhausted observation
allowance, eligible work, and a false actual stop predicate imply an increased
calendar-visit count. An empty calendar entry counts as a visit. This is not
a per-row fairness theorem, and the theorem does not itself prove that a
fresh turn reaches the observation boundary. Actual initialization/clock
fixtures connect that boundary to execution for the supported H=1 profile.

Prepared controls:

- `tests/executor-progress-unit.lisp`: H=1 clock turn, H=2/no-clock controls,
  whole conditional antecedent after one actual clock transition, and a
  zero-fuel hypothesis-removal witness.
- `tests/executor-progress-control.lsp`: restore the original stop disjunct,
  reproduce eight zero-visit turns, reject the progress oracle, then restore
  the repaired function and rerun the oracle.
- `tests/executor-progress-trace.lisp`: clock and signal pending together;
  independent reference/TRACE must agree on calendar visitation after H,
  leave the signal pending, and never label it as consumed.

These repair proofs and controls are prepared source, pending their qualified
pilot; the executed result above concerns the original counterexample only.
Q1 continuation already omits work-room capacity and is not claimed here to
be an exact characterization of the concrete stop predicate. Completing that
composition contract remains separate from this policy correction.
