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
