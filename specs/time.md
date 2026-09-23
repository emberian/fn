# Clock observations and bundle expiry

Status: executable model and certified properties. `books/clock`,
`books/clock-invariants` and `tests/acl2/clock-tests` are certified by ACL2:
every witness and tooth cited below is accepted, including the two-node witness
in the safety section. This is not a clock
discipline, a time-synchronisation protocol, a retention policy, or a
qualification of any host time source.

fn had no model of time at all. [The independent review](../planning/review-2026-09-18-independent.md)
records that as structural naivety 5: neither NNTP injection nor bundle expiry
could be modeled, and "expiry correctness is clock-error correctness". This
specification closes the safety half of that gap for bundle expiry and states
precisely what remains open.

## The observation contract

The host supplies one value per decision:

```
(fn-clock-observation monotonic wall wall-error-bound has-wall)
```

| Field | Meaning | Host obligation |
| --- | --- | --- |
| `monotonic` | a local counter in milliseconds whose epoch is outside this observation record | nondecreasing within the selected clock domain; an anchor from another domain must never be compared to it |
| `wall` | this node's estimate of DTN time, milliseconds since 2000-01-01T00:00:00Z (RFC 9171 §4.2.6) | meaningful only when `has-wall` is true |
| `wall-error-bound` | the half-width of the interval the host certifies contains the true DTN time | an honest bound; the model's safety result is conditional on it |
| `has-wall` | whether the host claims any wall reading | false is a legitimate, permanent answer for a node without a clock |

The admissible interval of an observation is
`[wall - wall-error-bound, wall + wall-error-bound]`. `fn-clock-admissible-truep`
names membership in it. Nothing in this model relates the interval of one node
to the interval of any other node.

Bundle age reaches the decision as an **anchor**, `(age . monotonic-at-anchor)`,
or `nil` when this node holds no Bundle Age information. RFC 9171 §4.4.2 makes
the Bundle Age block the sum of the bundle's *known* intervals of residence and
transmission up to its most recent forwarding; the local node adds its own
residence, measured monotonically. The current estimate is therefore
`age + (monotonic - monotonic-at-anchor)`, which is the only shape that stays
monotone in local elapsed time without a wall clock.

The BP native recovery path uses a separate durable domain gate before that
legacy anchor reaches `fn-clock-expiry-decision`. The host observes Linux
`CLOCK_BOOTTIME` milliseconds and the kernel boot ID from
`/proc/sys/kernel/random/boot_id`; ACL2 validates the exact boot-ID octets and
compares them to an immutable FNBS kind-6 `clock-domain.fnb` marker. A valid
same-boot marker permits reuse of the counter across process restarts. A
different boot, malformed marker, or missing marker beside legacy obligations
fences BP lifecycle before replay or expiry. This first recovery slice preserves
the known lower-bound age and obligations; it does not reanchor after a reboot.
The host observation that the boot ID identifies one stable boot and that
`CLOCK_BOOTTIME` advances during suspend is a Linux boundary assumption, not a
theorem of the ACL2 clock model.

An anchor is a **lower bound** on the bundle's true age, never an upper bound:
intervals unknown to every forwarder are omitted from it. The theorem that uses
this carries it as an explicit hypothesis rather than an axiom, because fn has
no `encapsulate` machinery for named assumptions yet; see "What is left open".

## The decision

`fn-clock-expiry-decision creation-time lifetime bundle-age observation`
returns exactly one of `:expired`, `:live`, `:uncertain`.

RFC 9171 §5.5 permits computing bundle age from the creation timestamp only when
that timestamp is non-zero **and** the local clock is known to be accurate;
otherwise age MUST come from the Bundle Age block. fn goes further and prefers
the age path whenever an anchor exists, because that path needs no clock
agreement at all.

- **Age path** (an anchor is present): `:expired` when the estimate exceeds the
  lifetime, otherwise `:live`.
- **Wall path** (no anchor): `:uncertain` when there is no wall reading or the
  creation timestamp is zero ("time unknown", §4.2.6). Otherwise the decision is
  taken over the whole admissible interval -- `:expired` when *every* admissible
  true time puts the age past the lifetime, `:live` when *no* admissible true
  time does, and `:uncertain` when the interval straddles the lifetime.

`:uncertain` is not permission to do anything. `fn-clock-may-drop-local-copyp`
is true of `:expired` alone, and it authorises only dropping this node's own
copy of the bundle. It is not a retention release: nothing in `fn-bp` calls
`fn-retain-release` on an expiry verdict, and RFC 9171 §5.5's deletion is a BPA
operation on a bundle, not an fn operation on an accepted article. The three
outcomes stay distinct through every boundary, as the assurance rules require.

## FLR-004, restated

[FLR-004](failures.md) requires fn to tolerate "delayed, duplicated, reordered,
and replayed network inputs, arbitrary contact gaps, and clock errors within
explicit policy", that "safety must not require a synchronized global clock",
and that "bundle or message expiry requires explicit clock/age semantics".

Its **safety half** is discharged by three theorems in
`books/clock-invariants.lisp`, none of which mentions a second node's clock:

| Theorem | What it establishes |
| --- | --- |
| `fn-clock-expired-requires-every-admissible-clock-to-agree` | whenever the wall path answers `:expired`, every true time this node's own declared error bound admits really does put the bundle past its lifetime |
| `fn-clock-expired-and-live-cannot-both-be-sound` | two nodes with unrelated wall readings cannot reach opposite confident verdicts while both of their declared error bounds are honest -- agreement between the nodes is never required, only honesty of each node about itself |
| `fn-clock-expiry-is-monotone-in-local-time` | once `:expired` under an observation, still `:expired` under any later observation of the same clock, where "later" means the monotonic counter has not gone backwards *and* the earliest admissible true time has not gone backwards |

`fn-clock-expired-by-age-requires-true-age-over-lifetime` covers the age path
under its stated lower-bound hypothesis.

`fn-clock-later-observationp` is the precise contract a host must meet for
monotonicity. A resynchronisation that widens the error bound far enough to move
the earliest admissible true time backwards is **not** a later observation of
the same clock, and the theorem does not apply to it. That is deliberate: a node
that discovers its clock was wrong is allowed to stop being sure.

The owner is where that sentence became executable
([D10-a](../planning/decisions.md), 2026-09-21). `fn-own-observe` answers
`:observed`, `:refused` or `:invalid`, and a refusal leaves the owner with no
clock rather than with the reading its host has just contradicted: a node that
has stopped being sure decides nothing under the clock it used to hold. Note
that `fn-clock-later-observationp` is **non-strict**, so a reading equal to the
one held is a later observation of the same clock and is admitted; the owner's
clock is a high-water mark, not a counter.

The article acceptance stamp consumes the owner's observation at prepare.
`fn-record-stamp-of-observation` takes the whole second of its DTN epoch wall
reading; an absent or out-of-range reading yields `:clock-unusable`, so the
owner refuses the submission and consumes its durable allocation reservation.
This is the node's local wall reading, not a verified true time or a comparison
between nodes. A schema-0 article has the fixed stamp `:legacy`.

`tests/acl2/clock-tests.lisp` exhibits two nodes whose clocks differ by 200
seconds reaching opposite verdicts on one bundle, together with the fact that
their admissible intervals are disjoint -- so at most one of them is honest, and
the second theorem above is not violated. That witness is the concrete content
of "safety never depends on two nodes agreeing on wall time".

## What is left open

- **Liveness.** Nothing bounds how long a node may answer `:uncertain`. A node
  with no wall clock and no Bundle Age block answers `:uncertain` forever
  (`fn-clock-no-wall-and-no-age-is-uncertain`), which is why RFC 9171 §4.4.2
  requires a Bundle Age block whenever the creation timestamp is zero. A
  liveness claim would need a hypothesis bounding the host's error bound and a
  fairness assumption; PRF-018 is where that belongs, and it is not made here.
- **The honesty of `wall-error-bound` is an assumption, not a theorem.** It is
  the one place a host lie turns into a wrong `:expired`. It should become a
  constrained function under the C1-15 assumptions packet; until
  `books/assumptions.lisp` exists, naming it `A-CLOCK` here would be prose
  pretending to be an assumption artifact, which the assurance rules forbid.
- **The Bundle Age lower-bound property is likewise a hypothesis**, discharged
  by the caller, not by this book.
- **Cross-boot age recovery** remains open. The BP startup gate detects an
  incompatible or legacy clock domain and fences it, even if the new boot's
  numeric uptime is higher. No migration, reanchor, or reboot liveness theorem
  follows from that refusal. The generic `fn-clock-expiry-decision` still takes
  a bare pair and relies on its caller to establish domain compatibility.
- **NNTP injection time** is untouched. This lane models bundle expiry only.
- **Lifetime overrides** (RFC 9171 §4.3.1, a BPA imposing a shorter effective
  lifetime) are representable only by passing the override as `lifetime`;
  the requirement that an override not replace the asserted lifetime is not
  modeled.
- **Actual-caller scope.** `host/bp-ingress-host.lisp` already calls
  `fn-clock-expiry-decision` for ingress. The native BP startup join selects
  `fn-bpnf-clock-domain-plan` before it exposes persisted anchors. The
  clock-domain certification proves that planner's byte and decision contract;
  source-matched native restart and physical observation evidence are tracked
  separately under PRF-061 and SCN-029.
