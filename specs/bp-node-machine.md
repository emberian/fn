# The BP node processing machine (T12)

Status: the contract the T12 implementation lanes are briefed from. Written
in phase 0 of step T12a of [the trajectory plan](../planning/plan-2026-09-22-trajectory.md)
(§3.1, the T12 paragraph; §3.3), and revised the same day against
[gpt-6's review](../planning/review-2026-09-22-bp-node-machine.md) (F-A to
F-N, integration order A to E, traces BP-R01 to BP-R24). It edits no book,
host file, tool or test. Signatures and line numbers are read from `dev`
`2788d4cb` (2026-09-22) unless a line says otherwise; those the second
revision added are read from `dev` `7c5d2e6e`. Nothing here is a
theorem until a lane certifies it; the statements in §5 and §6 are the
statements the lanes prove, verbatim.

What changed in the revision: the twelve questions are decisions (§12); the
four identities `origin` conflated are separate (§2.3); a carrier-to-work
binding survives discard (§2.4); the ACK contract is an explicit disposition
(§9.2); expiry is decided at one progress boundary (§4.2); budgets are five,
not one (§2.1); fragments are a family transformation with a fast
refinement (§7); the theorem statements use record constructors and
selectors (§5); the lane structure is slices A to E (§11); the defects the
review found in existing code are in §13 with their lines.

What changed in the second revision (the contract patch answering
[gpt-6's second review](../planning/review-2026-09-22-bp-node-machine-2.md),
traces N01 to N18): the dialogue's four questions are decisions D-13 to D-16
(§12); the carrier table is three logical records with different lifetimes
(§2.4); selection is among enabled candidates (§4.2, §4.3, §8); receipt
overdue is defined over unresolved work (§9.6); journal admission is a
cleanup-debt invariant (§2.1); rotation is a publication protocol (§3.6);
the principal is selected by the observed channel (§2.3); every defect the
review names in a §5 statement is repaired in the statement; the minimal
loop is inside A1's proof boundary (§9.1, §11); fragment families are a
conservation invariant (§7.3); the codec boundary guidance for T1 is §4.6;
the counterexample suite is §11.1. §0.5 maps the review to sections. No
earlier section number moved.

Reading order for a lane: §0.4 and §0.5 (findings to sections), your slice
in §11, the counterexample suite (§11.1) for your theorems, then the
sections they name. §12 is the decision record, not a reading list.

This file supersedes §1.5 and §1.6 of [bp-design](bp-design.md), which
carry a pointer here and are not edited further; bp-design's packet table
(§5) and interoperability plan (§3) stay where they are.

## 0. What is true today

### 0.1 The books and the host, measured

| What | Where | Certified at its digest (persvati `certify-20260922T121645Z-3620455` unless noted) |
| --- | --- | --- |
| the two ends: `fn-bpn-send`, `fn-bpn-receive`, `fn-bpn-expiry`, `fn-bpn-hop-exceededp`, `fn-bpn-next-hop-count`, `fn-bpn-forward-decision`; K1 to K5 | `books/bp-node.lisp` | green |
| the outbound lifecycle: `fn-bpn-machine-state`, `fn-bpn-job`, `fn-bpn-propose`, `fn-bpn-persist-result-step`, `fn-bpn-apply-record`, `fn-bpn-replay-records`, `fn-bpn-step`, `fn-bpn-trace`; M1 to M3 | `books/bp-node-machine.lisp` | green |
| typing, preservation, the confinement pair | `books/bp-node-machine-invariants.lisp` | green |
| `fn-bpn-lifecycle-invariantp` and PRF-046's three keystones | `books/bp-node-machine-authorization.lisp` | green |
| FNBS kinds 2 to 4, the namespace plan | `books/bp-node-machine-codec.lisp` | green |
| FNBS kind 1, the frontier `(:bpn-sequence n)`, `fn-bpn-sequence-reserve` | `books/bp-node-records.lisp` | green |
| PRF-045's non-reuse and persistence-cut models | `books/bp-sequence-fidelity.lisp`, `books/bp-sequence-persistence.lisp` | green |
| the receive-evidence namespace | `books/bp-receive-evidence.lisp` | green |
| reference fragmentation/reassembly; cursor cutter and bounded position scanner proved equal on all inputs; whole-parent restoration, fragment/reassemble inverse, consumed-fragment agreement and indexed second-cut offset composition | `books/bp-fragment.lisp`, `books/bp-fragment-invariants.lisp`, `books/bp-fragment-fast.lisp` | scoped C1 certificate in `planning/evidence/bp-fragment-c1-subset-2026-09-23.md`; principal/coherence active-set partition and machine-level N10 remain open |
| the receiver, the FNRJ journal, the join the host calls (`fn-bpaj-dispatch`) | `books/bp-receipt*.lisp`, `books/bp-native-app.lisp`, `-fast` | receipt books green; `bp-native-app`, `-fast`, `bp-receiver-evolving-*` red |
| the release decision and, since `9dd5e3a2`, `fn-bprl-release-record`, `fn-bprl-replay-records`, `fn-bprl-replay-journal` | `books/bp-release.lisp` | green, persvati `certify-20260922T184059Z-2797731` |
| the convergence layer, C1 to C4 | `books/tcpcl-*.lisp` | green |
| the contact scheduler and its per-peer table | `books/scheduler.lisp`, `books/scheduler-peers.lisp` | green; no native caller |

The host:

- `host/native/bp-service.lisp:110-116`, `fnn-bps-step`, is the one call to
  `fn-bpn-step`, a pure `(state, event) -> (state, effects)` adapter. The
  events it issues: `:enqueue`, `:persist-result`, `:forward-result`,
  `:clock`, `:contact`, `:restart`. `:resume` is never issued.
- The contact is the literal `t` for every ready peer
  (`bp-service.lisp:317-318`).
- One TCP connection per bundle attempt, torn down inside `:cl-send`; the
  XFER_REFUSE reason is logged at `tcpcl.lisp:274` and dropped.
- Reception does not go through the machine. `fnn-tcl-act`
  (`tcpcl.lisp:244-267`) holds the final XFER_ACK, calls `*fnn-tcl-deliver*`,
  and flushes the ACK when the callback returns normally, whatever it
  decided. `fnn-bpapp-deliver` (`bp-app.lisp:152`) runs the FNRJ join and
  the owner Store submission under the owner mutex, returns normally on
  `:busy` and on refusal (`:177-180`), and parks the receipt bundle on the
  connection (`:188-196`) after a test cut `fnn-bpapp-pause-after-decision`
  (`:143`).
- The route 7-tuple is built from command-line arguments and read back by
  position (`bp-service.lisp:162-167`).

### 0.2 What bp-design §1.5.1 says that is no longer true

`fn-bpn-step`, `fn-bpn-trace` and `fn-bpn-machine-statep` exist
(`bp-node-machine.lisp:640`, `:657`, `:270`), outbound only. Kind 1 and kinds
2 to 4 exist. Still true: reassembly is not wired, status reports are absent,
dispatch has no routing table, there is no bundle list with retention
constraints, T1 to T6 are unproved, nothing calls `fn-retain-release` from
the BP path.

The finite `fn-bpnf-step` foundation receives a parsed bundle and its exact
wire only with typed `(:cl session xfer peer-eid principal generation)`
provenance. `session` is a pair of unsigned 64-bit counters, `xfer` and
`generation` are unsigned 64-bit, `peer-eid` is a BP EID, and `principal` is
nil or bounded canonical text octets. This checks replayable provenance shape;
the host must still establish that the principal was admitted by the current
session configuration. The foundation delegates outbound events to
`fn-bpn-step`; the native BP service calls `fn-bpnf-step` for durable kind-5
reception and outbound events. The inherited
`fn-bpn-step`, its bounded restart replay, `fn-bpnf-recover-fnbs-step`, and
`fn-bpnf-step` have verified guards in `bp-node-machine-guards.lisp`.
Recovery validates whole held rows on the cold path; ordinary steps do not.
Reception issues an FNBS operation only when its epoch and operation ID fit
the 64-bit frame field; the maximum operation ID is a terminal frontier and
is refused so the incremented state frontier remains representable.
The ACL2 mixed FNBS namespace plan partitions legacy and received kind-5/7 final names
before their respective byte decoders and rejects unknown names. The native
caller carries the base-state invariant and validates delegated outbound
events at the boundary; guard verification alone does not establish those
facts for the service adapter.
If the FNBS kind-5 encoder refuses a proposed record as non-frameable, the
native effect driver must return the matching `:persist-result` with
`:refused`; it cannot issue a stored receive answer or leave a pending
operation waiting for a callback that will never arrive.

The A3 application extension selects a locally addressed pending held row
from the same foundation list. `:deliver` allocates a volatile epoch/marker
pair; `:deliver-result` must echo that pair and exact held key before issuing
a kind-7 FNBS publication. The kind-7 row binds the earlier kind-5 arrival
and primary identity, application disposition, and bounded detail. Only its
durable publication changes the held dispatch and creates an owed receipt
handoff for a successful request. Mixed replay folds kind-5 and kind-7 rows
in one ordered epoch/operation stream and rejects an orphan, mismatched,
repeated or reversed delivery. An ambiguous Store/FNRJ result fences all
non-recovery foundation events. This logical join is not yet a native article
and return-receipt service: its publisher, replay and application caller must
be connected through one native `fnn-bps` handle, then tested after process
death. TCPCL custody remains independent of application commitment.

### 0.3 The absences this design closes

1. One held-bundle list with RFC 9171 §5 retention constraints for every
   bundle, whatever its ingress.
2. Reception through the machine, with an explicit disposition and the
   data-carrier ACK released on durable BP acceptance only.
3. Dispatch from a live routing table; history replayed without it.
4. Authoritative submission outcomes and receipt handoffs that outlive
   the carrier, beside an evictable report-correlation index (§2.4).
5. The FNRJ receipt handed to FNBS as a restartable, idempotent outbox
   whose "owed" is a durable handoff disposition, and
   receipt ADUs delivered to the sender's release join.
6. Reassembly and proactive fragmentation as capacity-accounted family
   transformations over a fast refinement of the reference.
7. Status reports: four assertions, generation off by default.
8. A serialized service loop with a bounded inbox and attempt/session
   correlation, the scheduler behind a real persistence boundary.
9. Five budgets, an immutable arrival order, and a stated operating
   envelope.
10. K6: the delivered request's admission is `fn-peer-decide-transfer` over
    an admitted principal.

### 0.4 The review's findings, where each is answered

| Finding | Repair in | Gate (trace) | Slice | Existing-code defect (§13) |
| --- | --- | --- | --- | --- |
| F-A scheduler supplies `:durable` itself | §8 | BP-R01 | A | D1 |
| F-B discard loses report correlation; no report-free retry | §2.4, §9.6 | BP-R08, BP-R09 | A (binding), B (policy, gate) | D2 |
| F-C receipt handoff is not an outbox | §9.4 | BP-R03, BP-R04, BP-R05 | A | D3 |
| F-D normal callback return is not the ACK contract | §9.2 | BP-R10 | A | D4, D5 |
| F-E same id, different hop-local image | §4.1, §4.4 | BP-R06, BP-R07 | A | D6 |
| F-F reassembly retains fragments, needs a 65th slot | §7.2 | BP-R11, BP-R13 | C | |
| F-G fragmentation is a multi-record protocol | §7.3 | BP-R12 | C | |
| F-H reference reassembler is quadratic; whole-state checks remain | §7.4, §2.7 | BP-R22 | C (fragments), A (checks) | D7, D8, D12 |
| F-I replay must not consult today's routes | §3.4, §4.5, §7.5 | BP-R14 | A (applicability), B (reroute gate) | |
| F-J K6 provenance and exact binding | §2.3, §6 | BP-R19, BP-R20 | A | |
| F-K five theorem defects | §5 | teeth rule §5.0 | A, C | |
| F-L clock sweep does not guard progress | §4.2 | BP-R16, BP-R17 | A | |
| F-M journal budget is not live capacity | §2.1, §4.3 | BP-R21, BP-R24 | A (budgets), E (envelope) | D9 |
| F-N event queue and correlation | §9.1, §4.3 | BP-R15, BP-R24 | B | D10 |

### 0.5 The second review, where each item is answered

| Review item | Repair in | Trace | Slice | §13 |
| --- | --- | --- | --- | --- |
| Q1 rotation needs a publication protocol | §3.6, §2.1, D-13 | N16 | E (with A2's T6) | |
| Q2 address-bound peer, EID a consistency check | §2.3, §6, D-14 | N15 | A3 | |
| Q3 Store event order as a contract | §10, §11 (A3), D-15 | N14 | T4, A3 | |
| Q4 requester retry, stable application identity, durable handoff | §2.4, §9.4, §9.6, D-16 | N01, N13 | A1 (records), A3 | |
| 2.1 binding retirement changes authoritative behaviour | §2.4, §4.1, §4.4 | N01 | A1, A3 | |
| 2.2 oldest-first blocks useful work | §4.2, §4.3, §8 | N03, N04 | A1 | |
| 2.3 a delivered report disables retry | §9.6, T5 | N02 | A3, B | D22 |
| 2.4 cleanup reserve is not an invariant | §2.1 | N05 | A1, E | |
| T1 expiry scope and ADU class | T1 | | A1 | |
| T2/T3 teeth are not exact checks | §5.0, T2, T3, §11.1 | | A1 | |
| T4 already-fragmented parent; fast domain; offset zero | T4, §7.2 | N09, N10 | C1, C2 | D19, D20 |
| T5 administrative input versus branch | T5 | N11 | A1 | |
| T6 epoch, issued publication, fixed point, unanchored attempts, queue binding | T6, §2.6 | N06, N07, N08 | A1, A2 | D18 |
| K6 arity and peer identifier | §6 | | A3 | D21 |
| 5.7 progress assumptions | §5.7, §8.1 | N18 | B | |
| codec boundary (their §4) | §4.6 | N17 | T1 | |
| fragment families (their §7) | §7.2, §7.3 | N09, N10 | C1, C2 | |
| observable progress (their §8) | §8.1 | N18 | B, E | |
| reports (their §9) | §7.6, §9.6 | N02 | D1, B | |
| A1 gate (their §10) | §9.1, §9.2, §11 | N12, N14 | A1, A3 | |

## 1. The one decision: one held-bundle list, four identities

RFC 9171 §5 has one bundle store in which every bundle carries retention
constraints and is dispatched, forwarded, delivered, expired, deleted and
discarded by the same steps. **The machine keeps one list of held bundles and
one BP transition authority** (§12, D-1): no second inbound machine, one
pending proposal, one token frontier, one fence, records applied on
`:durable`. Today's `fn-bpn-job` becomes the local-submission case of
`fn-bpn-held`; its route leaves the record (§2.5).

Inside that one list, four identities are separate fields and are never
substituted for one another (§2.3): the **bundle identity** (RFC 9171
§4.2.1), the **submission identity** (which local operation authored it),
the **forwarding-attempt identity** (which durable attempt a CL outcome
completes), and the **ingress provenance** (how it arrived and under which
admitted principal).

Not in the machine's state: the workflow image (`fn-bp-statep`) and anything
that includes `bp-workflow` or the store codec (review F3 of 2026-09-22).
The application's obligations are the workflow's; the machine emits nothing
that could release them (T2's confinement pair).

## 2. State

### 2.1 Configuration, policy and the five budgets

`fn-bpn-config` (`bp-node.lisp:81-90`) is unchanged. The machine's knobs:

```lisp
(fn-defrecord fn-bpn-policy
  :tag :fn-bpn-policy
  :constructor (fn-bpn-policy reports previous-node
                              max-held max-octets
                              stage-slots stage-octets
                              max-outcomes max-correlation control-reserve
                              owner-backoff)
  :fields ((fn-bpn-policy-reports fn-bpn-report-policyp)      ; nil, or the set of assertions generated; default nil (RFC 9171 §5.1)
           (fn-bpn-policy-previous-node fn-bpn-machine-boolp)
           (fn-bpn-policy-max-held fn-bpn-machine-limitp)     ; live slots, 64
           (fn-bpn-policy-max-octets fn-bpn-machine-limitp)   ; live bytes, 16777216
           (fn-bpn-policy-stage-slots fn-bpn-machine-limitp)  ; cap on slots reserved for open families (§7.3)
           (fn-bpn-policy-stage-octets fn-bpn-machine-limitp)
           (fn-bpn-policy-max-outcomes fn-bpn-machine-limitp) ; authoritative history: submission outcomes, receipt handoffs, conflict records (§2.4)
           (fn-bpn-policy-max-correlation fn-bpn-machine-limitp) ; evictable report-correlation index (§2.4)
           (fn-bpn-policy-control-reserve fn-bpn-machine-limitp) ; journal records kept free for kinds 12 and 13 (below)
           (fn-bpn-policy-owner-backoff fn-bpn-machine-limitp))  ; monotonic interval before a :busy delivery is eligible again (§4.2)
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)
```

The five budgets are distinct and each is checked by name:

| Budget | Measure | Consumed by | Released by |
| --- | --- | --- | --- |
| live slots | `(len held)` + slots reserved by open plans ≤ `max-held` | kind 5; kind 15 (reserves one per planned child) | kind 11; kind 17; kind 18 (net `1 - (len ids)`) |
| live bytes | `fn-bpn-held-octets` + octets reserved by open plans ≤ `max-octets` | same | same |
| staged space | slots and octets reserved by open plans ≤ `stage-slots`, `stage-octets` (a cap within the two above, not beside them) | kind 15 | kind 16 (reservation becomes live), kind 17 |
| authoritative history | submission outcomes + receipt handoffs + conflict records ≤ `max-outcomes` | kind 5 with a submission, kind 7 creating a handoff, kind 14 | kind 12, under §2.4's retirement rule only |
| journal authority | `remaining(s)` = `*fn-bpn-machine-max-records*` − (`next-token` − `generation-base`) | every record | rotation (§3.6) starts a new physical generation |

The report-correlation index is bounded by `max-correlation` and is not a
budget: insertion beyond the bound evicts its oldest entry (§2.4).

**Journal admission is a cleanup-debt invariant** (review-2 §2.4). The
debt `D(s)` is the number of records the machine is committed to writing
before every live entry, attempt, plan and owed handoff reaches retirement:

```text
D(s)       = Σ_{h live} debt(h) + Σ_{P open} debt(P) + 3 · |owed handoffs|
debt(h)    = 1                                        ; its discard, kind 11
           + [h retained by a constraint, not deleted]; one terminal record: 7, 9 on :sent or (:refused 1), 10, or consumption by 18
           + [h has (:forwarding ...)]                 ; the reserved result of its attempt, kind 9, whatever the outcome
           + 3 · [h is a local whole :request not yet delivered] ; the handoff it can create (§2.4)
debt(P)    = 1 + 3 · |unmaterialized children of P|   ; kind 17, and per child kind 16 plus the child's own 2
owed handoff: 3                                       ; the receipt carrier's kind 5 and its own 2
```

The invariant, a conjunct of `fn-bpn-machine-statep`:

```text
remaining(s) >= D(s) + R
```

`R` is the rotation reserve: the records the retiring generation must
still accept for rotation to run. Under §3.6's protocol it is 0, because
rotation writes only into the new generation and the selection namespace;
it stays in the statement so that any protocol writing a marker into the
retiring generation must pay for it. `control-reserve` is an **admission
margin** above the invariant, not part of it.

Every proposed record `r` of cost 1 either **pays debt** (`D` falls by at
least 1: kinds 7, 9, 10, 11, 16, 17, kind 6 `:administrative`, and kind 18
when its inputs' debt exceeds its output's) and is never refused for
journal credit, or **spends free credit** and is admitted only when
`remaining(s) − D(s) − R − control-reserve ≥ 1 + ΔD(r)`: kind 5 (ΔD = 2,
or 5 for a local request), kind 6 otherwise (0), kind 8 (+1, the reserved
result), kind 15 (1 + 3·children), kind 14 (0), kind 18 otherwise (a
reassembled request gains the +3 its fragments did not carry). Kinds 12
and 13 (ΔD = 0) may use the margin: they need only `remaining(s) − D(s) −
R ≥ 1`, so settlement and rerouting do not starve at the frontier while
the invariant still holds. A failed forwarding result (kind 9, `:failed`, `:uncertain` or a
refusal other than `(:refused 1)`) is paid by the credit its kind 8
reserved; this is N05's counterexample closed. A report is a kind 5 like
any other and can spend only free credit, so it never consumes credit that
closes accepted work. The keystones, in `-invariants`:

- `fn-bpn-step-preserves-journal-debt-cover`: the inequality is preserved by
  every event (a conjunct of T6's preservation, stated alone so its teeth
  are its own).
- `fn-bpn-debt-paying-record-is-never-refused-for-credit`: a proposal whose
  record pays debt is never answered `:journal-exhausted` or `:capacity`
  for journal credit.

When a transition's record cannot be admitted, the answer is its refusal
effect (`:capacity`) and nothing durable; `:journal-exhausted` and the fence
are reached only if the inequality itself would fail, which the invariant
says is unreachable (repair of D9: today `fn-bpn-propose` answers the
refusal with the state unchanged and no fence, `bp-node-machine.lisp:372-373`).

A lifecycle is about five records; 4096 records per physical generation is
about 800 simple lifecycles, fewer with attempts, reports and fragments.
Rotation (§3.6, D-13) starts a new physical generation; logical frontiers do
not reset.

### 2.2 A held bundle

```lisp
(fn-defrecord fn-bpn-held
  :tag :fn-bpn-held
  :constructor (fn-bpn-make-held id arrival ingress submission lineage bundle wire
                                 anchor dispatch next-hop constraints attempt deleted token)
  :fields ((fn-bpn-held-id fn-bpn-bundle-idp)               ; (fn-bpp-bundle-id primary (len payload))
           (fn-bpn-held-arrival fn-bpn-machine-u64p)        ; token of its kind-5/16/18 record; never changes
           (fn-bpn-held-ingress fn-bpn-ingressp)            ; §2.3
           (fn-bpn-held-submission fn-bpn-maybe-submissionp); §2.3; nil for transit
           (fn-bpn-held-lineage fn-bpn-lineagep)            ; nil, or (:family family-id index) (§7)
           (fn-bpn-held-bundle fn-bpb-bundlep)
           (fn-bpn-held-wire fn-cbor-octet-listp)           ; = (fn-bpb-encode bundle)
           (fn-bpn-held-anchor fn-clock-age-anchorp)
           (fn-bpn-held-dispatch fn-bpn-maybe-dispatchp)    ; nil | (t6 . disposition) of its kind-6 record
           (fn-bpn-held-next-hop fn-bpn-maybe-eidp)         ; the durable forwarding decision (§3.4)
           (fn-bpn-held-constraints fn-bpn-constraint-setp) ; subset of :dispatch-pending :forward-pending :reassembly-pending
           (fn-bpn-held-attempt fn-bpn-maybe-inflightp)     ; §2.3
           (fn-bpn-held-deleted fn-bpn-maybe-reasonp)       ; nil | an RFC 9171 §6.1.1 Table 1 keyword
           (fn-bpn-held-token fn-bpn-machine-u64p))         ; last record that touched it
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)

(defun fn-bpn-retainedp (h)
  (or (consp (fn-bpn-held-constraints h)) (consp (fn-bpn-held-attempt h))))
```

List invariants (conjuncts of `fn-bpn-machine-statep`): ids unique;
arrivals unique; `wire = (fn-bpb-encode bundle)`; a deleted entry has no
constraint and no attempt; an entry with `:forward-pending` either has a
next hop or is blocked on routes (§4.5); a submission names at most one live
entry.

### 2.3 Identities and provenance

```lisp
;; submission identity: which local operation authored the bundle
(defun fn-bpn-submissionp (x)
  ;; (:work work attempt generation)       the workflow's :submit (was the job key)
  ;; (:receipt receipt-id trigger)         the FNRJ receipt receipt-id, sent in reply to the request
  ;;                                       carrier trigger (§9.4). trigger is the delivered request
  ;;                                       bundle's identity: a carrier/attempt identity, distinct from
  ;;                                       the application request, which is unchanged across retries
  ;;                                       (D-16). receipt-id is fn-bpaj-receipt-id of the request
  ;;                                       (bp-native-app.lisp:408), stable per work.
  ;; (:report subject-id assertion)        a status report about subject-id (§7.6)
  ...)

;; ingress provenance: how the bundle arrived
(defun fn-bpn-ingressp (x)
  ;; (:cl session xfer peer-eid principal generation)
  ;;     session    fn-bpn-session-idp, (incarnation . counter), host-issued
  ;;     xfer       the TCPCL transfer id
  ;;     peer-eid   the node ID the peer announced in SESS_INIT: data, not authority
  ;;     principal  the configured peer name the session admitted, or nil (below)
  ;;     generation the configuration generation of that admission
  ;; (:local)                              authored here (a submission is set)
  ;; (:family family-id ingresses)         reassembled; the fragments' ingresses, deduplicated
  ...)

;; forwarding-attempt identity, and the volatile delivery marker
(defun fn-bpn-maybe-inflightp (x)
  ;; nil
  ;; (:forwarding attempt-token peer session)  attempt-token = the token of its kind-8 record (durable)
  ;; (:delivering delivery-token)              delivery-token = the token of its kind-6 :deliver record (volatile)
  ...)
```

**Which carries authority.** Only `principal` does. It is set when
`fn-bpaj-session-principal` (below) admitted the session: the observed
channel selected a configured peer at `generation`, that peer has a BP
trust row naming its boundary, and the announced `peer-eid` is one of the
peer's `(:bp eid)` rows; otherwise it is nil. An announced peer EID is
never a principal and never selects one. The bundle's source and
destination EIDs are data: the destination selects local delivery, the
source (report-to for reports) addresses a receipt or report. The fragment
lineage says which fragments a reassembled ADU came from; its principal is
the common principal of every fragment's ingress, or nil when they differ or
any is nil. Configuration generation says which configuration admitted the
principal; K6 decides against the configuration current at delivery (§6).

**How a session gets its principal** (D-14, review-2 Q2). The order is
fixed:

```text
observed channel -> configured peer -> allowed-EID check -> admitted principal
```

never `announced EID -> peer lookup`. The decision is ACL2's,
`fn-bpaj-session-principal cfg channel announced-eid` (in
`books/bp-session-admission.lisp`), composed with raw announced-EID parsing
and typed FNBS ingress construction by `fn-bpaj-tcpcl-ingress-result` (in
`books/bp-channel-ingress.lisp`). The native host calls that one result at
each completed inbound transfer after TCPCL negotiation; `channel` is what it
observed (listener, network namespace, peer address), never what the peer
said. The inner selector answers `(:admitted peer-name generation)`,
`(:refused :no-configured-peer)` (no peer row's boundary matches the channel),
`(:refused :no-trust-profile)` (the matched peer has no BP trust row), and
`(:refused :eid-mismatch)` (the announced node ID is not one of that
peer's `(:bp eid)` rows). The finite loopback selector currently also reports
`:channel` and `:ambiguous-peer`, and combines missing boundary and trust as
`:no-trust-profile`. The outer result retains the ACL2 refusal reason and
returns a typed anonymous ingress for a valid announced EID; malformed or
overlong raw EID bytes return no ingress. A refused session carries principal nil; it may
still hand the node transit bundles if the operator's policy allows
unauthenticated transit, but nothing it delivers is admitted by K6.

The finite native slice observes IPv4 local listener and remote address from
the accepted socket. A durable `bp-boundary add` peer row declares loopback,
no translation, and `all-co-resident`; the selector first requires one peer
for that channel and only then checks its configured BP EID. ACL2 stamps
the selected peer name and configuration generation on ingress. Application
request and receipt handoff require that name, generation, and configured EID
still agree with the live owner configuration; a nil principal refuses the
application handoff while retaining BP custody. This is a loopback boundary
profile, not an origin-authentication claim. The general A-BP-PATH assumption,
network and private-tunnel profiles, and the full K6 transit-policy join
remain open.

The trust row names its boundary. `"bp-trust" "network"` alone is not a
valid row; the row is `"bp-trust" "network"` together with
`"bp-boundary"` naming (1) the listener (interface address and port, or
network namespace), (2) the peer address that selects this peer, (3) the
address translation on the path (`none`, or the NAT or proxy named), and
(4) the set of originators that can reach that listener from that address
(for loopback: every process on the host). The node's page prints the row.
The assumption it rests on is a constrained function in
`books/assumptions.lisp`, and K6's soundness theorems mention it:

```lisp
;; A-BP-PATH. "A connection the host observes on listener L from address a,
;; inside boundary B, originates from an originator B names for a."
(encapsulate (((fn-assume-bp-path-authentic * * *) => *)) ...)  ; boundary channel peer-name
```

Keystones: `fn-bpaj-session-principal-is-selected-by-the-channel` (an
admitted principal is the peer the channel selects, and the announced EID
is among its allowed EIDs); `fn-bpaj-announced-eid-never-selects-a-peer`
(for one channel, two announced EIDs that are both admitted give the same
peer). This is the same trust statement as NNTP source-address admission
when the boundary and adversary are the same; it is not origin
authentication, and an admitted hop is not evidence that the bundle's
source or a receipt's issuer is that hop (RFC 9174 §4.6, RFC 9172 §2.2).
Three roles stay separate fields: the ingress principal (who handed this
node the work), the request's `authorization-context` (who authored it,
T9's subject), and the receipt issuer (who may release this obligation);
v0 claims only the first, under A-BP-PATH.

### 2.4 Carrier history: three logical records with three lifetimes

The first revision's one carrier table served three consumers: repeated
submissions answered from a persisted result, the receipt outbox's "still
owed" decision, and report interpretation after discard. Evicting it under
pressure turned a completed submission into a new one and a handed-off
receipt into owed output (review-2 §2.1, N01). They are three records, of
which two are authoritative and one is an index. None is another machine;
all three are fields of the machine state, changed only by records.

```lisp
;; 1. Submission outcome: AUTHORITATIVE. Answers a repeated :transmit and
;;    every post-discard decision about a bundle this node authored.
(fn-defrecord fn-bpn-outcome
  :tag :fn-bpn-outcome
  :constructor (fn-bpn-make-outcome submission destination adu-id bundle-id sequence
                                    commitment expiry-evidence family result)
  :fields ((fn-bpn-outcome-submission fn-bpn-submissionp)
           (fn-bpn-outcome-destination fn-bpp-eidp)        ; the request's destination, for §4.4's agreement check
           (fn-bpn-outcome-adu-id fn-bpn-content-idp)      ; content id of the ADU
           (fn-bpn-outcome-bundle-id fn-bpn-bundle-idp)
           (fn-bpn-outcome-sequence fn-bpp-timep)          ; the persisted creation sequence (§4.4)
           (fn-bpn-outcome-commitment fn-bpn-content-idp)  ; digest of the canonical immutable projection (§4.1 step 4)
           (fn-bpn-outcome-expiry-evidence fn-bpn-expiry-evidencep) ; creation time, lifetime, largest durable age and its anchor
           (fn-bpn-outcome-family fn-bpn-maybe-family-idp) ; plan id when proactively fragmented (§7.3)
           (fn-bpn-outcome-result fn-bpn-outcome-resultp)) ; :held :forwarded :delivered (:deleted reason) :discarded (:family-failed ...)
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)

;; 2. Receipt handoff: AUTHORITATIVE. The reply trigger and whether the
;;    receipt was handed to FNBS.
(fn-defrecord fn-bpn-handoff
  :tag :fn-bpn-handoff
  :constructor (fn-bpn-make-handoff receipt-id trigger disposition)
  :fields ((fn-bpn-handoff-receipt-id fn-bpn-machine-textp)
           (fn-bpn-handoff-trigger fn-bpn-bundle-idp)       ; the delivered request carrier (§2.3)
           (fn-bpn-handoff-disposition fn-bpn-handoff-dispositionp)) ; :owed | (:handed-off token)
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)

;; 3. Report correlation: an OBSERVATIONAL INDEX, bounded, evictable.
(fn-defrecord fn-bpn-correlation
  :tag :fn-bpn-correlation
  :constructor (fn-bpn-make-correlation subject submission attempts)
  :fields ((fn-bpn-correlation-subject fn-bpn-report-subjectp) ; bundle id, with fragment offset and length for a child
           (fn-bpn-correlation-submission fn-bpn-submissionp)
           (fn-bpn-correlation-attempts fn-bpn-token-listp))  ; attempt tokens, most recent first, bounded
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)
```

**Outcomes.** Created by the kind-5 record of a bundle with a submission,
its result updated by kinds 7, 9, 10, 11, 16 and 17, and kept across kind
11 (discard). Removed only by kind 12 `(:history-retired token key)`:

- a `:work` outcome when the host reports `(:work-settled submission)` (the
  workflow released or abandoned the work, §9.6); the workflow never
  transmits that submission again, because a submission names its attempt;
- a `:receipt` or `:report` outcome when the lifetime of its subject has
  elapsed under a decidable observation (the expiry evidence is in the
  record, so no journal rescan is needed). After that, a retransmission of
  the trigger is expired before dispatch (T3) and cannot create a new
  handoff under a decidable clock.

That is the **idempotency window**: a repeated `:transmit` of a submission
is answered from its outcome for as long as the workflow can repeat it. The
**stale-operation behaviour** past the window is stated, not hidden: under
an uncertain clock a retransmitted, already-expired trigger can be
delivered again, and the join answers `:return-receipt` from the committed
receipt (`bp-native-app.lisp:404`), so the worst case is a second receipt
carrier for the same receipt fact, never a second receipt fact, article or
pin. When `max-outcomes` is reached and nothing is retirable, a new
submission is refused `(:capacity :history)`; nothing authoritative is
evicted to make room (question 3 in §12).

**Handoffs.** Created `:owed` by the kind-7 record of a local `:request`
delivery whose outcome carries a receipt, `(:accepted rid)`,
`(:duplicate rid)` or `(:returned rid)` (§9.3); set to `(:handed-off t)`
by the kind-5 record `t` of submission `(:receipt rid trigger)`; retired
by kind 12 with that submission's outcome. An `:owed` handoff is never
retired (it is debt, §2.1). "Owed" is the presence of an `:owed` handoff,
never the absence of anything, so no eviction can make a handed-off
receipt owed again. The crash between the FNRJ commit and kind 7 is
covered without a second record: the request entry is still
`:dispatch-pending`, it is redelivered, and the join answers from the
committed receipt.

**Correlation.** Inserted by kind 5 (with a submission), kind 8 (the
attempt token) and kind 16 (a child's subject); on insertion beyond
`max-correlation` the oldest entry is evicted. Eviction is a deterministic
function of the records, so replay reproduces it and it needs no record of
its own. Losing an entry loses only the interpretation of a later report.
`fn-bpn-correlation-of-subject subject st` finds the entry whose subject
matches (a fragment report names offset and length) and the observation is
emitted for its submission; this is what makes BP-R08 hold after the home
carrier is physically gone.

**Post-discard decisions read only authoritative fields.** Duplicate
equivalence against a discarded bundle this node authored compares the
outcome's `commitment` (§4.1 step 4); the destination and ADU checks of
§4.4 read `destination` and `adu-id`; retirement reads `expiry-evidence`.
A commitment comparison concludes equality of digests, and the claim that
the immutable projections are equal is made only under the collision
assumption of the digest in use, with its collision figure (SHA-256: about
2^-128 for a chosen pair) quoted beside it; it is never stated as an
exact-byte theorem. `fn-bpn-machine-statep` requires every live entry with
a submission to have an outcome whose `commitment` is the digest of that
entry's immutable projection.

### 2.5 The routing table: live selection only

```lisp
(fn-defrecord fn-bpn-route
  :tag :fn-bpn-route
  :constructor (fn-bpn-make-route peer-name peer-eid cl reach)
  :fields ((fn-bpn-route-peer-name fn-bpn-machine-textp)
           (fn-bpn-route-peer-eid fn-bpp-eidp)
           (fn-bpn-route-cl fn-bpn-routep)            ; today's 7-tuple, bp-node-machine.lisp:31-39
           (fn-bpn-route-reach fn-bpn-eid-listp))
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)
(defun fn-bpn-next-hop (routes destination) ...)  ; first route whose peer-eid or reach names the destination's node ID
```

The table is installed by `(:routes table generation)` and is never
persisted by the machine. It is consulted only to choose a new action: a
dispatch, a reroute, an attempt's CL address. It is never consulted to
decide whether a historical record applies (§3.4). Its configuration home is
§7.5.

### 2.6 The machine state

```lisp
(fn-defrecord fn-bpn-machine-state
  :tag :fn-bpn-machine-state
  :constructor (fn-bpn-make-machine-state config policy held outcomes handoffs correlation
                                          families generation generation-base
                                          sessions routes route-generation waits cursor
                                          pending issued quiescing fenced next-token)
  :fields ((fn-bpn-machine-state-config fn-bpn-configp)
           (fn-bpn-machine-state-policy fn-bpn-policyp)
           (fn-bpn-machine-state-held fn-bpn-held-listp)
           (fn-bpn-machine-state-outcomes fn-bpn-outcome-listp)   ; unique submissions (§2.4)
           (fn-bpn-machine-state-handoffs fn-bpn-handoff-listp)   ; unique (receipt-id . trigger) (§2.4)
           (fn-bpn-machine-state-correlation fn-bpn-correlation-listp) ; bounded index (§2.4)
           (fn-bpn-machine-state-families fn-bpn-family-listp)    ; open family plans (§7), nil until slice C
           (fn-bpn-machine-state-generation fn-bpn-machine-u64p)  ; physical journal generation (§3.6)
           (fn-bpn-machine-state-generation-base fn-bpn-machine-u64p) ; first logical token of that generation
           (fn-bpn-machine-state-sessions fn-bpn-session-listp)   ; open (peer-eid . session . mru) triples, volatile
           (fn-bpn-machine-state-routes fn-bpn-route-listp)       ; volatile
           (fn-bpn-machine-state-route-generation fn-bpn-machine-u64p)
           (fn-bpn-machine-state-waits fn-bpn-wait-listp)         ; (id . wait) per blocked entry, volatile (§4.2)
           (fn-bpn-machine-state-cursor fn-bpn-action-classp)     ; next action class to serve, volatile (§4.2)
           (fn-bpn-machine-state-pending fn-bpn-maybe-pendingp)
           (fn-bpn-machine-state-issued fn-bpn-maybe-issuedp)     ; nil | (token . record): issued, not definitively answered (T6)
           (fn-bpn-machine-state-quiescing fn-bpn-machine-boolp)  ; rotation's quiesce (§3.6), volatile
           (fn-bpn-machine-state-fenced fn-bpn-machine-boolp)
           (fn-bpn-machine-state-next-token fn-bpn-machine-u64p)) ; logical, globally monotone, never reset
  :recognizer fn-bpn-machine-recordp :recognizer-verify-guards nil
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)
```

`issued` is set when a `:persist` effect is emitted and cleared only by a
definitive answer for its token (`:durable` or `:refused`). `:uncertain`
clears `pending` and fences, as today (`bp-node-machine.lisp:494-521`), but
leaves `issued`: a record whose publication may be visible in the
authoritative directory is tracked independently of the volatile pending
field (review-2 T6, N06, D18).

`fn-bpn-machine-statep` conjoins the record recognizer, the five budgets,
the journal-debt cover (§2.1), §2.2's list invariants, outcome/held
agreement (an outcome with result `:held` names a live entry and every live
entry with a submission has one, with the commitment of §2.4), handoff
uniqueness, `issued` agreeing with `pending` when both are set, and the
pending-token equation.
`fn-bpn-machine-invariantp` and `fn-bpn-lifecycle-invariantp` keep their
names; the latter's authorization relation (`fn-bpn-proposal-effectsp`)
binds every proposed record to its exact success, refusal and uncertainty
effects, and for kind 8 binds the exact forwarding image, the peer, the
session and the CL address from the live table (review §2.1: not weakened to
"a typed `:cl-send`").

**Durable and volatile fields.** `fn-bpn-durable-projection st` is a
machine state: config, policy, held (with `(:delivering ...)` markers
erased), outcomes, handoffs, correlation, families, generation,
generation-base and next-token kept; sessions, routes, route-generation,
waits, cursor, pending, issued, quiescing and fenced set to their restart
values (nil, nil, 0, nil, the first class, nil, nil, nil, nil). Because it
is a state, not a separate projection record, a fixed-point statement over
it is well typed (T6). `fn-bpn-clear-inflight` erases every attempt and
delivery marker, anchored or not; `fn-bpn-reanchor st obs` is §4.5's
re-anchoring. These three are the vocabulary of T6.

### 2.7 No whole-state revalidation on the served path

`fn-bpn-step` retains its total logical malformed-state response but its
verified `mbe` executable arm calls `fn-bpn-dispatch` directly. The guard is
`fn-bpn-machine-statep` together with `fn-bpn-machine-eventp`; ACL2 guard
verification proves agreement of the logical and executable arms under that
guard. Both saved-image profiles include `bp-node-machine-guards`.
`fnn-bps-open` checks the initial machine invariant once, and `fnn-bps-step`
validates `fn-bpn-machine-eventp` before calling this exact `fn-bpn-step`.
Only initialization and step answers write the service's state;
`fn-bpn-step-preserves-machine-invariant` carries the state premise between
calls. The native image containing this wiring has not yet been built or
exercised in this packet. The audit extends past `fn-bpn-step`:
`fn-bpn-existing-sequence` has a guard-verified `mbe` executable arm that
omits the whole-state recognizer, and the ready-peers host projection uses
the maintained state directly. §4.4's carrier lookup remains future work
for stronger dispatch bounds.

## 3. Events, effects, records

### 3.1 Events

`OBS` below is an `fn-clock-observationp`. Every event that can lead to a
delivery, an attempt or an expiry carries one (F-L).

| Event | Issued by | Notes |
| --- | --- | --- |
| `(:bundle-received octets ingress obs)` | the loop, from the TCPCL callback | answered by exactly one `:receive-answer` (§9.2) |
| `(:transmit submission destination sequence adu obs)` | the loop, for the workflow's `:submit`, an owed receipt (§9.4), or a report | idempotent by submission (§4.4) |
| `(:deliver-result id delivery-token outcome obs)` | the loop, after a `:deliver` ran | `outcome`: `:accepted`, `:duplicate`, `(:refused reason)`, `:busy`, `:uncertain`; for a `:request`, `(:accepted rid)`, `(:duplicate rid)`, `(:returned rid)` name the committed receipt (§2.4, §9.3) |
| `(:forward-result attempt-token session outcome obs)` | the loop, from the CL outcome | `outcome`: `:sent`, `(:refused code)` (RFC 9174 Table 6), `:failed`, `:uncertain` |
| `(:session peer-eid session open-p mru obs)` | the loop, on session establishment and end | replaces `(:contact peer open-p)`; `mru` the negotiated transfer MRU; a close clears only that session |
| `(:quiesce on-p obs)` | the loop, on the operator's rotate and after it | §3.6 |
| `(:generation-selected generation base-token obs)` | the loop, after the selection record is durable | §3.6 |
| `(:resume peer-eid session obs)` | the loop, a bounded per-peer progress action | §4.3 |
| `(:clock obs)` | the loop's timer | the shared progress boundary (§4.2) |
| `(:persist-result token outcome obs)` | the loop, after publishing | `:durable`, `:refused`, `:uncertain`; gains `obs` |
| `(:routes table generation)` | the loop, at open and on every configuration generation | §4.5 |
| `(:work-settled submission)` | the loop, from the workflow's release or abandonment | proposes kind 12 |
| `(:author-report subject-id assertion reason sequence obs)` | the loop, after `:report-due` | §7.6 |
| `(:restart records sequence-ready obs)` | the loop at open | §4.5 |

`fn-bpn-machine-eventp` bounds `:restart`'s record list, `:bundle-received`'s
octets by the transfer limit, `table` by `fn-bpn-route-listp`, and every
session id and token by `fn-bpn-machine-u64p`.

### 3.2 Effects

| Effect | Meaning | Host obligation |
| --- | --- | --- |
| `(:persist token record)` | publish this FNBS record under the ACL2-derived name, answer `:persist-result` | unchanged |
| `(:receive-answer ingress disposition)` | the disposition of one `:bundle-received` | §9.2; `disposition` is `:stored`, `:duplicate`, `:observed`, `(:refused reason)` or `(:uncertain reason)` |
| `(:deliver id delivery-token adu-class key payload ingress report-p)` | hand the ADU to the join for its class; answer `:deliver-result` | §9.3; `adu-class` is `:request` or `:receipt` (`fn-bpn-adu-class` over the ADU kind, `bp-adu.lisp:20-21`), anything else is `:refused :adu-class` without a `:deliver` |
| `(:cl-send cl peer-eid session attempt-token id image)` | offer `image` on `session` | answer `:forward-result` with the same attempt token and session |
| `(:transport submission status)` | relay to the workflow when `submission` is a `:work` | statuses `fn-bp-transport-statusp` accepts today |
| `(:report-due subject-id assertion reason)` | enabled and requested | §7.6 |
| `(:bundle-queue-accepted submission bundle-id sequence :durable/:duplicate)`, `-refused`, `-uncertain` | answer to `:transmit` | §4.4 |
| `(:forward-refused id peer-eid reason)`, `(:forward-stale attempt-token session)` | informational | none |
| `(:restart-ready n)`, `(:restart-fault why)`, `(:routes-installed n)`, `(:routes-refused why)`, `(:journal-exhausted)` | | `:restart-fault` refuses to serve (§3.5) |

`fn-bpn-effectp` is the enumeration; `:release` and `:receipt-prepare` are
not in it (M1, unchanged).

### 3.3 Records (FNBS kinds)

**Implementation status (2026-09-23, A2 partial).**
`books/bp-fnbs-codec.lisp` now owns the kind-5 byte frame for the typed
`:cl` reception proposed by `fn-bpnf-step`: epoch, operation ID, arrival,
session pair, transfer ID, peer EID, explicit optional-principal presence,
admission generation, and the exact received wire octets. Its decoder
reconstructs the initial held row after BP wire decoding and refuses malformed
bytes. `books/bp-fnbs-byte-publisher.lisp` models private creation/write,
file barrier, link and directory barrier with the actual `fn-bs-*` operations;
an occupied damaged final name is a recovery fault. These are the first
physical and codec parts of A2. `fn-bpnf-byte-crash-keeps-canonical-kind-five`
proves exact recovery of one fenced canonical record in any admissible crash
image that selects its final inode. The general `fn-bs-crash-imagep` to observed
journal theorem and native publisher/recovery caller are still open. The
present kind-5 subset has no
submission or receipt handoff; the broader row below remains the target.
`fn-bpnf-actual-link-crash-is-absent-or-exact` further connects the real
`fn-bs-link` pending entry to the absent-or-exact crash choices;
`fn-bpnf-directory-barrier-quiet` fixes the final name after directory
fsync. The relation across every native publisher call remains open.
The kind-5 payload has exact length `76 + peer-CBOR + principal-blob + wire`;
typed bounds give `76 + 2048 + 512 + 131072 = 133708`, below the
134144-octet frame limit. The present non-`:bad` theorem also assumes the
record's field-value predicate; removing that remaining hypothesis is open.
`books/bp-fnbs-replay.lisp` is the bounded kind-5 byte-row scanner over
canonical final names: it decodes exact frames, rejects damaged/duplicate or
out-of-order rows and capacity overflow, and reconstructs the held list and
last `(epoch . operation-id)` pair. `fn-bpnf-recover-event` constructs the
recovery-only `fn-bpnf-step` event from those exact row bytes. The step
atomically requires successful inherited base restart and ready FNBS replay,
installs both projections, clears volatile issued work, and advances to a
fresh epoch with operation ID zero. A fault leaves the uncertain state
fenced. This does not yet establish the byte-store publisher's whole-history
crash relation or a native caller. `fn-bpnf-recover-auto-event` selects the
fresh epoch as one above both the current state epoch and the replayed last
epoch; at the 64-bit terminal epoch, the step faults rather than wrapping.
Process-death callbacks cannot survive to the new process remains a host
assumption.
`books/bp-fnbs-namespace.lisp` partitions one bounded physical FNBS
directory into legacy lifecycle finals, kind-5 received finals, and hidden
stages. The old contiguous namespace planner validates the legacy subset;
the kind-5 byte replay validates the received subset. An unknown public name
faults before either replay. `fn-bpnf-mixed-recovery-plan` composes the split
with the legacy contiguous planner and returns both final-name partitions,
hidden stages, and the old token frontier. Its mixed, kind-5-only, and
legacy-gap tests certified in the coherent A2/guard batch.
`books/bp-fnbs-publication.lisp` authorizes the immutable kind-5 publisher
only from the exact pending `:store` issued echo and observed lock ownership
and absent final name. It returns ACL2-derived final name, frame bytes and
`fn-jpub-initial`; stale epoch/operation ID, changed held row, uncertain
issued status, or missing lock/name precondition faults. `fn-bpnf-stored-
frame-limit` supplies the bounded kind-5 physical read size. This join
certified in the coherent A2/guard batch and still awaits a native caller.

Every record is built by its constructor and read by selectors; no book and
no theorem matches a record by list shape. `fn-bpn-rec-kind`,
`fn-bpn-rec-token` are total over `fn-bpn-recordp`; each kind has its field
selectors and a `-of-constructor` theorem.

| Kind | Constructor | Applied as |
| --- | --- | --- |
| 1 | `(:bpn-sequence n)` | unchanged |
| 2-4 | retired | §3.5 |
| 5 | `(fn-bpn-rec-stored token held)` | append `held` (arrival = token, `:dispatch-pending`); create its outcome and correlation entry when it has a submission; a `(:receipt rid trigger)` submission sets that handoff `(:handed-off token)` |
| 6 | `(fn-bpn-rec-dispatched token id disposition)` | set `dispatch` to `(token . disposition)`; `disposition`: `:deliver` (keep `:dispatch-pending`); `(:forward next-hop)` (replace by `:forward-pending`, set next hop); `:administrative` (drop `:dispatch-pending`); `:await-fragments` (add `:reassembly-pending`) |
| 7 | `(fn-bpn-rec-delivered token id delivery-token outcome)` | drop `:dispatch-pending`; outcome result `:delivered`; an outcome naming a receipt `rid` creates handoff `(rid, id, :owed)`; `(:refused :adu-class)` is written with no `:deliver` ever emitted (T1) |
| 8 | `(fn-bpn-rec-attempting token id peer-eid session age)` | attempt `(:forwarding token peer-eid session)`; `age` kept for re-anchoring; the attempt token joins the correlation entry |
| 9 | `(fn-bpn-rec-forwarded token id attempt-token outcome)` | clear the attempt; on `:sent` or `(:refused 1)` drop `:forward-pending` and set outcome `:forwarded`; otherwise keep it |
| 10 | `(fn-bpn-rec-deleted token id reason)` | clear constraints and attempt, set `deleted`; outcome `(:deleted reason)` |
| 11 | `(fn-bpn-rec-discarded token id)` | remove the live entry; outcome `:discarded`, kept |
| 12 | `(fn-bpn-rec-history-retired token key)` | remove the outcome for submission `key`, and for a `:receipt` key its handoff; §2.4's retirement rule is part of applicability |
| 13 | `(fn-bpn-rec-rerouted token id next-hop)` | replace next hop; `nil` returns the entry to `:dispatch-pending` with `dispatch` nil |
| 14 | `(fn-bpn-rec-conflict token id ingress content-id)` | append a conflict entry to history (§4.1) |
| 15 | `(fn-bpn-rec-family-planned token family plan)` | slice C, §7.3 |
| 16 | `(fn-bpn-rec-family-child token family index held)` | slice C, §7.3 |
| 17 | `(fn-bpn-rec-family-retired token family disposition)` | slice C, §7.3; `disposition` `:materialized` or `(:terminated reason)` |
| 18 | `(fn-bpn-rec-reassembled token family held fragment-ids)` | slice C, §7.2 |
| 19 | `(fn-bpn-rec-checkpoint-chunk generation index bytes)` | slice E, §3.6; only in a new generation's staging, never applied by ordinary replay |
| 20 | `(fn-bpn-rec-checkpoint-manifest generation frontier chunk-digests)` | slice E, §3.6; the last object staged |

Slice A's codec defines kinds 5 to 14 and refuses 15 to 20 at recovery as
`(:unsupported-kind k)`; slice C adds 15 to 18 and slice E 19 and 20, each
with its replay case, so the replay theorem gains one case per kind rather
than being re-proved. Record payloads are bounded by
`*fn-bpn-lifecycle-max-payload*` (134144, `bp-node-machine-codec.lisp:24`);
a checkpoint is chunked to that bound rather than the bound raised (§3.6).

### 3.4 Applicability: historical versus live

`fn-bpn-record-applicablep st r` asks only what the durable state answers:
the token is the frontier; the entry exists (or not, for 5, 16, 18); the
constraint the record moves is present; the attempt it clears has that
attempt token; the budgets of §2.1 hold after it. It never asks whether a
route, a session or a configuration generation is current. A kind-6
`(:forward p)` names the next hop's EID and is applicable with no table at
all (F-I). Liveness of routes and sessions is checked when a transition
proposes a record, by `fn-bpn-propose`'s caller, and is part of the
authorization relation, not of applicability.

### 3.5 Retired kinds 2 to 4

No record of kinds 2, 3 or 4 is written. At recovery the codec answers a
directory that contains one with `(:restart-fault (:unsupported-schema k
name))`, the machine stays fenced, and the host prints the diagnosis and
exits `uncertain`. The directory is never treated as empty and never reset
(§12, D-2). Before the slice-A image is deployed anywhere, root confirms that
no node's lifecycle directory holds kinds 2 to 4 (the review did not verify
the design's claim that none does); historical fixtures and evidence that
contain them are kept.

### 3.6 Rotation: a new physical generation from a checkpoint (D-13)

Operator-controlled, v0, slice E. A small extension of T6 and the
publication model with a cut table, not a second storage system and not
compaction; retention policy is unchanged.

**Frontiers.** `next-token` (hence `arrival`, attempt tokens and delivery
tokens), session ids, the creation-sequence frontier of kind 1 (PRF-045, a
distinct non-reuse frontier) and the loop's operation ids are **logical and
globally monotone**: rotation never resets them. What rotation resets is the
physical record count of the current generation, `next-token −
generation-base` (§2.1). A new entry therefore never sorts ahead of an old
one, and no completion from an earlier epoch matches an operation allocated
after it.

**The protocol** (the loop drives it; every decision is a book function):

1. **Quiesce.** `(:quiesce t obs)`: the machine refuses new admissions
   (reception `(:refused :busy)`, transmit `-refused :busy`) and proposes
   only debt-paying records. The loop drains: every outstanding attempt is
   answered (sessions are closed, so an unanswered offer is `:uncertain` and
   writes its reserved kind 9); every `:delivering` marker is answered;
   the pending publication is answered. If any answer is `:uncertain` for a
   publication, the machine is fenced and rotation is abandoned: recovery
   comes first.
2. **Checkpoint.** With `pending`, `issued` and every in-flight marker nil,
   fix the frontier `t = next-token`. `fn-bpn-checkpoint st` is the durable
   projection (§2.6) of `st`: live entries with their durable age evidence,
   outcomes, handoffs, the correlation index retained by policy, open
   family plans with their remaining reservations, the logical frontiers,
   the sequence frontier, and the configuration and policy provenance
   (config generation, policy) the projection names. Sessions, routes,
   waits and delivery markers are volatile and are not historical authority.
3. **Stage.** Write the checkpoint into generation `g+1`'s staging as kind-19
   chunks, each within the record payload bound, then the kind-20 manifest
   (generation, frontier `t`, chunk count and digests), each through the
   ordinary publisher (write, file barrier, link, directory barrier).
4. **Select.** Publish the selection record `(:bpn-generation g+1
   manifest-digest)` in the generation-selection namespace (the pattern of
   kind 1's frontier namespace) and barrier it. On `:durable`, the loop
   issues `(:generation-selected g+1 t obs)`: `generation` and
   `generation-base` advance and quiescing ends. Only now may generation `g`
   cease to be recovery authority; it is kept until the next rotation
   (evidence), then removed by housekeeping.

A generation number is never reused: an unselected staging is ignored and
the next rotation uses a number greater than any observed.

**Recovery distinguishes four authorities** (`fn-bpn-generation-authority
dir`, slice E):

| Observed | Authority | Recovery |
| --- | --- | --- |
| selection names `g`; `g+1` staging incomplete (torn chunk, no manifest) | incomplete staging | recover `g`; staging ignored |
| selection names `g`; `g+1` complete and verified | complete, unselected | recover `g`; nothing was acknowledged under `g+1`, because quiesce holds until the selection is durable |
| selection names `g+1`; its manifest and chunks verify | selected | recover from the checkpoint, then `g+1`'s records |
| selection unreadable or torn, two selections, or the named manifest missing, torn or failing its digests | damaged | `(:restart-fault (:generation-authority why))`, fenced, exit uncertain |

Recovery never falls back to an older apparently valid generation after a
newer one could have acknowledged operations: the damaged row fences.

**Cut table** (N16 exercises each by `kill -9`): during a chunk write; after
the chunks and before the manifest; after the manifest, before the
selection write; selection written, barrier not answered; selection
`:durable`, before `:generation-selected`; after it, with new work admitted
and a stale completion from the previous epoch delivered (its operation id
is unknown, §9.1, and its token cannot match a newer attempt).

**The six obligations**, slice E, in `books/bp-node-rotation.lisp` (new)
beside A2's replay book:

1. `fn-bpn-checkpoint-replays-to-the-projection`: replaying a decoded
   checkpoint gives exactly `(fn-bpn-durable-projection st)`.
2. `fn-bpn-generation-authority-is-recoverable`: for every row of the cut
   table, recovery selects the authority the table names, or faults.
3. `fn-bpn-rotation-preserves-acknowledged-history`: every record answered
   `:durable` before the selection is reflected in the recovered
   projection (from 1 and the quiesce precondition).
4. `fn-bpn-recovered-owed-work-has-a-continuation` (T6) holds of a state
   recovered from a checkpoint: live entries, handoffs and plans continue.
5. `fn-bpn-rotation-frontiers-are-monotone`: every logical frontier after
   `:generation-selected` is at least its value before; none resets.
6. `fn-bpn-rotation-is-affordable`: for every state satisfying §2.1's
   budgets, the checkpoint's chunk count plus one, plus `D(s)` plus
   `control-reserve`, is at most `*fn-bpn-machine-max-records*`, so a new
   generation starts inside its own debt cover. A theorem over the policy
   constants and the chunk bound.

The publication facts it needs are the ones T6 needs (§6 of the review):
the FNBS publisher's relation to the byte-store model, including the cut
after an uncertainty callback. Rotation adds no storage primitive.

## 4. The transitions

Every transition is total, refuses malformed operands in the logic, does
bounded work, and either proposes exactly one record through
`fn-bpn-propose` or changes nothing durable. A proposal's success effects
are released only on `(:persist-result token :durable obs)`. **No transition
chains a second proposal after a durable result** (F-N): owed follow-on work
is found by the next progress action (§4.2), which the loop issues.

### 4.1 Reception: `fn-bpn-receive-step st octets ingress obs`

RFC 9171 §5.6, with fn's rule that nothing is stored before it decodes.

1. Decode bounded: `(fn-bpb-decode octets transfer-limit)`; an error is
   `(:receive-answer ingress (:refused (:decode why)))`.
2. `fn-bpp-flags-conformantp` on the primary, else `(:refused :flags)`.
3. Block disposition, `fn-bpn-block-disposition bundle`: every block is
   primary, payload, Previous Node (6), Bundle Age (7) or Hop Count (10), or
   an unsupported type. For an unsupported block, its processing-control
   flags decide (RFC 9171 §4.2.4): "delete bundle if not processed" refuses
   `(:refused :unsupported-block)`; "discard block if not processed" drops
   the block; otherwise it is kept as opaque immutable content. BPSec
   blocks (11, 12) are unsupported in the v0 profile and handled by the same
   rule. `fn-bpn-blocks-supportedp` is the resulting predicate; `fn-bpb-bundlep`
   is structural only and is not called semantic validity.
4. Identity and duplicate equivalence (F-E). `id = (fn-bpp-bundle-id
   primary (len payload))`. `fn-bpn-immutable-projection b` is the primary
   block, the payload block's data, and every block other than 6, 7 and 10
   with its type, number, flags and data. If a live entry has `id`: equal
   immutable projections (exact) is `:duplicate` (nothing stored; the held
   copy is kept, whatever its mutable blocks); different projections is
   `(:refused :identity-conflict)` and, within the historical budget, a kind
   14 record naming the ingress and the conflicting projection's content id
   (the held entry is never replaced). If no live entry has `id` but an
   outcome does (a bundle this node authored and discarded), the same two
   answers are decided by the outcome's `commitment` (§2.4, under the
   digest's collision assumption). A fragment whose ADU key names a live
   reassembled bundle, or a reassembly still in the correlation index, is
   `:duplicate` (§7.2).
5. Administrative record addressed here (`fn-bpp-administrativep` and
   `fn-bpn-local-destinationp`), reached only when steps 1 to 4 admitted
   it and found no entry or outcome with `id` (T5 names that predicate):
   §7.6's parser; a decodable report yields `(:transport submission
   status)` for the correlation entry it names (§2.4), labelled a remote
   observation, plus `(:receive-answer ingress :observed)`; a malformed or
   unsupported administrative ADU yields `:observed` alone (RFC 9713 §2).
   Nothing is stored and no deadline moves (§9.6).
6. Budgets (§2.1): live slots, live bytes, journal admission; failure is
   `(:refused :capacity)`.
7. Propose kind 5 with ingress `ingress`, no submission, anchor
   `(fn-bpn-anchor-of bundle obs)`, `:dispatch-pending`. Success effects:
   `(:receive-answer ingress :stored)` and, when requested and enabled,
   `(:report-due id :received :none)`. Refusal effect `(:receive-answer
   ingress (:refused :persistence))`; uncertainty effect `(:receive-answer
   ingress (:uncertain :persistence))`.

Lifetime is not asked at reception: an uncertain clock must not refuse a
bundle a later observation can decide. `(fn-bpn-transfer-admissiblep st n)`
is the pure START-time capacity query (§9.2); it is advisory and step 6 is
the decision.

### 4.2 The progress boundary: `fn-bpn-progress-step st obs` (`:clock`)

**Current A3 native subset.** The shared `bp-node` service does not yet run
this full progress scheduler for received held rows. Its application caller
uses `fn-bpah-pending-decision-at` before Store: a current observation must
decide the exact persisted held carrier `:live`; `:expired` is skipped and
`:uncertain` fences. New kind-5 rows persist the receive-time Bundle Age
anchor (or an explicit wall-clock tag); older canonical kind-5 rows have no
anchor and remain uncertain rather than acquiring an invented arrival time.
This narrows A3 delivery eligibility beyond the target's `not :expired`
condition until the full progress transition and reclamation records land.
Already committed application and return-carrier obligations are independent
of that held-carrier eligibility.
The host-called A3 selector `fn-bpah-pending-decision-at` gives an eligible
local `:live` carrier priority over an older carrier whose *clock* expiry is
`:uncertain`. If no local live carrier exists, it reports the oldest uncertain
carrier explicitly, so the owner refuses application dispatch pending clock
evidence. The older carrier remains held in either case. This per-carrier
clock decision does not relax the separate global fence after an ambiguous
FNBS or Store publication; `fnn-bpnode-dispatch-one` checks the service's
uncertain outcome before calling `:deliver`, and `fn-bpnf-step` refuses to
issue a delivery marker while an uncertain publication is issued. This A3
selection only covers local whole application requests/receipts; N03's route
wait, N04's session MRU, and N05's journal debt remain open in A1.

One action per event. This is the only place delivery and dispatch are
started, so expiry is decided before either (F-L). Selection is among
**enabled** candidates (review-2 §2.2): an older blocked entry never
occupies the branch a newer ready entry needs (N03, N04).

**Action classes and eligibility.** Four classes: `:expire`, `:dispatch`,
`:deliver`, `:discard`. An entry is a candidate of a class when the class's
precondition holds of it (below); it is **eligible** when it is a candidate
and it has no wait in `waits`, or its wait's condition now holds:

| Wait | Set when | Condition that ends it |
| --- | --- | --- |
| `(:route rg)` | dispatch found no route; a reroute returned it to dispatch | `route-generation > rg` |
| `(:mru peer mru)` | `start-one` found the image exceeds the session MRU and no plan (before slice C, or `:mru-infeasible`) | a session to `peer` opens with a different MRU, or `route-generation` changes |
| `(:after m)` | a delivery answered `:busy` or `:uncertain` | `(fn-clock-monotonic obs) ≥ m`, `m` = then + `owner-backoff` |
| `(:fragments key n)` | reassembly answered `(:missing lo hi)` with `n` active fragments | the active set for `key` changes size |
| `(:credit)` | a free-credit record (§2.1) could not be admitted | `remaining − D − control-reserve` has grown |

Waits are volatile: after restart every candidate is eligible once and is
re-tagged if still blocked. A wait never makes an entry ineligible for
`:expire` or `:discard`.

**Service.** The class served is the first class, starting at `cursor` and
cycling, that has an eligible candidate; `cursor` then advances past it.
Within the class the entry of **least arrival among eligible candidates**
is chosen. So every class with an eligible candidate is served within four
progress events (`fn-bpn-progress-serves-every-enabled-class-within-four`),
and FIFO holds among eligible candidates, not among all.

1. **`:expire`.** Candidates: not deleted, `(fn-bpn-held-expiry h obs)` is
   `:expired`. Propose kind 10 `:lifetime-expired`; success effects
   `(:transport submission :expired)` for a work submission and
   `(:report-due id :deleted :lifetime-expired)` when requested and enabled.
   `:uncertain` makes nothing a candidate.
2. **`:dispatch`.** Candidates: `:dispatch-pending`, no in-flight marker,
   `dispatch` nil. For the chosen entry, if its expiry under `obs` is
   `:expired` the action is class 1's instead. Otherwise:
   - local destination, administrative: kind 6 `:administrative`, whatever
     its ingress, including a report this node authored to itself (F-K 5);
     its success effects are §4.1 step 5's observation effects;
   - local destination, fragment: slice C (§7.2); before slice C the entry
     is held with `:reassembly-pending` via kind 6 `:await-fragments` and
     expires normally;
   - local destination, whole: kind 6 `:deliver`;
   - otherwise `(fn-bpn-next-hop routes destination)`: kind 6 `(:forward
     p)`; no route: nothing durable, `(:forward-refused id nil
     :no-known-route)`, and wait `(:route route-generation)`.
3. **`:deliver`.** Candidates: `dispatch` is `(t6 . :deliver)`, still
   `:dispatch-pending`, no `(:delivering ...)` marker. For the chosen
   entry, if its expiry under `obs` is `:expired`, class 1's action. If
   `(fn-bpn-adu-class payload)` is not `:request` or `:receipt`, propose
   kind 7 with outcome `(:refused :adu-class)` and emit no `:deliver`: the
   unsupported class has a durable disposition (review-2 T1). Otherwise set
   the volatile marker `(:delivering t6)` and emit `(:deliver id t6 class
   key payload ingress report-p)`. No record.
4. **`:discard`.** Candidates: not retained. Kind 11.
5. No eligible candidate in any class: nothing.

`fn-bpn-deliver-result-step st id delivery-token outcome obs`: a token that
does not match the entry's marker is stale and changes nothing.
`:accepted`, `:duplicate`, `(:refused r)` and the receipt-naming outcomes
of §3.1 propose kind 7 (a refusal is a completed delivery at this layer;
what the application decided is FNRJ's). `:busy` and `:uncertain` clear
the marker, propose nothing, leave `:dispatch-pending` and set wait
`(:after m)`, so class 3 redelivers after the backoff (BP-R17) and serves
other entries meanwhile.

### 4.3 Forwarding: `fn-bpn-session-step`, `fn-bpn-resume-step`, `fn-bpn-forward-result-step`

`fn-bpn-start-one st peer session obs`, called by a session open and by
`:resume`, selects the entry of **least arrival among eligible forward
candidates** for `(peer, session)`: `:forward-pending`, next hop `peer`, no
attempt, not deleted, not a family parent with an open plan, and no wait
whose condition fails (§4.2's table). An older entry whose image does not
fit carries `(:mru peer mru)` and is passed over; a newer one that fits is
served (N04). For the chosen entry:

1. if `(fn-bpn-held-expiry h obs)` is `:expired`: kind 10
   `:lifetime-expired` (the progress boundary applies here too);
2. if `fn-bpn-hop-exceededp`: kind 10 `:hop-limit-exceeded`;
3. if the **actual** forwarding image, computed now at `obs`, exceeds the
   session's negotiated MRU: slice C's family plan (§7.3), or, for a child
   of an open plan, the re-fragmentation path of §7.3; before slice C,
   `(:forward-refused id peer :mru)`, nothing durable, and wait `(:mru
   peer mru)`;
4. otherwise, subject to journal admission (kind 8 spends free credit and
   reserves its result, §2.1), kind 8 with the session, the age estimate,
   and success effect `(:cl-send cl peer session token id image)`, `image =
   (fn-bpn-forward-image st h obs)` (Previous Node replaced under policy,
   Bundle Age set, Hop Count incremented, re-encoded; the held record is
   unchanged).

`fn-bpn-forward-result-step st attempt-token session outcome obs`: the entry
whose attempt is `(:forwarding attempt-token peer session)`; if none, the
outcome is stale (BP-R15) and the answer is `(:forward-stale attempt-token
session)` with no record. Otherwise kind 9. Success effects on `:sent` or
`(:refused 1)`: `(:transport submission :forwarded)` for a work submission
and `(:report-due id :forwarded :none)` when requested and enabled; else
`(:transport submission :attempted)` and `(:forward-refused id peer
outcome)`.

Sessions: at most one outbound session per peer per incarnation; any number
of inbound sessions; an entry may be attempted on any open session to its
next hop. `(:session peer s nil mru obs)` removes only `(peer . s)`; an attempt
on `s` is left for its `:forward-result`, or `:uncertain` from the loop when
the session ended without one.

`(:resume peer session obs)` runs `fn-bpn-start-one` once. It is kept (§12,
D-11) as a bounded action the loop issues, never a recursive retry (§9.1).

### 4.4 Authoring: `fn-bpn-transmit-step`, `fn-bpn-report-step`

`fn-bpn-transmit-step st submission destination sequence adu obs`:

1. **Idempotence reuses the persisted result** (F-E). If an outcome for
   `submission` exists: when its `adu-id` is the content id of `adu` and
   its `destination` equals `destination`, answer
   `(:bundle-queue-accepted submission bundle-id sequence :duplicate)` from
   the outcome, with no record, no reauthoring and no comparison against a
   bundle rebuilt from this event's clock; otherwise
   `(:bundle-queue-refused submission :submission-conflict)`. The retry's
   `sequence` is burned. The outcome is authoritative for the window of
   §2.4, so this answer cannot silently become a second carrier.
2. Budgets, the history budget, and journal admission, else `-refused
   :capacity` (with `:history` when it is the history budget).
3. Propose kind 5 with ingress `(:local)`, the submission, bundle
   `(fn-bpn-send-bundle config destination adu sequence obs)`, wire
   `(fn-bpn-send ...)` (K1, K5 stay `bp-node`'s), anchor `(0 . monotonic)`,
   `:dispatch-pending`. Success effect `(:bundle-queue-accepted submission
   id sequence :durable)`.

`fn-bpn-report-step` is §7.6. The sequence in both is reserved and durable
before the event (PRF-045).

### 4.5 Persistence, routes, settlement, restart

- `fn-bpn-persist-result-step st token outcome obs`: `:durable` applies the
  pending record, clears `issued` and releases its success effects;
  `:refused` clears the proposal and `issued` and releases the refusal
  effect (the publisher answers `:refused` only when nothing was linked,
  a publisher obligation of A2); `:uncertain` clears `pending`, **keeps
  `issued`**, fences and releases the uncertainty effect. Nothing is
  chained.
- `fn-bpn-routes-step st table generation` installs the table (live). Then,
  one record per event: an entry with `:forward-pending`, no attempt, whose
  next hop has no route in `table` is rerouted, kind 13 with the new next
  hop, or nil to return it to `:dispatch-pending`. An entry with an attempt
  in flight is not rerouted until its result. `(:routes-installed n)`
  reports how many candidates remain; the loop re-issues until 0.
- `fn-bpn-work-settled-step st submission`: kind 12 when the outcome's
  bundle is not live; otherwise nothing (the outcome outlives the carrier,
  never the reverse). Receipt and report outcomes are retired by the
  progress step under §2.4's lifetime rule, from `control-reserve`.
- `fn-bpn-restart-step st records ready obs`: replay by
  `fn-bpn-apply-record` over `fn-bpn-record-applicablep`; a retired or
  unsupported kind or an inapplicable record is `:restart-fault` and fences;
  otherwise the state is `(fn-bpn-normalize replayed obs)` (T6):
  volatile fields at their restart values, every attempt and delivery
  marker cleared whether or not the entry has an anchor, every anchor
  re-established as `(age . (fn-clock-monotonic obs))` with `age` the
  largest age any durable record of the entry carries, or nil when none
  does. Sessions and routes are empty; the loop installs routes after
  `:restart-ready`, never before. A restart event is the first event of an
  epoch; T6's replay equation is stated over one epoch (§5, T6).

### 4.6 The codec boundary under the machine: guidance for the T1 lane

Root hands this subsection to the T1 lane (plan §4.1); it answers the
dialogue's §3.1 from review-2 §4. The machine's books sit above the CBOR,
record, frame and statement seams and depend on exactly what this says.

**Three families of checks, three different claims.**

1. *Abstract proof books* over the seam: protocol and state theorems (T1 to
   T6 here) derived from the seam's constraints only, true whichever
   attachment executes.
2. *Concrete codec conformance books*: exact wire vectors and grammar facts
   about the concrete functions (`fn-bpb-encode`, the record codec, §7.6's
   report grammar), proved of the definitions, not of the constrained
   functions.
3. *Attachment smoke tests*: `assert-event`s that run the public functions
   through the production attachment and compare their results with the
   concrete functions on the same vectors. An attached evaluation is not a
   theorem: the prover never replaces a constrained function by its
   attachment while simplifying (ACL2's `books/misc/defattach-example.lisp`
   draws exactly this line). The image evidence records the attachment
   configuration; reattaching is a behavioural change even when every
   abstract theorem still holds.

**Guard facts are exported.** A caller's guard proof must follow from the
seam's logical interface: the decoder's input guard does not prove its
output fits the next function. Each seam exports success-implies-record,
the projection type facts, consumed-length bounds, and every other fact a
downstream guard uses. A checked `defattach` needs a guard-verified
implementation whose guard the interface guard implies; no trust-tagged
skip is used to cover an interface that failed to state its contract.

**Round trip plus canonicality does not identify the wire language.** For
any length-preserving permutation `π` of the accepted encodings,
`E' = π ∘ E`, `D' = D ∘ π⁻¹` satisfies the same inverse laws, canonicality
and size bounds while using another kind byte, field order or
representation. So the concrete conformance facts of family 2 stay, and a
claim that depends on exact bytes (RFC conformance, compatibility of two
independently chosen attachments, a record name derived from bytes) cites
them or a named functional-instantiation route from the seam to the
concrete codec, never the abstract laws alone (N17).

**Streaming: primitives below, composition above.** The seam exports the
primitive step contracts composition needs: accepted result types,
consumed-prefix bounds, remaining-budget monotonicity, positive consumption
where a loop relies on it, exact residual-input behaviour. Bounded carry,
partition independence and aggregate work are theorems of a streaming
invariants book above the seam. An output-size bound is not a work bound
(a decoder that rescans its prefix has bounded output and quadratic work):
the executable path gets an explicit cost model and a refinement from the
logical parser, and the image is measured. No constraint assumes the
complexity result it should prove.

**Before T1 widens across the tree**, it certifies one representative
mini-closure containing: a guarded downstream consumer whose guard
proof uses only exported facts; a concrete vector theorem; an attached
`assert-event` comparing attached and concrete results; and a streaming
split-input test. This is one bounded compatibility experiment, not a gate
on every later book. For the machine, the consumer is the record decoder's
caller in `fn-bpn-restart-step` and the vector is one kind-5 record.

## 5. The theorems

Notation, fixed for every statement:

```text
EFFECTS  = (fn-bpn-answer-effects (fn-bpn-step st event))
NEXT     = (fn-bpn-answer-state (fn-bpn-step st event))
RECORDS  = (fn-bpn-persisted-records EFFECTS)     ; the record of every :persist effect, by selector
OBS      = (fn-bpn-event-obs event)               ; nil for an event without one
(HELD x) = (fn-bpn-find-held x (fn-bpn-machine-state-held st))
```

The subject is `fn-bpn-step`; the host calls `fn-bpn-step-fast`
(`fnn-bps-step`, `bp-service.lisp:113`, through the loop of §9.1), and
`fn-bpn-step-fast-is-step` (§2.7) is the equation. Machine theorems live in
`books/bp-node-machine-invariants.lisp` and `-authorization.lisp`; T6's
replay and recovery in `books/bp-node-replay.lisp` (new, slice A2); T4 in
`books/bp-fragment-invariants.lisp` and `books/bp-fragment-fast.lisp` (new,
slice C1); the loop's correlation keystones in `books/bp-service-loop.lisp`
(new, slice A1) and §5.7 in the same book (slice B); rotation in
`books/bp-node-rotation.lisp` (new, slice E); teeth in
`tests/acl2/bp-node-machine-teeth-tests.lisp` (new), whose first rows are
§11.1's.

### 5.0 The rule for teeth

1. Each **positive tooth** is a reachable trace from
   `fn-bpn-initial-machine-state` by `fn-bpn-trace`. It first asserts that
   the theorem's complete antecedent holds of the constructor-produced
   record or effect, e.g. `(member-equal (fn-bpn-rec-deleted 7 id
   :lifetime-expired) RECORDS)`, and only then the conclusion. An antecedent
   no reachable trace satisfies is a vacuous theorem and fails review.
2. One `must-fail` per hypothesis that can fail on a reachable state. It is
   an **exact logical check** (review-2 T2/T3): the witness asserts every
   retained hypothesis, the failure of the omitted one, and the negation of
   the conclusion, all of the same state and event. A witness that
   violates the antecedent some other way (a discard offered against a
   theorem about deletion records) is not a tooth. Dropping one hypothesis
   never licenses dropping another in the same witness.
3. A hypothesis that no reachable state can falsify (an invariant) is
   witnessed by a **corrupted-state** `must-fail`, in its own section of the
   test book and labelled so; it is never counted as a reachable witness.
4. A redundant hypothesis is removed only after ACL2 proves the theorem with
   that hypothesis omitted. Failure to find a rule-2 counterexample is not a
   proof of redundancy. Record the proved weaker theorem and the removed
   hypothesis in the evidence file.
5. A theorem over arbitrary events also has **boundary tests**: a
   malformed event, a `:persist-result` with a token that is not pending,
   a stale `:forward-result`, a `:deliver-result` whose token does not
   match the marker. Each changes nothing and emits nothing (or only its
   stale observation), and each is asserted.

The per-theorem witnesses and must-fails this revision introduces are
listed in §11.1, so the implementation lane's first commit is that suite.

### T1. Delivery names a validated, whole, non-administrative bundle this node holds, whose expiry the observation does not decide as expired, of a supported ADU class

```lisp
(defthm fn-bpn-deliver-effect-names-a-validated-whole-live-bundle
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal e EFFECTS)
                (equal (fn-bpn-effect-kind e) :deliver))
           (let* ((h (HELD (fn-bpn-deliver-id e)))
                  (b (fn-bpn-held-bundle h))
                  (p (fn-bpb-bundle-primary b)))
             (and h
                  (fn-bpb-bundlep b)
                  (equal (fn-bpn-held-wire h) (fn-bpb-encode b))
                  (fn-bpp-flags-conformantp p)
                  (fn-bpn-blocks-supportedp b)
                  (not (fn-bpp-fragmentp (fn-bpp-flags p)))
                  (not (fn-bpp-administrativep (fn-bpp-flags p)))
                  (fn-bpn-local-destinationp st h)
                  (member-eq :dispatch-pending (fn-bpn-held-constraints h))
                  (equal (cdr (fn-bpn-held-dispatch h)) :deliver)
                  (not (equal (fn-bpn-held-expiry h OBS) :expired))
                  (equal (fn-bpn-deliver-token e) (car (fn-bpn-held-dispatch h)))
                  (equal (fn-bpn-deliver-adu-class e) (fn-bpn-adu-class (fn-bpb-payload b)))
                  (member-eq (fn-bpn-deliver-adu-class e) '(:request :receipt))
                  (equal (fn-bpn-deliver-key e) (fn-bpp-adu-key p))
                  (equal (fn-bpn-deliver-payload e) (fn-bpb-payload b))
                  (equal (fn-bpn-deliver-ingress e) (fn-bpn-held-ingress h))))))

(defthm fn-bpn-unsupported-adu-class-is-refused-durably
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal r RECORDS)
                (equal (fn-bpn-rec-kind r) :delivered)
                (not (member-eq (fn-bpn-adu-class (fn-bpb-payload (fn-bpn-held-bundle (HELD (fn-bpn-rec-id r)))))
                                '(:request :receipt))))
           (and (equal (fn-bpn-rec-outcome r) '(:refused :adu-class))
                (not (fn-bpn-effect-kind-memberp :deliver EFFECTS)))))
```

**Scope of the lifetime conjunct.** It says the event's observation does
not decide the bundle expired: `(not (equal ... :expired))`, which admits
`:uncertain`. It is not `:live`, and it says nothing about the true
physical age. The registry sentence says "not decided expired under the
event's observation", never "unexpired". The administrative conjunct holds
whatever the ingress, so a report this node authored to itself is never
delivered (F-K 5). A whole local bundle of an unsupported ADU class is
never lost in a callback: the second theorem gives it a durable kind 7
`(:refused :adu-class)` with no `:deliver`. Teeth: §11.1.

### T2. A deliverable bundle is deleted only by expiry; fragments' deletions are enumerated; discard needs no constraint; the machine touches no obligation

```lisp
(defun fn-bpn-deliverablep (st h)
  (and h
       (fn-bpn-local-destinationp st h)
       (not (fn-bpp-fragmentp (fn-bpp-flags (fn-bpb-bundle-primary (fn-bpn-held-bundle h)))))
       (not (fn-bpp-administrativep (fn-bpp-flags (fn-bpb-bundle-primary (fn-bpn-held-bundle h)))))
       (member-eq :dispatch-pending (fn-bpn-held-constraints h))))

(defthm fn-bpn-deliverable-bundle-is-deleted-only-by-expiry
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal r RECORDS)
                (equal (fn-bpn-rec-kind r) :deleted)
                (fn-bpn-deliverablep st (HELD (fn-bpn-rec-id r))))
           (and (equal (fn-bpn-rec-reason r) :lifetime-expired)
                (equal (fn-bpn-held-expiry (HELD (fn-bpn-rec-id r)) OBS) :expired))))

(defthm fn-bpn-local-deletion-reasons
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal r RECORDS)
                (equal (fn-bpn-rec-kind r) :deleted)
                (fn-bpn-local-destinationp st (HELD (fn-bpn-rec-id r))))
           (member-eq (fn-bpn-rec-reason r) '(:lifetime-expired :block-unintelligible))))

(defthm fn-bpn-discard-is-proposed-only-for-an-unretained-entry
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal r RECORDS)
                (equal (fn-bpn-rec-kind r) :discarded))
           (and (HELD (fn-bpn-rec-id r))
                (not (fn-bpn-retainedp (HELD (fn-bpn-rec-id r)))))))

(defthm fn-bpn-step-emits-no-release-and-no-receipt-prepare
  (and (not (fn-bpn-effect-kind-memberp :release EFFECTS))
       (not (fn-bpn-effect-kind-memberp :receipt-prepare EFFECTS))))
```

A fragment consumed by reassembly is retired by kind 18, not deleted
(§7.2), so the local-deletion list is complete. `:block-unintelligible` is
the conflict disposition of §7.2 and is reachable only from slice C.
Hypotheses removed as redundant (rule 4): the first revision's
`fn-bpp-fragmentp` in the local-deletion theorem (a local whole bundle is
deleted only by expiry, which is in the list, and an unsupported ADU class
is a kind 7, not a deletion) and `(HELD id)` (implied by
`fn-bpn-local-destinationp`, which is nil of nil). The first revision's
tooth "a delivered entry is discarded, not deleted" is withdrawn: it does
not satisfy the antecedent of a theorem about deletion records. Teeth:
§11.1.

### T3. Expiry is the clock book's decision on the event's observation

```lisp
(defthm fn-bpn-expiry-deletion-is-decided-by-the-events-observation
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal r RECORDS)
                (equal (fn-bpn-rec-kind r) :deleted)
                (equal (fn-bpn-rec-reason r) :lifetime-expired))
           (and (fn-clock-observationp OBS)
                (equal (fn-bpn-held-expiry (HELD (fn-bpn-rec-id r)) OBS) :expired))))

(defthm fn-bpn-uncertain-clock-deletes-nothing-by-expiry
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (not (fn-clock-has-wall OBS))
                (fn-bpn-no-anchors-p (fn-bpn-machine-state-held st))
                (member-equal r RECORDS)
                (equal (fn-bpn-rec-kind r) :deleted))
           (not (equal (fn-bpn-rec-reason r) :lifetime-expired))))
```

The event tag is not constrained (F-L): expiry may be decided by `:clock`,
`:resume`, a session open or a persist result, and the theorem constrains
the evidence. `fn-clock-expiry-is-monotone-in-local-time`
(`clock-invariants.lisp:145`) carries over. The two cases the first
revision listed as positives of the first theorem are, restated exactly,
the must-fails of the second: an anchored entry with a wall-less
observation past its lifetime is deleted `:lifetime-expired` (asserting
no-wall, kind, and every hypothesis but `fn-bpn-no-anchors-p`), and an
unanchored entry with a confident wall past its lifetime is deleted
`:lifetime-expired` (asserting no-anchors, kind, and every hypothesis but
the wall's absence). Teeth: §11.1.

### T4. Fragmentation and reassembly: inverse, fast equals reference, whole-parent restoration, re-fragmentation, coherent replacement

```lisp
(defthm fn-bpf-fragment-then-reassemble-is-identity
  (implies (equal (car (fn-bpf-fragment payload boundaries)) :ok)
           (equal (fn-bpf-reassemble (cadr (fn-bpf-fragment payload boundaries)) (len payload))
                  (list :ok payload))))

;; over ALL inputs, including (:invalid :bounds) (question 4 in §12)
(defthm fn-bpf-reassemble-fast-is-reassemble
  (equal (fn-bpf-reassemble-fast fs total) (fn-bpf-reassemble fs total)))

(defthm fn-bpf-fragment-fast-is-fragment
  (equal (fn-bpf-fragment-fast payload boundaries) (fn-bpf-fragment payload boundaries)))

;; whole-parent fragmentation: the only case in which unfragmenting restores the parent
(defthm fn-bpn-whole-parent-fragments-share-the-key-and-unfragment-to-the-parent
  (implies (and (fn-bpp-blockp p)
                (not (fn-bpp-fragmentp (fn-bpp-flags p)))          ; whole parent
                (fn-bpf-fragmentablep p)
                (equal (car (fn-bpf-fragment payload boundaries)) :ok) ; a successful plan
                (equal total (len payload)))                        ; nonempty and bounded by the plan
           (let ((cs (fn-bpn-fragment-primaries p boundaries total)))
             (and (fn-bpn-all-equal (fn-bpp-adu-key p) (fn-bpn-map-adu-key cs))
                  (fn-bpn-all-total total cs)
                  (equal (fn-bpn-map-fragment-offset cs) (fn-bpf-starts boundaries))
                  (fn-bpn-all-unfragment-to p cs)))))

;; re-fragmentation: a fragment parent keeps its ADU key and total; offsets compose
(defthm fn-bpn-refragmentation-composes-offsets
  (implies (and (fn-bpp-blockp p)
                (fn-bpp-fragmentp (fn-bpp-flags p))                 ; a fragment parent
                (fn-bpf-fragmentablep p)
                (equal (car (fn-bpf-fragment payload boundaries)) :ok)
                (<= (+ (fn-bpp-fragment-offset p) (len payload)) (fn-bpp-total-adu-length p)))
           (let ((cs (fn-bpn-refragment-primaries p boundaries (len payload))))
             (and (fn-bpn-all-equal (fn-bpp-adu-key p) (fn-bpn-map-adu-key cs))
                  (fn-bpn-all-total (fn-bpp-total-adu-length p) cs)
                  (equal (fn-bpn-map-fragment-offset cs)
                         (fn-bpn-shift-offsets (fn-bpp-fragment-offset p) (fn-bpf-starts boundaries)))))))

;; the offset-zero input and header coherence, not first arrival
(defthm fn-bpn-reassembled-record-is-a-complete-coherent-reassembly
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal r RECORDS)
                (equal (fn-bpn-rec-kind r) :reassembled))
           (let* ((ids (fn-bpn-rec-fragment-ids r))
                  (h (fn-bpn-rec-held r))
                  (zero (fn-bpn-offset-zero-fragment st ids))
                  (res (fn-bpf-reassemble (fn-bpn-fragments-of-ids st ids)
                                          (fn-bpp-total-adu-length
                                           (fn-bpb-bundle-primary (fn-bpn-held-bundle zero))))))
             (and zero
                  (equal (fn-bpp-fragment-offset (fn-bpb-bundle-primary (fn-bpn-held-bundle zero))) 0)
                  (fn-bpn-family-headers-coherentp st ids)
                  (equal (fn-bpf-result-tag res) :ok)
                  (equal (fn-bpn-active-set st (fn-bpn-rec-family r)) ids)
                  (equal (fn-bpb-payload (fn-bpn-held-bundle h)) (fn-bpf-result-bytes res))
                  (equal (fn-bpb-bundle-primary (fn-bpn-held-bundle h))
                         (fn-bpn-unfragment (fn-bpb-bundle-primary (fn-bpn-held-bundle zero))))
                  (equal (fn-bpn-extension-blocks (fn-bpn-held-bundle h))
                         (fn-bpn-extension-blocks (fn-bpn-held-bundle zero)))
                  (equal (fn-bpn-held-ingress h)
                         (fn-bpn-family-ingress (fn-bpn-map-held-ingress st ids)))))))

(defthm fn-bpn-reassembly-replaces-its-family
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-record-applicablep st r)
                (equal (fn-bpn-rec-kind r) :reassembled))
           (let ((after (fn-bpn-machine-state-held (fn-bpn-apply-record st r))))
             (and (equal (len after)
                         (+ 1 (- (len (fn-bpn-machine-state-held st))
                                 (len (fn-bpn-rec-fragment-ids r)))))
                  (fn-bpn-none-held-p (fn-bpn-rec-fragment-ids r) after)))))
```

The first needs `fn-bpf-cut-covers` and
`fn-bpf-reassemble-ok-agrees-with-every-fragment`, commented out in
`bp-fragment-invariants.lisp` (`:427`, `:248`).

Definitions the statements rest on: `fn-bpf-starts boundaries` is the
list of child start offsets relative to the payload (`0` then each
boundary); `fn-bpn-refragment-primaries p bs n` builds each child with
offset `(+ (fn-bpp-fragment-offset p) start)` and total
`(fn-bpp-total-adu-length p)`, which `fn-bpf-fragment-block`
(`bp-fragment.lisp:369-383`) does not do when handed relative offsets (D20);
`fn-bpn-offset-zero-fragment st ids` is the entry of `ids` whose fragment
offset is 0, or nil; `fn-bpn-family-headers-coherentp st ids` says every
fragment of `ids` has the same ADU key, total ADU length, destination,
report-to, lifetime, CRC type and flags other than the fragment flag.
Arrival order orders active fragments for selection only; it never picks
the header (N10). The whole-parent hypothesis is what the first revision
lacked: `fn-bpf-fragmentablep` (`bp-fragment.lisp:390`) tests only the
must-not-fragment flag, so the old statement admitted a fragment parent
and claimed to restore it (D19, N09). The fast reassembler's equality is
unconditional: it answers `(:invalid :bounds)` exactly where the reference
does, so no caller's validation is load-bearing. Teeth: §11.1.

### T5. A status report is only a transport observation, on either ingress

```lisp
;; the administrative BRANCH: steps 1 to 4 of §4.1 admitted it and found no entry or outcome with its id
(defthm fn-bpn-received-local-administrative-bundle-yields-only-observations
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp (list :bundle-received octets ingress obs))
                (fn-bpn-reaches-administrative-branch-p st octets))
           (let ((ans (fn-bpn-step st (list :bundle-received octets ingress obs))))
             (and (fn-bpn-only-transport-and-observed-effects (fn-bpn-answer-effects ans))
                  (not (fn-bpn-effect-kind-memberp :deliver (fn-bpn-answer-effects ans)))
                  (not (fn-bpn-effect-kind-memberp :persist (fn-bpn-answer-effects ans)))
                  (equal (fn-bpn-answer-state ans) st)))))

;; every decodable local administrative INPUT, including refusals and conflicts:
;; the semantic prohibition, with the effect class widened to what reception actually does
(defthm fn-bpn-received-local-administrative-bundle-is-never-application-authority
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp (list :bundle-received octets ingress obs))
                (fn-bpn-decodes-to-local-administrative-p st octets))
           (let ((effects (fn-bpn-answer-effects
                           (fn-bpn-step st (list :bundle-received octets ingress obs)))))
             (and (fn-bpn-effects-within-p effects '(:receive-answer :transport :persist))
                  (fn-bpn-persisted-kinds-within-p effects '(:conflict))
                  (not (fn-bpn-effect-kind-memberp :deliver effects))
                  (not (fn-bpn-effect-kind-memberp :bundle-queue-accepted effects))))))

(defthm fn-bpn-local-administrative-entry-is-dispatched-administratively
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal r RECORDS)
                (equal (fn-bpn-rec-kind r) :dispatched)
                (fn-bpn-local-destinationp st (HELD (fn-bpn-rec-id r)))
                (fn-bpp-administrativep (fn-bpp-flags (fn-bpb-bundle-primary
                                                       (fn-bpn-held-bundle (HELD (fn-bpn-rec-id r)))))))
           (equal (fn-bpn-rec-disposition r) :administrative)))

(defthm fn-bpn-transport-observation-cannot-close-a-work
  (implies (and (fn-bp-statep wf)
                (fn-bp-work-outstandingp (fn-bp-find-work work-id (fn-bp-state-works wf))))
           (fn-bp-work-outstandingp
            (fn-bp-find-work work-id
                             (fn-bp-state-works
                              (fn-bp-result-state
                               (fn-bp-step wf (fn-bp-transport-event other-work attempt-id
                                                                     generation status))))))))
```

;; review-2 §2.3: a transport observation never moves a receipt deadline (A3, bp-workflow).
;; No outstanding hypothesis: overdue already requires it, and a transport event never
;; reopens a closed work, so it would be redundant (rule 4).
(defthm fn-bp-transport-observation-preserves-receipt-overdue
  (implies (fn-bp-statep wf)
           (equal (fn-bp-receipt-overduep
                   (fn-bp-find-work work-id
                                    (fn-bp-state-works
                                     (fn-bp-result-state
                                      (fn-bp-step wf (fn-bp-transport-event other-work attempt-id
                                                                            generation status)))))
                   obs policy)
                  (fn-bp-receipt-overduep (fn-bp-find-work work-id (fn-bp-state-works wf))
                                          obs policy))))
```

`fn-bpn-reaches-administrative-branch-p st octets` is defined, not
assumed: the bounded decode succeeds, the flags conform, no block demands
deletion when unprocessed, the bundle is administrative and addressed
here, and no live entry or outcome has its identity (so neither the
duplicate nor the conflict branch of §4.1 step 4 runs). The first theorem
is about that branch; the second is about every decodable local
administrative input and widens the effect class to the refusals and the
kind-14 conflict record reception can actually produce (N11), keeping the
prohibition that matters: no delivery, no queue acceptance, no receipt
authority, and (T2's last theorem) no release.

`fn-bp-find-work` is `(work-id xs)` (`bp-workflow.lisp:177`) and
`fn-bp-state-works` (`:311`) is the projection. The third is quantified over
any `other-work`, so no transport event closes any work; it is stated in
the teeth book, which may include `bp-workflow-transport-invariants`, and
follows from `fn-bp-observe-transport-never-moves-status-backward`. It
does not say observations preserve retry deadlines; the fourth does, and
it holds because §9.6 defines overdue without reading the transport
status (N02). Teeth: §11.1.

### T6. Preservation, authorization, raw replay, recovery, re-anchoring, owed work

```lisp
(defthm fn-bpn-step-preserves-lifecycle-invariant
  (implies (and (fn-bpn-lifecycle-invariantp st) (fn-bpn-machine-eventp event))
           (fn-bpn-lifecycle-invariantp NEXT)))

(defthm fn-bpn-trace-preserves-lifecycle-invariant
  (implies (and (fn-bpn-lifecycle-invariantp st) (fn-bpn-machine-event-listp events))
           (fn-bpn-lifecycle-invariantp (fn-bpn-trace st events))))

(defthm fn-bpn-step-cl-send-is-authorized-by-durable-attempt-record
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal e EFFECTS)
                (equal (fn-bpn-effect-kind e) :cl-send))
           (let* ((pending (fn-bpn-machine-state-pending st))
                  (r (fn-bpn-pending-record pending)))
             (and pending
                  (equal (fn-bpn-event-kind event) :persist-result)
                  (equal (fn-bpn-persist-result-token event) (fn-bpn-pending-token pending))
                  (equal (fn-bpn-persist-result-outcome event) :durable)
                  (equal (fn-bpn-rec-kind r) :attempting)
                  (equal (fn-bpn-cl-send-attempt-token e) (fn-bpn-rec-token r))
                  (equal (fn-bpn-cl-send-session e) (fn-bpn-rec-session r))
                  (equal (fn-bpn-cl-send-id e) (fn-bpn-rec-id r))
                  (fn-bpn-record-applicablep st r)
                  (equal EFFECTS (fn-bpn-pending-success-effects pending))
                  (fn-bpn-proposal-effectsp st r
                                            (fn-bpn-pending-success-effects pending)
                                            (fn-bpn-pending-refusal-effect pending)
                                            (fn-bpn-pending-uncertainty-effect pending))))))

(defthm fn-bpn-transmit-acceptance-is-durable-or-the-persisted-result
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal e EFFECTS)
                (equal (fn-bpn-effect-kind e) :bundle-queue-accepted))
           (or (let ((c (fn-bpn-find-outcome (fn-bpn-transmit-submission event)
                                             (fn-bpn-machine-state-outcomes st))))
                 (and (equal (fn-bpn-event-kind event) :transmit)
                      (equal (fn-bpn-queue-answer-mode e) :duplicate)
                      c
                      (equal (fn-bpn-queue-answer-submission e) (fn-bpn-transmit-submission event))
                      (equal (fn-bpn-outcome-destination c) (fn-bpn-transmit-destination event))
                      (equal (fn-bpn-outcome-adu-id c) (fn-bpn-content-id (fn-bpn-transmit-adu event)))
                      (equal (fn-bpn-queue-answer-bundle-id e) (fn-bpn-outcome-bundle-id c))
                      (equal (fn-bpn-queue-answer-sequence e) (fn-bpn-outcome-sequence c))
                      (equal NEXT st)))
               (let* ((pending (fn-bpn-machine-state-pending st))
                      (r (fn-bpn-pending-record pending))
                      (h (fn-bpn-rec-held r))
                      (b (fn-bpn-held-bundle h)))
                 (and (equal (fn-bpn-queue-answer-mode e) :durable)
                      pending
                      (equal (fn-bpn-event-kind event) :persist-result)
                      (equal (fn-bpn-persist-result-token event) (fn-bpn-pending-token pending))
                      (equal (fn-bpn-persist-result-outcome event) :durable)
                      (equal (fn-bpn-rec-kind r) :stored)
                      (equal (fn-bpn-rec-token r) (fn-bpn-pending-token pending))
                      (equal (fn-bpn-held-submission h) (fn-bpn-queue-answer-submission e))
                      (equal (fn-bpp-destination (fn-bpb-bundle-primary b))
                             (fn-bpn-pending-transmit-destination pending))
                      (equal (fn-bpn-content-id (fn-bpb-payload b))
                             (fn-bpn-pending-transmit-adu-id pending))
                      (equal (fn-bpn-queue-answer-bundle-id e) (fn-bpn-held-id h))
                      (equal (fn-bpn-queue-answer-sequence e)
                             (fn-bpp-sequence (fn-bpb-bundle-primary b)))
                      (fn-bpn-record-applicablep st r))))))

;; slice A2, books/bp-node-replay.lisp: ONE RUNNING EPOCH. Restart is not in `events`;
;; recovery (the next theorem) is the bridge between epochs.
(defthm fn-bpn-durable-projection-is-replay-of-the-confirmed-journal
  (implies (and (fn-bpn-epoch-basep base)
                (fn-bpn-epoch-event-listp events))
           (equal (fn-bpn-durable-projection (fn-bpn-trace base events))
                  (fn-bpn-durable-projection
                   (fn-bpn-replay-state base (fn-bpn-confirmed-journal base events))))))

(defthm fn-bpn-recovery-is-normalized-replay-of-an-observed-journal
  (implies (and (fn-bpn-epoch-basep base)
                (fn-bpn-epoch-event-listp events)
                (fn-bpn-observed-journal-p journal base events)
                (fn-bpn-sequence-readyp ready)
                (fn-clock-observationp obs))
           (let* ((ans (fn-bpn-step (fn-bpn-recovering-state base)
                                    (fn-bpn-restart-event journal ready obs)))
                  (rec (fn-bpn-answer-state ans)))
             (and (equal (fn-bpn-effect-kind (car (fn-bpn-answer-effects ans))) :restart-ready)
                  (equal (fn-bpn-normalize rec obs)
                         (fn-bpn-normalize (fn-bpn-cut-state (fn-bpn-trace base events) journal)
                                           obs))
                  ;; fixed point: the recovered state IS normalized, so the equation above
                  ;; cannot erase an anchor or in-flight marker recovery forgot to clear
                  (equal (fn-bpn-normalize rec obs) rec)))))

;; A2: the physical premise of the observed-journal relation
(defthm fn-bpn-physical-cut-is-an-observed-journal
  (implies (and (fn-bpn-epoch-basep base)
                (fn-bpn-epoch-event-listp events)
                (fn-bpn-publisher-relation dir base events)     ; FNBS publisher over the byte-store model
                (fn-bs-byte-crash-image-p dir crashed))
           (fn-bpn-observed-journal-p (fn-bpn-journal-of-directory crashed) base events)))

(defthm fn-bpn-restart-reanchors-every-held-bundle
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (equal (fn-bpn-effect-kind
                        (car (fn-bpn-answer-effects (fn-bpn-step st (fn-bpn-restart-event records ready obs)))))
                       :restart-ready)
                (member-equal h (fn-bpn-machine-state-held
                                 (fn-bpn-answer-state (fn-bpn-step st (fn-bpn-restart-event records ready obs))))))
           (and (null (fn-bpn-held-attempt h))                  ; anchored or not (N08)
                (if (fn-bpn-durable-age-of records (fn-bpn-held-id h))
                    (and (equal (fn-clock-anchor-monotonic (fn-bpn-held-anchor h)) (fn-clock-monotonic obs))
                         (equal (fn-clock-anchor-age (fn-bpn-held-anchor h))
                                (fn-bpn-durable-age-of records (fn-bpn-held-id h))))
                  (null (fn-bpn-held-anchor h))))))

(defthm fn-bpn-recovered-owed-work-has-a-continuation
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (null (fn-bpn-machine-state-pending st))
                (not (fn-bpn-machine-state-fenced st))
                (fn-bpn-owedp k st))
           (or (fn-bpn-enabled-action-p k st)
               (fn-bpn-blocked-with-wakeup-p k st))))
```

Definitions the statements rest on, each a function, not a hypothesis
predicate standing in for one:

- `fn-bpn-epoch-basep base`: lifecycle invariant, `pending`, `issued`,
  every attempt and delivery marker nil, not fenced: the state a
  successful restart produces (the fixed point says so). A recovered
  state is an epoch base; the initial state is one.
- `fn-bpn-epoch-event-listp events`: machine events none of which is
  `:restart`. A type recognizer does not stand in for the execution
  protocol: restart clears attempts and reanchors without adding a
  confirmed record, so it is outside the equation and inside recovery.
- `fn-bpn-confirmed-journal base events`: the records whose
  `(:persist-result token :durable obs)` the trace delivered, in token
  order, computed from the trace.
- `fn-bpn-observed-journal-p journal base events`: `journal` is the
  confirmed journal, or the confirmed journal followed by the record of
  `issued` at the end of the trace. It depends on issued operations and
  the physical cut, not on a surviving pending slot: after an uncertainty
  callback `pending` is nil and `issued` still names the record, which is
  N06's cut (file visible, callback run, then death).
- `fn-bpn-publisher-relation dir base events`: the FNBS publisher's
  relation between the trace and the byte-store directory (write, file
  barrier, link, directory barrier), preserved by its actual operation
  sequence including the cut after an uncertainty callback. The byte
  facts come from `fn-bs-store-recovery-is-a-kernel-crash` and
  `fn-bs-acknowledged-record-survives-byte-crash`
  (`byte-store-keystones.lisp:30-119`) under their stated assumptions; K0's
  general preservation gap is why A2 proves the relation for this
  publisher instead of assuming an atomic directory. A torn or malformed
  authoritative record outside the relation fences recovery; it is never
  an absent transaction.
- `fn-bpn-cut-state live journal`: `live` with its issued record applied
  when `journal` contains it, and its proposal cleared.
- A transmit's pending proposal carries the event's destination and the
  content id of its ADU (`fn-bpn-pending-transmit-destination`,
  `fn-bpn-pending-transmit-adu-id`), so the queue-acceptance theorem binds
  the durable answer to the submission, destination, ADU identity and
  persistence token of the request that asked for it, not merely to the
  presence of some outcome.
- `fn-bpn-normalize st obs` = `(fn-bpn-reanchor (fn-bpn-clear-inflight
  (fn-bpn-durable-projection st)) obs)`, a machine state (§2.6).
- `fn-bpn-owedp k st` over a **stable obligation key** `k`, looked up in
  each state, never a held record carried from an earlier state: `(:bundle
  id)` (an entry with that id is live and retained), `(:handoff rid
  trigger)` (that handoff is `:owed`), `(:family f)` (that plan is open).
  `fn-bpn-enabled-action-p k st`: the progress step or `start-one` on some
  open session would propose a record or emit a `:deliver` for it.
  `fn-bpn-blocked-with-wakeup-p k st`: its entry carries one of §4.2's
  waits, or it waits for a session to its next hop, or for a clock
  observation that decides expiry. Review §5.3: a journal can replay
  perfectly and still strand work; this theorem is the one that says it
  does not.

Hypothesis note: `fn-bpn-machine-eventp` on the restart event is redundant
with `fn-bpn-restart-event`'s recognizer and is absent (rule 4). Teeth:
§11.1, and the first revision's: a journal with a token gap is
`(:restart-fault :lifecycle-record)`; a journal holding kind 3 is
`(:restart-fault (:unsupported-schema 3 ...))`; a trace ending immediately
after a durable kind 8 recovers with the attempt cleared on **both** sides
(F-K 4); a route removed between the trace and the restart does not fault
the recovery (BP-R14); an `:attempting` age larger than the stored age
re-anchors to the larger; the four `must-fail`s of
`bp-node-machine-authorization-tests.lisp` carried over by constructor.

### 5.7 Conditional progress (review §5.5)

Safety is T1 to T6, and it holds for **every** environment: the first
theorem of `books/bp-service-loop.lisp`,
`fn-bps-run-preserves-the-loop-and-lifecycle-invariants`, has no
environmental hypothesis, so nothing below weakens safety when a progress
premise fails.

Progress is a set of separate lemmas, one per way an obligation can wait,
each with only the premises it needs (review-2 §5.7). Assumptions are
constrained functions in `books/assumptions.lisp`; each relates the same
trace, operation ids, obligation key and service index the conclusion
uses, so the encapsulate constrains the environment `fn-bps-run` consumes,
not a free boolean. Obligations are named by the stable keys of T6's
`fn-bpn-owedp`. Bounds are in loop turns; §8.1 relates turns to elapsed
time and contact capacity for the deployable profile.

```lisp
;; 1. route-waiting: no environmental premise but the route itself
(defthm fn-bps-route-waiting-entry-is-dispatched-after-a-route-appears
  (implies (and (fn-bps-loop-invariantp loop)
                (fn-bps-waits-on-route-p (list :bundle id) loop)
                (fn-bps-env-installs-route-for env (fn-bps-destination-of id loop) i)
                (fn-assume-bp-persistence-answers env)                          ; A-BP-PERSIST
                (fn-assume-bp-journal-headroom loop n)                          ; A-BP-JOURNAL
                (<= (+ i (fn-bps-class-bound loop)) n))
           (not (fn-bps-waits-on-route-p (list :bundle id) (fn-bps-run loop env n)))))

;; 2. forwardable: contact and peer service over the ELIGIBLE queue prefix
(defthm fn-bps-forwardable-entry-leaves-forward-pending
  (implies (and (fn-bps-loop-invariantp loop)
                (fn-bps-forward-eligible-p (list :bundle id) loop)
                (fn-assume-bp-contact-recurs env (fn-bps-next-hop-of id loop) window) ; A-BP-CONTACT
                (fn-assume-bp-peer-serves-eligible-prefix env (fn-bps-next-hop-of id loop)
                                                          (list :bundle id) window)      ; A-BP-PEER
                (fn-assume-bp-persistence-answers env)
                (fn-assume-bp-journal-headroom loop n)
                (<= (fn-bps-forward-bound (list :bundle id) loop window) n))
           (not (fn-bps-forward-pending-p (list :bundle id) (fn-bps-run loop env n)))))

;; 3. locally deliverable: a DEFINITIVE owner response
(defthm fn-bps-deliverable-entry-is-delivered
  (implies (and (fn-bps-loop-invariantp loop)
                (fn-bps-locally-deliverable-p (list :bundle id) loop)
                (fn-assume-bp-owner-answers-definitively env window)            ; A-BP-OWNER
                (fn-assume-bp-persistence-answers env)
                (fn-assume-bp-journal-headroom loop n)
                (<= (fn-bps-deliver-bound (list :bundle id) loop window) n))
           (not (fn-bps-dispatch-pending-p (list :bundle id) (fn-bps-run loop env n)))))

;; 4. incomplete family: completes if its cover arrives, else expires once time is decidable
(defthm fn-bps-incomplete-family-reassembles-or-expires
  (implies (and (fn-bps-loop-invariantp loop)
                (fn-bps-reassembly-pending-p (list :bundle id) loop)
                (or (fn-bps-env-completes-cover env id i)
                    (fn-assume-bp-clock-decides env window))                    ; A-BP-CLOCK
                (fn-assume-bp-persistence-answers env)
                (fn-assume-bp-journal-headroom loop n)
                (<= (fn-bps-family-bound (list :bundle id) loop i window) n))
           (not (fn-bps-reassembly-pending-p (list :bundle id) (fn-bps-run loop env n)))))

;; 5. requester retry: purely local
(defthm fn-bps-overdue-work-is-retried
  (implies (and (fn-bps-loop-invariantp loop)
                (fn-bps-work-overdue-p work-id loop obs)
                (fn-assume-bp-persistence-answers env)
                (fn-assume-bp-journal-headroom loop n)
                (<= (fn-bps-retry-bound loop) n))
           (fn-bps-work-has-new-attempt-p work-id loop (fn-bps-run loop env n))))
```

The assumptions, one sentence each:

- **A-BP-CONTACT**: in every `window` turns a session to the next hop is
  open with a usable byte budget at least the image of the eligible
  prefix up to this entry (§8.1's vocabulary), not merely briefly open.
- **A-BP-PERSIST**: every publication is answered `:durable` within the turn
  it is issued (a refusal or uncertainty ends the premise; it does not fail
  the theorem).
- **A-BP-PEER**: on each such session the peer completes, in arrival order,
  every offered carrier of the **eligible queue prefix** up to this entry
  with `:sent` or a definitive refusal, not merely some attempt.
- **A-BP-OWNER**: in every `window` turns the application join answers a
  delivery with a **definitive** response (`:accepted`, `:duplicate`,
  `:returned`, `(:refused r)`); `:uncertain` repeated indefinitely violates
  it, and N18 checks that the monitor reports that (question 7 in §12).
- **A-BP-CLOCK**: within `window` turns after a bundle's lifetime has
  elapsed, some observation decides its expiry.
- **A-BP-JOURNAL**: `remaining − D − control-reserve` covers the free-credit
  records of `n` turns.
- **A-BP-RETURN** (work level): a feasible timed return route and eligible
  receipt progress under the same premises in the reverse direction; a
  route entry alone is not a return contact.

Bounds: each class is served at least once in every four progress events
(§4.2) and the loop gives each action class a share of every turn (§9.1),
so a bound is the entry's rank among eligible candidates of its class
times the class period times `window`; a rank among one next hop's
carriers never stands for time spent in another class. The work-level
theorem (a work reaches a receipt or its retry fires, §9.6) composes 2 to
5 with A-BP-RETURN. **No assumption mentions reports**, and none is
satisfied by a report's content. Excluded, and not made progress
guarantees by any selector: arbitrary outages, indefinitely uncertain
time, an exhausted journal, an adversarial peer.
`fn-assume-fairness-contact-index` (`assumptions.lisp:291`) is the
scheduler's existing assumption; A-BP-CONTACT is stated so that the
scheduler's contact plan implies it.

## 6. K6: the delivered request's admission is the transit decision

K6 ([peering §1.4](peering.md)): a BP peer is the same profile over another
convergence layer. What the machine hands the application is `(:deliver id
t class key payload ingress report-p)`. The loop routes it by `class`
(§9.3): `:request` to the receiver join, `:receipt` to the sender's
release join. For a request, the join's admission changes in one place:

```lisp
(defun fn-bpaj-ingress-peer (cfg ingress) ...)
  ;; the peer NAME (the key fn-cfg-peer-find takes, peer-inbound.lisp:257)
  ;; admitted as ingress's principal and still configured at the current
  ;; configuration, or nil: nil for (:local), for a nil principal, for a
  ;; family whose fragments disagree, and for a principal no longer configured.
  ;; It returns an identifier, never a peer record; fn-peer-decide-transfer
  ;; looks the record up itself.
(defun fn-bpaj-admission (node cfg joined store request-octets ingress clock generation)
  ;; (:submit args) | (:bind record) | (:refused reason) | (:busy) | (:persist-intent) | ...
  ...)
```

Contract, by case:

- `fn-bpaj-ingress-peer` nil: `(:refused :no-principal)`. This covers
  self-delivery of a request (ingress `(:local)`) and an unauthenticated
  session; neither is a transit peer.
- `fn-peer-decide-transfer node cfg peer msgid article clock id subject`
  (`peer-inbound.lisp:254`) `:want`: `(:submit (fn-peer-injection-arguments
  node cfg peer msgid article generation id subject))`, the shared transit
  submission path.
- `:have`: `:have` means history holds the Message-ID; it does not
  authorize a receipt. The join still requires the exact binding it
  requires today: `fn-bpaj-record-lookup store request`
  (`bp-native-app.lisp:357`) finds a unique accepted record with matching
  payload and content subject, the owner generation is current and the
  planned transaction identity agrees; then `(:bind record)`; else
  `:stale-owner-generation`, `:missing-duplicate-record`,
  `:store-binding-conflict` or `:store-conflict` as today (`:381-401`).
- `:refuse`: `(:refused reason)`. `:defer`, or the join's `:blocked`:
  `(:busy)`, which reaches the machine as `:busy` (§4.2).

The finite A3 `:request-intent`/`:request-context-v2` join binds the Store
record to the request's raw article octets. That is correct for the historical
control-submission path but is not the general transit rule above:
`fn-peer-injection-arguments` stores `fn-peer-relayed-octets`, which may update
Path and remove Xref. The transit form therefore needs a new, versioned
intent **before** the Store attempt. `:request-transit-intent` (FNRJ code 7)
pins the immutable raw request ADU, admitted peer name, owner configuration
generation, local and expected peer Path identities, and ACL2-computed stored
projection. Replay checks that the projection is exactly
`fn-pu-relay-article` of the raw article under those pinned identities;
an arbitrary journal blob cannot choose Store bytes. `:request-transit-context`
(code 8) binds an exact accepted Store record to that pinned projection and
carries the original request unchanged for receipt content. The request's
original subject is a digest of the raw article; the Store record's content
subject is a digest of its Path/Xref projection, and they need not be equal.
The live `fn-peer-decide-transfer` decision and peer generation must be checked
before creating the intent or retrying an uncommitted Store attempt. Recovery
uses the persisted projection and Path identities, never later peer policy to
reinterpret old bytes. Existing intents and v2 contexts retain their raw-byte
binding and historical receipt replay; they are not reinterpreted as transit
records. The BP-only loopback trust command grants no inbound groups; an
explicit inbound profile and local path-identity policy are prerequisites to
`:want` under `fn-peer-decide-transfer`.

The theorems, in `books/bp-native-app-invariants.lisp` (new), soundness
first:

```lisp
(defthm fn-bpaj-submit-is-sound
  (implies (and (fn-bpaj-statep joined) (fn-sn-statep store) (fn-node-statep node) (fn-cfgp cfg)
                (equal (car (fn-bpaj-admission node cfg joined store request-octets ingress clock generation))
                       :submit))
           (let ((peer (fn-bpaj-ingress-peer cfg ingress)))
             (and peer
                  (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))
                  (fn-bpaj-principal-admitted-under-path-p cfg ingress peer) ; mentions A-BP-PATH (§2.3)
                  (equal (fn-peer-decision-kind
                          (fn-peer-decide-transfer node cfg peer
                                                   (fn-bpaj-msgid request-octets)
                                                   (fn-bpaj-article request-octets) clock
                                                   (fn-bpaj-id request-octets)
                                                   (fn-bpaj-subject request-octets)))
                         :want)
                  (equal (cadr (fn-bpaj-admission node cfg joined store request-octets ingress clock generation))
                         (fn-peer-injection-arguments node cfg peer
                                                      (fn-bpaj-msgid request-octets)
                                                      (fn-bpaj-article request-octets) generation
                                                      (fn-bpaj-id request-octets)
                                                      (fn-bpaj-subject request-octets)))))))

(defthm fn-bpaj-bind-is-the-exact-accepted-record
  (implies (and (fn-bpaj-statep joined) (fn-sn-statep store) (fn-node-statep node) (fn-cfgp cfg)
                (equal (car (fn-bpaj-admission node cfg joined store request-octets ingress clock generation))
                       :bind))
           (and (equal (fn-peer-decision-kind
                        (fn-peer-decide-transfer node cfg (fn-bpaj-ingress-peer cfg ingress)
                                                 (fn-bpaj-msgid request-octets)
                                                 (fn-bpaj-article request-octets) clock
                                                 (fn-bpaj-id request-octets)
                                                 (fn-bpaj-subject request-octets)))
                       :have)
                (equal (cadr (fn-bpaj-admission node cfg joined store request-octets ingress clock generation))
                       (cadr (fn-bpaj-record-lookup store (fn-bpaj-request request-octets))))
                (fn-bpaj-record-matches-requestp
                 store
                 (cadr (fn-bpaj-record-lookup store (fn-bpaj-request request-octets)))
                 (fn-bpaj-request request-octets))
                (equal generation (fn-bpaj-request-generation joined request-octets)))))
```

`fn-bpaj-record-matches-requestp` takes three arguments, `(store record
request)` (`bp-native-app.lisp:347`), and the store is substantive: it is
what establishes that the record is an accepted record of that Store
(`fn-bpr-store-record-acceptedp`). The first revision's two-argument call
was an arity error. `fn-bpaj-principal-admitted-under-path-p cfg ingress
peer` says the ingress's principal is `peer`, admitted by
`fn-bpaj-session-principal` over the session's channel, and holds
`(fn-assume-bp-path-authentic boundary channel peer)` for the boundary of
the peer's trust row; this is how the soundness theorem mentions A-BP-PATH
rather than resting on it in prose.

The converse (`:want` implies `:submit`) is **not** claimed. It needs
`fn-bpaj-coherentp node cfg joined store`, a composed invariant connecting
the node, the Store, the joined receiver state and the configuration; K6's
lane states that predicate and the iff under it as a separate target after
the two soundness theorems certify. The refinement fact the peering packet
asks for stays as stated before, now as a teeth-book theorem: where the old
dispatcher answered `(:submit)` for an ingress with a peer, the new decision
is `:want` or refuses for one of `:loop :out-of-scope :capacity :no-inbound
:oversize :no-date`.

Receipt destination: a receipt is addressed to the request bundle's source
EID, as `bp-app.lisp:185` does today with `source`, and routed; the
delivering session's peer is only a possible next hop (BP-R20).
Provenance: `fn-prov-make-bp` (`bp-native-app.lisp:325`) records
`(:bp-receive node bundle-id policy)` and gains the ingress principal and
generation. Teeth (BP-R19): same Message-ID with different content is
`:refused` or `:store-binding-conflict`, never `:bind`; conflicting accepted
records; stale generation; missing duplicate record; a reassembled request
whose fragments share a principal is admitted (slice C2; under question 5
fragments of different principals are never combined, so the old
"disagree gives `:no-principal`" case becomes "never reassembled");
self-delivery; an unconfigured session identity; N15, a session whose
channel selects a configured peer but whose announced EID is not among
that peer's rows, is refused `:eid-mismatch` and nothing it delivers is
admitted under the announced identity.

`books/bp-native-app` is red at its digest and opens the record codec
book-wide; the K6 edit waits for T1's BP-receiver cluster (slice A3's gate).

## 7. Limits, reassembly, fragmentation, routes, reports

### 7.1 Limits that compose (§12, D-9)

`*fn-bpf-max-length*` is now 65538, equal to `*fn-bpa-max-octets*`.
`fn-bpn-limits-compose` in `books/bp-limits.lisp` proves the relationships
among the limits in the current finite machine: ADU/reassembly equality,
image capacity, lifecycle-record headroom and aggregate capacity for 64
maximum-size images. The machine still checks each actual encoded image.
The planned explicit header cap, stage slots and stage octets are not yet
machine fields, so their rows below remain obligations for the family-plan
batch. The limit equality alone does not establish maximum-size ADU service.

| Limit | Value today | Must satisfy |
| --- | --- | --- |
| request and receipt ADU | `*fn-bpa-max-octets*` 65538 | ≤ reassembly length |
| reassembly length | `*fn-bpf-max-length*` 65538 | = ADU max; proved in current constants |
| bundle image | `*fn-bpn-machine-max-job-octets*` = `*fn-frame-max-blob*` 131072 | ADU max + `*fn-bpn-max-header-octets*` ≤ it |
| record payload | `*fn-bpn-lifecycle-max-payload*` 134144 | bundle image + held-record overhead ≤ it |
| fragment count | `*fn-bpf-max-fragments*` 64 | count × (per-fragment image) ≤ stage-octets; count ≤ stage-slots + 1 |
| TCPCL transfer | the route's transfer MRU and the session's negotiated MRU | a whole image or a fragment image ≤ it (§7.3) |
| aggregate | `max-octets` 16777216 | max-held × bundle image ≤ it, or the byte budget is the binding one and says so |
| execution | fast reassembly and cutting | cost linear in output length plus fragment bytes (§7.4) |

### 7.2 Reassembly as a family replacement (F-F)

A local-destination fragment is dispatched `:await-fragments` (kind 6,
adding `:reassembly-pending`). Reassembly is **the receiving node's local
active-set decision**; it never interprets a sender's private family plan.
The **active set** `fn-bpn-active-set st key` for an ADU key is the held
fragments with that key that are not deleted and not consumed, whose total
ADU length and headers are coherent with each other
(`fn-bpn-family-headers-coherentp`, T4), and whose ingress principals are
compatible (question 5: equal principals, recommended; the set is keyed by
`(key . principal)`). Locally consumed or deleted entries are excluded; no
ADU is globally blacklisted because one local copy was retired. The
progress step's dispatch branch, for a fragment, computes
`fn-bpf-reassemble-fast` over the active set, ordered by offset; arrival
order only chooses which active set is served.

The finite C2 query in `bp-node-fragment-family.lisp` currently reads A1's
actual `fn-bpnf-held-list`. An anchor must be a live held fragment; rows join
its set only when admitted principal, ADU key and primary-header coherence
key agree. Deleted rows and rows marked `:reassembly-consumed` in the
constraint slot are excluded. That consumed marker is a query convention
until the durable family replacement event exists. The query projects the
selected bundles into `fn-bpf` cells and calls `fn-bpf-reassemble-fast`;
success entails an offset-zero source, independent of arrival order. A1's
receive proposal does not alter this query before its matched durable
publication. The query is read-only and has no host caller or machine
replacement event yet, so it does not establish the later T4 conservation,
retirement, or final-delivery claims.

The A3 native Store dispatcher calls `fn-bpah-pending-view`. That selector
now excludes every fragment before classifying its payload, including a
fragment whose payload bytes themselves decode as a valid request ADU. Its
host-facing theorem `fn-bpah-host-pending-view-excludes-fragment` and a
reachable partial-ADU witness cover this safety gate. A complete C2 query
still requires durable family replacement before Store may see a whole ADU.
`fn-bpnf-family-plan` in `bp-node-fragment-plan.lisp` projects a bounded
candidate from the C2 active set: it takes the offset-zero primary and
extension blocks, replaces the payload with the fast reassembly result,
names the consumed principal/identity/arrival rows, and checks the exact
post-replacement slot and octet budgets. The served
`fn-bpnf-fragment-step` asks for that plan; proposal retains every source
fragment, and only a matching durable kind-18 publication invokes the same
`fn-bpnf-family-apply` rule used by ordered byte replay. Refusal leaves the
source rows intact; uncertainty fences ordinary events until recovery.
The first kind-18 byte component, `bp-fnbs-family-codec.lisp`, encodes
`(epoch, operation-id, anchor-arrival, whole-arrival, exact-whole-wire)`
under the protected FNBS frame. The anchor is a previously durable kind-5
arrival, and the whole arrival must be allocated by the node's durable
arrival frontier. Replay must recompute the active family from earlier
kind-5 rows and compare the wire byte for byte before applying replacement;
the record alone is not authority to retire fragments. The codec currently
has round-trip/corruption witnesses. The state-owned `next-arrival` frontier
allocates the whole's arrival independently of live held-list length and is
reconstructed from ordered kind-5/7/18 replay.
`fn-bpnf-family-apply` is the pure replacement rule shared by live
completion and replay: it rejects repeated anchor arrivals and wrong
whole arrival or bytes, recomputes the principal/coherence active set, and
copies the offset-zero source's ingress and retained age anchor. The native
service calls the fragment wrapper and ACL2 publisher authorization for kind
18, then advances the family selector after durable kind-5 reception and
cold recovery. The native interrupted-contact fixture and fragment-step
guard closure remain to be qualified. This finite slice does not yet provide
kind-10 conflict deletion, retransmission correlation after replacement,
or proactive forwarding fragmentation.

- `(:ok bytes)`: propose kind 18 `(fn-bpn-rec-reassembled token family held
  ids)`. Applied atomically: the fragment entries leave the live list (their
  kind-5 records stay in the journal as provenance, their dispatch and
  reassembly obligations are finished by this record), and one entry is
  appended: primary `(fn-bpn-unfragment ...)` of **the offset-zero
  fragment** (not the first to arrive, N10), the extension blocks of that
  fragment, payload `bytes`, ingress `(:family family ingresses)`,
  `:dispatch-pending`. Live slots change by `1 - (len ids)`; no sixty-fifth
  slot is ever needed, and T4's replacement theorem says so. The
  reassembly `(key → whole id)` enters the correlation index.
- `(:missing lo hi)`: nothing durable; the entries wait `(:fragments key
  n)` (§4.2).
- A fragment is not combined with an active set whose headers it
  contradicts; it forms or joins the set it is coherent with, and
  incoherent singleton sets expire normally.
- **A retransmitted fragment after reassembly** is answered `:duplicate` at
  reception while the reassembled bundle is live or its reassembly is in
  the correlation index (§4.1 step 4); past that, it forms a new active set
  that completes or expires, and a second complete reassembly is a second
  local delivery that the join answers idempotently by work id (the
  stale-operation behaviour; never a second article).
- `(:conflict i)`: kind 10 `:block-unintelligible` for the later-arriving
  fragment of the conflicting pair; it is deleted, so it is excluded from
  every later active input (BP-R13, "no poisoned input"), and a later valid
  fragment can still complete the cover.
- `(:invalid :bounds)`: kind 10 `:block-unintelligible` for this fragment.

`family` for reassembly is the active set's key, `(ADU key . principal)`
under question 5's recommendation. Repeated reassembly after restart is
impossible by construction: kind 18 removed the inputs.

### 7.3 Proactive fragmentation as a durable family plan (F-G)

When `start-one`'s selected entry's forwarding image exceeds the next hop's
transfer MRU and the bundle is fragmentable:

1. `fn-bpn-fragment-plan st h mru obs` computes boundaries such that every
   child's **encoded forwarding image**, with its mutable blocks set at
   their worst-case width (below) and the encoding-length changes they
   cause, is ≤ `mru`; it checks each image, not an overhead constant. A
   whole parent uses the whole-parent contract of T4; a fragment parent the
   re-fragmentation contract. If no plan exists (an MRU
   below the minimum feasible image, or more than `*fn-bpf-max-fragments*`
   children), the answer is `(:forward-refused id peer :mru-infeasible)` and
   nothing durable.
2. Propose kind 15 `(fn-bpn-rec-family-planned token family plan)`, `plan`
   binding parent id, the planned child set (index, child id, subrange),
   total ADU length, the parent's submission lineage, and the completion
   policy (the work is `:forwarded` when every required child is
   forwarded). It **reserves** one live slot and the child's image octets
   per planned child against `max-held` and `max-octets` themselves (the
   reservation counts in the live measures of §2.1, capped by
   `stage-slots`, `stage-octets`), and the journal debt `1 + 3·children`;
   admission fails without all three.
3. For each unmaterialized child in index order, kind 16
   `(fn-bpn-rec-family-child token family index held)`: the child entry,
   `:forward-pending`, the parent's next hop, lineage `(:family family
   index)`. The child's slot and octets move from reservation to live, so
   both inequalities are preserved across the conversion. Materialization
   is the progress step's owed work while the plan is open; a restart with
   a proper prefix of children resumes at the next index. Its rank is the
   number of unmaterialized children.
4. Kind 17 `(fn-bpn-rec-family-retired token family disposition)` removes
   the parent: `:materialized` after the last child (BP-R12: never before
   every child is durable); `(:terminated reason)` when the parent must end
   before materialization completes (its lifetime decided expired, a
   deletion), which in the same record moves every unmaterialized child to
   terminal `(:cancelled reason)` and releases their reservations.

**The conservation invariant** (review-2 §7), a conjunct of
`fn-bpn-machine-statep` for every open plan `P`,
`fn-bpn-family-conservedp P st`: the planned child set partitions into
**unmaterialized**, **materialized-live** and **terminal-with-an-outcome**;
the three are disjoint and their union is exactly the planned set. Every
live child has the planned identity, subrange, ADU key, total and lineage;
every terminal child has an explicit outcome (`:forwarded`, `(:deleted
reason)`, `(:cancelled reason)`), never an unexplained absence. Reserved
slots and octets equal those of the unmaterialized children.

Three facts are separate, and none implies a later one:

1. **materialization completed**: no unmaterialized child (every child was
   durably created or cancelled);
2. **parent replacement completed**: kind 17 is applied, so no parent
   bytes are still needed for any child;
3. **forwarding succeeded**: every required child's outcome is
   `:forwarded`.

After (1) and (2), children can still expire: the plan closes, when its
last child becomes terminal, with outcome `:forwarded` or `(:family-failed
children)`, recorded in the submission outcome; the work's retry policy
(§9.6) remains responsible for a failed family. A forwarded child is not
evidence that its siblings were forwarded. A duplicate local submission
names the parent's outcome, whose `family` names the plan. No host-side
fragmentation controller exists.

**The image is checked again at send time.** A child's forwarding image
can grow after planning (the Bundle Age encoding crosses a CBOR width
boundary). Recommended (question 6): the plan's boundaries are chosen so
that every child fits the MRU with the mutable blocks at their **worst-case
encoded width** (Bundle Age at its 9-octet width, Hop Count at its maximum,
Previous Node at this node's EID), and `fn-bpn-plan-child-image-bounded`
states it; `start-one` still computes the actual image (§4.3 step 3) and a
child that exceeds a *smaller* session MRU than planned (a route change)
is re-fragmented as a fragment parent under T4's re-fragmentation
contract, never restored by unfragmenting.

### 7.4 The executable refinement (F-H)

`books/bp-fragment.lisp` stays the reference. `books/bp-fragment-fast.lisp`
now defines `fn-bpf-fragment-fast` (a cursor over the payload) and
`fn-bpf-reassemble-fast` (bounded position scans). Both have certified
all-input equality with the reference, including the four reassembly
outcomes, conflict precedence and least reported positions. Reassembly
validates input before scanning, probes at most 64 fragments at each output
position, and makes at most three position scans. It avoids full-canvas
allocation for conflict and gap outcomes; the success path still builds the
output canvas. This is a work bound, not measured native speed. The planned
sorted-interval linear algorithm and machine/native call-site connection
remain C2 work. Slice C measures (BP-R22) payload size and held-set size
independently on the native image: allocations, time and latency for
success, gap, overlap and conflict.

### 7.5 The routing table's configuration home (F-I, §12 D-3)

- Slice A: the host installs one route from the same command-line arguments
  `bp-service run` takes today plus the peer's EID; the machine decides from
  a table.
- Slice B: rows under the existing peer-row family and the existing
  `:set-peer` kind (`config.lisp:644-647`), labels `"transport-bp"` (exists,
  `peer-config.lisp:281`), `"bp-cl-host"`, `"bp-cl-params"`, `"bp-cl-mru"`,
  `"bp-reach"`, read by `books/bp-routes.lisp` (new, `fn-bpn-route-*`):
  `fn-bpn-routes-of-config cfg` and the keystone that every route it reads
  from an admissible configuration is an `fn-bpn-routep` address with an
  `fn-bpp-eidp` peer. The writer is `fn-bpn-route-rows-compose group rows`,
  and its keystone is that every row of `group` without a BP label is in
  the result unchanged. Live selection uses the table of the current
  configuration generation; the loop issues `:routes` on every generation
  change; history never consults it (§3.4); an already forward-pending entry
  whose next hop disappears is rerouted by kind 13 (§4.5, BP-R14).
- No new delta kind in `books/config` (§12, D-3).

### 7.6 Status reports (§12, D-6)

`books/bp-status-report.lisp` (new, slice D1, `fn-bpn-report-*`, over
`bp-primary-cbor`). The payload grammar, RFC 9171 §6.1.1, corrected per the
review's §4:

```text
admin-record  = [1, status-report]
status-report = [status-info, reason, source, creation-timestamp]            ; subject is whole
              / [status-info, reason, source, creation-timestamp, offset, length] ; subject is a fragment
status-info   = [received, forwarded, delivered, deleted]
assertion     = [false] / [true] / [true, dtn-time]   ; the time only when the subject asked for times
```

Structural target (not a captured vector): `[1, [[[true], [false], [false],
[false]], reason, source, [time, sequence]]]`. Offset and length are two
fields, not a nested pair. Whether an assertion carries a time is governed
by the **subject's** "status time requested" flag, not by fn's own
choice; fn's parser accepts timed assertions on incoming reports.
`fn-bpn-report-decode` is bounded, exact and canonical in the pattern of
`fn-bpa-decode-exact`; `fn-bpn-report-decode-of-encode` and
`fn-bpn-report-accepted-input-is-canonical` are its codec keystones, and the
reason table is Table 1 codes 0 to 11. The decoder rejects inputs over
4,096 octets before parsing. The current report recognizer limits a DTN SSP
to 1,024 octets and the other fields to fixed counts and 64-bit integers;
`fn-bpn-report-encode-length-bound` proves a valid report's encoding is at
most 1,194 octets, so the round trip needs no separate size premise. D1a
covers this codec and its exact wire vectors only; generation, correlation
and consumption remain D1b/D2 work.

Generation. `fn-bpn-policy-reports` defaults to nil in every image and every
configuration (RFC 9171 §5.1: disabled by default); the lab and operator
configurations enable it explicitly, with the historical and journal
budgets of §2.1 applying to report bundles like any other. When enabled and
requested, generation at each of the four points is a SHOULD of RFC 9171
and fn generates: reception (§4.1), forwarding (§4.3), delivery (§4.2),
deletion (§4.2, §4.3). `:report-due` makes the loop reserve a sequence and
issue `:author-report`, which the node turns into a durable outbound carrier
with submission `(:report subject assertion)`. The kind-10 deletion record
retains the exact selected report intent across a crash before outbound
authoring, and the outbound job key binds that intent to one carrier.
Reports are diagnostic evidence only and never necessary for application
retry or release (§9.6). A report never requests reports.

Consumption. §4.1 step 5 for received ones and §4.2's `:administrative`
dispatch for locally authored ones; both use
`fn-bpn-correlation-of-subject` (§2.4) to find the submission, including
fragment subjects. What reports are for (review-2 §9): labelled **remote
observations** for the operator and for interoperability, never release
authority and never a retry input. A report that says delivered does not
disable the receipt deadline, a replayed report does not move it, and a
report naming an older attempt's subject does not touch a newer attempt
(the correlation entry names the attempt tokens it covers). Parsing,
logging and correlating a report is bounded work per report and is served
in the loop's diagnostic share (§9.1), so report traffic cannot consume the
service accepted work needs.

The D1b kind-10 source now has an ACL2 held-row expiry selector, an outer
proposal step, an exact immutable publication authorization and one ordered
FNBS 5/7/18/10 replay. A definitely expired, unprocessed received carrier
gets a kind-10 record bound to its arrival and primary identity. The record
also carries the exact bounded status-report payload selected at proposal, or
the one-octet suppression sentinel; replay retains the full record in the
held tombstone. No report effect is issued before the deletion publication
callback is durable, and an uncertain callback fences the issued operation.
The recovery outbox selector can find that same intent after a process death.
The `fn-bpn-report-author-step` extension of the same service owner now
proposes an administrative outbound bundle/job from a recovered intent, using
a stable epoch/op work key. The native `bp-node` caller asks ACL2 to age held
carriers before Store dispatch, then queues owed reports through the base
lifecycle journal; received administrative reports are parsed and correlated
read-only by `fn-bpn-report-observe-next`. This source join still needs a
source-matched native image, the death-after-kind-10 test, and broader policy
qualification before a served D1b claim.

Minimal generation and consumption before slice B's gate (§11): the
deletion assertion at §4.2's `:expire` and §4.3's deletions, and §4.1
step 5's consumption, land as D1b; the other three generation points and
the foreign vectors stay in D2.

## 8. The scheduler: its policy, behind a real persistence boundary (F-A, §12 D-4)

`books/scheduler` decides which outstanding work gets an attempt; the
machine carries bundles. The scheduler is called natively per peer through
`books/scheduler-peers` (`fn-sched-table-step`); its selection, aging and
charging policy are reused. Its execution step is not:
`fn-sched-drive-attempt` (`scheduler.lisp:304-309`) prepares the attempt and
then supplies `(fn-bp-storage-complete-event txid 0 :durable)` itself (D1),
so `fn-sched-tick-step` (`:547`) can return the workflow's `:submit` without
the FNWF attempt record ever being published.

Repair, in `books/scheduler-runner.lisp` (new, slice A3):

1. `fn-sched-select ss wf` returns the work the tick would choose, and
   nothing else.
2. `fn-sched-prepare ss wf work` returns the workflow state after
   `fn-bp-attempt-prepare-event` and the FNWF record to publish; no
   `:submit` is released.
3. The loop publishes the FNWF record; `fn-sched-complete ss wf outcome`
   applies `(fn-bp-storage-complete-event txid 0 outcome)` with the real
   outcome. Only `:durable` releases `:submit` and charges the contact
   budget; `:refused` releases nothing and does not charge; `:uncertain`
   fences the workflow.
4. The refinement theorem:
   `fn-sched-runner-durable-branch-is-drive-attempt`: when the published
   outcome is `:durable`, prepare-then-complete equals
   `fn-sched-drive-attempt`, so every scheduler keystone applies to the
   successful branch; refusal and uncertainty are stated separately
   (`fn-sched-runner-refusal-releases-nothing`,
   `fn-sched-runner-uncertain-fences`).

`fn-sched-step`'s `:contact-open`/`:contact-close` are inputs that return
no effects (`scheduler.lisp:727-730`). Session management is the loop's
(§9.5): the loop opens a session when the scheduler's contact window
starts, and closes it when it ends, and those are the machine's `:session`
events. The machine forwards every forward-pending entry for an open
session in arrival order **among eligible candidates** until it is sent,
expires or is deleted (RFC 9171 §5.4). The FIFO theorem, restated
(review-2 §2.2), over the immutable `arrival` field (F-M):

The native FNBS contact runner uses `fn-bpsc-contact-event` in
`books/bp-contact-service.lisp` for a single peer/window tick. The CLI's
`start-delay` and `end-delay` are offsets in milliseconds from that invocation's
one monotonic observation, and ACL2 constructs and bounds the resulting
window. They are not persistent absolute contact-plan timestamps; no epoch
agreement is assumed across processes or reboot. The runner advances the
machine's clock before consulting ready peers, opens a contact only when
that peer is ready and the observation falls inside the inclusive window,
and closes the contact after a bounded send batch. Its host caller is
`fnn-command-bp-contact-tick` in `host/native/bp-contact.lisp`; effects go
through the same `fnn-bps-step` and durable publisher as the normal BP
service. The older FNWF `fn-sched-tick-step` cannot be called on the FNBS
machine: its modeled `:durable` completion does not represent an observed
FNBS publication outcome. This finite runner does not itself establish the
multi-class fairness or return-receipt progress claims below.

The native BP observation for durable Bundle Age anchors uses Linux
`CLOCK_BOOTTIME` milliseconds, whose origin is shared by processes in one
boot and whose elapsed time includes suspend. Before replay or an expiry
step, the service checks a bounded Linux boot-ID observation against a
durable FNBS clock-domain record. ACL2 validates the canonical boot ID,
classifies legacy namespace evidence, and decides whether the exact domain
record may be initialized, whether the saved domain matches, or whether
startup must fence. An absent domain alongside durable lifecycle or sequence
evidence, a malformed record, and a changed boot ID all fence before any
persisted age anchor is compared. Initialization uses the immutable publisher's
file and directory barriers under the shared journal owner. This is a
same-boot restart contract; cross-boot recovery and reanchoring remain open.
The standalone `bp send` command opens the same service owner before reserving
its sequence frontier, so newly authored wire cannot create unmarked durable
BP state. Existing legacy spools without a domain record remain fenced rather
than silently migrated.
Contact window offsets above are still per-invocation and do not become
persistent absolute timestamps.

```lisp
(defthm fn-bpn-start-one-selects-the-least-arrival-among-eligible
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal r RECORDS)
                (equal (fn-bpn-rec-kind r) :attempting))
           (let ((h (HELD (fn-bpn-rec-id r))))
             (and (fn-bpn-forward-eligiblep st h (fn-bpn-rec-peer r) (fn-bpn-rec-session r) OBS)
                  (not (fn-bpn-earlier-eligible-forward-p st h (fn-bpn-rec-peer r)
                                                          (fn-bpn-rec-session r) OBS))))))

(defthm fn-bpn-ineligible-forward-candidate-waits-on-a-named-dependency
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-forward-candidatep st h peer)
                (not (fn-bpn-forward-eligiblep st h peer session obs)))
           (fn-bpn-wait-names-a-dependency-p (fn-bpn-wait-of (fn-bpn-held-id h) st))))
```

The first is the property the service needs: least arrival among entries
that can run, not least arrival regardless. The second says an entry passed
over is waiting on a route generation, a session MRU, or journal credit,
and is reconsidered when that changes, not on every tick. The same pair is
stated for each class of §4.2 (`fn-bpn-progress-selects-the-least-arrival-among-eligible`).
A bundle's lifetime is not a bound on retries: nonprogress is bounded by
the loop's yield rule (§9.1) and by journal admission (§2.1).

A requeued bundle leaves the work `:attempted`, which is not retryable
(`fn-bp-retryable-statusp`, `bp-workflow.lisp:65`), so the workflow does
not make a second bundle while the first is carried; the receipt-loss
policy (§9.6) is what moves a stalled work on.

`tools/scheduler.py` retires when slice B's native call lands.

### 8.1 Contacts and the observable premises (review-2 §8)

Logical service turns stay the internal proof's unit (§5.7). They are not
presented as a deployment timing guarantee without a relation to elapsed
time and capacity, which this subsection gives the deployable profile.

**Contact vocabulary**, adopted from CCSDS 734.3-B-1, *Schedule-Aware
Bundle Routing* (July 2019), §2.3 to §2.4, for its planning model only (no
custody or other assumption of that document is imported, and a scheduled
contact is not a promise that it works). An opportunity is a **contact**:
a directed session interval from this node to a next hop, with

- the **contact interval**: planned start and end, and observed start and
  end;
- the **usable byte budget**: bytes transferable in the interval after
  TCPCL and bundle overhead, planned and observed;
- the **MRU**: the negotiated transfer MRU of the session (a bundle larger
  than it is not served by this contact, whatever its budget);
- the **observed completion latency**: from offer to final
  acknowledgement, per carrier.

A session that opens briefly is not necessarily a transfer opportunity for
a given bundle, and a return route in a table is not a future return
contact with enough capacity. A-BP-CONTACT and A-BP-RETURN are stated in
these terms (§5.7).

**Monitors: one operational witness per premise.** The service loop
measures and the node's page reports:

| Premise | What the monitor records |
| --- | --- |
| contact service (A-BP-CONTACT) | expected versus actual start and end; usable duration; bytes offered and completed; the largest missed opportunity |
| persistence (A-BP-PERSIST) | operation id, issued, barrier and result times, definitive versus uncertain outcomes, the longest outstanding publication |
| peer service (A-BP-PEER) | per eligible carrier: waiting age, refusal codes, completed-byte budget; not merely some unrelated successful attempt |
| owner service (A-BP-OWNER) | busy intervals, definitive responses, uncertainty and recovery intervals (N18) |
| journal service (A-BP-JOURNAL) | free records minus cleanup debt minus control reserve (§2.1) |
| return service (A-BP-RETURN) | a feasible timed return route and eligible receipt progress, not only an EID route entry |

**What a monitor establishes**, the sentence for the node's page: *a
monitor establishes that the premises held on the observed finite prefix of
this run, and detects when one was violated; it never proves that a future
contact will occur, so no progress bound is claimed beyond what was
observed.* A premise the monitor reports violated is reported as such
(N18), never folded into "satisfied".

## 9. What the host does

### 9.1 The serialized service loop (F-N)

`books/bp-service-loop.lisp` (new) defines the reducer the host runs; the
host does I/O and nothing else. **Slice A1 creates it** with the minimal
reducer and its correlation invariant, inside A1's proof boundary
(review-2 §10): the semantics that decide which completion releases which
ACK or effect are proved, not left in raw host code. Slice B extends the
same book with contact scheduling, per-class shares and fairness. A1's
version includes only the machine's books (never `bp-workflow`,
`bp-native-app` or `owner`).

```lisp
(fn-defrecord fn-bps-loop
  :constructor (fn-bps-make-loop machine inbox outstanding turn-budget)
  :fields ((fn-bps-loop-machine fn-bpn-machine-statep)
           (fn-bps-loop-inbox fn-bps-inboxp)             ; bounded FIFO of machine events
           (fn-bps-loop-outstanding fn-bps-op-listp)     ; I/O operations issued, by op id
           (fn-bps-loop-turn-budget fn-bpn-machine-limitp)))
(defun fn-bps-loop-step (loop input) ...) ; -> (loop . operations)
```

Inputs are external: a received transfer, a CL outcome, a publication
result, a session change, a timer tick, a configuration generation, a
delivery result, a workflow output. Rules:

- One machine event at a time; while the machine has a pending proposal,
  new events queue in the inbox. Nothing is dropped silently: a received
  transfer when the inbox is full is answered `(:refused :busy)` (so the
  ACK is XFER_REFUSE `No Resources`, §9.2); timer ticks coalesce;
  completions are never queued behind the bound (they are bounded by
  `outstanding`).
- Every I/O operation has an op id; its completion names it; a completion
  with an unknown op id is logged and ignored.
- Effects of a durable result are executed in order; follow-on semantic
  work (`:report-due`, progress after a durable record) is enqueued as
  events, never executed recursively.
- **Yield rule.** A turn runs at most `turn-budget` machine events. After
  an event that proposes nothing, or a refusal, the loop does not re-issue
  the same kind of progress event until an input changes the time, a
  session, the routes, or completes an operation (BP-R24).
- **Per-class shares** (slice B). A turn's budget is divided among action
  classes (reception answers, completions, progress by class, workflow
  outputs, diagnostics including report handling), each with a guaranteed
  share when it has work, so no class's backlog consumes another's
  service; this is what lets §5.7's bounds be per class.
- **Operation ids are logical and monotone** across restarts and rotation
  (§3.6); a completion from an earlier epoch never matches.
- After `:restart-ready`, the loop issues `:routes`, then sessions, then
  `:clock`.

**The correlation invariant** (A1), `fn-bps-correlatedp loop`: every
outstanding operation id names exactly one machine obligation, and each
machine obligation that awaits the host has exactly one outstanding
operation: a publication (its token, which is `issued`), a `:cl-send` (its
attempt token and session), a `:deliver` (its delivery token), a
reception callback (its ingress, awaiting a `:receive-answer`). A1's
keystones:

- `fn-bps-step-preserves-correlation`.
- `fn-bps-completion-releases-only-its-own-operation`: a completion with op
  id `o` changes only the obligation `o` names and releases only the
  effects the machine attached to it; an unknown `o` changes nothing.
- `fn-bps-reception-answer-is-the-machines-disposition`: the disposition
  the loop returns to the TCPCL callback for a transfer is the disposition
  of the machine's `:receive-answer` for that transfer's ingress, and no
  other (the subject §9.2's ACK mapping reads).

`fnn-bps-step` (`bp-service.lisp:110-116`) stays the one call into the
machine; `fnn-bps-drive-effects` (`:207`) is replaced by the loop's
operation executor. The current `fn-bpn-contact-step` drops events while a
proposal is pending (`bp-node-machine.lisp:473-475`, D10); the inbox is its
repair.

### 9.2 Reception and the ACK (F-D, §12 D-5)

- `*fnn-tcl-deliver*` is bound to a callback that submits
  `(:bundle-received octets ingress obs)` to the loop and **returns the
  disposition** from the matching `(:receive-answer ingress disposition)`.
- `fnn-tcl-act`'s `:bundle-received` arm calls the ACL2
  `fn-tcl-delivery-plan` with the held TCPCL messages, transfer ID, and the
  callback result. `(:accepted path-or-nil)` releases the held final
  XFER_ACK (nil path is an exact already-durable duplicate);
  `(:refused :capacity)`, `(:refused :busy)`, and
  `(:refused :persistence)` replace it with XFER_REFUSE `No Resources`
  (`*fn-tcl-refuse-no-resources*`), any other definitive refusal with `Not
  Acceptable`; `(:uncertain ...)` drops it and fails the session. The host
  executes the plan's exact message list; it does not select the protocol
  code. The planner validates that the held list ends in the matching END
  ACK. It preserves earlier machine outputs in the same read batch, including
  non-ACK controls and partial ACKs for an earlier transfer, while refusing
  any earlier END ACK.
  Its keystone, restated (review-2 §10): **no successful final
  END acknowledgement for a late-refused transfer.** Partial XFER_ACKs for
  earlier segments (RFC 9174 §5.2.3) may already have been sent and are
  permitted and are preserved when still held. What is excluded is an
  XFER_ACK with the END flag acknowledging the whole transfer from the
  refusal or uncertainty path:

  ```lisp
  (defthm fn-tcl-late-refusal-gets-no-final-ack
    (implies (fn-tcl-held-final-ackp messages xfer)
             (let ((plan (fn-tcl-delivery-plan
                          messages xfer (list :refused reason))))
               (and (equal (fn-tcl-delivery-plan-status plan) :refused)
                    (not (fn-tcl-output-has-final-ackp
                          (fn-tcl-delivery-plan-messages plan) xfer)))))
  ```

  and its sender-side companion,
  `fn-tcl-partial-acks-are-not-completion`: the sender's outcome is
  `:outbound-sent` only on an END acknowledgement whose acknowledged length
  equals the transfer length; acknowledged prefixes never complete a
  bundle. A late capacity refusal is never a success ACK (BP-R10, N12).
- The ACK is released when kind 5 is durable, before dispatch, delivery or
  any application work: the callback returns as soon as the receive answer
  exists; the loop continues with the queued progress events after it.
- At XFER_SEGMENT START with a Transfer Length Extension, the session calls
  `fn-bpn-transfer-admissiblep` and refuses `No Resources` early when it
  answers nil. Without the extension there is no early answer; the END
  disposition decides.
- The receive-evidence namespace is not written on this path; the kind-5
  record is the one authoritative receive record (§12, D-8).

### 9.3 Delivery, by ADU class

- `:request`: under the owner mutex, the receiver join with
  `fn-bpaj-admission` (§6) in place of `fn-bpaj-dispatch`'s `:submit` arm.
  Its result is the `:deliver-result`: `(:accepted rid)` (a new commit
  and receipt decision), `(:duplicate rid)` (bound to the existing
  accepted record), `(:returned rid)` (the join's `:return-receipt` from a
  committed receipt, `bp-native-app.lisp:404`), `(:refused r)`, `:busy`
  (the join's `:blocked`, `:405`, and `:defer`), `:uncertain` (the owner
  fenced). `rid` is `fn-bpaj-receipt-id` of the request (`:408`). The
  Store commit and the FNRJ receipt decision are the join's durable
  writes, unchanged; the kind-7 record then makes the handoff `:owed`
  (§2.4).
- `:receipt`: the sender's receipt consumption: the workflow's receipt
  event, `fn-bprl-release-decision`, the release record, and
  `fn-retain-release` on the owner Store's forwarding pin, with the
  independent archive pin untouched (review §5.4). This path is slice A3's
  and runs against the native owner's Store, not a shadow workflow image.
  The request join is never the receipt path.
- When `report-p`, the loop issues `:author-report` after kind 7 is
  durable.

### 9.4 The receipt outbox: FNRJ to FNBS (F-C, §12 D-12)

The first native A3 caller is `host/native/bp-node.lisp` in the full image.
It opens the clock-gated single FNBS owner, then the Store owner. `serve`
returns the TCPCL custody disposition after kind-5 durability and separately
drives the ACL2 `:deliver` marker through Store/FNRJ or FNWF/Store, followed
by kind-7 publication. `dispatch` repeats that work after a process restart.
The ACL2 `fn-bpah-outbox-view` binds each owed handoff to its delivered held
request and a return job key containing its state-owned arrival index, so a
new retry carrier with the same receipt ID cannot alias the first. The native
caller obtains the receipt ADU from recovered FNRJ, compares any existing
job's exact ADU and peer through ACL2, queues it in FNBS, and leaves transport to a later
explicit contact tick. `fn-bpah-outbox-effective-status` now projects
`(:handed-off sequence)` without a second mutable flag, but only when the
selected `(rid, trigger)` handoff, recovered FNRJ receipt ADU and durable
FNBS job's exact payload and peer agree. Missing or contradictory evidence
remains `:owed`; a malformed view is `:invalid`. The native caller's switch
to this projection is a separate integration step. The stored kind-7
handoff remains `:owed` so the projection can be reconstructed after restart.

A receipt is owed output while its handoff is `:owed` (§2.4): created by
the kind-7 record of the request delivery that named it, ended by the
kind-5 record of submission `(:receipt rid trigger)`. "Owed" is a present
authoritative record, never the absence of an evictable one (the first
revision defined it as "no carrier binding", which history eviction made
true again, N01).

- `fn-bpn-owed-handoffs st` (machine, slice A1) lists the `:owed` handoffs;
  its keystone `fn-bpn-owed-handoff-ends-only-by-its-receipt-carrier` says
  an `:owed` handoff changes only by the kind 5 of its own submission, and
  no record of kind 11 or 12 removes it.
- `books/bp-receipt-outbox.lisp` (new, slice A3, `fn-bprx-*`) builds the
  receipt ADU for a handoff from FNRJ: `fn-bprx-receipt-adu fnrj rid` is
  the committed receipt, and `fn-bprx-handoff-adu-is-the-committed-receipt`
  its keystone; it computes no ownedness of its own.
- After every durable kind 7 that creates a handoff and at every recovery,
  the loop issues `(:transmit (:receipt rid trigger) source-eid sequence
  adu obs)` for each owed handoff, addressed to the request bundle's source
  EID and routed (§6). `:transmit`'s idempotence (§4.4) makes redrive safe.
- **Retry has one owner, the requester** (D-16). If the receipt carrier
  expires or is deleted, the receiver does not reauthor it. The
  requester's retry (§9.6) sends the **same application request** (the
  request ADU carries no attempt field, `bp-adu.lisp:44-55`, and the join
  compares it whole under its work id, `bp-native-app.lisp:228-233`, so a
  changed request would be `:conflict`) in a **new carrier** with a new
  bundle identity. The join answers `(:returned rid)` from the committed
  receipt, kind 7 creates handoff `(rid, new trigger)`, and a new receipt
  carrier is authored: same receipt fact, new reply submission, no second
  article and no second pin (N13). A receipt fact is never lost; a receipt
  carrier may be.
- `fnn-bpapp-pause-after-decision` (`bp-app.lisp:143`) stays as a test cut
  and gains its siblings: after Store commit, after receipt decision, after
  FNBS enqueue, after local completion, after the receipt carrier is
  discarded (BP-R03 to BP-R05).

### 9.5 Forwarding and sessions

- The loop opens one outbound session per peer when the scheduler's contact
  starts (until slice B, when a transmit makes an entry forward-pending to
  a configured route), keeps it for the contact, and issues `(:session peer
  s t mru obs)` with the negotiated MRU; a passive session opens `(peer .
  s')` for its duration once `fn-bpaj-session-principal` has answered
  (§2.3), carrying the principal it admitted or nil.
- `:cl-send` offers `image` on session `s` (`fnn-tclc-pending`), and the
  outcome `:outbound-sent`, `:outbound-refused` with its Table 6 code (the
  code reaches the machine; today it is logged at `tcpcl.lisp:274` and
  dropped, D11), or `:outbound-failed` answers `:forward-result` with the
  attempt token and session the effect carried. A session that ends with an
  offer outstanding answers `:uncertain`.
- After each result, while `s` is established, the loop issues `(:resume
  peer s obs)` subject to the yield rule.

### 9.6 The receipt-loss retry policy (F-B)

Reports are optional; retry is not. **Overdue is defined over unresolved
work and its stable retry terms, never over remote transport statuses**
(review-2 §2.3). `fn-bp-receipt-overduep work obs policy` (new in
`books/bp-workflow.lisp`, slice A3) is true exactly when:

- the work is outstanding (`fn-bp-work-outstandingp`: no receipt consumed,
  not abandoned), whatever its transport status, `:delivered` included;
- its current attempt has a durable start (the FNWF attempt record's
  anchor), and `obs` decides that `receipt-wait` (a term of the work's
  policy) has elapsed since it;
- the policy's attempt bound is not exhausted (exhaustion is its own
  outcome, `:retry-exhausted`, reported, not silently dropped).

It reads no transport status, so no observation moves the deadline:
`fn-bp-transport-observation-preserves-receipt-overdue` (T5). A report
that says delivered, a replayed report, and a report about an older
attempt all leave it unchanged (N02). The first revision's whitelist
(`:forwarded`, `:attempted`, `:bundle-created`) omitted `:delivered`, so a
delivery report followed by a lost receipt stranded the work; today's code
strands it too (D22).

An overdue work is moved by `fn-bp-request-retry` (`bp-workflow.lisp:615`,
which already accepts any outstanding work) to `:unknown`, which is
retryable (`:65-68`); the scheduler prepares a new attempt with a new
attempt id, so the new carrier has a new submission identity and a new
bundle identity, and carries the unchanged request ADU (§9.4). The loop
evaluates the predicate on its timer. A delayed report is interpreted
through the correlation index (§2.4) as a labelled remote observation and
can only advance the work's transport status, never close it (T5). BP-R09
is this policy with every report dropped; N02 is it with a delivery report
present. A receipt-wait timer bounds the next local retry opportunity, not
delivery time across disconnected links: a finite completion bound needs
forward and return service (§5.7).

### 9.7 Authoring, clock, routes, restart

- `:transmit` for a work: the loop reserves the sequence first (PRF-045);
  a retry of the same submission gets `:duplicate` from its outcome and its
  new sequence is burned (§4.4).
- `:clock` on a timer and after every durable result, subject to the yield
  rule.
- `:routes` at open after `:restart-ready`, and on every configuration
  generation change.
- `:restart` at open, with the observation.

## 10. The checkpointed branches

Measured against `dev` `722c9566` for the first five rows (every `defun` and
`defthm` they add is on `dev` by name) and against `dev` `2788d4cb` for the
last.

| Branch | On `dev` | Disposition |
| --- | --- | --- |
| `w12/bp-sequence` | kind 1, the sequence frontier, the persistence-cut model | nothing left to take; delete |
| `w13/bp-lifecycle` | `fn-bpn-step`, the proposal machine, M1 to M3 | nothing left to take (its contact step lacks `f4d061d2`'s guard); delete |
| `w18/bp-lifecycle-assurance` | PRF-046's three keystones, byte-identical | delete; landing note names `f4d061d2 ec64c5d3 29c8d8b2 ff80403e 3a7ef781` |
| `w19/bp-app-fast-invariant` | the fourteen `fn-bpaj-*-fast-is-checked` and `fn-bpaj-successful-replay-has-statep` | nothing left to take (`51a0b1a3` is `dev`'s `6708e238`); delete |
| `w19/bp-authored-wire` | `fn-bpn-authored-wire-authorize-carries-reservation` and teeth, byte-identical | delete |
| `w25/bp-obligation-vertical` (13 ahead) | since `9dd5e3a2` (merged `2788d4cb`, persvati `certify-20260922T184059Z-2797731`): `fn-bprl-release-record`, `fn-bprl-replay-records`, `fn-bprl-replay-journal` in `books/bp-release.lisp`, landed verbatim from `faf16519` because `host/bp-release-owner-host.lisp` calls the last and `host/native/build.lisp` loads that file | **slice A3 takes** `books/bp-release-store.lisp` (`fn-bprl-store-join` and its three theorems, from `faf16519`), `books/bp-release-owner.lisp` (`fn-bprl-owner-join` and three, `4c42ef73`), `host/native/bp-obligation.lisp` and the `host/bp-release-owner-host.lisp` additions (`4c42ef73`, `e13d9007`, `e342c187`), the `host/native/workflow.lisp` and `host/workflow-host.lisp` changes of `faf16519` and `4c42ef73`, and the tests `tests/test_bp_obligation_native.py`, the `test_bp_app_native.py` and `test_bp_service_native.py` additions, `9e21db92`'s `test_native_app_journal.py` cases; each re-derived against the machine of slice A, not merged. **Not A3's**: the Store event-order commits `d9816877 c6270e3e 2f9f36d7 38f337ab 9d5df71d e16f54b0 adf63066 4c7cbfe1` and the `store-node*`/`store-files` parts of `e342c187` edit `store-node`, `store-files`, `replay`, `store-events`, `node-retention-transitions`, which are T2/T4's books; they are an input to T4's brief (D-15, the contract below). `faf16519`'s `frame-journal`/`frame` edits are re-derived by A3 against T1's frame seam. The branch is deleted after A3's landing note names what it took |

**The Store event-order contract** (D-15, review-2 Q3). T4 owns Store
event order; A3 owns the release joins; the dependency between them is
this statement, which T4 proves over the functions it owns and A3 cites,
not a commit number:

```lisp
;; T4 proves; names are T4's to fix. Subject: fn-sn-finish, the arm the owner calls.
(defthm fn-sn-release-completion-commutes-with-recovery
  (implies (and (fn-sn-statep s)
                (fn-sn-retention-event-p e)
                (fn-sn-event-ordered-after-p e (fn-sn-retention-event-txid e) s) ; after its accepted transaction
                (fn-sn-pending-is-p s e)                                         ; completed against the exact pending op
                (equal (fn-sn-finish-outcome s :durable) :ok))
           (and (equal (fn-sn-retention (fn-sn-finish-state s :durable))
                       (fn-sn-retention (fn-sn-recover (fn-sn-committed-history (fn-sn-finish-state s :durable)))))
                (equal (fn-sn-deltas-of (fn-sn-finish-state s :durable) e)
                       (fn-sn-event-arm-deltas e))                               ; article, index, config deltas of e's arm
                (fn-sn-archive-pin-unchanged-p s (fn-sn-finish-state s :durable)))))
```

In words: the retention state obtained by successful live completion of a
release event on the authoritative owner Store equals the retention state
recovered from its committed ordered history, with the deltas that event's
arm prescribes, and the independent archive pin is untouched. A3 develops
against this interface; A3's integration evidence depends on T4's theorem
and the owner-path test (N14), not on which of the eight commits
(`d9816877 c6270e3e 2f9f36d7 38f337ab 9d5df71d e16f54b0 adf63066 4c7cbfe1`)
carries it. The review could not resolve the branch; root supplies T4's
lane with the patch series, and until then no commit is marked integrated
or unnecessary.

Zero-ahead and superseded BP branches (`w10/dtn-3`, `w11/bp-node`,
`w11/tcpcl-*`, `w13/bp-convergence`, `w14/bp-sequence-fidelity`,
`w15/bp-receive-integrity`, `w17/bp-namespace`, `w18/bp-evidence-bounded`,
`w18/bp-publisher` but for four host lines root reads before deleting,
`w18/native-bp-app`, `w19/bp-authored-wire-pre-rebase`,
`w25/bp-authoritative-integration`, `w25/native-efficiency`, and the
2026-09-18 to 09-20 `w2`, `w4`, `w5`, `w6`, `w8`, `w9` branches) hold nothing
`dev` lacks and are deleted in slice A1's landing note.

Development oracles (plan §5.3): `tests/bp-dtn7/mock_bpa.py`,
`run_four_node_lab.py`, `lab_bpa.py`, `bp_fn_ingress_driver.py`,
`fn_sender_lab.py`, `run_fn_exchange_lab.py`, `run_fn_ingress_lab.sh`,
`run_two_node.sh`, `tools/bpa_dtn7.py`, `tools/bpa_payload_extract.rs`,
`build_payload_extractor.sh` survive until slice B's gate record exists and
are deleted in its landing note. `bootstrap.sh`, `pin.json`,
`run_fn_bp_interop.py`, `run_fn_tcpcl_interop.py`,
`run_fn_bp_sequence_durability.py`, `run_fn_tcpcl_spool_recovery.py`,
`run_fn_bp_authored_wire.py` and `tools/tcpcl_lab.py` drive the native image
and stay. The `bp send`, `bp receive`, `bp decode` verbs and the
receive-evidence namespace stay until their replacement has passed its gate
(§12, D-8): T13 re-points `run_fn_bp_interop.py` at `bp-service` after slice
D's wire evidence exists.

## 11. The lane structure: slices A to E

This replaces the phase-2/phase-3 briefs. Each slice lands its behaviour
with the safety and replay theorems that behaviour's ACKs depend on; there
is no proof-after-implementation interval (§12, D-10). Within a phase,
edited books are disjoint; every lane follows [how we work](../planning/how-we-work.md):
its own worktree, its own closure certified before it reports, 300 s per
book for discovery, 1800 s once for the final closure, `green_check
--changed-since <base> --strict`, an evidence file
`planning/evidence/bp-<slice>-<rev>-2026-09-xx.md`. hbox builds under
`swarm-build`; ACL2 by hand through `tools/acl2`.

Proposed placement against plan §3.3 (root's call; the plan's T12 rows are
root's to rewrite): phase 2: A1 (hbox 2), A2 (local, certifies on hbox by
farm), C1 (whichever lane frees first; its books are disjoint); phase 3: A1
continued, A3 (persvati 2 once T1's BP-receiver cluster is green), D1a
(local); phase 4: D1b then B (hbox 2); phase 5: C2 then D2 (hbox 2), E
(persvati 2).

Sizes sum to 37 to 50 lane-days against the plan's 20 to 31 for T12a to
T12d; the first revision's 32 to 44 grew by the three history records and
the debt invariant (A1), the issued-publication cut (A2), the session
principal and retry terms (A3), re-fragmentation and conservation (C1, C2),
the minimal report generation (D1b) and rotation (E). The implementation
lane's first commit in each slice is that slice's part of §11.1.

### Slice A: correct contracts and the two-process article-and-receipt round trip

Gate for the slice, run by A1 after A2 and A3 have merged: two native
processes on one box exchange **two** independent works, W1 and W2, each an
ordinary article; W1's application receipt returns through FNBS and W2's
receipt is withheld by the harness. The gate checks **identities and
authority, not counts** (review-2 §10):

- at the destination, exactly one accepted article per work in the
  **owner Store**, each matched by work id, request bytes and content
  subject, and by the accepted Store transaction id the join planned; one
  archive pin each;
- the returned receipt's issuer and authorization context are the
  destination's and the receipt names W1's work id, subject, requester,
  policy and terms;
- at the home, **exactly W1's forwarding pin** (by its retention key) is
  released by `fn-retain-release` through the release join; W2's forwarding
  pin remains; both archive pins remain (N14: releasing the wrong pin
  would preserve the aggregate count, so the count is not the check);
- the session principal was admitted under the declared `bp-boundary`
  (question 1) and the harness's second session with a matching address
  and a wrong announced EID is refused (N15);
- each crash cut of BP-R02 to BP-R05 taken by `kill -9` at a named cut and
  recovered, and N06's cut (publication visible, uncertainty callback run,
  then death), with the same identities afterwards.

Store and pins read through the owner, never from workflow or log
projections.

**A1: the machine (T12a). Fable. hbox. 8 to 10 lane-days.**
- Edits: `books/bp-node-machine.lisp`, `-invariants`, `-authorization`,
  `-codec` (kinds 5 to 14, retired 2 to 4), `books/tcpcl-session.lisp` (`fn-tcl-refuse-held-final`),
  new `books/bp-service-loop.lisp` (the minimal reducer and its correlation
  invariant, §9.1),
  `tests/acl2/bp-node-machine-tests.lisp`, `-authorization-tests.lisp`, new
  `tests/acl2/bp-node-machine-teeth-tests.lisp`, new
  `tests/acl2/bp-service-loop-tests.lisp`, `host/bp-node-machine-host.lisp`,
  `host/native/bp-service.lisp` (the loop's executor, sessions from the one
  configured route), `host/native/tcpcl.lisp` (disposition mapping),
  new `tests/test_bp_roundtrip_native.py`, `docs/prefixes.md`.
- Include closure: `bp-node-machine-codec` is about 65 books (`bp-node`,
  `bp-bundle*`, `bp-primary*`, `clock`, `frame-*`, `journal-publish`);
  `tcpcl-session` about 8. Never include `bp-workflow`, `bp-native-app` or
  `owner` from the machine's books.
- Theorems: T1 (both), T2, T3, T5's first two (the branch and the widened
  theorem), T6 except the replay,
  recovery and physical-cut theorems, `fn-bpn-step-fast-is-step`, the
  eligible-selection pairs of §4.2 and §8, the class-service theorem, the
  two journal-debt keystones (§2.1), `fn-bpn-owed-handoff-ends-only-by-its-receipt-carrier`,
  the loop's three correlation keystones (§9.1), the TCPCL final-ACK
  keystone and its sender companion (§9.2). Teeth per §5.0 and §11.1.
- Order: (0) §11.1's A1 witnesses and must-fails, as `must-fail` and
  pending forms, in the teeth books, before any definition changes; (1)
  records and constructors (outcomes, handoffs, correlation, `issued`,
  waits), codec kinds, recovery refusing 2 to 4, the existing theorems
  re-established (regenerate the `-of-constructor` and `-components`
  lemmas in a live session, do not repair them); (2) transitions of §4 and
  the fast step; (3) the theorems; (4) the loop book; (5) the host and the
  round-trip test. Batch (5)'s receive path does not merge before A2's
  replay and recovery theorems certify.
- Traces it must pass: BP-R02 (with A2), BP-R06, BP-R07, BP-R10, BP-R16,
  BP-R17, N03, N04, N05, N08, N11, N12.

**A2: the bundle store (T12b). Opus. local, certifies on hbox by farm. 3 to 4 lane-days.**
- Edits: `books/bp-node-records.lisp`, new `books/bp-node-replay.lisp`,
  new `tests/acl2/bp-node-replay-tests.lisp`, `tools/native_cuts.py` (cuts
  re-targeted at FNBS kinds 5 to 14).
- Include closure: `bp-node-records` about 20 books plus A1's machine.
- Starts when A1's batch (1) merges. Theorems: T6's
  `fn-bpn-durable-projection-is-replay-of-the-confirmed-journal` (one
  epoch), `fn-bpn-recovery-is-normalized-replay-of-an-observed-journal`
  (with its fixed point) and `fn-bpn-physical-cut-is-an-observed-journal`
  (the FNBS publisher relation, including the cut after an uncertainty
  callback), PRF-045 closed over the loop's reserve and recover. 3 to 5
  lane-days.
- Traces: BP-R02 (the recovery half), BP-R14's replay half (a removed route
  does not fault recovery), N06, N07.

**A3: obligations, receipts, the scheduler boundary, K6 (T12d). Opus; Fable for K6 if its soundness pair stalls. persvati. 6 to 7 lane-days.**
- Edits: `books/bp-release.lisp`, `books/bp-release-invariants.lisp`,
  `books/bp-release-store.lisp` and `books/bp-release-owner.lisp` (from
  `w25/bp-obligation-vertical`, §10), new `books/bp-receipt-outbox.lisp`,
  new `books/scheduler-runner.lisp`, `books/bp-workflow.lisp`
  (`fn-bp-receipt-overduep` and its preservation theorem only),
  `books/bp-native-app.lisp` (`fn-bpaj-admission`, `fn-bpaj-ingress-peer`,
  `fn-bpaj-session-principal`), `books/assumptions.lisp` (A-BP-PATH only), new
  `books/bp-native-app-invariants.lisp`, `host/native/bp-app.lisp`,
  `host/native/bp-obligation.lisp`, `host/bp-release-owner-host.lisp`,
  `host/native/workflow.lisp`, `host/workflow-host.lisp`, their tests.
- Include closure: `bp-native-app` about 98 books (it includes `owner` and
  `config`); `bp-release` about 24; `scheduler` about 20.
- Gated on T1's BP-receiver cluster being green for the `bp-native-app`
  edit; the outbox, runner and release parts start earlier.
- Theorems: §6's two soundness theorems and §2.3's two session-principal
  keystones, `fn-bprx-handoff-adu-is-the-committed-receipt`, T5's last two
  (`fn-bpn-transport-observation-cannot-close-a-work`,
  `fn-bp-transport-observation-preserves-receipt-overdue`),
  `fn-bp-retry-request-adu-is-unchanged` (attempt n+1's request ADU equals
  attempt n's), §8's three runner theorems, PRF-012's discharge over the
  release join's caller. Depends on D-15's Store contract from T4 for
  integration, not for development.
- Traces: BP-R01, BP-R03, BP-R04, BP-R05, BP-R19, N01, N02 (workflow level,
  a synthesized delivery observation), N13, N14 (with the slice gate),
  N15.

### Slice B: relay, lost observations, persistent sessions (T12c). Fable. hbox. 5 to 7 lane-days.

- First batch, before the gate: D1b (below) on the machine books.
- Edits: `books/bp-service-loop.lisp` (A1's book extended to the full
  reducer of §9.1: contacts, per-class shares, the §8.1 monitors), new
  `books/bp-routes.lisp`, `books/assumptions.lisp` (A-BP-CONTACT, -PERSIST,
  -PEER, -OWNER, -CLOCK, -JOURNAL, -RETURN), `books/scheduler-peers.lisp` only if
  the native call needs an accessor, `host/native/bp-service.lisp`,
  `tests/test_bp_service_native.py`, new `tests/bp-gate/` harness.
- Include closure: the loop includes the machine and `scheduler-peers`
  (about 27, with `bp-workflow`); `bp-routes` includes `peer-config`
  (about 15, with `config`).
- Theorems: `fn-bps-run-preserves-the-loop-and-lifecycle-invariants` (no
  environmental hypothesis), §5.7's five progress lemmas and the
  work-level composition; `bp-routes`' two keystones; reroute (kind 13)
  preservation.
- Gate: three processes on one box, home, relay, destination, with
  nonoverlapping contacts (home to relay, then relay to destination). (i)
  The home discards its first carrier after forwarding it to the relay;
  the relay expires it before the destination contact; the relay, with
  reports explicitly enabled, sends a deletion report; home interprets it
  through the correlation index; home retries by policy; one article and one pin at
  the destination; the receipt returns across the relay to home and the
  forwarding pin is released. (ii) The same run with reports disabled at the
  relay and every report dropped by the harness: home retries by §9.6's
  policy and reaches the same end state. (iii) The v0.3 rows: an interrupted
  contact (`kill -9` of the relay inside a transfer), an expiry, staging
  exhaustion (relay at `max-held` refuses `No Resources`, the sender's entry
  stays forward-pending and is accepted after a discard). Counts from the
  journals and the owner Store, reason codes from the machine, never from
  logs; record `planning/evidence/bp-gate-<rev>-2026-09-xx.md`.
- Traces: BP-R08, BP-R09, BP-R14 (the live reroute half), BP-R15, BP-R20,
  BP-R24, N02 (end to end, a delivery report present and the receipt
  dropped), N18.

### Slice C: fragment transformations and their executable correspondence

**C1: lemmas and the fast refinement. Opus. any free lane, local closure (about 8 books). 3 to 4 lane-days.**
- Edits: `books/bp-fragment.lisp` (the length bound), new
  `books/bp-limits.lisp` (`fn-bpn-limits-compose`, in the same batch as the
  raise), `books/bp-fragment-invariants.lisp` (the two commented lemmas),
  new `books/bp-fragment-fast.lisp`, `tests/acl2/bp-fragment-tests.lisp`.
- Theorems: T4's first five (inverse, the two fast equalities, whole-parent
  restoration, re-fragmentation), `fn-bpn-plan-child-image-bounded` (§7.3)
  and `fn-bpn-limits-compose`; the fix of D20 (a composing
  `fn-bpn-refragment-primaries` beside `fn-bpf-fragment-block`). Traces:
  N09 (the contract half). No machine book is
  edited; `bp-limits` only includes the codec, so C1 runs beside A1, and
  if A1 changes `*fn-bpn-lifecycle-max-payload*` it re-certifies
  `bp-limits` in its closure. The reference is never connected to the
  native path.

**C2: family transformations in the machine. Fable. hbox, after B. 4 to 5 lane-days.**
- Edits: A1's four machine books (kinds 15 to 18, the plan, the
  replacement), `books/bp-node-replay.lisp` (the four replay cases),
  the teeth book, `tests/test_bp_service_native.py`.
- Theorems: T4's last two (coherent reassembly, replacement), T2's
  local-deletion enumeration over fragments, `fn-bpn-family-conservedp`
  preserved, the debt and reservation inequalities across kinds 15 to 18,
  T6 extended by the four kinds.
- Traces: BP-R11, BP-R12, BP-R13, N09 (the machine half), N10, BP-R22 (measured on the native image:
  payload size and held-set size scaled independently, allocations, time,
  latency, for success, gap, overlap, conflict).

### Slice D: reports and independent wire evidence

**D1a: the report codec. Sonnet. local, phase 3. 1 to 2 lane-days.** New
`books/bp-status-report.lisp` and its tests: §7.6's grammar, decoder,
round trip, canonical-input keystone, reason table, timed assertions.
Concrete conformance facts per §4.6 (the codec's exact bytes, not only its
inverse laws).

**D1b: minimal deletion-report generation and consumption. Opus. landed by
slice B's lane as its first batch (phase 4, when A1's machine books are
free). 1 lane-day.** The deletion assertion at the `:expire` class and at
`start-one`'s deletions (§4.2, §4.3) behind `fn-bpn-policy-reports`, and
§4.1 step 5's consumption through the correlation index, with the teeth of
§11.1's T5 row. This is what slice B's report-present gate (i) needs; the
first revision had B's gate depend on generation that D2 scheduled after
it (review-2 §10).

**D2: generation, demultiplexing, vectors. Opus. hbox, after C2. 2 to 3 lane-days.**
- Edits: the machine books (the three remaining generation points, policy default nil, the
  administrative element for received and locally authored reports, the
  unsupported-block cases of §4.1 step 3 beyond the v0 profile's tests),
  new `tests/bp-vectors/` with independent CRC-bearing bundles (CRC-16 and
  CRC-32C, with RFC 9171 erratum 8043's zeroing of the CRC value bytes, not
  the byte-string header) and timed-status reports produced by dtn7-rs and
  a second implementation, each vector with its producer and version.
- Scope rule: each conformance claim names its profile and its peer/feature
  row. RFC 9171 errata 8376 and 8377 are held for document update and are
  not treated as normative; no general fragmentation/BPSec composition
  claim; the dtn-scheme gate is not evidence for RFC 9758 `ipn` encodings;
  TCPCL erratum 8770 is reported, not adopted.
- Traces: BP-R18, BP-R23.

### Slice E: exhaustion, rotation and the operating envelope. Opus. persvati. 4 to 6 lane-days, after B and C2.

- Edits: `books/bp-service-loop.lisp` (throttling terms, the quiesce
  protocol), the machine books (kinds 19 and 20, `:quiesce`,
  `:generation-selected`), `books/bp-node-replay.lisp` (the checkpoint
  replay case), new `books/bp-node-rotation.lisp`, `tools/native_cuts.py`
  (rotation's cuts), `tests/test_bp_service_native.py`,
  `docs/operator.md`'s BP section.
- Theorems: §3.6's six obligations.
- Work: exhaust the journal separately from saturating 64 live slots;
  admission near the last record; repeated `No Resources` with no clock
  progress; cleanup and control traffic under pressure, with the debt
  cover measured (N05 at scale); rotation at every cut of §3.6's table;
  the documented envelope (records per generation, lifecycles per
  generation at the measured mix, rotation's duration and checkpoint size
  at `max-held`). Broad deployment claims wait on this record.
- Traces: BP-R21 (and BP-R24 re-run at the limit), N05 (measured), N16.

### Trace assignment

| Trace | Slice | | Trace | Slice | | Trace | Slice |
| --- | --- | --- | --- | --- | --- | --- | --- |
| BP-R01 | A3 | | BP-R09 | B | | BP-R17 | A1 |
| BP-R02 | A1, A2 | | BP-R10 | A1 | | BP-R18 | D2 |
| BP-R03 | A3 | | BP-R11 | C2 | | BP-R19 | A3 |
| BP-R04 | A3 | | BP-R12 | C2 | | BP-R20 | B |
| BP-R05 | A3 | | BP-R13 | C2 | | BP-R21 | E |
| BP-R06 | A1 | | BP-R14 | A2, B | | BP-R22 | C2 |
| BP-R07 | A1 | | BP-R15 | B | | BP-R23 | D2 |
| BP-R08 | B | | BP-R16 | A1 | | BP-R24 | B |

The second review's traces (their labels; not requirement IDs):

| Trace | What it checks | Slice |
| --- | --- | --- |
| N01 | receipt carrier stored, discarded, correlation evicted, recovered: the old handed-off receipt is not owed again | A3 (on A1's records) |
| N02 | same unresolved work; a delivery report arrives; the receipt is lost: overdue and retry still fire | A3 (workflow level), B (end to end) |
| N03 | old route-less entry plus newer locally deliverable entry: the newer delivers; the old keeps its `(:route rg)` wait | A1 |
| N04 | old infeasible-MRU entry plus newer fitting entry: the fitting one is attempted; the old is not discarded | A1 |
| N05 | repeated failed forwarding results near the reserve: every admitted cleanup keeps its credit | A1 (theorem, teeth), E (measured) |
| N06 | publish a canonical file, deliver the uncertainty callback, then kill and recover: the visible record is admitted by the cut model with no fabricated confirmation | A2 |
| N07 | durable attempt, restart with a different boot-domain monotonic origin: the domain gate fences before comparing retained Bundle Age anchors; autonomous cross-boot reanchoring remains open | A2 |
| N08 | unanchored entry with an attempt in flight, restart: attempt cleared | A1 |
| N09 | fragment an already-fragmented parent: offsets compose; the whole-parent theorem does not apply | C1, C2 |
| N10 | nonzero-offset fragment arrives before the offset-zero one: primary and blocks come from the offset-zero fragment | C2 |
| N11 | decodable local administrative bundle that conflicts with a held identity: refusal and kind 14, within T5's widened class | A1 |
| N12 | multi-segment transfer with partial ACKs, then a late END capacity refusal: no successful final END ACK; partial ACKs not read as completion | A1 |
| N13 | identical application request retried in a fresh carrier: same receipt fact, new reply submission, no new article or pin | A3 |
| N14 | two works, receipt for the first only: exactly the first forwarding pin changes; archive pins and the second work remain | A3, slice-A gate |
| N15 | network peer address matches, announced EID does not: no admission under the announced identity | A3 |
| N16 | rotation killed at every publication and selection cut, then new work and a stale completion: one recovery authority, no identifier reuse, arrival order kept | E |
| N17 | an attached codec passes the vectors while a theorem needs the exact encoding: the evidence and the conformance obligation stay distinct | T1 (the §4.6 mini-closure), cited by D2 |
| N18 | the owner answers `:uncertain` repeatedly, never `:busy`: the premise is reported violated, not declared satisfied | B |

### 11.1 The counterexample suite

The witnesses and must-fails this patch introduces, per theorem group, each
an exact check in the sense of §5.0 rule 2 (every retained hypothesis
asserted, the omitted one failing, the conclusion negated). The first
commit of the slice that owns a group writes its rows into the test book
named, as `must-fail`s and as pending positive forms, before any definition
changes; the implementation is then written against them. Mutation
witnesses (a deliberately wrong variant of a function, defined in the test
book, showing a conjunct has teeth) and corrupted-state witnesses live in
their own labelled sections and are never counted as reachable.

| Group | Book (slice) | Positive witnesses | Must-fails and mutation witnesses |
| --- | --- | --- | --- |
| T1 | `bp-node-machine-teeth-tests` (A1) | received whole request for this node dispatched `:deliver` and delivered; a request whose expiry under OBS is `:uncertain` is delivered (the scope of `not :expired`); a whole local bundle of an unsupported ADU class gets kind 7 `(:refused :adu-class)` and no `:deliver` | kind hypothesis dropped: `e` is the event's `:receive-answer`, conclusion false; unsupported-class hypothesis dropped: a request's kind 7 is `(:accepted rid)`, not `(:refused :adu-class)`; invariant-removal tooth open: find a state satisfying the checked dispatcher's weaker recognizer, violating the stronger invariant, and actually emitting the forbidden `:deliver`, or prove the theorem without that hypothesis. A `wire` ≠ encoding state fails the checked recognizer and is not an exact tooth. |
| T2 | same (A1) | expired deliverable bundle deleted `:lifetime-expired`; expired local fragment deleted `:lifetime-expired` (pre-C); delivered entry discarded | `deliverablep` dropped: transit bundle deleted `:hop-limit-exceeded` by `:resume` (asserting invariant, event, membership, kind); kind dropped (first theorem): the kind-7 record of a deliverable entry has no reason; `local-destinationp` dropped: the same transit deletion; kind dropped (discard theorem): kind 10 of a retained entry. Withdrawn: "a delivered entry is discarded, not deleted" |
| T3 | same (A1) | first theorem: anchored entry, wall-less observation past its lifetime, deleted; second theorem: an unanchored, wall-less transit bundle whose expiry is uncertain and whose hop limit causes deletion for a reason other than lifetime expiry; each positive asserts its own full antecedent | reason dropped (first theorem): a `:hop-limit-exceeded` deletion whose expiry under OBS is `:uncertain`; `no-anchors` dropped (second): the anchored wall-less deletion; no-wall dropped (second): an unanchored entry with a confident wall past its lifetime deleted `:lifetime-expired`; boundary: a stale `:persist-result`, a stale `:forward-result`, a malformed event, each changing nothing |
| T4 | `bp-fragment-tests` (C1), teeth book (C2) | 10 bytes cut at 3 and 7 reassemble to themselves; whole parent's three children unfragment to it; fragment parent at offset 100 of 300, payload 100 cut at 40: offsets 100 and 140, total 300; N10: offset-40 fragment arrives before offset-0, primary and extension blocks from offset 0; a complete cover at `max-held` reassembles | whole-parent hypothesis dropped (N09): a fragment parent's child does not unfragment to it; re-fragmentation's fragment-parent hypothesis: the proposed whole-parent negative also violates the retained extent bound, so withdraw it and prove the weakened theorem before removing the hypothesis; fast equality: `(:invalid :bounds)` inputs (total 0, overlap past total) answered identically by both; mutation: a reassembler taking the first-arrived fragment's header fails the offset-zero conjunct on N10's trace; boundary: incoherent headers (same key, different lifetime) are never combined |
| T5 | teeth book (A1); `bp-workflow` tests (A3) | a correlated local deletion report yields only `:transport` and `:observed`, state unchanged; N11 satisfies the widened theorem (refusal and kind 14 only); N02: a work overdue at OBS stays overdue after a delivered observation | branch predicate weakened to `decodes-to-local-administrative-p` (N11): the effects contain a kind-14 `:persist`, refuting the first theorem; `decodes-to-local-administrative-p` dropped (widened theorem): the same octets with the administrative flag clear are stored, a kind 5 outside the class; contrast for the overdue theorem: the receipt event makes overdue false, so the function is not constant |
| T6 queue acceptance | teeth book (A1) | durable branch: submission, destination, ADU id, token and answer all bound; duplicate branch from the outcome | kind dropped: a `:bundle-queue-refused` effect satisfies neither disjunct; a retry with a changed destination is `-refused :submission-conflict`, never accepted |
| T6 replay and recovery | `bp-node-replay-tests` (A2) | one epoch with kinds 5, 6, 8, 9, 11; N06: issued record visible after the uncertainty callback recovers to the cut state; N07 | epoch hypothesis dropped (N07): a trace with a durable kind 8 then `:restart` differs from the replay of its confirmed journal (attempt cleared, anchor reset); observed-journal hypothesis dropped: a journal with a record never issued; mutation: a restart that omits `fn-bpn-clear-inflight` satisfies the two-sided equation and fails the fixed-point conjunct |
| T6 physical publisher relation | `bp-node-replay-tests` (A2) and byte-publisher tests | N06 must construct a nonempty encoded FNBS frame in a byte-store state, establish the FNBS publisher relation, select an admissible byte crash cut, scan the resulting directory, and assert the physical theorem's full antecedent and conclusion; zero new events after recovering a nonempty journal is a separate positive. These remain open until executable and certified. | Select at least two distinct admissible crash cuts. A machine-level issued-record witness alone is not a physical-theorem positive; an externally supplied logical journal is not a byte-store witness. |
| T6 re-anchoring, continuation | teeth book (A1) | N08: an unanchored entry with an attempt recovers with neither; N03's and N04's waiting entries are `blocked-with-wakeup` | `:restart-ready` dropped: a faulting restart (token gap) leaves the attempt; not-fenced dropped: a fenced state's owed entry is neither enabled nor waiting on a named wakeup; pending dropped: likewise while a proposal is pending |
| Journal debt (§2.1) | teeth book (A1) | N05 split: `F = remaining - D - R - control-reserve`. At `F=1`, a kind-8 attempt is refused without durable mutation. At `F=2`, kind 8 and its failed kind 9 both complete and return free credit to zero above the margin. At `remaining = D + R + control-reserve`, a debt-paying discard remains admitted. Each positive asserts its full retained antecedent. These are open until the tests are executable and certified. | debt-paying hypothesis dropped: a kind 5 at that frontier is refused `:capacity`; mutation: the first revision's rule (failed results exempt, no reservation at kind 8) breaks the inequality. The old one-credit attempt is only a mutant counterexample. |
| Selection (§4.2, §8) | teeth book (A1) | N03: older route-less transit entry and newer local request, the request is delivered within four progress events. N04: older valid bundle with a 48 KiB payload and no-fragment flag, whose encoded image is verified below 131,072 octets, exceeds a 32 KiB session MRU; a later valid 8 KiB payload bundle has an encoded image within the MRU and is attempted. Assert both actual encoded lengths and the full eligibility antecedent. These are open until the tests are executable and certified. | mutation: the first revision's least-arrival-regardless selector chooses the route-less entry forever on N03; eligibility dropped: N04's older entry is a candidate and not eligible. The previous 200 KB fixture was outside the held-bundle profile. |
| Handoff and outbox | teeth book (A1); outbox tests (A3) | N01: stored, discarded, correlation evicted by insertions, recovered: no owed handoff; N13: same request in a fresh carrier gives handoff `(rid, trigger2)`, one receipt fact, one article | mutation: the first revision's "owed = no binding" reports N01's receipt owed again; a changed request under the same work id is `:conflict` (`bp-native-app.lisp:228-233`) |
| Loop correlation (§9.1) | `bp-service-loop-tests` (A1) | two outstanding operations; completing the second releases only its effects; a refused-capacity reception returns exactly that disposition | boundary: an unknown op id changes nothing; an op id from an earlier epoch changes nothing |
| TCPCL (§9.2) | `tcpcl-session` tests (A1) | N12: three segments, two partial ACKs, END refused: an XFER_REFUSE, no END ACK, no held final | held-final hypothesis dropped: refusing a transfer with no held final emits no refusal; sender: two partial ACKs and no END are never `:outbound-sent` |
| K6 and principal (§6, §2.3) | `bp-native-app` tests (A3) | `:bind` with the exact accepted record (three-argument match); the channel selects P and the EID is P's: admitted P | N15: P's channel with Q's EID is `:eid-mismatch`; same Message-ID with different content is never `:bind`; announced-EID theorem, admission hypothesis dropped: Q's EID on P's channel does not yield Q |
| Rotation (§3.6) | rotation tests (E) | N16 at each cut-table row: the authority the table names; frontiers after selection exceed those before | mutation: a recovery that falls back to `g` on a damaged selection loses a record acknowledged under `g+1` |
| Codec seam (§4.6) | T1's mini-closure | the production attachment agrees with the concrete codec on the vectors | N17: a permuted codec `(π∘E, D∘π⁻¹)` satisfies the seam's constraints and fails the concrete vector theorem, so no exact-byte fact is derivable from the seam alone |
| Progress (§5.7) | `bp-service-loop` tests (B) | each lemma's trace under its premises | N18: an owner answering `:uncertain` forever; the monitor reports A-BP-OWNER violated, the deliverable lemma's premise is false, and the invariants still hold |

### Registry (root writes it at each landing)

PRF-046's events become T6's preservation pair and the two restated
keystones; a new target "The BP node machine delivers, forwards, expires and
discards only as RFC 9171 §5 says" carries T1 to T3 and T5 with each
hypothesis stack in one sentence; T4 is an event of the fragment target; K6's
soundness pair is an event of PRF-042 or its own target; PRF-038 gains its
`events` key (D13); REP-006 stays `specified` until slice B's gate record.

## 12. Decisions

The twelve questions of the first draft, answered by the review and adopted
(D-1 to D-12), and the dialogue's four, answered by the second review
(D-13 to D-16). Each condition is written into the section named.

- **D-1 One list.** One held-bundle collection and one transition authority;
  bundle, submission, forwarding-attempt and ingress identities are separate
  fields, never one `origin` (§1, §2.3).
- **D-2 Kinds 2 to 4.** Retired, with `(:unsupported-schema k)` at recovery,
  never read as an empty store and never reset; root verifies no deployed
  directory holds them before the slice-A image ships; fixtures kept (§3.5).
- **D-3 Routes.** The existing peer-row family and `:set-peer`; a composing
  writer that preserves unrelated rows; live selection from the current
  configuration; history never consults routes; forward-pending entries are
  rerouted on a route change (§2.5, §3.4, §4.5, §7.5).
- **D-4 Scheduler.** Its policy, reused; its self-supplied `:durable`
  replaced by prepare, publish, complete, with a refinement theorem to the
  macrostep on the durable branch; session management is the loop's (§8).
- **D-5 ACK.** Released after durable BP acceptance and before application
  acceptance, from an explicit disposition; a late capacity refusal is
  XFER_REFUSE, never a success ACK; recovery redrives what follows (§9.2).
- **D-6 Reports.** All four assertions in v0; generation default off (RFC
  9171 §5.1), enabled explicitly in lab and operator configurations; the
  grammar corrected; timed incoming assertions supported; a report is never
  needed for retry (§7.6, §9.6).
- **D-7 Fragmentation.** Kept in v0: proactive fragmentation and reassembly
  as restart-safe, capacity-accounted family transformations over a proved
  fast refinement, landed after the whole-bundle slice (§7, slice C).
- **D-8 One receive record.** Kind 5 is the one authoritative receive record
  on the machine path; the interop verbs and receive-evidence namespace stay
  until their replacement passes its gate (§9.2, §10).
- **D-9 Reassembly limit.** 65538, raised only with `fn-bpn-limits-compose`
  over every limit it composes with (§7.1).
- **D-10 Replay order.** The replay proof follows the schema (A2 after A1's
  batch 1) and co-lands with the receive path whose ACK depends on it (§11).
- **D-11 `:resume`.** Kept, as a bounded, serialized loop action with
  attempt and session correlation (§4.3, §9.1).
- **D-12 Receipts.** Through the machine, as a restartable, idempotent
  FNRJ-to-FNBS outbox, addressed to the original requester and routed, with
  receipt ADUs on their own delivery branch into the release join (§9.3,
  §9.4).

- **D-13 Journal lifetime: rotation with a publication protocol.** A
  narrow, operator-controlled rotation, a small extension of T6 and the
  publication model with a cut table: quiesce, drain, checkpoint a fixed
  logical frontier into a new generation in bounded chunks plus a
  manifest, barrier, publish and barrier the selection, and only then
  retire the old authority. Recovery distinguishes incomplete staging,
  complete-unselected, selected and damaged authority, and never falls
  back past a generation that could have acknowledged operations. Logical
  frontiers are globally monotone; only the physical record count resets.
  Six obligations: exact checkpoint projection, recoverable selection,
  preserved acknowledged history, continuation, non-reuse, affordability
  (§3.6, §2.1, slice E).
- **D-14 BP principal: address-bound under a boundary-naming network-trust
  profile.** `observed channel -> configured peer -> allowed-EID check ->
  admitted principal`; the announced EID is a consistency check only and
  never selects or adds authority; the trust row names listener,
  address, translation and co-resident originators; A-BP-PATH states the
  boundary as a constrained function K6's theorems mention; no origin
  authentication is claimed (§2.3, §6).
- **D-15 Store event order.** T4 owns Store event order, A3 the release
  joins; the dependency is a commutative contract between live completion
  of a release event and recovery of its committed ordered history, with
  the arm's deltas and the archive pin untouched, which T4 proves and A3
  cites (§10, §11).
- **D-16 Receipt retry.** Requester-owned: the receiver never reauthors an
  expired receipt carrier. The retry carries the unchanged application
  request in a new carrier whose bundle identity is the explicit
  trigger of the reply submission `(:receipt rid trigger)`; the handoff
  disposition is an authoritative record that survives eviction of the
  report index (§2.3, §2.4, §9.4, §9.6).

The first revision's four open questions are D-13 to D-16.

### Open, needing ember

Each is a place the second review left to judgement. The contract is
written to the recommendation; an answer otherwise changes the section
named.

1. **The boundary the two-process gate declares** (§2.3, §11 slice-A
   gate). Both processes on one box talk over loopback, and loopback does
   not separate mutually untrusted local processes. Options: declare the
   boundary as "loopback listener; originators: every process on this
   host" and say on the gate record that nothing is claimed about
   co-resident processes; or run each node in its own network namespace
   with a veth pair, so the boundary is the namespace. Recommend: the
   first for the slice-A gate (honest, no new harness machinery), the
   namespace form for slice B's three-process gate if it is cheap there.
2. **How far T9 takes the three roles** (§2.3). Ingress principal, request
   author, receipt issuer. Options: T9 v0 settles the subjects and the
   identity slots (principal to permitted EID and keyset bindings, the
   signed request statement's subject, a receipt issuer authorization)
   and claims only the profiles verified on the image; or T9 also ships
   signed BP receipts in v0. Recommend: the first; the network-trust
   profile stays the gate's admission profile, named as weaker.
3. **Authoritative history at its bound** (§2.4). When `max-outcomes` is
   reached and nothing is retirable, options: refuse new submissions
   `(:capacity :history)`; or compact closed outcomes into a generation
   watermark (a closed-operation summary) at rotation. Recommend: refuse
   in v0 (nothing authoritative is ever evicted), and let rotation's
   checkpoint carry a watermark in v1.
4. **The fast reassembler's domain** (T4). Options: equality with the
   reference over all inputs, `(:invalid :bounds)` included; or equality
   under `fn-bpf-inputsp` with the machine's validation boundary proved
   (`fn-bpn-active-set-satisfies-inputsp`). Recommend: all inputs, so no
   caller's validation is load-bearing; the boundary form only if the
   lane measures `fn-bpf-inputsp` as superlinear and says so.
5. **Fragments from different principals** (§7.2). Options: key the active
   set by `(ADU key . principal)`, so a second peer's fragment can never
   join, or deny, a first peer's request; or combine them and give the
   result a nil principal (the first revision), which K6 refuses. Recommend:
   key by principal (no cross-peer poisoning); the cost is that a request
   split over two paths from two peers never reassembles, which no v0
   topology does.
6. **Send-time image growth** (§7.3). Options: plan children at the
   mutable blocks' worst-case encoded width, proved by
   `fn-bpn-plan-child-image-bounded`; or plan at the current width and
   re-plan when a child outgrows the MRU. Recommend: the worst-case
   envelope (the plan stays immutable; at most a few octets per child),
   with re-fragmentation only for a session MRU smaller than planned.
7. **An owner that stays uncertain** (§5.7). Options: A-BP-OWNER requires a
   definitive response in every window, and indefinite uncertainty is a
   reported violation (N18); or add a bounded-recovery premise under which
   uncertainty resolves within a stated number of windows. Recommend: the
   first for v0; the bounded-recovery premise when the owner's own
   recovery has a proved bound.
8. **Checkpoint representation** (§3.6). Options: kind-19 chunks through
   the ordinary record publisher plus a kind-20 manifest; or immutable
   content-addressed objects referenced by the manifest. Recommend:
   chunks as records, which reuse the publisher, the codec and T6's cut
   facts; objects only if slice E measures the chunk count at `max-held`
   as unaffordable.

### Answered by review 3 (2026-09-23)

gpt-6's third review, `planning/review-2026-09-23-bp-node-machine-3.md`,
answers the eight questions above: every recommendation stands, with four
amendments that the slices carry as contract changes. Q3: a request must not
acquire a receipt-handoff obligation whose metadata was never reserved; the
handoff's metadata reservation is an admission contract apart from cleanup
debt. Q5: the principal partition applies at reception, before the global
duplicate and conflict checks (§4.1 step 4), with wire bundle identity kept
apart from the local admitted-claim identity; the held-entry uniqueness
invariant and the reassembly shortcut respect the same partition. Q6: the
worst-case envelope is quantified over permitted forwarding observations
and every mutable encoding change, and the image is checked again at send
time. Q8: physical usage counts checkpoint chunks and the manifest
(`checkpoint-records + next-token - generation-base`) or names their
separate budget. Its §2 to §4 are fixture and definition changes owned by
slices A1, A2, A3, C1/C2 and E (its §5); the handoff to Codex
(`planning/handoff-to-codex-2026-09-23.md`) briefs them.

## 13. Defects in existing code

Found by the review (D1 to D11), while designing (D12 to D17), and by the
second review or while answering it (D18 to D22). Each names its line and
the slice that closes it.

- **D1** `books/scheduler.lisp:304-309`, `fn-sched-drive-attempt` supplies
  `(fn-bp-storage-complete-event txid 0 :durable)` itself; the scheduler
  can release `:submit` for an FNWF attempt that was never published (F-A).
  Slice A3, §8.
- **D2** `books/bp-node-machine.lisp` has no correlation outside the job;
  the first draft's discard (§4.4 then) removed it with the carrier, so a
  delayed report after discard is uninterpretable, and nothing retries a
  `:forwarded` work without a report (F-B). Slice A1 (binding), B (gate).
- **D3** `host/native/bp-app.lisp:143` and `:182-196`: after the durable
  receipt decision the receipt bundle is authored and parked on the
  connection; a crash between loses the return carrier with no outbox to
  rediscover it (F-C). Slice A3, §9.4.
- **D4** `host/native/tcpcl.lisp:251-267`, `fnn-tcl-act`: the held final
  ACK is flushed on any normal return of the delivery callback (F-D).
  Slice A1, §9.2.
- **D5** `host/native/bp-app.lisp:177-180`: `fnn-bpapp-deliver` returns
  normally on `:busy` and on application refusal, so today the peer gets a
  success ACK for a transfer the receiver deferred. Slice A1/A3, §9.2 and
  §9.3.
- **D6** `books/bp-node-machine.lisp:401-406`, `fn-bpn-enqueue-step`
  rebuilds the bundle from the retry's observation before comparing it to
  the existing job, so a retry under a changed clock is `:enqueue-conflict`
  (F-E). Slice A1, §4.4.
- **D7** `books/bp-node-machine.lisp:642`: `fn-bpn-step` runs
  `fn-bpn-machine-statep`, hence `fn-bpb-bundlep` over every held bundle,
  on every event. Slice A1, §2.7.
- **D8** `books/bp-node-machine.lisp:284`: `fn-bpn-existing-sequence` also
  runs `fn-bpn-machine-statep`, per transmit (F-H's audit). Slice A1, §2.7.
- **D9** `books/bp-node-machine.lisp:372-373`: `fn-bpn-propose` on
  record-budget exhaustion answers the refusal with the state unchanged and
  does not fence, contrary to the first draft's prose (F-M). Slice A1, §2.1.
- **D10** `books/bp-node-machine.lisp:473-475`: `fn-bpn-contact-step`
  ignores a contact event while a proposal is pending; the host does not
  re-issue it (F-N). Slice A1 (minimal loop), B.
- **D11** `host/native/tcpcl.lisp:274`: the XFER_REFUSE reason is logged
  and dropped, so `Completed` is treated as failure and the bundle re-sent.
  Slice A1, §9.5.
- **D12** `books/bp-fragment.lisp:144-153`, `fn-bpf-coversp` takes `len`
  of a fragment's bytes per output position and `fn-bpf-cell-of` reaches the
  byte with `nth`; `fn-bpf-extent` (`:316-321`) cuts with `nth`: quadratic
  list traversal if executed (F-H). Slice C1, §7.4; the reference stays.
- **D13** `planning/proofs.json`: PRF-038 names seven theorems, no
  `events` key, no `proof-events.json` target. Root at slice A's landing.
- **D14** `host/native/bp-service.lisp:317-318`: the contact is the literal
  `t` for every ready peer. Slice B.
- **D15** `host/native/bp-service.lisp:162-167`: the route read by position
  in host code. Slice A1 (`:cl-send` carries the address).
- **D16** `books/bp-node-machine.lisp:582-590` (restart keeps the pre-crash
  anchor across a monotonic reset) and `:414-420` (a job is never removed,
  so 64 jobs of any fate refuse forever). Slice A1, §4.5 and kind 11.
- **D17** `specs/reconfiguration.md:176-178` lists eight delta kinds;
  `books/config.lisp:571-573` has ten. T8's lane or root. And
  `docs/prefixes.md`'s `fn-bpn-` row lacks `bp-node-machine*`,
  `bp-receive-evidence`, and the new `bp-node-replay`, `bp-routes`,
  `bp-status-report`, `bp-service-loop` (`fn-bps-`), `bp-receipt-outbox`
  (`fn-bprx-`), `bp-fragment-fast`, `bp-limits`, `scheduler-runner`. Each slice registers
  its own.

- **D18** `books/bp-node-machine.lisp:494-521`, `fn-bpn-persist-result-step`:
  on `:uncertain` (and on a `:durable` whose record does not apply) it
  clears `pending` and fences, leaving no trace of the issued
  publication, while the file may already be visible in the authoritative
  directory; recovery then meets a record the machine state no longer
  names (review-2 T6 and §6, N06). Slice A1 (`issued`, §2.6), A2 (the
  observed-journal relation over it).
- **D19** `books/bp-fragment.lisp:390-392`, `fn-bpf-fragmentablep` tests only
  the must-not-fragment flag, not that the parent is whole; the first
  revision's restoration theorem used it as if it did (review-2 T4, N09).
  The predicate is correct for RFC 9171 §5.8; the defect is its use as a
  wholeness guard. Slice C1 (the whole-parent hypothesis in T4).
- **D20** `books/bp-fragment.lisp:369-383`, `fn-bpf-fragment-block` keeps a
  fragment parent's flags and overwrites its offset and total with the
  caller's arguments; nothing composes a child's offset with the parent's
  or keeps the parent's total, so re-fragmenting through it with relative
  offsets yields children whose offset and total disagree with the ADU.
  It has no caller today (only `bp-fragment-invariants.lisp:437-453`).
  Slice C1 (`fn-bpn-refragment-primaries`, T4).
- **D21** `books/bp-native-app.lisp:376-406`, `fn-bpaj-dispatch` takes no
  ingress or peer, nor does its twin `fn-bpaj-dispatch-fast`
  (`host/bp-native-app-host.lisp:114`), and `fnn-bpapp-accept-locked`
  (`host/native/bp-app.lisp:74-84`) hands the owner only the bundle's
  source and destination EIDs, which are data: the native join admits a
  request from any session that reaches the listener (review-2 Q2; the
  reviewed lines are `:347-411`). Slice A3 (K6,
  `fn-bpaj-session-principal`).
- **D22** `books/bp-workflow.lisp:65-68` and `:636-644`: `:delivered` and
  `:forwarded` are not retryable, restart leaves a `:delivered` work
  alone, and `fn-bp-request-retry` (`:615`, which would move it) has no
  host caller; a delivery report followed by a lost receipt strands the
  work (review-2 §2.3, N02). Slice A3 (`fn-bp-receipt-overduep` over
  unresolved work, and its native caller).

The first draft's F7 (`host/bp-release-owner-host.lisp:8` calling a function
no book defined) is closed on `dev` by `9dd5e3a2` (§10).

### Finite native A2 receive and recovery join (2026-09-23)

The `bp receive` command opens one `fnn-bps` handle under the shared spool
and FNBS lifecycle locks. The handle owns `fn-bpnf-step`; outbound events
enter it as `(:base event)`. On startup, ACL2's mixed namespace plan separates
legacy contiguous final names and kind-5 epoch/operation names in the same
directory. The host reads bounded exact bytes once, and
`fn-bpnf-recover-auto-event` supplies the recovery event to the actual step.
A fault in either replay leg stops the service before listening.

For one complete inbound TCPCL transfer, the host observes session and
configured admission provenance; `fn-bpnf-receive-wire-event` applies the
existing BP reception policy and constructs `:receive-bundle` only for the
canonical exact wire. The step's `:persist` effect is authorized by
`fn-bpnf-publication-authorize`; ACL2 supplies the kind-5 frame, final name,
and journal publication initial state. The physical result is fed back as
`(:persist-result epoch operation-id result)`. Only its matching durable
completion or exact duplicate yields `(:accepted path-or-nil)` for TCPCL;
refusal and uncertainty remain distinct. An uncertain operation remains
fenced until recovery. The separate operator evidence namespace remains
secondary to FNBS custody.
The read-only `bp-service inspect-received FRAME ADU-OUT` command uses ACL2's
kind-5 frame decoder and ADU projection; a damaged frame yields a refusal
without an output file. It is an evidence tool, not another reception path.

This slice retains complete bundles and does not yet bind application
dispatch, durable receipt handoff, or returned receipt release. Those are A3
composition obligations; a TCPCL transfer ACK proves none of them. The
namespace planner's current ACL2 behavior is certified, while its guard
verification remains open through the inherited lifecycle helper chain.
