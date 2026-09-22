# The BP node processing machine (T12)

Status: the contract the T12 implementation lanes are briefed from. Written
in phase 0 of step T12a of [the trajectory plan](../planning/plan-2026-09-22-trajectory.md)
(§3.1, the T12 paragraph; §3.3), and revised the same day against
[gpt-6's review](../planning/review-2026-09-22-bp-node-machine.md) (F-A to
F-N, integration order A to E, traces BP-R01 to BP-R24). It edits no book,
host file, tool or test. Signatures and line numbers are read from `dev`
`2788d4cb` (2026-09-22) unless a line says otherwise. Nothing here is a
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

Reading order for a lane: §0.4 (findings to sections), your slice in §11,
then the sections it names. §12 is the decision record, not a reading list.

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
| fragmentation and reassembly (reference only), two lemmas commented out | `books/bp-fragment.lisp`, `books/bp-fragment-invariants.lisp` | green |
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

### 0.3 The absences this design closes

1. One held-bundle list with RFC 9171 §5 retention constraints for every
   bundle, whatever its ingress.
2. Reception through the machine, with an explicit disposition and the
   data-carrier ACK released on durable BP acceptance only.
3. Dispatch from a live routing table; history replayed without it.
4. A durable carrier-to-work binding that outlives the carrier.
5. The FNRJ receipt handed to FNBS as a restartable, idempotent outbox, and
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
                              max-history cleanup-reserve)
  :fields ((fn-bpn-policy-reports fn-bpn-report-policyp)      ; nil, or the set of assertions generated; default nil (RFC 9171 §5.1)
           (fn-bpn-policy-previous-node fn-bpn-machine-boolp)
           (fn-bpn-policy-max-held fn-bpn-machine-limitp)     ; live slots, 64
           (fn-bpn-policy-max-octets fn-bpn-machine-limitp)   ; live bytes, 16777216
           (fn-bpn-policy-stage-slots fn-bpn-machine-limitp)  ; transformation slots reserved for open families (§7)
           (fn-bpn-policy-stage-octets fn-bpn-machine-limitp)
           (fn-bpn-policy-max-history fn-bpn-machine-limitp)  ; carrier bindings plus conflict records (§2.4)
           (fn-bpn-policy-cleanup-reserve fn-bpn-machine-limitp)) ; journal tokens held back for terminal records
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)
```

The five budgets are distinct and each is checked by name:

| Budget | Measure | Consumed by | Released by |
| --- | --- | --- | --- |
| live slots | `(len held)` ≤ `max-held` | kind 5; kind 16 (from its reservation) | kind 11; kind 17; kind 18 (net `1 - (len ids)`) |
| live bytes | `fn-bpn-held-octets` ≤ `max-octets` | same | same |
| staged space | slots and octets reserved by open families ≤ `stage-slots`, `stage-octets` | kind 15 | kind 16 (converted to live), kind 17 |
| historical metadata | carrier bindings plus conflict records ≤ `max-history` | kind 5 with a submission, kind 14 | kind 12 |
| journal authority | `*fn-bpn-machine-max-records*` − `next-token` | every record | nothing in v0 (§11, slice E) |

**Admission rule** (`fn-bpn-admissiblep st need`): a transition that adds a
live entry (kind 5 from reception or transmit, kind 15) is refused unless
the remaining journal authority after it is at least `cleanup-reserve` plus
two tokens per live entry (its terminal record and its discard), so every
admitted carrier keeps a path to retirement. Terminal and cleanup records
(kinds 7, 9 to 12, 17, 18) are not subject to the reserve. When the frontier is reached
anyway, `fn-bpn-propose` sets the fence and answers the refusal effect with
`:journal-exhausted` (repair of D9; today it answers with the state
unchanged).

A lifecycle is about five records; 4096 tokens is about 800 simple
lifecycles per journal, fewer with attempts, reports and fragments. That is
the v0 bounded-run limit until slice E states the envelope.

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
  ;; (:receipt receipt-id request-id)      the FNRJ receipt for request bundle request-id (§9.4)
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

**Which carries authority.** Only `principal` does. It is set when the
host's session admission found a configured peer (`fn-cfgp` peer with a
`(:bp eid)` transport row equal to `peer-eid`, at `generation`) **and** the
session satisfied that peer's configured authentication policy; otherwise it
is nil. An announced peer EID is never a principal. The bundle's source and
destination EIDs are data: the destination selects local delivery, the
source (report-to for reports) addresses a receipt or report. The fragment
lineage says which fragments a reassembled ADU came from; its principal is
the common principal of every fragment's ingress, or nil when they differ or
any is nil. Configuration generation says which configuration admitted the
principal; K6 decides against the configuration current at delivery (§6).

### 2.4 Carrier bindings: the work correlation that survives discard

```lisp
(fn-defrecord fn-bpn-carrier
  :tag :fn-bpn-carrier
  :constructor (fn-bpn-make-carrier submission bundle-id sequence adu-id family attempts status)
  :fields ((fn-bpn-carrier-submission fn-bpn-submissionp)
           (fn-bpn-carrier-bundle-id fn-bpn-bundle-idp)
           (fn-bpn-carrier-sequence fn-bpp-timep)       ; the persisted creation sequence (§4.4)
           (fn-bpn-carrier-adu-id fn-bpn-content-idp)   ; content id of the ADU, for submission conflict
           (fn-bpn-carrier-family fn-bpn-maybe-family-idp) ; child ids when proactively fragmented (§7.3)
           (fn-bpn-carrier-attempts fn-bpn-token-listp) ; attempt tokens, most recent first, bounded
           (fn-bpn-carrier-status fn-bpn-carrier-statusp)) ; :held :forwarded :delivered :deleted :discarded
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)
```

The state carries `carriers`, one per submission. A binding is created by
the kind-5 record of a bundle with a submission, updated by kinds 7, 9, 10,
11, 17, and **survives kind 11 (discard)**: discard removes the payload and
the live slot, not the binding. It is removed only by kind 12
`(:carrier-retired token submission)`, proposed when the host reports
`(:work-settled submission)` (the workflow released or abandoned the work,
§9.6) or, under historical-metadata pressure, for the binding of oldest
arrival whose bundle's lifetime has elapsed under a decidable observation.
Losing a binding to that pressure loses only the interpretation of a later
report; the report-free retry policy (§9.6) does not read bindings.

A report or a fragment report names a bundle identity (with fragment offset
and length); `fn-bpn-carrier-of-bundle id st` finds the binding whose bundle
id, or one of whose family children, matches, and the transport observation
is emitted for its submission. This is what makes BP-R08 hold after the home
carrier is physically gone.

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
  :constructor (fn-bpn-make-machine-state config policy held carriers families
                                          sessions routes route-generation
                                          pending fenced next-token)
  :fields ((fn-bpn-machine-state-config fn-bpn-configp)
           (fn-bpn-machine-state-policy fn-bpn-policyp)
           (fn-bpn-machine-state-held fn-bpn-held-listp)
           (fn-bpn-machine-state-carriers fn-bpn-carrier-listp)   ; unique submissions
           (fn-bpn-machine-state-families fn-bpn-family-listp)    ; open family plans (§7), nil until slice C
           (fn-bpn-machine-state-sessions fn-bpn-session-listp)   ; open (peer-eid . session) pairs, volatile
           (fn-bpn-machine-state-routes fn-bpn-route-listp)       ; volatile
           (fn-bpn-machine-state-route-generation fn-bpn-machine-u64p)
           (fn-bpn-machine-state-pending fn-bpn-maybe-pendingp)
           (fn-bpn-machine-state-fenced fn-bpn-machine-boolp)
           (fn-bpn-machine-state-next-token fn-bpn-machine-u64p))
  :recognizer fn-bpn-machine-recordp :recognizer-verify-guards nil
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)
```

`fn-bpn-machine-statep` conjoins the record recognizer, the five budgets,
§2.2's list invariants, carrier/held agreement (a binding with status
`:held` names a live entry and vice versa), and the pending-token equation.
`fn-bpn-machine-invariantp` and `fn-bpn-lifecycle-invariantp` keep their
names; the latter's authorization relation (`fn-bpn-proposal-effectsp`)
binds every proposed record to its exact success, refusal and uncertainty
effects, and for kind 8 binds the exact forwarding image, the peer, the
session and the CL address from the live table (review §2.1: not weakened to
"a typed `:cl-send`").

**Durable and volatile fields.** `fn-bpn-durable-projection st` keeps
config, policy, held (with `(:delivering ...)` markers erased), carriers,
families and next-token; it drops sessions, routes, route-generation,
pending and fenced. `fn-bpn-clear-inflight` erases every attempt and
delivery marker; `fn-bpn-reanchor st obs` is §4.5's re-anchoring. These
three are the vocabulary of T6.

### 2.7 No whole-state revalidation on the served path

`fn-bpn-step` evaluates `fn-bpn-machine-statep` on entry
(`bp-node-machine.lisp:642`): `fn-bpb-bundlep` over every held bundle on
every event (D7). `fn-bpn-step-fast` is the same dispatcher validating only
the event's operands, and

```lisp
(defthm fn-bpn-step-fast-is-step
  (implies (fn-bpn-lifecycle-invariantp st)
           (equal (fn-bpn-step-fast st event) (fn-bpn-step st event))))
```

is the equation under which every theorem of §5 is about the function
`fnn-bps-step` calls. The audit extends past `fn-bpn-step`:
`fn-bpn-existing-sequence` (`bp-node-machine.lisp:284`) also evaluates
`fn-bpn-machine-statep` (D8) and is replaced by the carrier lookup of §4.4;
slice A lists every `fnn-core` call in `host/native/bp-service.lisp`,
`host/bp-node-machine-host.lisp` and the new loop book whose subject runs a
whole-state recognizer, and each gets a fast twin with its equation or is
removed.

## 3. Events, effects, records

### 3.1 Events

`OBS` below is an `fn-clock-observationp`. Every event that can lead to a
delivery, an attempt or an expiry carries one (F-L).

| Event | Issued by | Notes |
| --- | --- | --- |
| `(:bundle-received octets ingress obs)` | the loop, from the TCPCL callback | answered by exactly one `:receive-answer` (§9.2) |
| `(:transmit submission destination sequence adu obs)` | the loop, for the workflow's `:submit`, an owed receipt (§9.4), or a report | idempotent by submission (§4.4) |
| `(:deliver-result id delivery-token outcome obs)` | the loop, after a `:deliver` ran | `outcome`: `:accepted`, `:duplicate`, `(:refused reason)`, `:busy`, `:uncertain` |
| `(:forward-result attempt-token session outcome obs)` | the loop, from the CL outcome | `outcome`: `:sent`, `(:refused code)` (RFC 9174 Table 6), `:failed`, `:uncertain` |
| `(:session peer-eid session open-p obs)` | the loop, on session establishment and end | replaces `(:contact peer open-p)`; a close clears only that session |
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

Every record is built by its constructor and read by selectors; no book and
no theorem matches a record by list shape. `fn-bpn-rec-kind`,
`fn-bpn-rec-token` are total over `fn-bpn-recordp`; each kind has its field
selectors and a `-of-constructor` theorem.

| Kind | Constructor | Applied as |
| --- | --- | --- |
| 1 | `(:bpn-sequence n)` | unchanged |
| 2-4 | retired | §3.5 |
| 5 | `(fn-bpn-rec-stored token held)` | append `held` (arrival = token, `:dispatch-pending`); create its carrier binding when it has a submission |
| 6 | `(fn-bpn-rec-dispatched token id disposition)` | set `dispatch` to `(token . disposition)`; `disposition`: `:deliver` (keep `:dispatch-pending`); `(:forward next-hop)` (replace by `:forward-pending`, set next hop); `:administrative` (drop `:dispatch-pending`); `:await-fragments` (add `:reassembly-pending`) |
| 7 | `(fn-bpn-rec-delivered token id delivery-token outcome)` | drop `:dispatch-pending`; binding status `:delivered` |
| 8 | `(fn-bpn-rec-attempting token id peer-eid session age)` | attempt `(:forwarding token peer-eid session)`; `age` kept for re-anchoring |
| 9 | `(fn-bpn-rec-forwarded token id attempt-token outcome)` | clear the attempt; on `:sent` or `(:refused 1)` drop `:forward-pending` and set binding `:forwarded`; otherwise keep it |
| 10 | `(fn-bpn-rec-deleted token id reason)` | clear constraints and attempt, set `deleted`; binding `:deleted` |
| 11 | `(fn-bpn-rec-discarded token id)` | remove the live entry; binding `:discarded`, kept |
| 12 | `(fn-bpn-rec-carrier-retired token submission)` | remove the binding |
| 13 | `(fn-bpn-rec-rerouted token id next-hop)` | replace next hop; `nil` returns the entry to `:dispatch-pending` with `dispatch` nil |
| 14 | `(fn-bpn-rec-conflict token id ingress content-id)` | append a conflict entry to history (§4.1) |
| 15 | `(fn-bpn-rec-family-planned token family plan)` | slice C, §7.3 |
| 16 | `(fn-bpn-rec-family-child token family index held)` | slice C, §7.3 |
| 17 | `(fn-bpn-rec-family-retired token family)` | slice C, §7.3 |
| 18 | `(fn-bpn-rec-reassembled token family held fragment-ids)` | slice C, §7.2 |

Slice A's codec defines kinds 5 to 14 and refuses 15 to 18 at recovery as
`(:unsupported-kind k)`; slice C adds them, each with its replay case, so
the replay theorem gains one case per kind rather than being re-proved.
Record payloads are bounded by `*fn-bpn-lifecycle-max-payload*` (134144,
`bp-node-machine-codec.lisp:24`).

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
   with its type, number, flags and data. If an entry or a live binding has
   `id`: equal immutable projections is `:duplicate` (nothing stored; the
   held copy is kept, whatever its mutable blocks); different projections is
   `(:refused :identity-conflict)` and, within the historical budget, a kind
   14 record naming the ingress and the conflicting projection's content id
   (the held entry is never replaced).
5. Administrative record addressed here (`fn-bpp-administrativep` and
   `fn-bpn-local-destinationp`): §7.6's parser; a decodable report yields
   `(:transport submission status)` for the binding it names (§2.4) plus
   `(:receive-answer ingress :observed)`; a malformed or unsupported
   administrative ADU yields `:observed` alone (RFC 9713 §2). Nothing is
   stored.
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

One action per event, chosen in this order; each later branch runs only
when no earlier one applies. This is the only place delivery and dispatch
are started, so expiry is decided before either (F-L).

1. **Expiry.** The entry of least arrival, not deleted, whose
   `(fn-bpn-held-expiry h obs)` is `:expired`: propose kind 10
   `:lifetime-expired`; success effects `(:transport submission :expired)`
   for a work submission and `(:report-due id :deleted :lifetime-expired)`
   when requested and enabled. `:uncertain` selects nothing.
2. **Dispatch.** The entry of least arrival with `:dispatch-pending`, no
   in-flight marker, and `dispatch` nil:
   - local destination, administrative: kind 6 `:administrative`, whatever
     its ingress, including a report this node authored to itself (F-K 5);
     its success effects are §4.1 step 5's observation effects;
   - local destination, fragment: slice C (§7.2); before slice C, kind 10
     `:block-unintelligible` is **not** used; the entry is held with
     `:reassembly-pending` via kind 6 `:await-fragments` and expires
     normally;
   - local destination, whole: kind 6 `:deliver`;
   - otherwise `(fn-bpn-next-hop routes destination)`: kind 6 `(:forward
     p)`; no route: nothing durable, `(:forward-refused id nil
     :no-known-route)`, and the entry waits for `:routes`.
3. **Delivery.** The entry of least arrival whose `dispatch` is `(t6 .
   :deliver)`, still `:dispatch-pending`, with no `(:delivering ...)`
   marker: set the volatile marker `(:delivering t6)` (t6 the kind-6 token)
   and emit `(:deliver id t6 class key payload ingress report-p)`. No record.
4. **Discard.** The entry of least arrival that is not retained: kind 11.
5. Otherwise nothing.

`fn-bpn-deliver-result-step st id delivery-token outcome obs`: a token that
does not match the entry's marker is stale and changes nothing.
`:accepted`, `:duplicate`, `(:refused r)` propose kind 7 (a refusal is a
completed delivery at this layer; what the application decided is FNRJ's).
`:busy` and `:uncertain` clear the marker, propose nothing, and leave
`:dispatch-pending`, so branch 3 redelivers on a later progress action
(BP-R17); the loop's yield rule (§9.1) keeps that from spinning.

### 4.3 Forwarding: `fn-bpn-session-step`, `fn-bpn-resume-step`, `fn-bpn-forward-result-step`

`fn-bpn-start-one st peer session obs`, called by a session open and by
`:resume`, selects the entry of **least arrival** with `:forward-pending`,
next hop `peer`, no attempt, not deleted, not a family parent with an open
plan, and:

1. if `(fn-bpn-held-expiry h obs)` is `:expired`: kind 10
   `:lifetime-expired` (the progress boundary applies here too);
2. if `fn-bpn-hop-exceededp`: kind 10 `:hop-limit-exceeded`;
3. if the forwarding image exceeds the route's transfer MRU: slice C's
   family plan (§7.3); before slice C, `(:forward-refused id peer
   :mru)` and nothing durable;
4. otherwise, subject to journal admission, kind 8 with the session, the
   age estimate, and success effect `(:cl-send cl peer session token id
   image)`, `image = (fn-bpn-forward-image st h obs)` (Previous Node
   replaced under policy, Bundle Age set, Hop Count incremented,
   re-encoded; the held record is unchanged).

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
next hop. `(:session peer s nil obs)` removes only `(peer . s)`; an attempt
on `s` is left for its `:forward-result`, or `:uncertain` from the loop when
the session ended without one.

`(:resume peer session obs)` runs `fn-bpn-start-one` once. It is kept (§12,
D-11) as a bounded action the loop issues, never a recursive retry (§9.1).

### 4.4 Authoring: `fn-bpn-transmit-step`, `fn-bpn-report-step`

`fn-bpn-transmit-step st submission destination sequence adu obs`:

1. **Idempotence reuses the persisted result** (F-E). If a carrier binding
   for `submission` exists: when its `adu-id` is the content id of `adu`
   and the destination agrees, answer `(:bundle-queue-accepted submission
   bundle-id sequence :duplicate)` from the binding, with no record, no
   reauthoring and no comparison against a bundle rebuilt from this
   event's clock; otherwise `(:bundle-queue-refused submission
   :submission-conflict)`. The retry's `sequence` is burned.
2. Budgets and journal admission, else `-refused :capacity`.
3. Propose kind 5 with ingress `(:local)`, the submission, bundle
   `(fn-bpn-send-bundle config destination adu sequence obs)`, wire
   `(fn-bpn-send ...)` (K1, K5 stay `bp-node`'s), anchor `(0 . monotonic)`,
   `:dispatch-pending`. Success effect `(:bundle-queue-accepted submission
   id sequence :durable)`.

`fn-bpn-report-step` is §7.6. The sequence in both is reserved and durable
before the event (PRF-045).

### 4.5 Persistence, routes, settlement, restart

- `fn-bpn-persist-result-step st token outcome obs`: `:durable` applies the
  pending record and releases its success effects; `:refused` clears the
  proposal and releases the refusal effect; `:uncertain` fences and
  releases the uncertainty effect. Nothing is chained.
- `fn-bpn-routes-step st table generation` installs the table (live). Then,
  one record per event: an entry with `:forward-pending`, no attempt, whose
  next hop has no route in `table` is rerouted, kind 13 with the new next
  hop, or nil to return it to `:dispatch-pending`. An entry with an attempt
  in flight is not rerouted until its result. `(:routes-installed n)`
  reports how many candidates remain; the loop re-issues until 0.
- `fn-bpn-work-settled-step st submission`: kind 12 when the binding's
  bundle is not live; otherwise nothing (the binding outlives the carrier,
  never the reverse).
- `fn-bpn-restart-step st records ready obs`: replay by
  `fn-bpn-apply-record` over `fn-bpn-record-applicablep`; a retired or
  unsupported kind or an inapplicable record is `:restart-fault` and fences;
  otherwise the state is `(fn-bpn-reanchor (fn-bpn-clear-inflight
  replayed) obs)`: every attempt cleared, every anchor re-established as
  `(age . (fn-clock-monotonic obs))` with `age` the largest age any durable
  record of the entry carries, or nil. Sessions and routes are empty; the
  loop installs routes after `:restart-ready`, never before.

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
slice C1); §5.7 in `books/bp-service-loop.lisp` (new, slice B); teeth in
`tests/acl2/bp-node-machine-teeth-tests.lisp` (new).

### 5.0 The rule for teeth

1. Each **positive tooth** is a reachable trace from
   `fn-bpn-initial-machine-state` by `fn-bpn-trace`. It first asserts that
   the theorem's complete antecedent holds of the constructor-produced
   record or effect, e.g. `(member-equal (fn-bpn-rec-deleted 7 id
   :lifetime-expired) RECORDS)`, and only then the conclusion. An antecedent
   no reachable trace satisfies is a vacuous theorem and fails review.
2. One `must-fail` per hypothesis that can fail on a reachable state,
   showing the conclusion false without it.
3. A hypothesis that no reachable state can falsify (an invariant) is
   witnessed by a **corrupted-state** `must-fail`, in its own section of the
   test book and labelled so; it is never counted as a reachable witness.
4. A redundant hypothesis is removed, not witnessed.

### T1. Delivery names a validated, whole, non-administrative, unexpired bundle this node holds

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
                  (equal (fn-bpn-deliver-key e) (fn-bpp-adu-key p))
                  (equal (fn-bpn-deliver-payload e) (fn-bpb-payload b))
                  (equal (fn-bpn-deliver-ingress e) (fn-bpn-held-ingress h))))))
```

The administrative conjunct holds whatever the ingress, so a report this
node authored to itself is never delivered (F-K 5). Teeth: a received
whole bundle for this node, dispatched and delivered (positive); an
administrative bundle authored locally to this node is dispatched
`:administrative` and emits no `:deliver`; an entry whose expiry is
`:expired` under the progress event's observation is deleted, not delivered.

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

(defthm fn-bpn-local-fragment-deletion-reasons
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal r RECORDS)
                (equal (fn-bpn-rec-kind r) :deleted)
                (HELD (fn-bpn-rec-id r))
                (fn-bpn-local-destinationp st (HELD (fn-bpn-rec-id r)))
                (fn-bpp-fragmentp (fn-bpp-flags (fn-bpb-bundle-primary
                                                 (fn-bpn-held-bundle (HELD (fn-bpn-rec-id r)))))))
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
(§7.2), so the fragment theorem's list is complete. `:block-unintelligible`
is the conflict disposition of §7.2 and is reachable only from slice C.
Teeth: an expired deliverable bundle is deleted `:lifetime-expired`
(positive); a transit bundle is deleted `:hop-limit-exceeded` by `:resume`
(`local-destinationp` fails); a delivered entry is discarded, not deleted
(`:dispatch-pending` fails); an entry with an attempt is never discarded.

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
(`clock-invariants.lisp:145`) carries over. Teeth: an anchored entry,
wall-less observation past its lifetime, deleted (the age path);
an unanchored entry with a confident wall past its lifetime, deleted.

### T4. Fragmentation and reassembly: inverse, fast equals reference, replacement

```lisp
(defthm fn-bpf-fragment-then-reassemble-is-identity
  (implies (equal (car (fn-bpf-fragment payload boundaries)) :ok)
           (equal (fn-bpf-reassemble (cadr (fn-bpf-fragment payload boundaries)) (len payload))
                  (list :ok payload))))

(defthm fn-bpf-reassemble-fast-is-reassemble
  (implies (fn-bpf-inputsp fs total)
           (equal (fn-bpf-reassemble-fast fs total) (fn-bpf-reassemble fs total))))

(defthm fn-bpf-fragment-fast-is-fragment
  (equal (fn-bpf-fragment-fast payload boundaries) (fn-bpf-fragment payload boundaries)))

(defthm fn-bpn-fragment-primaries-share-the-key-and-unfragment-to-the-parent
  (implies (and (fn-bpp-blockp p) (fn-bpf-fragmentablep p)
                (fn-bpf-boundariesp boundaries 0 total) (natp total))
           (and (fn-bpn-all-equal (fn-bpp-adu-key p)
                                  (fn-bpn-map-adu-key (fn-bpn-fragment-primaries p boundaries total)))
                (equal (fn-bpn-unfragment (car (fn-bpn-fragment-primaries p boundaries total))) p))))

(defthm fn-bpn-reassembled-record-is-a-complete-agreeing-reassembly
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp event)
                (member-equal r RECORDS)
                (equal (fn-bpn-rec-kind r) :reassembled))
           (let* ((ids (fn-bpn-rec-fragment-ids r))
                  (h (fn-bpn-rec-held r))
                  (first (HELD (car ids)))
                  (res (fn-bpf-reassemble (fn-bpn-fragments-of-ids st ids)
                                          (fn-bpp-total-adu-length
                                           (fn-bpb-bundle-primary (fn-bpn-held-bundle first))))))
             (and (equal (fn-bpf-result-tag res) :ok)
                  (equal (fn-bpn-fragment-family-ids st (fn-bpn-rec-family r)) ids)
                  (equal (fn-bpb-payload (fn-bpn-held-bundle h)) (fn-bpf-result-bytes res))
                  (equal (fn-bpb-bundle-primary (fn-bpn-held-bundle h))
                         (fn-bpn-unfragment (fn-bpb-bundle-primary (fn-bpn-held-bundle first))))
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
`bp-fragment-invariants.lisp` (`:427`, `:248`). Teeth: a non-ascending
boundary list is `(:invalid :bounds)`; a gap answers `(:missing lo hi)`; a
conflict answers `(:conflict i)` with the least `i` from both
implementations; a complete cover at `max-held` reassembles (BP-R11).

### T5. A status report is only a transport observation, on either ingress

```lisp
(defthm fn-bpn-received-local-administrative-bundle-yields-only-observations
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp (list :bundle-received octets ingress obs))
                (fn-bpn-decodes-to-local-administrative-p st octets))
           (let ((ans (fn-bpn-step st (list :bundle-received octets ingress obs))))
             (and (fn-bpn-only-transport-and-observed-effects (fn-bpn-answer-effects ans))
                  (not (fn-bpn-effect-kind-memberp :deliver (fn-bpn-answer-effects ans)))
                  (not (fn-bpn-effect-kind-memberp :persist (fn-bpn-answer-effects ans)))
                  (equal (fn-bpn-answer-state ans) st)))))

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

`fn-bp-find-work` is `(work-id xs)` (`bp-workflow.lisp:177`) and
`fn-bp-state-works` (`:311`) is the projection. The third is quantified over
any `other-work`, so no transport event closes any work; it is stated in
the teeth book, which may include `bp-workflow-transport-invariants`, and
follows from `fn-bp-observe-transport-never-moves-status-backward`. Teeth:
the same octets with the administrative flag clear are stored and
dispatched; an administrative bundle for another node is stored and
forwarded; a `:receipt-prepare` event closes the work (the positive
contrast for the third).

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
           (or (let ((c (fn-bpn-find-carrier (fn-bpn-transmit-submission event)
                                             (fn-bpn-machine-state-carriers st))))
                 (and (equal (fn-bpn-event-kind event) :transmit)
                      (equal (fn-bpn-queue-answer-mode e) :duplicate)
                      c
                      (equal (fn-bpn-queue-answer-bundle-id e) (fn-bpn-carrier-bundle-id c))
                      (equal (fn-bpn-queue-answer-sequence e) (fn-bpn-carrier-sequence c))
                      (equal NEXT st)))
               (let* ((pending (fn-bpn-machine-state-pending st))
                      (r (fn-bpn-pending-record pending)))
                 (and (equal (fn-bpn-queue-answer-mode e) :durable)
                      pending
                      (equal (fn-bpn-event-kind event) :persist-result)
                      (equal (fn-bpn-persist-result-outcome event) :durable)
                      (equal (fn-bpn-rec-kind r) :stored)
                      (equal (fn-bpn-held-submission (fn-bpn-rec-held r))
                             (fn-bpn-queue-answer-submission e))
                      (fn-bpn-record-applicablep st r))))))

;; slice A2, books/bp-node-replay.lisp
(defthm fn-bpn-durable-projection-is-replay-of-the-confirmed-journal
  (implies (and (fn-bpn-lifecycle-invariantp base)
                (fn-bpn-machine-event-listp events))
           (equal (fn-bpn-durable-projection (fn-bpn-trace base events))
                  (fn-bpn-durable-projection
                   (fn-bpn-replay-state base (fn-bpn-confirmed-journal base events))))))

(defthm fn-bpn-recovery-is-normalized-replay-of-an-observed-journal
  (implies (and (fn-bpn-lifecycle-invariantp base)
                (fn-bpn-machine-event-listp events)
                (fn-bpn-observed-journal-p journal base events)
                (fn-bpn-sequence-readyp ready)
                (fn-clock-observationp obs))
           (let ((ans (fn-bpn-step (fn-bpn-recovering-state base)
                                   (fn-bpn-restart-event journal ready obs))))
             (and (equal (fn-bpn-effect-kind (car (fn-bpn-answer-effects ans))) :restart-ready)
                  (equal (fn-bpn-normalize (fn-bpn-answer-state ans) obs)
                         (fn-bpn-normalize (fn-bpn-cut-state (fn-bpn-trace base events) journal)
                                           obs))))))

(defthm fn-bpn-restart-reanchors-every-held-bundle
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp (fn-bpn-restart-event records ready obs))
                (equal (fn-bpn-effect-kind
                        (car (fn-bpn-answer-effects (fn-bpn-step st (fn-bpn-restart-event records ready obs)))))
                       :restart-ready)
                (member-equal h (fn-bpn-machine-state-held
                                 (fn-bpn-answer-state (fn-bpn-step st (fn-bpn-restart-event records ready obs)))))
                (consp (fn-bpn-held-anchor h)))
           (and (equal (fn-clock-anchor-monotonic (fn-bpn-held-anchor h)) (fn-clock-monotonic obs))
                (equal (fn-clock-anchor-age (fn-bpn-held-anchor h))
                       (fn-bpn-durable-age-of records (fn-bpn-held-id h)))
                (null (fn-bpn-held-attempt h)))))

(defthm fn-bpn-recovered-owed-work-has-a-continuation
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (null (fn-bpn-machine-state-pending st))
                (not (fn-bpn-machine-state-fenced st))
                (fn-bpn-owedp h st))
           (or (fn-bpn-enabled-action-p h st)
               (fn-bpn-blocked-with-wakeup-p h st))))
```

Definitions the statements rest on, each a function, not a hypothesis
predicate standing in for one:

- `fn-bpn-confirmed-journal base events`: the records whose
  `(:persist-result token :durable obs)` the trace delivered, in token
  order, computed from the trace.
- `fn-bpn-observed-journal-p journal base events`: `journal` is the
  confirmed journal, or the confirmed journal followed by the record pending
  at the end of the trace (the cut after the link and before the process
  observed `:durable`, review §5.2). PRF-045's persistence-cut model is the
  file-level evidence that an observed file is complete or absent.
- `fn-bpn-cut-state live journal`: `live` with its pending record applied
  when `journal` contains it, and its proposal cleared.
- `fn-bpn-normalize st obs` = `(fn-bpn-reanchor (fn-bpn-clear-inflight
  (fn-bpn-durable-projection st)) obs)`; both sides of the recovery theorem
  are normalized, and `fn-bpn-normalize-idempotent` is a lemma.
- `fn-bpn-owedp h st`: `h` retained, or a carrier binding whose bundle is
  live with a constraint, or an open family. `fn-bpn-enabled-action-p`:
  the progress step or `start-one` on some open session would propose a
  record or emit a `:deliver` for it. `fn-bpn-blocked-with-wakeup-p`: it
  waits on one named wakeup: a session to its next hop, a `:routes` event,
  an owner availability after `:busy`, a missing fragment, or a clock
  observation that decides expiry. Review §5.3: a journal can replay
  perfectly and still strand work; this theorem is the one that says it
  does not.

Hypothesis note: `fn-bpn-machine-eventp` on the restart event is redundant
with `fn-bpn-restart-event`'s recognizer in the recovery theorem and is
therefore absent there (rule 4). Teeth: a journal with a token gap is
`(:restart-fault :lifecycle-record)`; a journal holding kind 3 is
`(:restart-fault (:unsupported-schema 3 ...))`; a trace ending immediately
after a durable kind 8 recovers with the attempt cleared on **both** sides
(the case F-K 4 named); a route removed between the trace and the restart
does not fault the recovery (BP-R14); an `:attempting` age larger than the
stored age re-anchors to the larger; the four `must-fail`s of
`bp-node-machine-authorization-tests.lisp` carried over by constructor.

### 5.7 Conditional progress (review §5.5)

Safety is T1 to T6. Progress is stated separately, over the service loop of
§9.1, with its assumptions as constrained functions in
`books/assumptions.lisp` (AGENTS: an assumption is an `encapsulate` with a
local witness, and the theorem mentions it):

```lisp
(defthm fn-bps-owed-carrier-leaves-owed-state-under-its-assumptions
  (implies (and (fn-bps-loop-invariantp loop)
                (fn-bpn-owedp h (fn-bps-loop-machine loop))
                (fn-assume-bp-contact-recurs env (fn-bpn-held-next-hop h) window)   ; A-BP-CONTACT
                (fn-assume-bp-persistence-answers env)                              ; A-BP-PERSIST
                (fn-assume-bp-peer-completes env window)                            ; A-BP-PEER
                (fn-assume-bp-owner-available env window)                           ; A-BP-OWNER
                (fn-assume-bp-journal-headroom loop n)                              ; A-BP-JOURNAL
                (natp n)
                (<= (fn-bps-progress-bound h loop window) n))
           (not (fn-bpn-owedp h (fn-bps-loop-machine (fn-bps-run loop env n))))))
```

The assumptions, one sentence each: A-BP-CONTACT, in every `window` turns
the environment opens a session to the entry's next hop; A-BP-PERSIST,
every publication is answered `:durable` within the turn it is issued (a
refusal or uncertainty ends the premise, it does not fail the theorem);
A-BP-PEER, in every session at least one attempt completes `:sent` or
`(:refused 1)`; A-BP-OWNER, the application join answers something other
than `:busy` at least once in every `window` turns; A-BP-JOURNAL, the
remaining journal authority covers the records of `n` turns.
`fn-bps-progress-bound` is linear in the entry's rank by arrival among
entries to the same next hop times `window`. Excluded, and not made progress
guarantees by any selector: arbitrary outages (A-BP-CONTACT false),
indefinitely uncertain time (then only forwarding progresses, not expiry),
an exhausted journal, and an adversarial peer (A-BP-PEER false). **No
assumption mentions reports**: the theorem holds for an environment that
drops every status report. The work-level statement (a work reaches a
receipt or its retry policy fires, §9.6) is slice B's second theorem, over
the same assumptions plus A-BP-RETURN (a route back to the requester).
`fn-assume-fairness-contact-index` (`assumptions.lisp:291`) is the
scheduler's existing assumption and A-BP-CONTACT is stated so that the
scheduler's contact plan implies it.

## 6. K6: the delivered request's admission is the transit decision

K6 ([peering §1.4](peering.md)): a BP peer is the same profile over another
convergence layer. What the machine hands the application is `(:deliver id
t class key payload ingress report-p)`. The loop routes it by `class`
(§9.3): `:request` to the receiver join, `:receipt` to the sender's
release join. For a request, the join's admission changes in one place:

```lisp
(defun fn-bpaj-ingress-peer (cfg ingress) ...)
  ;; the configured peer record named by ingress's principal at the current
  ;; configuration, or nil: nil for (:local), for a nil principal, for a
  ;; family whose fragments disagree, and for a principal no longer configured
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

The theorems, in `books/bp-native-app-invariants.lisp` (new), soundness
first:

```lisp
(defthm fn-bpaj-submit-is-sound
  (implies (and (fn-bpaj-statep joined) (fn-sn-statep store) (fn-node-statep node) (fn-cfgp cfg)
                (equal (car (fn-bpaj-admission node cfg joined store request-octets ingress clock generation))
                       :submit))
           (let ((peer (fn-bpaj-ingress-peer cfg ingress)))
             (and peer
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
                 (cadr (fn-bpaj-record-lookup store (fn-bpaj-request request-octets)))
                 (fn-bpaj-request request-octets))
                (equal generation (fn-bpaj-request-generation joined request-octets)))))
```

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
whose fragments share a principal is admitted, one whose fragments disagree
is `:no-principal` (both from slice C2); self-delivery; an unconfigured session identity.

`books/bp-native-app` is red at its digest and opens the record codec
book-wide; the K6 edit waits for T1's BP-receiver cluster (slice A3's gate).

## 7. Limits, reassembly, fragmentation, routes, reports

### 7.1 Limits that compose (§12, D-9)

`*fn-bpf-max-length*` (`bp-fragment.lisp:50`, 65536) rises to
`*fn-bpa-max-octets*` (`bp-adu.lisp:24`, 65538) only in the same batch as a
theorem over constants, `fn-bpn-limits-compose`, in `books/bp-limits.lisp`
(new, slice C1; it includes `bp-adu`, `bp-fragment`, `frame-octets` and
`bp-node-machine-codec`), that states every inequality below.
The raise alone establishes nothing about maximum-size ADUs.

| Limit | Value today | Must satisfy |
| --- | --- | --- |
| request and receipt ADU | `*fn-bpa-max-octets*` 65538 | ≤ reassembly length |
| reassembly length | `*fn-bpf-max-length*` 65536 → 65538 | = ADU max |
| bundle image | `*fn-bpn-machine-max-job-octets*` = `*fn-frame-max-blob*` 131072 | ADU max + `*fn-bpn-max-header-octets*` ≤ it |
| record payload | `*fn-bpn-lifecycle-max-payload*` 134144 | bundle image + held-record overhead ≤ it |
| fragment count | `*fn-bpf-max-fragments*` 64 | count × (per-fragment image) ≤ stage-octets; count ≤ stage-slots + 1 |
| TCPCL transfer | the route's transfer MRU and the session's negotiated MRU | a whole image or a fragment image ≤ it (§7.3) |
| aggregate | `max-octets` 16777216 | max-held × bundle image ≤ it, or the byte budget is the binding one and says so |
| execution | fast reassembly and cutting | cost linear in output length plus fragment bytes (§7.4) |

### 7.2 Reassembly as a family replacement (F-F)

A local-destination fragment is dispatched `:await-fragments` (kind 6,
adding `:reassembly-pending`). The progress step's dispatch branch, for a
fragment, computes `fn-bpf-reassemble-fast` over the **active** fragments
with its ADU key: held, not deleted, not already consumed, projected in
arrival order.

- `(:ok bytes)`: propose kind 18 `(fn-bpn-rec-reassembled token family held
  ids)`. Applied atomically: the fragment entries leave the live list (their
  kind-5 records stay in the journal as provenance, their dispatch and
  reassembly obligations are finished by this record), and one entry is
  appended: primary `(fn-bpn-unfragment ...)` of the offset-zero fragment,
  its blocks, payload `bytes`, ingress `(:family family ingresses)`,
  `:dispatch-pending`. Live slots change by `1 - (len ids)`; no sixty-fifth
  slot is ever needed, and T4's replacement theorem says so.
- `(:missing lo hi)`: nothing durable; the entries wait (blocked on a
  missing fragment, T6's `fn-bpn-blocked-with-wakeup-p`).
- `(:conflict i)`: kind 10 `:block-unintelligible` for the later-arriving
  fragment of the conflicting pair; it is deleted, so it is excluded from
  every later active input (BP-R13, "no poisoned input"), and a later valid
  fragment can still complete the cover.
- `(:invalid :bounds)`: kind 10 `:block-unintelligible` for this fragment.

`family` for reassembly is the ADU key. Repeated reassembly after restart is
impossible by construction: kind 18 removed the inputs.

### 7.3 Proactive fragmentation as a durable family plan (F-G)

When `start-one`'s selected entry's forwarding image exceeds the next hop's
transfer MRU and the bundle is fragmentable:

1. `fn-bpn-fragment-plan st h mru obs` computes boundaries such that every
   child's **actual encoded forwarding image**, after its mutable blocks are
   set and with the encoding-length changes they cause, is ≤ `mru`; it
   checks each image, not an overhead constant. If no plan exists (an MRU
   below the minimum feasible image, or more than `*fn-bpf-max-fragments*`
   children), the answer is `(:forward-refused id peer :mru-infeasible)` and
   nothing durable.
2. Propose kind 15 `(fn-bpn-rec-family-planned token family plan)`, `plan`
   binding parent id, child ids, boundaries, total ADU length, the parent's
   submission lineage, and the completion policy (the work is `:forwarded`
   when every child is forwarded). It reserves staged slots and octets for
   every child; admission fails without them.
3. For each child in order, kind 16 `(fn-bpn-rec-family-child token family
   index held)`: the child entry, `:forward-pending`, the parent's next hop,
   lineage `(:family family index)`. Child creation is the progress step's
   owed work while the plan is open; a restart with a proper prefix of
   children resumes at the next index.
4. After the last child, kind 17 `(fn-bpn-rec-family-retired token family)`
   removes the parent and releases the plan's reservation. The parent is
   never retired before every child is durable (BP-R12).

Children are forwarded by the ordinary `start-one`. A forwarded child is not
evidence that its siblings were forwarded: the carrier binding records per
child and becomes `:forwarded` only when all are. A duplicate local
submission names the parent's binding, whose `family` lists the children.
No host-side fragmentation controller exists.

### 7.4 The executable refinement (F-H)

`books/bp-fragment.lisp` stays the reference (its header says so).
`books/bp-fragment-fast.lisp` (new, slice C1) defines
`fn-bpf-fragment-fast` (a cursor over the payload, no repeated `nth`) and
`fn-bpf-reassemble-fast` (one pass building the output by offset over
fragments sorted by offset, tracking the least gap and least conflict
position), with T4's two equalities, including the four outcomes, conflict
precedence and the least conflict/gap positions. The machine calls only the
fast functions. Slice C measures (BP-R22) payload size and held-set size
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
`fn-bpa-decode-exact`; `fn-bpn-report-round-trip` and
`fn-bpn-report-accepted-input-is-canonical` are its keystones, and the
reason table is Table 1 codes 0 to 11.

Generation. `fn-bpn-policy-reports` defaults to nil in every image and every
configuration (RFC 9171 §5.1: disabled by default); the lab and operator
configurations enable it explicitly, with the historical and journal
budgets of §2.1 applying to report bundles like any other. When enabled and
requested, generation at each of the four points is a SHOULD of RFC 9171
and fn generates: reception (§4.1), forwarding (§4.3), delivery (§4.2),
deletion (§4.2, §4.3). `:report-due` makes the loop reserve a sequence and
issue `:author-report`, which `fn-bpn-report-step` turns into a transmit
with submission `(:report subject assertion)`, so a report is a held entry
dispatched like any other and is idempotent by submission. A crash between
`:report-due` and `:author-report` loses the report: reports are never
evidence and never necessary for retry (§9.6). A report never requests
reports.

Consumption. §4.1 step 5 for received ones and §4.2's `:administrative`
dispatch for locally authored ones; both use `fn-bpn-carrier-of-bundle` to
find the submission, including fragment subjects.

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
session in arrival order until it is sent, expires or is deleted (RFC 9171
§5.4); `fn-bpn-start-one-selects-the-least-arrival` is its FIFO theorem,
over the immutable `arrival` field (F-M). A bundle's lifetime is not a bound
on retries: nonprogress is bounded by the loop's yield rule (§9.1) and by
journal admission (§2.1).

A requeued bundle leaves the work `:attempted`, which is not retryable
(`fn-bp-retryable-statusp`, `bp-workflow.lisp:65`), so the workflow does
not make a second bundle while the first is carried; the receipt-loss
policy (§9.6) is what moves a stalled work on.

`tools/scheduler.py` retires when slice B's native call lands.

## 9. What the host does

### 9.1 The serialized service loop (F-N)

`books/bp-service-loop.lisp` (new, slice B; slice A lands a minimal version
with the same interface) defines the reducer the host runs; the host does
I/O and nothing else.

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
- After `:restart-ready`, the loop issues `:routes`, then sessions, then
  `:clock`.

`fnn-bps-step` (`bp-service.lisp:110-116`) stays the one call into the
machine; `fnn-bps-drive-effects` (`:207`) is replaced by the loop's
operation executor. The current `fn-bpn-contact-step` drops events while a
proposal is pending (`bp-node-machine.lisp:473-475`, D10); the inbox is its
repair.

### 9.2 Reception and the ACK (F-D, §12 D-5)

- `*fnn-tcl-deliver*` is bound to a callback that submits
  `(:bundle-received octets ingress obs)` to the loop and **returns the
  disposition** from the matching `(:receive-answer ingress disposition)`.
- `fnn-tcl-act`'s `:bundle-received` arm (`tcpcl.lisp:251-267`) maps the
  disposition, not the fact of a normal return: `:stored`, `:duplicate`
  and `:observed` flush the held final XFER_ACK; `(:refused :capacity)` and
  `(:refused :busy)` replace it with XFER_REFUSE `No Resources`
  (`*fn-tcl-refuse-no-resources*`), any other refusal with `Not
  Acceptable`; `(:uncertain ...)` drops it (`fnn-tcl-drop`) and the session
  fails, as today. The replacement is a TCPCL session-machine transition
  `fn-tcl-refuse-held-final` (new, in `books/tcpcl-session.lisp`, RFC 9174
  §5.2.4), whose keystone is that the session emits no XFER_ACK for a
  transfer it refused. A late capacity refusal is never a success ACK
  (BP-R10).
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
  Its result is the `:deliver-result`: `:accepted`, `:duplicate`,
  `(:refused r)`, `:busy` (the join's `:blocked`, `bp-native-app.lisp:405`,
  and `:defer`), `:uncertain` (the owner fenced). The Store commit and the
  FNRJ receipt decision are the join's durable writes, unchanged.
- `:receipt`: the sender's receipt consumption: the workflow's receipt
  event, `fn-bprl-release-decision`, the release record, and
  `fn-retain-release` on the owner Store's forwarding pin, with the
  independent archive pin untouched (review §5.4). This path is slice A3's
  and runs against the native owner's Store, not a shadow workflow image.
  The request join is never the receipt path.
- When `report-p`, the loop issues `:author-report` after kind 7 is
  durable.

### 9.4 The receipt outbox: FNRJ to FNBS (F-C, §12 D-12)

A committed FNRJ receipt is owed output until FNBS holds a kind-5 record
for its submission `(:receipt receipt-id request-id)`.

- `books/bp-receipt-outbox.lisp` (new, slice A3, `fn-bprx-*`):
  `fn-bprx-owed-receipts fnrj carriers` is the committed receipts whose
  submission has no carrier binding; its keystone
  `fn-bprx-committed-receipt-is-owed-until-stored` says a committed receipt
  is in the list exactly when no binding for its submission exists.
- After every receipt decision and at every recovery, the loop issues
  `(:transmit (:receipt rid req) source-eid sequence adu obs)` for each owed
  receipt, addressed to the request bundle's source EID and routed (§6).
  `:transmit`'s idempotence (§4.4) makes redrive safe: a second transmit of
  the same submission answers `:duplicate` from the binding.
- The receipt carrier's own fate: if it expires or is deleted, the receipt
  is not reauthored by the receiver. The requester's retry (§9.6) sends a
  new request bundle; the join answers `:return-receipt` from the committed
  receipt (`bp-native-app.lisp:404`), and the new request id makes a new
  submission, hence a new receipt carrier. A receipt fact is never lost;
  a receipt carrier may be.
- `fnn-bpapp-pause-after-decision` (`bp-app.lisp:143`) stays as a test cut
  and gains its siblings: after Store commit, after receipt decision, after
  FNBS enqueue, after local completion, after the receipt carrier is
  discarded (BP-R03 to BP-R05).

### 9.5 Forwarding and sessions

- The loop opens one outbound session per peer when the scheduler's contact
  starts (until slice B, when a transmit makes an entry forward-pending to
  a configured route), keeps it for the contact, and issues `(:session peer
  s t obs)`; a passive session from a configured peer opens `(peer . s')`
  for its duration.
- `:cl-send` offers `image` on session `s` (`fnn-tclc-pending`), and the
  outcome `:outbound-sent`, `:outbound-refused` with its Table 6 code (the
  code reaches the machine; today it is logged at `tcpcl.lisp:274` and
  dropped, D11), or `:outbound-failed` answers `:forward-result` with the
  attempt token and session the effect carried. A session that ends with an
  offer outstanding answers `:uncertain`.
- After each result, while `s` is established, the loop issues `(:resume
  peer s obs)` subject to the yield rule.

### 9.6 The receipt-loss retry policy (F-B)

Reports are optional; retry is not. A work whose attempt is `:forwarded`,
`:attempted` or `:bundle-created` and has had no receipt for `receipt-wait`
(a term of the work's policy, decided by `fn-bp-receipt-overduep work obs
policy`, new in `books/bp-workflow.lisp`, slice A3) is moved by
`fn-bp-request-retry` (`bp-workflow.lisp:615`) to `:unknown`, which is
retryable (`:65-68`); the scheduler then prepares a new attempt with a new
attempt id, so the new bundle has a new submission identity. The loop
evaluates the predicate on its timer; no report is read. A delayed report
that arrives later is interpreted through the carrier binding (§2.4) and
can only advance the work's transport status, never close it (T5). BP-R09
is this policy with every report dropped.

### 9.7 Authoring, clock, routes, restart

- `:transmit` for a work: the loop reserves the sequence first (PRF-045);
  a retry of the same submission gets `:duplicate` from the binding and its
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
| `w25/bp-obligation-vertical` (13 ahead) | since `9dd5e3a2` (merged `2788d4cb`, persvati `certify-20260922T184059Z-2797731`): `fn-bprl-release-record`, `fn-bprl-replay-records`, `fn-bprl-replay-journal` in `books/bp-release.lisp`, landed verbatim from `faf16519` because `host/bp-release-owner-host.lisp` calls the last and `host/native/build.lisp` loads that file | **slice A3 takes** `books/bp-release-store.lisp` (`fn-bprl-store-join` and its three theorems, from `faf16519`), `books/bp-release-owner.lisp` (`fn-bprl-owner-join` and three, `4c42ef73`), `host/native/bp-obligation.lisp` and the `host/bp-release-owner-host.lisp` additions (`4c42ef73`, `e13d9007`, `e342c187`), the `host/native/workflow.lisp` and `host/workflow-host.lisp` changes of `faf16519` and `4c42ef73`, and the tests `tests/test_bp_obligation_native.py`, the `test_bp_app_native.py` and `test_bp_service_native.py` additions, `9e21db92`'s `test_native_app_journal.py` cases; each re-derived against the machine of slice A, not merged. **Not A3's**: the Store event-order commits `d9816877 c6270e3e 2f9f36d7 38f337ab 9d5df71d e16f54b0 adf63066 4c7cbfe1` and the `store-node*`/`store-files` parts of `e342c187` edit `store-node`, `store-files`, `replay`, `store-events`, `node-retention-transitions`, which are T2/T4's books; they are an input to T4's brief (§12, open question 3). `faf16519`'s `frame-journal`/`frame` edits are re-derived by A3 against T1's frame seam. The branch is deleted after A3's landing note names what it took |

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
continued, A3 (persvati 2 once T1's BP-receiver cluster is green), D1
(local); phase 4: B (hbox 2); phase 5: C2 then D2 (hbox 2), E (persvati 2).

Sizes sum to 32 to 44 lane-days against the plan's 20 to 31 for T12a to
T12d; the difference is the receipt outbox, the carrier bindings, the loop,
the fast fragment refinement and the operating envelope the review added.

### Slice A: correct contracts and the two-process article-and-receipt round trip

Gate for the slice, run by A1 after A2 and A3 have merged: two native
processes on one box exchange one ordinary article and its return
application receipt through FNBS; at the destination exactly one accepted
article and one archive pin in the **owner Store**; at the home, the
forwarding pin released by `fn-retain-release` through the release join and
the archive pin kept; each crash cut of BP-R02 to BP-R05 taken by `kill -9`
at a named cut and recovered, with the same Store and pin counts. Store and
pins read through the owner, never from workflow or log projections.

**A1: the machine (T12a). Fable. hbox. 7 to 9 lane-days.**
- Edits: `books/bp-node-machine.lisp`, `-invariants`, `-authorization`,
  `-codec` (kinds 5 to 14, retired 2 to 4), `books/tcpcl-session.lisp` (`fn-tcl-refuse-held-final`),
  `tests/acl2/bp-node-machine-tests.lisp`, `-authorization-tests.lisp`, new
  `tests/acl2/bp-node-machine-teeth-tests.lisp`, `host/bp-node-machine-host.lisp`,
  `host/native/bp-service.lisp` (the minimal loop, sessions from the one
  configured route), `host/native/tcpcl.lisp` (disposition mapping),
  new `tests/test_bp_roundtrip_native.py`, `docs/prefixes.md`.
- Include closure: `bp-node-machine-codec` is about 65 books (`bp-node`,
  `bp-bundle*`, `bp-primary*`, `clock`, `frame-*`, `journal-publish`);
  `tcpcl-session` about 8. Never include `bp-workflow`, `bp-native-app` or
  `owner` from the machine's books.
- Theorems: T1, T2, T3, T5's first two, T6 except the two replay theorems,
  `fn-bpn-step-fast-is-step`, `fn-bpn-start-one-selects-the-least-arrival`,
  the TCPCL refusal keystone. Teeth per §5.0.
- Order: (1) records and constructors, codec kinds, recovery refusing 2 to
  4, the existing theorems re-established (regenerate the `-of-constructor`
  and `-components` lemmas in a live session, do not repair them); (2)
  transitions of §4 and the fast step; (3) the theorems; (4) the host and
  the round-trip test. Batch (4)'s receive path does not merge before A2's
  two replay theorems certify.
- Traces it must pass: BP-R02 (with A2), BP-R06, BP-R07, BP-R10, BP-R16,
  BP-R17.

**A2: the bundle store (T12b). Opus. local, certifies on hbox by farm. 3 to 4 lane-days.**
- Edits: `books/bp-node-records.lisp`, new `books/bp-node-replay.lisp`,
  new `tests/acl2/bp-node-replay-tests.lisp`, `tools/native_cuts.py` (cuts
  re-targeted at FNBS kinds 5 to 14).
- Include closure: `bp-node-records` about 20 books plus A1's machine.
- Starts when A1's batch (1) merges. Theorems: T6's
  `fn-bpn-durable-projection-is-replay-of-the-confirmed-journal` and
  `fn-bpn-recovery-is-normalized-replay-of-an-observed-journal`, PRF-045
  closed over the loop's reserve and recover.
- Traces: BP-R02 (the recovery half), BP-R14's replay half (a removed route
  does not fault recovery).

**A3: obligations, receipts, the scheduler boundary, K6 (T12d). Opus; Fable for K6 if its soundness pair stalls. persvati. 5 to 6 lane-days.**
- Edits: `books/bp-release.lisp`, `books/bp-release-invariants.lisp`,
  `books/bp-release-store.lisp` and `books/bp-release-owner.lisp` (from
  `w25/bp-obligation-vertical`, §10), new `books/bp-receipt-outbox.lisp`,
  new `books/scheduler-runner.lisp`, `books/bp-workflow.lisp`
  (`fn-bp-receipt-overduep` only), `books/bp-native-app.lisp`
  (`fn-bpaj-admission`, `fn-bpaj-ingress-peer`), new
  `books/bp-native-app-invariants.lisp`, `host/native/bp-app.lisp`,
  `host/native/bp-obligation.lisp`, `host/bp-release-owner-host.lisp`,
  `host/native/workflow.lisp`, `host/workflow-host.lisp`, their tests.
- Include closure: `bp-native-app` about 98 books (it includes `owner` and
  `config`); `bp-release` about 24; `scheduler` about 20.
- Gated on T1's BP-receiver cluster being green for the `bp-native-app`
  edit; the outbox, runner and release parts start earlier.
- Theorems: §6's two soundness theorems, `fn-bprx-committed-receipt-is-owed-until-stored`,
  §8's three runner theorems, PRF-012's discharge over the release join's
  caller.
- Traces: BP-R01, BP-R03, BP-R04, BP-R05, BP-R19.

### Slice B: relay, lost observations, persistent sessions (T12c). Fable. hbox. 5 to 7 lane-days.

- Edits: new `books/bp-service-loop.lisp` (the full reducer of §9.1), new
  `books/bp-routes.lisp`, `books/assumptions.lisp` (A-BP-CONTACT, -PERSIST,
  -PEER, -OWNER, -JOURNAL, -RETURN), `books/scheduler-peers.lisp` only if
  the native call needs an accessor, `host/native/bp-service.lisp`,
  `tests/test_bp_service_native.py`, new `tests/bp-gate/` harness.
- Include closure: the loop includes the machine and `scheduler-peers`
  (about 27, with `bp-workflow`); `bp-routes` includes `peer-config`
  (about 15, with `config`).
- Theorems: §5.7's carrier progress and its work-level companion; the loop
  invariant; `bp-routes`' two keystones; reroute (kind 13) preservation.
- Gate: three processes on one box, home, relay, destination, with
  nonoverlapping contacts (home to relay, then relay to destination). (i)
  The home discards its first carrier after forwarding it to the relay;
  the relay expires it before the destination contact; the relay, with
  reports explicitly enabled, sends a deletion report; home interprets it
  through the binding; home retries by policy; one article and one pin at
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
  BP-R24.

### Slice C: fragment transformations and their executable correspondence

**C1: lemmas and the fast refinement. Opus. any free lane, local closure (about 8 books). 2 to 3 lane-days.**
- Edits: `books/bp-fragment.lisp` (the length bound), new
  `books/bp-limits.lisp` (`fn-bpn-limits-compose`, in the same batch as the
  raise), `books/bp-fragment-invariants.lisp` (the two commented lemmas),
  new `books/bp-fragment-fast.lisp`, `tests/acl2/bp-fragment-tests.lisp`.
- Theorems: T4's first four and `fn-bpn-limits-compose`. No machine book is
  edited; `bp-limits` only includes the codec, so C1 runs beside A1, and
  if A1 changes `*fn-bpn-lifecycle-max-payload*` it re-certifies
  `bp-limits` in its closure. The reference is never connected to the
  native path.

**C2: family transformations in the machine. Fable. hbox, after B. 3 to 4 lane-days.**
- Edits: A1's four machine books (kinds 15 to 18, the plan, the
  replacement), `books/bp-node-replay.lisp` (the four replay cases),
  the teeth book, `tests/test_bp_service_native.py`.
- Theorems: T4's last two, T2's fragment enumeration, T6 extended by the
  four kinds.
- Traces: BP-R11, BP-R12, BP-R13, BP-R22 (measured on the native image:
  payload size and held-set size scaled independently, allocations, time,
  latency, for success, gap, overlap, conflict).

### Slice D: reports and independent wire evidence

**D1: the report codec. Sonnet. local. 1 to 2 lane-days.** New
`books/bp-status-report.lisp` and its tests: §7.6's grammar, decoder,
round trip, canonical-input keystone, reason table, timed assertions.
Slice B uses it for BP-R08.

**D2: generation, demultiplexing, vectors. Opus. hbox, after C2. 2 to 3 lane-days.**
- Edits: the machine books (four generation points, policy default nil, the
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

### Slice E: exhaustion and the operating envelope. Opus. persvati. 2 to 3 lane-days, after B.

- Edits: `books/bp-service-loop.lisp` (throttling terms only),
  `tests/test_bp_service_native.py`, `docs/operator.md`'s BP section.
- Work: exhaust the journal separately from saturating 64 live slots;
  admission near the last token; repeated `No Resources` with no clock
  progress; cleanup and control traffic under pressure; a documented
  bounded-run limit (records per journal, lifecycles per journal at the
  measured mix) or the rollover the answer to open question 1 chooses.
  Broad deployment claims wait on this record.
- Traces: BP-R21 (and BP-R24 re-run at the limit).

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

### Registry (root writes it at each landing)

PRF-046's events become T6's preservation pair and the two restated
keystones; a new target "The BP node machine delivers, forwards, expires and
discards only as RFC 9171 §5 says" carries T1 to T3 and T5 with each
hypothesis stack in one sentence; T4 is an event of the fragment target; K6's
soundness pair is an event of PRF-042 or its own target; PRF-038 gains its
`events` key (D13); REP-006 stays `specified` until slice B's gate record.

## 12. Decisions

The twelve questions of the first draft, answered by the review and adopted.
Each condition is written into the section named.

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

### Open, needing ember

1. **Journal longevity at v0.** The 4096-token journal is about 800 simple
   lifecycles. Options: a documented bounded-run limit plus an operator
   "rotate" that starts a new namespace generation from a checkpoint record
   of live state and bindings (narrow, one new kind, slice E), or the
   bounded-run limit alone with rotation in v1 compaction. Recommend: the
   narrow rotation in slice E, because agents running for weeks exceed 800
   lifecycles and a fenced node needs an operator either way.
2. **What authenticates a BP principal at v0.** TCPCL sessions today run
   without TLS, so under §2.3 no session has a principal and K6 refuses
   every request. Options: TCPCL TLS with the peer's configured
   certificate; or an explicit per-peer `"bp-trust" "network"` row (the
   configured address is the authority, noncrypto, visible on the node's
   page). Recommend: the explicit network-trust row for v0 (matches the
   2026-09-19 "noncrypto authority OK" direction and is honest in
   configuration), TCPCL TLS as the first step after T12.
3. **The Store event-order commits on `w25/bp-obligation-vertical`.** Eight
   commits edit `store-node`, `store-files`, `replay`, `store-events` and
   `node-retention-transitions`, which are T2/T4's books. Recommend: they go
   to T4's brief as an input, and A3 depends only on the release joins.
4. **Receipt-carrier expiry.** §9.4 lets a receipt carrier die and relies
   on the requester's retry to regenerate it. The alternative is receiver-
   side reauthoring on the receipt's own delivery policy. Recommend: the
   requester's retry (one owner of retry, no second policy), unless ember
   wants receipts to survive a requester that has itself stopped retrying.

## 13. Defects in existing code

Found by the review (D1 to D11) and while designing (D12 to D17). Each names
its line and the slice that closes it.

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

The first draft's F7 (`host/bp-release-owner-host.lisp:8` calling a function
no book defined) is closed on `dev` by `9dd5e3a2` (§10).
