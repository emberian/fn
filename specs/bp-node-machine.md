# The BP node processing machine (T12a)

Status: a design, phase 0 of step T12a in
[the trajectory plan](../planning/plan-2026-09-22-trajectory.md) (§3.1, the
T12 paragraph; §3.3, hbox lane 2 in phases 2 and 3). It edits no book, host
file, tool or test. Every signature it quotes was read from the tree at `dev`
`722c9566` on 2026-09-22; every "today" below is that revision. Phase 2
implements the definitions this document states; phase 3 proves the six
theorems it states; nothing here is a theorem until then.

This is a new file rather than a rewrite of §1.5 of
[bp-design](bp-design.md). §1.5 and §1.6 there are the wave-4 target
contract with three dated status sections, and the inventory those sections
carry is no longer true in the shape they state it (§0.2 below): `fn-bpn-step`
exists, has one host caller, three certified keystones and 118 theorems
around it, and is the outbound half of the machine this document completes.
Rewriting §1.5 in place would either erase that history or bury the contract
under it. bp-design's §1.5 and §1.6 now carry a pointer here and are not
edited further; their packet table (§5) and the interoperability plan (§3)
stay where they are.

Reading order for the phase-2 lane: §0 (what exists), §1 (the one decision),
§2 (state), §3 (events, effects, records), §4 (the six transitions), §5 (the
six theorems), §6 (K6), §7 (reassembly, dispatch, routes, reports), §8 (the
scheduler), §9 (what the host does), §10 (the branches), §11 (the two briefs),
§12 (questions for ember), §13 (defects found while designing).

## 0. What is true today

### 0.1 The books and the host, measured

| What | Where | Certified at its current digest (persvati `certify-20260922T121645Z-3620455`) |
| --- | --- | --- |
| the two ends: `fn-bpn-send`, `fn-bpn-receive` (three outcomes), `fn-bpn-expiry`, `fn-bpn-hop-exceededp`, `fn-bpn-next-hop-count`, `fn-bpn-forward-decision`; keystones K1 to K5 | `books/bp-node.lisp` (715 lines) | green |
| the outbound lifecycle: `fn-bpn-machine-state` (8 fields), `fn-bpn-job` (11 fields), the proposal machine (`fn-bpn-propose`, `fn-bpn-persist-result-step`, `fn-bpn-apply-record`, `fn-bpn-replay-records`), seven event arms, `fn-bpn-step`, `fn-bpn-trace`; M1 to M3 | `books/bp-node-machine.lisp` (713) | green |
| 90 theorems: typing, preservation of `fn-bpn-machine-invariantp`, the confinement trio (`fn-bpn-step-emits-no-release-from-actual-effects`, `-no-receipt-prepare`, `-effects-are-typed`) | `books/bp-node-machine-invariants.lisp` (1378) | green |
| 30 theorems: `fn-bpn-lifecycle-invariantp` and PRF-046's three keystones | `books/bp-node-machine-authorization.lisp` (896) | green |
| FNBS kinds 2 to 4 (`:queued`, `:attempting`, the result triple), the namespace plan, the publication authorization | `books/bp-node-machine-codec.lisp` (386) | green |
| FNBS kind 1, the creation-sequence frontier `(:bpn-sequence n)`, `fn-bpn-sequence-reserve` | `books/bp-node-records.lisp` (195) | green |
| the observed-file non-reuse model (PRF-045), the persistence-cut model | `books/bp-sequence-fidelity.lisp`, `books/bp-sequence-persistence.lisp` | green |
| the authored-wire publication authorization | `books/bp-authored-wire.lisp` | green |
| the receive-evidence namespace (`.wire` plus a verdict sidecar per transfer) | `books/bp-receive-evidence.lisp` | green |
| fragmentation, reassembly, `fn-bpf-complete-agreeing-cover-reassembles-to-payload`; two lemmas still commented out | `books/bp-fragment.lisp`, `books/bp-fragment-invariants.lisp` | green |
| the receiver (`fn-bpr-accept-request`, its four tags), the journal, the join the host calls (`fn-bpaj-dispatch`) and its fast twins | `books/bp-receipt*.lisp`, `books/bp-native-app.lisp`, `books/bp-native-app-fast.lisp` | receipt books green; `bp-native-app`, `bp-native-app-fast`, `bp-receiver-evolving-*` red |
| the convergence layer, C1 to C4 | `books/tcpcl-*.lisp` | green |
| the contact scheduler and its per-peer table | `books/scheduler*.lisp` | green; no native caller |

The host:

- `host/native/bp-service.lisp:110-116` is the one call to `fn-bpn-step`:

  ```lisp
  (defun fnn-bps-step (service event)
    ;; Assurance subject: this is the host call to fn-bpn-step, with no sibling
    ;; dispatcher between the native service and the proved transition.
    (let ((answer (fnn-core 'fn-bpn-step (fnn-bps-state service) event)))
      (setf (fnn-bps-state service)
            (fnn-core 'fn-bpn-host-answer-state answer))
      (fnn-core 'fn-bpn-host-answer-effects answer)))
  ```

  It is a pure `(state, event) -> (state, effects)` adapter. Every event the
  host issues reaches it: `:enqueue` (`:354`), `:persist-result` (`:217`),
  `:forward-result` (`:205`), `:clock` (`:315`), `:contact` (`:318`),
  `:restart` (`:296`). `:resume`, the seventh arm of `fn-bpn-eventp`, is
  never issued.
- The contact is fabricated: `bp-service.lisp:317-318` issues
  `(:contact peer t)` for every peer `fn-bpn-host-ready-peers` names, with no
  window, schedule or session behind the `t`.
- One TCP connection is opened per bundle attempt and torn down inside the
  `:cl-send` effect (`bp-service.lisp:169-205`); the XFER_REFUSE reason code a
  peer sends is logged at `tcpcl.lisp:274` and never reaches the machine.
- The receive path does not go through the machine at all. `tcpcl.lisp:251-267`
  holds the final XFER_ACK, hands the octets to `*fnn-tcl-deliver*`, and
  releases the ack when that returns. On the `bp receive` verb the callback is
  `fnn-bp-deliver` (`bp.lisp:344`): decode with `fn-bpn-receive` (`:362`),
  publish the wire and a verdict sidecar under the receive-evidence namespace.
  On `bp-app receive` it is `fnn-bpapp-deliver` (`bp-app.lisp:152`): decode
  (`:155`), evidence (`:168`), then under the owner mutex the FNRJ dispatcher
  loop and the owner Store submission (`:74-140`), then the receipt bundle is
  authored with `fn-bpn-host-send` at `:188` and parked on the connection at
  `:196` for the next loop iteration to offer. Every durable write happens
  before the ack leaves; none of it is a machine transition.
- The route `(:route host port node-id keepalive segment-mru transfer-mru)`
  is built from command-line arguments at `bp-service.lisp:347-350` and stored
  inside every job; the host reads it back by position at `:162-167`.

### 0.2 What bp-design §1.5.1 says that is no longer true, and what is still true

Still true: reassembly is not wired (`fn-bpn-receive` refuses a fragment with
`:fragment-not-reassembled`, `bp-node.lisp:427`); status reports are absent;
dispatch has no routing table; there is no bundle list with retention
constraints; T1 to T6 are unproved; nothing calls `fn-retain-release` from the
BP path (independent review naivety 6).

No longer true as stated: "`fn-bpn-make-state`, `fn-bpn-statep`, `fn-bpn-step`
and `fn-bpn-trace`: none exists." `fn-bpn-step` and `fn-bpn-trace` exist at
`bp-node-machine.lisp:640,657` with `fn-bpn-machine-statep` at `:270`; they
are the outbound lifecycle only. "The FNBS record family and the
`(:bpn-sequence n)` durable frontier of section 1.3: absent." Kind 1 is
`bp-node-records.lisp`, kinds 2 to 4 are `bp-node-machine-codec.lisp`, and
the frontier is reserved and barriered before every bundle is authored
(`bp.lisp:133-170`, PRF-045). "`host/native/bp.lisp` takes the sequence
number as an argument" is true only of the one-shot `bp send` verb.

### 0.3 The absences this design closes

1. One bundle list with RFC 9171 §5 retention constraints, holding received,
   reassembled, forwarded, locally authored and report bundles alike.
2. Reception through the machine, with the ack released on a durable record.
3. Dispatch: local delivery against forwarding, decided from a routing table
   the machine holds.
4. Reassembly through `fn-bpf-reassemble`, and proactive fragmentation at
   the next hop's transfer MRU.
5. Status reports: generated as bundles the node authors when requested and
   enabled; parsed into transport observations and nothing else.
6. Discard: a bundle with no constraint and no attempt leaves the list, so a
   node that has carried 64 bundles is not full forever (§13, F1).
7. Restart re-anchoring of every bundle's age (time.md, "re-established from
   durable state").
8. K6: the delivered ADU's admission is `fn-peer-decide-transfer`.

## 1. The one decision: a job is a bundle

Today the outbound half keeps `fn-bpn-job` records (work, attempt,
generation, sequence, anchor, peer, route, bundle, wire, status, token) and
the two ends keep nothing. RFC 9171 §5 has one bundle store in which every
bundle, whatever its origin, carries retention constraints and is dispatched,
forwarded, delivered, expired, deleted and discarded by the same steps. A
second list for received bundles would state T2, T3 and T6 twice, would give
a relay two forwarding paths (a transit bundle would need a job, and a job's
`:queued` record today requires `peer = destination`,
`bp-node-machine.lisp:196-198`, which is false for a next hop), and would
leave the two lists sharing one token frontier through a seam.

So: **the job becomes the local-origin case of a held bundle.** The state's
`jobs` field becomes `held`, a list of `fn-bpn-held` records (§2.2); a job's
work/attempt/generation key becomes the `origin` field; its status becomes a
constraint set and an in-flight attempt; its route leaves the record and is
looked up in the routing table at send time. The proposal machine
(`fn-bpn-propose`, `:persist-result`, `fn-bpn-apply-record`,
`fn-bpn-replay-records`, the fence) is unchanged in shape: one pending
proposal, one token frontier, one fence, records applied on `:durable`. The
three PRF-046 keystones are restated one for one over the new record (§5,
T6) and remain about the function the host calls.

The cost, measured: `books/bp-node-machine` is in the include closure of five
books (`-invariants`, `-authorization`, `-codec` and the two test books) and
one host wrapper, so the widening is contained in the lane's own books; the
118 theorems around it are record algebra that `fn-defrecord` regenerates
and preservation lemmas whose proofs keep their shape. The alternative, a
second machine composed beside this one, was rejected for the reasons above
and because its two fences and two token spaces are exactly the "two
journals per node" the independent review named.

What is deliberately not in the state: the workflow image (`fn-bp-statep`).
bp-design's `fn-bpn-obligation-openp` read it; the machine does not need it
(§4.4, discard) and including `books/bp-workflow` would put the store codec
into the machine's closure (review F3). What "obligation" means at this
layer is a constraint or an attempt (§2.3); the application's obligations
are the workflow's and the machine never emits an effect that could touch
them (T2c).

## 2. State

### 2.1 Configuration and policy

`fn-bpn-config` (`bp-node.lisp:81-90`) is unchanged: `(fn-bpn-config node-id
lifetime crc-type hop-limit transfer-limit)`. Adding a field to it would
reopen K1 and K5's proofs, which name `fn-bpn-configp` as a literal; the
machine's own knobs go beside it:

```lisp
(fn-defrecord fn-bpn-policy
  :tag :fn-bpn-policy
  :constructor (fn-bpn-policy reports previous-node max-held max-octets)
  :fields ((fn-bpn-policy-reports fn-bpn-machine-boolp)        ; generate requested status reports
           (fn-bpn-policy-previous-node fn-bpn-machine-boolp)  ; insert our Previous Node block on forwarding
           (fn-bpn-policy-max-held fn-bpn-machine-limitp)      ; was max-jobs; 64 today
           (fn-bpn-policy-max-octets fn-bpn-machine-limitp))   ; 16777216 today
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)
```

### 2.2 A held bundle

```lisp
(fn-defrecord fn-bpn-held
  :tag :fn-bpn-held
  :constructor (fn-bpn-make-held id origin bundle wire anchor next-hop
                                 constraints attempt deleted token)
  :fields ((fn-bpn-held-id fn-bpn-bundle-idp)              ; (fn-bpp-bundle-id primary (len payload))
           (fn-bpn-held-origin fn-bpn-originp)              ; §2.3
           (fn-bpn-held-bundle fn-bpb-bundlep)              ; the decoded, canonical bundle
           (fn-bpn-held-wire fn-cbor-octet-listp)           ; = (fn-bpb-encode bundle), a list invariant
           (fn-bpn-held-anchor fn-clock-age-anchorp)        ; (age . monotonic) or nil
           (fn-bpn-held-next-hop fn-bpn-maybe-eidp)         ; nil until dispatched to forwarding
           (fn-bpn-held-constraints fn-bpn-constraint-setp) ; subset of the three
           (fn-bpn-held-attempt fn-bpn-maybe-attemptp)      ; nil | (:attempting peer)
           (fn-bpn-held-deleted fn-bpn-maybe-reasonp)       ; nil | a §6.1.1 Table 1 reason keyword
           (fn-bpn-held-token fn-bpn-machine-u64p))         ; the token of the last record that touched it
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)
```

`fn-bpn-bundle-idp` is the shape of `fn-bpp-bundle-id`'s value
(`bp-primary.lisp:709`: `(:fn-bp-bundle-id source creation-time sequence
fragment-offset payload-length)`). The creation sequence, the ADU key
(`fn-bpp-adu-key`, `bp-primary.lisp:702`), the destination and the flags are
projections of `bundle` and are not stored twice.

### 2.3 Origins, constraints, attempts

```lisp
(defun fn-bpn-originp (x)
  ;; (:local work attempt generation)  a bundle the workflow's :submit made (was the job key)
  ;; (:receipt receipt-id)             a bundle the application's receipt made
  ;; (:cl xfer-id peer-eid)            received over the convergence layer from that session peer
  ;; (:reassembled adu-key)            built by fn-bpn-reassemble from held fragments
  ;; (:report subject-id assertion)    a status report this node authored about subject-id
  ...)
(defun fn-bpn-constraintp (x)
  (fn-bpn-member x '(:dispatch-pending :forward-pending :reassembly-pending)))
(defun fn-bpn-constraint-setp (x) ...)   ; a duplicate-free list of constraints
(defun fn-bpn-maybe-attemptp (x)
  (or (null x) (and (true-listp x) (equal (len x) 2) (equal (car x) :attempting)
                    (fn-bpp-eidp (nth 1 x)))))
(defun fn-bpn-retainedp (h)              ; what "obligation open" means at this layer
  (or (consp (fn-bpn-held-constraints h)) (consp (fn-bpn-held-attempt h))))
```

A held bundle with `deleted` set has no constraints and no attempt (a list
invariant); it stays in the list until discarded so that its fate is
readable, exactly as an `:expired` job is kept today.

### 2.4 The routing table

```lisp
(fn-defrecord fn-bpn-route
  :tag :fn-bpn-route
  :constructor (fn-bpn-make-route peer-name peer-eid cl reach)
  :fields ((fn-bpn-route-peer-name fn-bpn-machine-textp)   ; the configured peer's name (fn-cfg-peer-name)
           (fn-bpn-route-peer-eid fn-bpp-eidp)             ; its BP node ID, the (:bp eid) transport row
           (fn-bpn-route-cl fn-bpn-routep)                 ; today's 7-tuple, unchanged: host port node-id keepalive segment-mru transfer-mru
           (fn-bpn-route-reach fn-bpn-eid-listp))          ; node IDs reachable through this peer, besides the peer itself
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)
(defun fn-bpn-route-listp (rs) ...)      ; distinct peer names, at most *fn-cfg-max-rows* entries
(defun fn-bpn-next-hop (routes destination)
  ;; the first route whose peer-eid's node ID is the destination's node ID or whose reach lists it; nil otherwise
  ...)
```

The table is installed by a `(:routes table)` event and is not persisted by
the machine: its provenance is configuration (§7.3). The existing
`fn-bpn-routep` (`bp-node-machine.lisp:31-39`) survives verbatim as the
convergence-layer address of a route; it leaves the held record and is
carried in the `:cl-send` effect instead.

### 2.5 The machine state

```lisp
(fn-defrecord fn-bpn-machine-state
  :tag :fn-bpn-machine-state
  :constructor (fn-bpn-make-machine-state config policy held contacts routes
                                          pending fenced next-token)
  :fields ((fn-bpn-machine-state-config fn-bpn-configp)
           (fn-bpn-machine-state-policy fn-bpn-policyp)
           (fn-bpn-machine-state-held fn-bpn-held-listp)          ; unique ids
           (fn-bpn-machine-state-contacts fn-bpn-contact-listp)   ; unchanged: a duplicate-free list of open peer EIDs
           (fn-bpn-machine-state-routes fn-bpn-route-listp)
           (fn-bpn-machine-state-pending fn-bpn-maybe-pendingp)   ; unchanged
           (fn-bpn-machine-state-fenced fn-bpn-machine-boolp)     ; unchanged
           (fn-bpn-machine-state-next-token fn-bpn-machine-u64p)) ; unchanged
  :recognizer fn-bpn-machine-recordp :recognizer-verify-guards nil
  :car-fn fn-cbor-ag-car :cdr-fn fn-cbor-ag-cdr)

(defun fn-bpn-machine-statep (st)         ; the specification recognizer
  (and (fn-bpn-machine-recordp st)
       (<= (len (fn-bpn-machine-state-held st)) (fn-bpn-policy-max-held (fn-bpn-machine-state-policy st)))
       (<= (fn-bpn-held-octets (fn-bpn-machine-state-held st)) (fn-bpn-policy-max-octets (fn-bpn-machine-state-policy st)))
       (fn-bpn-held-wires-are-encodings (fn-bpn-machine-state-held st))   ; wire = (fn-bpb-encode bundle) for every entry
       (fn-bpn-held-deleted-are-unretained (fn-bpn-machine-state-held st))
       (or (null (fn-bpn-machine-state-pending st))
           (equal (fn-bpn-pending-token (fn-bpn-machine-state-pending st))
                  (fn-bpn-machine-state-next-token st)))))
```

`fn-bpn-machine-invariantp` (token below `*fn-bpn-machine-max-records*`, no
fence with a pending proposal) and `fn-bpn-lifecycle-invariantp` (the
pending proposal is applicable and its three effect lists are the authorized
ones, `bp-node-machine-authorization.lisp:90-109`) keep their names and
their conjuncts over the new record.

**No revalidation on the served path.** Today `fn-bpn-step` evaluates
`fn-bpn-machine-statep` on entry (`bp-node-machine.lisp:642`), which runs
`fn-bpb-bundlep` over every held bundle's decoded blocks and payload on every
event: 64 bundles of a mebibyte each is an octet-list walk of 64 MiB per
`:clock`. That is the recognizer-per-command the assurance rules forbid
(D3). Phase 2 splits it the way `books/bp-native-app-fast` did:
`fn-bpn-step` keeps the entry check in the logic; `fn-bpn-step-fast` is the
same dispatcher without it, validating only the event's own operands
(bounded by construction: an octet list of at most the transfer limit, one
EID, one key), and

```lisp
(defthm fn-bpn-step-fast-is-step
  (implies (fn-bpn-lifecycle-invariantp st)
           (equal (fn-bpn-step-fast st event) (fn-bpn-step st event))))
```

is the named equation under which every theorem of §5, stated over
`fn-bpn-step`, is a theorem about `fn-bpn-step-fast`, the function
`fnn-bps-step` calls from phase 2 on. The invariant is established once by
`:restart` (replay validates every record with `fn-bpn-record-applicablep`,
which is where `fn-bpb-bundlep` runs, once per record) and preserved by
every step (T6).

## 3. Events, effects, records

### 3.1 Events the host issues

| Event | Who issues it | Notes |
| --- | --- | --- |
| `(:bundle-received octets origin obs)` | the TCPCL callback, `origin = (:cl xfer-id peer-eid)` with the session's negotiated peer node ID | the ack is held until the machine answers (§9.1) |
| `(:transmit origin destination sequence adu obs)` | the workflow's `:submit` effect (`bp-workflow.lisp:482-488`) as `origin = (:local work attempt generation)`; the application's receipt as `origin = (:receipt id)` | replaces `:enqueue`; `route` and `peer` are gone: the destination EID is the argument and the next hop is the table's |
| `(:author-report id assertion reason sequence obs)` | the host, after a `:report-due` effect, with a freshly reserved sequence | §7.4 |
| `(:deliver-result id outcome)` | the host, after the `:deliver` effect ran through the application join; `outcome` is `:accepted`, `:duplicate`, `:refused` or `:uncertain` | §6 |
| `(:forward-result id peer outcome)` | the host, from the CL outcome of a `:cl-send`; `outcome` is `:sent`, `(:refused code)` with the RFC 9174 Table 6 code, `:failed` or `:uncertain` | the code reaches the machine (§13, F3) |
| `(:contact peer open-p obs)` | the scheduler's open/close (§8); until T12c, the operator or a session-up | gains `obs` for the age estimate of the first send |
| `(:resume peer obs)` | the host, after each completed attempt while the contact is open | the seventh arm becomes reachable (§9.3) |
| `(:persist-result token outcome)` | the host, after publishing a `:persist` record; `:durable`, `:refused` or `:uncertain` | unchanged |
| `(:clock obs)` | the host's sweep | one expiry or one discard per event, as today |
| `(:routes table)` | the host, from configuration at open and at every reconfiguration | §7.3 |
| `(:restart records sequence-ready obs)` | the host at open, after namespace recovery | gains `obs` for re-anchoring (T6) |

`fn-bpn-machine-eventp` bounds the `:restart` record list as today
(`bp-node-machine-invariants.lisp:19-25`) and bounds `:bundle-received`'s
octets by the configured transfer limit and `(:routes table)` by
`fn-bpn-route-listp`.

### 3.2 Effects the host executes

| Effect | Meaning | Host obligation (§9) |
| --- | --- | --- |
| `(:persist token record)` | publish this FNBS record under the name ACL2 derives, then report `:persist-result` | unchanged |
| `(:receive-stored id)` | the `:bundle-stored` record is durable | release the held XFER_ACK |
| `(:receive-duplicate id)` | already held, byte-identical | release the ack |
| `(:receive-observed id)` | an administrative record for this node was consumed (§7.4); nothing stored | release the ack |
| `(:receive-refused reason)` | never stored: undecodable, non-conformant flags, capacity | release the ack when the transfer had completed; XFER_REFUSE `No Resources` when the capacity query refused it at START (§9.1) |
| `(:receive-uncertain reason)` | the store is uncertain | drop the ack; the transfer fails at the peer and is retried (C3) |
| `(:deliver id adu-key payload origin report-p)` | hand the ADU to the application join under the owner mutex, then answer `:deliver-result` | §6; reserve a sequence before answering when `report-p` |
| `(:cl-send cl peer id wire)` | offer `wire` on the session to `peer` at address `cl`; answer `:forward-result` | one session per open contact, offers in effect order (§9.3) |
| `(:transport work attempt generation status)` | relay to the workflow | unchanged; statuses are those `fn-bp-transport-statusp` accepts today: `:attempted`, `:forwarded`, `:delivered`, `:deleted`, `:expired`; `:bundle-created` waits for packet 6 (T12c) |
| `(:report-due id assertion reason)` | the subject requested this report and policy enables it | reserve a sequence, then issue `:author-report`; may be dropped on a crash, reports are not evidence (T5) |
| `(:bundle-queue-accepted origin sequence :durable/:duplicate)`, `-refused`, `-uncertain` | the answer to `:transmit`, as today keyed by origin | unchanged |
| `(:forward-refused id peer reason)` | informational | unchanged |
| `(:restart-ready n)`, `(:restart-fault why)`, `(:routes-installed n)`, `(:routes-refused why)` | | |

`fn-bpn-effectp` is the enumeration; `:release` and `:receipt-prepare` are
not in it (M1, unchanged).

### 3.3 Records (FNBS kinds)

Kind 1 (`:bpn-sequence`, `bp-node-records`) is unchanged. Kinds 2 to 4 are
today's job records and are retired (§12, Q2): no new record of those kinds
is written and the phase-2 codec refuses them at recovery as
`:lifecycle-record` faults. The new kinds, each carrying the token first, in
one append-only frame family with the specs the codec book states:

| Kind | Record | Applied by `fn-bpn-apply-record` as |
| --- | --- | --- |
| 5 | `(:bundle-stored token held)` | append `held` (constraints `(:dispatch-pending)`, no attempt) |
| 6 | `(:dispatched token id disposition)` with `disposition` one of `:deliver`, `(:forward next-hop)`, `:await-fragments` | `:deliver`: keep `:dispatch-pending`; `(:forward p)`: replace `:dispatch-pending` by `:forward-pending`, set `next-hop`; `:await-fragments`: add `:reassembly-pending` |
| 7 | `(:reassembled token adu-key held fragment-ids)` | append the reassembled `held` with origin `(:reassembled key)` and `(:dispatch-pending)`; remove `:reassembly-pending` from every listed fragment |
| 8 | `(:delivered token id outcome)` | drop `:dispatch-pending` |
| 9 | `(:attempting token id peer age)` | set `attempt = (:attempting peer)`; `age` is the estimate written into the transmitted Bundle Age block, kept for re-anchoring |
| 10 | `(:forwarded token id peer outcome)` | clear `attempt`; on `:sent` or `(:refused 1)` (Completed) drop `:forward-pending`; otherwise keep it (requeued) |
| 11 | `(:deleted token id reason)` | clear every constraint and the attempt; set `deleted` |
| 12 | `(:discarded token id)` | remove the entry |

`fn-bpn-record-applicablep` is per kind as today: the token is the frontier,
the entry exists (or does not, for kind 5), the constraint the record moves
is present, the attempt the record clears is set, the disposition names a
route the table holds. Every record's payload is bounded by
`*fn-bpn-lifecycle-max-payload*` (134144 octets today, which holds one held
bundle of `*fn-bpn-machine-max-job-octets*`; the lane keeps that name or
renames it with the record).

The token frontier `*fn-bpn-machine-max-records*` is 4096; at five records
per bundle that is about eight hundred bundles per journal lifetime, after
which the machine fences (`bp-node-machine.lisp:372-373`). Compaction is v1
(d) and this design does not change the bound.

## 4. The six transitions

Every transition is total, takes and returns the state, refuses malformed
operands in the logic (the `set-verify-guards-eagerness 0` discipline of the
existing book), performs bounded work, and either proposes exactly one
record or changes nothing durable. "Proposes" means `fn-bpn-propose` as
today: the state gains a pending proposal and the answer is one `:persist`
effect; the record is applied, and the proposal's success effects released,
only on `(:persist-result token :durable)`.

### 4.1 Reception: `fn-bpn-receive-step st octets origin obs`

RFC 9171 §5.6, in its order, with fn's stronger rule that nothing is stored
before it decodes.

1. Bounds first: `(fn-bpb-decode octets (fn-bpn-config-transfer-limit
   config))` refuses over-long input before reading it
   (`fn-bpb-decode-refuses-overlong-input`); a decode error is
   `(:receive-refused why)` and no record.
2. `fn-bpp-flags-conformantp` on the primary, else `(:receive-refused
   :flags-not-conformant)`.
3. The id: `(fn-bpp-bundle-id primary (len payload))`. Held already with the
   same wire: `(:receive-duplicate id)`; held with a different wire under
   the same id: `(:receive-refused :identity-conflict)` (two bundles with
   one identity is corruption or a hostile peer; neither replaces what is
   held).
4. Administrative record addressed to this node
   (`fn-bpp-administrativep flags` and `fn-bpn-local-destinationp`): decode
   the payload as a status report (§7.4); if it names the ADU key of a held
   bundle with origin `(:local work attempt generation)`, the answer is
   `(:transport work attempt generation status)` for the assertion it
   carries, plus `(:receive-observed id)`; otherwise `(:receive-observed id)`
   alone. Nothing is stored and nothing else is emitted (T5).
5. Capacity: `held` at `max-held`, or octets plus `(len octets)` over
   `max-octets`: `(:receive-refused :capacity)`.
6. Otherwise propose `(:bundle-stored token held)` with origin `origin`,
   anchor `(fn-bpn-anchor-of bundle obs)` (`bp-node.lisp:224`: the Bundle
   Age block's value paired with the monotonic reading, or nil), constraints
   `(:dispatch-pending)`. Its success effects: `(:receive-stored id)` and,
   when the flags request a reception report and policy enables reports,
   `(:report-due id :received :none)`.

On `(:persist-result token :durable)` of a kind-5 record the machine applies
it and then runs §4.2 on the new entry in the same step, so the answer to
that event is the receive-stored effect followed by the dispatch proposal's
`:persist`. The lifetime question is not asked at reception: RFC 9171 §5.6
does not ask it, expiry is §4.4's, and an uncertain clock at reception must
not refuse a bundle that a later observation can decide.

The capacity query `(fn-bpn-transfer-admissiblep st n)` is a pure function
the host calls at XFER_SEGMENT START when a Transfer Length Extension
announces `n` octets, so that `No Resources` is answered before the data is
taken (§9.1); step 5 repeats the check on the octets actually received.

### 4.2 Dispatch and delivery: `fn-bpn-dispatch-step st id`, `fn-bpn-deliver-result-step st id outcome`

RFC 9171 §5.3 and §5.7. Dispatch runs once per stored or reassembled entry,
immediately after its record is durable, and again for every entry with
`:forward-pending` and no next hop after a `(:routes table)` event.

- A fragment (`fn-bpp-fragmentp`) addressed to this node: collect the held
  fragments with its ADU key (§7.1); if `fn-bpf-reassemble` answers `(:ok
  bytes)`, propose `(:reassembled token key held ids)` where `held` is the
  bundle whose primary is `(fn-bpn-unfragment (primary of the offset-zero
  fragment))`, whose blocks are that fragment's, whose payload is `bytes` and
  whose origin is `(:reassembled key)`; if `(:missing lo hi)`, propose
  `(:dispatched token id :await-fragments)`; if `(:conflict i)`, propose
  `(:deleted token id :block-unintelligible)` for this fragment (two
  fragments disagreeing on a byte is corruption, bp-design §1.5).
- A whole bundle addressed to this node: propose `(:dispatched token id
  :deliver)`; its success effect is `(:deliver id adu-key payload origin
  report-p)` with `report-p` from the flags and policy.
- Otherwise `(fn-bpn-next-hop routes destination)`: a route gives
  `(:dispatched token id (:forward next-hop))`; no route gives nothing
  durable and `(:forward-refused id nil :no-known-route)`: the entry keeps
  `:dispatch-pending` and is re-dispatched when a table arrives (RFC 9171
  §5.4.1, "ceases to be contraindicated").

`fn-bpn-deliver-result-step`: `:accepted`, `:duplicate` and `:refused`
propose `(:delivered token id outcome)`, whose success effects are
`(:report-due id :delivered :none)` when requested and enabled;
`:uncertain` changes nothing (the entry keeps `:dispatch-pending` and is
delivered again after the application recovers; the owner's fence is the
owner's). A refusal by the application is a completed delivery at this
layer: the bundle reached its application agent, which decided; what it
decided is the application's record (FNRJ), not the carrier's.

### 4.3 Forwarding: `fn-bpn-contact-step st peer open-p obs`, `fn-bpn-start-one st peer obs`, `fn-bpn-forward-result-step st id peer outcome`

RFC 9171 §5.4. The contact set and its open/close are unchanged.
`fn-bpn-start-one`, called by an open and by `:resume`, selects the oldest
entry (smallest `token`) with `:forward-pending`, `next-hop = peer`, no
attempt and not deleted, and:

1. if `fn-bpn-hop-exceededp` (`bp-node.lisp:264`): propose `(:deleted token id
   :hop-limit-exceeded)`;
2. if the wire exceeds the route's transfer MRU and the bundle is
   fragmentable (`fn-bpf-fragmentablep`, not `fn-bpp-no-fragmentp`): §7.2,
   propose the first fragment's `(:bundle-stored ...)`; the parent is
   deleted `:no-additional-information` once every fragment is stored;
3. otherwise propose `(:attempting token id peer age)` where `age` is
   `(fn-clock-age-estimate anchor obs)` (or nil), with success effect
   `(:cl-send cl peer id image)`, `image` = `(fn-bpn-forward-image st entry
   obs)`: the held bundle with the Previous Node block removed and, under
   policy, this node's inserted; the Bundle Age block set to `age`; the Hop
   Count incremented with `fn-bpn-next-hop-count` (`bp-node.lisp:273`);
   re-encoded. The held record is unchanged; only the image differs
   (bp-design §1.5, `fn-bpn-forward-prepare`).

`fn-bpn-forward-result-step` proposes `(:forwarded token id peer outcome)`.
Its success effects: on `:sent` or `(:refused 1)`, `(:transport ...
:forwarded)` for a local origin and `(:report-due id :forwarded :none)` when
requested; otherwise `(:transport ... :attempted)` and `(:forward-refused
id peer outcome)`. A requeued entry is selected again on the next `:resume`
or open; there is no retry counter: a forward-pending bundle is forwarded
until it is sent, expires or is deleted, which is RFC 9171 §5.4.1 and is
why the node needs no second scheduler (§8).

### 4.4 The clock: `fn-bpn-clock-step st obs`

RFC 9171 §5.5, §5.10, §5.11. One decision per event, as today. In order:

1. the first entry, not deleted, whose `fn-bpn-held-expiry entry obs`
   (`fn-clock-expiry-decision` over the primary's creation time and lifetime,
   the entry's anchor and `obs`) is `:expired`: propose `(:deleted token id
   :lifetime-expired)`, success effects `(:transport ... :expired)` for a
   local origin and `(:report-due id :deleted :lifetime-expired)` when
   requested; `:live` and `:uncertain` select nothing (M3, unchanged);
2. else the first entry that is discardable, `(not (fn-bpn-retainedp
   entry))` (no constraint, no attempt: sent, delivered, deleted, or a
   reassembled fragment): propose `(:discarded token id)`;
3. else nothing.

Deletion never removes an entry and discard never deletes one; the two
records are distinct so that a journal reads as the RFC's two steps.

### 4.5 Authoring: `fn-bpn-transmit-step st origin destination sequence adu obs`, `fn-bpn-report-step st id assertion reason sequence obs`

RFC 9171 §5.2 and §6.1.1. `fn-bpn-transmit-step` is today's
`fn-bpn-enqueue-step` with the job replaced by a held entry: the bundle is
`(fn-bpn-send-bundle config destination adu sequence obs)`, the wire
`(fn-bpn-send ...)` (both `bp-node.lisp`, unchanged, so K1 and K5 stay the
node's), the entry has origin `origin`, anchor `(0 . monotonic)`, constraints
`(:dispatch-pending)`; an existing entry with the same origin and the same
bundle and wire answers `:duplicate` without a record, a different one
`:enqueue-conflict`, capacity refuses, otherwise `(:bundle-stored ...)` is
proposed. Dispatch (§4.2) follows on durability, so a bundle for a peer we
route to gains `:forward-pending` and a next hop, and a bundle for this
node's own EID is delivered to ourselves (RFC 9171 §5.3 step 1).

`fn-bpn-report-step` authors a status-report bundle (§7.4) about held entry
`id` when that entry exists, requested `assertion` in its flags, and policy
enables reports; the report bundle is a held entry with origin `(:report id
assertion)`, is dispatched like any other, and answers `:bundle-queue-*`
like a transmit. A stale or fabricated `:author-report` (no such entry, or
the assertion was not requested) changes nothing.

The sequence in both events is one the host reserved and made durable
before the event (`fn-bpn-sequence-reserve`, PRF-045); a sequence that goes
unused because the transition refused is burned, which the frontier's
monotonicity permits.

### 4.6 Persistence, routes and restart: `fn-bpn-persist-result-step`, `fn-bpn-routes-step st table`, `fn-bpn-restart-step st records sequence-ready obs`

`fn-bpn-persist-result-step` is unchanged (`bp-node-machine.lisp:494-520`):
`:durable` applies the pending record and releases its success effects, and
when the applied record is kind 5 or 7 the answer continues with §4.2's
proposal; `:refused` clears the proposal; `:uncertain` fences.

`fn-bpn-routes-step` installs `table` when `fn-bpn-route-listp` holds and
re-dispatches every entry that has `:dispatch-pending` and no next hop (one
proposal per event; the host issues `:routes` again while
`(:routes-installed n)` reports `n > 0` re-dispatched candidates).

`fn-bpn-restart-step` is today's (`:600-624`) with two changes: every entry
recovered with an attempt has it cleared (`fn-bpn-resume-held`, as
`fn-bpn-resume-jobs` today, M2), and every entry's anchor is re-established
as `(age . (fn-clock-monotonic obs))` where `age` is the largest age any
durable record of that entry carries (its `:bundle-stored` anchor age, or a
later `:attempting` record's `age`), or nil when it had none (T6). The
residence before the restart is an unknown interval and is omitted, which
RFC 9171 §4.4.2 permits and time.md states as "an anchor is a lower bound".

## 5. The six theorems, for phase 3

Hypotheses are `(fn-bpn-lifecycle-invariantp st)` and `(fn-bpn-machine-eventp
event)` unless stated. `(fn-bpn-answer-effects (fn-bpn-step st event))` is
written `EFFECTS` and `(fn-bpn-answer-state (fn-bpn-step st event))`
`NEXT`; `(fn-bpn-find-held id (fn-bpn-machine-state-held st))` is `HELD`. The
subject is `fn-bpn-step`; the function the host calls is `fn-bpn-step-fast`
(`host/native/bp-service.lisp:113` in phase 2, replacing today's `'fn-bpn-step`
in the same line), and `fn-bpn-step-fast-is-step` (§2.5) is the named
equation between them. Every theorem lives in
`books/bp-node-machine-invariants.lisp` or `-authorization.lisp`; the teeth in
`tests/acl2/bp-node-machine-teeth-tests.lisp` (new), one `must-fail` per
hypothesis, each over a reachable state built by `fn-bpn-trace` from
`fn-bpn-initial-machine-state`.

### T1. Delivery names a validated, whole, non-administrative bundle this node holds

```lisp
(defthm fn-bpn-deliver-effect-names-a-validated-whole-bundle
  (implies (and (fn-bpn-lifecycle-invariantp st) (fn-bpn-machine-eventp event)
                (member-equal (list :deliver id key payload origin report-p) EFFECTS))
           (let* ((h HELD) (b (fn-bpn-held-bundle h)) (p (fn-bpb-bundle-primary b)))
             (and h
                  (fn-bpb-bundlep b)
                  (equal (fn-bpn-held-wire h) (fn-bpb-encode b))
                  (fn-bpp-flags-conformantp p)
                  (not (fn-bpp-fragmentp (fn-bpp-flags p)))
                  (not (fn-bpp-administrativep (fn-bpp-flags p)))
                  (fn-bpn-local-destinationp st h)
                  (member-eq :dispatch-pending (fn-bpn-held-constraints h))
                  (equal key (fn-bpp-adu-key p))
                  (equal payload (fn-bpb-payload b))
                  (equal origin (fn-bpn-held-origin h))))))

(defthm fn-bpn-reassembled-entry-is-a-complete-agreeing-reassembly
  (implies (and (fn-bpn-lifecycle-invariantp st) (fn-bpn-machine-eventp event)
                (member-equal (list :persist token (list :reassembled key held ids)) EFFECTS))
           (let ((r (fn-bpf-reassemble (fn-bpn-fragments-of st key)
                                       (fn-bpp-total-adu-length
                                        (fn-bpb-bundle-primary (fn-bpn-held-bundle (fn-bpn-find-held (car ids) (fn-bpn-machine-state-held st))))))))
             (and (equal (fn-bpf-result-tag r) :ok)
                  (equal (fn-bpb-payload (fn-bpn-held-bundle held)) (fn-bpf-result-bytes r))
                  (equal (fn-bpb-bundle-primary (fn-bpn-held-bundle held))
                         (fn-bpn-unfragment (fn-bpb-bundle-primary (fn-bpn-held-bundle (fn-bpn-find-held (car ids) (fn-bpn-machine-state-held st))))))
                  (equal (fn-bpp-adu-key (fn-bpb-bundle-primary (fn-bpn-held-bundle held))) key)))))
```

"Validated" is the list invariant `wire = (fn-bpb-encode bundle)` together
with `fn-bpb-bundlep`, established at reception by `fn-bpb-decode-yields-bundle`
and preserved by every record. Host line: `bp-service.lisp:113`; the effect is
executed by the delivery obligation of §9.2. Teeth: (invariant) a state whose
pending proposal's success effects contain a `:deliver` for an id not held,
fed `(:persist-result token :durable)`, emits that `:deliver`, so the
conclusion fails; (eventp) a `:restart` whose record list exceeds
`*fn-bpn-machine-max-records*`; (reassembly) two held fragments that disagree
on one byte are never reassembled and one is deleted `:block-unintelligible`.

### T2. An undelivered bundle for this node is deleted only by expiry; discard needs no constraint, no attempt; the machine touches no obligation

```lisp
(defthm fn-bpn-undelivered-local-bundle-is-deleted-only-by-expiry
  (implies (and (fn-bpn-lifecycle-invariantp st) (fn-bpn-machine-eventp event)
                HELD (fn-bpn-local-destinationp st HELD)
                (member-eq :dispatch-pending (fn-bpn-held-constraints HELD))
                (member-equal (list :persist token (list :deleted id reason)) EFFECTS))
           (and (equal reason :lifetime-expired)
                (equal (car event) :clock)
                (equal (fn-bpn-held-expiry HELD (nth 1 event)) :expired))))

(defthm fn-bpn-discard-is-proposed-only-for-an-unretained-entry
  (implies (and (fn-bpn-lifecycle-invariantp st) (fn-bpn-machine-eventp event)
                (member-equal (list :persist token (list :discarded id)) EFFECTS))
           (and HELD (not (fn-bpn-retainedp HELD)))))

(defthm fn-bpn-step-emits-no-release-and-no-receipt-prepare
  (and (not (fn-bpn-effect-kind-memberp :release EFFECTS))
       (not (fn-bpn-effect-kind-memberp :receipt-prepare EFFECTS))))
```

The third is today's confinement pair (`bp-node-machine-invariants.lisp:1322,1348`)
restated over the new effect vocabulary and stays unconditional. The
`:block-unintelligible` arm of bp-design's T2 is gone because a stored
bundle has decoded; the only corruption a held bundle can show is a fragment
conflict, which is a fragment, not a deliverable bundle, and is covered by
T1's third tooth. Teeth: (local destination) a transit bundle with
`:forward-pending` is deleted `:hop-limit-exceeded` by `:resume`; (dispatch
pending) a delivered entry is discarded, not deleted; (retained) an entry
with an attempt is never discarded.

### T3. Expiry only by the clock book's decision; an uncertain clock deletes nothing

```lisp
(defthm fn-bpn-expiry-deletion-is-proposed-only-by-a-clock-decision
  (implies (and (fn-bpn-lifecycle-invariantp st) (fn-bpn-machine-eventp event)
                (member-equal (list :persist token (list :deleted id :lifetime-expired)) EFFECTS))
           (and (equal (car event) :clock)
                (equal (fn-bpn-held-expiry HELD (nth 1 event)) :expired))))

(defthm fn-bpn-uncertain-clock-deletes-nothing
  (implies (and (fn-bpn-lifecycle-invariantp st) (fn-clock-observationp obs)
                (not (fn-clock-has-wall obs))
                (fn-bpn-no-anchors-p (fn-bpn-machine-state-held st)))
           (not (fn-bpn-deletion-proposedp (fn-bpn-answer-effects (fn-bpn-step st (list :clock obs)))))))
```

`fn-bpn-held-expiry` is `fn-clock-expiry-decision` over the entry, so the
first theorem's conclusion is the clock book's word, and
`fn-clock-expiry-is-monotone-in-local-time` (`clock-invariants.lisp:145`)
carries over: a bundle once `:live` cannot expire under a clock that merely
became less sure. M3 (`fn-bpn-find-expired-requires-expired-decision`) is the
selection half and stays. Teeth: (no-wall) an anchored entry with a wall-less
observation past its lifetime is deleted (the age path needs no wall); (no
anchors) an unanchored entry with a confident wall past its lifetime is
deleted.

### T4. Fragmentation and reassembly are inverse

```lisp
(defthm fn-bpn-fragment-then-reassemble-is-identity
  (implies (equal (car (fn-bpf-fragment payload boundaries)) :ok)
           (equal (fn-bpf-reassemble (cadr (fn-bpf-fragment payload boundaries)) (len payload))
                  (list :ok payload))))

(defthm fn-bpn-fragment-primaries-share-the-key-and-unfragment-to-the-parent
  (implies (and (fn-bpp-blockp p) (fn-bpf-fragmentablep p)
                (fn-bpf-boundariesp boundaries 0 total) (natp total))
           (and (fn-bpn-all-equal (fn-bpp-adu-key p)
                                  (fn-bpn-map-adu-key (fn-bpn-fragment-primaries p boundaries total)))
                (equal (fn-bpn-unfragment (car (fn-bpn-fragment-primaries p boundaries total))) p))))
```

The first needs the two lemmas commented out in `bp-fragment-invariants.lisp`
(`fn-bpf-cut-covers` at `:427`, `fn-bpf-reassemble-ok-agrees-with-every-fragment`
at `:248`), which are packet 2's and the first thing the phase-2 lane proves,
and then follows from `fn-bpf-complete-agreeing-cover-reassembles-to-payload`
(`:188`) with `fn-bpf-cut-agrees` (`:407`) and `fn-bpf-cut-same-total` (`:413`).
The second uses `fn-bpf-fragment-block-preserves-adu-key` (`:437`) and the new
`fn-bpn-unfragment` (clear the fragment flag, drop the two fragment fields,
recompute the CRC). Teeth: a boundary list that is not ascending is
`(:invalid :bounds)` and reassembles to nothing; a cover with a gap answers
`(:missing lo hi)`.

### T5. A status report is only a transport observation

```lisp
(defthm fn-bpn-administrative-bundle-yields-only-a-transport-observation
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-cbor-octet-listp octets) (fn-clock-observationp obs)
                (fn-cbor-result-okp (fn-bpb-decode octets (fn-bpn-config-transfer-limit (fn-bpn-machine-state-config st))))
                (fn-bpp-administrativep (fn-bpp-flags (fn-bpb-bundle-primary (fn-cbor-result-value (fn-bpb-decode octets ...)))))
                (fn-bpn-local-destination-primaryp st (fn-bpb-bundle-primary (fn-cbor-result-value (fn-bpb-decode octets ...)))))
           (let ((effects (fn-bpn-answer-effects (fn-bpn-step st (list :bundle-received octets origin obs)))))
             (and (fn-bpn-only-transport-and-observed-effects effects)
                  (not (fn-bpn-effect-kind-memberp :deliver effects))
                  (not (fn-bpn-effect-kind-memberp :persist effects))
                  (equal (fn-bpn-answer-state (fn-bpn-step st (list :bundle-received octets origin obs))) st)))))

(defthm fn-bpn-transport-observation-cannot-close-a-work
  (implies (and (fn-bp-statep wf) (fn-bp-work-outstandingp (fn-bp-find-work work-id (fn-bp-state-works wf))))
           (fn-bp-work-outstandingp
            (fn-bp-find-work (fn-bp-result-state (fn-bp-step wf (fn-bp-transport-event work-id attempt-id generation status)))
                             work-id))))
```

The second is the composition with the workflow and is a corollary of
`fn-bp-observe-transport-never-moves-status-backward`
(`books/bp-workflow-transport-invariants`); it is stated in
`tests/acl2/bp-node-machine-teeth-tests.lisp`, which may include
`bp-workflow-transport-invariants` (a test book's closure is its own), not in
the machine's book, so the machine's closure stays clear of the store codec.
Teeth: (administrative) the same octets with the flag clear are stored and
dispatched; (local destination) an administrative bundle for another node is
stored and forwarded; (workflow) a `:receipt-prepare` event, not a transport
one, closes the work.

### T6. State, replay, restart

```lisp
(defthm fn-bpn-step-preserves-lifecycle-invariant      ; PRF-046, restated over the new record
  (implies (and (fn-bpn-lifecycle-invariantp st) (fn-bpn-machine-eventp event))
           (fn-bpn-lifecycle-invariantp NEXT)))

(defthm fn-bpn-trace-preserves-lifecycle-invariant
  (implies (and (fn-bpn-lifecycle-invariantp st) (fn-bpn-machine-event-listp events))
           (fn-bpn-lifecycle-invariantp (fn-bpn-trace st events))))

(defthm fn-bpn-step-cl-send-is-authorized-by-durable-attempt-record   ; PRF-046, restated: :attempting is kind 9
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-effect-kind-memberp :cl-send EFFECTS))
           (let* ((pending (fn-bpn-machine-state-pending st)) (record (fn-bpn-pending-record pending)))
             (and pending (equal (car event) :persist-result)
                  (equal (nth 1 event) (fn-bpn-pending-token pending)) (equal (nth 2 event) :durable)
                  (equal (fn-cbor-ag-car record) :attempting)
                  (fn-bpn-record-applicablep st record)
                  (equal EFFECTS (fn-bpn-pending-success-effects pending))
                  (fn-bpn-proposal-effectsp st record (fn-bpn-pending-success-effects pending)
                                            (fn-bpn-pending-refusal-effect pending)
                                            (fn-bpn-pending-uncertainty-effect pending))))))

(defthm fn-bpn-step-queue-acceptance-is-durable-or-exact-duplicate   ; PRF-046, restated: :queued is kind 5, the key is the origin
  ...as today with (list work attempt generation) replaced by origin and fn-bpn-job-exactp by fn-bpn-held-exactp...)

(defthm fn-bpn-restart-reanchors-every-held-bundle
  (implies (and (fn-bpn-lifecycle-invariantp st)
                (fn-bpn-machine-eventp (list :restart records ready obs))
                (equal (car (car (fn-bpn-answer-effects (fn-bpn-step st (list :restart records ready obs))))) :restart-ready)
                (member-equal h (fn-bpn-machine-state-held (fn-bpn-answer-state (fn-bpn-step st (list :restart records ready obs)))))
                (consp (fn-bpn-held-anchor h)))
           (and (equal (fn-clock-anchor-monotonic (fn-bpn-held-anchor h)) (fn-clock-monotonic obs))
                (equal (fn-clock-anchor-age (fn-bpn-held-anchor h))
                       (fn-bpn-durable-age-of records (fn-bpn-held-id h)))
                (null (fn-bpn-held-attempt h)))))
```

`fn-bpn-durable-age-of` folds the records: the `:bundle-stored` anchor age,
raised by every `:attempting` record's `age`. Bundle ids are unique by
`fn-bpn-held-listp` (a recognizer conjunct, not a theorem). The replay
theorem belongs to T12b and is stated here so both lanes state the same
thing:

```lisp
(defthm fn-bpn-live-state-is-replay-of-journal          ; T12b, books/bp-node-records or a sibling
  (implies (and (fn-bpn-machine-event-listp events)
                (fn-bpn-journal-of-trace-p journal base events))    ; journal = the :durable-confirmed records, in token order
           (equal (fn-bpn-machine-state-held (nth 1 (fn-bpn-replay-records base journal)))
                  (fn-bpn-resume-held (fn-bpn-machine-state-held (fn-bpn-trace base events))))))
```

in the shape of `fn-bpr-live-state-is-replay-of-journal` (PRF-012's last
event). Teeth: (restart) a record list with a token gap is `(:restart-fault
:lifecycle-record)` and the state is fenced; (reanchor) an entry whose
`:attempting` age is larger than its stored age re-anchors to the larger;
(cl-send) the four `must-fail`s of `bp-node-machine-authorization-tests.lisp`
carried over.

## 6. K6: the delivered ADU's admission is the transit decision

K6 in [peering §1.4](peering.md) says the BP peer is the same profile over
another convergence layer: the same peer record (`fn-cfg-peerp` with `(:bp
eid)`, `peer-config.lisp:160`), the same decision `fn-peer-decide-transfer`,
the same acceptance path, the same provenance record, the same history
predicate, and Path plus Previous Node as the loop check.

What the machine hands the store is the `:deliver` effect: `(:deliver id
adu-key payload origin report-p)`, where `payload` is the request ADU's
octets and `origin` is `(:cl xfer-id peer-eid)`. The host runs it under the
owner mutex through the application join (`fnn-bpapp-accept-locked`,
`bp-app.lisp:74`, the same loop as today), and the join's admission changes
in one place. Today `fn-bpaj-dispatch` (`bp-native-app.lisp:376-406`) answers
`(:submit)` when the intent is current and `fn-bpaj-record-lookup` finds no
record for the article's Message-ID; its article gate is
`fn-bpaj-article-fields` (`:289-301`: parse, `fn-af-proto-article-check`,
Message-ID and groups present); scope, loop, capacity and the peer's
existence are not asked there, and its duplicate test is a scan of
`fn-sf-records` that is the BP-side twin of `fn-peer-history-hasp`
(`peer-inbound.lisp:277`). After K6:

```lisp
(defun fn-bpaj-transit-peer (cfg source-eid) ...)   ; the configured peer whose (:bp eid) transport row is source-eid, or nil
(defun fn-bpaj-admission (node cfg joined store request-octets origin clock generation)
  ;; (:submit args) | (:bind record) | (:refused reason) | (:busy) | (:persist-intent) | ...
  ;; the :submit and :bind arms are decided by fn-peer-decide-transfer:
  ;;   :want   -> (:submit (fn-peer-injection-arguments node cfg peer msgid octets generation id subject))
  ;;   :have   -> (:bind (fn-bpaj-record-lookup store request))   ; the exact committed record, for the FNRJ context
  ;;   :refuse -> (:refused reason)
  ;;   :defer  -> (:busy)
  ...)
```

with `peer` the transit peer of the origin's session EID, `octets` the
request's article, `msgid` the parsed Message-ID, `id` and `subject` the
identity the owner derives (`owner-host.lisp:639`, `:bad` refuses), and
`clock` the owner's observation. The theorem, phase 3, in
`books/bp-native-app-invariants.lisp` (new; the join's invariant book, which
does not exist today):

```lisp
(defthm fn-bpaj-submit-is-the-transit-decision
  (implies (and (fn-bpaj-statep joined) (fn-sn-statep store) (fn-node-statep node) (fn-cfgp cfg)
                (equal (fn-bpaj-request-status joined request-octets) :intent)
                (equal generation (fn-bpaj-request-generation joined request-octets)))
           (iff (equal (car (fn-bpaj-admission node cfg joined store request-octets origin clock generation)) :submit)
                (equal (fn-peer-decision-kind
                        (fn-peer-decide-transfer node cfg (fn-bpaj-transit-peer cfg (fn-bpn-origin-peer origin))
                                                 (fn-bpaj-msgid request-octets) (fn-bpaj-article request-octets) clock
                                                 (fn-bpaj-id request-octets) (fn-bpaj-subject request-octets)))
                       :want))))

(defthm fn-bpaj-submitted-arguments-are-the-post-path-arguments
  (implies (equal (car (fn-bpaj-admission ...)) :submit)
           (equal (cadr (fn-bpaj-admission ...))
                  (fn-peer-injection-arguments node cfg peer msgid octets generation id subject))))
```

The second is the BP side of `fn-peer-transfer-is-the-post-path`
(`peer-inbound-invariants.lisp:23`): what the owner installs for a BP-delivered
article is `fn-node-prepare` of the same arguments the NNTP transit installs,
and the owner-level half is `fn-own-take-installs-the-queued-submission-whatever-it-carries`
(`owner-invariants.lisp:1557`), unchanged. The equality theorem the peering
packet asks for, between the old and the new decision on the reachable set,
is:

```lisp
(defthm fn-bpaj-old-submit-implies-want-on-configured-peers
  (implies (and ...the hypotheses above...
                (fn-bpaj-transit-peer cfg (fn-bpn-origin-peer origin))
                (equal (fn-bpaj-dispatch joined store request-octets generation) (list :submit)))
           (or (equal (fn-peer-decision-kind (fn-peer-decide-transfer ...)) :want)
               (member-equal (fn-peer-decision-reason (fn-peer-decide-transfer ...))
                             '(:loop :out-of-scope :capacity :no-inbound :oversize :no-date)))))
```

that is, the new decision refuses only what the old one never asked (loop,
scope, capacity, inbound allowance, size, date), and never refuses what the
old one accepted for another reason. Provenance: `fn-prov-make-bp`
(`bp-native-app.lisp:325`) keeps recording `(:bp-receive node bundle-id
policy)`; the `kind` formal RET-007 asks for on `fn-peer-decide-transfer`
stays that row's open item and K6 does not take it.

Two facts bound this: `fn-peer-transfer` has no production caller (the owner
decomposes it, `owner-host.lisp:641-644`, with `generation` fixed at 0), so
K6 is stated over the decision and the arguments, not over `fn-peer-transfer`;
and `books/bp-native-app` is red at its current digest and opens the record
codec book-wide (`theory_check`), so the K6 edit waits for T1's BP-receiver
cluster (phase 1) and is the last batch of the phase-2 lane (§11.1).

## 7. Reassembly, fragmentation, routes, reports

### 7.1 Reassembly, bounded

`fn-bpn-fragments-of st key` is the held entries whose primary is a fragment
with ADU key `key`, in token order, projected to `fn-bpf-make offset payload
total`; it is a walk of at most `max-held` entries and is called once per
received fragment (§4.2). `fn-bpf-reassemble` refuses more than
`*fn-bpf-max-fragments*` (64) fragments or a total over `*fn-bpf-max-length*`
(65536) as `(:invalid :bounds)`, which the dispatch maps to `(:deleted ...
:block-unintelligible)` for the offending fragment. The fragment bound is
two octets below `*fn-bpa-max-octets*` (65538), so an fn request ADU of the
two largest sizes cannot be reassembled (§13, F5); the lane raises
`*fn-bpf-max-length*` to `*fn-bpa-max-octets*`, both being its books'
constants, and re-certifies `bp-fragment*`.

A reassembled entry is a new record (kind 7) rather than an edit of the
offset-zero fragment, so that the journal reads as RFC 9171 §5.9 and the
fragments' fate (discardable) is the ordinary one.

### 7.2 Fragmentation, proactive only

When an entry's wire exceeds the next hop's transfer MRU
(`fn-bpn-route-cl`'s sixth slot) and the bundle is fragmentable,
`fn-bpn-fragment-plan st entry mru` chooses boundaries every `mru -
overhead` payload octets, where `overhead` is the encoded size of the
primary block, the replicated blocks and the payload block head (a bound the
codec book states as `*fn-bpn-fragment-overhead*`), so that every fragment's
image fits; blocks flagged replicate-in-fragments go in every fragment and
all blocks in the first (RFC 9171 §5.8). Each fragment is a held entry with
the parent's origin, `:forward-pending` and the same next hop; the parent
is deleted `:no-additional-information` after the last fragment's record.
Bounded by `*fn-bpf-max-fragments*`; a bundle that would need more is
contraindicated (`:forward-refused id peer :fragment-count`) and waits.
Reactive fragmentation after `No Resources` is packet 7's, unchanged.

### 7.3 The routing table's provenance

The table's shape is §2.4. Its source is configuration, in two steps:

- Phase 2 (this step): the host installs one route built from the same
  command-line arguments `bp-service run` takes today (`bp-service.lisp:347-350`)
  plus the peer's EID, so the machine decides from a table and the host
  computes nothing new; the row family below is defined and read but not yet
  written by a verb.
- T12c (phase 4): the rows live in the configuration's peers slot under the
  existing `:set-peer` kind (`config.lisp:644-647`), keyed by peer name, with
  slot labels the reader book `books/bp-routes.lisp` (new, `fn-bpn-route-*`)
  understands: `"transport-bp"` (exists, `peer-config.lisp:281`; `c` is the
  EID), `"bp-cl-host"` (`c` host, `n` port), `"bp-cl-params"` (`c` expected
  node ID, `n` keepalive), `"bp-cl-mru"` (`n` segment MRU, a second row for
  the transfer MRU), and one `"bp-reach"` row per reachable node ID (`c`).
  `fn-bpn-routes-of-config cfg` folds `fn-cfg-peers` into `fn-bpn-route-listp`,
  and the keystone is that every route read from an admissible configuration
  is an `fn-bpn-routep` address with a `fn-bpp-eidp` peer. Because `:set-peer`
  replaces the whole row group, the operator verb that writes BP rows
  composes the peer's current group with them (an ACL2 function in
  `bp-routes`, not host code); the typed record `fn-cfg-peerp` gains the BP
  fields after T9b (phase 3) has certified the row round trip, and until
  then a `peer set` verb that rewrites the group from the typed record would
  drop BP rows, which is why the verb is T12c's and not phase 2's.

No new delta kind is added in phase 2 (§12, Q3): `books/config` is in the
closure of the owner and the admin books, and a new kind there in the same
phase as T2 is a red umbrella nobody in the BP lane owns. Contact windows are
not configuration in this design; they are the scheduler's observations
(§8), and R7 of [reconfiguration](reconfiguration.md) stays open with its
seam until T12c decides whether a timed plan is needed on one box.

### 7.4 Status reports are bundles this node authors

RFC 9171 §6.1.1. A report is an administrative record whose payload is
`[1, [status-info, reason, source, creation-timestamp, [offset, length]?]]`
with each of the four status assertions a boolean and no status time (fn
never asserts "report status time"). `books/bp-status-report.lisp` (new,
`fn-bpn-report-*`, over `bp-primary-cbor`) defines
`fn-bpn-report-make`, `fn-bpn-report-encode`, `fn-bpn-report-decode` (bounded,
exact, canonical, in the pattern of `fn-bpa-decode-exact`) and
`fn-bpn-report-subject` (the ADU key it names, with the fragment fields when
present), with `fn-bpn-report-round-trip` and
`fn-bpn-report-accepted-input-is-canonical`, and the reason table (Table 1
codes 0 to 11 as keywords). The report bundle's primary has the
administrative flag, `no-fragment`, destination the subject's report-to EID,
source and report-to this node's ID, the configured lifetime, and no report
requests of its own (a report about a report is never asked); its blocks are
`fn-bpn-send-blocks` (hop count and age, as for any bundle fn authors).

Generation is the `:report-due` effect at each of the four points (§4.1
reception, §4.3 forwarding, §4.2 delivery, §4.4 deletion), when the
subject's flags request it (`*fn-bpp-flag-report-*`, `bp-primary.lisp:200-203`)
and `fn-bpn-policy-reports` is set, and the host's `:author-report` after a
sequence reservation. A crash between the two loses the report, which is
allowed: reports are never evidence (T5), RFC 9171 makes their generation
a MAY, and the workflow's receipt is what discharges anything. There is no
`reports` state field and no report record kind: a report is a held entry
of origin `(:report subject assertion)` and its record is kind 5.

Parsing is §4.1 step 4. A report is consumed only when it is addressed to
this node; a report in transit is a bundle like any other.

## 8. The scheduler question (D07), decided

The two admissible answers were `books/scheduler` called from the native
host, or `bp-node-machine`'s contact model proved to be the scheduler's. The
facts: `fn-sched-step ss wf event` (`scheduler.lisp:719`) takes the sender
workflow image and drives `fn-bp-step` for the attempt whose `:submit` it
selects; its queue items are works with a class and a size; its contact is
one `(peer start end)` window; its retry budget is per contact and per
attempt; its keystones (`fn-sched-step-preserves-queued`,
`fn-sched-retries-stay-within-the-contact-bound`, `fn-sched-aging-bound`,
the conditional progress under `fn-assume-fairness-contact-index`) are
about which *work* gets an *attempt*. `fn-bpn-contact-openp` is a membership
flag over EIDs with no window; `fn-bpn-find-queued-for-peer` is first-fit; the
machine counts no retries. They are not two models of one thing: one
decides attempts, the other carries bundles.

**Decision: `books/scheduler` is called from the native host, per peer
through `books/scheduler-peers` (`fn-sched-table-step`, `:154`;
`fn-sched-table-tick-is-the-peer-tick`, `:186`), and the node machine does
not select attempts.** The division:

- The scheduler decides, under a contact and its retry budget, which
  outstanding work is attempted now; its `:submit` effect becomes the
  machine's `:transmit` (the bundle is created). It is the RFC's "application
  agent requests transmission" (§5.2), and every scheduler keystone applies
  verbatim.
- The machine forwards every forward-pending bundle for an open peer, oldest
  first, until it is sent, expires or is deleted (§4.3). That is RFC 9171
  §5.4, not a second scheduler: there is no retry count to bound because a
  bundle's lifetime is its bound, and there is no fairness question among
  bundles for one peer because every one is sent while the contact holds.
  The property phase 3 states about it is
  `fn-bpn-start-one-selects-the-oldest-forward-pending-entry`, a FIFO fact.
- The scheduler's `:contact-open`/`:contact-close` are the machine's
  `(:contact peer open-p obs)`; the host relays an ACL2 effect to an ACL2
  event and decides nothing. The `t` at `bp-service.lisp:318` is retired with
  it. Until T12c lands, phase 2's host keeps that line and this document
  names it as the twin it is (§13, F2).
- A requeued bundle (`:forwarded ... (:refused code)` or `:failed`) leaves
  the work in `:attempted`, which is not retryable
  (`fn-bp-retryable-statusp`), so the workflow does not make a second bundle
  while the first is still carried; `:expired` and `:deleted` are retryable
  and do.
- `fn-bp-transport-statusp` still carries the four BPA-era statuses
  (`:bpa-submit-replied`, `:bpa-accepted`, `:inbound-persisted`, `:dequeued`)
  and lacks `:bundle-created`; that is packet 6, T12c's, and the machine
  emits only statuses the workflow accepts today until then (§3.2).

`tools/scheduler.py` retires when T12c's host call lands; its plan-file
format goes with it. What the machine does not prove is that the scheduler's
contact is the machine's contact: that is the composed-trace statement of
T12c (`fn-bps-run`, the service loop as a machine), owed with the gate.

## 9. What the host must do

Per transition, in I/O terms, over today's files. The phase-2 lane edits
`host/native/bp-service.lisp`, `host/native/tcpcl.lisp` and
`host/bp-node-machine-host.lisp`; `host/native/bp.lisp`'s one-shot verbs are
unchanged (§10, the oracle table).

### 9.1 Reception

- `*fnn-tcl-deliver*` is bound by the service to a callback that issues
  `(:bundle-received octets (:cl xfer-id peer) obs)` through `fnn-bps-step`
  and drives the effects: `:persist` publishes kind 5 under the ACL2 name
  with `fnn-immutable-publish-effect` (write, fsync, link, fsync directory)
  and answers `:persist-result`; `:receive-stored`, `:receive-duplicate`,
  `:receive-observed` and `:receive-refused` return normally so
  `tcpcl.lisp:267` releases the held ack; `:receive-uncertain` raises
  `fnn-store-indeterminate` so `tcpcl.lisp:259` drops it. The receive-evidence
  namespace is not written on this path (§10).
- At XFER_SEGMENT START with a Transfer Length Extension, the session calls
  `(fn-bpn-transfer-admissiblep st n)` and refuses `No Resources`
  (`*fn-tcl-refuse-no-resources*`) when it answers nil; the TCPCL machine
  already has the refusal path, the host adds the query.
- The `:dispatch` proposal that follows kind 5 is one more `:persist` in the
  same effect list; the ack is released on `:receive-stored`, before it.

### 9.2 Delivery

- `:deliver` runs the application join under the owner mutex exactly as
  `fnn-bpapp-accept-locked` does today, with `fn-bpaj-admission` (§6) in
  place of `fn-bpaj-dispatch`'s `:submit` arm; the outcome the join reports
  (`:accepted`, `:duplicate`, `:refused reason`, uncertain when the owner
  fenced) is the `:deliver-result`.
- When `report-p`, reserve a sequence (`fnn-bp-reserve-sequence`) before
  answering, and issue `:author-report` after `:delivered` is durable.
- The application's receipt bundle is no longer authored at `bp-app.lisp:188`
  and parked at `:196`: the join hands the receipt ADU back and the host
  issues `(:transmit (:receipt id) peer-eid sequence adu obs)`. It is then a
  held entry forwarded on the next contact with that peer, which may be the
  session that delivered the request (§9.3).

### 9.3 Forwarding

- One TCPCL session per open contact, kept for the contact's duration: on
  `(:contact peer t obs)` the host connects (or accepts) once; on each
  `:cl-send` it offers `wire` as the session's pending bundle
  (`fnn-tclc-pending`, the mechanism `bp-app.lisp:196` uses) and waits for
  `:outbound-sent`, `:outbound-refused` (with its Table 6 code) or
  `:outbound-failed`, answering `:forward-result` with `:sent`, `(:refused
  code)` or `:failed`; a session that ends without an outcome answers
  `:uncertain`. After each answer, while the session is established, issue
  `(:resume peer obs)`; on session end issue `(:contact peer nil obs)`.
- A passive session from a configured peer opens the contact for that peer
  for its duration, so a receipt can ride back on the session that delivered
  the request; the scheduler's open/close (T12c) is the other source.

### 9.4 Authoring, clock, routes, restart

- `:transmit` from the workflow's `:submit`: reserve the sequence first, as
  `bp-service.lisp:338-346` does today (reusing an existing entry's sequence
  by origin, `fn-bpn-existing-sequence`).
- `:clock` from the service loop, repeated while it produces effects, as
  today (`:314-316`); `:report-due` reserves a sequence and issues
  `:author-report`.
- `:routes` at open and on every configuration generation change, from the
  table `fn-bpn-routes-of-config` computes (phase 2: the one route from the
  command line).
- `:restart` as today (`fnn-bps-open`, `:245-300`), with the observation
  added.

### 9.5 What the developer-image tests measure (phases 2 and 3)

`tests/test_bp_service_native.py` grows one test per transition on the
developer DTN image built by `hbox-image-build.sh`, each an outage/restart
witness in the shape the four lifecycle tests have today:

1. receive, dispatch, deliver on loopback between two images: one article
   accepted at the destination, one archive pin, the `:bundle-stored`,
   `:dispatched`, `:delivered` records in that order, the ack released after
   the first;
2. relay: an image whose routing table names the destination through a third
   image forwards with the Previous Node inserted and the Bundle Age raised;
3. reassembly: two fragments authored by `bp decode`'s inverse harness
   reassemble to the golden ADU; a gap holds `:await-fragments`; a conflict
   deletes;
4. expiry sweep on a short-lifetime bundle with the report requested: one
   `:deleted`, one report bundle authored, the workflow's work outstanding;
5. restart mid-attempt: the entry is re-anchored to the recorded age and the
   restart monotonic, re-sent once, exactly one copy at the peer;
6. discard: after `:sent` the entry is gone on the next sweep and a
   sixty-fifth bundle is accepted;
7. an administrative record for the node: no record written, one
   `:transport` line;
8. capacity: the sixty-fifth concurrent bundle is refused `No Resources` at
   START.

### 9.6 The T12c gate on one box

Two DTN images and a relay (three processes on hbox; ember's decision 8),
the four-node lab's shape without the mock BPA: home posts, the relay's
contact to home opens then closes, its contact to the destination opens
later; measured: exactly one article and one pin at the destination, the
relay's `:forwarded` record naming the destination peer, the receipt bundle
back through the relay and `fn-bprl-release-decision` (T12d) at home. Then
the three rows the v0.3 row asked for: an interrupted contact (`kill -9` of
the relay inside a transfer: the transfer fails at the sender (C3), is
re-offered on the next contact, and the destination holds one copy); an
expiry (a bundle held at the relay past its lifetime is deleted with a
deletion report to home, and home's workflow retries with a distinct
transport identity); staging exhaustion (the relay at `max-held` refuses `No
Resources`, the sender's entry stays forward-pending, and it is accepted
after a discard frees a slot). Each row is a named assertion in the record
`planning/evidence/bp-gate-<rev>-2026-09-xx.md`, with the counts from the
journals and the reason codes from the machine, never from the log.

## 10. The checkpointed branches

Measured with `git log dev..<branch>` and `git diff --stat dev...<branch>`
against `dev` `722c9566`. Every `defun` and `defthm` the five named branches
add is on `dev` by name (50 of 50, 93 of 93, 132 of 132, 39 of 39, 12 of 12);
where a book differs, the branch holds the older text.

| Branch | What it contributes, on `dev` today | What is dropped, by name |
| --- | --- | --- |
| `w12/bp-sequence` (16 ahead) | kind 1, `fn-bpn-sequence-reserve-advances-frontier`, the persistence-cut model `fn-bpn-sp-trace-authored-sequences-unique` | its `frame-journal.lisp` with `*fn-frame-max-store-payload*` at 65538 and no `:request-intent`/`:request-context-v2`; `fnn-bp-record` in `host/native/bp.lisp`; the deploy-gate tooling half, which `dev` has |
| `w13/bp-lifecycle` (8 ahead) | `fn-bpn-step`, the proposal machine, M1 to M3 | `fn-bpn-contact-step` without the fenced/pending guard that `f4d061d2` added; `fnn-bps-frame-name-p`, `fnn-bps-record-names`, `fn-bpn-host-machine-max-records`, `fn-bpn-host-machine-statep`, superseded by `w17/bp-namespace` and `w18/bp-publisher` |
| `w18/bp-lifecycle-assurance` (5 ahead) | PRF-046's three keystones, `fn-bpn-lifecycle-invariantp`, the four `must-fail` teeth; byte-identical to `dev` | nothing; delete with a landing note naming `f4d061d2 ec64c5d3 29c8d8b2 ff80403e 3a7ef781` |
| `w19/bp-app-fast-invariant` (7 ahead) | the fourteen `fn-bpaj-*-fast-is-checked` correspondences and `fn-bpaj-successful-replay-has-statep`; the checked/fast pattern §2.5 reuses | `fn-bpaj-config-status-fast` without the reachable `(null joined)` arm `dev` has; `51a0b1a3`, patch-equivalent to `dev`'s `6708e238` |
| `w19/bp-authored-wire` (8 ahead) | `fn-bpn-authored-wire-authorize-carries-reservation` and its three teeth; byte-identical to `dev` | nothing; delete |
| `w25/bp-obligation-vertical` (13 ahead; not in the brief, found by the audit) | **unlanded ACL2**: `books/bp-release-owner.lisp` (`fn-bprl-owner-join` and three theorems), `books/bp-release-store.lisp` (`fn-bprl-store-join` and three), and `fn-bprl-release-record`, `fn-bprl-replay-records`, `fn-bprl-replay-journal` in `books/bp-release.lisp` | **T12d's brief takes all three files as its starting point**; `host/bp-release-owner-host.lisp:8` on `dev` calls `fn-bprl-replay-journal`, which only this branch defines (§13, F7) |

Zero-ahead and superseded BP branches (`w10/dtn-3`, `w11/bp-node`,
`w11/tcpcl-*`, `w13/bp-convergence`, `w14/bp-sequence-fidelity`,
`w15/bp-receive-integrity`, `w17/bp-namespace`, `w18/bp-evidence-bounded`,
`w18/bp-publisher` but for four host lines root reads before deleting,
`w18/native-bp-app`, `w19/bp-authored-wire-pre-rebase`,
`w25/bp-authoritative-integration`, `w25/native-efficiency`, and the
2026-09-18 to 09-20 `w2`, `w4`, `w5`, `w6`, `w8`, `w9` branches) hold nothing
`dev` lacks and are deleted in the phase-2 landing note.

The packet-5 question the plan's §5.3 assigns here, which Python BPA tools
survive as development oracles under D07: `tests/bp-dtn7/mock_bpa.py`,
`run_four_node_lab.py`, `lab_bpa.py`, `bp_fn_ingress_driver.py`,
`fn_sender_lab.py`, `run_fn_exchange_lab.py`, `run_fn_ingress_lab.sh`,
`run_two_node.sh`, `tools/bpa_dtn7.py`, `tools/bpa_payload_extract.rs` and
`build_payload_extractor.sh` survive until the T12c gate record exists,
because the four-node lab is the only run of the interrupted-contact shape
today; they are deleted in T12c's landing note. `tests/bp-dtn7/bootstrap.sh`,
`pin.json`, `run_fn_bp_interop.py`, `run_fn_tcpcl_interop.py`,
`run_fn_bp_sequence_durability.py`, `run_fn_tcpcl_spool_recovery.py`,
`run_fn_bp_authored_wire.py` and `tools/tcpcl_lab.py` drive the native image
against a peer and stay. `bp send`, `bp receive` and `bp decode`
(`host/native/bp.lisp`) stay as the interop harness's verbs until T13
re-points `run_fn_bp_interop.py` at `bp-service`; the receive-evidence
namespace (`books/bp-receive-evidence.lisp`) stays with `bp receive` and is
not written by the machine path, whose kind-5 record carries the wire.

## 11. The two briefs

### 11.1 Phase 2, hbox lane 2: the machine

Shape per [how we work](../planning/how-we-work.md). Model: Fable (the plan's
tier for T12a).

**Books you edit, and nothing else:** `books/bp-node-machine.lisp`,
`books/bp-node-machine-invariants.lisp`, `books/bp-node-machine-authorization.lisp`,
`books/bp-node-machine-codec.lisp`, `books/bp-fragment-invariants.lisp` (the
two lemmas at `:248` and `:427`), `books/bp-fragment.lisp` (the length bound
only), new `books/bp-status-report.lisp`, new `books/bp-routes.lisp`,
`tests/acl2/bp-node-machine-tests.lisp`,
`tests/acl2/bp-node-machine-authorization-tests.lisp`, new
`tests/acl2/bp-status-report-tests.lisp`, `host/bp-node-machine-host.lisp`,
`host/native/bp-service.lisp`, `host/native/tcpcl.lisp` (the capacity query,
the multi-offer session, the ack on `:receive-stored`),
`tests/test_bp_service_native.py`, `docs/prefixes.md` (the `fn-bpn-` row
gains `bp-node-machine*`, `bp-receive-evidence`, `bp-status-report`,
`bp-routes`). Last batch, gated on `books/bp-native-app` being green from
T1's BP-receiver cluster: `books/bp-native-app.lisp` (`fn-bpaj-admission`,
§6) and `host/native/bp-app.lisp` (§9.2). `books/bp-node.lisp` is not edited;
if a definition there must move, that is a finding you report.

**Include closure:** `bp-node-machine-codec` is 61 books (`bp-node`,
`bp-bundle*`, `bp-primary*`, `clock`, `defrecord`, `frame-fields`,
`frame-trailer`, `journal-publish`, `byte-store-txn-name` and under them);
`bp-node-machine` is in the closure of five books and `host/bp-node-machine-host`.
`bp-native-app` is 97 books (it includes `owner`); do not include it or
`bp-workflow` from the machine's books.

**Ground truth to paste into your first session, not to re-derive:** the
state, job, pending and answer records at `bp-node-machine.lisp:64-80,
228-239, 253-279, 294-301`; `fn-bpn-propose` `:369-378`;
`fn-bpn-persist-result-step` `:494-520`; `fn-bpn-lifecycle-invariantp`
`bp-node-machine-authorization.lisp:90-109`; `fn-bpp-adu-key`,
`fn-bpp-bundle-id`, `fn-bpp-administrativep`, the flag constants
`bp-primary.lisp:195-203, 217, 702, 709`; `fn-bpb-bundle-age`,
`fn-bpb-bundle-hop-count`, `fn-bpb-bundle-previous-node`, the three block
constructors `bp-bundle.lisp:676-729`; `fn-bpf-fragment (payload boundaries)`
`bp-fragment.lisp:348`, `fn-bpf-reassemble (fs total)` `:282`,
`fn-bpf-boundariesp (bs from limit)` `:326`; `fn-clock-expiry-decision`
`clock.lisp:212`, `fn-clock-age-anchorp` `:125`; the TCPCL events
`(:bundle-received xfer-id data)` `tcpcl-session.lisp:715`, `fn-tcl-send (s
ref octets now)` `:862`, `(:outbound-sent xfer-id ref)`, `(:outbound-refused
xfer-id ref reason)` `:741`, `(:outbound-failed xfer-id ref)` `:386`, the
refuse codes `:43-49`; the host entry `bp-service.lisp:110-116` and the
callback contract `tcpcl.lisp:91-102`.

**Order of batches, each certified before the next:** (1) `bp-fragment*`:
the two lemmas and T4's first theorem, the length bound; (2) the records and
state (§2, §3.3) with the codec kinds 5 to 12 and the recovery plan, the
existing 118 theorems re-established over the new record, the four
authorization teeth carried; (3) the transitions (§4) and `fn-bpn-step-fast`
with `fn-bpn-step-fast-is-step`; (4) `bp-status-report` and `bp-routes`;
(5) the host, the developer-image tests of §9.5; (6) K6's definition change.
Batch 2 is the one that touches every theorem; do it in a live session
(`proof_repl.py start bpnm books/bp-node-machine-invariants --upto
fn-bpn-machine-statep-components`) and expect the `-of-constructor` and
`-components` lemmas to be regenerated rather than repaired.

**Box and certification:** hbox, `swarm-build` around every build,
`tools/acl2` for every session; `python3 tools/farm.py submit hbox
--remote-root /tank/fn/lanes/t12a-bp-machine --affected-by
books/bp-node-machine --closure` at 300 s per book for discovery and 1800 s
once for the final closure; then `python3 tools/green_check.py
--changed-since dev --strict` in the worktree. A book that needs more than
300 s is a finding you report with the theorem named.

**Size:** 8 to 12 lane-days, the plan's estimate; batch 2 is 3 to 5 of them.

**Evidence file:** `planning/evidence/bp-node-machine-<rev>-2026-09-xx.md`
with the farm run ids and manifests, the `green_check` line, the image built
from the frozen tree, the eight tests of §9.5 with their counts, and what you
did not do.

**Report:** the theorem statements (not names) certified so far, the host
lines, the teeth book, the farm run id and manifest, the evidence file, and
the list of §13's defects you closed or left.

### 11.2 Phase 3, hbox lane 2: the proofs

Same books, same box, same lane. **Theorems, in this order:** T6's
preservation pair and the two restated PRF-046 keystones (the umbrella every
other proof stands under), T3, T2, T1, T5's first theorem, T6's
re-anchoring, T4's second theorem, then K6's three in the new
`books/bp-native-app-invariants.lisp` and `fn-bpn-start-one-selects-the-oldest-forward-pending-entry`.
**Teeth:** `tests/acl2/bp-node-machine-teeth-tests.lisp`, one reachable
non-degenerate witness per theorem and one `must-fail` per hypothesis as §5
lists them, over `fn-bpn-trace` from the initial state; T5's composition
theorem lives there too. **Registry:** PRF-046's events become the restated
pair plus T6's preservation; a new target `PRF-05x` "The BP node machine
delivers, forwards, expires and discards only as RFC 9171 §5 says" carries
T1 to T5 with the hypotheses in one sentence each, and K6 is an event of
PRF-042 or a target of its own, root's call; PRF-038 gains the `events` key
it lacks (§13, F8); REP-006 stays `specified` until T12c's gate record.
**Size:** the plan's remainder of T12a's 8 to 12; T1 and T2 are the long
ones because they are stated over a persist effect and need the
authorization relation opened one kind at a time.

## 12. Questions for ember

Each with my recommendation; none is decided here.

1. **One list.** Fold the outbound job into the held bundle (§1), restating
   PRF-046's keystones over the new record, rather than composing a second
   machine beside the existing one. Recommend: yes.
2. **Kinds 2 to 4.** Retire them (the phase-2 codec refuses them at
   recovery) rather than reading them as legacy. No deployed node has a
   lifecycle directory (the DTN image has only run under tests; the persvati
   915 node runs no `bp-service`), so ENC-004's evolution rule has no store
   to protect here. Recommend: retire.
3. **The routing table's configuration home.** Rows under the existing
   `:set-peer` with a composing verb in T12c, typed-record fields after T9b
   (§7.3), rather than two new delta kinds in `books/config` in phase 2.
   Recommend: no new kind now; revisit in T12c if a timed contact plan wants
   `:set-contact`.
4. **The scheduler.** `books/scheduler` called natively per peer in T12c;
   the machine forwards FIFO and selects no attempts (§8). Recommend: yes.
5. **The ack.** Release the XFER_ACK on the durable kind-5 record, before
   the application decides, instead of after the whole owner submission as
   `bp-app` does today (§9.1). This is what bp-design §2.4 designed and what
   makes a peer's retry meaningful; the application's decision is the
   receipt's, not the ack's. Recommend: yes.
6. **Reports at v0.** Generate all four assertions when requested and
   policy-enabled, as bundles this node authors (§7.4); dtn7-rs requests
   delivery reports on every bundle it sends. Recommend: yes, with
   `fn-bpn-policy-reports` defaulting to `t` on the DTN image and `nil`
   otherwise.
7. **Fragmentation in phase 2.** Proactive cutting at the next hop's MRU
   (§7.2) alongside reassembly; without it an oversize bundle waits forever.
   Recommend: yes; the gate measures reassembly, lab I1 measures the cut.
8. **The receive-evidence namespace.** Not written by the machine path; the
   kind-5 record carries the wire and the token is the identity. Recommend:
   retire it with the `bp receive` verb in T13.
9. **`*fn-bpf-max-length*`.** Raise 65536 to `*fn-bpa-max-octets*` (65538)
   so every fn ADU can be reassembled (§13, F5). Recommend: raise; both are
   the lane's constants.
10. **T12b's order inside phase 2.** T12b states `fn-bpn-live-state-is-replay-of-journal`
    over kinds 5 to 12 after batch 2 of §11.1 merges, and starts with the
    sequence and cut work that needs no machine; stating it earlier means
    stating it over kinds 2 to 4 and proving it twice. Recommend: sequence
    it so.
11. **The `:resume` arm.** Keep it and make it reachable through the host's
    per-contact loop (§9.3) rather than removing it. Recommend: keep.
12. **The application's receipt through the machine.** `(:transmit (:receipt
    id) ...)` forwarded on the next contact, instead of parking it on the
    delivering session (§9.2); the T12c gate's "receipts back" row then
    measures the machine, not the host. Recommend: yes.

## 13. Defects found while designing, for the lanes named

- **F1** `bp-node-machine.lisp:414-420`: a job is never removed, so after
  `max-jobs` (64) jobs of any fate the machine refuses `:capacity` forever.
  Closed by discard (§4.4). Phase 2.
- **F2** `host/native/bp-service.lisp:317-318`: the contact predicate is the
  literal `t` for every ready peer; a decision the design gives the
  scheduler, computed nowhere. Retired by T12c; named until then (§8).
- **F3** `host/native/tcpcl.lisp:274`: the XFER_REFUSE reason code is logged
  and dropped, so `Completed` (the peer already holds the bundle, RFC 9174
  §5.2.4) is treated as a failure and the bundle is re-sent forever. Closed
  by `(:refused code)` in `:forward-result` (§3.1, §4.3). Phase 2.
- **F4** `bp-node-machine.lisp:582-590`: restart keeps the pre-crash age
  anchor `(age . monotonic)` verbatim; across a reboot the monotonic counter
  restarts and the age estimate `age + (now - monotonic)` is wrong in the
  direction of keeping an expired bundle alive (time.md, "monotonic-counter
  resets across a restart are not modeled"). Closed by re-anchoring (§4.6,
  T6). Phase 2 and 3.
- **F5** `*fn-bpf-max-length*` 65536 < `*fn-bpa-max-octets*` 65538: the two
  largest fn ADUs are not reassemblable. §7.1; question 9.
- **F6** `bp-node-machine.lisp:642`: `fn-bpn-step` runs `fn-bpn-machine-statep`,
  hence `fn-bpb-bundlep` over every held bundle, on every event: a
  whole-state recognizer on the served path (D3). Closed by
  `fn-bpn-step-fast` (§2.5). Phase 2.
- **F7** `host/bp-release-owner-host.lisp:8` calls `fn-bprl-replay-journal`,
  defined in no book on `dev` (only on `w25/bp-obligation-vertical`), and
  `host/native/build.lisp:93` `ld`s that file into the production image.
  T12d's first item; root should confirm what the production build does at
  that line today.
- **F8** PRF-038 (`planning/proofs.json`) names seven theorems and has no
  `events` key and no `proof-events.json` target, so its keystones are
  invisible to the ledger. T14 or the phase-3 registry edit.
- **F9** `host/native/bp-service.lisp:162-167` reads the route record by
  position (`second` … `seventh`) in host code; `fn-bpn-routep` is the owner
  of that shape. Closed by the `:cl-send` effect carrying the address and
  `fn-bpn-host-*` accessors. Phase 2.
- **F10** `specs/reconfiguration.md:176-178` lists eight delta kinds;
  `books/config.lisp:571-573` has ten (`:set-peer`, `:remove-peer`). T8's
  lane, or root when it lands.
- **F11** `docs/prefixes.md`'s `fn-bpn-` row names `bp-node`,
  `bp-node-records`, `bp-authored-wire`; `bp-node-machine*` and
  `bp-receive-evidence` use the prefix unregistered. Phase 2 (§11.1).
- **F12** `books/bp-node.lisp` and bp-design §1.5.1 say `fn-bpn-step` does
  not exist; the plan's §3.1 repeats it. This document is the correction;
  root's next pass over bp-design's status sections should cite it.
