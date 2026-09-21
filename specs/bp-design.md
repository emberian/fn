# fn as a BPv7 node: design

Status: design with exact statements, wave 4. Nothing here is certified; every
`defun` and `defthm` below is a commitment for the packets in "Migration",
not a claim. The books it builds on are certified today: `bp-primary-cbor`,
`bp-primary`, `bp-fragment`, `clock`, `bp-adu`, `bp-workflow`, `bp-receipt`,
`bp-release`, `relay`, and the wave-3 `scheduler` book
(`build/lanes/w3-scheduler/books/scheduler.lisp`, uncommitted at the time of
writing; its contact observation is `(fn-sched-contact peer start end)` and its
events are `admit`, `open`, `close`, `tick`, `expiry`, `transport`, `restart`).

## Why

What fn calls its BP integration today is an application polling a co-located
dtn7-rs daemon over HTTP on loopback: three verbs (`/status/bundles`,
`/download?BID`, `/delete?BID`) in `tools/bpa_dtn7.py`, an opaque BID that
"is a key into one agent's table" ([bp-primary](bp-primary.md)), a Rust
binary using the *upstream* decoder to extract the ADU, and an insert API
whose reply "follows an asynchronously spawned store/transmit operation"
([bp-workflow](bp-workflow.md)). The certified books that model the primary
block, fragmentation and expiry have no caller. That is theater: the proofs
are about functions the host never runs, and the host's actual protocol
surface is an HTTP client to a process fn does not control, cannot reason
about, and whose retained-copy semantics fn had to discover by experiment
("a pinned BPA restart window in which stored inventory does not resume
forwarding", [tests/bp-dtn7/README](../tests/bp-dtn7/README.md)).

This design makes fn a BPv7 node in its own right. The bundle protocol agent
is fn's core; the bundle store is fn's store; the convergence layer is fn's,
written against RFC 9174 and run by the native host on its own sockets. The
pinned dtn7-rs build and ION stop being fn's agent and become fn's *peers*.

## 1. fn as a BPv7 node

### 1.1 Vocabulary, and custody

| RFC 9171 term | fn realisation |
| --- | --- |
| Bundle Protocol Agent (§3.1) | the `fn-bpn-*` machine in `books/bp-node.lisp` (this design), executed by the native host |
| Application agent, administrative element | the sender workflow `fn-bp` (bp-workflow) and the receiver `fn-bpr` (bp-receipt) are the application agent; status reports are generated and parsed by `fn-bpn` itself and are the administrative element |
| Node ID, endpoint | `fn-bpp-eidp` values; fn's node ID is a `dtn` node ID; its registration is one singleton endpoint `dtn://<node>/fn` in the Active state |
| Bundle store | the fn Store journal, with a new record family (§1.3). A bundle is a durable record; its payload is an object the Store already keeps |
| Retention constraint (§3.1, §5.4, §5.6, §5.7) | `fn-bpn-constraintp`: `:dispatch-pending`, `:forward-pending`, `:reassembly-pending`; a per-bundle set in the bundle record |
| Custody | not in BPv7. RFC 9171 Appendix A removes RFC 5050 custody transfer and fn imports nothing of it |
| Convergence layer adapter (§7) | `fn-tcl-*` (§2), sockets in the native host |
| Contact plan, routing (§5.4 step 2) | the wave-3 scheduler: `fn-sched-contact-holdsp` decides whether a peer is reachable now; `fn-sched-selection` decides which work goes |

**Custody in fn's sense.** fn has two obligations that live longer than any
bundle: the archive pin an accepted article holds (RET-001, `fn-retain`), and
the `:forward` pin an outstanding work holds (`fn-bprl-undertake`). Both are
released only by `fn-retain-release` under checked application evidence
(`fn-bprl-release-decision`, a receipt). These are what "custody" means in
fn: a promise about content, discharged by a receipt. They are deliberately
*not* BPv7 retention constraints, which are BPA bookkeeping about one bundle
and vanish on deletion (§5.10 step 2). A bundle is a carrier; the article is
the subject. When a carrier expires, is refused or is deleted, the subject's
obligation is untouched and the scheduler makes a new carrier
(`fn-sched-expiry-preserves-workflow`, already proved on the scheduler side;
`fn-bpn-step-preserves-obligations` below on the node side). The word
"custody" is never used for retention constraints in fn's books.

### 1.2 What fn keeps from RFC 9171 §5, verbatim

| Section | fn keeps | Notes |
| --- | --- | --- |
| 5.2 Transmission | steps 1–2 | source node ID is always fn's own singleton; `dtn:none` sources are never originated (they are unidentifiable, `fn-bpp-identifiablep`) |
| 5.3 Dispatching | steps 1–2 | one local endpoint; delivery disavows forwarding to self |
| 5.4 Forwarding | steps 1–5, Previous Node removal and insertion, Bundle Age increment "at the last possible moment" | node selection is the scheduler's contact; CLA selection is TCPCL today, LTP later; the retry count is the scheduler's `retry-bound` |
| 5.4.1 Contraindicated | both steps | contraindication is `:no-contact`, `:hop-limit`, `:no-route`; "ceases to be contraindicated" is a later `fn-sched-open-event` |
| 5.4.2 Forwarding failed | step 2 | see 1.2.1 for step 1 |
| 5.5 Expiration | in full | the age/wall decision is `fn-clock-expiry-decision`, already certified, and fn prefers the Bundle Age path (time.md) |
| 5.6 Reception | steps 1–5 | CRCs of *every* block with a CRC are checked, not "SHOULD" |
| 5.7 Delivery | steps 1–3 | the registration is always Active; reassembly precedes delivery |
| 5.8 Fragmentation | the constraints in full | proactive only, cut at the peer's Transfer MRU (`fn-bpf-cut`) |
| 5.9 Reassembly | in full | at fn as destination; `fn-bpf-reassemble` is the material-extent rule |
| 5.10, 5.11 Deletion and discard | in full | plus fn's stronger rule that discard is gated by obligations, §1.6 T2 |
| 6.1.1 Status reports | generation of all four assertions when requested and enabled; parsing of all four | never with "report status time" (fn's wall is not trusted); never as evidence, §1.6 T5 |
| 4.4.1–4.4.3 Previous Node, Bundle Age, Hop Count | in full | Bundle Age is always attached to fn-originated bundles because fn's creation time may legitimately be 0 (§4.2.6) |

#### 1.2.1 What fn deliberately does not implement

- **§5.4.2 step 1, forwarding back to the previous node.** A MAY. With a
  contact plan, the previous node is the one hop known to be behind us; sending
  a bundle back there is a loop the Hop Count block would eventually stop at the
  price of the bundle. fn declares failure and deletes with the contraindication
  reason instead. This is the one place fn chooses a stricter behaviour than the
  RFC's option.
- **§5.7 step 2, passive registrations and the delivery-failure actions.**
  fn's endpoint is its own core; a bundle it cannot deliver is one it refuses at
  the convergence layer *before* storing (XFER_REFUSE `No Resources`), never one
  it "abandons" after accepting. There is no deferral queue and no abandonment.
- **§5.12 cancelling a transmission.** An fn work is cancelled by fn's
  workflow, not by BP. A bundle already handed to a CL transfer completes or
  fails there (RFC 9174 §6.1: a message cannot be cut short); the bundle record
  is then deleted with `:transmission-cancelled` by the ordinary path.
- **Lifetime overrides and "Traffic pared".** fn never shortens a lifetime it
  did not set (time.md leaves this open, and this design keeps it out).
- **`dtn:none`-sourced bundles as an origin.** Received ones are processed
  (they cannot be fragmented, `fn-bpf-anonymous-conformant-bundle-is-not-fragmentable`).
- **Custody, RFC 5050 compatibility, the `report status time` flag.**
- **Multiple registrations, group endpoints, non-singleton delivery.** One
  endpoint per node in wave 4.
- **Reactive fragmentation** after `No Resources` refusal: packet 7, not wave 4.
- **Any block type other than** payload (1), Previous Node (6), Bundle Age (7),
  Hop Count (10), BIB (11), BCB (12). Unknown blocks follow §5.6 step 4 by
  their block processing control flags; that is the whole treatment.

### 1.3 The bundle store is the fn store

`books/frame` gains a record family `FNBS` (schema 1), replayed by the same
journal machinery as FNWF and FNRJ. The host writes the record, barriers it,
and only then calls the transition that assumes it (the FNWF discipline,
[bp-workflow-host](bp-workflow-host.md)).

```lisp
;; books/bp-node.lisp
(defun fn-bpn-make-bundle (id primary blocks payload-ref constraints anchor
                           arrival origin validated)
  (declare (xargs :guard t))
  (list :fn-bpn-bundle id primary blocks payload-ref constraints anchor
        arrival origin validated))
```

| Field | Type | Meaning |
| --- | --- | --- |
| `id` | `fn-bpp-bundle-id` of `primary` and the payload length | the §4.3.1 identity, never a BID |
| `primary` | `fn-bpp-blockp` | the decoded primary block, canonical (`fn-bpp-accepted-input-is-canonical-by-construction`) |
| `blocks` | list of `fn-bpb-blockp` (§1.4, canonical block frame) | every non-payload canonical block in wire order, with its block number and processing flags |
| `payload-ref` | object id in the Store | the payload octets. For an fn-originated bundle this is the request ADU, `fn-bpo-request-adu` of the work, and is *derivable*; for a transit bundle it is an opaque object with a bundle pin |
| `constraints` | subset of `(:dispatch-pending :forward-pending :reassembly-pending)` | §5 retention constraints |
| `anchor` | `fn-clock-age-anchorp` | the Bundle Age block value, if any, plus the monotonic reading at arrival (time.md); re-established from `arrival` on restart |
| `arrival` | `fn-clock-observationp` | the observation at reception or creation |
| `origin` | `(:local work-id attempt-id generation)` or `(:cl session-id transfer-id peer)` | provenance |
| `validated` | `t` only after §5.6 step 3 succeeded on the exact stored octets | the gate for delivery and forwarding |

Records: `(:bundle-stored bundle)`, `(:bundle-constraint id :add/:remove
constraint)`, `(:bundle-validated id)`, `(:bundle-deleted id reason)`,
`(:bundle-discarded id)`, `(:reassembly id-key fragments)`,
`(:report-intent report)`, `(:report-sent report)`. The creation-timestamp
sequence counter is a durable frontier like the transaction pair:
`(:bpn-sequence n)` is written before any bundle with sequence `n` exists, so
a restart cannot reuse a `(source, creation-time, sequence)` triple.

The bundle store is *the* Store: one journal, one recovery, one crash
argument. Payload objects are pinned by the bundle record (`:bundle` pin kind
in `fn-retain-kindp`) for exactly as long as the record has a retention
constraint or an open fn obligation refers to it; the archive pin and the
`:forward` pin are independent of it (`fn-retain-release-preserves-independent-pin`).

### 1.4 The gap the frame closes: `books/bp-bundle.lisp`

The primary block is modeled; the bundle around it is not (bp-primary.md,
"the canonical block format (§4.3.2) and the payload block are not modeled").
Packet 0 adds `fn-bpb-*`:

```lisp
(defun fn-bpb-make-block (type number flags crc-type data) ...)  ; §4.3.2
(defun fn-bpb-blockp (b) ...)          ; type < 2^64, number, flags a bit set,
                                       ; crc-type in {0 1 2}, data an octet list
(defun fn-bpb-flag-replicate-in-fragments (b) ...)   ; §4.2.4 bit 0
(defun fn-bpb-flag-report-if-unprocessable (b) ...)  ; bit 1
(defun fn-bpb-flag-delete-if-unprocessable (b) ...)  ; bit 2
(defun fn-bpb-flag-discard-if-unprocessable (b) ...) ; bit 4
(defun fn-bpb-encode-block (b) ...)
(defun fn-bpb-decode-block (octets budget) ...)      ; (:ok b rest) | (:error why)
(defun fn-bpb-encode-bundle (primary blocks payload) ...)
;; indefinite-length array head 0x9F, primary, canonical blocks, payload block
;; (type 1, number 1), break 0xFF -- §4.1
(defun fn-bpb-decode-bundle (octets limit) ...)
;; (:ok primary blocks payload) | (:error why)
;; limit is checked against (len octets) before the first octet is read;
;; each block's data length is checked before take.
```

Theorems required of packet 0: `fn-bpb-decode-of-encode`,
`fn-bpb-accepted-input-is-canonical` (the primary-block proof pattern, over
arbitrary input), `fn-bpb-block-numbers-unique` (a decoded bundle has
pairwise distinct block numbers, payload is number 1, §4.1),
`fn-bpb-decode-allocates-within-limit`. The CRC over a canonical block
includes its own zero-filled CRC field, as for the primary block, and reuses
`fn-bpp-crc16`/`fn-bpp-crc32c`.

### 1.4.1 Status, 2026-09-20 (lane w9/dtn-2)

`books/bp-bundle.lisp` exists and the names above are its names, with three
differences the design did not anticipate and this section records rather
than hides:

- The decoder's per-block bound is a book constant (`*fn-bpb-max-data*`), not
  the caller's `limit`. Two bounds, both applied before allocation: the whole
  input against the caller's limit first, then each declared byte-string
  length against the per-block bound before any `take`. Discharging the
  round trip against the caller's limit would have required a length
  arithmetic the block recognizer already carries.
- The payload block is a field of `fn-bpb-bundle`, not the last element of
  its block list, because RFC 9171 section 4.1 requires it last and unique
  and "last" is not a property to re-derive at every use.
- `fn-bpb-block-numbers-unique` is not a separate theorem: pairwise-distinct
  numbers, no block numbered 0 or 1 among the canonical blocks, and the
  payload block numbered 1 are conjuncts of `fn-bpb-bundlep`, which
  `fn-bpb-decode-yields-bundle` establishes for every accepted input. A
  separate theorem restating a conjunct of the recognizer would be a
  corollary (AGENTS.md, "cite keystones, never corollaries").

Still open at 1.4, and not claimed: the CRC over a canonical block is
computed in the logic and checked, but no vector from another implementation
pins it. The `bp7` crate's published samples are primary blocks, which
`tests/acl2/bp-primary-tests.lisp` already uses; a canonical-block vector
wants a capture from the dtn7 interop, and until one is recorded in
`tests/bp-dtn7/` the canonical-block CRC is exercised only against fn's own
encoder.

### 1.5 The processing machine: `books/bp-node.lisp`

State:

```lisp
(defun fn-bpn-make-state (config bundles reassembly next-seq reports) ...)
;; config    : (node-id endpoint reporting-enabled attach-previous-node
;;              hop-limit default-lifetime crc-type)
;; bundles   : fn-bpn-bundle list, unique ids
;; reassembly: alist  fn-bpp-adu-key -> fn-bpf-fragment-listp with total
;; next-seq  : the durable creation-timestamp sequence frontier
;; reports   : status-report intents not yet transmitted
(defun fn-bpn-statep (st) ...)
```

Events and effects (the host's `step(state, event) -> (state', effects)`):

```lisp
;; events
(:bundle-received octets origin obs)          ; from the CL, complete transfer
(:transmit work-id attempt-id generation adu peer lifetime flags obs)
                                              ; the workflow's :submit effect
(:forward-result id peer outcome)             ; :sent | (:refused reason) | :failed
(:deliver-result id outcome)                  ; :accepted | :duplicate | :refused
(:clock obs)                                  ; expiry sweep
(:contact peer open-p)                        ; from the scheduler
(:restart obs)
;; effects
(:cl-send peer id octets)                     ; hand a bundle image to the CL
(:deliver id adu-key payload origin)          ; to fn-bpr-accept-request
(:transport work-id attempt-id generation status)
                                              ; to fn-sched-transport-event
(:report report)                              ; a status report to transmit
(:persist record)                             ; an FNBS record the host must
                                              ; barrier before the next step
```

The definitions, in RFC order. Each is total and returns `(state effects)`;
refusals return the state unchanged and no effects.

```lisp
(defun fn-bpn-receive (st octets origin obs)
  ;; §5.6.  Bounds first: (<= (len octets) (fn-bpn-config-transfer-limit st))
  ;; is required by the CL before this is called (fn-tcl-inbound-fits-mru).
  ;; Step 3 before step 1: a bundle that does not decode is never stored.
  (let ((d (fn-bpb-decode-bundle octets (fn-bpn-config-transfer-limit st))))
    (if (not (eq (car d) :ok))
        (fn-bpn-refuse st :block-unintelligible)          ; no record, no report
      (let* ((primary (nth 1 d)) (blocks (nth 2 d)) (payload (nth 3 d))
             (id (fn-bpp-bundle-id primary (len payload)))
             (b (fn-bpn-make-bundle id primary blocks (fn-bpn-object-of payload)
                                    '(:dispatch-pending)
                                    (fn-bpn-anchor-from blocks obs) obs origin t)))
        (cond ((fn-bpn-find-bundle st id) (fn-bpn-duplicate st id))
              ((not (fn-bpn-blocks-processable st blocks))
               (fn-bpn-unsupported-block st b))         ; §5.6 step 4
              (t (mv (fn-bpn-store st b)
                     (append (fn-bpn-reception-report-effects st b)   ; step 2
                             (list (list :persist (list :bundle-stored b)))))))))))

(defun fn-bpn-dispatch (st id)
  ;; §5.3: local endpoint -> deliver, else forward.  Called after :persist.
  ...)

(defun fn-bpn-forward-decision (st id contact obs)
  ;; §5.4 steps 1-3 as one pure decision.
  ;; (:send peer) | (:wait reason) | (:fail reason)
  (let ((b (fn-bpn-find-bundle st id)))
    (cond ((not (fn-bpn-bundle-validated b)) '(:fail :block-unintelligible))
          ((eq (fn-clock-expiry-decision (fn-bpp-creation-time (fn-bpn-bundle-primary b))
                                          (fn-bpp-lifetime (fn-bpn-bundle-primary b))
                                          (fn-bpn-bundle-anchor b) obs)
               :expired)
           '(:fail :lifetime-expired))
          ((fn-bpp-hop-limit-exceededp (fn-bpn-hop-count b)) '(:fail :hop-limit-exceeded))
          ((not (fn-sched-contact-holdsp contact (fn-clock-monotonic obs)))
           '(:wait :no-timely-contact))
          ((not (fn-bpn-next-hop-for st b contact)) '(:wait :no-known-route))
          (t (list :send (fn-sched-contact-peer contact))))))

(defun fn-bpn-forward-prepare (st id peer obs)
  ;; §5.4 step 4.  Remove Previous Node; insert own Previous Node if configured;
  ;; increase Bundle Age by the local residence (fn-clock-age-estimate of the
  ;; anchor at obs); increment Hop Count.  The bundle *record* is unchanged;
  ;; only the transmitted image differs.  Effect: (:cl-send peer id image).
  ...)

(defun fn-bpn-forward-result (st id peer outcome)
  ;; §5.4 step 5.  :sent removes :forward-pending, emits a forwarding report
  ;; if requested, and (:transport ... :forwarded) for a local origin.
  ;; (:refused :completed) counts as :sent (RFC 9174 Table 6).
  ;; Any other refusal or :failed leaves :forward-pending and emits
  ;; (:transport ... :attempted); the scheduler owns the retry.
  ...)

(defun fn-bpn-forwarding-failed (st id reason)
  ;; §5.4.2 step 2 only: local destination -> drop :forward-pending;
  ;; otherwise fn-bpn-delete with reason.
  ...)

(defun fn-bpn-expire (st obs)
  ;; §5.5.  For every bundle whose fn-clock-expiry-decision is :expired,
  ;; fn-bpn-delete with :lifetime-expired.  :live and :uncertain do nothing.
  ...)

(defun fn-bpn-deliver (st id)
  ;; §5.7.  Fragment -> fn-bpn-reassemble; complete -> (:deliver ...).
  (let ((b (fn-bpn-find-bundle st id)))
    (if (fn-bpp-fragmentp (fn-bpn-bundle-primary b))
        (fn-bpn-reassemble st b)
      (if (fn-bpn-deliverablep b)
          (mv (fn-bpn-drop-constraint st id :dispatch-pending)
              (list (list :deliver id (fn-bpp-adu-key (fn-bpn-bundle-primary b))
                          (fn-bpn-bundle-payload-ref b) (fn-bpn-bundle-origin b))))
        (mv st nil)))))

(defun fn-bpn-deliverablep (b)
  (and (fn-bpn-bundlep b)
       (fn-bpn-bundle-validated b)
       (fn-bpp-blockp (fn-bpn-bundle-primary b))
       (fn-bpp-flags-conformantp (fn-bpn-bundle-primary b))
       (not (fn-bpp-fragmentp (fn-bpn-bundle-primary b)))
       (member-eq :dispatch-pending (fn-bpn-bundle-constraints b))))

(defun fn-bpn-reassemble (st b)
  ;; §5.9 with fn-bpf-reassemble over the fragments sharing fn-bpp-adu-key.
  ;; (:ok bytes): the offset-zero fragment's payload becomes bytes, its primary
  ;;   has the fragment flag cleared and the fragment fields removed, its
  ;;   :reassembly-pending is removed, every other fragment loses
  ;;   :reassembly-pending (and is then discardable), and delivery proceeds.
  ;; (:missing i j): add :reassembly-pending to b, no effect.
  ;; (:conflict i): delete every fragment of the key with :block-unintelligible;
  ;;   two fragments disagreeing on a byte is corruption, not a partial ADU.
  ...)

(defun fn-bpn-fragment (st id mtu)
  ;; §5.8, proactive.  Only when (not (fn-bpp-no-fragmentp primary)) and
  ;; (fn-bpf-fragmentablep primary).  Boundaries chosen so that every fragment's
  ;; encoded bundle fits mtu; fn-bpf-cut for the payloads and
  ;; fn-bpf-fragment-block for the primaries; blocks flagged
  ;; fn-bpb-flag-replicate-in-fragments go in every fragment, all blocks in the
  ;; offset-zero fragment.  Each fragment is a new bundle record with the parent's
  ;; origin; the parent record loses :forward-pending and is deleted with
  ;; :no-additional-information once every fragment is :sent.
  ...)

(defun fn-bpn-delete (st id reason)
  ;; §5.10.  Deletion report if requested; all constraints removed;
  ;; (:persist (:bundle-deleted id reason)).  Reason is one of the Table 1
  ;; codes fn can name: :lifetime-expired :transmission-cancelled
  ;; :depleted-storage :no-known-route :no-timely-contact :block-unintelligible
  ;; :hop-limit-exceeded :block-unsupported :no-additional-information.
  ...)

(defun fn-bpn-discardablep (st id)
  ;; §5.11 plus fn's rule.
  (let ((b (fn-bpn-find-bundle st id)))
    (and b (null (fn-bpn-bundle-constraints b))
         (not (fn-bpn-obligation-openp st b)))))

(defun fn-bpn-obligation-openp (st b)
  ;; A local-origin bundle whose work is still fn-bp-work-outstandingp at the
  ;; attempt generation it carries; or a local-destination bundle not yet
  ;; delivered.  Both read from the origin field and the workflow image the
  ;; host threads in; nothing here consults a peer.
  ...)

(defun fn-bpn-discard (st id)
  (if (fn-bpn-discardablep st id) (mv (fn-bpn-remove st id) (list (list :persist (list :bundle-discarded id)))) (mv st nil)))

(defun fn-bpn-transmit (st work-id attempt-id generation adu peer lifetime flags obs)
  ;; §5.2.  Primary: source = own node ID, destination = peer, report-to = own
  ;; node ID, creation time = (if (fn-clock-has-wall obs) wall 0), sequence =
  ;; next-seq, lifetime, flags with fragment bits clear.  Blocks: Bundle Age 0
  ;; always; Hop Count (limit, 0); Previous Node never at origin.  Constraint
  ;; :dispatch-pending, origin (:local work-id attempt-id generation), validated t.
  ;; Effects: (:persist (:bpn-sequence next-seq+1)) BEFORE (:persist (:bundle-stored b)),
  ;; then (:transport work-id attempt-id generation :bundle-created).
  ...)

(defun fn-bpn-step (st event) ...)   ; the dispatcher; every case above
(defun fn-bpn-trace (st events) ...)
```

Status reports as typed statements:

```lisp
(defun fn-bpn-make-report (received forwarded delivered deleted reason
                           source creation-time sequence offset length) ...)
;; each assertion is t/nil; reason a Table 1 code; offset/length present iff
;; the subject is a fragment (§6.1.1).  No status times.
(defun fn-bpn-encode-report (r) ...)       ; the CBOR array of §6.1.1, as the
                                           ; payload of an admin-record bundle
(defun fn-bpn-decode-report (octets) ...)  ; (:ok r) | (:error why)
(defun fn-bpn-report-subject (r) ...)      ; the fn-bpp-adu-key it names
```

A decoded report is an *observation*: `fn-bpn-receive` of an administrative
bundle addressed to fn yields `(:transport work-id attempt-id generation
:forwarded)` or `:delivered` for the local-origin bundle whose ADU key the
report names, and nothing else. The scheduler relays that to `fn-bp-step`,
where `fn-bp-observe-transport` cannot close a work
(`fn-bp-observe-transport-never-moves-status-backward` and the receipt
requirement in bp-workflow.md). That is the whole force of REP-006 and
RET-003 at the bundle layer.

#### 1.5.1 Status, 2026-09-20 (lane w9/dtn-2)

`books/bp-node.lisp` exists and is **two ends of this machine, not the
machine**. What it has: `fn-bpn-send`, `fn-bpn-receive` with the three
outcomes, `fn-bpn-expiry` over `fn-clock-expiry-decision`,
`fn-bpn-hop-exceededp` and `fn-bpn-next-hop-count`, and
`fn-bpn-forward-decision` restricted to those two questions.

Open, and each one is a named absence rather than a weakened claim:

- `fn-bpn-make-state`, `fn-bpn-statep`, the bundle list, the retention
  constraints, `fn-bpn-step` and `fn-bpn-trace`: none exists. The theorems
  of section 1.6 are stated against `fn-bpn-step` and therefore have no
  subject yet; T1 to T6 are **not** proved and nothing in this tree claims
  them.
- The FNBS record family and the `(:bpn-sequence n)` durable frontier of
  section 1.3: absent. `host/native/bp.lisp` takes the sequence number as an
  argument and says in its own header that a restarted operator must not
  reuse one. This is the gap that keeps the node from being restart-safe.
- Reassembly: `fn-bpn-receive` refuses a fragment (`:fragment-not-reassembled`)
  rather than reassembling it. `books/bp-fragment` has the reassembly and is
  not wired in.
- Status reports (section 6.1.1) and `fn-bpn-make-report`: absent. A received
  administrative record is decoded as a bundle like any other and its payload
  is handed out as an ADU; nothing turns it into a transport observation.
- Dispatch: `fn-bpn-receive` does not decide local delivery against
  forwarding, because there is no routing table here. The host journals the
  accepted ADU; `books/scheduler` owns the contact and `books/bp-receipt`
  owns the receiver path, and joining them is the next packet.

### 1.6 Theorems the node must carry

Hypotheses are `fn-bpn-statep st` and `fn-bpn-eventp event` unless stated;
`(fn-bpn-effects st event)` abbreviates `(mv-nth 1 (fn-bpn-step st event))`
and `(fn-bpn-next st event)` the state.

**T1. No delivery without a validated primary block and a complete payload.**

```lisp
(defthm fn-bpn-deliver-requires-validated-primary-and-complete-payload
  (implies (and (fn-bpn-statep st) (fn-bpn-eventp event)
                (member-equal (list :deliver id key ref origin)
                              (fn-bpn-effects st event)))
           (let ((b (fn-bpn-find-bundle st id)))
             (and (fn-bpn-bundle-validated b)
                  (fn-bpp-blockp (fn-bpn-bundle-primary b))
                  (fn-bpp-flags-conformantp (fn-bpn-bundle-primary b))
                  (equal key (fn-bpp-adu-key (fn-bpn-bundle-primary b)))
                  (or (not (fn-bpp-fragmentp (fn-bpn-bundle-primary b)))
                      (let ((r (fn-bpf-reassemble
                                (fn-bpn-fragments-of st key)
                                (fn-bpp-total-adu-length (fn-bpn-bundle-primary b)))))
                        (and (equal (fn-bpf-result-tag r) :ok)
                             (equal (len (fn-bpf-result-bytes r))
                                    (fn-bpp-total-adu-length (fn-bpn-bundle-primary b)))
                             (equal ref (fn-bpn-object-of (fn-bpf-result-bytes r))))))))))
```

`validated` is set only by `fn-bpn-receive` on a successful
`fn-bpb-decode-bundle`, and `fn-bpb-decode-bundle` succeeds only when every
attached CRC verifies (`fn-bpb-accepted-block-has-valid-crc`, the canonical
analogue of `fn-bpp-accepted-block-has-valid-crc`).

**T2. No deletion of an undelivered bundle whose obligation is open.**
Two statements, because the obligation lives on the application side.

```lisp
(defthm fn-bpn-undelivered-local-bundle-is-deleted-only-by-expiry-or-corruption
  (implies (and (fn-bpn-statep st) (fn-bpn-eventp event)
                (fn-bpn-local-destinationp st (fn-bpn-find-bundle st id))
                (member-eq :dispatch-pending
                           (fn-bpn-bundle-constraints (fn-bpn-find-bundle st id)))
                (member-equal (list :persist (list :bundle-deleted id reason))
                              (fn-bpn-effects st event)))
           (or (and (equal reason :lifetime-expired)
                    (equal event (list :clock obs))
                    (equal (fn-clock-expiry-decision
                            (fn-bpp-creation-time (fn-bpn-bundle-primary (fn-bpn-find-bundle st id)))
                            (fn-bpp-lifetime (fn-bpn-bundle-primary (fn-bpn-find-bundle st id)))
                            (fn-bpn-bundle-anchor (fn-bpn-find-bundle st id))
                            obs)
                           :expired))
               (equal reason :block-unintelligible))))

(defthm fn-bpn-discard-refuses-while-obligation-open
  (implies (and (fn-bpn-statep st)
                (fn-bpn-obligation-openp st (fn-bpn-find-bundle st id)))
           (equal (fn-bpn-discard st id) (mv st nil))))

(defthm fn-bpn-step-preserves-obligations
  ;; The node never touches the workflow or the pins.  The workflow image wf is
  ;; threaded through fn-bpn-obligation-openp read-only.
  (implies (and (fn-bpn-statep st) (fn-bpn-eventp event) (fn-bp-statep wf))
           (and (equal (fn-bpn-workflow-of (fn-bpn-next st event) wf) wf)
                (not (member-equal-kind :release (fn-bpn-effects st event)))
                (not (member-equal-kind :receipt-prepare (fn-bpn-effects st event))))))
```

`:block-unintelligible` in T2 is the reception path: a bundle is deleted with
that reason only when it never became `validated`, so "undelivered because
corrupt" is distinguished from "undelivered because we chose to". Refusing at
the CL (`No Resources`) is not deletion: the bundle was never stored.

**T3. Expiry only by the clock book's decision.**

```lisp
(defthm fn-bpn-expiry-only-by-clock-decision
  (implies (and (fn-bpn-statep st) (fn-bpn-eventp event)
                (member-equal (list :persist (list :bundle-deleted id :lifetime-expired))
                              (fn-bpn-effects st event)))
           (and (equal (car event) :clock)
                (equal (fn-clock-expiry-decision
                        (fn-bpp-creation-time (fn-bpn-bundle-primary (fn-bpn-find-bundle st id)))
                        (fn-bpp-lifetime (fn-bpn-bundle-primary (fn-bpn-find-bundle st id)))
                        (fn-bpn-bundle-anchor (fn-bpn-find-bundle st id))
                        (nth 1 event))
                       :expired))))

(defthm fn-bpn-uncertain-clock-deletes-nothing
  (implies (and (fn-bpn-statep st) (fn-clock-observationp obs)
                (not (fn-clock-has-wall obs))
                (fn-bpn-no-anchors-p st))
           (equal (fn-bpn-next st (list :clock obs)) st)))
```

The second is the node-level face of `fn-clock-no-wall-and-no-age-is-uncertain`.
Together with `fn-clock-expiry-is-monotone-in-local-time`, a bundle fn once
kept as `:live` cannot become `:expired` by a clock that merely got *less*
sure.

**T4. Fragmentation and reassembly identity.**

```lisp
(defthm fn-bpn-fragment-then-reassemble-is-identity
  (implies (and (fn-cbor-octet-listp payload)
                (fn-bpf-boundariesp boundaries (len payload)))
           (equal (fn-bpf-reassemble (fn-bpf-cut payload 0 boundaries (len payload))
                                     (len payload))
                  (list :ok payload))))

(defthm fn-bpn-fragments-share-the-adu-key-and-reassembly-restores-the-primary
  (implies (and (fn-bpp-blockp p) (fn-bpf-fragmentablep p)
                (fn-bpf-boundariesp boundaries total))
           (and (fn-bpn-all-equal (fn-bpp-adu-key p)
                                  (fn-bpn-map-adu-key (fn-bpn-fragment-primaries p boundaries total)))
                (equal (fn-bpn-unfragment (car (fn-bpn-fragment-primaries p boundaries total)))
                       p))))
```

The first is a corollary of the certified
`fn-bpf-complete-agreeing-cover-reassembles-to-payload` once the two open
lemmas in `bp-fragment-invariants` land: `fn-bpf-cut-covers` (a cut covers
its payload) and `fn-bpf-reassemble-ok-agrees-with-every-fragment`. Those two
are packet 2's first deliverable, because T4 is not provable without them.
The second uses `fn-bpf-fragment-block-preserves-adu-key` (certified) and a
new `fn-bpn-unfragment` that clears the fragment flag, drops the two fragment
fields and recomputes the CRC.

**T5. Status reports never discharge obligations.**

```lisp
(defthm fn-bpn-status-report-is-only-a-transport-observation
  (implies (and (fn-bpn-statep st)
                (fn-bpp-administrativep (fn-bpn-primary-of octets))
                (equal (fn-bpn-effects st (list :bundle-received octets origin obs))
                       effects))
           (and (fn-bpn-only-transport-and-persist-effects effects)
                (not (member-equal-kind :deliver effects))
                (not (member-equal-kind :release effects)))))

(defthm fn-bpn-transport-observation-cannot-close-a-work
  ;; composed with the workflow: relaying any :transport effect through
  ;; fn-sched-transport-event and fn-bp-step leaves every receipt and every
  ;; outstanding work outstanding.
  (implies (and (fn-bp-statep wf) (fn-bp-work-outstandingp (fn-bp-find-work wf work-id)))
           (fn-bp-work-outstandingp
            (fn-bp-find-work
             (fn-bp-result-state (fn-bp-step wf (fn-bp-transport-event work-id attempt-id generation status)))
             work-id))))
```

The second is already implied by `fn-bp-observe-transport-preserves-state`
and the definition of `fn-bp-observe-transport` (bp-workflow.md: "BP delivery
alone does not close the fn obligation"); it is restated here so that the
node's theorem file names the composition explicitly.

**T6. State and replay.** `fn-bpn-step-preserves-statep`,
`fn-bpn-trace-preserves-statep`, `fn-bpn-ids-unique`,
`fn-bpn-replay-journal-is-trace` (the FNBS records denote events, as
`fn-bp-replay-journal` does for FNWF), and
`fn-bpn-restart-reanchors-age` (after `(:restart obs)` every anchor's
monotonic is `obs`'s and its age is the age estimated at the last durable
observation, time.md's "re-established from durable state").

## 2. The convergence layer fn owns: TCPCLv4

RFC 9174 is the CL RFC 9171 §5.4 says MUST be implemented for Internet
forwarding, and it is what dtn7-rs and ION both speak. fn implements it in
`books/tcpcl-octets.lisp`, `books/tcpcl-records.lisp` and
`books/tcpcl-session.lisp` (`fn-tcl-*`), with the octet codec, the session
machine and the transfer machines as ACL2 definitions and the sockets in the
native host.  This design said `books/tcpcl.lisp`, one book, until
2026-09-21; the cluster landed as those three plus
`books/tcpcl-invariants.lisp`, and no book of that single name has ever
existed. TLS (§4.4) is a profile slot, §4 below; wave 4 sends `CAN_TLS = 0`.

### 2.1 The octet grammar, with bounds before allocation

All integers are unsigned, network byte order. `U8`, `U16`, `U32`, `U64`.
The decoder is `(fn-tcl-decode buf phase limits)` returning `(:ok msg n)`
with `n` octets consumed, `(:need k)` when at least `k` more octets are
required (the host reads and retries; nothing is copied), or `(:error
reason)`. The `limits` are fn's own SESS_INIT values plus configured caps;
every length field is compared with them **before** `take` is applied to the
buffer, exactly as `fn-bpc-decode` preflights (bp-primary.md).

| Message | Octets | Bound checked first |
| --- | --- | --- |
| Contact Header (§4.2) | `64 74 6E 21` `version:U8` `flags:U8` | 6 octets; magic exact; version = 4 else `(:error :version)`; flags bit 0 = CAN_TLS, others ignored |
| Message header (§4.5) | `type:U8` | type in `{01 02 03 04 05 06 07}` else MSG_REJECT `Message Type Unknown` (0x01) and close |
| SESS_INIT 0x07 (§4.6) | `keepalive:U16` `segment-mru:U64` `transfer-mru:U64` `node-id-len:U16` `node-id:bytes` `ext-len:U32` `ext:bytes` | `node-id-len <= 1024` (fn's cap; an EID longer than that is refused as `Contact Failure`), `ext-len <= 4096`; extension items parsed as `(flags:U8 type:U16 len:U16 value)` and must exactly fill `ext-len` else the SESS_INIT "is considered to have failed" |
| XFER_SEGMENT 0x01 (§5.2.2) | `flags:U8` `xfer-id:U64` [`ext-len:U32` `ext:bytes` iff START] `data-len:U64` `data:bytes` | `data-len <= own segment MRU` else `(:error :segment-exceeds-mru)` -> SESS_TERM `Contact Failure`; `ext-len <= 4096`; Transfer Length Extension (type 0x0001, `total:U64`) at most once and `total <= own transfer MRU` else XFER_REFUSE `Not Acceptable`; a running total exceeding the transfer MRU is refused `No Resources` before the segment's data is taken |
| XFER_ACK 0x02 (§5.2.3) | `flags:U8` `xfer-id:U64` `acked-len:U64` | xfer-id must be the sender's in-flight or pipelined id else MSG_REJECT `Message Unexpected` (0x03) |
| XFER_REFUSE 0x03 (§5.2.4) | `reason:U8` `xfer-id:U64` | reason in Table 6, unknown codes read as `Unknown` (0x00) |
| KEEPALIVE 0x04 | nothing | |
| SESS_TERM 0x05 (§6.1) | `flags:U8` `reason:U8` | flags bit 0 = REPLY; reason Table 9, unknown read as `Unknown` |
| MSG_REJECT 0x06 (§5.1.2) | `reason:U8` `rejected-header:U8` | |

`fn-tcl-encode` is the inverse; `fn-tcl-decode-of-encode` and
`fn-tcl-accepted-input-is-canonical` are the codec theorems (the grammar is
fixed-width except for lengths, so canonicality is length-exactness).

### 2.2 Session state

```lisp
(defun fn-tcl-make-session (role phase sent-ch got-ch sent-si got-si
                            local peer negotiated inbound outbound
                            next-xfer-id last-rx last-tx term) ...)
;; role       : :active | :passive
;; phase      : :tcp-connected | :contact | :messaging | :init | :established
;;              | :ending | :closed
;; sent-ch/got-ch/sent-si/got-si : booleans; phase is derived from them
;; local, peer: SESS_INIT parameter records (keepalive segment-mru transfer-mru node-id)
;; negotiated : (keepalive segment-mtu transfer-mtu tls) per §4.3 and §4.7:
;;              keepalive = min, MTUs = the peer's MRUs, tls = and of CAN_TLS
;; inbound    : nil or one fn-tcl-inbound (§5.2.2 forbids interleaving)
;; outbound   : list of fn-tcl-outbound, at most one :sending, the rest
;;              :waiting-ack (pipelined) in id order
;; next-xfer-id: U64 frontier, starts at 0, +1 per transfer (§5.2.1)
;; last-rx, last-tx : monotonic ms of the last message each way
;; term       : nil | (:sent reason) | (:received reason) | (:both reason)
(defun fn-tcl-inbound (xfer-id started ended received-len total staged) ...)
;; staged is the object being written, appended per segment; total from the
;; Transfer Length Extension or nil
(defun fn-tcl-outbound (xfer-id octets sent-len acked-len status) ...)
;; status: :sending | :waiting-ack | :acknowledged | (:refused reason) | :failed
(defun fn-tcl-sessionp (s) ...)
```

Phase transitions (RFC 9174 §3.3 Figures 4–14, with fn's role annotations):

| From | On | To | Emits |
| --- | --- | --- | --- |
| `:tcp-connected` (active) | `:open` | `:contact` | own CH |
| `:tcp-connected` (passive) | peer CH | `:contact` | own CH |
| `:contact` | peer CH, version 4 | `:messaging` | own SESS_INIT (§4.3: TLS = and; fn requires `tls = nil` in wave 4 and terminates `Contact Failure` if the negotiated value is unacceptable) |
| `:contact` | peer CH, version != 4 | `:closed` | (passive) own CH then SESS_TERM `Version mismatch`; (active) close |
| `:messaging` | peer SESS_INIT acceptable | `:established` | `(:session-up peer-node-id negotiated)` to the node |
| `:messaging` | peer SESS_INIT unacceptable (MRU below fn's minimum, node ID not the contact's configured peer, bad extension list) | `:ending` | SESS_TERM `Contact Failure` |
| `:established` | XFER_SEGMENT START (no inbound) | `:established` | ack per segment; on END `(:bundle-received octets (:cl sid xfer-id peer) obs)` |
| `:established` | XFER_SEGMENT for another id while inbound live | `:ending` | MSG_REJECT `Message Unexpected`, SESS_TERM `Contact Failure` |
| `:established` | `(:send id octets)` from the node, outbound idle or pipelining | `:established` | segments of at most `segment-mtu`, Transfer Length Extension on START when more than one segment |
| `:established` | XFER_ACK final for an outbound | `:established` | `(:forward-result id peer :sent)` when `acked-len = (len octets)` and END flag set |
| `:established` | XFER_REFUSE for an outbound | `:established` | `(:forward-result id peer (:refused reason))`; no further segments of that id |
| `:established` | `(:tick m)` with `m - last-tx >= keepalive` and keepalive > 0 | same | KEEPALIVE |
| `:established` | `(:tick m)` with `m - last-rx >= 2 * keepalive` and keepalive > 0 | `:ending` | SESS_TERM `Idle timeout` |
| `:established` | SESS_TERM (REPLY 0) | `:ending` | SESS_TERM with REPLY 1, same reason |
| `:established` | `(:terminate reason)` from the node | `:ending` | SESS_TERM (REPLY 0) |
| `:ending` | XFER_SEGMENT START | `:ending` | XFER_REFUSE `Session Terminating` |
| `:ending` | in-progress transfers complete both ways | `:closed` | `(:close)` |
| any | `(:tcp-closed)` | `:closed` | `(:transfer-failed id)` for each unfinished transfer either way; `(:session-down)` |
| any | undecodable input | `:closed` | before contact: close silently (§6.1); after: MSG_REJECT then close |

### 2.3 The drive function and its theorems

```lisp
(defun fn-tcl-drive (s octets) ...)   ; -> (fn-tcl-make-result s2 events unconsumed)
;; Consumes as many complete messages as octets holds; a trailing partial
;; message is kept as unconsumed, never copied into s.
(defun fn-tcl-tick (s monotonic) ...) ; keepalive and idle timeout
(defun fn-tcl-send (s id octets) ...) ; from the node: (:cl-send ...)
(defun fn-tcl-terminate (s reason) ...)
(defun fn-tcl-tcp-closed (s) ...)
```

**C1. Partition independence**, in the shape of
`fn-wire-drive-partition-independence` (books/wire-invariants.lisp:561):

```lisp
(defthm fn-tcl-drive-partition-independence
  (implies (and (fn-tcl-sessionp s)
                (fn-wire-octet-listp left) (fn-wire-octet-listp right))
           (equal (fn-tcl-drive s (append left right))
                  (let ((l (fn-tcl-drive s left)))
                    (let ((r (fn-tcl-drive (fn-tcl-result-session l)
                                           (append (fn-tcl-result-unconsumed l) right))))
                      (fn-tcl-make-result (fn-tcl-result-session r)
                                          (append (fn-tcl-result-events l)
                                                  (fn-tcl-result-events r))
                                          (fn-tcl-result-unconsumed r)))))))
```

The `unconsumed` carry is the one difference from the NNTP wire theorem: a
TCPCL message is not self-delimiting at every octet, so a partial message is
handed back rather than absorbed. The host's loop is exactly the right-hand
side (`fnn-recv` chunk, prepend the carry, drive), which is why this is the
theorem and not a weaker one.

**C2. A transfer is acknowledged only when every segment was received.**

```lisp
(defthm fn-tcl-final-ack-means-every-segment
  (implies (and (fn-tcl-sessionp s) (fn-wire-octet-listp octets)
                (member-equal (list :bundle-received data (list :cl sid id peer) obs)
                              (fn-tcl-result-events (fn-tcl-drive s octets))))
           (let ((segs (fn-tcl-segments-of-id (fn-tcl-history s octets) id)))
             (and (consp segs)
                  (fn-tcl-start-flag (car segs))
                  (fn-tcl-end-flag (car (last segs)))
                  (fn-tcl-no-start-or-end-inside segs)
                  (equal data (fn-tcl-concat-data segs))
                  (equal (fn-tcl-last-ack-len (fn-tcl-result-events (fn-tcl-drive s octets)) id)
                         (len data))
                  (or (null (fn-tcl-declared-total segs))
                      (equal (fn-tcl-declared-total segs) (len data)))))))

(defthm fn-tcl-ack-length-is-cumulative
  ;; every XFER_ACK emitted for id carries the sum of data lengths received
  ;; so far for id, with the flags of the segment it answers (§5.2.3)
  ...)

(defthm fn-tcl-sender-acknowledged-requires-final-ack
  (implies (and (fn-tcl-sessionp s)
                (equal (fn-tcl-outbound-status (fn-tcl-find-outbound (fn-tcl-result-session (fn-tcl-drive s octets)) id))
                       :acknowledged))
           (fn-tcl-received-ack-with s octets id :end (len (fn-tcl-outbound-octets (fn-tcl-find-outbound s id))))))
```

**C3. An interrupted transfer resumes or is refused, never partially
delivered.** TCPCLv4 has no in-session resumption; "resume" is the
scheduler retrying the bundle in a later session, and a receiver that already
holds the bundle answers `Completed` (which `fn-bpn-forward-result` counts as
`:sent`).

```lisp
(defthm fn-tcl-inbound-outcomes-are-exhaustive
  ;; every inbound id that saw START ends in exactly one of: a
  ;; :bundle-received event, a :refused reason, or a :transfer-failed event on
  ;; tcp close; the staged object of a refused or failed transfer is released
  ;; and never named by a :bundle-received event
  (implies (and (fn-tcl-sessionp s) (fn-tcl-started-inbound-p s id))
           (fn-tcl-exactly-one (fn-tcl-inbound-outcome (fn-tcl-closure s events) id)
                               '(:complete :refused :failed))))

(defthm fn-tcl-tcp-close-never-completes-a-transfer
  (implies (and (fn-tcl-sessionp s) (fn-tcl-inbound s)
                (not (fn-tcl-inbound-ended (fn-tcl-inbound s))))
           (and (not (member-equal-kind :bundle-received (fn-tcl-result-events (fn-tcl-tcp-closed s))))
                (member-equal (list :transfer-failed (fn-tcl-inbound-xfer-id (fn-tcl-inbound s)))
                              (fn-tcl-result-events (fn-tcl-tcp-closed s))))))

(defthm fn-tcl-refused-transfer-sends-no-more-segments
  (implies (and (fn-tcl-sessionp s)
                (equal (fn-tcl-outbound-status (fn-tcl-find-outbound s id)) (list :refused r)))
           (not (fn-tcl-emits-segment-for (fn-tcl-result-events (fn-tcl-send s id2 octets)) id))))
```

**C4. Discipline and bounds.**
`fn-tcl-no-interleaving` (a second START while an inbound is live is
rejected and no second inbound is created), `fn-tcl-refuse-only-after-preceding-settled`
(§5.2.4 MUST: a refusal for id implies every earlier id was fully acked or
refused), `fn-tcl-segment-never-exceeds-mru` (the decoder returns `(:error
:segment-exceeds-mru)` without taking data when `data-len > segment-mru`, and
no `(:need k)` is ever answered with `k` larger than the MRU plus the fixed
header), `fn-tcl-ending-refuses-new-transfers`,
`fn-tcl-keepalive-zero-disables-both` (no KEEPALIVE emitted and no
`Idle timeout` when the negotiated interval is 0),
`fn-tcl-negotiation-is-min-and-and` (keepalive is the min of the two, MTUs are
the peer's MRUs, TLS is the conjunction), `fn-tcl-drive-preserves-sessionp`,
`fn-tcl-retained-input-is-bounded` (the unconsumed carry is shorter than one
maximal message).

### 2.4 Host integration in the native host, and the adapter retired

The uncommitted `build/lanes/w3-native-host/host/native/io.lisp` already
puts `sb-bsd-sockets` (`fnn-recv`, `fnn-send-all`, `fnn-serve-client`,
`fnn-graceful-close`) under the trust tag `:fn-native-host` and reaches the
core through `fnn-call` on `:program` wrappers. TCPCL is added to that
surface and nowhere else:

- `host/tcpcl-host.lisp` (`:program` wrappers over `fn-tcl-drive`,
  `fn-tcl-tick`, `fn-tcl-send`, `fn-tcl-terminate`, `fn-tcl-tcp-closed`, each
  marshalling one session global keyed by session id, like
  `fn-sched-host-install`).
- `host/bp-node-host.lisp` (wrappers over `fn-bpn-step`, threading the
  workflow and scheduler globals read-only for `fn-bpn-obligation-openp`).
- `host/native/tcpcl.lisp` (raw): `fnn-tcl-listen port`, `fnn-tcl-connect
  host port` (both `AF_INET6`, no TLS in wave 4), and one `fnn-tcl-session
  fd role` loop: read at most `segment-mtu + 32` octets, prepend the carry,
  `fnn-call fn-tcl-host-drive`, write every emitted message with the
  partial-write offset tracked per HST-002, deliver `:bundle-received` to
  `fn-bpn-host-step` **after** the FNBS `:bundle-stored` record is barriered,
  and only then emit the final XFER_ACK (so an ack is fn's durable acceptance
  of the octets, which is stronger than RFC 9174 requires and is what makes
  the ack meaningful to a peer that retries on failure). Keepalive ticks come
  from the same monotonic source the clock observation uses.
- Sessions are opened by the scheduler's contact: `fn-sched-open-event` for
  a peer whose CL address is configured makes the host connect (active) or
  accept only that peer's address (passive); `fn-sched-close-event` sends
  SESS_TERM. A session established to a node ID other than the contact's
  configured peer is terminated `Contact Failure` (RFC 9174 §4.6: an
  unauthenticated node ID SHOULD NOT drive routing; fn routes by contact plan
  and never by the announced ID).

Retired, all of it: `tools/bpa_dtn7.py`, `tools/bpa_payload_extract.rs`,
`tests/bp-dtn7/build_payload_extractor.sh`, the `stage_inbound`,
`inbound_items`, BID and `MAX_BPA_INVENTORY` parts of
`tools/workflow_journal.py` and the FNBI inbox format, the BID-keyed parts of
`tools/run_bp_receive.py` (its `receive_bpa_request` becomes the `:deliver`
effect into `fn-bpr-accept-request` in the native host), `tests/bp-dtn7/lab_bpa.py`,
`bp_fn_ingress_driver.py`, `fn_sender_lab.py`, `run_fn_exchange_lab.py`,
`run_fn_ingress_lab.sh`, `run_two_node.sh`, and the transport statuses
`:bpa-submit-replied`, `:inbound-persisted`, `:dequeued` in
`fn-bp-transport-statusp` (§5.2 of the migration). `tests/bp-dtn7/bootstrap.sh`
and `pin.json` survive because the pinned dtn7-rs is still built — as a peer.

## 3. Interoperability plan

The lab stops being "fn polls its own daemon" and becomes fn speaking TCPCLv4
to nodes it does not control, over a link it can break.

| Lab | Peer | Transport | What it establishes |
| --- | --- | --- | --- |
| I1 fn–fn | fn | TCPCLv4 between two Linux network namespaces on hbox (`ip netns add fnA/fnB`, a veth pair, `tc qdisc add ... netem delay 200ms loss 5%` and `ip link set down` mid-transfer) | C1–C4 against real sockets: partition (chunk size sweep 1, 7, 1500, 65536), pipelined segments, interruption at every message boundary, restart both sides, expiry across a delay, fragmentation at a small Transfer MRU and reassembly |
| I2 fn–dtn7-rs | the pinned dtn7-rs (`tests/bp-dtn7/pin.json`), configured with its `tcp` CLA (TCPCLv4) and **no** HTTP client on fn's side | that fn's primary and canonical block encodings are accepted by an independent BPv7 implementation and vice versa, including Previous Node, Bundle Age and Hop Count round trips; status reports requested by dtn7-rs and generated by fn; each XFER_REFUSE reason provoked |
| I3 fn–ION | ION-DTN (`tcpcli`/`tcpclo` inducts and outducts), built on hbox by the w3-ltp-ion lane | the same as I2 against the reference implementation; ION's `ipn` scheme exercised (RFC 9758 updates `ipn`; fn's `ipn` codec must be checked against it before I3 is claimed) |
| I4 fn–relay–fn | fn as the middle node, non-overlapping contact windows | §5.4 forwarding with Previous Node insertion and Bundle Age increment through a real store-and-forward hop; `relay` book's undertaking on top |
| I5 two machines | hbox and persvati over the actual network, not loopback, not a namespace | that nothing in I1–I4 depended on a single kernel |

Each lab writes an evidence record under `tests/evidence/` in the existing
form (exact revisions, ports, the message trace, what was *not* shown).
Interoperability is claimed per lab and per feature row, never as "fn
interoperates".

dtn7-rs also speaks MTCP (`draft-burleigh-dtn-mtcpcl`, a length-prefixed
bundle stream). It is not built: it is not the standard CL and would only
defer the TCPCL work. `draft-ietf-dtn-udpcl-04` (BPv7 over UDP) is noted as
a candidate third CL after LTP, not before.

**LTP later, through ION.** RFC 5326 is the second CL, exercised first
against ION's `ltpcli`/`ltpclo` over `udplsi`/`udplso`. The fn side is a
later `books/ltp.lisp` (`fn-ltp-*`) with the same discipline as §2: the
segment grammar (control byte with CTRL/EXC/flag bits, SDNV lengths bounded
before allocation), red/green parts, checkpoints and report segments, the
cancel handshake, and theorems that a red part is signalled to the node only
on a complete reception report, and that a green part is never signalled as
reliable. LTP's block is a bundle; its client is `fn-bpn-receive`, unchanged.
The w3-ltp-ion lane's `tests/ltp/` is where that harness starts.

## 4. Security posture

fn's authority today is noncryptographic: A-POLICY is an explicit `t` in the
lab (bp-receipt.md), the peer node ID from SESS_INIT is unauthenticated, and
the receipt is unsigned (D09 open). This design does not hide that; it makes
the slots where verification goes explicit so that adding it is a profile
change, not a redesign.

**BPSec as a profile slot.** RFC 9172 defines the Block Integrity Block
(type 11) and Block Confidentiality Block (type 12) as canonical blocks whose
block-type-specific data is an Abstract Security Block: security targets (an
array of block numbers), security context ID, security context flags,
security source (an EID), optional context parameters, and per-target
security results. RFC 9173 fixes the two default contexts, BIB-HMAC-SHA2
(context 1) and BCB-AES-GCM (context 2). Packet 8 adds `books/bpsec.lisp`
(`fn-bps-*`): the ASB grammar, bounded, both directions, canonical; the
target rules (a BCB targeting the payload also protects any BIB over it;
block 0 may be a BIB target and then the primary CRC type may be 0, which
today fn treats as unprotected by policy, bp-primary.md); and the
verification function as a **constrained** function under an `encapsulate`,
`(fn-bps-verify context params key-ref target-octets result) -> :verified |
:failed | :unsupported`, whose real implementation is the host's trusted
cryptographic primitive (HST-004, A-CRYPTO). Nothing in the certified books
computes an HMAC.

What the receiver would verify, under `fn-bpn-security-policy` per peer:

| Policy | `fn-bpn-receive` step 3' (after CRCs, before storing) |
| --- | --- |
| `:none` (wave 4) | nothing; a zero-CRC primary block is refused `:block-unintelligible` because no BIB can be checked |
| `:require-bib-primary` | a BIB whose targets include block 0, from the configured security source for that peer, verifies; else delete `:block-unintelligible` (RFC 9172 §3.10's "security operation failed" reason code when registered) |
| `:require-bib-payload` | the same for block 1 |
| `:accept-bcb-payload` | a BCB over block 1 is decrypted before delivery only; a bundle that is forwarded keeps its BCB and is never decrypted at a transit node |

Theorem to carry with the slot:

```lisp
(defthm fn-bpn-deliver-under-policy-requires-verified-targets
  (implies (and (fn-bpn-statep st)
                (equal (fn-bpn-policy-for st peer) :require-bib-payload)
                (member-equal (list :deliver id key ref (list :cl sid xid peer))
                              (fn-bpn-effects st event)))
           (equal (fn-bpn-verification-of st id 1) :verified)))
```

and `fn-bpn-transit-never-decrypts` (a `:cl-send` image for a bundle with a
BCB carries the BCB and the ciphertext unchanged).

**TCPCL TLS** (RFC 9174 §4.4) is the other slot: `CAN_TLS` negotiation is
modeled now (`fn-tcl-negotiation-is-min-and-and`), the handshake is a host
primitive later, and node-ID authentication (§4.4.4.3) is what would let the
announced node ID drive anything. Until then fn binds sessions to the contact
plan's configured peer and address, and the threat in §7.9 (node
impersonation) is mitigated only by that binding and by A-POLICY. That is
stated, not solved.

## 5. Migration, in ordered packets

Each packet names its owner lane, what it deletes, and what must be true
before it is merged. "Certifies" means the Makefile target list grows and
`make certify` is green on a clean tree; every theorem named is stated as in
this document or the packet's spec says why it changed.

| # | Packet | Owner | Deliverables | Acceptance |
| --- | --- | --- | --- | --- |
| 0 | Bundle frame | core | `books/bp-bundle`, `-invariants`, `tests/acl2/bp-bundle-tests`; `specs/bp-bundle.md` | `fn-bpb-decode-of-encode`, `fn-bpb-accepted-input-is-canonical`, `fn-bpb-block-numbers-unique`, bounds theorem; vectors: the `bp7` crate's `doc/encoding_samples.md` blocks (with the stale-SSP caveat already recorded) and an ION-emitted bundle captured in lab I3 |
| 1 | Bundle store records | core + host | FNBS record family in `books/frame`, replay in `books/bp-node-records`, `(:bpn-sequence n)` frontier | `fn-bpn-replay-journal-is-trace`; the five process-death cuts of `tests/test_bp_receive_process_crash.py` re-targeted at FNBS |
| 2 | Fragment lemmas | core | `fn-bpf-cut-covers`, `fn-bpf-reassemble-ok-agrees-with-every-fragment` uncommented and proved | both certify; T4 stated and certified against them |
| 3 | Node machine | core | `books/bp-node`, `-invariants`, teeth; `specs/bp-node.md` | T1, T2, T3, T5, T6 certified; each with a concrete tooth (a fabricated `validated` bundle with a bad CRC is not `fn-bpn-statep`; a `:clock` event with `:uncertain` deletes nothing; an admin-record bundle produces no `:deliver`) |
| 4 | TCPCL books | core | `books/tcpcl-octets`, `-records`, `-session`, `-invariants`, teeth; `specs/tcpcl.md` | codec round trip and canonicality; C1–C4 certified; the partition tooth is the chunk-size sweep as `assert-event`s |
| 5 | Native host | host | `host/tcpcl-host.lisp`, `host/bp-node-host.lisp`, `host/native/tcpcl.lisp`; `tools/fn_native.py` grows `serve-tcpcl` and `connect-tcpcl`; lab I1 | I1 evidence record; fn–fn exchange with the receipt returning over TCPCL; SIGKILL at every message boundary recovers per T2/T6; **deletes** `tools/bpa_dtn7.py`, `tools/bpa_payload_extract.rs`, `tests/bp-dtn7/build_payload_extractor.sh`, `lab_bpa.py`, `bp_fn_ingress_driver.py`, `fn_sender_lab.py`, `run_fn_exchange_lab.py`, `run_fn_ingress_lab.sh`, `run_two_node.sh`, the FNBI inbox code in `workflow_journal.py`, and `tests/test_bp_receive*.py` (replaced by native-host tests) |
| 6 | Workflow and scheduler alignment | core (sender-proofs) + scheduler | `fn-bp-transport-statusp` becomes `:intent :bundle-created :attempted :forwarded :delivered :expired :deleted :lost :no-contact :restart :unknown` (rank preserved; the three BPA-era statuses removed); `fn-sched-open-event`/`close-event` drive CL sessions; `fn-bpi-context-bundle-id` becomes an `fn-bpp-bundle-id` | `bp-workflow*`, `bp-workflow-transport-invariants`, `scheduler*`, `bp-ingress*` re-certify; `fn-bp-observe-transport-never-moves-status-backward` unchanged in statement |
| 7 | Interop labs | lab | I2 (dtn7-rs peer), I3 (ION peer), I4 (relay), I5 (hbox–persvati); reactive fragmentation on `No Resources` | one evidence record per lab with the feature matrix; no row claimed without its trace |
| 8 | BPSec slot | core + host | `books/bpsec`, the `encapsulate`d `fn-bps-verify`, policy table; host HMAC-SHA2 under A-CRYPTO | `fn-bpn-deliver-under-policy-requires-verified-targets`, `fn-bpn-transit-never-decrypts`; RFC 9173 Appendix A test vectors |
| 9 | LTP | core + lab (w3-ltp-ion) | `books/ltp`, `host/native/ltp.lisp` (UDP), lab against ION | red-part completeness theorem; evidence record |

### 5.1 Which books survive

| Book | Fate |
| --- | --- |
| `bp-adu` | survives unchanged: it is the payload profile of fn-originated bundles |
| `bp-primary`, `bp-primary-cbor`, `bp-primary-invariants` | survive unchanged; gain their first caller in packet 0 |
| `bp-fragment`, `-invariants` | survive; two open lemmas closed in packet 2 |
| `clock`, `-invariants` | survive unchanged; gain their first caller in packet 3 |
| `bp-workflow*` | survive; transport status set edited in packet 6 with re-certification |
| `bp-receipt*`, `bp-receiver-*` | survive unchanged; `fn-bpr-accept-request` is the delivery registration; BID never appears in them today and still does not |
| `bp-release`, `-invariants` | survive unchanged |
| `relay`, `-invariants`, `-crash-invariants` | survive unchanged; the relay's undertaking is the application-layer forwarding promise, composed over the node's §5.4 forwarding, which itself issues no receipt |
| `scheduler`, `-invariants` | survive; contact open/close gain the session effect in packet 6 |
| `bp-ingress`, `bp-outbound` | survive; the context's bundle id changes type in packet 6 |
| `frame`, `bp-workflow-records`, `bp-receipt-records` | survive; FNBS added, FNBI removed |
| `wire`, `wire-invariants` | untouched; its partition theorem is the pattern for C1 |

### 5.2 Which host code is deleted

Listed under packet 5. The principle: after packet 5 no fn process speaks
HTTP to a BPA, no fn process runs an upstream BP decoder, and the only
program that parses a bundle is the certified core. The pinned dtn7-rs
checkout remains a lab dependency in the same sense ION is: a peer.

## What this design does not decide

- D01/D09 (native encoding, signing) and the receipt authority: unchanged and
  still open; §4 shows where they plug in.
- Routing beyond the contact plan (SABR, epidemic): out of scope; the
  scheduler's contact is the only route.
- Flight or space-link qualification: none; I5 is two machines on one
  network.
- ION's actual TCPCL behaviour and RFC 9758 `ipn` details: to be measured in
  lab I3, not assumed here.
