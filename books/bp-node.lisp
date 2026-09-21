; books/bp-node.lisp -- fn as a BPv7 node: what it puts on the wire and what
; it does with what arrives.
;
; SCOPE, said before anything else.  `specs/bp-design.md` section 1.5 designs a
; full processing machine: a bundle store, retention constraints, reassembly,
; status reports, a dispatcher and a trace.  This book is not that machine.  It
; is the two ends the convergence layer actually touches --
;
;   `fn-bpn-send`     an ADU and this node's configuration become the octets
;                     of one complete BPv7 bundle;
;   `fn-bpn-receive`  a peer's octets become an accepted bundle, a refusal or
;                     an uncertain outcome, with the ADU recovered from the
;                     payload block;
;
; -- together with the two decisions RFC 9171 section 5.4 requires before a
; bundle may be forwarded: lifetime expiry (section 5.5) and hop count
; (section 4.4.3).  The store, the constraints, reassembly and status reports
; are open; `specs/bp-design.md` section 1.5 carries them and says so.
;
; What this buys the host: `bp send` is not `tcpcl send` with a contact check.
; The octets it hands the convergence layer are a bundle this node authored,
; with its own node ID as the source, its clock observation as the creation
; timestamp and its configured lifetime; the octets `bp receive` accepts are a
; bundle this node decoded, whose ADU it recovered, and whose lifetime and hop
; count it checked.

(in-package "ACL2")

(include-book "bp-bundle-invariants")

; CERTIFIED 2026-09-21 (w11/bp-node), the first time this book ever has been.
; Three things had to change and each is recorded where it is, because each
; was invisible until the event before it closed -- `certify-book` stops at
; the first failure, so "everything else closes" had never been a statement
; about anything after `fn-bpn-receive`.
;
;   1. `books/bp-primary` now WITHDRAWS its six projections
;      (`fn-bpp-projection-vocabulary`).  `fn-bpn-receive`'s guard is
;      `fn-bpp-fragmentp`'s `(natp flags)` on the primary of a decoded
;      bundle; with the projection enabled the goal read
;      `(integerp (nth 1 primary))` and every fact available was about
;      `fn-bpp-blockp` or `(fn-bpp-flags primary)`.
;   2. The bridge that carries that fact is forward-chaining ONLY.  As a
;      rewrite AND a forward-chaining rule concluding
;      `(fn-bpp-flag-setp (fn-bpp-flags p))` it collapsed its own
;      forward-chained literal to T on the way into the context and added
;      nothing; the guard goal was pushed for induction with the fact
;      "available" throughout.
;   3. K5 is stated BEFORE K1, because K1's only route from `fn-bpb-decode`
;      to `fn-bpb-encode` is `fn-bpb-decode-of-encode`, whose first
;      hypothesis is exactly K5.
;
; Still true of this book, and not a defect: it is the two ends of
; `specs/bp-design.md` section 1.5 and not the machine.  T1 to T6 of section
; 1.6 are stated against an `fn-bpn-step` that does not exist and are NOT
; proved here or anywhere.

(include-book "clock")
(include-book "defrecord")

; -----------------------------------------------------------------------------
; Configuration
;
; A node ID (RFC 9171 section 4.2.5.2), the lifetime it stamps on its own
; bundles, the CRC type it writes, the hop limit it writes, and the largest
; transfer it will decode.  The last is the convergence layer's transfer MRU:
; `fn-bpn-receive` passes it to `fn-bpb-decode` as the bound applied before
; the first octet is examined.

(defun fn-bpn-hop-limitp (x)
  (declare (xargs :guard t))
  (and (natp x) (<= 1 x) (<= x 255)))

(defun fn-bpn-transfer-limitp (x)
  (declare (xargs :guard t))
  (and (posp x) (<= x *fn-bpb-max-input*)))

(verify-guards fn-bpn-hop-limitp)
(verify-guards fn-bpn-transfer-limitp)

(fn-defrecord fn-bpn-config
  :tag :fn-bpn-config
  :constructor (fn-bpn-config node-id lifetime crc-type hop-limit transfer-limit)
  :fields ((fn-bpn-config-node-id fn-bpp-previous-nodep)
           (fn-bpn-config-lifetime fn-bpp-timep)
           (fn-bpn-config-crc-type fn-bpp-crc-typep)
           (fn-bpn-config-hop-limit fn-bpn-hop-limitp)
           (fn-bpn-config-transfer-limit fn-bpn-transfer-limitp))
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

; The block numbers fn writes.  Section 4.1 reserves 0 for the primary block
; and 1 for the payload block; fn numbers its two extension blocks 2 and 3 and
; writes no others, so `fn-bpb-numbers-distinctp` holds by construction.
(defconst *fn-bpn-hop-count-block-number* 2)
(defconst *fn-bpn-bundle-age-block-number* 3)

; -----------------------------------------------------------------------------
; Sending
;
; Section 4.2.6: a creation timestamp time of zero means the node had no
; accurate clock.  fn writes its wall reading when it has one and zero when it
; does not -- never a monotonic counter dressed as a DTN time.

(defun fn-bpn-creation-time (obs)
  (declare (xargs :guard (fn-clock-observationp obs)))
  (if (fn-clock-has-wall obs) (fn-clock-wall obs) 0))

(defun fn-bpn-send-blocks (config)
  (declare (xargs :guard (fn-bpn-configp config)))
  (list (fn-bpb-hop-count-block *fn-bpn-hop-count-block-number* 0
                                (fn-bpn-config-crc-type config)
                                (fn-bpp-make-hop-count
                                 (fn-bpn-config-hop-limit config) 0))
        (fn-bpb-bundle-age-block *fn-bpn-bundle-age-block-number* 0
                                 (fn-bpn-config-crc-type config)
                                 0)))

(defun fn-bpn-send-bundle (config peer adu sequence obs)
  (declare (xargs :guard (and (fn-bpn-configp config)
                              (fn-bpp-eidp peer)
                              (fn-bpb-datap adu)
                              (fn-bpp-timep sequence)
                              (fn-clock-observationp obs))))
  (fn-bpb-make-bundle
   (fn-bpp-make-block 0 (fn-bpn-config-crc-type config)
                      peer
                      (fn-bpn-config-node-id config)
                      (fn-bpn-config-node-id config)
                      (fn-bpn-creation-time obs)
                      sequence
                      (fn-bpn-config-lifetime config)
                      nil nil)
   (fn-bpn-send-blocks config)
   (fn-bpb-payload-block (fn-bpn-config-crc-type config) adu)))

; `fn-bpb-encode`'s guard is `fn-bpb-bundlep`, so this function's guard
; obligation IS keystone K5 below (`fn-bpn-send-bundle-is-a-bundle`), which
; is stated where the keystones are.  Deferred here and discharged there --
; the caller-discharges-the-callee's-guard pattern of
; docs/proof-style.md section 4.  `bp send` reaches this function through
; `fnn-call`, which checks the guard on every call, so the verification is
; mandatory and is done, only later in the file.
(defun fn-bpn-send (config peer adu sequence obs)
  (declare (xargs :guard (and (fn-bpn-configp config)
                              (fn-bpp-eidp peer)
                              (fn-bpb-datap adu)
                              (fn-bpp-timep sequence)
                              (fn-clock-observationp obs))
                  :verify-guards nil))
  (fn-bpb-encode (fn-bpn-send-bundle config peer adu sequence obs)))

; -----------------------------------------------------------------------------
; The three outcomes, kept distinct all the way out (AGENTS.md, D13).
;
;   (:accepted bundle)     decoded, in lifetime, within its hop limit
;   (:refused reason)      decided against, with the reason
;   (:uncertain bundle r)  the clock cannot decide the lifetime question; the
;                          bundle is not refused and is not accepted

(defun fn-bpn-accepted (bundle) (declare (xargs :guard t)) (list :accepted bundle))
(defun fn-bpn-refused (reason) (declare (xargs :guard t)) (list :refused reason))
(defun fn-bpn-uncertain (bundle reason)
  (declare (xargs :guard t)) (list :uncertain bundle reason))

(defun fn-bpn-acceptedp (r)
  (declare (xargs :guard t))
  (and (consp r) (eq (fn-cbor-ag-car r) :accepted)))
(defun fn-bpn-refusedp (r)
  (declare (xargs :guard t))
  (and (consp r) (eq (fn-cbor-ag-car r) :refused)))
(defun fn-bpn-uncertainp (r)
  (declare (xargs :guard t))
  (and (consp r) (eq (fn-cbor-ag-car r) :uncertain)))
(defun fn-bpn-outcome-bundle (r)
  (declare (xargs :guard t))
  (fn-cbor-ag-car (fn-cbor-ag-cdr r)))
(defun fn-bpn-outcome-reason (r)
  (declare (xargs :guard t))
  (if (fn-bpn-refusedp r)
      (fn-cbor-ag-car (fn-cbor-ag-cdr r))
    (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr r)))))

(verify-guards fn-bpn-accepted)
(verify-guards fn-bpn-refused)
(verify-guards fn-bpn-uncertain)
(verify-guards fn-bpn-acceptedp)
(verify-guards fn-bpn-refusedp)
(verify-guards fn-bpn-uncertainp)
(verify-guards fn-bpn-outcome-bundle)
(verify-guards fn-bpn-outcome-reason)

; -----------------------------------------------------------------------------
; The lifetime and hop-count questions
;
; Section 4.4.2: the Bundle Age block carries the bundle's accumulated age in
; milliseconds.  Anchoring it at the local monotonic reading of arrival is
; what `books/clock` calls an age anchor, and it is what makes the expiry
; decision usable on a node with no wall clock.

; The one bridge the guards below need, and the reason they do not open
; `fn-bpb-bundlep`.  `fn-bpb-decode-yields-bundle` is an exported REWRITE
; whose conclusion is `(fn-bpb-bundlep ...)`; with that recognizer enabled
; the target opens before the rule can fire, so the rule never applies and
; the field types never arrive.  Closed, the rule puts `(fn-bpb-bundlep x)`
; in the context as a literal and this lemma takes it the one step the
; callees want.
(local
 (defthm fn-bpn-bundle-primary-is-a-block
   (implies (fn-bpb-bundlep bundle)
            (fn-bpp-blockp (fn-bpb-bundle-primary bundle)))
   ;; FORWARD-chaining, triggered on the projection: the guard goals are in
   ;; the primary's field vocabulary, not in `fn-bpp-blockp`, so a rewrite
   ;; rule with that conclusion has nothing to fire on.  Forward-chained,
   ;; the literal lands in the context and the enabled recognizer opens it
   ;; into exactly the field facts the callees want.
   :rule-classes (:rewrite
                  (:forward-chaining
                   :trigger-terms ((fn-bpb-bundle-primary bundle))))
   :hints (("Goal" :in-theory (e/d (fn-bpb-bundlep)
                                   (fn-bpp-blockp fn-bpp-eidp
                                    fn-bpp-vchar-listp fn-bpp-vcharp))))))

(defun fn-bpn-anchor-of (bundle obs)
  (declare (xargs :guard (and (fn-bpb-bundlep bundle)
                              (fn-clock-observationp obs))))
  (let ((ms (fn-bpb-bundle-age bundle)))
    (if (fn-clock-timep ms)
        (cons ms (fn-clock-monotonic obs))
      nil)))

; The guard wants the primary block's creation time and lifetime to be
; times, which is two conjuncts of `fn-bpp-blockp`, which is one conjunct of
; `fn-bpb-bundlep`.  Both recognizers are withdrawn by their books' export
; theories, so the obligation cannot be discharged without opening them HERE
; --- and only here.  The endpoint-ID and octet-list vocabulary underneath
; stays closed: it is the fan, and none of it is about a time.
(defun fn-bpn-expiry (bundle obs)
  (declare (xargs :guard (and (fn-bpb-bundlep bundle)
                              (fn-clock-observationp obs))
                  :guard-hints
                  (("Goal"
                    :in-theory (e/d (fn-bpb-bundlep fn-bpp-blockp
                                     fn-clock-age-anchorp
                                     fn-clock-observationp)
                                    (fn-bpp-eidp fn-bpp-vchar-listp
                                     fn-bpp-vcharp fn-cbor-octet-listp
                                     fn-cbor-octetp fn-bpb-block-listp
                                     fn-bpb-blockp
                                     ;; The fragment bit is a bit test, and
                                     ;; opened it puts `numerator` and
                                     ;; `denominator` parity goals in front
                                     ;; of a guard about times.  It is
                                     ;; carried, not decided, here.
                                     fn-bpp-fragmentp fn-bpp-flag-onp))))))
  (let ((primary (fn-bpb-bundle-primary bundle)))
    (fn-clock-expiry-decision (fn-bpp-creation-time primary)
                              (fn-bpp-lifetime primary)
                              (fn-bpn-anchor-of bundle obs)
                              obs)))

; Section 4.4.3: a bundle whose hop count exceeds its hop limit is to be
; deleted.  A bundle with no Hop Count block has no hop question to answer.
(defun fn-bpn-hop-exceededp (bundle)
  (declare (xargs :guard (fn-bpb-bundlep bundle)))
  (let ((hop (fn-bpb-bundle-hop-count bundle)))
    (and (fn-bpp-hop-countp hop)
         (fn-bpp-hop-limit-exceededp hop))))

; The hop count this node would write when forwarding: one more than what
; arrived.  Section 4.4.3 says the count is increased by one at each
; forwarding node.
(defun fn-bpn-next-hop-count (hop)
  (declare (xargs :guard (fn-bpp-hop-countp hop)))
  (fn-bpp-make-hop-count (nth 1 hop) (+ 1 (nth 2 hop))))

(verify-guards fn-bpn-anchor-of)
(verify-guards fn-bpn-expiry)
(verify-guards fn-bpn-hop-exceededp)
(verify-guards fn-bpn-next-hop-count)

; -----------------------------------------------------------------------------
; Receiving
;
; RFC 9171 section 5.6, in the order it fixes: the bundle is decoded before
; anything is kept (a bundle that does not decode is never stored), the block
; flags are checked against section 4.2.3, and the lifetime question is asked
; before the bundle is treated as deliverable.
;
; Fragments are refused rather than reassembled.  `books/bp-fragment` has the
; reassembly; wiring it in is an open item of `specs/bp-design.md` section 1.5
; and is not claimed here.

; And the same step for a DECODED bundle, which is the one `fn-bpn-receive`
; needs: `fn-bpb-decode-yields-bundle` is a rewrite whose left-hand side is
; `(fn-bpb-bundlep ...)`, and the guard goals below are in the primary's
; field vocabulary, where that term never appears.  Forward-chained from the
; projection, the field facts arrive.
(local
 (defthm fn-bpn-decoded-primary-is-a-block
   (implies (fn-cbor-result-okp (fn-bpb-decode octets limit))
            (fn-bpp-blockp
             (fn-bpb-bundle-primary
              (fn-cbor-result-value (fn-bpb-decode octets limit)))))
   :rule-classes (:rewrite
                  (:forward-chaining
                   :trigger-terms
                   ((fn-bpb-bundle-primary
                     (fn-cbor-result-value (fn-bpb-decode octets limit))))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance fn-bpb-decode-yields-bundle)
                  (:instance fn-bpn-bundle-primary-is-a-block
                             (bundle (fn-cbor-result-value
                                      (fn-bpb-decode octets limit)))))
            :in-theory (disable fn-bpb-decode-yields-bundle fn-bpb-decode
                                fn-bpp-blockp fn-bpb-bundlep)))))

; Everything `(fn-bpp-fragmentp (fn-bpp-flags primary))` needs of a decoded
; primary block, in ACCESSOR vocabulary rather than through the recognizer:
; `fn-bpp-flags` is guarded by `(true-listp b)` and `fn-bpp-fragmentp` by
; `(natp flags)`, and those two are the whole of what `fn-bpn-receive`'s
; guard is missing.
;
; Two measured constraints fix the shape of this lemma, and both were paid
; for on 2026-09-21.
;
;   * The conclusion is arithmetic, not `(fn-bpp-flag-setp ...)`.  A lemma
;     that both FORWARD-CHAINS `(fn-bpp-flag-setp (fn-bpp-flags p))` and is
;     an enabled REWRITE with that same left-hand side adds a literal its own
;     rewrite immediately collapses to T, so the context gains nothing; the
;     guard goal was pushed for induction as `*18` with the fact "available"
;     the whole time.  This is the BRIEF's rule about a local `defthm`
;     concluding a recognizer call, one layer further in: the collapse
;     happens to a FORWARD-CHAINED literal, not to a `:use` hypothesis.
;   * It has NO rewrite class at all, for the same reason.  Forward chaining
;     is the only class that can put a fact about a term the conclusion does
;     not contain into the context.
;
; And it is stated over `(fn-bpp-flags p)` rather than `(nth 1 p)` because
; `books/bp-primary` now withdraws its projections
; (`fn-bpp-projection-vocabulary`); before that withdrawal the accessor was
; unfolded out of the goal before any rule could match it.
(local
 (defthm fn-bpn-decoded-primary-flag-test-is-guarded
   (implies (fn-cbor-result-okp (fn-bpb-decode octets limit))
            (and (true-listp
                  (fn-bpb-bundle-primary
                   (fn-cbor-result-value (fn-bpb-decode octets limit))))
                 (integerp
                  (fn-bpp-flags
                   (fn-bpb-bundle-primary
                    (fn-cbor-result-value (fn-bpb-decode octets limit)))))
                 (<= 0
                     (fn-bpp-flags
                      (fn-bpb-bundle-primary
                       (fn-cbor-result-value (fn-bpb-decode octets limit)))))
                 (<= (fn-bpp-flags
                      (fn-bpb-bundle-primary
                       (fn-cbor-result-value (fn-bpb-decode octets limit))))
                     *fn-bpc-max-uint*)))
   :rule-classes ((:forward-chaining
                   :trigger-terms
                   ((fn-bpb-bundle-primary
                     (fn-cbor-result-value (fn-bpb-decode octets limit))))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance fn-bpn-decoded-primary-is-a-block))
            ;; `fn-bpn-bundle-primary-is-a-block` and
            ;; `fn-bpb-decode-yields-bundle` are disabled because they are
            ;; ENABLED rewrites whose left-hand sides are the `:use`d
            ;; hypothesis: left on, they collapse it to T and the citation
            ;; is gone (the same hazard the generated `-of-accessors`
            ;; family has -- see BOARD 2026-09-20, w10/dtn-3).
            ;; `fn-bpp-flag-setp` is left ENABLED here, unlike in the block
            ;; bridge above: it is the step from the recognizer's conjunct
            ;; to the arithmetic this lemma concludes.
            :in-theory (e/d (fn-bpp-blockp)
                            (fn-bpn-decoded-primary-is-a-block
                             fn-bpn-bundle-primary-is-a-block
                             fn-bpb-decode-yields-bundle
                             fn-bpb-decode fn-bpp-eidp fn-bpp-vchar-listp
                             fn-bpp-vcharp
                             fn-bpp-fragmentp fn-bpp-flag-onp))))))

; Same guard shape as `fn-bpn-expiry`, and for the same reason: the callees
; want the decoded primary block's fields typed, which is
; `fn-bpb-decode-yields-bundle` (exported by
; `books/bp-bundle-invariants`) followed by two conjuncts of two withdrawn
; recognizers.  Opened here and nowhere else.
(defun fn-bpn-receive (config octets obs)
  (declare (xargs :guard (and (fn-bpn-configp config)
                              (fn-cbor-octet-listp octets)
                              (fn-clock-observationp obs))
                  ;; The conjecture here is only the CALLEES' guards, and
                  ;; every callee is guarded by `fn-bpb-bundlep` or
                  ;; `fn-bpp-blockp`, both discharged by the two bridges
                  ;; above.  So nothing is opened: not the recognizers, and
                  ;; not the callees themselves.  Measured 2026-09-20: with
                  ;; `fn-pp-flags-conformantp` left enabled the conjecture
                  ;; turns into `(integerp (nth 1 ...))` over an opened
                  ;; primary and there is nothing in that vocabulary to
                  ;; discharge it with.
                  :guard-hints
                  (("Goal"
                    :in-theory (e/d (fn-clock-observationp)
                                    (fn-bpp-eidp fn-bpp-vchar-listp
                                     fn-bpp-vcharp fn-cbor-octet-listp
                                     fn-cbor-octetp fn-bpb-block-listp
                                     fn-bpb-blockp fn-bpb-bundlep
                                     fn-bpp-blockp
                                     fn-bpp-fragmentp fn-bpp-flag-onp
                                     fn-bpp-flags-conformantp
                                     fn-bpn-hop-exceededp fn-bpn-expiry
                                     fn-bpn-anchor-of
                                     fn-bpb-bundle-hop-count
                                     fn-bpb-bundle-age
                                     fn-bpb-decode))))))
  (let ((d (fn-bpb-decode octets (fn-bpn-config-transfer-limit config))))
    (if (not (fn-cbor-result-okp d))
        (fn-bpn-refused (fn-cbor-result-value d))
      (let* ((bundle (fn-cbor-result-value d))
             (primary (fn-bpb-bundle-primary bundle)))
        (cond ((not (fn-bpp-flags-conformantp primary))
               (fn-bpn-refused :flags-not-conformant))
              ((fn-bpp-fragmentp (fn-bpp-flags primary))
               (fn-bpn-refused :fragment-not-reassembled))
              ((fn-bpn-hop-exceededp bundle)
               (fn-bpn-refused :hop-limit-exceeded))
              ((eq (fn-bpn-expiry bundle obs) :expired)
               (fn-bpn-refused :lifetime-expired))
              ((eq (fn-bpn-expiry bundle obs) :uncertain)
               (fn-bpn-uncertain bundle :lifetime-uncertain))
              (t (fn-bpn-accepted bundle)))))))

; The ADU an accepted bundle carries: the payload block's data and nothing
; else.  A caller that has not checked `fn-bpn-acceptedp` gets nil.
(defun fn-bpn-received-adu (r)
  (declare (xargs :guard t))
  (if (and (fn-bpn-acceptedp r) (fn-bpb-bundlep (fn-bpn-outcome-bundle r)))
      (fn-bpb-payload (fn-bpn-outcome-bundle r))
    nil))

(verify-guards fn-bpn-received-adu)

; -----------------------------------------------------------------------------
; Forwarding
;
; Section 5.4 steps 1 to 3 as one pure decision, restricted to the two
; questions this book answers.  Routing and contact windows belong to
; `books/scheduler`; this says only whether the bundle may be forwarded at
; all.

(defun fn-bpn-forward-decision (bundle obs)
  (declare (xargs :guard (and (fn-bpb-bundlep bundle)
                              (fn-clock-observationp obs))))
  (cond ((eq (fn-bpn-expiry bundle obs) :expired) (list :refuse :lifetime-expired))
        ((fn-bpn-hop-exceededp bundle) (list :refuse :hop-limit-exceeded))
        ((eq (fn-bpn-expiry bundle obs) :uncertain)
         (list :refuse :lifetime-uncertain))
        (t (list :forward))))

(defun fn-bpn-forwardp (decision)
  (declare (xargs :guard t))
  (and (consp decision) (eq (fn-cbor-ag-car decision) :forward)))

(verify-guards fn-bpn-forward-decision)
(verify-guards fn-bpn-forwardp)

; -----------------------------------------------------------------------------
; The three bridges above exist for ONE obligation, `fn-bpn-receive`'s
; guard, and they are closed here so that no keystone pays for them.
; Measured 2026-09-21 on K1: left open, its `Time:` line reads
; `427.20 seconds (prove: 0.43, other: 426.77)` -- seven minutes in which
; the prover did four tenths of a second of proof search.  `other` is
; forward chaining and type reasoning (docs/proof-style.md section 9.1), and
; two of these three ARE forward-chaining rules triggered on
; `(fn-bpb-bundle-primary (fn-cbor-result-value (fn-bpb-decode octets
; limit)))` -- a term K1's goal is full of.  The cure for that shape is a
; theory change and never a hint.
(local (in-theory (disable fn-bpn-decoded-primary-is-a-block
                           fn-bpn-decoded-primary-flag-test-is-guarded
                           fn-bpn-bundle-primary-is-a-block
                           ;; And the exported rule the three rest on, for
                           ;; the same reason: its left-hand side is
                           ;; `(fn-bpb-bundlep (fn-cbor-result-value
                           ;; (fn-bpb-decode ...)))` and every keystone
                           ;; below opens `fn-bpn-receive`, which puts that
                           ;; term in front of it.
                           fn-bpb-decode-yields-bundle)))

; -----------------------------------------------------------------------------
; Keystones.
;
; K5 IS STATED FIRST, and the order is load-bearing rather than cosmetic.  K1
; is the round trip, and the only rule that relates `fn-bpb-decode` to
; `fn-bpb-encode` is `fn-bpb-decode-of-encode`, whose first hypothesis is
; `(fn-bpb-bundlep bundle)` -- which for the bundle `fn-bpn-send` authors IS
; K5.  Measured 2026-09-21: with K1 first, as this book was written before it
; had ever certified, the form does not fail, it RUNS -- twenty minutes on
; hbox with no checkpoint, because the rewriter cannot relieve that
; hypothesis and falls back on induction over an encoder.

; The two extension blocks fn writes carry CBOR that this book never has to
; look inside.  `fn-bpc-enc-are-octets` and `fn-bpc-enc-length-bound` are
; exported by `books/bp-primary-cbor` and say everything `fn-bpb-datap`
; wants; what K5 must NOT do is let `fn-bpc-enc` unfold, because the goal
; then becomes `(FN-CBOR-OCTET-LISTP (CONS 130 (APPEND
; (FN-CBOR-ENCODE-ARGUMENT 0 (FN-BPN-CONFIG-HOP-LIMIT CONFIG)) '(0))))` and
; neither exported rule matches it any more (measured 2026-09-21).  So the
; two facts are proved here once, with the encoder CLOSED, and K5 closes it
; too.
(local
 (defthm fn-bpn-hop-count-data-is-block-data
   (implies (fn-bpp-hop-countp hop)
            (fn-bpb-datap (fn-bpp-hop-count-data hop)))
   :hints (("Goal"
            :in-theory (e/d (fn-bpb-datap fn-bpp-hop-count-data
                             fn-bpp-hop-countp fn-bpc-shapep fn-bpc-cost
                             ;; Both are in `fn-bpc-vocabulary` and both are
                             ;; DISABLED at the end of
                             ;; `books/bp-primary-cbor`; the length bound is
                             ;; the whole of what is missing.
                             fn-bpc-enc-are-octets fn-bpc-enc-length-bound)
                            (fn-bpc-enc))))))

(local
 (defthm fn-bpn-bundle-age-data-is-block-data
   (implies (fn-bpp-bundle-agep ms)
            (fn-bpb-datap (fn-bpp-bundle-age-data ms)))
   :hints (("Goal"
            :in-theory (e/d (fn-bpb-datap fn-bpp-bundle-age-data
                             fn-bpp-bundle-agep fn-bpc-shapep fn-bpc-cost
                             fn-bpc-enc-are-octets fn-bpc-enc-length-bound)
                            (fn-bpc-enc))))))

; K5.  What `fn-bpn-send` puts on the wire is a bundle: it decodes, and it
; decodes to the bundle that was built.
(defthm fn-bpn-send-bundle-is-a-bundle
  (implies (and (fn-bpn-configp config) (fn-bpp-eidp peer)
                (fn-bpb-datap adu) (fn-bpp-timep sequence)
                (fn-clock-observationp obs))
           (fn-bpb-bundlep (fn-bpn-send-bundle config peer adu sequence obs)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-bpn-send-bundle fn-bpn-send-blocks
                            fn-bpb-bundlep fn-bpb-splitp
                            fn-bpb-block-listp fn-bpb-numbers-distinctp
                            fn-bpb-block-numbers fn-bpb-payload-blockp
                            fn-bpb-blockp fn-bpb-datap
                            fn-bpb-hop-count-block fn-bpb-bundle-age-block
                            fn-bpb-payload-block fn-bpn-configp
                            ;; The creation timestamp is
                            ;; `(if (fn-clock-has-wall obs) (fn-clock-wall
                            ;; obs) 0)` and `fn-bpp-timep` wants it bounded,
                            ;; so the clock's observation recognizer has to
                            ;; be open here for the same reason
                            ;; `fn-bpn-receive`'s guard opens it.  Measured
                            ;; 2026-09-21: closed, the form stops at
                            ;; `Subgoal 12.5`, `(INTEGERP (FN-CLOCK-WALL
                            ;; OBS))`, with `(FN-CLOCK-OBSERVATIONP OBS)`
                            ;; sitting unopened in its own hypotheses.
                            fn-clock-observationp)
                           (fn-bpp-eidp fn-bpp-vchar-listp fn-bpp-vcharp
                            fn-cbor-octet-listp fn-cbor-octetp
                            fn-bpc-enc fn-bpp-hop-count-data
                            fn-bpp-bundle-age-data)))))

; K5 is `fn-bpn-send`'s guard obligation, so the verification deferred at the
; definition happens here.
(verify-guards fn-bpn-send
  :hints (("Goal" :in-theory (disable fn-bpb-encode fn-bpn-send-bundle))))

; The ADU of the bundle `fn-bpn-send` authors is the ADU it was given.  This
; is the conclusion's half of K1 and it is pure record algebra --
; `fn-bpb-payload` is `fn-bpb-block-data` of `fn-bpb-bundle-payload`, and
; `fn-bpn-send-bundle` builds that field with `fn-bpb-payload-block` -- so it
; is proved here, once, with the three definitions open.  K1 keeps them
; CLOSED, because opening `fn-bpn-send-bundle` there would unfold the term
; that `fn-bpb-decode-of-encode` and K5 are both stated about.
(local
 (defthm fn-bpn-payload-of-send-bundle
   (equal (fn-bpb-payload (fn-bpn-send-bundle config peer adu sequence obs))
          adu)
   :hints (("Goal"
            :in-theory (enable fn-bpn-send-bundle fn-bpb-payload
                               fn-bpb-payload-block)))))

; `fn-bpb-decode-of-encode`'s second hypothesis is `(natp limit)`, and the
; limit K1 hands it is the receiver's configured transfer limit.
; `fn-defrecord` generates no per-field type fact, so without this the only
; route to it is opening `fn-bpn-configp` -- which K1 must not do, because
; K5's own hypothesis is that literal.
(local
 (defthm fn-bpn-config-transfer-limit-is-a-natural
   (implies (fn-bpn-configp config)
            (natp (fn-bpn-config-transfer-limit config)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (enable fn-bpn-configp)))))

; K1.  What a peer receives from `fn-bpn-send` carries exactly the ADU that
; was sent.  The subject is the pair of functions the host calls: `bp send`
; calls `fn-bpn-send` (host/native/bp.lisp) and `bp receive` calls
; `fn-bpn-receive`.
;
; The `:cases` is the receiver's TRANSFER LIMIT, and it is the second
; hypothesis of `fn-bpb-decode-of-encode`.  Nothing in the statement bounds
; the authored bundle against the receiver's limit -- a node configured for a
; 16-octet transfer refuses this very bundle, and
; `tests/acl2/bp-node-tests.lisp` has that witness -- so the theorem is true
; only because the acceptance hypothesis rules that branch out, and the split
; is how the prover gets to use it: above the limit
; `fn-bpb-decode-refuses-overlong-input` makes the decode `:limit`, the
; outcome a refusal, and the hypothesis false.
(defthm fn-bpn-receive-of-send-carries-the-adu
  (implies (and (fn-bpn-configp config) (fn-bpn-configp peer-config)
                (fn-bpp-eidp peer) (fn-bpb-datap adu) (fn-bpp-timep sequence)
                (fn-clock-observationp obs) (fn-clock-observationp obs2)
                (fn-bpn-acceptedp
                 (fn-bpn-receive peer-config
                                 (fn-bpn-send config peer adu sequence obs)
                                 obs2)))
           (equal (fn-bpn-received-adu
                   (fn-bpn-receive peer-config
                                   (fn-bpn-send config peer adu sequence obs)
                                   obs2))
                  adu))
  :hints (("Goal"
           :do-not-induct t
           :cases ((fn-cbor-at-mostp
                    (fn-bpb-encode
                     (fn-bpn-send-bundle config peer adu sequence obs))
                    (fn-bpn-config-transfer-limit peer-config)))
           ;; `fn-bpn-configp` is NOT opened: K5's hypothesis is
           ;; `(fn-bpn-configp config)` as a literal, and opening the
           ;; recognizer here would leave the rule unable to fire on the
           ;; very term this proof needs it for.  The one field fact the
           ;; decoder's `(natp limit)` hypothesis wants comes from the
           ;; local type lemma above instead.
           :in-theory (e/d (fn-bpn-receive fn-bpn-send fn-bpn-received-adu)
                           (fn-bpb-decode fn-bpb-encode fn-bpb-payload
                            fn-bpn-send-bundle fn-bpb-bundlep
                            fn-bpn-configp
                            fn-bpp-eidp fn-bpp-vchar-listp fn-bpp-vcharp
                            fn-bpp-previous-nodep fn-bpp-dtn-sspp
                            fn-bpp-eid-node-idp fn-bpp-eid-singletonp
                            fn-bpb-decode-yields-bundle
                            fn-bpp-blockp fn-bpp-flags-conformantp
                            fn-bpp-fragmentp fn-bpp-flag-onp
                            fn-bpn-expiry fn-bpn-hop-exceededp
                            fn-bpn-anchor-of fn-bpb-bundle-hop-count
                            fn-bpb-bundle-age)))))

; K2.  A bundle the clock calls expired is never forwarded, and neither is one
; whose hop count has passed its limit.
(defthm fn-bpn-expired-bundle-is-not-forwarded
  (implies (equal (fn-bpn-expiry bundle obs) :expired)
           (not (fn-bpn-forwardp (fn-bpn-forward-decision bundle obs)))))

(defthm fn-bpn-hop-exceeded-bundle-is-not-forwarded
  (implies (fn-bpn-hop-exceededp bundle)
           (not (fn-bpn-forwardp (fn-bpn-forward-decision bundle obs)))))

; K3.  The hop count fn writes on forwarding is one greater than the one it
; received, with the limit unchanged: the count increases at every hop, which
; is what makes the limit terminate a loop.
(defthm fn-bpn-next-hop-count-increases
  (implies (fn-bpp-hop-countp hop)
           (and (equal (nth 2 (fn-bpn-next-hop-count hop)) (+ 1 (nth 2 hop)))
                (equal (nth 1 (fn-bpn-next-hop-count hop)) (nth 1 hop)))))

; K4.  An accepted outcome is not a refusal and not an uncertain outcome:
; three outcomes, distinct at the boundary and not merely by convention.
(defthm fn-bpn-outcomes-are-distinct
  (and (implies (fn-bpn-acceptedp r)
                (and (not (fn-bpn-refusedp r)) (not (fn-bpn-uncertainp r))))
       (implies (fn-bpn-refusedp r)
                (and (not (fn-bpn-acceptedp r)) (not (fn-bpn-uncertainp r))))
       (implies (fn-bpn-uncertainp r)
                (and (not (fn-bpn-acceptedp r)) (not (fn-bpn-refusedp r))))))

; Every branch of `fn-bpn-receive` returns one of the three constructors, so
; the proof is the case split and nothing else -- once the vocabulary under
; the decoder is closed.  Open, this form's `Time:` line read
; `371.16 seconds (prove: 0.00, other: 371.16)`: no proof search at all,
; just forward chaining and type reasoning over a decoded bundle the
; statement never looks inside (docs/proof-style.md section 9.1).
(defthm fn-bpn-receive-yields-one-of-three
  (or (fn-bpn-acceptedp (fn-bpn-receive config octets obs))
      (fn-bpn-refusedp (fn-bpn-receive config octets obs))
      (fn-bpn-uncertainp (fn-bpn-receive config octets obs)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-bpn-receive fn-bpn-acceptedp fn-bpn-refusedp
                            fn-bpn-uncertainp fn-bpn-accepted fn-bpn-refused
                            fn-bpn-uncertain)
                           (fn-bpb-decode fn-bpp-blockp fn-bpb-bundlep
                            fn-bpp-flags-conformantp fn-bpp-fragmentp
                            fn-bpp-flag-onp fn-bpn-expiry
                            fn-bpn-hop-exceededp fn-bpn-anchor-of
                            fn-bpb-bundle-hop-count fn-bpb-bundle-age
                            fn-bpp-eidp fn-bpp-vchar-listp fn-bpp-vcharp)))))

; -----------------------------------------------------------------------------
; Export theory.

(fn-defrecord-export fn-bpn-vocabulary
  :records (fn-bpn-config)
  :also (fn-bpn-hop-limitp fn-bpn-transfer-limitp fn-bpn-creation-time
         fn-bpn-send-blocks fn-bpn-send-bundle fn-bpn-send
         fn-bpn-accepted fn-bpn-refused fn-bpn-uncertain
         fn-bpn-anchor-of fn-bpn-expiry fn-bpn-hop-exceededp
         fn-bpn-next-hop-count fn-bpn-receive fn-bpn-received-adu
         fn-bpn-forward-decision))
