; Witnesses and teeth for fn as a BPv7 node.
;
; Order: guard-world audit, the send/receive scenario, the three outcomes,
; then one concrete violating value per hypothesis of each keystone.

(in-package "ACL2")

(include-book "../../books/bp-node")

(local (in-theory (enable fn-bpn-vocabulary fn-bpb-vocabulary
                          fn-bpb-invariants-vocabulary
                          fn-cbor-record-vocabulary fn-cbor-codec-vocabulary)))

; -----------------------------------------------------------------------------
; Guard-world audit.  `fn-bpn-receive` takes a peer's octets, so its guard
; says only that they are octets and that the configuration is one; nothing
; about the bundle they are about to become.

(assert-event (equal (symbol-class 'fn-bpn-receive (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-bpn-send (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-bpn-forward-decision (w state))
                     :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-bpn-received-adu (w state))
                     :common-lisp-compliant))
(assert-event (equal (guard 'fn-bpn-received-adu nil (w state)) *t*))

; -----------------------------------------------------------------------------
; Two nodes and a clock with no wall reading: the disconnected case, where the
; creation timestamp is the zero of RFC 9171 section 4.2.6 and the Bundle Age
; block is what makes the lifetime decidable at all.

(defconst *bpn-a* (cons :dtn '(47 47 102 110 45 97 47)))     ; dtn://fn-a/
(defconst *bpn-b* (cons :dtn '(47 47 102 110 45 98 47)))     ; dtn://fn-b/

(defconst *bpn-config-a* (fn-bpn-config *bpn-a* 3600000 2 32 1048576))
(defconst *bpn-config-b* (fn-bpn-config *bpn-b* 3600000 2 32 1048576))

(assert-event (fn-bpn-configp *bpn-config-a*))
(assert-event (fn-bpn-configp *bpn-config-b*))

(defconst *bpn-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bpn-obs-later* (fn-clock-observation 4000 0 0 nil))

(assert-event (fn-clock-observationp *bpn-obs*))
(assert-event (not (fn-clock-has-wall *bpn-obs*)))

(defconst *bpn-adu* '(104 101 108 108 111))                  ; "hello"

(defconst *bpn-wire* (fn-bpn-send *bpn-config-a* *bpn-b* *bpn-adu* 7 *bpn-obs*))

; The wire image is a bundle, and it is strictly larger than the ADU it
; carries: a sender that forwarded the ADU unwrapped would fail here.
(assert-event (fn-cbor-octet-listp *bpn-wire*))
(assert-event (equal (car *bpn-wire*) 159))
(assert-event (< (len *bpn-adu*) (len *bpn-wire*)))

(defconst *bpn-received* (fn-bpn-receive *bpn-config-b* *bpn-wire* *bpn-obs-later*))

(assert-event (fn-bpn-acceptedp *bpn-received*))
(assert-event (equal (fn-bpn-received-adu *bpn-received*) *bpn-adu*))

; The creation timestamp is the zero of section 4.2.6 because this node has no
; wall clock, and the source is this node's ID -- not the peer's, and not
; dtn:none.
(assert-event (equal (fn-bpn-creation-time *bpn-obs*) 0))
(assert-event
 (equal (fn-bpp-source (fn-bpb-bundle-primary (fn-bpn-outcome-bundle *bpn-received*)))
        *bpn-a*))
(assert-event
 (equal (fn-bpp-destination
         (fn-bpb-bundle-primary (fn-bpn-outcome-bundle *bpn-received*)))
        *bpn-b*))
(assert-event
 (equal (fn-bpb-bundle-hop-count (fn-bpn-outcome-bundle *bpn-received*))
        (fn-bpp-make-hop-count 32 0)))

; And it may be forwarded.
(assert-event (fn-bpn-forwardp
               (fn-bpn-forward-decision (fn-bpn-outcome-bundle *bpn-received*)
                                        *bpn-obs-later*)))

; -----------------------------------------------------------------------------
; Teeth: one concrete violating value per hypothesis.

; A bundle whose accumulated age already exceeds its lifetime.  Hypothesis of
; K2: without `(equal (fn-bpn-expiry bundle obs) :expired)` the same bundle is
; forwarded, which the witness above shows.
(defconst *bpn-old*
  (fn-bpb-make-bundle
   (fn-bpp-make-block 0 2 *bpn-b* *bpn-a* *bpn-a* 0 1 1000 nil nil)
   (list (fn-bpb-bundle-age-block 3 0 2 5000))
   (fn-bpb-payload-block 2 *bpn-adu*)))

(assert-event (fn-bpb-bundlep *bpn-old*))
(assert-event (equal (fn-bpn-expiry *bpn-old* *bpn-obs-later*) :expired))
(assert-event (not (fn-bpn-forwardp
                    (fn-bpn-forward-decision *bpn-old* *bpn-obs-later*))))
(assert-event (equal (fn-bpn-outcome-reason
                      (fn-bpn-receive *bpn-config-b*
                                      (fn-bpb-encode *bpn-old*) *bpn-obs-later*))
                     :lifetime-expired))
(assert-event (fn-bpn-refusedp
               (fn-bpn-receive *bpn-config-b* (fn-bpb-encode *bpn-old*)
                               *bpn-obs-later*)))

; A bundle whose hop count has passed its limit.  Hypothesis of the second
; half of K2.
(defconst *bpn-looped*
  (fn-bpb-make-bundle
   (fn-bpp-make-block 0 2 *bpn-b* *bpn-a* *bpn-a* 0 2 3600000 nil nil)
   (list (fn-bpb-hop-count-block 2 0 2 (fn-bpp-make-hop-count 4 5))
         (fn-bpb-bundle-age-block 3 0 2 0))
   (fn-bpb-payload-block 2 *bpn-adu*)))

(assert-event (fn-bpb-bundlep *bpn-looped*))
(assert-event (fn-bpn-hop-exceededp *bpn-looped*))
(assert-event (not (fn-bpn-forwardp
                    (fn-bpn-forward-decision *bpn-looped* *bpn-obs-later*))))
(assert-event (equal (fn-bpn-outcome-reason
                      (fn-bpn-receive *bpn-config-b*
                                      (fn-bpb-encode *bpn-looped*) *bpn-obs-later*))
                     :hop-limit-exceeded))

; The same bundle with the count one below its limit is forwarded, so the
; refusal above is the hop count and not the rest of the bundle.
(defconst *bpn-near-limit*
  (fn-bpb-make-bundle
   (fn-bpp-make-block 0 2 *bpn-b* *bpn-a* *bpn-a* 0 2 3600000 nil nil)
   (list (fn-bpb-hop-count-block 2 0 2 (fn-bpp-make-hop-count 4 4))
         (fn-bpb-bundle-age-block 3 0 2 0))
   (fn-bpb-payload-block 2 *bpn-adu*)))

(assert-event (not (fn-bpn-hop-exceededp *bpn-near-limit*)))
(assert-event (fn-bpn-forwardp
               (fn-bpn-forward-decision *bpn-near-limit* *bpn-obs-later*)))

; The hop count this node would write next is one greater, and it is the one
; that crosses the limit.
(assert-event (equal (fn-bpn-next-hop-count (fn-bpp-make-hop-count 4 4))
                     (fn-bpp-make-hop-count 4 5)))
(assert-event (fn-bpp-hop-limit-exceededp
               (fn-bpn-next-hop-count (fn-bpp-make-hop-count 4 4))))

; Uncertain, and distinct from both: no Bundle Age block and no wall clock
; leaves the lifetime question undecided.  The bundle is neither accepted nor
; refused, which is the whole point of D13.
(defconst *bpn-undecidable*
  (fn-bpb-make-bundle
   (fn-bpp-make-block 0 2 *bpn-b* *bpn-a* *bpn-a* 0 3 3600000 nil nil)
   nil
   (fn-bpb-payload-block 2 *bpn-adu*)))

(assert-event (equal (fn-bpn-expiry *bpn-undecidable* *bpn-obs-later*) :uncertain))
(defconst *bpn-undecided*
  (fn-bpn-receive *bpn-config-b* (fn-bpb-encode *bpn-undecidable*) *bpn-obs-later*))
(assert-event (fn-bpn-uncertainp *bpn-undecided*))
(assert-event (not (fn-bpn-acceptedp *bpn-undecided*)))
(assert-event (not (fn-bpn-refusedp *bpn-undecided*)))
(assert-event (equal (fn-bpn-outcome-reason *bpn-undecided*) :lifetime-uncertain))
(assert-event (not (fn-bpn-forwardp
                    (fn-bpn-forward-decision *bpn-undecidable* *bpn-obs-later*))))

; The transfer limit is the configuration's, and it refuses before the first
; octet is examined: the same octets accepted above are refused by a node
; configured for a smaller transfer.
(defconst *bpn-config-tiny* (fn-bpn-config *bpn-b* 3600000 2 32 16))

(assert-event (fn-bpn-configp *bpn-config-tiny*))
(assert-event (equal (fn-bpn-outcome-reason
                      (fn-bpn-receive *bpn-config-tiny* *bpn-wire* *bpn-obs-later*))
                     :limit))

; Octets that are not a bundle at all.
(assert-event (fn-bpn-refusedp
               (fn-bpn-receive *bpn-config-b* '(1 2 3) *bpn-obs-later*)))

; One flipped octet in the payload of the wire image: the payload block's CRC
; no longer matches what section 4.2.2 prescribes, and the node refuses.
(defconst *bpn-corrupt*
  (append (fn-bpb-front *bpn-wire*)
          (list (mod (+ 1 (fn-bpb-final *bpn-wire*)) 256))))

(assert-event (not (equal *bpn-corrupt* *bpn-wire*)))
(assert-event (fn-bpn-refusedp
               (fn-bpn-receive *bpn-config-b* *bpn-corrupt* *bpn-obs-later*)))
(assert-event (null (fn-bpn-received-adu
                     (fn-bpn-receive *bpn-config-b* *bpn-corrupt* *bpn-obs-later*))))
