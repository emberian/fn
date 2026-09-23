; Actual kind-5 FNBS frame and issued-held reconstruction witnesses.
(in-package "ACL2")
(include-book "../../books/bp-fnbs-codec")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnfc-local* (cons :dtn '(47 47 102 110 45 97 47)))
(defconst *bpnfc-peer* (cons :dtn '(47 47 102 110 45 98 47)))
(defconst *bpnfc-config* (fn-bpn-config *bpnfc-local* 3600000 2 32 1048576))
(defconst *bpnfc-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bpnfc-bundle*
  (fn-bpn-send-bundle *bpnfc-config* *bpnfc-peer* '(1 2 3 4) 7 *bpnfc-obs*))
(defconst *bpnfc-wire* (fn-bpb-encode *bpnfc-bundle*))
(defconst *bpnfc-ingress* (list :cl (cons 2 7) 3 *bpnfc-peer* '(112) 5))
(defconst *bpnfc-base* (fn-bpn-initial-machine-state *bpnfc-config* 4 1048576))
(defconst *bpnfc-s0* (fn-bpnf-state *bpnfc-base* nil nil nil nil nil nil 9 0))
(defconst *bpnfc-proposal*
  (fn-bpnf-step *bpnfc-s0*
                 (list :receive-bundle *bpnfc-bundle* *bpnfc-wire*
                       *bpnfc-ingress*)))
(defconst *bpnfc-effect* (car (fn-bpnf-answer-effects *bpnfc-proposal*)))
(defconst *bpnfc-record*
  (fn-bpnf-stored-record (nth 1 *bpnfc-effect*)
                           (nth 2 *bpnfc-effect*) (nth 3 *bpnfc-effect*)))

(assert-event (equal (car *bpnfc-effect*) :persist))
(assert-event (equal (nth 1 *bpnfc-effect*) 9))
(assert-event (equal (nth 2 *bpnfc-effect*) 0))
(assert-event (fn-bpnf-stored-recordp *bpnfc-record*))
(assert-event (not (equal (fn-bpnf-stored-record-frame *bpnfc-record*) :bad)))
(assert-event
 (equal (fn-bpnf-stored-record-unframe
         (fn-bpnf-stored-record-frame *bpnfc-record*))
        *bpnfc-record*))
(assert-event
 (equal (nth 3 (fn-bpnf-stored-record-unframe
                (fn-bpnf-stored-record-frame *bpnfc-record*)))
        (nth 4 (fn-bpnf-issued (fn-bpnf-answer-state *bpnfc-proposal*)))))

; A new receive event retains its observation in a versioned kind-5 row.
; The older four-field logical event above remains the old canonical frame.
(defconst *bpnfc-anchored-proposal*
  (fn-bpnf-step *bpnfc-s0*
                 (list :receive-bundle *bpnfc-bundle* *bpnfc-wire*
                       *bpnfc-ingress* *bpnfc-obs*)))
(defconst *bpnfc-anchored-effect*
  (car (fn-bpnf-answer-effects *bpnfc-anchored-proposal*)))
(defconst *bpnfc-anchored-record*
  (fn-bpnf-stored-record
   (nth 1 *bpnfc-anchored-effect*)
   (nth 2 *bpnfc-anchored-effect*)
   (nth 3 *bpnfc-anchored-effect*)))
(assert-event (fn-bpnf-stored-recordp *bpnfc-anchored-record*))
(assert-event
 (equal (nth 9 (nth 3 *bpnfc-anchored-record*))
        (fn-bpnf-received-anchor *bpnfc-bundle* *bpnfc-obs*)))
(assert-event
 (equal (fn-bpnf-stored-record-unframe
         (fn-bpnf-stored-record-frame *bpnfc-anchored-record*))
        *bpnfc-anchored-record*))
(assert-event
 (not (equal (fn-bpnf-stored-record-frame *bpnfc-anchored-record*)
             (fn-bpnf-stored-record-frame *bpnfc-record*))))
(assert-event
 (equal (fn-bpnf-stored-record-frame
         (fn-bpnf-stored-record 9 2
          (fn-bpnf-frame-held-with-anchor
           *bpnfc-ingress* 0 *bpnfc-bundle* *bpnfc-wire*
           '(:observed-age -1 1))))
        :bad))

; Nil is the unauthenticated partition.  A present text principal with
; different bytes cannot collapse into it during decode.
(defconst *bpnfc-anon-ingress*
  (list :cl (cons 2 8) 4 *bpnfc-peer* nil 5))
(defconst *bpnfc-anon-held*
  (fn-bpnf-frame-held *bpnfc-anon-ingress* 0 *bpnfc-bundle* *bpnfc-wire*))
(defconst *bpnfc-anon-record*
  (fn-bpnf-stored-record 9 1 *bpnfc-anon-held*))
(assert-event (fn-bpnf-stored-recordp *bpnfc-anon-record*))
(assert-event
 (equal (fn-bpnf-stored-record-unframe
         (fn-bpnf-stored-record-frame *bpnfc-anon-record*))
        *bpnfc-anon-record*))
(assert-event
 (not (equal (fn-bpnf-stored-record-frame *bpnfc-anon-record*)
             (fn-bpnf-stored-record-frame *bpnfc-record*))))

; Damaged bytes and an inapplicable held row are refused by the codec.
(assert-event (null (fn-bpnf-stored-record-unframe '(1 2 3))))
(assert-event
 (equal (fn-bpnf-stored-record-frame
         (fn-bpnf-stored-record 9 2
           (fn-bpnf-frame-held *bpnfc-ingress* 1 *bpnfc-bundle* '(1 2 3))))
        :bad))
(must-fail
 (assert-event
  (equal (fn-bpnf-stored-record-unframe '(1 2 3))
         *bpnfc-record*)))
