; Exact debt projections and frontier arithmetic.  The receive and kind-7
; handoff rows below arise from the ACL2 boundary and foundation transition.
; Kind-8/9 runtime N05 teeth remain open until held forwarding is wired.
(in-package "ACL2")
(include-book "../../books/bp-node-debt")
(include-book "../../books/bp-node-receive-boundary")
(include-book "../../books/bp-node-fragment-replacement")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnd-local* (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47)))
(defconst *bpnd-sender* (cons :dtn '(47 47 98 112 45 115 101 110 100 101 114 47)))
(defconst *bpnd-other* (cons :dtn '(47 47 98 112 45 111 116 104 101 114 47)))
(defconst *bpnd-local-config*
  (fn-bpn-config *bpnd-local* 3600000 2 32 1048576))
(defconst *bpnd-sender-config*
  (fn-bpn-config *bpnd-sender* 3600000 2 32 1048576))
(defconst *bpnd-observation* (fn-clock-observation 1000 0 0 nil))
(defconst *bpnd-ingress*
  (list :cl (cons 0 1) 1 *bpnd-sender* '(115 101 110 100 101 114) 0))
(defconst *bpnd-request*
  (fn-bpa-encode
   (fn-bpa-make-request "w" "s" "dtn://bp-sender/" "dtn://bp-local/"
                        "p" "i" "c" "t" '(88 13 10))))
(defconst *bpnd-transit-bundle*
  (fn-bpn-send-bundle *bpnd-sender-config* *bpnd-other*
                      '(1 2 3 4) 7 *bpnd-observation*))
(defconst *bpnd-local-bundle*
  (fn-bpn-send-bundle *bpnd-sender-config* *bpnd-local*
                      *bpnd-request* 8 *bpnd-observation*))

(defun bpnd-durable-receive (st bundle)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((prepared (fn-bpnf-receive-wire-event
                    *bpnd-local-config* (fn-bpb-encode bundle)
                    *bpnd-observation* *bpnd-ingress*))
         (proposal (fn-bpnf-step
                    st (fn-bpnf-receive-wire-event-value prepared)))
         (effect (car (fn-bpnf-answer-effects proposal))))
    (if (and (fn-bpnf-receive-wire-readyp prepared)
             (equal (car effect) :persist))
        (fn-bpnf-answer-state
         (fn-bpnf-step
          (fn-bpnf-answer-state proposal)
          (list :persist-result (fn-bpn-nth 1 effect)
                (fn-bpn-nth 2 effect) :durable)))
      st)))

(defconst *bpnd-s0* (fn-bpnf-initial-state *bpnd-local-config* 8 1048576))
(defconst *bpnd-s1* (bpnd-durable-receive *bpnd-s0* *bpnd-transit-bundle*))
(defconst *bpnd-s2* (bpnd-durable-receive *bpnd-s1* *bpnd-local-bundle*))
(defconst *bpnd-old-held* (second (fn-bpnf-held-list *bpnd-s2*)))
(defconst *bpnd-new-held* (first (fn-bpnf-held-list *bpnd-s2*)))
(defconst *bpnd-new-key*
  (fn-bpnf-held-key (fn-bpnf-held-principal *bpnd-new-held*)
                     (fn-bpnf-held-id *bpnd-new-held*)))
(defconst *bpnd-before-debt* (fn-bpnd-debt *bpnd-s2* *bpnd-local*))

(assert-event
 (and (fn-bpnf-heldp *bpnd-old-held*)
      (fn-bpnf-heldp *bpnd-new-held*)
      (equal (len (fn-bpnf-held-list *bpnd-s2*)) 2)
      (not (fn-bpnf-issued *bpnd-s2*))
      (equal (fn-bpnd-held-debt *bpnd-old-held* *bpnd-local*) 2)
      (equal (fn-bpnd-held-debt *bpnd-new-held* *bpnd-local*) 5)
      (equal *bpnd-before-debt* 7)))

(defconst *bpnd-delivery*
  (fn-bpnf-step *bpnd-s2* (list :deliver *bpnd-new-key* *bpnd-local*)))
(defconst *bpnd-delivery-effect* (car (fn-bpnf-answer-effects *bpnd-delivery*)))
(defconst *bpnd-result*
  (fn-bpnf-step
   (fn-bpnf-answer-state *bpnd-delivery*)
   (list :deliver-result (fn-bpn-nth 1 *bpnd-delivery-effect*)
         (fn-bpn-nth 2 *bpnd-delivery-effect*)
         *bpnd-new-key* :request-accepted '(114 105 100))))
(defconst *bpnd-kind7* (car (fn-bpnf-answer-effects *bpnd-result*)))
(defconst *bpnd-durable*
  (fn-bpnf-step
   (fn-bpnf-answer-state *bpnd-result*)
   (list :persist-result (fn-bpn-nth 1 *bpnd-kind7*)
         (fn-bpn-nth 2 *bpnd-kind7*) :durable)))
(defconst *bpnd-after-state* (fn-bpnf-answer-state *bpnd-durable*))

; The local request's +3 future handoff credit becomes the actual owed
; handoff's +3 on kind 7.  Only its terminal record is paid.
(assert-event
 (and (equal (car *bpnd-delivery-effect*) :deliver)
      (equal (car *bpnd-kind7*) :persist-delivery)
      (equal (fn-bpnf-answer-effects *bpnd-durable*)
             '((:delivery-answer :durable)))
      (equal (fn-bpnd-handoffs-debt (fn-bpnf-handoffs *bpnd-after-state*)) 3)
      (equal (fn-bpnd-debt *bpnd-after-state* *bpnd-local*) 6)
      (equal (fn-bpnd-held-handoff-delta
              *bpnd-new-held*
              (fn-bpnf-find-held *bpnd-new-key*
                                  (fn-bpnf-held-list *bpnd-after-state*))
              (car (fn-bpnf-handoffs *bpnd-after-state*))
              *bpnd-local*)
             -1)))
(must-fail
 (assert-event
  (equal (fn-bpnd-debt *bpnd-after-state* *bpnd-local*) 3)))

; Prospective local deltas for the two not-yet-served forwarding records.
; The actual path must construct these row images in ACL2 before publication.
(defconst *bpnd-attempt-held*
  (update-nth 13 '(:forwarding 1 peer session) *bpnd-old-held*))
(assert-event
 (and (equal (fn-bpnd-held-delta
              *bpnd-old-held* *bpnd-attempt-held* *bpnd-local*) 1)
      (equal (fn-bpnd-held-delta
              *bpnd-attempt-held* *bpnd-old-held* *bpnd-local*) -1)))

(defconst *bpnd-margin* 2)
(defconst *bpnd-f1-used*
  (- *fn-bpnf-received-max-records*
     (+ *bpnd-before-debt* *bpnd-margin* 1)))
(defconst *bpnd-f2-used* (1- *bpnd-f1-used*))
(assert-event
 (and (equal (fn-bpnd-free *bpnd-f1-used* *bpnd-before-debt*
                             *bpnd-margin*) 1)
      (not (fn-bpnd-admitp *bpnd-f1-used* *bpnd-before-debt*
                              *bpnd-margin* 1 :spend))
      (equal (fn-bpnd-free *bpnd-f2-used* *bpnd-before-debt*
                             *bpnd-margin*) 2)
      (fn-bpnd-admitp *bpnd-f2-used* *bpnd-before-debt*
                       *bpnd-margin* 1 :spend)
      (equal (fn-bpnd-free (1+ *bpnd-f2-used*) (1+ *bpnd-before-debt*)
                             *bpnd-margin*) 0)
      (fn-bpnd-admitp (1+ *bpnd-f2-used*) (1+ *bpnd-before-debt*)
                       *bpnd-margin* -1 :pay)
      (equal (fn-bpnd-free (+ 2 *bpnd-f2-used*) *bpnd-before-debt*
                             *bpnd-margin*) 0)))
(must-fail
 (assert-event
  (fn-bpnd-admitp *bpnd-f1-used* *bpnd-before-debt*
                   *bpnd-margin* 1 :spend)))

; A debt-paying record is admitted at the margin frontier while a new
; obligation is refused.  A wholly full namespace has no physical slot even
; for a paying record; recovery/rotation must supply one before settlement.
(defconst *bpnd-frontier-used*
  (- *fn-bpnf-received-max-records*
     (+ *bpnd-before-debt* *bpnd-margin*)))
(assert-event
 (and (equal (fn-bpnd-free *bpnd-frontier-used* *bpnd-before-debt*
                             *bpnd-margin*) 0)
      (fn-bpnd-admitp *bpnd-frontier-used* *bpnd-before-debt*
                       *bpnd-margin* -1 :pay)
      (not (fn-bpnd-admitp *bpnd-frontier-used* *bpnd-before-debt*
                              *bpnd-margin* 2 :spend))
      (not (fn-bpnd-admitp *fn-bpnf-received-max-records*
                              *bpnd-before-debt* *bpnd-margin* -1 :pay))))
(must-fail
 (assert-event
  (fn-bpnd-admitp *bpnd-frontier-used* *bpnd-before-debt*
                   *bpnd-margin* 0 :pay)))

; A complete fragment family can increase debt.  Its two admitted fragment
; rows each cost two; the resulting local whole request costs five.  This
; kind-18 replacement must therefore spend one free debt credit in addition
; to its own physical record, even though it reduces the held-row count.
(defconst *bpnd-request-size* (len *bpnd-request*))
(defconst *bpnd-first-bytes* (take 20 *bpnd-request*))
(defconst *bpnd-last-bytes* (nthcdr 20 *bpnd-request*))
(defconst *bpnd-fragment-primary* (fn-bpb-bundle-primary *bpnd-local-bundle*))
(defconst *bpnd-fragment-zero*
  (fn-bpb-make-bundle
   (fn-bpf-fragment-block *bpnd-fragment-primary* 0 *bpnd-request-size*)
   (fn-bpb-bundle-blocks *bpnd-local-bundle*)
   (fn-bpb-payload-block 2 *bpnd-first-bytes*)))
(defconst *bpnd-fragment-tail*
  (fn-bpb-make-bundle
   (fn-bpf-fragment-block *bpnd-fragment-primary* 20 *bpnd-request-size*)
   (fn-bpb-bundle-blocks *bpnd-local-bundle*)
   (fn-bpb-payload-block 2 *bpnd-last-bytes*)))
(defconst *bpnd-fragment-held-zero*
  (fn-bpnf-held (fn-bpnf-ingress-principal *bpnd-ingress*)
                 (fn-bpb-bundle-id *bpnd-fragment-zero*) 0
                 *bpnd-ingress* nil nil *bpnd-fragment-zero*
                 (fn-bpb-encode *bpnd-fragment-zero*)
                 (fn-bpnf-received-anchor *bpnd-fragment-zero*
                                            *bpnd-observation*)
                 nil nil '(:dispatch-pending) nil nil 0))
(defconst *bpnd-fragment-held-tail*
  (fn-bpnf-held (fn-bpnf-ingress-principal *bpnd-ingress*)
                 (fn-bpb-bundle-id *bpnd-fragment-tail*) 1
                 *bpnd-ingress* nil nil *bpnd-fragment-tail*
                 (fn-bpb-encode *bpnd-fragment-tail*)
                 (fn-bpnf-received-anchor *bpnd-fragment-tail*
                                            *bpnd-observation*)
                 nil nil '(:dispatch-pending) nil nil 1))
(defconst *bpnd-frag-s1*
  (bpnd-durable-receive *bpnd-s0* *bpnd-fragment-zero*))
(defconst *bpnd-frag-s2*
  (bpnd-durable-receive *bpnd-frag-s1* *bpnd-fragment-tail*))
(defconst *bpnd-family-plan*
  (fn-bpnf-family-plan *bpnd-frag-s2* *bpnd-fragment-held-tail*))
(defconst *bpnd-family-record*
  (fn-bpnf-family-record-at 0 2 1 2 (fn-bpn-nth 2 *bpnd-family-plan*)
                             *bpnd-observation*))
(defconst *bpnd-family-applied*
  (fn-bpnf-family-apply-at *bpnd-frag-s2* *bpnd-family-record* 2))
(assert-event
 (and (< 20 *bpnd-request-size*)
      (fn-bpb-bundlep *bpnd-fragment-zero*)
      (fn-bpb-bundlep *bpnd-fragment-tail*)
      (fn-bpnf-heldp *bpnd-fragment-held-zero*)
      (fn-bpnf-heldp *bpnd-fragment-held-tail*)
      (equal (fn-bpnf-held-list *bpnd-frag-s2*)
             (list *bpnd-fragment-held-tail* *bpnd-fragment-held-zero*))
      (equal (car *bpnd-family-plan*) :ready)
      (equal (car *bpnd-family-applied*) :ready)
      (equal (fn-bpnd-held-debt
              (fn-bpn-nth 2 *bpnd-family-applied*) *bpnd-local*) 5)
      (equal (fn-bpnd-held-list-debt
              (list *bpnd-fragment-held-zero* *bpnd-fragment-held-tail*)
              *bpnd-local*) 4)
      (equal (fn-bpnd-family-delta
              (fn-bpn-nth 3 *bpnd-family-applied*)
              (fn-bpn-nth 2 *bpnd-family-applied*)
              *bpnd-local*) 1)))
(must-fail
 (assert-event
  (equal (fn-bpnd-family-delta
          (fn-bpn-nth 3 *bpnd-family-applied*)
          (fn-bpn-nth 2 *bpnd-family-applied*)
          *bpnd-local*)
         -1)))
