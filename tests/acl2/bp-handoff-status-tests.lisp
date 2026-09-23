(in-package "ACL2")
(include-book "../../books/bp-handoff-status")
(include-book "bp-receipt-tests")
(include-book "../../books/bp-fnbs-delivery-replay")
(include-book "std/testing/must-fail" :dir :system)

; A committed FNRJ receipt for the same request that the kind-5 held row
; carries.  Its receipt ID is the kind-7 handoff ID, not a host-derived name.
(defconst *bphs-sender* (cons :dtn (nthcdr 4 (fn-record-string-octets
                                              "dtn://sender.lab/"))))
(defconst *bphs-receiver* (cons :dtn (nthcdr 4 (fn-record-string-octets
                                                "dtn://fn.lab/inbox"))))
(defconst *bphs-receiver-node* (cons :dtn (nthcdr 4 (fn-record-string-octets
                                                     "dtn://fn.lab/"))))
(defconst *bphs-observation* (fn-clock-observation 1000 0 0 nil))
(defconst *bphs-sender-config*
  (fn-bpn-config *bphs-sender* 3600000 2 32 1048576))
(defconst *bphs-receiver-config*
  (fn-bpn-config *bphs-receiver-node* 3600000 2 32 1048576))
(defconst *bphs-request-adu* (fn-bpa-encode *bpr-request*))
(defconst *bphs-request-bundle*
  (fn-bpn-send-bundle *bphs-sender-config* *bphs-receiver*
                      *bphs-request-adu* 7 *bphs-observation*))
(defconst *bphs-ingress*
  (list :cl (cons 1 1) 1 *bphs-sender*
        (fn-record-string-octets "dtn://sender.lab/") 0))
(defconst *bphs-held*
  (fn-bpnf-held (fn-bpnf-ingress-principal *bphs-ingress*)
                 (fn-bpb-bundle-id *bphs-request-bundle*) 0 *bphs-ingress*
                 nil nil *bphs-request-bundle*
                 (fn-bpb-encode *bphs-request-bundle*)
                 nil nil nil '(:dispatch-pending) nil nil 0))
(defconst *bphs-rid* (fn-record-string-octets "receipt-1"))
(defconst *bphs-stored* (fn-bpnf-stored-record 3 0 *bphs-held*))
(defconst *bphs-delivered*
  (fn-bpah-delivery-record
   3 1 0 (fn-bpp-primary-identity
          (fn-bpb-bundle-primary *bphs-request-bundle*))
   :request-accepted *bphs-rid*))
(defun bphs-rows ()
  (list (list (fn-bpnf-stored-record-name 3 0)
              (fn-bpnf-stored-record-frame *bphs-stored*))
        (list (fn-bpnf-stored-record-name 3 1)
              (fn-bpah-delivery-frame *bphs-delivered*))))
(make-event `(defconst *bphs-replay* ',(fn-bpah-replay-rows (bphs-rows)
                                                       4 1048576)))
(defconst *bphs-handoff* (car (nth 2 *bphs-replay*)))
(defconst *bphs-receipt-adu* (fn-bpr-receipt-adu *bpr-committed* *bpr-request*))
(defconst *bphs-route*
  (list :route (fn-record-string-octets "127.0.0.1") 4556
        (fn-record-string-octets "dtn://fn.lab/inbox") 4 1024 1048576))

(defun bphs-reply-job (adu peer)
  (declare (xargs :guard (and (fn-bpb-datap adu) (fn-bpp-eidp peer))
                  :verify-guards nil))
  (let* ((bundle (fn-bpn-send-bundle *bphs-receiver-config* peer adu
                                     8 *bphs-observation*)))
    (fn-bpn-make-job
     (fn-bpah-outbox-work-id *bphs-rid* 0)
     (fn-record-string-octets "return") 0 8
     (fn-bpn-anchor-of bundle *bphs-observation*) peer *bphs-route*
     bundle (fn-bpb-encode bundle) :queued 0)))

(defun bphs-state-with-job (job)
  (declare (xargs :guard t))
  (fn-bpnf-state
   (fn-bpn-make-machine-state *bphs-receiver-config*
                              (if job (list job) nil) nil nil nil
                              (if job 1 0) 4 1048576)
   (nth 1 *bphs-replay*) nil (nth 2 *bphs-replay*) nil nil nil 4 0))

(defconst *bphs-job* (bphs-reply-job *bphs-receipt-adu* *bphs-sender*))
(defconst *bphs-live* (bphs-state-with-job *bphs-job*))
(defconst *bphs-fnrj* (fn-bpaj-make-state *bpr-committed* nil nil nil))

(assert-event (equal (car *bphs-replay*) :ready))
(assert-event (fn-bpnf-handoffp *bphs-handoff*))
(assert-event (fn-bpn-jobp *bphs-job*))
(assert-event
 (equal (fn-bpah-handoff-effective-status
         *bphs-live* *bphs-handoff* *bphs-receipt-adu* *bphs-sender*)
        '(:handed-off 8)))
(assert-event
 (equal *bphs-receipt-adu*
        (fn-bpr-receipt-adu (fn-bpaj-receiver *bphs-fnrj*) *bpr-request*)))

; Missing job, same-key contradictory ADU, and same-key wrong peer remain owed.
(assert-event
 (equal (fn-bpah-handoff-effective-status
         (bphs-state-with-job nil) *bphs-handoff*
         *bphs-receipt-adu* *bphs-sender*) :owed))
(assert-event
 (equal (fn-bpah-handoff-effective-status
         (bphs-state-with-job (bphs-reply-job *bphs-request-adu* *bphs-sender*))
         *bphs-handoff* *bphs-receipt-adu* *bphs-sender*) :owed))
(assert-event
 (equal (fn-bpah-handoff-effective-status
         (bphs-state-with-job (bphs-reply-job *bphs-receipt-adu* *bphs-receiver*))
         *bphs-handoff* *bphs-receipt-adu* *bphs-sender*) :owed))
(must-fail
 (assert-event
  (equal (fn-bpah-handoff-effective-status
          (bphs-state-with-job nil) *bphs-handoff*
          *bphs-receipt-adu* *bphs-sender*)
         '(:handed-off 8))))

; FNBS byte replay reconstructs the same kind-7 handoff.  An independently
; replayed outbound :queued record reconstructs the same carrier, so the
; effective status after recovery is the live one, without a mutable flag.
(defconst *bphs-base-recovered*
  (fn-bpn-answer-state
   (fn-bpn-step (fn-bpn-initial-machine-state *bphs-receiver-config*
                                             4 1048576)
                (list :restart (list (list :queued 0 *bphs-job*)) :ready))))
(defconst *bphs-recovered*
  (fn-bpnf-state *bphs-base-recovered* (nth 1 *bphs-replay*) nil
                 (nth 2 *bphs-replay*) nil nil nil 4 0))
(assert-event (fn-bpn-machine-statep *bphs-base-recovered*))
(assert-event
 (equal (fn-bpah-handoff-effective-status
         *bphs-recovered* *bphs-handoff* *bphs-receipt-adu* *bphs-sender*)
        '(:handed-off 8)))

; This is the exact API the native outbox caller uses.  FNRJ replay supplies
; the ADU; the returned sequence comes from the durable base job.
(defconst *bphs-view* (fn-bpah-outbox-view-for *bphs-live* *bphs-handoff*))
(assert-event (equal (fn-bpn-nth 0 *bphs-view*) :outbox))
(assert-event
 (equal (fn-bpah-outbox-effective-status
         *bphs-live* *bphs-view* *bphs-receipt-adu* *bphs-sender*)
        '(:handed-off 8)))
(assert-event
 (equal (fn-bpah-outbox-effective-status
         (bphs-state-with-job nil) *bphs-view*
         *bphs-receipt-adu* *bphs-sender*) :owed))
(must-fail
 (assert-event
  (equal (fn-bpah-outbox-effective-status
          *bphs-live* *bphs-view* *bphs-request-adu* *bphs-sender*)
         '(:handed-off 8))))
(must-fail
 (assert-event
  (equal (fn-bpah-outbox-effective-status
          *bphs-live* *bphs-view* *bphs-receipt-adu* *bphs-receiver*)
         '(:handed-off 8))))

; A second accepted carrier may return the same FNRJ RID, but its distinct
; arrival is a distinct handoff trigger and therefore a distinct outbound key.
(defconst *bphs-second-bundle*
  (fn-bpn-send-bundle *bphs-sender-config* *bphs-receiver*
                      *bphs-request-adu* 9 *bphs-observation*))
(defconst *bphs-second-held*
  (fn-bpnf-held (fn-bpnf-ingress-principal *bphs-ingress*)
                 (fn-bpb-bundle-id *bphs-second-bundle*) 1 *bphs-ingress*
                 nil nil *bphs-second-bundle*
                 (fn-bpb-encode *bphs-second-bundle*)
                 nil nil nil '(:dispatch-pending) nil nil 0))
(defconst *bphs-second-delivery*
  (fn-bpah-delivery-record
   3 2 1 (fn-bpp-primary-identity
          (fn-bpb-bundle-primary *bphs-second-bundle*))
   :request-duplicate *bphs-rid*))
(defconst *bphs-second-apply*
  (mv-let (ok held handoff)
    (fn-bpah-apply-delivery *bphs-second-delivery*
                            (list *bphs-second-held*))
    (list ok held handoff)))
(defconst *bphs-second-handoff* (nth 2 *bphs-second-apply*))
(defconst *bphs-two-carriers*
  (fn-bpnf-state
   (fn-bpnf-base *bphs-live*)
   (append (nth 1 *bphs-replay*) (nth 1 *bphs-second-apply*))
   nil (list *bphs-handoff* *bphs-second-handoff*)
   nil nil nil 4 0))
(defconst *bphs-second-view*
  (fn-bpah-outbox-view-for *bphs-two-carriers* *bphs-second-handoff*))
(assert-event (car *bphs-second-apply*))
(assert-event (fn-bpnf-handoffp *bphs-second-handoff*))
(assert-event (equal (fn-bpn-nth 0 *bphs-second-view*) :outbox))
(assert-event (not (equal (fn-bpn-nth 5 *bphs-second-view*)
                          (fn-bpn-nth 5 *bphs-view*))))
(assert-event
 (equal (fn-bpah-outbox-effective-status
         *bphs-two-carriers* *bphs-second-view*
         *bphs-receipt-adu* *bphs-sender*) :owed))
