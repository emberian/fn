(in-package "ACL2")
(include-book "../../books/bp-fnbs-delivery-publication")
(include-book "../../books/codec-attach")
(include-book "bp-fnbs-delivery-replay-tests")
(include-book "must-fail-checked")

(defconst *bpahp-record* (fn-bpn-nth 4 (fn-bpnf-issued *bpahr-live-result*)))
(make-event
 (list 'defconst '*bpahp-operation*
       (list 'quote
             (fn-bpah-publication-authorize
              *bpahr-live-result* 1 2 *bpahp-record* t t))))
(assert-event (fn-bpah-publication-operationp *bpahp-operation*))
(assert-event (equal (fn-bpah-publication-name *bpahp-operation*)
                     (fn-bpnf-stored-record-name 1 2)))
(assert-event (equal (fn-bpah-delivery-unframe
                      (fn-bpah-publication-frame *bpahp-operation*))
                     *bpahp-record*))
(assert-event (equal (car (fn-bpah-publication-authorize
                           *bpahr-live-result* 1 3 *bpahp-record* t t))
                     :fault))
(assert-event (equal (car (fn-bpah-publication-authorize
                           *bpahr-live-result* 1 2 *bpahp-record* t nil))
                     :fault))
(must-fail-checked
 (assert-event
  (fn-bpah-publication-operationp
   (fn-bpah-publication-authorize
    *bpahr-live-result* 1 3 *bpahp-record* t t))))

; KEYSTONE teeth (PRF-1013,
; fn-bpah-publication-authorize-admits-exactly-the-issued-pending-delivery):
; the positive witness above with its complete antecedent by name, then every
; part of the conclusion; then a wrong operation id and a withheld lock (the
; antecedent affirmed otherwise) answer the authority fault exactly.
(assert-event
 (let ((issued (fn-bpnf-issued *bpahr-live-result*)))
   (and (fn-bpnf-operationp issued)
        (fn-bpnf-operation-matchp issued 1 2)
        (equal (fn-bpn-nth 3 issued) :deliver)
        (equal (fn-bpn-nth 4 issued) *bpahp-record*)
        (equal (fn-bpn-nth 5 issued) :pending)
        (equal (fn-bpnf-epoch *bpahr-live-result*) 1)
        (equal (fn-bpnf-next-op *bpahr-live-result*) 3)
        (fn-bpah-delivery-recordp *bpahp-record*)
        (equal (fn-bpn-nth 1 *bpahp-record*) 1)
        (equal (fn-bpn-nth 2 *bpahp-record*) 2)
        (not (equal (fn-bpah-delivery-frame *bpahp-record*) :bad))
        (fn-bpah-publication-operationp *bpahp-operation*)
        (equal (nth 1 *bpahp-operation*) 1)
        (equal (nth 2 *bpahp-operation*) 2)
        (equal (nth 3 *bpahp-operation*) *bpahp-record*)
        (equal (fn-bpah-publication-name *bpahp-operation*)
               (fn-bpnf-stored-record-name 1 2))
        (equal (fn-bpah-publication-frame *bpahp-operation*)
               (fn-bpah-delivery-frame *bpahp-record*))
        (equal (nth 6 *bpahp-operation*) (fn-jpub-initial t)))))
(assert-event
 (and (not (fn-bpnf-operation-matchp (fn-bpnf-issued *bpahr-live-result*) 1 3))
      (equal (fn-bpah-publication-authorize
              *bpahr-live-result* 1 3 *bpahp-record* t t)
             '(:fault :delivery-authority))))
(assert-event
 (equal (fn-bpah-publication-authorize
         *bpahr-live-result* 1 2 *bpahp-record* nil t)
        '(:fault :delivery-authority)))
