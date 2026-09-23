(in-package "ACL2")
(include-book "../../books/bp-fnbs-delivery-publication")
(include-book "../../books/codec-attach")
(include-book "bp-fnbs-delivery-replay-tests")
(include-book "std/testing/must-fail" :dir :system)

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
(must-fail
 (assert-event
  (fn-bpah-publication-operationp
   (fn-bpah-publication-authorize
    *bpahr-live-result* 1 3 *bpahp-record* t t))))
