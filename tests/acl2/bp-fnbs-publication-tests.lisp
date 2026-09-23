; Exact A1 pending echo authorizes one FNBS immutable publication.
(in-package "ACL2")
(include-book "../../books/bp-fnbs-publication")
(include-book "bp-fnbs-codec-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun bpnfp-issued-state ()
  (fn-bpnf-answer-state *bpnfc-proposal*))
(defun bpnfp-authorized ()
  (fn-bpnf-publication-authorize
   (bpnfp-issued-state) 9 0 (nth 3 *bpnfc-effect*) t t))

(assert-event (fn-bpnf-publication-operationp (bpnfp-authorized)))
(assert-event
 (equal (fn-bpnf-publication-operation-name (bpnfp-authorized))
        (fn-bpnf-stored-record-name 9 0)))
(assert-event
 (equal (fn-bpnf-publication-operation-frame (bpnfp-authorized))
        (fn-bpnf-stored-record-frame *bpnfc-record*)))
(assert-event
 (equal (fn-bpnf-publication-operation-publisher (bpnfp-authorized))
        (fn-jpub-initial t)))

(assert-event
 (equal (car (fn-bpnf-publication-authorize
              (bpnfp-issued-state) 9 1 (nth 3 *bpnfc-effect*) t t))
        :fault))
(assert-event
 (equal (car (fn-bpnf-publication-authorize
              (bpnfp-issued-state) 8 0 (nth 3 *bpnfc-effect*) t t))
        :fault))
(assert-event
 (equal (car (fn-bpnf-publication-authorize
              (bpnfp-issued-state) 9 0 *bpnfc-anon-held* t t))
        :fault))
(assert-event
 (equal (car (fn-bpnf-publication-authorize
              (bpnfp-issued-state) 9 0 (nth 3 *bpnfc-effect*) nil t))
        :fault))
(assert-event
 (equal (car (fn-bpnf-publication-authorize
              (bpnfp-issued-state) 9 0 (nth 3 *bpnfc-effect*) t nil))
        :fault))
(assert-event
 (equal (car (fn-bpnf-publication-authorize
              (fn-bpnf-answer-state
               (fn-bpnf-step (bpnfp-issued-state)
                             '(:persist-result 9 0 :uncertain)))
              9 0 (nth 3 *bpnfc-effect*) t t))
        :fault))
(must-fail
 (assert-event
  (fn-bpnf-publication-operationp
   (fn-bpnf-publication-authorize
    (bpnfp-issued-state) 9 1 (nth 3 *bpnfc-effect*) t t))))
