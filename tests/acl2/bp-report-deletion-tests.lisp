(in-package "ACL2")
(include-book "../../books/bp-report-deletion")
(include-book "bp-app-handoff-tests")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bprd-arrival* (fn-clock-observation 1000 0 0 nil))
(defconst *bprd-later* (fn-clock-observation 3601002 0 0 nil))
(defconst *bprd-held*
  (update-nth 9 (fn-bpnf-received-anchor *bpah-bundle* *bprd-arrival*)
              *bpah-held*))
(defconst *bprd-identity*
  (fn-bpp-primary-identity
   (fn-bpb-bundle-primary (fn-bpnf-held-bundle *bprd-held*))))
(defconst *bprd-record*
  (fn-bpn-report-delete-record 1 4 (fn-bpn-nth 3 *bprd-held*)
                               *bprd-identity* :lifetime-expired))

(assert-event (fn-bpn-report-delete-recordp *bprd-record*))
(assert-event
 (equal (fn-bpn-report-find-expired-held
         (list *bprd-held*) *bprd-later*)
        *bprd-held*))
(assert-event
 (mv-let (ok updated)
   (fn-bpn-report-apply-delete *bprd-record* (list *bprd-held*))
   (and ok (equal (fn-bpn-nth 14 (car updated)) :lifetime-expired)
        (not (fn-bpn-report-held-delete-pendingp (car updated)))
        (equal (fn-bpnf-held-key
                (fn-bpnf-held-principal (car updated))
                (fn-bpnf-held-id (car updated)))
               (fn-bpnf-held-key
                (fn-bpnf-held-principal *bprd-held*)
                (fn-bpnf-held-id *bprd-held*))))))
(assert-event
 (mv-let (ok updated)
   (fn-bpn-report-apply-delete
    (fn-bpn-report-delete-record 1 4 (fn-bpn-nth 3 *bprd-held*)
                                 '(1) :lifetime-expired)
    (list *bprd-held*))
   (and (not ok) (equal updated (list *bprd-held*)))))
(must-fail
 (assert-event
  (mv-let (ok updated)
    (fn-bpn-report-apply-delete
     (fn-bpn-report-delete-record 1 4 (fn-bpn-nth 3 *bprd-held*)
                                  '(1) :lifetime-expired)
     (list *bprd-held*))
    (declare (ignore updated)) ok)))
(assert-event
 (null (fn-bpn-report-find-expired-held
        (list *bpah-held*) *bprd-later*))) ; legacy anchor is unknown
(must-fail
 (assert-event
  (fn-bpn-report-find-expired-held
   (list *bpah-held*) *bprd-later*)))
