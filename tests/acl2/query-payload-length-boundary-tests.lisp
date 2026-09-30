(in-package "ACL2")
(include-book "../../books/query-payload-length-boundary")
; Unfunded registered projection fixture. This uses actual selected-read,
; actual active QPG child and STATE ledger, not a fabricated observation.
; It is not a faithful publication/constructor/runtime or native witness.
(defun-nx fn-qplt-registered-fixture (fuel state)
  (declare (xargs :stobjs state :guard (natp fuel)))
  (let* ((state (f-put-global 'fn-owner-payload-view '(0 nil nil) state))
         (token (fn-ibp-query-token 1 1 0 1))
         (query (fn-miq-make 1 1 '(1 2) 1 9 2 "<a@x>" 7 '(1 2 0) nil 0 :done))
         (capture (fn-ibp-capture-make 1 '(1 2) 2 1 9 nil 0 1 nil 0 2))
         (grant '(:query-grant 1 1 0 1 1 2 1 9 1 0 1))
         (qpg (update-fn-qpg-segment-id 1 (create-fn-query-payload-grants)))
         (acquired (mv-list 3 (fn-qpg-acquire 1 0 1 0 1 grant qpg)))
         (qpg-token (nth 1 acquired))
         (segment (update-fn-ibp-qs-id 1 (create-fn-ibp-query-segment)))
         (registered (mv-list 2 (fn-ibp-query-slot-register token query capture segment)))
         (segment (update-fn-ibp-qs-inputsi 0 (list :query-context nil nil nil nil qpg-token)
                                            (nth 1 registered)))
         (segment (update-fn-ibp-qs-admissionsi 0 (list grant '(1 0 0 0 0) :active 1) segment))
         (selected (fn-miq-selected-token token 0 2))
         (held '(1 1 1 (60 97 64 120 62) 0 nil nil nil nil 0 nil nil nil nil nil))
         (updated (mv-list 2 (fn-ibp-query-slot-update token query
                              (list :selected selected held '(:chunk 4 18 2)) segment)))
         (node (fn-ibp-node-children-put 'fn-ibp-query-segment (nth 1 updated) (create-fn-ibp-node)))
         (node (fn-ibp-node-children-put 'fn-query-payload-grants (nth 2 acquired) node))
         (backing (update-fn-ibp-registry node (create-fn-index-backing)))
         (backing (update-fn-ibp-pool-capacity 1 backing))
         (mio (update-fn-mio$c-provider backing (create-fn-mio$c)))
         (selection (mv-list 4 (fn-miq-selected-read selected fuel mio)))
         (answer (mv-list 3 (fn-miq-selected-payload-length selected fuel mio '((65 66)) state)))
         (expected (list :ready (list :payload-length selected qpg-token 0 2)
                         (- (nth 3 selection) 1)))
         (installed (and (equal (nth 0 acquired) :acquired)
                         (equal (nth 0 registered) :captured)
                         (equal (nth 0 updated) :updated)
                         (equal (nth 0 selection) :selected)
                         (equal (nth 1 selection) held)
                         (equal (nth 2 selection) qpg-token))))
    (mv (list installed (equal (car answer) :ready) (equal answer expected)) state)))


(defthm fn-qplt-ready-denotation-positive
  (implies (state-p state)
    (let ((report (mv-nth 0 (fn-qplt-registered-fixture 4 state))))
      (and (nth 0 report) (nth 1 report) (nth 2 report))))
  :rule-classes nil)

; Literal omission of the ONLY keystone hypothesis: actual :ready.
; The same registered query and grant remain active, but fuel3 leaves zero
; scalar fuel, so actual wrapper :yield cannot equal the ready denotation.
(defthm fn-qplt-ready-hypothesis-removal
  (implies (state-p state)
    (let ((report (mv-nth 0 (fn-qplt-registered-fixture 3 state))))
      (and (nth 0 report) (not (nth 1 report)) (not (nth 2 report)))))
  :rule-classes nil)
