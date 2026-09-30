(in-package "ACL2")
(include-book "../../books/page-file-lease")
(include-book "../../books/page-discovery-ledger")
(defconst *prf-budget* '(10000 0 3 1 20))
(defconst *prf-baseline* '(1000 0 0 0 0))
(defconst *prf-start* (mv-nth 1 (mv-list 2 (fn-prl-make-baseline *prf-budget* *prf-baseline*))))
(defconst *prf-registered* (mv-nth 1 (mv-list 2 (fn-prl-register *prf-start* 11 '(64 0 1 0 0)))))
(defconst *prf-acquired* (mv-list 3 (fn-prf-acquire *prf-registered* 11 '(256 0 1 0 1))))
(defconst *prf-token* (mv-nth 1 *prf-acquired*))
(defconst *prf-held* (mv-nth 2 *prf-acquired*))
; KEYSTONE fn-prf-acquire-preserves-pool-funding.
; REACHABLE POSITIVE: exact admission antecedent and complete funding conclusion.
(assert-event (and (equal (mv-nth 0 *prf-acquired*) :admitted)
              (fn-prs-fundedp *prf-budget* *prf-baseline* '(0 0 0 0 0)
                              (fn-prl-nth 1 *prf-held*))
              (equal (fn-prl-close-preview *prf-held* 11) :read-file-held)
              (equal (fn-prf-file *prf-held* *prf-token*) 11)
              (equal (fn-prl-nth 1 *prf-held*) '(320 0 2 0 1))))
; KEYSTONE fn-prf-acquired-file-is-held.
; REACHABLE POSITIVE: exact admission antecedent and whole held-file conclusion.
(assert-event (and (equal (mv-nth 0 *prf-acquired*) :admitted)
                   (equal (fn-prl-close-preview *prf-held* 11) :read-file-held)))
; HYPOTHESIS-REMOVAL: registered but unpinned; no other hypotheses.
(assert-event (let ((r (mv-list 3 (fn-prf-acquire *prf-registered* 11 '(256 0 0 0 1)))))
           (and (not (equal (mv-nth 0 r) :admitted))
                (not (equal (fn-prl-close-preview (mv-nth 2 r) 11) :read-file-held)))))
; KEYSTONE fn-prf-acquire-preserves-pool-funding.
; HYPOTHESIS-REMOVAL: explicitly corrupted, unfunded state; no other hypotheses.
(assert-event (let* ((bad (fn-prl-make nil))
               (r (mv-list 3 (fn-prf-acquire bad 11 '(256 0 1 0 1)))))
           (and (not (equal (mv-nth 0 r) :admitted))
                (not (fn-prs-fundedp nil (fn-prl-baseline bad) '(0 0 0 0 0)
                                    (fn-prl-nth 1 (mv-nth 2 r)))))))
; One page borrow may come and go without consuming the scan's file pin.
(defconst *prf-page* (mv-list 3 (fn-prd-admit *prf-held* 11 128 64 '(256 0 0 1 1))))
(defconst *prf-after-page* (mv-nth 1 (mv-list 2 (fn-prd-release (mv-nth 2 *prf-page*) (mv-nth 1 *prf-page*)))))
(assert-event (and (equal (mv-nth 0 *prf-page*) :admitted)
              (equal (fn-prl-close-preview *prf-after-page* 11) :read-file-held)
              (equal (fn-prf-file *prf-after-page* *prf-token*) 11)
              (equal (mv-list 2 (fn-prl-settle *prf-held* *prf-token* t)) (list :stale *prf-held*))))
(defconst *prf-released* (mv-list 2 (fn-prf-release *prf-after-page* *prf-token*)))
(assert-event (and (equal (mv-nth 0 *prf-released*) :released)
              (equal (fn-prl-close-preview (mv-nth 1 *prf-released*) 11) :closable)
              (equal (fn-prl-baseline (mv-nth 1 *prf-released*)) *prf-baseline*)
              (equal (mv-list 2 (fn-prf-release (mv-nth 1 *prf-released*) *prf-token*))
                     (list :stale (mv-nth 1 *prf-released*)))))
; Mutation: another physical incarnation cannot release this file pin.
(assert-event (equal (mv-list 2 (fn-prf-release *prf-held* '(:file-pin 0 12))) (list :stale *prf-held*)))
(defconst *prf-request* '(:read-page 0 7 2 :directory 2 32768 16384 0))
; Regression for the physical placement boundary: base already skips
; the FNSI wrapper. No contents/authentication conclusion is asserted.
(assert-event (let ((r (mv-list 4 (fn-prf-page-placement *prf-held* *prf-token* *prf-request* 16384))))
           (and (equal (mv-nth 0 r) :placed)
                (equal (mv-nth 1 r) (fn-prf-file *prf-held* *prf-token*))
                (equal (fn-prl-nth 1 *prf-request*) (fn-prl-nth 1 *prf-token*))
                (equal (mv-nth 2 r) (+ 16384 (fn-prl-nth 6 *prf-request*)))
                (equal (mv-nth 3 r) 16384))))
; Hypothesis removal: mutated root ticket refuses and fails file equality.
(assert-event (let* ((bad (update-nth 1 1 *prf-request*))
                (r (mv-list 4 (fn-prf-page-placement *prf-held* *prf-token* bad 16384))))
           (and (not (equal (mv-nth 0 r) :placed))
                (not (equal (mv-nth 1 r) (fn-prf-file *prf-held* *prf-token*))))))
; Releasing a root cannot authorize another page, while an older page's own
; lease still independently prevents the file's close.
(defconst *prf-root-gone* (mv-nth 1 (mv-list 2 (fn-prf-release (mv-nth 2 *prf-page*) *prf-token*))))
(assert-event (and (equal (fn-prl-close-preview *prf-root-gone* 11) :read-file-held)
              (equal (mv-nth 0 (mv-list 4 (fn-prf-page-placement *prf-root-gone* *prf-token* *prf-request* 16384)))
                     :invalid-page-placement)))
