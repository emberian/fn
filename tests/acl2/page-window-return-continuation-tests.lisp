(in-package "ACL2")
(include-book "../../books/page-window-return-continuation")
; Actual admission/acquire logical chain. Supplied demand adequacy is NOT claimed.
(defconst *pwrt-admitted*
 (mv-list 3 (fn-prw-admit
  (mv-nth 1 (fn-prl-register
   (mv-nth 1 (fn-prl-make-baseline '(10000 0 2 2 20) '(1000 0 0 0 0)))
   11 '(64 0 1 0 0))) '(11 100 1000 200 900 16 77) '(256 0 0 1 1))))
(defconst *pwrt-token* (nth 1 *pwrt-admitted*))
(defconst *pwrt-acquired* (mv-list 3 (fn-pwx-acquire (nth 2 *pwrt-admitted*) (fn-pxe-new 0) *pwrt-token*)))
(defconst *pwrt-ledger* (nth 2 *pwrt-acquired*))
(defconst *pwrt-worker* (nth 1 *pwrt-acquired*))
(defconst *pwrt-ready*
 (mv-nth 0 (fn-pwrt-run (fn-pwrt-start *pwrt-token* *pwrt-worker* 7
                         (fn-prl-nth 3 *pwrt-ledger*) '(:actual-source :pending-read)) 64)))
; Complete antecedent/conclusion for the actual-return endpoint keystone.
(assert-event
 (and (equal (nth 0 *pwrt-admitted*) :admitted)
      (equal (nth 0 *pwrt-acquired*) :assigned)
      (fn-pwx-boundp *pwrt-ledger* *pwrt-worker* *pwrt-token* :running)
      (fn-pwrt-carryp *pwrt-ready*)
      (eq (fn-prl-nth 9 *pwrt-ready*) :ready)
      (equal (fn-prl-nth 4 *pwrt-ready*) (fn-prl-nth 3 *pwrt-ledger*))
      (equal (mv-list 3 (fn-pwrt-resolved-return *pwrt-ledger* *pwrt-worker* *pwrt-token*
                         (fn-prl-nth 8 *pwrt-ready*) (fn-prl-nth 7 *pwrt-ready*)))
             (mv-list 3 (fn-pwx-return *pwrt-ledger* *pwrt-worker* *pwrt-token*)))))
; Binding hypothesis removal: every other literal premise retained.
(assert-event
 (let ((binding (cons *pwrt-token* '((256 0 0 1 1) :window :running 1)))
       (removed (fn-prl-remove *pwrt-token* (fn-prl-nth 3 *pwrt-ledger*))))
  (and (not (equal binding (fn-prl-binding *pwrt-token* (fn-prl-nth 3 *pwrt-ledger*))))
       (equal removed (fn-prl-remove *pwrt-token* (fn-prl-nth 3 *pwrt-ledger*)))
       (not (equal (mv-list 3 (fn-pwrt-resolved-return *pwrt-ledger* *pwrt-worker* *pwrt-token* binding removed))
                   (mv-list 3 (fn-pwx-return *pwrt-ledger* *pwrt-worker* *pwrt-token*)))))))
; Removal hypothesis removal: actual binding retained, unrelated rows lost.
(assert-event
 (let ((binding (fn-prl-binding *pwrt-token* (fn-prl-nth 3 *pwrt-ledger*))))
  (and (equal binding (fn-prl-binding *pwrt-token* (fn-prl-nth 3 *pwrt-ledger*)))
       (not (equal nil (fn-prl-remove *pwrt-token* (fn-prl-nth 3 *pwrt-ledger*))))
       (not (equal (mv-list 3 (fn-pwrt-resolved-return *pwrt-ledger* *pwrt-worker* *pwrt-token* binding nil))
                   (mv-list 3 (fn-pwx-return *pwrt-ledger* *pwrt-worker* *pwrt-token*)))))))
; Literal complete positives for the actual one/run carry boundaries.
(assert-event
 (let* ((start (fn-pwrt-start *pwrt-token* *pwrt-worker* 7 (fn-prl-nth 3 *pwrt-ledger*) '(:source :aliases)))
        (one (fn-pwrt-one start))
        (run (mv-nth 0 (fn-pwrt-run start 64))))
  (and (fn-pwrt-carryp start) (natp 64)
       (fn-pwrt-carryp one) (fn-pwrt-carryp run)
       (equal (fn-prl-nth 1 one) (fn-prl-nth 1 start))
       (equal (fn-prl-nth 2 one) (fn-prl-nth 2 start))
       (equal (fn-prl-nth 3 one) (fn-prl-nth 3 start))
       (equal (fn-prl-nth 4 one) (fn-prl-nth 4 start))
       (equal (fn-prl-nth 10 one) (fn-prl-nth 10 start))
       (eq (fn-prl-nth 9 run) :ready)
       (equal (fn-prl-nth 8 run) (fn-prl-binding *pwrt-token* (fn-prl-nth 4 run)))
       (equal (fn-prl-nth 7 run) (fn-prl-remove *pwrt-token* (fn-prl-nth 4 run))))))
; Corrupted-state carry removal: all remaining run/one antecedents checked.
(assert-event
 (let* ((start (fn-pwrt-start *pwrt-token* *pwrt-worker* 7 (fn-prl-nth 3 *pwrt-ledger*) :source))
        (bad (update-nth 4 nil start)))
  (and (natp 0) (not (fn-pwrt-carryp bad))
       (not (fn-pwrt-carryp (fn-pwrt-one bad)))
       (not (fn-pwrt-carryp (mv-nth 0 (fn-pwrt-run bad 0)))))))
; Actual cancellation retains original running binding and all charge effects.
(assert-event
 (let* ((cancel (mv-list 3 (fn-pwx-cancel *pwrt-ledger* *pwrt-worker* *pwrt-token*)))
        (worker (nth 1 cancel))
        (cursor (mv-nth 0 (fn-pwrt-run
                 (fn-pwrt-start *pwrt-token* worker 7 (fn-prl-nth 3 *pwrt-ledger*) :source) 64))))
  (and (eq (nth 0 cancel) :cancelled)
       (fn-pwrt-carryp cursor) (eq (fn-prl-nth 9 cursor) :ready)
       (equal (fn-prl-nth 4 cursor) (fn-prl-nth 3 *pwrt-ledger*))
       (equal (mv-list 3 (fn-pwrt-resolved-return *pwrt-ledger* worker *pwrt-token*
                          (fn-prl-nth 8 cursor) (fn-prl-nth 7 cursor)))
              (mv-list 3 (fn-pwx-return *pwrt-ledger* worker *pwrt-token*)))
       (eq (nth 2 (mv-nth 1 (fn-pwx-return *pwrt-ledger* worker *pwrt-token*))) :cancelled-returned))))
