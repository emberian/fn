(in-package "ACL2")
(include-book "page-window-return-current-ready-tests")
; Corrupted-state hypothesis removal for the CURRENT keystone.
; Only the ghost carry hypothesis is omitted; every retained premise is checked.
; This ready state is reachable by the actual owner-entry trace in the prior
; fixture. Local creator/domain seeds remain explicitly unfunded scaffolding.
(defun fn-pwrt-ready-carry-removal-fixture (fn-page-window-workers fn-page-read-pool)
 (declare (xargs :stobjs (fn-page-window-workers fn-page-read-pool) :guard t :verify-guards nil))
 (let* ((fn-page-read-pool (update-fn-prp-data (list *pwrt-ledger* :fd :view :limits :mode 7) fn-page-read-pool))
        (fn-page-read-pool (update-fn-prp-alloc-installation '(nil nil 1000) fn-page-read-pool))
        (fn-page-window-workers
         (stobj-let
          ((fn-pww-node (fn-pww-registry fn-page-window-workers)))
          (fn-pww-node)
          (stobj-let
           ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
           (fn-pww-carry)
           (let* ((fn-pww-carry (update-fn-pww-token *pwrt-token* fn-pww-carry))
                  (fn-pww-carry (update-fn-pww-phase :return-scanning fn-pww-carry))
                  (fn-pww-carry (update-fn-pww-root '(:source :recipient :query) fn-pww-carry))
                  (fn-pww-carry (update-fn-pww-borrow-phase :owned fn-pww-carry))
                  (fn-pww-carry (update-fn-pww-pending-action
                   (update-nth 8
                    (cons *pwrt-token* (update-nth 3 1 (cdr (fn-prl-nth 8 *pwrt-ready*))))
                    *pwrt-ready*) fn-pww-carry)))
            fn-pww-carry)
           fn-pww-node)
          fn-page-window-workers))
        (expected (mv-list 3 (fn-pwx-return *pwrt-ledger* *pwrt-worker* *pwrt-token*)))
        (antecedent
         (stobj-let
          ((fn-pww-node (fn-pww-registry fn-page-window-workers)))
          (answer)
          (stobj-let
           ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
           (answer)
           (let ((cursor (fn-pww-pending-action fn-pww-carry)))
            (and (fn-pwx-tokenp *pwrt-token*) (natp 1) (< 0 1)
                 (equal *pwrt-token* (fn-pww-token fn-pww-carry))
                 (eq (fn-pww-phase fn-pww-carry) :return-scanning)
                 (eq (fn-prl-nth 0 cursor) :window-return)
                 (equal *pwrt-token* (fn-prl-nth 1 cursor))
                 (equal (fn-owner-page-read-binding-revision fn-page-read-pool) (fn-prl-nth 3 cursor))
                 (fn-pwrt-revision-roomp (fn-prl-nth 3 cursor) fn-page-read-pool)
                 (not (fn-pwrt-carryp cursor)) (eq (fn-prl-nth 9 cursor) :ready)
                 (equal (fn-prl-nth 4 cursor) (fn-prl-nth 3 (fn-owner-page-read-ledger fn-page-read-pool)))
                 (eq (nth 0 expected) :returned)))
           answer)
          answer)))
  (mv-let (word row left fn-page-window-workers fn-page-read-pool)
   (fn-owner-page-window-return-step *pwrt-worker* *pwrt-token* 2 fn-page-window-workers fn-page-read-pool)
   (declare (ignore left))
   (let ((conclusion
          (stobj-let
           ((fn-pww-node (fn-pww-registry fn-page-window-workers)))
           (answer)
           (stobj-let
            ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
            (answer)
            (and (eq word :returned) (equal row (nth 1 expected))
                 (equal (fn-owner-page-read-ledger fn-page-read-pool) (nth 2 expected))
                 (equal (fn-pww-phase fn-pww-carry) (fn-prl-nth 2 (nth 1 expected)))
                 (equal (fn-pww-root fn-pww-carry) '(:source :recipient :query))
                 (eq (fn-pww-borrow-phase fn-pww-carry) :owned))
            answer)
           answer)))
    (mv (and antecedent (not conclusion)) fn-page-window-workers fn-page-read-pool)))))
(defun fn-pwrt-ready-carry-removal-fixture-run ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-page-window-workers
  (mv-let (answer fn-page-window-workers)
   (with-local-stobj fn-page-read-pool
    (mv-let (answer fn-page-window-workers fn-page-read-pool)
     (fn-pwrt-ready-carry-removal-fixture fn-page-window-workers fn-page-read-pool)
     (mv answer fn-page-window-workers)))
   answer)))
(assert-event (fn-pwrt-ready-carry-removal-fixture-run))
