(in-package "ACL2")
(include-book "page-window-return-continuation-tests")
(include-book "../../books/page-window-return-current")

; Actual owner entry -> existing node -> CURRENT scan -> SAME pool publication.
; Unfunded local registry/pool installation is explicit test scaffolding; the
; pure ledger/worker comes from actual admission/acquire above, not a fake join.
(defun fn-pwrt-fixture-drive (worker token turns fn-page-window-workers fn-page-read-pool)
 (declare (xargs :stobjs (fn-page-window-workers fn-page-read-pool)
  :guard t :verify-guards nil :measure (nfix turns)))
 (if (zp turns) (mv :fixture-timeout nil fn-page-window-workers fn-page-read-pool)
  (mv-let (word row left fn-page-window-workers fn-page-read-pool)
   (fn-owner-page-window-return-step worker token 4 fn-page-window-workers fn-page-read-pool)
   (declare (ignore left))
   (if (eq word :yield)
    (fn-pwrt-fixture-drive worker token (- turns 1) fn-page-window-workers fn-page-read-pool)
    (mv word row fn-page-window-workers fn-page-read-pool)))))

(defun fn-pwrt-current-fixture (fn-page-window-workers fn-page-read-pool)
 (declare (xargs :stobjs (fn-page-window-workers fn-page-read-pool) :guard t :verify-guards nil))
 (let* ((fn-page-read-pool (update-fn-prp-data (list *pwrt-ledger* :fd-root :views :limits :mode 7) fn-page-read-pool))
        ; Representational domain seed is not genuine installed allowance.
        (fn-page-read-pool (update-fn-prp-alloc-installation '(nil nil 1000) fn-page-read-pool))
        (fn-page-window-workers
         (stobj-let
          ((fn-pww-node (fn-pww-registry fn-page-window-workers)))
          (fn-pww-node)
          (stobj-let
           ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
           (fn-pww-carry)
           (let* ((fn-pww-carry (update-fn-pww-token *pwrt-token* fn-pww-carry))
                  (fn-pww-carry (update-fn-pww-phase :running fn-pww-carry))
                  (fn-pww-carry (update-fn-pww-root '(:source :recipient :query) fn-pww-carry))
                  (fn-pww-carry (update-fn-pww-borrow-phase :owned fn-pww-carry))
                  (fn-pww-carry (update-fn-pww-pending-action '(:actual-pending-alias) fn-pww-carry)))
            fn-pww-carry)
           fn-pww-node)
          fn-page-window-workers)))
  (mv-let (word row fn-page-window-workers fn-page-read-pool)
   (fn-pwrt-fixture-drive *pwrt-worker* *pwrt-token* 32 fn-page-window-workers fn-page-read-pool)
   (let* ((expected (mv-list 3 (fn-pwx-return *pwrt-ledger* *pwrt-worker* *pwrt-token*)))
          (ok (and (eq word :returned) (equal row (nth 1 expected))
                   (equal (fn-owner-page-read-ledger fn-page-read-pool) (nth 2 expected))
                   (equal (fn-owner-page-read-binding-revision fn-page-read-pool) 8)
                   (equal (cdr (fn-prp-data fn-page-read-pool)) '(:fd-root :views :limits :mode 8)))))
    (mv-let (again ignored left fn-page-window-workers fn-page-read-pool)
     (fn-owner-page-window-return-step *pwrt-worker* *pwrt-token* 4 fn-page-window-workers fn-page-read-pool)
     (declare (ignore ignored left))
     (mv (and ok (eq again :already-returned)
              (equal (fn-owner-page-read-ledger fn-page-read-pool) (nth 2 expected))
              (equal (fn-owner-page-read-binding-revision fn-page-read-pool) 8))
         fn-page-window-workers fn-page-read-pool))))))

(defun fn-pwrt-current-fixture-run ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-page-window-workers
  (mv-let (answer fn-page-window-workers)
   (with-local-stobj fn-page-read-pool
    (mv-let (answer fn-page-window-workers fn-page-read-pool)
     (fn-pwrt-current-fixture fn-page-window-workers fn-page-read-pool)
     (mv answer fn-page-window-workers)))
   answer)))
(assert-event (fn-pwrt-current-fixture-run))
