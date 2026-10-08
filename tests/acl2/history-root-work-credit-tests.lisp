(in-package "ACL2")
(include-book "../../books/history-root-work-credit")
(include-book "../../books/owner-credits")
(include-book "../../books/defkeystone")

; The observed development case: 72 records need more than the article pool.
; The existing owner-work reserve holds them without changing that pool.
(defconst *fn-hroot-work-test-ledger*
  (fn-mca-initial *fn-bs-profile-development* 0 0 nil))
(defthm fn-hroot-work-positive
  (let* ((l *fn-hroot-work-test-ledger*)
         (r (fn-hroot-work-resize l :snapshot 3537792)))
    (and (fn-mcr-fundedp l) (equal (car r) :ok)
         (fn-mcr-fundedp (cadr r))
         (equal (fn-mcr-total (cadr r)) (fn-mcr-total l))
         (equal (fn-mcr-credit-of :snapshot (fn-mcr-ops (cadr r))) 3537792)
         (equal (fn-mcr-resize l :snapshot 3537792)
                '(:refused :memory-budget-exhausted)))))

; A missing-reserve mutant uses ordinary resize instead: it consumes the
; article pool and changes the funded total, even when the charge fits.
(defthm fn-hroot-work-pool-mutant
  (let* ((l *fn-hroot-work-test-ledger*)
         (r (fn-hroot-work-resize l :snapshot 256)))
    (and (fn-mcr-fundedp l) (equal (car r) :ok)
         (not (equal (fn-mcr-total (cadr (fn-mcr-resize l :snapshot 256)))
                     (fn-mcr-total l))))))

(defconst *fn-hroot-duplicate-ledger*
  (fn-mcr-make 100 0 0 0 0 0 '((:snapshot 0 . 1) (:snapshot 0 . 2)) 0 nil))
(defthm fn-hroot-work-unfunded-break
  (let* ((l *fn-hroot-duplicate-ledger*) (r (fn-hroot-work-resize l :snapshot 1)))
    (and (not (fn-mcr-fundedp l)) (equal (car r) :ok)
         (not (equal (fn-mcr-total (cadr r)) (fn-mcr-total l))))))
(defthm fn-hroot-work-refused-break
  (let* ((l *fn-hroot-work-test-ledger*)
         (r (fn-hroot-work-resize l :snapshot (+ 1 (fn-mcr-completion l)))))
    (and (fn-mcr-fundedp l) (not (equal (car r) :ok))
         (not (equal (fn-mcr-total (cadr r)) (fn-mcr-total l))))))

(defteeth fn-hroot-work-resize-keeps-total
  :claim (((funded (fn-mcr-fundedp l))
           (admitted (equal (car (fn-hroot-work-resize l id amount)) :ok)))
          (equal (fn-mcr-total (cadr (fn-hroot-work-resize l id amount)))
                 (fn-mcr-total l)))
  :subject fn-hroot-work-resize
  :witness ((l *fn-hroot-work-test-ledger*) (id :snapshot) (amount 3537792))
  :breaks ((funded ((l *fn-hroot-duplicate-ledger*) (id :snapshot) (amount 1)))
           (admitted ((l *fn-hroot-work-test-ledger*) (id :snapshot)
                      (amount (+ 1 (fn-mcr-completion *fn-hroot-work-test-ledger*))))))
  :mutations ((article-pool
               (:conclusion (equal (fn-mcr-total (cadr (fn-mcr-resize l id amount)))
                                   (fn-mcr-total l)))
               ((l *fn-hroot-work-test-ledger*) (id :snapshot) (amount 256))
               :fault "snapshot retention consumes the user article pool")))

(defthm fn-hroot-work-grow-return-and-refuse
  (let* ((l *fn-hroot-work-test-ledger*)
         (held (cadr (fn-hroot-work-resize l :snapshot 3537792)))
         (grown (cadr (fn-hroot-work-resize held :snapshot 4000000)))
         (returned (cadr (fn-hroot-work-resize grown :snapshot 0))))
    (and (equal (fn-mcr-credit-of :snapshot (fn-mcr-ops grown)) 4000000)
         (equal (fn-mcr-completion returned) (fn-mcr-completion l))
         (equal (fn-mcr-ops returned) (fn-mcr-ops l))
         (equal (fn-hroot-work-resize held :snapshot (+ 1 (fn-mcr-completion l)))
                '(:refused :completion-reserve-exhausted)))))
