; Snapshot work borrows the already funded owner work reserve. A resize is
; atomic: return the old grant and borrow the new one, installing only :ok.
(in-package "ACL2")
(include-book "memory-credits")

(defun fn-hroot-work-resize (l id amount)
  (declare (xargs :guard t))
  (let ((returned (cadr (fn-mcr-return l id))))
    (if (zp (nfix amount)) (list :ok returned)
      (fn-mcr-borrow returned id amount))))

(defthm fn-hroot-work-resize-keeps-funded
  (implies (and (fn-mcr-fundedp l)
                (equal (car (fn-hroot-work-resize l id amount)) :ok))
           (fn-mcr-fundedp (cadr (fn-hroot-work-resize l id amount))))
  :hints (("Goal" :in-theory '(car-cons cdr-cons fn-hroot-work-resize
                               fn-mcr-borrow-and-return-keep-funded))))

(defthm fn-hroot-work-resize-keeps-total
  (implies (and (fn-mcr-fundedp l)
                (equal (car (fn-hroot-work-resize l id amount)) :ok))
           (equal (fn-mcr-total (cadr (fn-hroot-work-resize l id amount)))
                  (fn-mcr-total l)))
  :hints (("Goal" :use ((:instance fn-mcr-borrow-and-return-keep-funded (x amount))
                 (:instance fn-mcr-return-gives-back-the-credit (a id))
                 (:instance fn-mcr-borrow-keeps-the-total
                            (l (cadr (fn-mcr-return l id))) (x amount)))
           :in-theory '(car-cons cdr-cons fn-hroot-work-resize fn-mcr-fundedp))))

(defthm fn-hroot-work-resize-sets-credit
  (implies (equal (car (fn-hroot-work-resize l id amount)) :ok)
           (equal (fn-mcr-credit-of id
                    (fn-mcr-ops (cadr (fn-hroot-work-resize l id amount))))
                  (nfix amount)))
  :hints (("Goal" :in-theory '(car-cons cdr-cons fn-hroot-work-resize zp nfix
                               fn-mcr-return-gives-back-the-credit
                               fn-mcr-borrow-sets-the-credit))))

(defun fn-hroot-reader-resize (l id amount workp)
  (declare (xargs :guard t))
  (if workp (fn-hroot-work-resize l id amount) (fn-mcr-resize l id amount)))
(in-theory (disable fn-hroot-work-resize fn-hroot-reader-resize))
