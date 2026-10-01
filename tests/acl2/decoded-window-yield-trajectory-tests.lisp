(in-package "ACL2")
(include-book "../../books/decoded-window-yield-trajectory")

(defun-nx pwy-test-case (b1 b2 lim)
 (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
        (input '(115 116 28 177 0 0))
        (st (fn-zin-set 7 6 (car init)))
        (win (mv-nth 1 init)) (tab (mv-nth 2 init))
        (r1 (fn-zin-loop b1 0 6 lim st input win tab nil))
        (r2 (fn-zin-loop b2 (mv-nth 2 r1) 6 lim (mv-nth 3 r1) input
                          (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
        (f1 (fn-pwz-actual-loop-semantic-fuel b1 0 6 lim st input win tab nil))
        (f2 (fn-pwz-actual-loop-semantic-fuel b2 (mv-nth 2 r1) 6 lim (mv-nth 3 r1) input
                                            (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
        (whole (fn-pwz-atomic-output-loop (+ f1 f2) 0 6 lim st input win tab nil)))
  (list r1 r2 whole)))

(local
 (defthm pwy-actual-yield-resumption-positive
  (let* ((c (pwy-test-case 1 4096 128)) (r1 (car c)) (r2 (cadr c)) (whole (caddr c)))
   (and (equal (car r1) :yield) (equal (car r2) :full)
        (equal (len (mv-nth 6 r2)) 128) (equal r2 whole)))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (b ip end lim st input win tab out) (fn-pwz-actual-loop-semantic-fuel b ip end lim st input win tab out))
                           (:free (b ip end lim st input win tab out) (fn-pwz-atomic-output-loop b ip end lim st input win tab out)))
           :in-theory (enable fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))

; Actual same-frontier basic-loop API; no repeated-full controller reachability claim.
(local
 (defthm pwy-actual-first-yield-removal
  (let* ((c (pwy-test-case 4096 4096 64)) (r1 (car c)) (r2 (cadr c)) (whole (caddr c)))
   (and (not (equal (car r1) :yield)) (equal (car r1) :full)
        (equal (car r2) :full) (equal (len (mv-nth 6 r1)) 64)
        (not (equal r2 whole))
        (not (equal (mv-nth 1 r2) (mv-nth 1 whole)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (b ip end lim st input win tab out) (fn-pwz-actual-loop-semantic-fuel b ip end lim st input win tab out))
                           (:free (b ip end lim st input win tab out) (fn-pwz-atomic-output-loop b ip end lim st input win tab out)))
           :in-theory (enable fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))

(defun-nx pwy-test-finite-case (quanta lim)
 (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
        (input '(115 116 28 177 0 0)) (st (fn-zin-set 7 6 (car init)))
        (r (fn-pwy-actual-loop-turns quanta 0 6 lim st input (mv-nth 1 init) (mv-nth 2 init) nil)))
  (list (mv-nth 0 r) (mv-nth 1 r)
   (fn-pwz-atomic-output-loop (mv-nth 1 r) 0 6 lim st input (mv-nth 1 init) (mv-nth 2 init) nil))))

(local
 (defthm pwy-actual-finite-yield-chain-positive
  (let ((r (pwy-test-finite-case '(1 1 1 4096) 128)))
   (and (equal (car (car r)) :full) (equal (len (mv-nth 6 (car r))) 128)
        (natp (cadr r)) (equal (car r) (caddr r))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (qs ip end lim st input win tab out) (fn-pwy-actual-loop-turns qs ip end lim st input win tab out))
                           (:free (b ip end lim st input win tab out) (fn-pwz-actual-loop-semantic-fuel b ip end lim st input win tab out))
                           (:free (b ip end lim st input win tab out) (fn-pwz-atomic-output-loop b ip end lim st input win tab out)))
           :in-theory (enable fn-pwy-actual-loop-turns fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))

(local
 (defthm pwy-actual-empty-quanta-yield-positive
  (let ((r (pwy-test-finite-case nil 128)))
   (and (equal (car (car r)) :yield) (equal (cadr r) 0)
        (equal (car r) (caddr r))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwy-actual-loop-turns fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))

(defun-nx pwy-test-completed-case (quanta b0)
 (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
        (input '(115 116 28 177 0 0)) (st (fn-zin-set 7 6 (car init)))
        (r (fn-pwy-actual-loop-turns quanta 0 6 128 st input (mv-nth 1 init) (mv-nth 2 init) nil))
        (whole (fn-zin-loop b0 0 6 128 st input (mv-nth 1 init) (mv-nth 2 init) nil)))
  (list (mv-nth 0 r) whole)))

(local
 (defthm pwy-actual-completed-finite-chain-positive
  (let* ((c (pwy-test-completed-case '(1 1 1 4096) 4096)) (r (car c)) (whole (cadr c)))
   (and (not (equal (car r) :yield)) (not (equal (car whole) :yield))
        (equal (car r) :full) (equal (len (mv-nth 6 r)) 128)
        (equal (fn-pwz-semantic-observation r) (fn-pwz-semantic-observation whole))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (qs ip end lim st input win tab out) (fn-pwy-actual-loop-turns qs ip end lim st input win tab out)))
    :in-theory (enable fn-pwy-actual-loop-turns fn-pwz-semantic-observation)))))

(local
 (defthm pwy-actual-finite-completion-removal
  (let* ((c (pwy-test-completed-case '(1) 4096)) (r (car c)) (whole (cadr c)))
   (and (equal (car r) :yield) (not (equal (car whole) :yield))
        (not (equal (fn-pwz-semantic-observation r) (fn-pwz-semantic-observation whole)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (qs ip end lim st input win tab out) (fn-pwy-actual-loop-turns qs ip end lim st input win tab out)))
    :in-theory (enable fn-pwy-actual-loop-turns fn-pwz-semantic-observation)))))

(local
 (defthm pwy-actual-basic-completion-removal
  (let* ((c (pwy-test-completed-case '(1 1 1 4096) 1)) (r (car c)) (whole (cadr c)))
   (and (not (equal (car r) :yield)) (equal (car whole) :yield)
        (not (equal (fn-pwz-semantic-observation r) (fn-pwz-semantic-observation whole)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (qs ip end lim st input win tab out) (fn-pwy-actual-loop-turns qs ip end lim st input win tab out)))
    :in-theory (enable fn-pwy-actual-loop-turns fn-pwz-semantic-observation)))))
