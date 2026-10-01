(in-package "ACL2")
(include-book "../../books/decoded-window-finite-output-trajectory")


(defun-nx pwf-test-case (turns b0)
 (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
        (input '(115 116 28 177 0 0)) (st (fn-zin-set 7 6 (car init)))
        (s (fn-pwf-actual-output-turns turns 0 6 st input
                   (mv-nth 1 init) (mv-nth 2 init) nil))
        (ref (fn-pwz-atomic-output-loop (mv-nth 1 s) 0 6 (mv-nth 2 s) st input
                   (mv-nth 1 init) (mv-nth 2 init) nil))
        (whole (fn-zin-loop b0 0 6 (mv-nth 2 s) st input
                   (mv-nth 1 init) (mv-nth 2 init) nil)))
  (list s ref whole)))

(local
 (defthm pwf-finite-yields-and-two-output-frontiers-positive
  (let* ((c (pwf-test-case '((64 1 1 1 1024) (128 1 1024)) 4096))
         (s (car c)) (r (mv-nth 0 s)))
   (and (mv-nth 3 s) (equal (mv-nth 2 s) 128)
        (equal r (cadr c)) (equal (len (mv-nth 6 r)) 128)
        (equal (car r) :full)))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (b ip end lim st input win tab out)
                             (fn-pwz-actual-loop-semantic-fuel b ip end lim st input win tab out))
                           (:free (b ip end lim st input win tab out)
                             (fn-pwz-atomic-output-loop b ip end lim st input win tab out)))
           :in-theory (enable fn-pwf-actual-output-turns fn-pwy-actual-loop-turns
                              fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))

(local
 (defthm pwf-empty-finite-output-transcript-positive
  (let* ((c (pwf-test-case nil 4096)) (s (car c)))
   (and (mv-nth 3 s) (equal (mv-nth 2 s) 0)
        (equal (mv-nth 0 s) (cadr c))
        (equal (car (mv-nth 0 s)) :yield)))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (b ip end lim st input win tab out)
                             (fn-pwz-actual-loop-semantic-fuel b ip end lim st input win tab out))
                           (:free (b ip end lim st input win tab out)
                             (fn-pwz-atomic-output-loop b ip end lim st input win tab out)))
           :in-theory (enable fn-pwf-actual-output-turns fn-pwy-actual-loop-turns
                              fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))

(local
 (defthm pwf-final-frontier-bound-removal
  (let* ((c (pwf-test-case '((128 1024) (64 1024)) 4096)) (s (car c)))
   (and (not (mv-nth 3 s)) (not (equal (mv-nth 0 s) (cadr c)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (b ip end lim st input win tab out)
                             (fn-pwz-actual-loop-semantic-fuel b ip end lim st input win tab out))
                           (:free (b ip end lim st input win tab out)
                             (fn-pwz-atomic-output-loop b ip end lim st input win tab out)))
           :in-theory (enable fn-pwf-actual-output-turns fn-pwy-actual-loop-turns
                              fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))

(local
 (defthm pwf-completed-finite-output-matches-actual-basic-loop-positive
  (let* ((c (pwf-test-case '((64 1 1 1 1024) (128 1 1024)) 4096))
         (s (car c)) (r (mv-nth 0 s)) (whole (caddr c)))
   (and (mv-nth 3 s) (not (equal (car r) :yield)) (not (equal (car whole) :yield))
        (equal (fn-pwz-semantic-observation r) (fn-pwz-semantic-observation whole))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (b ip end lim st input win tab out)
                             (fn-pwz-actual-loop-semantic-fuel b ip end lim st input win tab out))
                           (:free (b ip end lim st input win tab out)
                             (fn-pwz-atomic-output-loop b ip end lim st input win tab out)))
           :in-theory (enable fn-pwf-actual-output-turns fn-pwy-actual-loop-turns
                              fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))

(local
 (defthm pwf-completed-final-frontier-bound-removal
  (let* ((c (pwf-test-case '((128 1024) (64 1024)) 4096))
         (s (car c)) (r (mv-nth 0 s)) (whole (caddr c)))
   (and (not (mv-nth 3 s)) (not (equal (car r) :yield)) (not (equal (car whole) :yield))
        (not (equal (fn-pwz-semantic-observation r) (fn-pwz-semantic-observation whole)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (b ip end lim st input win tab out)
                             (fn-pwz-actual-loop-semantic-fuel b ip end lim st input win tab out))
                           (:free (b ip end lim st input win tab out)
                             (fn-pwz-atomic-output-loop b ip end lim st input win tab out)))
           :in-theory (enable fn-pwf-actual-output-turns fn-pwy-actual-loop-turns
                              fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))

(local
 (defthm pwf-finite-output-completion-removal
  (let* ((c (pwf-test-case '((252 1)) 4096))
         (s (car c)) (r (mv-nth 0 s)) (whole (caddr c)))
   (and (mv-nth 3 s) (equal (car r) :yield) (not (equal (car whole) :yield))
        (not (equal (fn-pwz-semantic-observation r) (fn-pwz-semantic-observation whole)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (b ip end lim st input win tab out)
                             (fn-pwz-actual-loop-semantic-fuel b ip end lim st input win tab out))
                           (:free (b ip end lim st input win tab out)
                             (fn-pwz-atomic-output-loop b ip end lim st input win tab out)))
           :in-theory (enable fn-pwf-actual-output-turns fn-pwy-actual-loop-turns
                              fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))

(local
 (defthm pwf-whole-loop-completion-removal
  (let* ((c (pwf-test-case '((64 1024) (128 1024)) 1))
         (s (car c)) (r (mv-nth 0 s)) (whole (caddr c)))
   (and (mv-nth 3 s) (not (equal (car r) :yield)) (equal (car whole) :yield)
        (not (equal (fn-pwz-semantic-observation r) (fn-pwz-semantic-observation whole)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (b ip end lim st input win tab out)
                             (fn-pwz-actual-loop-semantic-fuel b ip end lim st input win tab out))
                           (:free (b ip end lim st input win tab out)
                             (fn-pwz-atomic-output-loop b ip end lim st input win tab out)))
           :in-theory (enable fn-pwf-actual-output-turns fn-pwy-actual-loop-turns
                              fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))
