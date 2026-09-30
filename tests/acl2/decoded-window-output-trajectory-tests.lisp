(in-package "ACL2")
(include-book "../../books/decoded-window-output-trajectory")

; Actual initialized history/table and real fixed-Huffman wire, not native
; authority. BAD is an actual pull of the external reserved block-type octet.
(defun-nx pwo-test-as (n)
 (if (zp n) nil (cons 65 (pwo-test-as (1- n)))))
(defun-nx pwo-test-window-case (b0 b1 b2 m lim clear bad out)
 (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
        (input (if bad '(6 115 116 28 177 0 0) '(115 116 28 177 0 0)))
        (st (if bad (fn-zin-pull 0 (car init) input) (fn-zin-set 7 6 (car init))))
        (ip (if bad 1 0))
        (r1 (fn-zin-loop b1 ip (len input) m st input (mv-nth 1 init) (mv-nth 2 init) out))
        (r2 (fn-zin-loop b2 (mv-nth 2 r1) (len input) lim (mv-nth 3 r1) input
                          (mv-nth 4 r1) (mv-nth 5 r1) (if clear nil (mv-nth 6 r1))))
        (whole (fn-zin-loop b0 ip (len input)
                            (if clear (+ (len (mv-nth 6 r1)) (nfix lim)) lim)
                            st input (mv-nth 1 init) (mv-nth 2 init) out)))
  (list r1 r2 whole)))

(local
 (defthm pwo-actual-unconditional-normalization-positive
  (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
         (st (fn-zin-set 7 6 (car init)))
         (input '(115 116 28 177 0 0))
         (r (fn-zin-loop 4096 0 6 128 st input (mv-nth 1 init) (mv-nth 2 init) nil)))
   (and (equal (car r) :full) (equal (mv-nth 6 r) (pwo-test-as 128))
        (equal r (fn-pwz-atomic-output-loop
                  (fn-pwz-actual-loop-semantic-fuel 4096 0 6 128 st input (mv-nth 1 init) (mv-nth 2 init) nil)
                  0 6 128 st input (mv-nth 1 init) (mv-nth 2 init) nil))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (n) (pwo-test-as n))
                     (:free (b ip end lim st input win tab out) (fn-pwz-actual-loop-semantic-fuel b ip end lim st input win tab out))
                     (:free (b ip end lim st input win tab out) (fn-pwz-atomic-output-loop b ip end lim st input win tab out)))
           :in-theory (enable pwo-test-as fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))

(local
 (defthm pwo-actual-retained-positive
  (let* ((case (pwo-test-window-case 4096 1024 512 64 128 nil nil nil))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (<= (nfix 64) (nfix 128)) (equal (car r1) :full) (not (equal (car r2) :yield)) (not (equal (car whole) :yield)) (equal (fn-pwz-semantic-observation whole) (fn-pwz-semantic-observation r2)) (equal (car whole) :full) (equal (mv-nth 6 whole) (pwo-test-as 128))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (n) (pwo-test-as n))) :in-theory (enable pwo-test-as)))))

(local
 (defthm pwo-actual-retained-first-full-removal
  (let* ((case (pwo-test-window-case 4096 1024 512 64 128 nil t nil))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (<= (nfix 64) (nfix 128)) (not (equal (car r1) :full)) (not (equal (car r2) :yield)) (not (equal (car whole) :yield)) (not (equal (fn-pwz-semantic-observation whole) (fn-pwz-semantic-observation r2)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (n) (pwo-test-as n))) :in-theory (enable pwo-test-as)))))

(local
 (defthm pwo-actual-retained-second-completion-removal
  (let* ((case (pwo-test-window-case 4096 1024 0 64 128 nil nil nil))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (<= (nfix 64) (nfix 128)) (equal (car r1) :full) (not (not (equal (car r2) :yield))) (not (equal (car whole) :yield)) (not (equal (fn-pwz-semantic-observation whole) (fn-pwz-semantic-observation r2)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (n) (pwo-test-as n))) :in-theory (enable pwo-test-as)))))

(local
 (defthm pwo-actual-retained-whole-completion-removal
  (let* ((case (pwo-test-window-case 0 1024 512 64 128 nil nil nil))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (<= (nfix 64) (nfix 128)) (equal (car r1) :full) (not (equal (car r2) :yield)) (not (not (equal (car whole) :yield))) (not (equal (fn-pwz-semantic-observation whole) (fn-pwz-semantic-observation r2)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (n) (pwo-test-as n))) :in-theory (enable pwo-test-as)))))

(local
 (defthm pwo-actual-retained-frontier-order-removal
  (let* ((case (pwo-test-window-case 4096 1024 512 128 64 nil nil nil))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (not (<= (nfix 128) (nfix 64))) (equal (car r1) :full) (not (equal (car r2) :yield)) (not (equal (car whole) :yield)) (not (equal (fn-pwz-semantic-observation whole) (fn-pwz-semantic-observation r2)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (n) (pwo-test-as n))) :in-theory (enable pwo-test-as)))))

(local
 (defthm pwo-actual-cleared-positive
  (let* ((case (pwo-test-window-case 4096 1024 512 64 64 t nil nil))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (true-listp nil) (equal (car r1) :full) (not (equal (car r2) :yield)) (not (equal (car whole) :yield)) (equal (fn-pwz-semantic-observation whole) (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2) (append (mv-nth 6 r1) (mv-nth 6 r2)))) (equal (car whole) :full) (equal (mv-nth 6 whole) (pwo-test-as 128))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (n) (pwo-test-as n))) :in-theory (enable pwo-test-as)))))

(local
 (defthm pwo-actual-cleared-first-full-removal
  (let* ((case (pwo-test-window-case 4096 1024 512 64 64 t t nil))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (true-listp nil) (not (equal (car r1) :full)) (not (equal (car r2) :yield)) (not (equal (car whole) :yield)) (not (equal (fn-pwz-semantic-observation whole) (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2) (append (mv-nth 6 r1) (mv-nth 6 r2)))))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (n) (pwo-test-as n))) :in-theory (enable pwo-test-as)))))

(local
 (defthm pwo-actual-cleared-second-completion-removal
  (let* ((case (pwo-test-window-case 4096 1024 0 64 64 t nil nil))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (true-listp nil) (equal (car r1) :full) (not (not (equal (car r2) :yield))) (not (equal (car whole) :yield)) (not (equal (fn-pwz-semantic-observation whole) (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2) (append (mv-nth 6 r1) (mv-nth 6 r2)))))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (n) (pwo-test-as n))) :in-theory (enable pwo-test-as)))))

(local
 (defthm pwo-actual-cleared-whole-completion-removal
  (let* ((case (pwo-test-window-case 0 1024 512 64 64 t nil nil))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (true-listp nil) (equal (car r1) :full) (not (equal (car r2) :yield)) (not (not (equal (car whole) :yield))) (not (equal (fn-pwz-semantic-observation whole) (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2) (append (mv-nth 6 r1) (mv-nth 6 r2)))))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (n) (pwo-test-as n))) :in-theory (enable pwo-test-as)))))

(local
 (defthm pwo-actual-cleared-corrupted-output-properness-removal
  (let* ((case (pwo-test-window-case 4096 1024 512 1 0 t nil '(65 . 1)))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (not (true-listp '(65 . 1))) (equal (car r1) :full) (not (equal (car r2) :yield)) (not (equal (car whole) :yield)) (not (equal (fn-pwz-semantic-observation whole) (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2) (append (mv-nth 6 r1) (mv-nth 6 r2)))))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (n) (pwo-test-as n))) :in-theory (enable pwo-test-as)))))
