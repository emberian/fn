; PRF-1086: bounded descriptor emission for the existing history image plan.
; The cursor retains source lists; no tick copies or recognizes their suffixes.
; Library component: no host caller or full producer boundedness claim yet.
(in-package "ACL2")
(include-book "history-image-snapshot")

(defun fn-hpc-at (i x)
  (declare (xargs :guard (natp i)))
  (if (zp i) (if (consp x) (car x) nil)
    (fn-hpc-at (1- i) (if (consp x) (cdr x) nil))))

(defthm fn-hpc-at-of-cons
  (equal (fn-hpc-at i (cons a b))
         (if (zp i) a (fn-hpc-at (1- i) b))))

(in-theory (disable fn-hpc-at))

(defun fn-hpc-spinep (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n) (null x)
    (and (consp x) (fn-hpc-spinep (1- n) (cdr x)))))

(defthm fn-hpc-spinep-of-cons
  (equal (fn-hpc-spinep n (cons a b))
         (and (not (zp n)) (fn-hpc-spinep (1- n) b))))

(in-theory (disable fn-hpc-spinep))

(defun fn-hpc-cursorp (c)
  ; Only the fixed outer spine and three scalar fields are inspected.
  (declare (xargs :guard t))
  (and (fn-hpc-spinep 10 c)
       (member-equal (fn-hpc-at 0 c) '(0 1 2 3))
       (natp (fn-hpc-at 5 c)) (natp (fn-hpc-at 6 c))
       (natp (fn-hpc-at 7 c))))

(defun fn-hpc-begin (lpages plan epoch lease)
  ; PLAN is the existing (:plan REC FRESH TL TFRESH RS M ...) result.
  ; Its validity is carried from the preparing producer, not re-scanned.
  (declare (xargs :guard t))
  (list 0 lpages (fn-hpc-at 2 plan) (fn-hpc-at 3 plan)
        (fn-hpc-at 4 plan) (nfix (fn-hpc-at 5 plan)) 0
        (nfix (fn-hpc-at 6 plan)) epoch lease))

(defthm fn-hpc-begin-cursorp
  (fn-hpc-cursorp (fn-hpc-begin lpages plan epoch lease)))

(defun fn-hpc-tick (c)
  ; (mv KIND DESCRIPTOR NEXT), KIND :emit/:yield/:done.
  ; One phase transition OR one descriptor. No payload or stobj effect.
  (declare (xargs :guard (fn-hpc-cursorp c)))
  (let ((phase (fn-hpc-at 0 c))
        (ls (fn-hpc-at 1 c)) (fs (fn-hpc-at 2 c))
        (ts (fn-hpc-at 3 c)) (tf (fn-hpc-at 4 c))
        (rs (fn-hpc-at 5 c)) (j (fn-hpc-at 6 c))
        (m (fn-hpc-at 7 c)) (epoch (fn-hpc-at 8 c))
        (lease (fn-hpc-at 9 c)))
    (cond
     ((equal phase 0)
      (if (and (consp ls) (consp fs))
          (mv :emit (list (nfix (car fs)) 0 (* 2048 (nfix (car ls))))
              (list 0 (cdr ls) (cdr fs) ts tf rs j m epoch lease))
        (mv :yield nil (list 1 nil nil ts tf rs j m epoch lease))))
     ((equal phase 1)
      (if (and (consp ts) (consp tf))
          (mv :emit (list (nfix (car tf)) 2 (* 2048 (nfix (car ts))))
              (list 1 nil nil (cdr ts) (cdr tf) rs j m epoch lease))
        (mv :yield nil (list 2 nil nil nil nil rs j m epoch lease))))
     ((equal phase 2)
      (if (< j m)
          (mv :emit (list (+ rs j) 1 (+ *pgs-x-dir-base* (* 2048 j)))
              (list 2 nil nil nil nil rs (+ 1 j) m epoch lease))
        (mv :yield nil (list 3 nil nil nil nil rs j m epoch lease))))
     (t (mv :done nil c)))))

(defthm fn-hpc-tick-keeps-cursor
  (implies (fn-hpc-cursorp c)
           (fn-hpc-cursorp (mv-nth 2 (fn-hpc-tick c))))
  :hints (("Goal" :in-theory (union-theories
            '(fn-hpc-tick fn-hpc-cursorp fn-hpc-at-of-cons
              fn-hpc-spinep-of-cons (:e fn-hpc-spinep) (:e fn-hpc-at)
              member-equal natp zp) (theory 'minimal-theory)))))

(defthm fn-hpc-tick-keeps-capture-and-lease
  (and (equal (fn-hpc-at 8 (mv-nth 2 (fn-hpc-tick c))) (fn-hpc-at 8 c))
       (equal (fn-hpc-at 9 (mv-nth 2 (fn-hpc-tick c))) (fn-hpc-at 9 c))))

(defun fn-hpc-remaining (c)
  ; Logical residual only. Never called by the host or tick.
  (declare (xargs :guard (fn-hpc-cursorp c)))
  (append
   (if (equal (fn-hpc-at 0 c) 0)
       (fn-his-page-writes (true-list-fix (fn-hpc-at 1 c))
                           (true-list-fix (fn-hpc-at 2 c)) nil) nil)
   (if (member-equal (fn-hpc-at 0 c) '(0 1))
       (fn-his-table-writes (true-list-fix (fn-hpc-at 3 c))
                            (true-list-fix (fn-hpc-at 4 c)) nil) nil)
   (if (member-equal (fn-hpc-at 0 c) '(0 1 2))
       (fn-his-dir-writes (fn-hpc-at 5 c) (fn-hpc-at 6 c)
                          (fn-hpc-at 7 c) nil) nil)))

(local
 (defun fn-hpc-pair-model (ls fs sel)
   (if (or (atom ls) (atom fs)) nil
     (cons (list (nfix (car fs)) sel (* 2048 (nfix (car ls))))
           (fn-hpc-pair-model (cdr ls) (cdr fs) sel)))))
(local
 (defthm fn-hpc-page-writes-model
   (equal (fn-his-page-writes ls fs acc)
          (append (revappend acc nil) (fn-hpc-pair-model ls fs 0)))
   :hints (("Goal" :induct (fn-his-page-writes ls fs acc)
            :in-theory (disable nfix)))))
(local
 (defthm fn-hpc-table-writes-model
   (equal (fn-his-table-writes ls fs acc)
          (append (revappend acc nil) (fn-hpc-pair-model ls fs 2)))
   :hints (("Goal" :induct (fn-his-table-writes ls fs acc)
            :in-theory (disable nfix)))))
(local
 (defun fn-hpc-dir-model (rs j m)
   (declare (xargs :measure (nfix (- (nfix m) (nfix j)))))
   (if (zp (- (nfix m) (nfix j))) nil
     (cons (list (+ rs (nfix j)) 1 (+ *pgs-x-dir-base* (* 2048 (nfix j))))
           (fn-hpc-dir-model rs (+ 1 (nfix j)) m)))))
(local
 (defthm fn-hpc-dir-writes-model
   (equal (fn-his-dir-writes rs j m acc)
          (append (revappend acc nil) (fn-hpc-dir-model rs j m)))
   :hints (("Goal" :induct (fn-his-dir-writes rs j m acc)
            :in-theory (disable nfix)))))

(local
 (defthm fn-hpc-at-is-nth
   (equal (fn-hpc-at i x) (nth i x))
   :hints (("Goal" :in-theory (enable fn-hpc-at nth)))))

(local
 (defthm fn-hpc-nth-of-cons
   (equal (nth i (cons a b)) (if (zp i) a (nth (1- i) b)))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-hpc-begin-is-existing-plan
  (implies (and (true-listp lpages) (fn-his-plan-okp plan))
           (equal (fn-hpc-remaining (fn-hpc-begin lpages plan epoch lease))
                  (fn-his-plan-writes lpages plan)))
  :hints (("Goal" :in-theory (union-theories
           '(fn-hpc-remaining fn-hpc-begin fn-hpc-at-of-cons fn-hpc-at-is-nth
             fn-hpc-nth-of-cons fn-his-plan-writes fn-his-plan-okp nfix natp zp member-equal
             (:e fn-hpc-at) pgs-true-list-fix-when-true-listp)
           (theory 'minimal-theory)))))

(defthm fn-hpc-tick-refines-existing-plan
  (implies (fn-hpc-cursorp c)
           (equal (fn-hpc-remaining c)
                  (append (if (equal (mv-nth 0 (fn-hpc-tick c)) :emit)
                              (list (mv-nth 1 (fn-hpc-tick c))) nil)
                          (fn-hpc-remaining (mv-nth 2 (fn-hpc-tick c))))))
    :hints (("Goal" :expand ((fn-hpc-dir-model (fn-hpc-at 5 c) (fn-hpc-at 6 c) (fn-hpc-at 7 c)))
                     :in-theory (union-theories
            '(fn-hpc-tick fn-hpc-remaining fn-hpc-cursorp fn-hpc-at-of-cons
              fn-hpc-spinep-of-cons (:e fn-hpc-spinep) (:e fn-hpc-at)
              member-equal natp zp nfix true-list-fix
              fn-hpc-page-writes-model fn-hpc-table-writes-model
              fn-hpc-dir-writes-model fn-hpc-pair-model fn-hpc-dir-model
              revappend binary-append car-cons cdr-cons atom not)
            (theory 'minimal-theory)))))

(defthm fn-hpc-done-has-no-remaining-writes
  (implies (and (fn-hpc-cursorp c)
                (equal (mv-nth 0 (fn-hpc-tick c)) :done))
           (equal (fn-hpc-remaining c) nil))
  :hints (("Goal" :in-theory (union-theories
            '(fn-hpc-tick fn-hpc-remaining fn-hpc-cursorp member-equal
              car-cons cdr-cons binary-append natp)
            (theory 'minimal-theory)))))

(in-theory (disable fn-hpc-tick fn-hpc-remaining fn-hpc-begin))
