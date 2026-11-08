; Logical transport over a common finite domain. These traversals are proof
; machinery, not allocations on a served path. Functional instances discharge
; locality; the constrained functions introduce no system assumption.
(in-package "ACL2")

(encapsulate
 (((fn2-pw-point * * *) => *)
  ((fn2-pw-step * * * * *) => *)
  ((fn2-pw-affected * * * * * *) => *))
 (local (defun fn2-pw-point (key g c) (declare (ignore key g c)) t))
 (local (defun fn2-pw-step (delta g a h b)
          (declare (ignore delta g a h b)) t))
 (local (defun fn2-pw-affected (key delta g a h b)
          (declare (ignore key delta g a h b)) nil))
 (defthm fn2-pw-off-footprint
   (implies (and (fn2-pw-step delta g a h b)
                 (not (fn2-pw-affected key delta g a h b))
                 (fn2-pw-point key g a))
            (fn2-pw-point key h b))
   :rule-classes nil))

(defun fn2-pw-all (keys g c)
  (if (atom keys) t
    (and (fn2-pw-point (car keys) g c) (fn2-pw-all (cdr keys) g c))))
(defun fn2-pw-repaired (keys delta g a h b)
  (if (atom keys) t
    (and (or (not (fn2-pw-affected (car keys) delta g a h b))
             (fn2-pw-point (car keys) h b))
         (fn2-pw-repaired (cdr keys) delta g a h b))))
(defthm fn2-pw-transport
  (implies (and (fn2-pw-all keys g a)
                (fn2-pw-step delta g a h b)
                (fn2-pw-repaired keys delta g a h b))
           (fn2-pw-all keys h b))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-pw-all keys g a))
          ("Subgoal *1/2" :use ((:instance fn2-pw-off-footprint (key (car keys)))))))

; The bounded range is [start,start+count). No proper-list or duplicate-free
; hypothesis is needed: all traversals use exactly the same domain.
(defun fn2-pw-range (start count g c)
  (declare (xargs :measure (nfix count)))
  (if (zp count) t
    (and (fn2-pw-point start g c)
         (fn2-pw-range (+ 1 start) (- count 1) g c))))
(defun fn2-pw-range-repaired (start count delta g a h b)
  (declare (xargs :measure (nfix count)))
  (if (zp count) t
    (and (or (not (fn2-pw-affected start delta g a h b))
             (fn2-pw-point start h b))
         (fn2-pw-range-repaired (+ 1 start) (- count 1) delta g a h b))))
(defthm fn2-pw-range-transport
  (implies (and (fn2-pw-range start count g a)
                (fn2-pw-step delta g a h b)
                (fn2-pw-range-repaired start count delta g a h b))
           (fn2-pw-range start count h b))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-pw-range start count g a))
          ("Subgoal *1/2" :use ((:instance fn2-pw-off-footprint (key start))))))

; Independent constraints: predicate instances need not prove a fold law.
; The affected set is evaluated with BOTH endpoints and held fixed for the
; two sums. This also permits transitions which change ghost context.
(encapsulate
 (((fn2-fold-value * * *) => *)
  ((fn2-fold-step * * * * *) => *)
  ((fn2-fold-affected * * * * * *) => *))
 (local (defun fn2-fold-value (key g c) (declare (ignore key g c)) 0))
 (local (defun fn2-fold-step (delta g a h b)
          (declare (ignore delta g a h b)) t))
 (local (defun fn2-fold-affected (key delta g a h b)
          (declare (ignore key delta g a h b)) nil))
 (defthm fn2-fold-value-numberp
   (acl2-numberp (fn2-fold-value key g c)) :rule-classes :type-prescription)
 (defthm fn2-fold-off-footprint
   (implies (and (fn2-fold-step delta g a h b)
                 (not (fn2-fold-affected key delta g a h b)))
            (equal (fn2-fold-value key h b) (fn2-fold-value key g a)))
   :rule-classes nil))
(defun fn2-fold-all (keys g c)
  (if (atom keys) 0
    (+ (fn2-fold-value (car keys) g c) (fn2-fold-all (cdr keys) g c))))
(defun fn2-fold-touched (keys delta g a h b context core)
  (if (atom keys) 0
    (+ (if (fn2-fold-affected (car keys) delta g a h b)
           (fn2-fold-value (car keys) context core) 0)
       (fn2-fold-touched (cdr keys) delta g a h b context core))))
(defthm fn2-fold-replacement
  (implies (fn2-fold-step delta g a h b)
           (equal (+ (fn2-fold-all keys h b)
                     (fn2-fold-touched keys delta g a h b g a))
                  (+ (fn2-fold-all keys g a)
                     (fn2-fold-touched keys delta g a h b h b))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-fold-all keys g a))
          ("Subgoal *1/2" :use ((:instance fn2-fold-off-footprint (key (car keys)))))))
(defun fn2-fold-range (start count g c)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (fn2-fold-value start g c) (fn2-fold-range (+ 1 start) (- count 1) g c))))
(defun fn2-fold-range-touched (start count delta g a h b context core)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (if (fn2-fold-affected start delta g a h b)
           (fn2-fold-value start context core) 0)
       (fn2-fold-range-touched (+ 1 start) (- count 1) delta g a h b context core))))
(defthm fn2-fold-range-replacement
  (implies (fn2-fold-step delta g a h b)
           (equal (+ (fn2-fold-range start count h b)
                     (fn2-fold-range-touched start count delta g a h b g a))
                  (+ (fn2-fold-range start count g a)
                     (fn2-fold-range-touched start count delta g a h b h b))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-fold-range start count g a))
          ("Subgoal *1/2" :use ((:instance fn2-fold-off-footprint (key start))))))
