; Copied for fn2 squares E2 from acl2aiguide/examples/transport/fold-contract.lisp
; Source commit: 2283433658784eb4767192508f0e5135a8c939b1
; Original content follows unchanged; all includes resolve inside this copy.
; examples/transport/fold-contract.lisp
;
; What it shows: the relational two-representation contract for a fold and
; its summary (Experiment A of fn's TRANSPORT note, section 4).  Two step
; functions, two observation functions, two admissibility predicates and a
; relation FC-REL between the two state spaces are constrained so that the
; relation holds initially, is preserved by every event, and forces the
; observations to agree.  The generic theorem FC-REL-FOLD is proved once,
; by induction on the event list, from those constraints alone; any concrete
; pair of representations obtains it by :functional-instance, paying only
; for the constraints (:doc encapsulate, :doc functional-instantiation).
;
; The relation is a parameter, not the equality of observations: a
; relation weaker than "closed under every step" cannot be instantiated,
; and read-state-teeth.lisp shows the observation itself is such a
; relation.
;
; Cited by examples/transport/README.md, "Experiment A".

(in-package "ACL2")

(encapsulate
  (((fc1-init) => *)
   ((fc2-init) => *)
   ((fc1-step * *) => *)
   ((fc2-step * *) => *)
   ((fc1-obs * *) => *)
   ((fc2-obs * *) => *)
   ((fc1-ok *) => *)
   ((fc2-ok *) => *)
   ((fc-rel * *) => *))

  ; Witness: both representations are a single constant state.
  (local (defun fc1-init () nil))
  (local (defun fc2-init () nil))
  (local (defun fc1-step (s e) (declare (ignore s e)) nil))
  (local (defun fc2-step (s e) (declare (ignore s e)) nil))
  (local (defun fc1-obs (s q) (declare (ignore s q)) nil))
  (local (defun fc2-obs (s q) (declare (ignore s q)) nil))
  (local (defun fc1-ok (s) (declare (ignore s)) t))
  (local (defun fc2-ok (s) (declare (ignore s)) t))
  (local (defun fc-rel (s1 s2) (declare (ignore s1 s2)) t))

  ; Admissibility of the initial states, and the initial relation.
  (defthm fc-init-ok
    (and (fc1-ok (fc1-init))
         (fc2-ok (fc2-init))))
  (defthm fc-rel-init
    (fc-rel (fc1-init) (fc2-init)))

  ; Every event preserves admissibility on both sides and the relation.
  (defthm fc-rel-step
    (implies (and (fc1-ok s1) (fc2-ok s2) (fc-rel s1 s2))
             (and (fc1-ok (fc1-step s1 e))
                  (fc2-ok (fc2-step s2 e))
                  (fc-rel (fc1-step s1 e) (fc2-step s2 e)))))

  ; Related admissible states answer every query alike.
  (defthm fc-rel-obs
    (implies (and (fc1-ok s1) (fc2-ok s2) (fc-rel s1 s2))
             (equal (fc1-obs s1 q) (fc2-obs s2 q)))))

(defun fc1-fold (s j)
  (if (atom j) s (fc1-fold (fc1-step s (car j)) (cdr j))))

(defun fc2-fold (s j)
  (if (atom j) s (fc2-fold (fc2-step s (car j)) (cdr j))))

(defun fc-fold2-induct (s1 s2 j)
  (if (atom j)
      (list s1 s2)
    (fc-fold2-induct (fc1-step s1 (car j)) (fc2-step s2 (car j)) (cdr j))))

; The constrained functions cannot be evaluated; keep the prover from
; trying (:doc functional-instantiation-example gives the same advice).
(in-theory (disable (:executable-counterpart fc1-fold)
                    (:executable-counterpart fc2-fold)))

(defthm fc-ok-fold
  (implies (and (fc1-ok s1) (fc2-ok s2) (fc-rel s1 s2))
           (and (fc1-ok (fc1-fold s1 j))
                (fc2-ok (fc2-fold s2 j))))
  :hints (("Goal" :induct (fc-fold2-induct s1 s2 j))))

; The generic theorem: the relation survives every suffix.
(defthm fc-rel-fold
  (implies (and (fc1-ok s1) (fc2-ok s2) (fc-rel s1 s2))
           (fc-rel (fc1-fold s1 j) (fc2-fold s2 j)))
  :hints (("Goal" :induct (fc-fold2-induct s1 s2 j))))

; Its corollary: the observations agree after every suffix.
(defthm fc-obs-fold
  (implies (and (fc1-ok s1) (fc2-ok s2) (fc-rel s1 s2))
           (equal (fc1-obs (fc1-fold s1 j) q)
                  (fc2-obs (fc2-fold s2 j) q)))
  :hints (("Goal" :use (fc-rel-fold fc-ok-fold)
                  :in-theory (disable fc-rel-fold fc-ok-fold))))
