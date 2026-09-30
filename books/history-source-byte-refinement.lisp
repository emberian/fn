; Proof-only join of the actual tagged resident/cold source controller.
(in-package "ACL2")
(include-book "history-source-byte-cursor")
(include-book "history-cold-record-cursor")
(include-book "history-census-controller")

(defun-nx fn-hsrcb-invariantp (c pool)
  (if (fn-hsrcb-coldp c)
      (fn-hrcur-cold-invariantp (fn-hrcur-field 1 c) pool)
    (fn-hrcur-byte-invariantp c)))
(defun-nx fn-hsrcb-rest (c pool)
  (if (fn-hsrcb-coldp c)
      (fn-hrcur-cold-rest (fn-hrcur-field 1 c) pool)
    (fn-hrcur-byte-rest c)))

(defthm fn-hsrcb-tick-preserves-canonical-residual
  (implies (fn-hsrcb-invariantp c pool)
    (let ((v (mv-nth 0 (fn-hsrcb-tick c)))
          (b (mv-nth 1 (fn-hsrcb-tick c)))
          (next (mv-nth 2 (fn-hsrcb-tick c))))
      (and (fn-hsrcb-invariantp next pool)
           (implies (eq v :emit) (fn-scc-octetp b))
           (equal (fn-hsrcb-rest c pool)
                  (if (eq v :emit) (cons b (fn-hsrcb-rest next pool))
                    (fn-hsrcb-rest next pool)))
           (implies (eq v :prepared) (equal (fn-hsrcb-rest c pool) nil)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((fn-hsrcb-coldp c))
           :use ((:instance fn-hrcur-cold-tick-preserves-current-codec-residual
                           (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-byte-tick-preserves)
                 (:instance fn-hrcur-cold-tick-emits-one-octet (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-byte-tick-refines-residual)
                 (:instance fn-hrcur-byte-prepared-empty))
           :in-theory (e/d (fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick
                            fn-hsrcb-coldp fn-hrcur-field fn-hrcur-widthp)
                           (fn-hrcur-cold-tick fn-hrcur-cold-invariantp fn-hrcur-cold-rest
                            fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-byte-rest)))))

(defthm fn-hsrcb-supply-preserves-canonical-residual
  (implies (and (fn-hsrcb-invariantp c pool)
                (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick c)))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick c))))
                (equal byte (nth position pool)))
    (let ((v (mv-nth 0 (fn-hsrcb-supply c position byte)))
          (b (mv-nth 1 (fn-hsrcb-supply c position byte)))
          (next (mv-nth 2 (fn-hsrcb-supply c position byte))))
      (and (member-eq v '(:continue :emit)) (fn-hsrcb-invariantp next pool)
           (implies (eq v :emit) (fn-scc-octetp b))
           (equal (fn-hsrcb-rest c pool)
                  (if (eq v :emit) (cons b (fn-hsrcb-rest next pool))
                    (fn-hsrcb-rest next pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((fn-hsrcb-coldp c))
           :use ((:instance fn-hrcur-cold-supply-preserves-current-codec-residual
                           (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-byte-tick-preserves)
                 (:instance fn-hrcur-cold-supply-emits-one-octet (c (fn-hrcur-field 1 c))))
           :in-theory (e/d (fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick
                            fn-hsrcb-supply fn-hsrcb-demandp fn-hsrcb-coldp
                            fn-hrcur-field fn-hrcur-widthp)
                           (fn-hrcur-cold-tick fn-hrcur-cold-supply
                            fn-hrcur-cold-invariantp fn-hrcur-cold-rest
                            fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-byte-rest)))))

; This proof state is carried, never reevaluated by a served tick. It unifies
; the old resident length invariant and the current decoded source residual.
(defun-nx fn-hsrcc-total (c pool)
  (+ (nfix (fn-hrcur-field 2 c)) (len (fn-hsrcb-rest (fn-hrcur-field 1 c) pool))))
(defun-nx fn-hsrcc-invariantp (c pool)
  (and (fn-hrcur-widthp c 3)
       (member-eq (fn-hrcur-field 0 c) '(:active :done))
       (fn-hsrcb-invariantp (fn-hrcur-field 1 c) pool)
       (natp (fn-hrcur-field 2 c))
       (< (fn-hsrcc-total c pool) *fn-hrcur-u64-bound*)
       (implies (eq (fn-hrcur-field 0 c) :done)
                (equal (fn-hsrcb-rest (fn-hrcur-field 1 c) pool) nil))))

(defthm fn-hsrcc-tick-preserves-canonical-length
  (implies (fn-hsrcc-invariantp c pool)
    (let ((v (mv-nth 0 (fn-hsrcc-tick c)))
          (n (mv-nth 1 (fn-hsrcc-tick c)))
          (next (mv-nth 2 (fn-hsrcc-tick c))))
      (and (fn-hsrcc-invariantp next pool)
           (equal (fn-hsrcc-total next pool) (fn-hsrcc-total c pool))
           (implies (eq v :prepared) (equal n (fn-hsrcc-total c pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((fn-hsrcb-coldp (fn-hrcur-field 1 c)))
           :use ((:instance fn-hsrcb-tick-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-census-tick-refines-length))
           :in-theory (e/d (fn-hsrcc-invariantp fn-hsrcc-total fn-hsrcc-tick
                            fn-hrcur-census-invariantp fn-hrcur-census-total
                            fn-hsrcb-invariantp fn-hsrcb-rest fn-hrcur-field)
                           (fn-hsrcb-tick fn-hrcur-census-tick fn-hsrcb-coldp
                            fn-hrcur-cold-invariantp fn-hrcur-cold-rest
                            fn-hrcur-byte-invariantp fn-hrcur-byte-rest
                            fn-hrcur-census-tick-refines-length)))))

(defthm fn-hsrcc-supply-preserves-canonical-length
  (implies (and (fn-hsrcc-invariantp c pool)
                (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                (equal byte (nth position pool)))
    (and (equal (mv-nth 0 (fn-hsrcc-supply c position byte))
                (if (eq (fn-hrcur-field 0 c) :active) :continue
                  '(:refused :census-cursor)))
         (fn-hsrcc-invariantp (mv-nth 1 (fn-hsrcc-supply c position byte)) pool)
         (equal (fn-hsrcc-total (mv-nth 1 (fn-hsrcc-supply c position byte)) pool)
                (fn-hsrcc-total c pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hsrcb-supply-preserves-canonical-residual (c (fn-hrcur-field 1 c))))
           :in-theory (e/d (fn-hsrcc-invariantp fn-hsrcc-total fn-hsrcc-supply fn-hrcur-field)
                           (fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-invariantp fn-hsrcb-rest)))))

; The actual producer census boundary now consumes the shared tagged child,
; so the same statement covers resident and authenticated decoded cold rows.
(local
 (defthm fn-hct-tagged-completed-row-with-shape
  (implies (and (fn-hct-shapep c)
                (eq (fn-hrcur-field 0 c) :codec)
                (equal (fn-hrcur-field 2 c) (len h))
                (equal (fn-hrcur-field 3 c) (fn-hp-pes-len h))
                (fn-hsrcc-invariantp (fn-hrcur-field 4 c) pool)
                (equal (fn-hsrcc-total (fn-hrcur-field 4 c) pool) (len (fn-scc-encode ev)))
                (eq (mv-nth 0 (fn-hct-tick c)) :row-done))
    (and (equal (fn-hrcur-field 2 (mv-nth 2 (fn-hct-tick c))) (len (append h (list ev))))
         (equal (fn-hrcur-field 3 (mv-nth 2 (fn-hct-tick c))) (fn-hp-pes-len (append h (list ev))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hsrcc-tick-preserves-canonical-length (c (fn-hrcur-field 4 c)))
                 (:instance fn-hcc-counted-row-preserves-history-census
                   (count (fn-hrcur-field 2 c)) (pool (fn-hrcur-field 3 c))
                   (ordinal (fn-hrcur-field 2 c))
                   (encoded (mv-nth 1 (fn-hsrcc-tick (fn-hrcur-field 4 c))))))
           :in-theory (e/d (fn-hct-tick)
                           (fn-hsrcc-tick fn-hsrcc-invariantp fn-hsrcc-total
                            fn-hcc-counted-row-preserves-history-census
                            fn-hcc-row fn-hp-pes-len fn-scc-encode fn-scc-program
                            fn-scc-encode-is-program len))))))

(defthm fn-hct-tagged-completed-row-refines-history-census
  (implies (and (equal (fn-hrcur-field 2 c) (len h))
                (equal (fn-hrcur-field 3 c) (fn-hp-pes-len h))
                (fn-hsrcc-invariantp (fn-hrcur-field 4 c) pool)
                (equal (fn-hsrcc-total (fn-hrcur-field 4 c) pool) (len (fn-scc-encode ev)))
                (eq (mv-nth 0 (fn-hct-tick c)) :row-done))
    (and (equal (fn-hrcur-field 2 (mv-nth 2 (fn-hct-tick c))) (len (append h (list ev))))
         (equal (fn-hrcur-field 3 (mv-nth 2 (fn-hct-tick c))) (fn-hp-pes-len (append h (list ev))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :use fn-hct-tagged-completed-row-with-shape
           :in-theory (union-theories
                         '(fn-hct-tick fn-hct-shapep member-equal mv-nth car-cons cdr-cons
                           (:e equal) (:e zp) (:e binary-+) (:e consp))
                         (theory 'minimal-theory)))))

(in-theory (disable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcc-total fn-hsrcc-invariantp))
