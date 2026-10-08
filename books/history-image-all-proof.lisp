; Composition of buffered row writes with the canonical placed-image model.
(in-package "ACL2")
(include-book "history-image-row-proof")
(include-book "history-image-model-step")
(include-book "history-pages-append-grown")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-his-pes-len-append
 (equal (fn-hp-pes-len (append a b)) (+ (fn-hp-pes-len a) (fn-hp-pes-len b)))
 :hints (("Goal" :induct (fn-hp-pes-len a)
          :in-theory (e/d (fn-hp-pes-len) (fn-hp-pe fn-hp-pe-is-pad8)))))

(defthm fn-his-lens-append
 (equal (fn-hp-lens (append a b) salt) (fn-hp-x-add (fn-hp-lens a salt) (fn-hp-lens b salt)))
 :hints (("Goal" :in-theory (e/d (fn-hp-x-add) (fn-hp-lens fn-hp-pes-len)))))

(defthm fn-his-lens-aligned
 (fn-hp-x-aligned (fn-hp-lens h salt))
 :hints (("Goal" :use fn-hp-pes-len-mod-8
          :in-theory (e/d (fn-hp-x-aligned) (fn-hp-lens fn-hp-pes-len mod)))))

(defthm fn-his-deltas-aligned
 (fn-hp-deltas-aligned (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))
 :hints (("Goal" :do-not-induct t
          :use (fn-his-lens-aligned
                (:instance fn-hp-deltas-aligned-from-checks
                  (regs (fn-hp-regs h salt)) (ds (fn-hp-ds ev salt (fn-hp-pes-len h)))))
          :in-theory (e/d (fn-hp-lens)
                          (fn-his-lens-aligned fn-his-canonical-lens fn-hp-regs fn-hp-ds
                           fn-hp-deltas-aligned fn-hp-x-aligned fn-hp-deltas-aligned-from-checks
                           fn-hp-pe fn-hp-pe-is-pad8 adt-lens)))))

(local
 (defun-nx fn-his-place-content-ind (h seen salt pw starts np mem)
  (declare (xargs :guard (true-listp seen) :verify-guards t))
  (if (atom h) (list seen pw mem)
   (mv-let (v pw2 mem2) (ec-call (fn-his-place-row (car h) salt pw starts np mem))
    (if (eq v :ok)
        (fn-his-place-content-ind (cdr h) (append seen (list (car h))) salt pw2 starts np mem2)
      (list seen pw mem))))))

(defthm fn-his-place-row-extends-prefix
 (implies
  (and (fn-his-pwp pw) (fn-hp-evp ev) (equal (cadr pw) (fn-hp-lens seen salt))
       (fn-his-cursors-at (caddr pw) (cadr pw))
       (nat-listp starts) (equal (len starts) 5) (natp np)
       (true-listp hdr) (equal (len hdr) 2048)
       (unsigned-byte-p 64 (nth 4 (cadr pw)))
       (unsigned-byte-p 64 (len (fn-hp-pe ev)))
       (adt-placement-ok starts (fn-hp-x-add (cadr pw) (list 8 8 8 8 (len (fn-hp-pe ev)))) np)
       (equal (pgs-w-length pgs-mem) (* 2048 np)) (equal (pgs-d-length pgs-mem) np)
       (equal (nth *pgs-wi* (fn-his-rcs-flush-write (caddr pw) starts pgs-mem))
              (fn-hp-rep (fn-hp-piw seen salt starts np) 0 hdr)))
  (let ((res (fn-his-place-row ev salt pw starts np pgs-mem)))
   (equal (nth *pgs-wi* (fn-his-rcs-flush-write (caddr (mv-nth 1 res)) starts (mv-nth 2 res)))
          (fn-hp-rep (fn-hp-piw (append seen (list ev)) salt starts np) 0 hdr))))
 :hints (("Goal" :do-not-induct t
          :use (fn-his-place-row-appends-words
                (:instance fn-hp-lens-4 (h seen))
                (:instance fn-his-piw-append-fixed-header (h seen)))
          :in-theory (disable fn-his-pwp fn-hp-evp fn-his-cursors-at fn-hp-x-add fn-hp-lens fn-his-canonical-lens
                              fn-hp-pe fn-hp-pe-is-pad8 fn-hp-piw fn-hp-rep fn-hp-wreps
                              fn-hp-bb-list fn-hp-ds-words fn-hp-ds fn-hp-pes-len
                              fn-his-rcs-flush-write fn-his-place-row adt-placement-ok
                              fn-hp-deltas-aligned fn-hp-regs nth adt-nth-1+
                              fn-hp-lens-4 fn-hp-ds-words-of-ds fn-hp-mkey fn-hp-pack8
                              fn-scc-encode fn-scc-encode-is-program floor mod)))
 :rule-classes nil)

(local
 (defthm fn-his-content-pwp-fields
  (implies (fn-his-pwp pw)
           (and (natp (car pw)) (nat-listp (cadr pw)) (equal (len (cadr pw)) 5)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-his-pwp)))))

(defthm fn-his-place-all-extends-prefix
 (implies
  (and (true-listp seen) (fn-hp-events-okp h) (fn-his-pwp pw)
       (equal (cadr pw) (fn-hp-lens seen salt))
       (fn-his-cursors-at (caddr pw) (cadr pw))
       (nat-listp starts) (equal (len starts) 5) (natp np)
       (true-listp hdr) (equal (len hdr) 2048)
       (fn-hp-u64-listp (fn-hp-x-add (cadr pw) (fn-hp-lens h salt)))
       (adt-placement-ok starts (fn-hp-x-add (cadr pw) (fn-hp-lens h salt)) np)
       (equal (pgs-w-length pgs-mem) (* 2048 np)) (equal (pgs-d-length pgs-mem) np)
       (equal (nth *pgs-wi* (fn-his-rcs-flush-write (caddr pw) starts pgs-mem))
              (fn-hp-rep (fn-hp-piw seen salt starts np) 0 hdr)))
  (let ((res (fn-his-place-all h salt pw starts np pgs-mem)))
   (equal (nth *pgs-wi* (fn-his-rcs-flush-write (caddr (mv-nth 1 res)) starts (mv-nth 2 res)))
          (fn-hp-rep (fn-hp-piw (append seen h) salt starts np) 0 hdr))))
 :hints (("Goal" :induct (fn-his-place-content-ind h seen salt pw starts np pgs-mem)
          :in-theory (disable fn-his-place-row fn-his-pwp fn-his-cursors-at fn-hp-x-add fn-hp-lens
                              fn-his-canonical-lens fn-hp-evp fn-hp-pe fn-hp-pe-is-pad8
                              fn-hp-u64-listp adt-placement-ok fn-hp-pes-len
                              fn-hp-piw fn-hp-rep fn-his-rcs-flush-write nth adt-nth-1+
                              fn-his-place-row-accepts-planned fn-his-place-row-accepts-fitting-cursors
                              fn-his-place-all-accepts-planned
                              fn-hp-piw-caps-extend fn-hp-regs fn-hp-hdr2 fn-hp-wreps
                              adt-zeros (:e adt-zeros) fn-his-lens-append))
         ("Subgoal *1/3" :use fn-his-place-row-accepts-planned)
         ("Subgoal *1/2"
          :use ((:instance fn-his-place-row-accepts-planned)
                (:instance fn-his-place-row-extends-prefix (ev (car h)))
                (:instance fn-his-place-row-preserves-cursors-at (ev (car h)))
                (:instance fn-his-planned-row-word-fields (lens (cadr pw)))
                (:instance fn-his-planned-row-placement (lens (cadr pw)))
                (:instance fn-his-remaining-lengths-step (lens (cadr pw)))))))
