; fn: the :policy delta applied in quanta is the one-shot application
; (PKT-601 (6), lane config-consumer-catalog-2, 2026-09-27).
;
; books/catalog-delta.lisp defines the committed delta's application twice:
; `fn-cat-apply-delta' (one shot, the reference) and `fn-cat-apply-in-quanta'
; (the resumable run: `fn-cat-apply-delta-step' re-decides at most QUANTUM
; rows of a :policy range per step, `fn-cat-apply-delta-step-bounded'), and
; left their equality OPEN (a ground check in its test book).  A policy
; change touches every row it names, so the view consumes it only in
; bounded steps (D27); this book proves that the steps, under ANY schedule
; of positive quanta, end where the one-shot application does.
;
; KEYSTONE `fn-cfgp-apply-in-quanta-is-apply-delta': for a well-formed delta
; and a starting cursor at or before its range, the resumable run is the
; one-shot application.  Its inductive form
; `fn-cfgp-policy-in-quanta-is-the-range': from any cursor, the run
; re-decides exactly the rows from the later of the cursor and the range's
; start to the range's end (clipped to the count).

(in-package "ACL2")
(include-book "catalog-delta")

(local
 (defthm fn-cfgp-min-facts
   (implies (and (natp a) (natp b))
            (and (natp (min a b)) (<= (min a b) a) (<= (min a b) b)
                 (implies (<= a (min a b)) (equal (min a b) a))
                 (implies (< (min a b) a) (equal (min a b) b))))
   :rule-classes ((:rewrite)
                  (:linear :corollary (implies (and (natp a) (natp b))
                                               (and (<= (min a b) a) (<= (min a b) b)))))))

(local
 (defthm fn-cfgp-max-facts
   (implies (and (natp a) (natp b))
            (and (natp (max a b)) (<= a (max a b)) (<= b (max a b))
                 (implies (<= b a) (equal (max a b) a))
                 (implies (<= a b) (equal (max a b) b))))
   :rule-classes ((:rewrite)
                  (:linear :corollary (implies (and (natp a) (natp b))
                                               (and (<= a (max a b)) (<= b (max a b))))))))

(local
 (defthm fn-cfgp-count-natp
   (natp (fn-cat-count fn-cat))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-cat-count-is-len)))))

; The range split at any point in it is the range (catalog-delta's local
; lemma, restated here).
(defthm fn-cfgp-recontext-range-split
  (implies (and (natp i) (natp m) (natp to) (<= i m) (<= m to))
           (equal (fn-cat-recontext-range m to keyring generation fn-arena
                                          (fn-cat-recontext-range i m keyring generation
                                                                  fn-arena fn-cat))
                  (fn-cat-recontext-range i to keyring generation fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-cat-recontext-range i m keyring generation fn-arena fn-cat))))

(local
 (defthm fn-cfgp-range-empty-at
   (implies (and (natp i) (natp to) (<= to i))
            (equal (fn-cat-recontext-range i to keyring generation fn-arena fn-cat)
                   fn-cat))))

; The inductive form: from any cursor, the rows [max(cursor, from), to').
(defthm fn-cfgp-policy-in-quanta-is-the-range
  (implies (and (equal (car d) :policy)
                (natp cursor) (natp (nth 2 d)) (natp (nth 3 d)))
           (equal (fn-cat-apply-in-quanta d cursor quanta keyring fn-arena fn-cat)
                  (fn-cat-recontext-range (max cursor (nth 2 d))
                                          (min (nth 3 d) (fn-cat-count fn-cat))
                                          keyring (nth 1 d) fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-cat-apply-in-quanta d cursor quanta keyring fn-arena fn-cat)
           :in-theory (e/d (fn-cat-apply-in-quanta)
                           (min max fn-cat-recontext-range fn-cat-count-is-len
                            fn-cat-at-is-nth fn-cat-p-is-rowsp)))
          ("Subgoal *1/1"
           :use ((:instance fn-cfgp-recontext-range-split
                            (i (max cursor (nth 2 d)))
                            (m (min (min (nth 3 d) (fn-cat-count fn-cat))
                                    (+ (max cursor (nth 2 d))
                                       (if (and (consp quanta) (posp (car quanta)))
                                           (car quanta)
                                         1))))
                            (to (min (nth 3 d) (fn-cat-count fn-cat)))
                            (generation (nth 1 d)))))))

; KEYSTONE.  The resumable application from a cursor at or before the
; delta's range, under any schedule of quanta, is the one-shot application.
(defthm fn-cfgp-apply-in-quanta-is-apply-delta
  (implies (and (fn-delta-p d)
                (natp cursor)
                (<= cursor (nfix (nth 2 d))))
           (equal (fn-cat-apply-in-quanta d cursor quanta keyring fn-arena fn-cat)
                  (fn-cat-apply-delta d keyring fn-arena fn-cat)))
  :hints (("Goal"
           :do-not-induct t
           :cases ((equal (car d) :policy))
           :in-theory (e/d (fn-delta-p)
                           (fn-cat-recontext-range fn-cat-count-is-len
                            fn-cat-at-is-nth fn-cat-p-is-rowsp
                            fn-cat-apply-delta-step fn-cat-withdraw
                            fn-cat-redecide fn-dart-p)))
          ("Subgoal 2" :expand ((fn-cat-apply-in-quanta d cursor quanta keyring
                                                        fn-arena fn-cat)))
          ("Subgoal 1" :in-theory (e/d (fn-delta-p fn-cat-apply-delta)
                                       (fn-cat-recontext-range fn-cat-count-is-len
                                        fn-cat-at-is-nth fn-cat-p-is-rowsp
                                        fn-cat-apply-in-quanta min max)))))
