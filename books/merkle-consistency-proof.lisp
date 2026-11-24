; Consistency soundness: an accepted RFC 9162 consistency proof, under
; integrity evidence on every opening the trees and the verifier name, makes
; the old leaves a prefix of the new ones.
(in-package "ACL2")
(include-book "merkle")
(include-book "owed-discharge")
(local (include-book "merkle-consistency-run"))

(local (defthm mkc-long-proof
 (implies (and (equal (fn2-mk-phase 0 mk) 0) (posp m) (< m n) (< 61 count))
          (equal (car (fn2-mk-consistency-run 64 m n count d mk)) :proof-length))
 :hints (("Goal" :expand ((fn2-mk-consistency-run 64 m n count d mk))
          :in-theory (e/d (fn2-mk-verify-consistency) (fn2-mk-proof-openings fn2-mk-strip mkc-strip-closed))))))
(local (defthm mkc-subset-append-parts
 (and (subsetp-equal a (append a b c)) (subsetp-equal b (append a b c)) (subsetp-equal c (append a b c)))))
(local (defthm mkc-rows8p-cdr
 (implies (mkc-rows8p p) (and (mkc-rows8p (cdr p)) (implies (consp p) (mk-words8p (car p)))))))
(local (defthm mkc-observation-verify
 (implies (and (posp (len old)) (< (len old) (len new)) (< (len new) 1152921504606846976) (<= (len proof) 61))
          (equal (fn2-mk-consistency-observation old new proof)
                 (mkc-verify (len old) (len new) (mkc-norm proof)
                             (fn-b3-words 8 (fn2-mk-mth old)) (fn-b3-words 8 (fn2-mk-mth new)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use (mkc-observation-run mkc-observation-init
                (:instance mkc-run-top (m (len old)) (n (len new)) (p (mkc-norm proof))
                   (ro (fn-b3-words 8 (fn2-mk-mth old))) (rn (fn-b3-words 8 (fn2-mk-mth new)))
                   (d (mkc-d0 old new proof)) (mk (fn2-mk-table-init 1 (create-fn2-mk)))))
          :in-theory (union-theories (theory 'minimal-theory) '(mkc-norm-len))))))
(local (defthm mkc-long-observation
 (implies (and (posp (len old)) (< (len old) (len new)) (< 61 (len proof)))
          (equal (car (fn2-mk-consistency-observation old new proof)) :proof-length))
 :rule-classes nil
 :hints (("Goal" :use (mkc-observation-run
                       (:instance mkc-long-proof (m (len old)) (n (len new)) (count (len proof))
                          (d (mkc-d0 old new proof)) (mk (fn2-mk-table-init 1 (create-fn2-mk)))))
          :in-theory (e/d (mk-initial-phase) (mkc-observation-run mkc-long-proof fn2-mk-consistency-observation
                           fn2-mk-consistency-run mkc-d0 fn2-mk-table-init))))))
(local (defthm mkc-seed-facts
 (implies (and (posp m) (posp n))
          (and (equal (car (fn2-mk-strip (+ -1 m) (+ -1 n))) (floor (+ -1 m) (expt 2 (mkc-strip-k (+ -1 m)))))
               (equal (mv-nth 1 (fn2-mk-strip (+ -1 m) (+ -1 n))) (floor (+ -1 n) (expt 2 (mkc-strip-k (+ -1 m)))))
               (equal (+ (* (floor (+ -1 m) (expt 2 (mkc-strip-k (+ -1 m)))) (expt 2 (mkc-strip-k (+ -1 m))))
                         (expt 2 (mkc-strip-k (+ -1 m))))
                      m)
               (natp (mkc-strip-k (+ -1 m)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mkc-strip-closed (f (+ -1 m)) (s (+ -1 n)))
                       (:instance mkc-strip-size (f (+ -1 m))))
          :in-theory (disable mkc-strip-closed mkc-strip-size floor expt mkc-strip-k fn2-mk-strip)))))
(local (defthm mkc-verify-sound
 (implies (and (true-listp old) (true-listp new) (posp (len old)) (< (len old) (len new))
               (mkc-rows8p p)
               (equal (car (mkc-verify (len old) (len new) p (fn-b3-words 8 (mkc-hash old)) (fn-b3-words 8 (mkc-hash new)))) :ok)
               (fn2-mk-integrity-openings
                (append (mkc-opens old) (mkc-opens new)
                        (cadr (mkc-verify (len old) (len new) p (fn-b3-words 8 (mkc-hash old)) (fn-b3-words 8 (mkc-hash new)))))))
          (equal old (take (len old) new)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance mkc-seed-facts (m (len old)) (n (len new)))
                (:instance mkc-seed-sound (h (mkc-strip-k (+ -1 (len old))))
                   (f 0) (s (floor (+ -1 (len new)) (expt 2 (mkc-strip-k (+ -1 (len old))))))
                   (rows p) (fr (fn-b3-words 8 (mkc-hash old)))
                   (ro (fn-b3-words 8 (mkc-hash old))) (rn (fn-b3-words 8 (mkc-hash new)))
                   (all (append (mkc-opens old) (mkc-opens new)
                          (cadr (mkc-verify (len old) (len new) p (fn-b3-words 8 (mkc-hash old)) (fn-b3-words 8 (mkc-hash new)))))))
                (:instance mkc-seed-sound (h (mkc-strip-k (+ -1 (len old))))
                   (f (floor (+ -1 (len old)) (expt 2 (mkc-strip-k (+ -1 (len old))))))
                   (s (floor (+ -1 (len new)) (expt 2 (mkc-strip-k (+ -1 (len old))))))
                   (rows (cdr p)) (fr (car p))
                   (ro (fn-b3-words 8 (mkc-hash old))) (rn (fn-b3-words 8 (mkc-hash new)))
                   (all (append (mkc-opens old) (mkc-opens new)
                          (cadr (mkc-verify (len old) (len new) p (fn-b3-words 8 (mkc-hash old)) (fn-b3-words 8 (mkc-hash new))))))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(mkc-verify mkc-hyps mk-leaf-words8p mkc-subset-append-parts mkc-rows8p-cdr
                         natp posp (:type-prescription len) (:type-prescription mkc-strip-k)
                         (:executable-counterpart equal) (:executable-counterpart binary-*)
                         (:executable-counterpart binary-+) unicity-of-0 commutativity-of-*))))))
(local (defthm mkc-hash-is-mth (equal (mkc-hash xs) (fn2-mk-mth xs)) :hints (("Goal" :in-theory (enable mkc-hash fn2-mk-mth)))))
(local (defthm mkc-growing-prefix
 (implies (and (true-list-listp old) (true-list-listp new) (posp (len old)) (< (len old) (len new))
               (< (len new) 1152921504606846976)
               (fn2-mk-consistency-premise old new proof)
               (equal (car (fn2-mk-consistency-observation old new proof)) :ok))
          (equal old (take (len old) new)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :cases ((< 61 (len proof)))
          :use (mkc-observation-verify mkc-long-observation (:instance mkc-verify-sound (p (mkc-norm proof))))
          :in-theory (e/d (fn2-mk-consistency-premise mkc-opens)
                          (fn2-mk-consistency-observation mkc-verify fn2-mk-model fn2-mk-mth
                           fn2-mk-integrity-openings))))))

(defthm fn2-mk-consistency-sound-proved
 (fn2-mk-consistency-sound$owed old new proof)
 :rule-classes nil
 :hints (("Goal" :use (mk-nongrowing-prefix mkc-growing-prefix)
          :in-theory (e/d (fn2-mk-consistency-sound$owed)
                          (fn2-mk-consistency-premise fn2-mk-consistency-observation)))))
(fn2-owed-discharge fn2-mk-consistency-sound fn2-mk-consistency-sound-proved)
