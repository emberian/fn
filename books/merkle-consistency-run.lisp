; The row-backed consistency verifier refines the pure loop: each call of
; fn2-mk-verify-consistency is one loop step, and the trace it records is the
; loop's list of node openings.
; One link of the Merkle proof chain; events are exported.
(in-package "ACL2")
(include-book "merkle-consistency-model")

(defthm mkc-node-rows
 (equal (fn2-digests-rows (fn2-mk-node dst l r d)) (fn2-digests-rows d))
 :hints (("Goal" :in-theory (e/d (fn2-mk-node fn2-mk-node-first fn2-digests-rows)
                                 (fn-b3-compress-core fn2-digest-store-words)))))
(defthm mkc-copy-rows
 (equal (fn2-digests-rows (fn2-digest-copy dst src d)) (fn2-digests-rows d))
 :hints (("Goal" :in-theory (enable fn2-digest-copy fn2-digests-rows))))
(defun-nx mkc-rows-from (k cnt d)
 (declare (xargs :measure (nfix cnt)))
 (if (zp cnt) nil (cons (fn2-digest-list k d) (mkc-rows-from (+ 1 k) (1- cnt) d))))
(defthm mkc-rows-from-node
 (implies (and (natp dst) (natp k) (< dst k))
          (equal (mkc-rows-from k cnt (fn2-mk-node dst l r d)) (mkc-rows-from k cnt d))))
(defthm mkc-rows-from-copy
 (implies (and (natp dst) (natp k) (< dst k))
          (equal (mkc-rows-from k cnt (fn2-digest-copy dst src d)) (mkc-rows-from k cnt d))))
(defun mkc-nth-ind (i k cnt)
 (if (or (zp i) (zp cnt)) (list i k cnt) (mkc-nth-ind (1- i) (1+ k) (1- cnt))))
(defthm mkc-rows-from-nth
 (implies (and (natp i) (< i (nfix cnt)) (natp k))
          (equal (nth i (mkc-rows-from k cnt d)) (fn2-digest-list (+ k i) d)))
 :hints (("Goal" :induct (mkc-nth-ind i k cnt) :in-theory (enable nth) :expand ((mkc-rows-from k cnt d)))))
(defthm mkc-rows-from-len (equal (len (mkc-rows-from k cnt d)) (nfix cnt)) :hints (("Goal" :in-theory (enable len))))
(defun-nx mkc-st (f s i fr sr m n p ro rn d mk)
 (and (equal (fn2-mk-phase 0 mk) 2) (equal (fn2-mk-base 0 mk) 138) (equal (fn2-mk-count 0 mk) (len p))
      (equal (fn2-mk-old 0 mk) m) (equal (fn2-mk-new 0 mk) n) (equal (fn2-mk-index 0 mk) 0)
      (equal (fn2-mk-pf 0 mk) f) (equal (fn2-mk-ps 0 mk) s) (equal (fn2-mk-next 0 mk) i)
      (equal (fn2-digest-list 120 d) sr) (equal (fn2-digest-list 121 d) fr)
      (equal (fn2-digest-list 122 d) ro) (equal (fn2-digest-list 123 d) rn)
      (equal (fn2-digest-list 136 d) ro) (equal (fn2-digest-list 137 d) rn)
      (equal (mkc-rows-from 138 (len p) d) p)
      (equal (fn2-digests-rows d) (+ 138 (len p)))
      (natp f) (natp s) (< f 1152921504606846976) (< s 1152921504606846976)
      (natp i) (<= i (len p))
      (mk-words8p fr) (mk-words8p sr) (mkc-rows8p p)))
(defthm mkc-rows8p-nth
 (implies (and (mkc-rows8p p) (natp i) (< i (len p))) (mk-words8p (nth i p)))
 :hints (("Goal" :in-theory (enable nth len))))
(defthm mkc-rows-window
 (implies (and (equal (mkc-rows-from k cnt d) p) (natp i) (< i (nfix cnt)) (natp k))
          (equal (fn2-digest-list (+ k i) d) (nth i p)))
 :hints (("Goal" :in-theory (disable mkc-rows-from-nth mkc-rows-from)
                 :use ((:instance mkc-rows-from-nth)))))
(defthm mkc-rise-types
 (implies (and (natp f) (natp s))
          (and (integerp (car (fn2-mk-rise f s))) (<= 0 (car (fn2-mk-rise f s)))
               (integerp (mv-nth 1 (fn2-mk-rise f s))) (<= 0 (mv-nth 1 (fn2-mk-rise f s)))))
 :hints (("Goal" :induct (fn2-mk-rise f s) :in-theory (e/d (fn2-mk-rise) (mkc-rise-closed)))))
(defthm mkc-floor-le
 (implies (and (natp x) (posp e)) (<= (floor x e) x))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mkc-floor-bounds (w e))) :nonlinearp t)))
(defthm mkc-rise-le
 (implies (and (natp f) (natp s))
          (and (<= (car (fn2-mk-rise f s)) f) (<= (mv-nth 1 (fn2-mk-rise f s)) s)))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance mkc-floor-le (x f) (e (expt 2 (mkc-rise-k f))))
                       (:instance mkc-floor-le (x s) (e (expt 2 (mkc-rise-k f)))))
          :in-theory (disable floor))))
(defthm mkc-mod-small
 (implies (and (natp x) (< x 1152921504606846976)) (equal (mod x 1152921504606846976) x)))
(defthm mkc-rise-s-type
 (implies (and (natp f) (natp s)) (natp (mv-nth 1 (fn2-mk-rise f s))))
 :rule-classes :type-prescription)
(defthm mkc-rise-f-type
 (implies (and (natp f) (natp s)) (natp (car (fn2-mk-rise f s))))
 :rule-classes :type-prescription)
(defthm mkc-mod-small-zero
 (implies (and (natp x) (< x 1152921504606846976)) (equal (equal (mod x 1152921504606846976) 0) (equal x 0))))
(defthm mkc-rise-nfix
 (implies (and (natp f) (natp s))
          (and (equal (nfix (car (fn2-mk-rise f s))) (car (fn2-mk-rise f s)))
               (equal (nfix (mv-nth 1 (fn2-mk-rise f s))) (mv-nth 1 (fn2-mk-rise f s))))))
(defthm mkc-step-code
 (implies (and (mkc-st f s i fr sr m n p ro rn d mk) (< i (len p)) (not (equal s 0)))
          (equal (car (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk))
                 (let* ((c (nth i p)) (left (mkc-left f s))
                        (sr2 (if left (mk-join c sr) (mk-join sr c)))
                        (fr2 (if left (mk-join c fr) fr)))
                   (mv-let (f2 s2) (if left (fn2-mk-rise f s) (mv f s))
                     (declare (ignore f2))
                     (if (equal (+ 1 i) (len p))
                         (if (and (equal (floor s2 2) 0) (equal sr2 rn) (equal fr2 ro)) :ok :root-mismatch)
                       :more)))))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (mkc-st fn2-mk-verify-consistency fn2-mk-proof-same fn2-mk-proof-step fn2-mk-combine
                           fn2-mk-proof-end mk-parent-canonical)
                          (mkc-rise-closed fn2-mk-rise mk-join mkc-rows-from fn2-mk-node mod mod-zero)))))
(defthm mkc-step-state
 (implies (and (mkc-st f s i fr sr m n p ro rn d mk) (< (+ 1 i) (len p)) (not (equal s 0)))
          (let* ((c (nth i p)) (left (mkc-left f s))
                 (sr2 (if left (mk-join c sr) (mk-join sr c)))
                 (fr2 (if left (mk-join c fr) fr))
                 (res (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk)))
            (mv-let (f2 s2) (if left (fn2-mk-rise f s) (mv f s))
              (mkc-st (floor f2 2) (floor s2 2) (+ 1 i) fr2 sr2 m n p ro rn (mv-nth 1 res) (mv-nth 2 res)))))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (mkc-st fn2-mk-verify-consistency fn2-mk-proof-same fn2-mk-proof-step fn2-mk-combine
                           mk-parent-canonical)
                          (mkc-rise-closed fn2-mk-rise mk-join mkc-rows-from fn2-mk-node mod mod-zero)))))
(defthm mkc-step-openings
 (implies (and (mkc-st f s i fr sr m n p ro rn d mk) (< i (len p)) (not (equal s 0)))
          (equal (fn2-mk-proof-openings d mk)
                 (let* ((pp (fn-b3-words-octets (nth i p))) (r (fn-b3-words-octets sr)) (o (fn-b3-words-octets fr)))
                   (if (mkc-left f s) (list (cons 1 (append pp r)) (cons 1 (append pp o)))
                     (list (cons 1 (append r pp)))))))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (mkc-st fn2-mk-proof-openings) (mkc-rows-from)))))
(defthm mkc-zero-s-code
 (implies (and (mkc-st f s i fr sr m n p ro rn d mk) (< i (len p)) (equal s 0))
          (and (equal (car (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk)) :proof-length)
               (equal (fn2-mk-proof-openings d mk) nil)))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (mkc-st fn2-mk-verify-consistency fn2-mk-proof-same fn2-mk-proof-step fn2-mk-refuse
                           fn2-mk-proof-openings)
                          (mkc-rise-closed fn2-mk-rise mk-join mkc-rows-from fn2-mk-node)))))
(defthm mkc-end-code
 (implies (and (mkc-st f s i fr sr m n p ro rn d mk) (equal i (len p)))
          (and (equal (car (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk))
                      (if (and (equal s 0) (equal sr rn) (equal fr ro)) :ok :root-mismatch))
               (equal (fn2-mk-proof-openings d mk) nil)))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (mkc-st fn2-mk-verify-consistency fn2-mk-proof-same fn2-mk-proof-step fn2-mk-proof-end
                           fn2-mk-proof-openings)
                          (mkc-rise-closed fn2-mk-rise mk-join mkc-rows-from fn2-mk-node)))))
(defthm mkc-step-state-left
 (implies (and (mkc-st f s i fr sr m n p ro rn d mk) (< (+ 1 i) (len p)) (not (equal s 0)) (mkc-left f s))
          (mkc-st (floor (car (fn2-mk-rise f s)) 2) (floor (mv-nth 1 (fn2-mk-rise f s)) 2) (+ 1 i)
                  (mk-join (nth i p) fr) (mk-join (nth i p) sr) m n p ro rn
                  (mv-nth 1 (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk))
                  (mv-nth 2 (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk))))
 :hints (("Goal" :use mkc-step-state :in-theory (disable mkc-step-state mkc-st fn2-mk-verify-consistency
                                                          mkc-rise-closed fn2-mk-rise mk-join))))
(defthm mkc-step-state-right
 (implies (and (mkc-st f s i fr sr m n p ro rn d mk) (< (+ 1 i) (len p)) (not (equal s 0)) (not (mkc-left f s)))
          (mkc-st (floor f 2) (floor s 2) (+ 1 i) fr (mk-join sr (nth i p)) m n p ro rn
                  (mv-nth 1 (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk))
                  (mv-nth 2 (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk))))
 :hints (("Goal" :use mkc-step-state :in-theory (disable mkc-step-state mkc-st fn2-mk-verify-consistency
                                                          mkc-rise-closed fn2-mk-rise mk-join))))
(defun-nx mkc-run-ind (fuel f s i fr sr m n p d mk)
 (declare (xargs :measure (nfix fuel)))
 (if (or (zp fuel) (not (natp i)) (<= (len p) i) (equal s 0)) (list f s i fr sr d mk)
  (let* ((c (nth i p)) (left (mkc-left f s))
         (sr2 (if left (mk-join c sr) (mk-join sr c)))
         (fr2 (if left (mk-join c fr) fr))
         (res (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk)))
    (mv-let (f2 s2) (if left (fn2-mk-rise f s) (mv f s))
      (mkc-run-ind (1- fuel) (floor f2 2) (floor s2 2) (+ 1 i) fr2 sr2 m n p (mv-nth 1 res) (mv-nth 2 res))))))
(defthm mkc-nthcdr-shape
 (implies (and (natp i) (< i (len p)))
          (and (consp (nthcdr i p)) (equal (car (nthcdr i p)) (nth i p))
               (equal (cdr (nthcdr i p)) (nthcdr (+ 1 i) p))))
 :hints (("Goal" :in-theory (enable nth nthcdr len))))
(defthm mkc-nthcdr-end
 (implies (and (natp i) (<= (len p) i)) (not (consp (nthcdr i p))))
 :hints (("Goal" :in-theory (enable nthcdr len))))
(defthm mkc-st-facts
 (implies (mkc-st f s i fr sr m n p ro rn d mk)
          (and (natp i) (<= i (len p)) (natp f) (natp s)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable mkc-st))))
(defthm mkc-run-loop
 (implies (and (mkc-st f s i fr sr m n p ro rn d mk) (natp fuel) (< (- (len p) i) fuel))
          (equal (list (car (fn2-mk-consistency-run fuel m n (len p) d mk))
                       (mv-nth 1 (fn2-mk-consistency-run fuel m n (len p) d mk)))
                 (mkc-loop f s (nthcdr i p) fr sr ro rn)))
 :hints (("Goal" :induct (mkc-run-ind fuel f s i fr sr m n p d mk)
          :expand ((fn2-mk-consistency-run fuel m n (len p) d mk)
                   (mkc-loop f s (nthcdr i p) fr sr ro rn))
          :in-theory (disable mkc-st fn2-mk-verify-consistency fn2-mk-proof-openings mkc-rise-closed fn2-mk-rise
                              mk-join mkc-left mkc-step-state))
         ("Subgoal *1/1" :cases ((< i (len p))))))
(defun mkc-norm (proof)
 (if (atom proof) nil (cons (fn2-mk-proof-row (car proof)) (mkc-norm (cdr proof)))))
(defthm mkc-proof-row-words8p
 (mk-words8p (fn2-mk-proof-row r))
 :hints (("Goal" :in-theory (e/d (mk-words8p fn-b3-word-listp len) (nth)))))
(in-theory (disable fn2-mk-proof-row))
(defthm mkc-norm-rows8p (mkc-rows8p (mkc-norm proof)))
(defthm mkc-norm-len (equal (len (mkc-norm proof)) (len proof)) :hints (("Goal" :in-theory (enable len))))
(defthm mkc-load-rows
 (equal (fn2-digests-rows (fn2-digest-load dst w d)) (fn2-digests-rows d))
 :hints (("Goal" :in-theory (enable fn2-digest-load fn2-digests-rows))))
(defthm mkc-load-proof-rows
 (equal (fn2-digests-rows (fn2-mk-load-proof proof at d)) (fn2-digests-rows d))
 :hints (("Goal" :induct (fn2-mk-load-proof proof at d))))
(defthm mkc-load-proof-window
 (implies (natp at)
          (equal (mkc-rows-from at (len proof) (fn2-mk-load-proof proof at d)) (mkc-norm proof)))
 :hints (("Goal" :induct (fn2-mk-load-proof proof at d) :in-theory (enable len))
         ("Subgoal *1/1" :expand ((mkc-rows-from at (+ 1 (len (cdr proof))) (fn2-mk-load-proof proof at d))))))
(defthm mkc-init-rows
 (equal (fn2-digests-rows (fn2-digests-init n d)) n)
 :hints (("Goal" :in-theory (enable fn2-digests-init fn2-digests-rows))))
(defun-nx mkc-init-p (m n p ro rn d mk)
 (and (equal (fn2-mk-phase 0 mk) 0) (equal (fn2-mk-rows mk) 1)
      (equal (fn2-digest-list 136 d) ro) (equal (fn2-digest-list 137 d) rn)
      (equal (mkc-rows-from 138 (len p) d) p)
      (equal (fn2-digests-rows d) (+ 138 (len p)))
      (mk-words8p ro) (mkc-rows8p p)
      (posp m) (natp n) (< m n) (< n 1152921504606846976)))
(defthm mkc-strip-types
 (implies (and (natp f) (natp s))
          (and (integerp (car (fn2-mk-strip f s))) (<= 0 (car (fn2-mk-strip f s)))
               (integerp (mv-nth 1 (fn2-mk-strip f s))) (<= 0 (mv-nth 1 (fn2-mk-strip f s)))))
 :hints (("Goal" :induct (fn2-mk-strip f s) :in-theory (e/d (fn2-mk-strip) (mkc-strip-closed)))))
(defthm mkc-strip-le
 (implies (and (natp f) (natp s))
          (and (<= (car (fn2-mk-strip f s)) f) (<= (mv-nth 1 (fn2-mk-strip f s)) s)))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance mkc-floor-le (x f) (e (expt 2 (mkc-strip-k f))))
                       (:instance mkc-floor-le (x s) (e (expt 2 (mkc-strip-k f)))))
          :in-theory (disable floor))))
(defthm mkc-strip-nfix
 (implies (and (natp f) (natp s))
          (and (equal (nfix (car (fn2-mk-strip f s))) (car (fn2-mk-strip f s)))
               (equal (nfix (mv-nth 1 (fn2-mk-strip f s))) (mv-nth 1 (fn2-mk-strip f s))))))
(defthm mkc-setup-openings
 (implies (equal (fn2-mk-phase 0 mk) 0) (equal (fn2-mk-proof-openings d mk) nil))
 :hints (("Goal" :in-theory (enable fn2-mk-proof-openings))))
(defthm mkc-setup-zero
 (implies (and (mkc-init-p m n p ro rn d mk) (<= (len p) 61)
               (equal (car (fn2-mk-strip (+ -1 m) (+ -1 n))) 0))
          (let ((v (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk)))
            (and (equal (car v) :more)
                 (mkc-st 0 (mv-nth 1 (fn2-mk-strip (+ -1 m) (+ -1 n))) 0 ro ro m n p ro rn
                         (mv-nth 1 v) (mv-nth 2 v)))))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (mkc-init-p mkc-st fn2-mk-verify-consistency fn2-mk-proof-setup)
                          (mkc-strip-closed fn2-mk-strip mkc-rows-from mod mod-zero)))))
(defthm mkc-setup-seed
 (implies (and (mkc-init-p m n p ro rn d mk) (<= (len p) 61) (consp p)
               (not (equal (car (fn2-mk-strip (+ -1 m) (+ -1 n))) 0)))
          (let ((v (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk)))
            (and (equal (car v) :more)
                 (mkc-st (car (fn2-mk-strip (+ -1 m) (+ -1 n))) (mv-nth 1 (fn2-mk-strip (+ -1 m) (+ -1 n)))
                         1 (car p) (car p) m n p ro rn (mv-nth 1 v) (mv-nth 2 v)))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance mkc-rows-window (k 138) (cnt (len p)) (i 0)))
          :in-theory (e/d (mkc-init-p mkc-st fn2-mk-verify-consistency fn2-mk-proof-setup fn2-mk-refuse)
                          (mkc-strip-closed fn2-mk-strip mkc-rows-from mod mod-zero mkc-rows-window)))))
(defthm mkc-setup-empty
 (implies (and (mkc-init-p m n p ro rn d mk) (not (consp p))
               (not (equal (car (fn2-mk-strip (+ -1 m) (+ -1 n))) 0)))
          (equal (car (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk)) :proof-length))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (mkc-init-p fn2-mk-verify-consistency fn2-mk-proof-setup fn2-mk-refuse)
                          (mkc-strip-closed fn2-mk-strip mkc-rows-from mod mod-zero)))))
(defun-nx mkc-verify (m n p ro rn)
 (let ((f (car (fn2-mk-strip (+ -1 m) (+ -1 n)))) (s (mv-nth 1 (fn2-mk-strip (+ -1 m) (+ -1 n)))))
   (cond ((equal f 0) (mkc-loop 0 s p ro ro ro rn))
         ((atom p) (list :proof-length nil))
         (t (mkc-loop f s (cdr p) (car p) (car p) ro rn)))))
(defthm mkc-run-top
 (implies (and (mkc-init-p m n p ro rn d mk) (<= (len p) 61))
          (equal (list (car (fn2-mk-consistency-run 64 m n (len p) d mk))
                       (mv-nth 1 (fn2-mk-consistency-run 64 m n (len p) d mk)))
                 (mkc-verify m n p ro rn)))
 :hints (("Goal" :do-not-induct t
          :expand ((:free (c) (fn2-mk-consistency-run 64 m n c d mk)))
          :use (mkc-setup-zero mkc-setup-seed mkc-setup-empty
                (:instance mkc-run-loop (fuel 63) (f 0) (s (mv-nth 1 (fn2-mk-strip (+ -1 m) (+ -1 n)))) (i 0)
                   (fr ro) (sr ro)
                   (d (mv-nth 1 (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk)))
                   (mk (mv-nth 2 (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk))))
                (:instance mkc-run-loop (fuel 63) (f (car (fn2-mk-strip (+ -1 m) (+ -1 n))))
                   (s (mv-nth 1 (fn2-mk-strip (+ -1 m) (+ -1 n)))) (i 1)
                   (fr (car p)) (sr (car p))
                   (d (mv-nth 1 (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk)))
                   (mk (mv-nth 2 (fn2-mk-verify-consistency 0 m n 138 (len p) 136 137 d mk)))))
          :in-theory (e/d (mkc-verify mkc-init-p)
                          (mkc-setup-zero mkc-setup-seed mkc-setup-empty mkc-run-loop mkc-st
                           fn2-mk-verify-consistency fn2-mk-consistency-run mkc-loop
                           mkc-strip-closed fn2-mk-strip)))))
(defthm mkc-table-rows
 (equal (fn2-mk-rows (fn2-mk-table-init 1 (create-fn2-mk))) 1)
 :hints (("Goal" :in-theory (enable fn2-mk-table-init fn2-mk-rows create-fn2-mk))))
(defun-nx mkc-d0 (old new proof)
 (fn2-mk-load-proof proof 138
  (fn2-digest-load 137 (fn-b3-words 8 (fn2-mk-mth new))
   (fn2-digest-load 136 (fn-b3-words 8 (fn2-mk-mth old))
    (fn2-digests-init (+ 138 (len proof)) (create-fn2-digests))))))
(defthm mkc-observation-run
 (equal (fn2-mk-consistency-observation old new proof)
        (list (car (fn2-mk-consistency-run 64 (len old) (len new) (len proof) (mkc-d0 old new proof)
                                           (fn2-mk-table-init 1 (create-fn2-mk))))
              (mv-nth 1 (fn2-mk-consistency-run 64 (len old) (len new) (len proof) (mkc-d0 old new proof)
                                           (fn2-mk-table-init 1 (create-fn2-mk))))))
 :hints (("Goal" :in-theory (e/d (mkc-d0) (fn2-mk-mth fn2-mk-consistency-run fn2-mk-load-proof
                                           fn2-mk-table-init fn2-digests-init)))))
(defthm mkc-observation-init
 (implies (and (posp (len old)) (< (len old) (len new)) (< (len new) 1152921504606846976))
          (mkc-init-p (len old) (len new) (mkc-norm proof) (fn-b3-words 8 (fn2-mk-mth old))
                      (fn-b3-words 8 (fn2-mk-mth new)) (mkc-d0 old new proof)
                      (fn2-mk-table-init 1 (create-fn2-mk))))
 :hints (("Goal" :in-theory (e/d (mkc-init-p mkc-d0 mk-leaf-words8p)
                                 (fn2-mk-mth fn2-mk-load-proof fn2-mk-table-init fn2-digests-init mkc-rows-from)))))
