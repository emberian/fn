; RFC 9162 consistency proofs over the recursive tree model: tree
; decomposition at powers of two, subtree binding under integrity evidence,
; and the backward invariant of the verifier's loop as a pure function.
; One link of the Merkle proof chain; events are exported.
(in-package "ACL2")
(include-book "merkle-owed-proof")
(defun mkc-split-ind (h n)
 (if (zp h) (list h n) (mkc-split-ind (1- h) (ceiling n 2))))
(defthm mkc-half-in-range
 (implies (and (natp n) (posp e) (< (* 2 e) n) (<= n (* 4 e)))
          (and (< e (ceiling n 2)) (<= (ceiling n 2) (* 2 e))))
 :rule-classes nil)
(defthm mkc-split-step
 (implies (and (natp n) (posp e) (< (* 2 e) n) (<= n (* 4 e))
               (equal (fn2-mk-split (ceiling n 2)) e))
          (equal (fn2-mk-split n) (* 2 e)))
 :hints (("Goal" :expand ((fn2-mk-split n))))
 :rule-classes nil)
(defthm mkc-expt-step
 (implies (posp h) (equal (expt 2 h) (* 2 (expt 2 (+ -1 h)))))
 :hints (("Goal" :expand ((expt 2 h))))
 :rule-classes nil)
(defthm mkc-ceiling-natp (implies (natp n) (natp (ceiling n 2))) :rule-classes nil)
(defthm mkc-split-at-power
 (implies (and (natp h) (natp n) (< (expt 2 h) n) (<= n (* 2 (expt 2 h))))
          (equal (fn2-mk-split n) (expt 2 h)))
 :hints (("Goal" :induct (mkc-split-ind h n)
          :in-theory (union-theories (theory 'minimal-theory)
                       '(mkc-split-ind natp posp zp (:type-prescription expt-type-prescription-integerp-base)
                          (:type-prescription expt-type-prescription-positive-base)
                         (:type-prescription ceiling) (:type-prescription fn2-mk-split))))
         ("Subgoal *1/2" :use (mkc-expt-step
                 (:instance mkc-half-in-range (e (expt 2 (1- h))))
                 (:instance mkc-split-step (e (expt 2 (1- h))))
                 (:instance mkc-ceiling-natp)))
         ("Subgoal *1/1" :in-theory (enable fn2-mk-split (:executable-counterpart expt) (:executable-counterpart fn2-mk-split)))))
(defun mkc-fuel-ind (xs f1 f2)
 (declare (xargs :measure (nfix f1)))
 (cond ((or (zp f1) (zp f2) (atom xs) (atom (cdr xs))) (list xs f1 f2))
       (t (let ((k (fn2-mk-split (len xs))))
            (list (mkc-fuel-ind (take k xs) (1- f1) (1- f2))
                  (mkc-fuel-ind (nthcdr k xs) (1- f1) (1- f2)))))))
(defthm mkc-model-fuels
 (implies (and (natp f1) (natp f2) (<= (len xs) f1) (<= (len xs) f2))
          (equal (fn2-mk-model xs f1) (fn2-mk-model xs f2)))
 :rule-classes nil
 :hints (("Goal" :induct (mkc-fuel-ind xs f1 f2)
          :in-theory (disable fn-blake3-of-octets fn-blake3 take nthcdr)
          :expand ((fn2-mk-model xs f1) (fn2-mk-model xs f2)))))
(defun-nx mkc-hash (xs) (car (fn2-mk-model xs (len xs))))
(defun-nx mkc-opens (xs) (cadr (fn2-mk-model xs (len xs))))
(defun-nx mkc-top (xs w) (cons 1 (append (mkc-hash (take w xs)) (mkc-hash (nthcdr w xs)))))
(defthm mkc-two-or-more
 (implies (and (natp h) (< (expt 2 h) (len xs))) (and (consp xs) (consp (cdr xs))))
 :rule-classes nil
 :hints (("Goal" :expand ((len xs) (len (cdr xs))))))
(defthm mkc-split-model
 (implies (and (natp h) (< (expt 2 h) (len xs)) (<= (len xs) (* 2 (expt 2 h))))
          (and (equal (mkc-hash xs) (fn-blake3 (mkc-top xs (expt 2 h))))
               (equal (mkc-opens xs)
                      (cons (mkc-top xs (expt 2 h))
                            (append (mkc-opens (take (expt 2 h) xs))
                                    (mkc-opens (nthcdr (expt 2 h) xs)))))))
 :rule-classes nil
 :hints (("Goal" :use (mkc-two-or-more (:instance mkc-split-at-power (n (len xs)))
                       (:instance mkc-model-fuels (xs (take (expt 2 h) xs)) (f1 (+ -1 (len xs))) (f2 (expt 2 h)))
                       (:instance mkc-model-fuels (xs (nthcdr (expt 2 h) xs)) (f1 (+ -1 (len xs))) (f2 (- (len xs) (expt 2 h)))))
          :expand ((fn2-mk-model xs (len xs)))
          :in-theory (disable fn-blake3-of-octets fn-blake3 fn2-mk-split))))
(defthm mkc-octets-shape
 (and (true-listp (fn-b3-words-octets ws))
      (equal (len (fn-b3-words-octets ws)) (* 4 (len ws))))
 :hints (("Goal" :in-theory (enable fn-b3-words-octets))))
(defthm mkc-hash-shape
 (and (true-listp (mkc-hash xs)) (equal (len (mkc-hash xs)) 32))
 :hints (("Goal" :in-theory (enable mkc-hash))))
(defthm mkc-words8-of-octets
 (implies (mk-words8p u) (equal (fn-b3-words 8 (fn-b3-words-octets u)) u))
 :hints (("Goal" :in-theory (enable mk-words8p))))
(defthm mkc-top-member
 (implies (and (natp h) (< (expt 2 h) (len xs)) (<= (len xs) (* 2 (expt 2 h)))
               (subsetp-equal (mkc-opens xs) all))
          (and (member-equal (mkc-top xs (expt 2 h)) all)
               (subsetp-equal (mkc-opens (take (expt 2 h) xs)) all)
               (subsetp-equal (mkc-opens (nthcdr (expt 2 h) xs)) all)))
 :rule-classes nil
 :hints (("Goal" :use mkc-split-model :in-theory (disable mkc-top mkc-opens))))
(defthm mkc-join-hash
 (equal (fn-b3-words-octets (mk-join u v))
        (fn-blake3 (cons 1 (append (fn-b3-words-octets u) (fn-b3-words-octets v)))))
 :hints (("Goal" :in-theory (enable mk-join))))
(defthm mkc-child-hash
 (implies (and (natp h) (< (expt 2 h) (len xs)) (<= (len xs) (* 2 (expt 2 h)))
               (equal (mk-join u v) (fn-b3-words 8 (mkc-hash xs))))
          (equal (fn-blake3 (cons 1 (append (fn-b3-words-octets u) (fn-b3-words-octets v))))
                 (fn-blake3 (mkc-top xs (expt 2 h)))))
 :rule-classes nil
 :hints (("Goal" :use (mkc-split-model mkc-join-hash
                       (:instance mk-digest-round-trip (msg (mkc-top xs (expt 2 h)))))
          :in-theory (union-theories (theory 'minimal-theory) '()))))
(defthm mkc-child-opening
 (implies (and (natp h) (< (expt 2 h) (len xs)) (<= (len xs) (* 2 (expt 2 h)))
               (fn2-mk-integrity-openings all)
               (subsetp-equal (mkc-opens xs) all)
               (member-equal (cons 1 (append (fn-b3-words-octets u) (fn-b3-words-octets v))) all)
               (equal (mk-join u v) (fn-b3-words 8 (mkc-hash xs))))
          (equal (cons 1 (append (fn-b3-words-octets u) (fn-b3-words-octets v)))
                 (mkc-top xs (expt 2 h))))
 :rule-classes nil
 :hints (("Goal" :use (mkc-child-hash mkc-top-member
                       (:instance mk-opening-injective
                         (x (cons 1 (append (fn-b3-words-octets u) (fn-b3-words-octets v))))
                         (y (mkc-top xs (expt 2 h)))))
          :in-theory (union-theories (theory 'minimal-theory) '()))))
(defthm mkc-child
 (implies (and (natp h) (< (expt 2 h) (len xs)) (<= (len xs) (* 2 (expt 2 h)))
               (fn2-mk-integrity-openings all)
               (subsetp-equal (mkc-opens xs) all)
               (member-equal (cons 1 (append (fn-b3-words-octets u) (fn-b3-words-octets v))) all)
               (mk-words8p u) (mk-words8p v)
               (equal (mk-join u v) (fn-b3-words 8 (mkc-hash xs))))
          (and (equal u (fn-b3-words 8 (mkc-hash (take (expt 2 h) xs))))
               (equal v (fn-b3-words 8 (mkc-hash (nthcdr (expt 2 h) xs))))
               (subsetp-equal (mkc-opens (take (expt 2 h) xs)) all)
               (subsetp-equal (mkc-opens (nthcdr (expt 2 h) xs)) all)))
 :rule-classes nil
 :hints (("Goal" :use (mkc-top-member mkc-child-opening
                       (:instance mk-split-digest-pair
                          (x (fn-b3-words-octets u)) (y (fn-b3-words-octets v))
                          (u (mkc-hash (take (expt 2 h) xs))) (v (mkc-hash (nthcdr (expt 2 h) xs)))))
          :in-theory (e/d (mkc-top mk-words8p) (mkc-hash mkc-opens fn-blake3 fn-blake3-of-octets mk-join
                     fn2-mk-integrity-openings subsetp-equal member-equal)))))
(defthm mkc-bind
 (implies (and (true-listp xs) (true-listp ys) (equal (len xs) (len ys))
               (fn2-mk-integrity-openings all)
               (subsetp-equal (mkc-opens xs) all) (subsetp-equal (mkc-opens ys) all)
               (equal (fn-b3-words 8 (mkc-hash xs)) (fn-b3-words 8 (mkc-hash ys))))
          (equal xs ys))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mk-equal-packed-roots (fuel (len xs)))
                       (:instance mk-tree-binding (fuel (len xs))))
          :in-theory (e/d (mk-matchp mkc-hash mkc-opens) (fn2-mk-model fn2-mk-integrity-openings)))))
(defun mkc-kn-ind (k n l)
 (if (or (zp k) (zp n)) (list k n l) (mkc-kn-ind (1- k) (1- n) (cdr l))))
(defthm mkc-nthcdr-take
 (implies (and (natp k) (natp n) (<= k n))
          (equal (nthcdr k (take n l)) (take (- n k) (nthcdr k l))))
 :hints (("Goal" :induct (mkc-kn-ind k n l) :in-theory (enable take nthcdr))))
(defthm mkc-take-take
 (implies (and (natp k) (natp n) (<= k n))
          (equal (take k (take n l)) (take k l)))
 :hints (("Goal" :induct (mkc-kn-ind k n l) :in-theory (enable take nthcdr))))
(defthm mkc-take-split
 (implies (and (natp a) (natp w))
          (equal (take (+ a w) l) (append (take a l) (take w (nthcdr a l)))))
 :rule-classes nil
 :hints (("Goal" :induct (take a l) :in-theory (enable take nthcdr))))
(defthm mkc-right-step
 (implies (and (natp h) (equal w (expt 2 h)) (natp a) (< (+ a w) (len new))
               (fn2-mk-integrity-openings all)
               (member-equal (cons 1 (append (fn-b3-words-octets sr) (fn-b3-words-octets c))) all)
               (mk-words8p sr) (mk-words8p c)
               (equal (mk-join sr c)
                      (fn-b3-words 8 (mkc-hash (take (min (* 2 w) (- (len new) a)) (nthcdr a new)))))
               (subsetp-equal (mkc-opens (take (min (* 2 w) (- (len new) a)) (nthcdr a new))) all))
          (and (equal sr (fn-b3-words 8 (mkc-hash (take (min w (- (len new) a)) (nthcdr a new)))))
               (subsetp-equal (mkc-opens (take (min w (- (len new) a)) (nthcdr a new))) all)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mkc-child (u sr) (v c)
                         (xs (take (min (* 2 w) (- (len new) a)) (nthcdr a new)))))
          :in-theory (disable mkc-hash mkc-opens mk-join fn2-mk-integrity-openings))))
(defthm mkc-nthcdr-nthcdr
 (implies (and (natp a) (natp w) (<= w a))
          (equal (nthcdr w (nthcdr (- a w) l)) (nthcdr a l)))
 :hints (("Goal" :use ((:instance nthcdr-of-nthcdr (a w) (b (- a w)) (x l))) :in-theory (disable nthcdr-of-nthcdr))))
(defthm mkc-len-nthcdr
 (implies (and (natp k) (<= k (len l))) (equal (len (nthcdr k l)) (- (len l) k))))
(defthm mkc-expt-succ-linear
 (implies (natp h) (equal (expt 2 (+ 1 h)) (* 2 (expt 2 h))))
 :rule-classes ((:linear :trigger-terms ((expt 2 (+ 1 h)))))
 :hints (("Goal" :expand ((expt 2 (+ 1 h))))))
(defthm mkc-expt-diff
 (implies (natp h) (equal (+ (- (expt 2 h)) (expt 2 (+ 1 h))) (expt 2 h)))
 :hints (("Goal" :expand ((expt 2 (+ 1 h))))))
(defthm mkc-left-old
 (implies (and (natp h) (equal w (expt 2 h)) (natp a) (<= w a)
               (< a (len old)) (<= (len old) (+ a w))
               (fn2-mk-integrity-openings all)
               (member-equal (cons 1 (append (fn-b3-words-octets c) (fn-b3-words-octets fr))) all)
               (mk-words8p c) (mk-words8p fr)
               (equal (mk-join c fr) (fn-b3-words 8 (mkc-hash (nthcdr (- a w) old))))
               (subsetp-equal (mkc-opens (nthcdr (- a w) old)) all))
          (and (equal fr (fn-b3-words 8 (mkc-hash (nthcdr a old))))
               (subsetp-equal (mkc-opens (nthcdr a old)) all)
               (equal c (fn-b3-words 8 (mkc-hash (take w (nthcdr (- a w) old)))))
               (subsetp-equal (mkc-opens (take w (nthcdr (- a w) old))) all)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mkc-child (u c) (v fr) (xs (nthcdr (- a w) old))))
            :do-not-induct t :in-theory (disable mkc-hash mkc-opens mk-join fn2-mk-integrity-openings))))
(defthm mkc-left-prefix
 (implies (and (natp a) (natp w) (<= w a) (<= a (len old)) (<= a (len new))
               (fn2-mk-integrity-openings all)
               (equal c (fn-b3-words 8 (mkc-hash (take w (nthcdr (- a w) old)))))
               (equal c (fn-b3-words 8 (mkc-hash (take w (nthcdr (- a w) new)))))
               (subsetp-equal (mkc-opens (take w (nthcdr (- a w) old))) all)
               (subsetp-equal (mkc-opens (take w (nthcdr (- a w) new))) all)
               (equal (take (- a w) old) (take (- a w) new)))
          (equal (take a old) (take a new)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance mkc-bind (xs (take w (nthcdr (- a w) old))) (ys (take w (nthcdr (- a w) new))))
                (:instance mkc-take-split (a (- a w)) (l old))
                (:instance mkc-take-split (a (- a w)) (l new)))
          :in-theory (disable mkc-hash mkc-opens fn2-mk-integrity-openings))))
(defthm mkc-halve
 (implies (and (natp x) (natp h))
          (equal (floor (floor x (expt 2 h)) 2) (floor x (expt 2 (+ 1 h)))))
 )
(defun mkc-rise-ind (f s h)
 (declare (xargs :measure (nfix f)))
 (if (and (posp f) (evenp f)) (mkc-rise-ind (floor f 2) (floor s 2) (+ 1 h)) (list f s h)))
(defun mkc-rise-k (f)
 (declare (xargs :measure (nfix f)))
 (if (and (posp f) (evenp f)) (+ 1 (mkc-rise-k (floor f 2))) 0))
(defthm mkc-floor-floor
 (implies (and (natp x) (posp i) (posp j))
          (equal (floor (floor x i) j) (floor x (* i j)))))
(defthm mkc-rise-closed
 (implies (and (natp f) (natp s))
          (equal (fn2-mk-rise f s)
                 (mv (floor f (expt 2 (mkc-rise-k f))) (floor s (expt 2 (mkc-rise-k f))))))
 :hints (("Goal" :induct (mkc-rise-ind f s 0) :in-theory (enable fn2-mk-rise)
          :expand ((mkc-rise-k f)))))
(defthm mkc-even-half
 (implies (and (integerp f) (evenp f)) (equal (* 2 (floor f 2)) f))
 :rule-classes nil :hints (("Goal" :in-theory (enable evenp))))
(defthm mkc-rise-exact
 (implies (natp f)
          (equal (* (floor f (expt 2 (mkc-rise-k f))) (expt 2 (mkc-rise-k f))) f))
 :hints (("Goal" :induct (mkc-rise-k f) :expand ((mkc-rise-k f)))
         ("Subgoal *1/1" :use (mkc-even-half
                               (:instance mkc-floor-floor (x f) (i 2) (j (expt 2 (mkc-rise-k (floor f 2)))))
                               (:instance mkc-expt-step (h (+ 1 (mkc-rise-k (floor f 2))))))
                          :in-theory (disable mkc-floor-floor))))
(defthm mkc-rise-odd
 (implies (posp f)
          (and (oddp (mv-nth 0 (fn2-mk-rise f s)))
               (posp (mv-nth 0 (fn2-mk-rise f s)))))
 :hints (("Goal" :induct (fn2-mk-rise f s) :in-theory (enable fn2-mk-rise))))
(defthm mkc-rise-k-odd
 (implies (oddp f) (equal (mkc-rise-k f) 0))
 :hints (("Goal" :expand ((mkc-rise-k f)))))
(defun mkc-rows8p (rows)
 (if (atom rows) t (and (mk-words8p (car rows)) (mkc-rows8p (cdr rows)))))
(defun mkc-left (f s) (or (oddp f) (equal f s)))
(defun mkc-loop (f s rows fr sr ro rn)
 (declare (xargs :measure (len rows) :hints (("Goal" :in-theory (enable len)))))
 (cond ((atom rows) (list (if (and (equal s 0) (equal sr rn) (equal fr ro)) :ok :root-mismatch) nil))
       ((equal s 0) (list :proof-length nil))
       (t (let* ((c (car rows)) (left (mkc-left f s))
                 (p (fn-b3-words-octets c)) (r (fn-b3-words-octets sr)) (o (fn-b3-words-octets fr))
                 (ops (if left (list (cons 1 (append p r)) (cons 1 (append p o))) (list (cons 1 (append r p)))))
                 (sr2 (if left (mk-join c sr) (mk-join sr c)))
                 (fr2 (if left (mk-join c fr) fr)))
            (mv-let (f2 s2) (if left (fn2-mk-rise f s) (mv f s))
              (let ((res (mkc-loop (floor f2 2) (floor s2 2) (cdr rows) fr2 sr2 ro rn)))
                (list (car res) (append ops (cadr res)))))))))
(defun mkc-ind (f s h rows fr sr)
 (declare (xargs :measure (len rows) :hints (("Goal" :in-theory (enable len)))))
 (cond ((or (atom rows) (equal s 0)) (list f s h fr sr))
       (t (let* ((c (car rows)) (left (mkc-left f s))
                 (sr2 (if left (mk-join c sr) (mk-join sr c)))
                 (fr2 (if left (mk-join c fr) fr))
                 (h2 (if left (+ h (mkc-rise-k f)) h)))
            (mv-let (f2 s2) (if left (fn2-mk-rise f s) (mv f s))
              (mkc-ind (floor f2 2) (floor s2 2) (+ 1 h2) (cdr rows) fr2 sr2))))))
(defthm mkc-left-old2
 (implies (and (natp h) (equal v (expt 2 h)) (natp a) (<= v a) (equal a3 (- a v))
               (< a (len old)) (<= (len old) (+ a v))
               (fn2-mk-integrity-openings all)
               (member-equal (cons 1 (append (fn-b3-words-octets c) (fn-b3-words-octets fr))) all)
               (mk-words8p c) (mk-words8p fr)
               (equal (mk-join c fr) (fn-b3-words 8 (mkc-hash (nthcdr a3 old))))
               (subsetp-equal (mkc-opens (nthcdr a3 old)) all))
          (and (equal fr (fn-b3-words 8 (mkc-hash (nthcdr a old))))
               (subsetp-equal (mkc-opens (nthcdr a old)) all)
               (equal c (fn-b3-words 8 (mkc-hash (take v (nthcdr a3 old)))))
               (subsetp-equal (mkc-opens (take v (nthcdr a3 old))) all)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mkc-left-old (w v))))))
(defthm mkc-window-split
 (implies (and (posp v) (natp a) (<= v a) (< a (len new)) (equal a3 (- a v)) (equal w2 (* 2 v))
               (equal (min v (- (len new) a)) (min w (- (len new) a))))
          (and (< v (len (take (min w2 (- (len new) a3)) (nthcdr a3 new))))
               (<= (len (take (min w2 (- (len new) a3)) (nthcdr a3 new))) w2)
               (equal (take v (take (min w2 (- (len new) a3)) (nthcdr a3 new))) (take v (nthcdr a3 new)))
               (equal (nthcdr v (take (min w2 (- (len new) a3)) (nthcdr a3 new)))
                      (take (min w (- (len new) a)) (nthcdr a new)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance mkc-take-take (k v) (n (min (* 2 v) (- (len new) (- a v)))) (l (nthcdr (- a v) new)))
                (:instance mkc-nthcdr-take (k v) (n (min (* 2 v) (- (len new) (- a v)))) (l (nthcdr (- a v) new)))
                (:instance mkc-nthcdr-nthcdr (w v) (l new)))
          :in-theory (disable mkc-take-take mkc-nthcdr-take mkc-nthcdr-nthcdr))))
(defthm mkc-left-new2
 (implies (and (natp h) (equal v (expt 2 h)) (natp a) (<= v a) (< a (len new))
               (equal a3 (- a v)) (equal w2 (* 2 v))
               (equal (min v (- (len new) a)) (min w (- (len new) a)))
               (fn2-mk-integrity-openings all)
               (member-equal (cons 1 (append (fn-b3-words-octets c) (fn-b3-words-octets sr))) all)
               (mk-words8p c) (mk-words8p sr)
               (equal (mk-join c sr) (fn-b3-words 8 (mkc-hash (take (min w2 (- (len new) a3)) (nthcdr a3 new)))))
               (subsetp-equal (mkc-opens (take (min w2 (- (len new) a3)) (nthcdr a3 new))) all))
          (and (equal sr (fn-b3-words 8 (mkc-hash (take (min w (- (len new) a)) (nthcdr a new)))))
               (subsetp-equal (mkc-opens (take (min w (- (len new) a)) (nthcdr a new))) all)
               (equal c (fn-b3-words 8 (mkc-hash (take v (nthcdr a3 new)))))
               (subsetp-equal (mkc-opens (take v (nthcdr a3 new))) all)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use (mkc-window-split
                (:instance mkc-child (u c) (v sr) (xs (take (min w2 (- (len new) a3)) (nthcdr a3 new)))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(natp posp (:type-prescription expt-type-prescription-integerp-base)
                         (:type-prescription expt-type-prescription-positive-base))))))
(defthm mkc-left-prefix2
 (implies (and (natp a) (natp v) (<= v a) (equal a3 (- a v)) (<= a (len old)) (<= a (len new))
               (fn2-mk-integrity-openings all)
               (equal c (fn-b3-words 8 (mkc-hash (take v (nthcdr a3 old)))))
               (equal c (fn-b3-words 8 (mkc-hash (take v (nthcdr a3 new)))))
               (subsetp-equal (mkc-opens (take v (nthcdr a3 old))) all)
               (subsetp-equal (mkc-opens (take v (nthcdr a3 new))) all)
               (equal (take a3 old) (take a3 new)))
          (equal (take a old) (take a new)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mkc-left-prefix (w v))))))
(defun-nx mkc-inv (a w fr sr old new all)
  (and (equal fr (fn-b3-words 8 (mkc-hash (nthcdr a old))))
       (subsetp-equal (mkc-opens (nthcdr a old)) all)
       (equal sr (fn-b3-words 8 (mkc-hash (take (min w (- (len new) a)) (nthcdr a new)))))
       (subsetp-equal (mkc-opens (take (min w (- (len new) a)) (nthcdr a new))) all)
       (equal (take a old) (take a new))))
(defthm mkc-inv-left
 (implies (and (natp h) (equal v (expt 2 h)) (natp a) (<= v a)
               (< a (len old)) (<= (len old) (+ a v)) (< a (len new))
               (equal (min v (- (len new) a)) (min w (- (len new) a)))
               (fn2-mk-integrity-openings all)
               (member-equal (cons 1 (append (fn-b3-words-octets c) (fn-b3-words-octets sr))) all)
               (member-equal (cons 1 (append (fn-b3-words-octets c) (fn-b3-words-octets fr))) all)
               (mk-words8p c) (mk-words8p fr) (mk-words8p sr)
               (mkc-inv a3 w2 (mk-join c fr) (mk-join c sr) old new all)
               (equal a3 (- a v)) (equal w2 (* 2 v)))
          (mkc-inv a w fr sr old new all))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use (mkc-left-old2 mkc-left-new2 mkc-left-prefix2)
          :in-theory (union-theories (theory 'minimal-theory) '(mkc-inv natp (:type-prescription expt-type-prescription-integerp-base) (:type-prescription expt-type-prescription-positive-base))))))
(defthm mkc-inv-right
 (implies (and (natp h) (equal w (expt 2 h)) (natp a) (< (+ a w) (len new))
               (fn2-mk-integrity-openings all)
               (member-equal (cons 1 (append (fn-b3-words-octets sr) (fn-b3-words-octets c))) all)
               (mk-words8p sr) (mk-words8p c)
               (mkc-inv a3 w2 fr (mk-join sr c) old new all)
               (equal a3 a) (equal w2 (* 2 w)))
          (mkc-inv a w fr sr old new all))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use (mkc-right-step)
          :in-theory (e/d (mkc-inv) (mkc-hash mkc-opens mk-join fn2-mk-integrity-openings)))))
(defthm mkc-floor-bounds
 (implies (and (natp x) (posp w))
          (and (<= (* (floor x w) w) x) (< x (+ w (* (floor x w) w)))))
 :rule-classes nil)
(defthm mkc-floor-monotone
 (implies (and (natp x) (natp y) (<= x y) (posp w)) (<= (floor x w) (floor y w)))
 :rule-classes nil
 :hints (("Goal" :use (mkc-floor-bounds (:instance mkc-floor-bounds (x y)))
                 :nonlinearp t)))
(defthm mkc-expt-sum
 (implies (and (natp h) (natp k)) (equal (* (expt 2 h) (expt 2 k)) (expt 2 (+ h k)))))
(defthm mkc-floor3
 (implies (and (natp x) (natp h) (natp k))
          (equal (floor (floor (floor x (expt 2 h)) (expt 2 k)) 2) (floor x (expt 2 (+ 1 h k)))))
 :hints (("Goal" :in-theory (disable mkc-floor-floor)
          :use ((:instance mkc-floor-floor (i (expt 2 h)) (j (expt 2 k)))
                (:instance mkc-floor-floor (x (floor x (expt 2 h))) (i (expt 2 k)) (j 2))
                (:instance mkc-floor-floor (i (expt 2 (+ h k))) (j 2))))))
(defthm mkc-rise-a
 (implies (and (natp x) (natp h))
          (equal (* (floor (floor x (expt 2 h)) (expt 2 (mkc-rise-k (floor x (expt 2 h)))))
                    (expt 2 (+ h (mkc-rise-k (floor x (expt 2 h))))))
                 (* (floor x (expt 2 h)) (expt 2 h))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mkc-rise-exact (f (floor x (expt 2 h))))
                       (:instance mkc-expt-sum (k (mkc-rise-k (floor x (expt 2 h))))))
          :in-theory (disable mkc-rise-exact mkc-expt-sum))))
(defthm mkc-odd-half
 (implies (and (posp f1) (oddp f1) (posp v))
          (equal (* (floor f1 2) (* 2 v)) (- (* f1 v) v)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable oddp evenp))))
(defthm mkc-f1-floor
 (implies (and (natp x) (natp h))
          (equal (floor (floor x (expt 2 h)) (expt 2 (mkc-rise-k (floor x (expt 2 h)))))
                 (floor x (expt 2 (+ h (mkc-rise-k (floor x (expt 2 h))))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mkc-floor-floor (i (expt 2 h)) (j (expt 2 (mkc-rise-k (floor x (expt 2 h)))))))
          :in-theory (disable mkc-floor-floor))))
(defthm mkc-expt-mono
 (implies (and (natp h) (natp k)) (<= (expt 2 h) (expt 2 (+ h k))))
 :rule-classes nil
 :hints (("Goal" :use mkc-expt-sum :in-theory (disable mkc-expt-sum) :nonlinearp t)))
(defthm mkc-left-alg
 (implies (and (natp x) (natp y) (posp e) (posp v) (<= e v) (natp a)
               (equal a (* f1 v)) (<= a x) (< x (+ a v)) (<= a y)
               (posp f1) (oddp f1)
               (or (equal e v) (< y (+ a e))))
   (and (<= v a) (< a (+ 1 x)) (<= (+ 1 x) (+ a v)) (< a (+ 1 y))
        (equal (min v (- (+ 1 y) a)) (min e (- (+ 1 y) a)))
        (equal (* (floor f1 2) (* 2 v)) (- a v))))
 :rule-classes nil
 :hints (("Goal" :use mkc-odd-half :nonlinearp t)))
(defthm mkc-left-arith
 (implies (and (natp x) (natp y) (<= x y) (natp h)
               (not (equal (floor y (expt 2 h)) 0))
               (mkc-left (floor x (expt 2 h)) (floor y (expt 2 h))))
          (let* ((f (floor x (expt 2 h)))
                 (k (mkc-rise-k f)) (v (expt 2 (+ h k))) (a (* f (expt 2 h)))
                 (f1 (floor f (expt 2 k))))
            (and (<= v a) (< a (+ 1 x)) (<= (+ 1 x) (+ a v)) (< a (+ 1 y))
                 (equal (min v (- (+ 1 y) a)) (min (expt 2 h) (- (+ 1 y) a)))
                 (equal (* (floor f1 2) (expt 2 (+ 1 h k))) (- a v)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :cases ((oddp (floor x (expt 2 h))))
          :use (mkc-rise-a mkc-f1-floor
                (:instance mkc-expt-mono (k (mkc-rise-k (floor x (expt 2 h)))))
                (:instance mkc-expt-succ-linear (h (+ h (mkc-rise-k (floor x (expt 2 h))))))
                (:instance mkc-rise-odd (f (floor x (expt 2 h))) (s (floor y (expt 2 h))))
                (:instance mkc-rise-closed (f (floor x (expt 2 h))) (s (floor y (expt 2 h))))
                (:instance mkc-rise-k-odd (f (floor x (expt 2 h))))
                (:instance mkc-floor-bounds (w (expt 2 h)))
                (:instance mkc-floor-bounds (x y) (w (expt 2 h)))
                (:instance mkc-floor-bounds (w (expt 2 (+ h (mkc-rise-k (floor x (expt 2 h)))))))
                (:instance mkc-left-alg (e (expt 2 h))
                   (f1 (floor (floor x (expt 2 h)) (expt 2 (mkc-rise-k (floor x (expt 2 h))))))
                   (v (expt 2 (+ h (mkc-rise-k (floor x (expt 2 h))))))
                   (a (* (floor x (expt 2 h)) (expt 2 h)))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(natp posp mkc-left (:type-prescription floor) (:type-prescription expt)
                         (:type-prescription expt-type-prescription-integerp-base)
                         (:type-prescription expt-type-prescription-positive-base)
                         (:type-prescription mkc-rise-k) (:executable-counterpart oddp)
                         (:type-prescription floor-nonnegative-1)
                         mv-nth car-cons cdr-cons (:executable-counterpart zp)
                         fix (:executable-counterpart binary-+) unicity-of-0 commutativity-of-+)))))
(defthm mkc-right-alg
 (implies (and (natp f) (natp s) (< f s) (posp e) (natp y) (<= (* s e) y) (evenp f))
          (and (< (+ (* f e) e) (+ 1 y))
               (equal (* (floor f 2) (* 2 e)) (* f e))))
 :rule-classes nil
 :hints (("Goal" :use mkc-even-half :nonlinearp t)))
(defthm mkc-right-arith
 (implies (and (natp x) (natp y) (<= x y) (natp h)
               (not (mkc-left (floor x (expt 2 h)) (floor y (expt 2 h)))))
          (let ((f (floor x (expt 2 h))))
            (and (< (+ (* f (expt 2 h)) (expt 2 h)) (+ 1 y))
                 (equal (* (floor f 2) (expt 2 (+ 1 h))) (* f (expt 2 h))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance mkc-floor-monotone (w (expt 2 h)))
                (:instance mkc-floor-bounds (x y) (w (expt 2 h)))
                (:instance mkc-expt-succ-linear)
                (:instance mkc-right-alg (f (floor x (expt 2 h))) (s (floor y (expt 2 h))) (e (expt 2 h))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(natp posp mkc-left oddp (:type-prescription floor) (:type-prescription expt)
                         (:type-prescription expt-type-prescription-integerp-base)
                         (:type-prescription expt-type-prescription-positive-base)
                         (:type-prescription floor-nonnegative-1))))))
(defthm mkc-base-arith
 (implies (and (natp x) (natp y) (<= x y) (natp h) (equal (floor y (expt 2 h)) 0))
          (and (equal (floor x (expt 2 h)) 0) (< y (expt 2 h))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mkc-floor-monotone (w (expt 2 h)))
                       (:instance mkc-floor-bounds (x y) (w (expt 2 h)))))))
(defun-nx mkc-hyps (f s h rows fr sr ro rn old new all)
 (and (equal (car (mkc-loop f s rows fr sr ro rn)) :ok)
      (subsetp-equal (cadr (mkc-loop f s rows fr sr ro rn)) all)
      (fn2-mk-integrity-openings all)
      (subsetp-equal (mkc-opens old) all) (subsetp-equal (mkc-opens new) all)
      (equal ro (fn-b3-words 8 (mkc-hash old))) (equal rn (fn-b3-words 8 (mkc-hash new)))
      (true-listp old) (true-listp new) (posp (len old)) (<= (len old) (len new))
      (natp h) (equal f (floor (+ -1 (len old)) (expt 2 h))) (equal s (floor (+ -1 (len new)) (expt 2 h)))
      (mk-words8p fr) (mk-words8p sr) (mkc-rows8p rows)))
(defthm mkc-loop-base
 (implies (and (mkc-hyps f s h rows fr sr ro rn old new all)
               (or (atom rows) (equal s 0)))
          (mkc-inv (* f (expt 2 h)) (expt 2 h) fr sr old new all))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mkc-base-arith (x (+ -1 (len old))) (y (+ -1 (len new)))))
          :expand ((mkc-loop f s rows fr sr ro rn))
          :in-theory (e/d (mkc-hyps mkc-inv) (mkc-hash mkc-opens mk-join fn2-mk-integrity-openings)))))
(defthm mkc-loop-step-facts
 (implies (and (consp rows) (not (equal s 0)))
          (let ((res (mkc-loop f s rows fr sr ro rn)) (c (car rows)) (left (mkc-left f s)))
            (and (equal (car res)
                        (car (mkc-loop (floor (if left (mv-nth 0 (fn2-mk-rise f s)) f) 2)
                                       (floor (if left (mv-nth 1 (fn2-mk-rise f s)) s) 2)
                                       (cdr rows) (if left (mk-join c fr) fr)
                                       (if left (mk-join c sr) (mk-join sr c)) ro rn)))
                 (equal (cadr res)
                        (append (if left (list (cons 1 (append (fn-b3-words-octets c) (fn-b3-words-octets sr)))
                                               (cons 1 (append (fn-b3-words-octets c) (fn-b3-words-octets fr))))
                                  (list (cons 1 (append (fn-b3-words-octets sr) (fn-b3-words-octets c)))))
                                (cadr (mkc-loop (floor (if left (mv-nth 0 (fn2-mk-rise f s)) f) 2)
                                       (floor (if left (mv-nth 1 (fn2-mk-rise f s)) s) 2)
                                       (cdr rows) (if left (mk-join c fr) fr)
                                       (if left (mk-join c sr) (mk-join sr c)) ro rn)))))))
 :rule-classes nil
 :hints (("Goal" :expand ((mkc-loop f s rows fr sr ro rn))
          :in-theory (disable mkc-left mk-join fn2-mk-rise mkc-rise-closed))))
(defthm mkc-left-arith-mn
 (implies (and (posp m) (natp n) (<= m n) (natp h)
               (equal f (floor (+ -1 m) (expt 2 h))) (equal s (floor (+ -1 n) (expt 2 h)))
               (not (equal s 0)) (mkc-left f s))
          (let* ((k (mkc-rise-k f)) (v (expt 2 (+ h k))) (a (* f (expt 2 h))))
            (and (natp (+ h k)) (natp a) (<= v a) (< a m) (<= m (+ a v)) (< a n)
                 (equal (min v (- n a)) (min (expt 2 h) (- n a)))
                 (equal (* (floor (mv-nth 0 (fn2-mk-rise f s)) 2) (expt 2 (+ 1 (+ h k)))) (- a v))
                 (equal (expt 2 (+ 1 (+ h k))) (* 2 v)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance mkc-left-arith (x (+ -1 m)) (y (+ -1 n)))
                (:instance mkc-rise-closed)
                (:instance mkc-expt-succ-linear (h (+ h (mkc-rise-k f)))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(natp posp min (:type-prescription floor) (:type-prescription expt)
                         (:type-prescription expt-type-prescription-integerp-base)
                         (:type-prescription expt-type-prescription-positive-base)
                         (:type-prescription mkc-rise-k) (:type-prescription floor-nonnegative-1)
                         mv-nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart binary-+)
                         fix unicity-of-0 commutativity-of-+ associativity-of-+ commutativity-2-of-+
                         inverse-of-+ (:executable-counterpart unary--) distributivity-of-minus-over-+)))))
(defthm mkc-member-of-subset
 (implies (and (subsetp-equal (append xs ys) all) (member-equal x xs))
          (and (member-equal x all) (subsetp-equal ys all))))
(defthm mkc-floor-rise-left
 (implies (and (natp x) (natp y) (natp h) (equal f (floor x (expt 2 h))) (equal s (floor y (expt 2 h))))
          (and (equal (floor (mv-nth 0 (fn2-mk-rise f s)) 2) (floor x (expt 2 (+ 1 (+ h (mkc-rise-k f))))))
               (equal (floor (mv-nth 1 (fn2-mk-rise f s)) 2) (floor y (expt 2 (+ 1 (+ h (mkc-rise-k f))))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable mkc-rise-k))))
(defthm mkc-member-two
 (implies (subsetp-equal (append (list a b) ys) all)
          (and (member-equal a all) (member-equal b all) (subsetp-equal ys all)))
 :rule-classes nil)
(defthm mkc-member-one
 (implies (subsetp-equal (append (list a) ys) all)
          (and (member-equal a all) (subsetp-equal ys all)))
 :rule-classes nil)
(defthm mkc-hyps-left
 (implies (and (mkc-hyps f s h rows fr sr ro rn old new all) (consp rows) (not (equal s 0)) (mkc-left f s))
  (and (member-equal (cons 1 (append (fn-b3-words-octets (car rows)) (fn-b3-words-octets sr))) all)
       (member-equal (cons 1 (append (fn-b3-words-octets (car rows)) (fn-b3-words-octets fr))) all)
       (mk-words8p (car rows))
       (mkc-hyps (floor (mv-nth 0 (fn2-mk-rise f s)) 2) (floor (mv-nth 1 (fn2-mk-rise f s)) 2)
                 (+ 1 (+ h (mkc-rise-k f))) (cdr rows) (mk-join (car rows) fr) (mk-join (car rows) sr)
                 ro rn old new all)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use (mkc-loop-step-facts
                (:instance mkc-floor-rise-left (x (+ -1 (len old))) (y (+ -1 (len new))))
                (:instance mkc-member-two
                  (a (cons 1 (append (fn-b3-words-octets (car rows)) (fn-b3-words-octets sr))))
                  (b (cons 1 (append (fn-b3-words-octets (car rows)) (fn-b3-words-octets fr))))
                  (ys (cadr (mkc-loop (floor (mv-nth 0 (fn2-mk-rise f s)) 2) (floor (mv-nth 1 (fn2-mk-rise f s)) 2)
                                      (cdr rows) (mk-join (car rows) fr) (mk-join (car rows) sr) ro rn)))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(mkc-hyps mkc-rows8p mk-join-words8p natp posp (:type-prescription mkc-rise-k)
                         (:type-prescription len))))))
(defthm mkc-loop-left
 (implies (and (mkc-hyps f s h rows fr sr ro rn old new all) (consp rows) (not (equal s 0)) (mkc-left f s)
               (implies (mkc-hyps (floor (mv-nth 0 (fn2-mk-rise f s)) 2) (floor (mv-nth 1 (fn2-mk-rise f s)) 2)
                                  (+ 1 (+ h (mkc-rise-k f))) (cdr rows) (mk-join (car rows) fr) (mk-join (car rows) sr)
                                  ro rn old new all)
                        (mkc-inv (* (floor (mv-nth 0 (fn2-mk-rise f s)) 2) (expt 2 (+ 1 (+ h (mkc-rise-k f)))))
                                 (expt 2 (+ 1 (+ h (mkc-rise-k f))))
                                 (mk-join (car rows) fr) (mk-join (car rows) sr) old new all)))
          (mkc-inv (* f (expt 2 h)) (expt 2 h) fr sr old new all))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use (mkc-hyps-left
                (:instance mkc-left-arith-mn (m (len old)) (n (len new)))
                (:instance mkc-inv-left (h (+ h (mkc-rise-k f))) (v (expt 2 (+ h (mkc-rise-k f))))
                   (a (* f (expt 2 h))) (w (expt 2 h)) (c (car rows))
                   (a3 (* (floor (mv-nth 0 (fn2-mk-rise f s)) 2) (expt 2 (+ 1 (+ h (mkc-rise-k f))))))
                   (w2 (expt 2 (+ 1 (+ h (mkc-rise-k f)))))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(mkc-hyps natp posp (:type-prescription len))))))
(defthm mkc-right-arith-mn
 (implies (and (posp m) (natp n) (<= m n) (natp h)
               (equal f (floor (+ -1 m) (expt 2 h))) (equal s (floor (+ -1 n) (expt 2 h)))
               (not (mkc-left f s)))
          (and (natp (* f (expt 2 h))) (< (+ (* f (expt 2 h)) (expt 2 h)) n)
               (equal (* (floor f 2) (expt 2 (+ 1 h))) (* f (expt 2 h)))
               (equal (expt 2 (+ 1 h)) (* 2 (expt 2 h)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance mkc-right-arith (x (+ -1 m)) (y (+ -1 n)))
                (:instance mkc-expt-succ-linear))
          :in-theory (disable mkc-left floor expt mkc-floor-floor mkc-floor3 mkc-expt-sum))))
(defthm mkc-hyps-right
 (implies (and (mkc-hyps f s h rows fr sr ro rn old new all) (consp rows) (not (equal s 0)) (not (mkc-left f s)))
  (and (member-equal (cons 1 (append (fn-b3-words-octets sr) (fn-b3-words-octets (car rows)))) all)
       (mk-words8p (car rows))
       (mkc-hyps (floor f 2) (floor s 2) (+ 1 h) (cdr rows) fr (mk-join sr (car rows)) ro rn old new all)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use (mkc-loop-step-facts
                (:instance mkc-halve (x (+ -1 (len old))))
                (:instance mkc-halve (x (+ -1 (len new))))
                (:instance mkc-member-one
                  (a (cons 1 (append (fn-b3-words-octets sr) (fn-b3-words-octets (car rows)))))
                  (ys (cadr (mkc-loop (floor f 2) (floor s 2) (cdr rows) fr (mk-join sr (car rows)) ro rn)))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(mkc-hyps mkc-rows8p mk-join-words8p natp posp (:type-prescription len))))))
(defthm mkc-loop-right
 (implies (and (mkc-hyps f s h rows fr sr ro rn old new all) (consp rows) (not (equal s 0)) (not (mkc-left f s))
               (implies (mkc-hyps (floor f 2) (floor s 2) (+ 1 h) (cdr rows) fr (mk-join sr (car rows)) ro rn old new all)
                        (mkc-inv (* (floor f 2) (expt 2 (+ 1 h))) (expt 2 (+ 1 h)) fr (mk-join sr (car rows)) old new all)))
          (mkc-inv (* f (expt 2 h)) (expt 2 h) fr sr old new all))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use (mkc-hyps-right
                (:instance mkc-right-arith-mn (m (len old)) (n (len new)))
                (:instance mkc-inv-right (w (expt 2 h)) (a (* f (expt 2 h))) (c (car rows))
                   (a3 (* (floor f 2) (expt 2 (+ 1 h)))) (w2 (expt 2 (+ 1 h)))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(mkc-hyps natp posp (:type-prescription len))))))
(defthm mkc-loop-sound
 (implies (mkc-hyps f s h rows fr sr ro rn old new all)
          (mkc-inv (* f (expt 2 h)) (expt 2 h) fr sr old new all))
 :rule-classes nil
 :hints (("Goal" :induct (mkc-ind f s h rows fr sr)
          :in-theory (union-theories (theory 'minimal-theory) '(mkc-ind)))
         ("Subgoal *1/3" :use (mkc-loop-base mkc-loop-left mkc-loop-right))
         ("Subgoal *1/2" :use (mkc-loop-base mkc-loop-left mkc-loop-right))
         ("Subgoal *1/1" :use (mkc-loop-base mkc-loop-left mkc-loop-right))))
(defthm mkc-seed-sound
 (implies (and (mkc-hyps f s h rows fr fr ro rn old new all)
               (equal (len old) (+ (* f (expt 2 h)) (expt 2 h)))
               (< (len old) (len new)))
          (equal old (take (len old) new)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance mkc-loop-sound (sr fr))
                (:instance mkc-bind (xs (nthcdr (* f (expt 2 h)) old))
                                    (ys (take (expt 2 h) (nthcdr (* f (expt 2 h)) new))))
                (:instance mkc-take-split (a (* f (expt 2 h))) (w (expt 2 h)) (l new))
                (:instance append-of-take-and-nthcdr (n (* f (expt 2 h))) (x old)))
          :in-theory (e/d (mkc-inv mkc-hyps) (mkc-hash mkc-opens mk-join fn2-mk-integrity-openings mkc-loop
                                               append-of-take-and-nthcdr)))))
(defun mkc-strip-k (f)
 (declare (xargs :measure (nfix f)))
 (if (and (posp f) (oddp f)) (+ 1 (mkc-strip-k (floor f 2))) 0))
(defun mkc-strip-ind (f s)
 (declare (xargs :measure (nfix f)))
 (if (and (posp f) (oddp f)) (mkc-strip-ind (floor f 2) (floor s 2)) (list f s)))
(defthm mkc-strip-closed
 (implies (and (natp f) (natp s))
          (equal (fn2-mk-strip f s)
                 (mv (floor f (expt 2 (mkc-strip-k f))) (floor s (expt 2 (mkc-strip-k f))))))
 :hints (("Goal" :induct (mkc-strip-ind f s) :in-theory (enable fn2-mk-strip)
          :expand ((mkc-strip-k f)))))
(defthm mkc-odd-half2
 (implies (and (integerp f) (oddp f)) (equal (+ 1 (* 2 (floor f 2))) f))
 :rule-classes nil :hints (("Goal" :in-theory (enable oddp evenp))))
(defthm mkc-strip-alg
 (implies (and (acl2-numberp e) (acl2-numberp q) (equal e2 (* 2 e)) (equal (+ e (* e q)) (+ 1 g)) (equal (+ 1 (* 2 g)) f))
          (equal (+ e2 (* e2 q)) (+ 1 f)))
 :rule-classes nil)
(defthm mkc-strip-size
 (implies (natp f)
          (equal (+ (* (floor f (expt 2 (mkc-strip-k f))) (expt 2 (mkc-strip-k f))) (expt 2 (mkc-strip-k f)))
                 (+ 1 f)))
 :hints (("Goal" :induct (mkc-strip-k f) :expand ((mkc-strip-k f)))
         ("Subgoal *1/1" :use (mkc-odd-half2
                               (:instance mkc-floor-floor (x f) (i 2) (j (expt 2 (mkc-strip-k (floor f 2)))))
                               (:instance mkc-expt-succ-linear (h (mkc-strip-k (floor f 2))))
                               (:instance mkc-strip-alg (e (expt 2 (mkc-strip-k (floor f 2))))
                                  (e2 (expt 2 (+ 1 (mkc-strip-k (floor f 2)))))
                                  (q (floor f (expt 2 (+ 1 (mkc-strip-k (floor f 2))))))
                                  (g (floor f 2))))
                          :in-theory (disable mkc-floor-floor))))
