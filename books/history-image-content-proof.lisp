; Word-level refinement of buffered final placement.
(in-package "ACL2")
(include-book "history-image-place-proof")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-his-rc-write-materializes-words
 (implies (and (true-listp ws)
               (fn-his-rc-fitp (len ws) rc start (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
  (let* ((res (fn-his-rc-write ws rc start pgs-mem))
         (out (mv-nth 0 res)) (mem (mv-nth 1 res)))
   (equal (fn-hp-rep (nth *pgs-wi* mem) (* 2048 (+ start (car out))) (reverse (caddr out)))
          (fn-hp-rep (nth *pgs-wi* pgs-mem) (* 2048 (+ start (car rc)))
                     (append (reverse (caddr rc)) ws)))))
 :hints (("Goal" :do-not-induct t
          :use (fn-his-rc-write-materializes
                (:instance fn-his-rc-write-fits
                 (nw (pgs-w-length pgs-mem)) (nd (pgs-d-length pgs-mem)))
                (:instance fn-hp-x-put-words
                 (j (* 2048 (+ start (car rc)))) (ws (append (reverse (caddr rc)) ws)))
                (:instance fn-hp-x-put-words
                 (j (* 2048 (+ start (car (mv-nth 0 (fn-his-rc-write ws rc start pgs-mem))))))
                 (ws (reverse (caddr (mv-nth 0 (fn-his-rc-write ws rc start pgs-mem)))))
                 (pgs-mem (mv-nth 1 (fn-his-rc-write ws rc start pgs-mem)))))
          :in-theory (e/d (fn-his-rc-fitp fn-his-rcp)
                          (fn-his-rc-write fn-his-rc-write-materializes fn-his-rc-write-fits
                           fn-hp-x-put fn-hp-rep fn-hp-x-put-words reverse floor nth adt-nth-1+)))))

(local
 (defun fn-his-index-pair-ind (i j xs)
  (declare (xargs :guard (and (natp i) (natp j) (true-listp xs)) :measure (nfix i)))
  (if (or (zp i) (zp j)) xs
    (fn-his-index-pair-ind (1- i) (1- j) (cdr xs)))))

(local
 (defthm fn-his-update-nth-commute
  (implies (and (natp i) (natp j) (or (not (equal i j)) (equal x y)))
           (equal (update-nth i x (update-nth j y z))
                  (update-nth j y (update-nth i x z))))
  :hints (("Goal" :induct (fn-his-index-pair-ind i j z) :in-theory (enable update-nth)))
  :rule-classes ((:rewrite :loop-stopper ((i j))))))

(defthm fn-his-word-write-commute
 (implies (and (natp a) (natp b) (not (equal a b)))
  (equal (update-pgs-di (floor a 2048) 1
          (update-pgs-wi a x (update-pgs-di (floor b 2048) 1 (update-pgs-wi b y pgs-mem))))
         (update-pgs-di (floor b 2048) 1
          (update-pgs-wi b y (update-pgs-di (floor a 2048) 1 (update-pgs-wi a x pgs-mem))))))
 :hints (("Goal" :in-theory (e/d (update-pgs-di update-pgs-wi)
                                (floor update-nth nth adt-nth-1+))))
 :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm fn-his-put-single-commutes
 (implies (and (natp a) (natp b) (or (< a b) (<= (+ b (len ys)) a)))
  (equal (fn-hp-x-put a (list x) (fn-hp-x-put b ys pgs-mem))
         (fn-hp-x-put b ys (fn-hp-x-put a (list x) pgs-mem))))
 :hints (("Goal" :induct (fn-hp-x-put b ys pgs-mem)
          :in-theory (e/d (fn-hp-x-put len)
                          (update-pgs-di update-pgs-wi floor nth adt-nth-1+)))))

(defthm fn-his-put-commutes
 (implies (and (natp a) (natp b)
               (or (<= (+ a (len xs)) b) (<= (+ b (len ys)) a)))
  (equal (fn-hp-x-put a xs (fn-hp-x-put b ys pgs-mem))
         (fn-hp-x-put b ys (fn-hp-x-put a xs pgs-mem))))
 :hints (("Goal" :induct (fn-hp-x-put a xs pgs-mem)
          :in-theory (e/d (fn-hp-x-put len)
                          (update-pgs-di update-pgs-wi floor nth adt-nth-1+)))
         ("Subgoal *1/2" :use ((:instance fn-his-put-single-commutes (x (car xs))))))
 :rule-classes nil)

(local
 (defun-nx fn-his-cursor-pair-ind (ws rc start mem1 mem2)
  (declare (xargs :guard t :verify-guards t))
  (if (atom ws) (list rc mem1 mem2)
   (let ((a (ec-call (fn-his-rc-write (list (car ws)) rc start mem1)))
         (b (ec-call (fn-his-rc-write (list (car ws)) rc start mem2))))
    (fn-his-cursor-pair-ind (cdr ws) (car a) start (cadr a) (cadr b))))))

(defthm fn-his-rc-write-cursor-independent
 (equal (mv-nth 0 (fn-his-rc-write ws rc start mem1))
        (mv-nth 0 (fn-his-rc-write ws rc start mem2)))
 :hints (("Goal" :induct (fn-his-cursor-pair-ind ws rc start mem1 mem2)
          :in-theory (disable fn-hp-x-put)))
 :rule-classes nil)

(defthm fn-his-rc-write-commutes-with-disjoint-put
 (implies
  (and (fn-his-rcp rc) (natp start) (natp j)
       (or (<= (+ j (len ys)) (* 2048 (+ start (car rc))))
           (<= (+ (* 2048 (+ start (car rc))) (cadr rc) (len ws)) j)))
  (equal (mv-nth 1 (fn-his-rc-write ws rc start (fn-hp-x-put j ys pgs-mem)))
         (fn-hp-x-put j ys (mv-nth 1 (fn-his-rc-write ws rc start pgs-mem)))))
 :hints (("Goal" :induct (fn-his-rc-write ws rc start pgs-mem)
          :in-theory (e/d (fn-his-rcp len)
                          (fn-hp-x-put fn-his-put-append floor)))
         ("Subgoal *1/2"
          :use ((:instance fn-his-put-commutes
                  (a (* 2048 (+ start (car rc)))) (b j)
                  (xs (reverse (cons (car ws) (caddr rc))))))))
 :rule-classes nil)

(defthm fn-his-put-empty-by-definition
  (implies (atom ws) (equal (fn-hp-x-put j ws pgs-mem) pgs-mem))
  :hints (("Goal" :in-theory (enable fn-hp-x-put))))

(defthm fn-his-rc-write-empty-by-definition
  (implies (atom ws) (equal (fn-his-rc-write ws rc start pgs-mem) (list rc pgs-mem)))
  :hints (("Goal" :in-theory (enable fn-his-rc-write))))

(defun fn-his-put-apart-from-cursors (j ys cells rcs starts)
 (declare (xargs :guard (natp j)))
 (if (or (atom cells) (atom ys)) t
  (and (consp rcs) (consp starts) (fn-his-rcp (car rcs)) (natp (car starts))
       (or (atom (car cells))
           (<= (+ j (len ys)) (* 2048 (+ (car starts) (car (car rcs)))))
           (<= (+ (* 2048 (+ (car starts) (car (car rcs))))
                  (cadr (car rcs)) (len (car cells))) j))
       (fn-his-put-apart-from-cursors j ys (cdr cells) (cdr rcs) (cdr starts)))))

(defthm fn-his-rcs-write-commutes-with-disjoint-put
 (implies (and (natp j) (fn-his-put-apart-from-cursors j ys cells rcs starts))
  (equal (mv-nth 1 (fn-his-rcs-write cells rcs starts (fn-hp-x-put j ys pgs-mem)))
         (fn-hp-x-put j ys (mv-nth 1 (fn-his-rcs-write cells rcs starts pgs-mem)))))
 :hints (("Goal" :induct (fn-his-rcs-write cells rcs starts pgs-mem)
          :in-theory (disable fn-his-rc-write fn-his-rcp fn-hp-x-put))
         ("Subgoal *1/2"
          :use ((:instance fn-his-rc-write-commutes-with-disjoint-put
                  (ws (car cells)) (rc (car rcs)) (start (car starts))))))
 :rule-classes nil)

(local
 (defun-nx fn-his-cursors-pair-ind (cells rcs starts mem1 mem2)
  (declare (xargs :guard (and (true-listp rcs) (true-listp starts)) :verify-guards t))
  (if (atom cells) (list rcs starts mem1 mem2)
   (let ((a (ec-call (fn-his-rc-write (car cells) (car rcs) (car starts) mem1)))
         (b (ec-call (fn-his-rc-write (car cells) (car rcs) (car starts) mem2))))
    (fn-his-cursors-pair-ind (cdr cells) (cdr rcs) (cdr starts) (cadr a) (cadr b))))))

(defthm fn-his-rcs-write-cursors-independent
 (equal (mv-nth 0 (fn-his-rcs-write cells rcs starts mem1))
        (mv-nth 0 (fn-his-rcs-write cells rcs starts mem2)))
 :hints (("Goal" :induct (fn-his-cursors-pair-ind cells rcs starts mem1 mem2)
          :in-theory (disable fn-his-rc-write fn-hp-x-put))
         ("Subgoal *1/2"
          :use ((:instance fn-his-rc-write-cursor-independent
                  (ws (car cells)) (rc (car rcs)) (start (car starts))))))
 :rule-classes nil)

(defthm fn-his-rc-write-page-monotone
 (implies (fn-his-rcp rc)
          (<= (car rc) (car (mv-nth 0 (fn-his-rc-write ws rc start pgs-mem)))))
 :hints (("Goal" :induct (fn-his-rc-write ws rc start pgs-mem)
          :in-theory (e/d (fn-his-rcp len) (fn-hp-x-put floor)))))

(local
 (defthm fn-his-len-zero-atom
  (implies (equal (len x) 0) (atom x))
  :hints (("Goal" :expand ((len x))))))

(defthm fn-his-put-apart-subrange
 (implies (and (natp a) (natp b) (<= a b) (<= (+ b (len ys)) (+ a (len xs)))
               (fn-his-put-apart-from-cursors a xs cells rcs starts))
          (fn-his-put-apart-from-cursors b ys cells rcs starts))
 :hints (("Goal" :induct (fn-his-put-apart-from-cursors a xs cells rcs starts)
          :in-theory (e/d (len) (fn-his-rcp)))))

(defthm fn-his-pending-write-apart
 (implies
  (and (fn-his-rcp rc) (natp start) (true-listp ws)
       (fn-his-put-apart-from-cursors (* 2048 (+ start (car rc)))
                                     (append (reverse (caddr rc)) ws) cells rcs starts))
  (let ((out (mv-nth 0 (fn-his-rc-write ws rc start pgs-mem))))
   (fn-his-put-apart-from-cursors (* 2048 (+ start (car out)))
                                 (reverse (caddr out)) cells rcs starts)))
 :hints (("Goal" :do-not-induct t
          :use (fn-his-rc-write-position fn-his-rc-write-page-monotone
                (:instance fn-his-put-apart-subrange
                  (a (* 2048 (+ start (car rc))))
                  (xs (append (reverse (caddr rc)) ws))
                  (b (* 2048 (+ start (car (mv-nth 0 (fn-his-rc-write ws rc start pgs-mem))))))
                  (ys (reverse (caddr (mv-nth 0 (fn-his-rc-write ws rc start pgs-mem)))))))
          :in-theory (e/d (fn-his-rcp)
                          (fn-his-rc-write fn-his-put-apart-from-cursors fn-his-put-apart-subrange
                           fn-his-rc-write-position fn-his-rc-write-page-monotone reverse len floor)))))

(defun fn-his-cursors-apart (cells rcs starts)
 (declare (xargs :guard t))
 (if (atom cells) (and (null cells) (null rcs) (null starts))
  (and (consp rcs) (consp starts) (fn-his-rcp (car rcs)) (natp (car starts))
       (fn-his-put-apart-from-cursors
        (* 2048 (+ (car starts) (car (car rcs))))
        (append (reverse (caddr (car rcs))) (car cells))
        (cdr cells) (cdr rcs) (cdr starts))
       (fn-his-cursors-apart (cdr cells) (cdr rcs) (cdr starts)))))

(def-loop fn-his-merged-blocks (cells rcs starts)
 :shape :step :over (cells rcs starts) :done (atom cells)
 :body (cons (* 2048 (+ (car starts) (car (car rcs))))
             (append (reverse (caddr (car rcs))) (car cells)))
 :next ((cdr cells) (cdr rcs) (cdr starts))
 :guard (fn-his-cursors-apart cells rcs starts)
 :guard-hints (("Goal" :in-theory (disable fn-his-put-apart-from-cursors))))

(defthm fn-his-merged-write-ready
 (implies (and (fn-hp-u64-listp ws) (fn-hp-u64-listp (caddr rc))
               (fn-his-rc-fitp (len ws) rc start (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
  (let ((j (* 2048 (+ start (car rc)))) (merged (append (reverse (caddr rc)) ws)))
   (and (fn-hp-u64-listp merged)
        (<= (+ j (len merged)) (pgs-w-length pgs-mem))
        (or (atom merged) (< (floor (+ j (len merged) -1) 2048) (pgs-d-length pgs-mem))))))
 :hints (("Goal" :do-not-induct t
          :cases ((equal (len (append (reverse (caddr rc)) ws)) 0))
          :in-theory (e/d (fn-his-rc-fitp fn-his-rcp)
                          (floor fn-hp-u64-listp reverse len)))))

(local
 (defthm fn-his-empty-list-by-length
  (implies (true-listp x) (equal (equal (len x) 0) (equal x nil)))
  :hints (("Goal" :expand ((len x) (true-listp x))))))

(defthm fn-his-flush-cons
 (implies (fn-his-rcp rc)
  (equal (fn-his-rcs-flush-write (cons rc rcs) (cons start starts) pgs-mem)
         (fn-his-rcs-flush-write rcs starts
          (fn-hp-x-put (* 2048 (+ start (car rc))) (reverse (caddr rc)) pgs-mem))))
 :hints (("Goal" :do-not-induct t :expand ((fn-his-rcs-flush-write (cons rc rcs) (cons start starts) pgs-mem))
          :in-theory (e/d (fn-his-rcp len true-listp)
                          (fn-his-rcs-flush-write fn-hp-x-put)))))

(defthm fn-his-rcs-flush-moves-disjoint-put-before-write
 (implies (and (natp j) (fn-his-put-apart-from-cursors j ys cells rcs starts))
  (equal
   (fn-his-rcs-flush-write (mv-nth 0 (fn-his-rcs-write cells rcs starts pgs-mem)) starts
    (fn-hp-x-put j ys (mv-nth 1 (fn-his-rcs-write cells rcs starts pgs-mem))))
   (fn-his-rcs-flush-write
    (mv-nth 0 (fn-his-rcs-write cells rcs starts (fn-hp-x-put j ys pgs-mem))) starts
    (mv-nth 1 (fn-his-rcs-write cells rcs starts (fn-hp-x-put j ys pgs-mem))))))
 :hints (("Goal"
          :use (fn-his-rcs-write-commutes-with-disjoint-put
                (:instance fn-his-rcs-write-cursors-independent
                  (mem1 pgs-mem) (mem2 (fn-hp-x-put j ys pgs-mem))))
          :in-theory (disable fn-his-rcs-write fn-hp-x-put fn-his-rcs-flush-write
                              fn-his-put-apart-from-cursors))))

(defthm fn-his-merged-write-keeps-lengths
 (implies (and (fn-hp-u64-listp ws) (fn-hp-u64-listp (caddr rc))
               (fn-his-rc-fitp (len ws) rc start (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
  (let ((mem (fn-hp-x-put (* 2048 (+ start (car rc))) (append (reverse (caddr rc)) ws) pgs-mem)))
   (and (equal (pgs-w-length mem) (pgs-w-length pgs-mem))
        (equal (pgs-d-length mem) (pgs-d-length pgs-mem)))))
 :hints (("Goal" :use fn-his-merged-write-ready
          :in-theory (e/d (fn-his-rc-fitp fn-his-rcp)
                          (fn-hp-x-put reverse len floor fn-hp-u64-listp)))))

(defthm fn-his-flush-empty-by-definition
  (implies (atom rcs) (equal (fn-his-rcs-flush-write rcs starts pgs-mem) pgs-mem))
  :hints (("Goal" :in-theory (enable fn-his-rcs-flush-write))))

(local
 (defun-nx fn-his-rcs-materialize-ind (cells rcs starts mem)
  (declare (xargs :guard (fn-his-cursors-apart cells rcs starts) :verify-guards t
                  :guard-hints (("Goal" :in-theory (disable fn-his-put-apart-from-cursors)))))
  (if (atom cells) mem
   (fn-his-rcs-materialize-ind (cdr cells) (cdr rcs) (cdr starts)
    (ec-call (fn-hp-x-put (* 2048 (+ (car starts) (car (car rcs))))
                          (append (reverse (caddr (car rcs))) (car cells)) mem))))))

(defthm fn-his-rcp-fields
  (implies (fn-his-rcp rc)
   (and (natp (car rc)) (natp (cadr rc)) (true-listp (caddr rc))
        (equal (len (caddr rc)) (cadr rc))))
  :hints (("Goal" :in-theory (enable fn-his-rcp)))
  :rule-classes :forward-chaining)

(defthm fn-his-flush-consp
 (implies (and (consp rcs) (consp starts) (fn-his-rcp (car rcs)))
  (equal (fn-his-rcs-flush-write rcs starts pgs-mem)
         (fn-his-rcs-flush-write (cdr rcs) (cdr starts)
          (fn-hp-x-put (* 2048 (+ (car starts) (car (car rcs))))
                       (reverse (caddr (car rcs))) pgs-mem))))
 :hints (("Goal" :use ((:instance fn-his-flush-cons (rc (car rcs)) (rcs (cdr rcs))
                                    (start (car starts)) (starts (cdr starts))))
          :in-theory (disable fn-his-rcs-flush-write fn-his-flush-cons fn-hp-x-put fn-his-rcp))))

(defthm fn-his-rcs-materialize-step
 (implies (and (consp cells) (true-listp (car cells))
               (fn-his-cursors-apart cells rcs starts))
  (let* ((all (fn-his-rcs-write cells rcs starts pgs-mem))
         (head (fn-hp-x-put (* 2048 (+ (car starts) (car (car rcs))))
                            (append (reverse (caddr (car rcs))) (car cells)) pgs-mem))
         (rest (fn-his-rcs-write (cdr cells) (cdr rcs) (cdr starts) head)))
   (equal (fn-his-rcs-flush-write (mv-nth 0 all) starts (mv-nth 1 all))
          (fn-his-rcs-flush-write (mv-nth 0 rest) (cdr starts) (mv-nth 1 rest)))))
 :hints (("Goal" :do-not-induct t
          :expand ((fn-his-rcs-write cells rcs starts pgs-mem)
                   (fn-his-cursors-apart cells rcs starts))
          :use ((:instance fn-his-rc-write-position (ws (car cells)) (rc (car rcs)) (start (car starts)))
                (:instance fn-his-rc-write-materializes (ws (car cells)) (rc (car rcs)) (start (car starts)))
                (:instance fn-his-pending-write-apart
                  (ws (car cells)) (rc (car rcs)) (start (car starts))
                  (cells (cdr cells)) (rcs (cdr rcs)) (starts (cdr starts)))
                (:instance fn-his-rcs-flush-moves-disjoint-put-before-write
                  (j (* 2048 (+ (car starts)
                                (car (mv-nth 0 (fn-his-rc-write (car cells) (car rcs) (car starts) pgs-mem))))))
                  (ys (reverse (caddr (mv-nth 0 (fn-his-rc-write (car cells) (car rcs) (car starts) pgs-mem)))))
                  (cells (cdr cells)) (rcs (cdr rcs)) (starts (cdr starts))
                  (pgs-mem (mv-nth 1 (fn-his-rc-write (car cells) (car rcs) (car starts) pgs-mem)))))
          :in-theory (disable fn-his-rc-write fn-his-rcs-write fn-his-rcs-flush-write
                              fn-his-cursors-apart fn-his-put-apart-from-cursors fn-his-rcp
                              fn-hp-x-put fn-his-put-append reverse len floor))))

(defthm fn-his-rcs-write-materializes
 (implies
  (and (fn-his-cellsp cells) (fn-his-cursors-apart cells rcs starts)
       (fn-his-rcs-fitp cells rcs starts (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
  (let ((res (fn-his-rcs-write cells rcs starts pgs-mem)))
   (equal (fn-his-rcs-flush-write (mv-nth 0 res) starts (mv-nth 1 res))
          (fn-hp-x-put-blocks (fn-his-merged-blocks cells rcs starts) pgs-mem))))
 :hints (("Goal" :induct (fn-his-rcs-materialize-ind cells rcs starts pgs-mem)
          :in-theory (e/d (fn-his-merged-blocks fn-his-cursors-apart fn-hp-x-put-blocks)
                          (fn-his-rcs-write fn-his-rc-write fn-his-rcp fn-his-rc-fitp
                           fn-his-rcs-flush-write fn-hp-x-put fn-his-put-apart-from-cursors
                           fn-his-put-append floor)))
         ("Subgoal *1/1" :in-theory (enable fn-his-rcs-write))
         ("Subgoal *1/2"
          :use ((:instance fn-his-rcs-materialize-step)
                (:instance fn-his-merged-write-ready (ws (car cells)) (rc (car rcs)) (start (car starts)))
                (:instance fn-his-merged-write-keeps-lengths (ws (car cells)) (rc (car rcs)) (start (car starts)))))))

