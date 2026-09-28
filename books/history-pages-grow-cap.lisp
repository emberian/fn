; fn: a placed image viewed with larger caps (lane arena-store-4,
; 2026-09-28).  Prefix fn-hp-.
;
; KEYSTONE (model) fn-hp-piw-caps-extend: the placed image of H at STARTS in
; NP pages is unchanged when each region is padded to the pages of larger
; lengths LENS2 (fn-hp-rblocks-c, fn-hp-wpadc) that are themselves placed at
; STARTS: the words past a region's own cap are zeros either way.  The
; growth step's append (books/history-pages-grow-append.lisp) rewrites the
; old image this way before the nest machinery applies.
(in-package "ACL2")
(include-book "history-pages-grow")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable floor mod pgs-true-list-fix-when-true-listp pgs-ptab-p-true-listp fn-cp-id-length-bound
                           adt-len-region-below-body adt-body append-atom-under-list-equiv pgs-append-assoc
                           fn-hp-lens-col-sizes fn-hp-okp fn-hp-regs)))
; -----------------------------------------------------------------------------
; E. Larger caps: a region padded past its own cap still holds its words,
;    then zeros.

(defun fn-hp-wpadc (r c)
  ; region R's words padded to C pages
  (declare (xargs :verify-guards nil))
  (fn-hp-pack8 (* 2048 (nfix c)) (append r (adt-zeros (- (* 16384 (nfix c)) (len r))))))

(defthm fn-hp-len-wpadc (equal (len (fn-hp-wpadc r c)) (* 2048 (nfix c))))

(defthm fn-hp-true-listp-wpadc (true-listp (fn-hp-wpadc r c)))

(defthm fn-hp-wpadc-cap
  (equal (fn-hp-wpadc r (adt-cap (len r))) (fn-hp-wpad r))
  :hints (("Goal" :in-theory (enable fn-hp-wpad adt-pad))))

(local
 (defthm fn-hp-consp-iff-len-g
   (iff (consp x) (< 0 (len x)))))

(defthm fn-hp-consp-wpadc
  (iff (consp (fn-hp-wpadc r c)) (not (zp c)))
  :hints (("Goal" :use ((:instance fn-hp-len-wpadc) (:instance fn-hp-consp-iff-len-g (x (fn-hp-wpadc r c))))
           :in-theory (disable fn-hp-len-wpadc fn-hp-wpadc fn-hp-consp-iff-len-g))))

(local (in-theory (disable fn-hp-consp-iff-len-g)))

(defun fn-hp-rblocks-c (regs starts lens2)
  ; each region's words padded to the pages LENS2 needs, at its start
  (declare (xargs :verify-guards nil))
  (if (or (atom regs) (atom starts) (atom lens2)) nil
    (cons (cons (* 2048 (nfix (car starts))) (fn-hp-wpadc (car regs) (adt-cap (nfix (car lens2)))))
          (fn-hp-rblocks-c (cdr regs) (cdr starts) (cdr lens2)))))

(defthm fn-hp-in-block-rblock-c-is-in-region
  (implies (natp k)
           (equal (fn-hp-in-block k (cons (* 2048 (nfix s)) (fn-hp-wpadc r (adt-cap (nfix l)))))
                  (fn-hp-in-region k s l)))
  :hints (("Goal" :in-theory (disable fn-hp-wpadc adt-cap))))

(defthm fn-hp-block-apart-empty
  (implies (atom (fn-hp-bw b)) (fn-hp-block-apart b blocks)))

(defthm fn-hp-rblocks-c-apart-of-adt-apart
  (implies (and (adt-apart s c starts lens2) (natp s) (equal c (adt-cap (nfix l))))
           (fn-hp-block-apart (cons (* 2048 s) (fn-hp-wpadc r (adt-cap (nfix l)))) (fn-hp-rblocks-c regs starts lens2)))
  :hints (("Goal" :induct (fn-hp-rblocks-c regs starts lens2) :in-theory (disable adt-cap fn-hp-wpadc))))

(defthm fn-hp-rblocks-c-apart-of-adt-apart-2
  (implies (and (adt-apart s c starts lens2) (natp s) (natp l) (equal c (adt-cap l)))
           (fn-hp-block-apart (cons (* 2048 s) (fn-hp-wpadc r (adt-cap l))) (fn-hp-rblocks-c regs starts lens2)))
  :hints (("Goal" :use ((:instance fn-hp-rblocks-c-apart-of-adt-apart)) :in-theory (disable fn-hp-rblocks-c-apart-of-adt-apart
                                                                                        adt-cap fn-hp-wpadc))))

(defthm fn-hp-rblocks-c-apart
  (implies (adt-placement-ok starts lens2 np)
           (fn-hp-blocks-apart (fn-hp-rblocks-c regs starts lens2)))
  :hints (("Goal" :induct (fn-hp-rblocks-c regs starts lens2) :in-theory (disable adt-cap fn-hp-wpadc))))

(defthm fn-hp-hdr-apart-rblocks-c
  (implies (and (adt-placement-ok starts lens2 np) (equal (len hdr) 2048))
           (fn-hp-block-apart (cons 0 hdr) (fn-hp-rblocks-c regs starts lens2)))
  :hints (("Goal" :induct (fn-hp-rblocks-c regs starts lens2) :in-theory (disable adt-cap fn-hp-wpadc))))

(defun fn-hp-caps-le (lens lens2)
  (declare (xargs :verify-guards nil))
  (if (or (atom lens) (atom lens2)) t
    (and (<= (adt-cap (nfix (car lens))) (adt-cap (nfix (car lens2)))) (fn-hp-caps-le (cdr lens) (cdr lens2)))))

(defthm fn-hp-apart-mono
  (implies (and (adt-apart s c2 starts lens2) (fn-hp-caps-le lens lens2) (equal (len lens) (len lens2)) (natp c) (natp c2) (<= c c2) (natp s))
           (adt-apart s c starts lens))
  :hints (("Goal" :induct (list (adt-apart s c2 starts lens2) (fn-hp-caps-le lens lens2)) :in-theory (disable adt-cap))))

(defthm fn-hp-placement-mono
  (implies (and (adt-placement-ok starts lens2 np) (fn-hp-caps-le lens lens2) (equal (len lens) (len lens2)))
           (adt-placement-ok starts lens np))
  :hints (("Goal" :induct (list (adt-placement-ok starts lens2 np) (fn-hp-caps-le lens lens2)) :in-theory (disable adt-cap))))

(local
 (defthm fn-hp-zeros-plus-g
   (implies (and (natp a) (natp b)) (equal (adt-zeros (+ a b)) (append (adt-zeros a) (adt-zeros b))))
   :hints (("Goal" :induct (adt-zeros a)))))

(local
 (defthm fn-hp-unle-nthcdr-prefix
   (implies (and (natp m) (<= (+ m 8) (len x)))
            (equal (adt-unle 8 (nthcdr m (append x y))) (adt-unle 8 (nthcdr m x))))
   :hints (("Goal" :use ((:instance adt-nthcdr-of-append-less (n m))
                         (:instance adt-unle-append (w 8) (x (nthcdr m x)) (rest y)))
            :in-theory (disable adt-nthcdr-of-append-less adt-unle-append adt-unle)))))

(local
 (defun fn-hp-uz-ind-g (w m) (if (zp w) (list w m) (fn-hp-uz-ind-g (1- w) (1- m)))))

(local
 (defthm fn-hp-unle-zeros-g
   (equal (adt-unle w (adt-zeros m)) 0)
   :hints (("Goal" :induct (fn-hp-uz-ind-g w m) :in-theory (enable adt-unle adt-zeros)))))

(local
 (defun fn-hp-nz-ind-g (m z) (if (or (zp m) (zp z)) (list m z) (fn-hp-nz-ind-g (1- m) (1- z)))))

(local
 (defthm fn-hp-nthcdr-zeros-any
   (implies (natp m) (equal (nthcdr m (adt-zeros z)) (adt-zeros (- (nfix z) m))))
   :hints (("Goal" :induct (fn-hp-nz-ind-g m z) :in-theory (enable nthcdr adt-zeros)))))

(local
 (defthm fn-hp-unle-nthcdr-zeros
   (implies (and (natp m) (<= (len x) m))
            (equal (adt-unle 8 (nthcdr m (append x (adt-zeros z)))) 0))
   :hints (("Goal" :use ((:instance adt-nthcdr-of-append-more (n m) (y (adt-zeros z))))
            :in-theory (disable adt-nthcdr-of-append-more adt-unle)))))

(defthm fn-hp-nth-wpadc
  (implies (and (natp i) (< i (* 2048 (nfix c))) (<= (adt-cap (len r)) (nfix c)) (true-listp r))
           (equal (nth i (fn-hp-wpadc r c))
                  (if (< i (* 2048 (adt-cap (len r)))) (nth i (fn-hp-wpad r)) 0)))
  :hints (("Goal" :do-not-induct t
           :cases ((< i (* 2048 (adt-cap (len r)))))
           :use ((:instance adt-cap-covers (u (len r)))
                 (:instance fn-hp-zeros-plus-g (a (- (* 16384 (adt-cap (len r))) (len r)))
                            (b (- (* 16384 (nfix c)) (* 16384 (adt-cap (len r))))))
                 (:instance fn-hp-unle-nthcdr-prefix (m (* 8 i))
                            (x (append r (adt-zeros (- (* 16384 (adt-cap (len r))) (len r)))))
                            (y (adt-zeros (- (* 16384 (nfix c)) (* 16384 (adt-cap (len r)))))))
                 (:instance fn-hp-unle-nthcdr-zeros (m (* 8 i)) (x r) (z (- (* 16384 (nfix c)) (len r)))))
           :in-theory (e/d (fn-hp-wpad adt-pad fn-hp-wpadc)
                           (adt-cap-covers fn-hp-zeros-plus-g fn-hp-unle-nthcdr-prefix fn-hp-unle-nthcdr-zeros adt-cap
                            adt-unle adt-zeros fn-hp-pack8)))))

(defthm fn-hp-nth-rblocks-c
  (implies (and (natp q) (< q (len regs)) (< q (len starts)) (< q (len lens2)))
           (equal (nth q (fn-hp-rblocks-c regs starts lens2))
                  (cons (* 2048 (nfix (nth q starts))) (fn-hp-wpadc (nth q regs) (adt-cap (nfix (nth q lens2)))))))
  :hints (("Goal" :induct (list (fn-hp-rblocks-c regs starts lens2) (nth q regs))
           :in-theory (e/d (nth) (fn-hp-wpadc adt-cap)))))

(defthm fn-hp-len-rblocks-c
  (implies (and (equal (len starts) (len regs)) (equal (len lens2) (len regs)))
           (equal (len (fn-hp-rblocks-c regs starts lens2)) (len regs))))

(defthm fn-hp-caps-le-nth
  (implies (and (fn-hp-caps-le lens lens2) (natp q) (< q (len lens)) (< q (len lens2)))
           (<= (adt-cap (nfix (nth q lens))) (adt-cap (nfix (nth q lens2)))))
  :hints (("Goal" :induct (list (fn-hp-caps-le lens lens2) (nth q lens)) :in-theory (e/d (nth) (adt-cap))))
  :rule-classes :linear)

(defthm fn-hp-in-region-mono
  (implies (and (fn-hp-in-region k s l) (<= (adt-cap (nfix l)) (adt-cap (nfix l2))))
           (fn-hp-in-region k s l2))
  :hints (("Goal" :in-theory (disable adt-cap))))

(defmacro fn-hp-ext-list ()
  '(cons (cons 0 (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np)) (fn-hp-rblocks-c (fn-hp-regs h salt) starts lens2)))

(defmacro fn-hp-ext-hyps ()
  '(and (adt-placement-ok starts lens2 np) (equal (len starts) 5) (equal (len lens2) 5) (natp np)
        (fn-hp-caps-le (fn-hp-lens h salt) lens2)))

(defun fn-hp-rrc-ind (regs starts lens2 q0)
  (if (or (atom regs) (atom starts) (atom lens2)) (list regs starts lens2 q0)
    (fn-hp-rrc-ind (cdr regs) (cdr starts) (cdr lens2) (+ 1 (nfix q0)))))

(defthm fn-hp-block-at-rblocks-c-region
  (implies (and (natp k) (natp q0) (equal (len lens2) (len regs)))
           (equal (fn-hp-block-at k (fn-hp-rblocks-c regs starts lens2))
                  (if (fn-hp-region-of k lens2 starts q0)
                      (nth (- (fn-hp-region-of k lens2 starts q0) q0) (fn-hp-rblocks-c regs starts lens2))
                    nil)))
  :hints (("Goal" :induct (fn-hp-rrc-ind regs starts lens2 q0)
           :in-theory (e/d (nfix) (fn-hp-wpadc adt-cap fn-hp-in-block fn-hp-in-region)))
          ("Subgoal *1/2" :in-theory (disable fn-hp-wpadc adt-cap fn-hp-in-block fn-hp-in-region nfix)
           :use ((:instance fn-hp-region-of-sound (lens (cdr lens2)) (starts (cdr starts)) (q (+ 1 q0))))))
  :rule-classes nil)

(defthm fn-hp-ext-lhs-word
  (implies (and (fn-hp-ext-hyps) (natp k) (< k (* 2048 np)))
           (equal (nth k (fn-hp-wreps (adt-zeros (* 2048 np)) (fn-hp-ext-list)))
                  (cond ((< k 2048) (nth k (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np)))
                        ((fn-hp-region-of k lens2 starts 0)
                         (nth (- k (* 2048 (nth (fn-hp-region-of k lens2 starts 0) starts)))
                              (fn-hp-wpadc (nth (fn-hp-region-of k lens2 starts 0) (fn-hp-regs h salt))
                                           (adt-cap (nfix (nth (fn-hp-region-of k lens2 starts 0) lens2))))))
                        (t 0))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-nth-wreps-hdr (w (adt-zeros (* 2048 np)))
                            (hdr (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))
                            (rb (fn-hp-rblocks-c (fn-hp-regs h salt) starts lens2)))
                 (:instance fn-hp-rblocks-c-apart (regs (fn-hp-regs h salt)))
                 (:instance fn-hp-hdr-apart-rblocks-c (regs (fn-hp-regs h salt))
                            (hdr (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np)))
                 (:instance fn-hp-block-at-rblocks-c-region (regs (fn-hp-regs h salt)) (q0 0))
                 (:instance fn-hp-region-of-sound (lens lens2) (q 0))
                 (:instance fn-hp-nth-rblocks-c (regs (fn-hp-regs h salt)) (q (fn-hp-region-of k lens2 starts 0)))
                 (:instance fn-hp-nth-zeros (m (* 2048 np)))
                 (:instance fn-hp-placement-natp-start (lens lens2) (r (fn-hp-region-of k lens2 starts 0))))
           :in-theory (e/d (fn-hp-lens)
                           (fn-hp-nth-wreps fn-hp-rblocks-c-apart fn-hp-hdr-apart-rblocks-c fn-hp-block-at-member
                            fn-hp-nth-rblocks-c fn-hp-nth-zeros fn-hp-wreps fn-hp-rblocks-c
                            fn-hp-hdr2 fn-hp-regs adt-placement-ok fn-hp-block-apart fn-hp-blocks-apart fn-hp-wpadc adt-cap
                            fn-hp-in-region fn-hp-region-of fn-hp-block-at fn-hp-caps-le fn-hp-nth-wpadc fn-hp-region-of-unique)))))

(defthm fn-hp-region-of-shrink
  (implies (and (adt-placement-ok starts lens2 np) (fn-hp-caps-le lens lens2) (equal (len lens) (len lens2))
                (equal (len starts) (len lens2)) (natp k))
           (equal (fn-hp-region-of k lens starts 0)
                  (if (and (fn-hp-region-of k lens2 starts 0)
                           (fn-hp-in-region k (nth (fn-hp-region-of k lens2 starts 0) starts)
                                            (nth (fn-hp-region-of k lens2 starts 0) lens)))
                      (fn-hp-region-of k lens2 starts 0)
                    nil)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-placement-mono)
                 (:instance fn-hp-region-of-sound (lens lens2) (q 0))
                 (:instance fn-hp-region-of-sound (q 0))
                 (:instance fn-hp-region-of-unique (q0 0) (q (fn-hp-region-of k lens2 starts 0)))
                 (:instance fn-hp-region-of-unique (lens lens2) (q0 0) (q (fn-hp-region-of k lens starts 0)))
                 (:instance fn-hp-caps-le-nth (q (fn-hp-region-of k lens starts 0)))
                 (:instance fn-hp-in-region-mono (s (nth (fn-hp-region-of k lens starts 0) starts))
                            (l (nth (fn-hp-region-of k lens starts 0) lens))
                            (l2 (nth (fn-hp-region-of k lens starts 0) lens2))))
           :in-theory (disable fn-hp-placement-mono fn-hp-region-of-unique fn-hp-caps-le-nth fn-hp-in-region-mono
                               adt-placement-ok fn-hp-region-of fn-hp-in-region adt-cap fn-hp-caps-le))))

(local
 (defthm fn-hp-nth-adt-lens-c
   (implies (and (natp q) (< q (len regs))) (equal (nth q (adt-lens regs)) (len (nth q regs))))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-hp-true-listp-nth-tll
   (implies (true-list-listp x) (true-listp (nth q x)))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-hp-nth-wpadc-region
  (implies (and (natp k) (natp st) (fn-hp-in-region k st l2) (<= (adt-cap (len r)) (adt-cap (nfix l2))) (true-listp r))
           (equal (nth (- k (* 2048 st)) (fn-hp-wpadc r (adt-cap (nfix l2))))
                  (if (fn-hp-in-region k st (len r)) (nth (- k (* 2048 st)) (fn-hp-wpad r)) 0)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-nth-wpadc (i (- k (* 2048 st))) (c (adt-cap (nfix l2)))))
           :in-theory (disable fn-hp-nth-wpadc fn-hp-wpadc fn-hp-wpad adt-cap))))

(defmacro fn-hp-q2 () '(fn-hp-region-of k lens2 starts 0))

(defthm fn-hp-ext-word-hi
  (implies (and (fn-hp-ext-hyps) (natp k) (< k (* 2048 np)) (<= 2048 k))
           (equal (nth k (fn-hp-wreps (adt-zeros (* 2048 np)) (fn-hp-ext-list)))
                  (nth k (fn-hp-piw h salt starts np))))
  :hints (("Goal" :do-not-induct t
           :cases ((not (fn-hp-q2)) (fn-hp-in-region k (nth (fn-hp-q2) starts) (nth (fn-hp-q2) (fn-hp-lens h salt))))
           :use ((:instance fn-hp-ext-lhs-word)
                 (:instance fn-hp-piw-word)
                 (:instance fn-hp-placement-mono (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-region-of-shrink (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-region-of-sound (lens lens2) (q 0))
                 (:instance fn-hp-caps-le-nth (lens (fn-hp-lens h salt)) (q (fn-hp-q2)))
                 (:instance fn-hp-nth-wpadc-region (r (nth (fn-hp-q2) (fn-hp-regs h salt)))
                            (l2 (nth (fn-hp-q2) lens2)) (st (nth (fn-hp-q2) starts)))
                 (:instance fn-hp-placement-natp-start (lens lens2) (r (fn-hp-q2)))
                 (:instance fn-hp-nth-adt-lens-c (regs (fn-hp-regs h salt)) (q (fn-hp-q2))))
           :in-theory (e/d (fn-hp-lens)
                           (fn-hp-ext-lhs-word fn-hp-piw-word fn-hp-placement-mono fn-hp-region-of-shrink
                            fn-hp-caps-le-nth fn-hp-nth-wpadc fn-hp-nth-wpadc-region fn-hp-wreps fn-hp-rblocks-c fn-hp-hdr2 fn-hp-regs
                            adt-placement-ok fn-hp-wpadc fn-hp-wpad adt-cap fn-hp-region-of fn-hp-caps-le fn-hp-piw
                            fn-hp-nth-adt-lens-c fn-hp-region-of-unique fn-hp-nth-wreps fn-hp-nth-wreps-last fn-hp-nth-wreps-outside fn-hp-in-region)))))

(defthm fn-hp-ext-word
  (implies (and (fn-hp-ext-hyps) (natp k) (< k (* 2048 np)))
           (equal (nth k (fn-hp-wreps (adt-zeros (* 2048 np)) (fn-hp-ext-list)))
                  (nth k (fn-hp-piw h salt starts np))))
  :hints (("Goal" :do-not-induct t :cases ((< k 2048))
           :use ((:instance fn-hp-ext-lhs-word) (:instance fn-hp-piw-word) (:instance fn-hp-ext-word-hi)
                 (:instance fn-hp-placement-mono (lens (fn-hp-lens h salt))))
           :in-theory (e/d (fn-hp-lens)
                           (fn-hp-ext-lhs-word fn-hp-piw-word fn-hp-ext-word-hi fn-hp-placement-mono
                            fn-hp-wreps fn-hp-rblocks-c fn-hp-hdr2 fn-hp-regs adt-placement-ok fn-hp-wpadc fn-hp-wpad
                            adt-cap fn-hp-region-of fn-hp-caps-le fn-hp-piw fn-hp-region-of-unique fn-hp-nth-wreps
                            fn-hp-nth-wreps-last fn-hp-nth-wreps-outside fn-hp-in-region)))))

(defthm fn-hp-rblocks-c-within
  (implies (adt-placement-ok starts lens2 np)
           (fn-hp-blocks-within (fn-hp-rblocks-c regs starts lens2) (* 2048 np)))
  :hints (("Goal" :induct (fn-hp-rblocks-c regs starts lens2) :in-theory (disable adt-cap fn-hp-wpadc))))

(local
 (defthm fn-hp-ext-agree
   (implies (and (fn-hp-ext-hyps) (natp a) (<= (+ a n) (* 2048 np)))
            (fn-hp-agree a n (fn-hp-wreps (adt-zeros (* 2048 np)) (fn-hp-ext-list)) (fn-hp-piw h salt starts np)))
   :hints (("Goal" :induct (fn-hp-agree-ind a n)
            :in-theory (disable fn-hp-piw fn-hp-wreps fn-hp-rblocks-c fn-hp-ext-word adt-placement-ok fn-hp-lens fn-hp-hdr2
                                fn-hp-regs fn-hp-caps-le fn-hp-nth-wreps fn-hp-nth-wreps-last fn-hp-nth-wreps-outside
                                fn-hp-piw-word fn-hp-ext-lhs-word fn-hp-ext-word-hi adt-zeros))
           ("Subgoal *1/2" :use ((:instance fn-hp-ext-word (k a)))))))

; The image viewed with larger caps is the same image: a region's pages past
; its own cap hold zeros either way.
(defthm fn-hp-piw-caps-extend
  (implies (fn-hp-ext-hyps)
           (equal (fn-hp-piw h salt starts np)
                  (fn-hp-wreps (adt-zeros (* 2048 np)) (fn-hp-ext-list))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-equal-by-agree (x (fn-hp-wreps (adt-zeros (* 2048 np)) (fn-hp-ext-list)))
                            (y (fn-hp-piw h salt starts np)))
                 (:instance fn-hp-ext-agree (a 0) (n (* 2048 np)))
                 (:instance fn-hp-len-piw (s starts))
                 (:instance fn-hp-placement-mono (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-rblocks-c-within (regs (fn-hp-regs h salt)))
                 (:instance fn-hp-placement-np-pos (lens lens2))
                 (:instance fn-hp-len-wreps (w (adt-zeros (* 2048 np))) (blocks (fn-hp-ext-list))))
           :in-theory (disable fn-hp-ext-agree fn-hp-len-piw fn-hp-rblocks-c-within fn-hp-len-wreps fn-hp-placement-mono
                               fn-hp-piw fn-hp-wreps fn-hp-rblocks-c adt-placement-ok fn-hp-lens fn-hp-agree fn-hp-hdr2
                               fn-hp-regs fn-hp-caps-le))))
