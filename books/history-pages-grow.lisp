; fn: the history's growth step over a placed image (lanes arena-store-3/-4,
; 2026-09-28).  Prefix fn-hp-.
;
; KEYSTONE (model) fn-hp-piw-relocated: moving region R of the placed image
; at STARTS in NP pages to page TT >= NP of an image grown to NPN pages is
; three block writes -- the header's words 6-18 (the new region table and
; NPAGES), R's old pages zeroed, R's padded words at TT -- over the old
; image extended with zero pages, and the result is the placed image at the
; new starts.  FNADTSN2's free placement (books/proto/adt-bytes.lisp,
; adt-placement-ok) is what lets a region move without moving the others.
(in-package "ACL2")
(include-book "history-pages-placed-write")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable floor mod pgs-true-list-fix-when-true-listp pgs-ptab-p-true-listp fn-cp-id-length-bound
                           adt-len-region-below-body adt-body append-atom-under-list-equiv pgs-append-assoc
                           fn-hp-lens-col-sizes fn-hp-okp fn-hp-regs)))
(local (defthm fn-hp-consp-when-len-5-w (implies (equal (len x) 5) (consp x))))
(local (defthm fn-hp-len-lens-regs-5-w (equal (len (adt-lens (fn-hp-regs h salt))) 5) :hints (("Goal" :in-theory (disable fn-hp-regs)))))
(local (in-theory (disable fn-hp-consp-when-len-5-w)))
; -----------------------------------------------------------------------------
; D. The growth step: a region moves to new pages; nothing else moves.

; The word at K after any list of replacements: the LAST block holding K.
(defun fn-hp-last-block-at (k blocks)
  (declare (xargs :guard (and (natp k) (alistp blocks))))
  (if (atom blocks) nil
    (or (fn-hp-last-block-at k (cdr blocks))
        (if (and (consp (car blocks)) (fn-hp-in-block k (car blocks))) (car blocks) nil))))

(defthm fn-hp-nth-wreps-last
  (implies (and (natp k) (alistp blocks))
           (equal (nth k (fn-hp-wreps w blocks))
                  (if (fn-hp-last-block-at k blocks)
                      (nth (- k (fn-hp-bj (fn-hp-last-block-at k blocks))) (fn-hp-bw (fn-hp-last-block-at k blocks)))
                    (nth k w))))
  :hints (("Goal" :induct (fn-hp-wreps w blocks)
           :in-theory (disable fn-hp-rep fn-hp-nth-rep-block fn-hp-nth-wreps fn-hp-block-at-member nth))))

(defthm fn-hp-last-block-at-append
  (equal (fn-hp-last-block-at k (append a b))
         (or (fn-hp-last-block-at k b) (fn-hp-last-block-at k a))))

(defthm fn-hp-wreps-append
  (equal (fn-hp-wreps (fn-hp-wreps w a) b) (fn-hp-wreps w (append a b))))

(defthm fn-hp-last-block-at-apart-nil
  (implies (and (fn-hp-block-apart b blocks) (fn-hp-in-block k b))
           (not (fn-hp-last-block-at k blocks)))
  :hints (("Goal" :induct (fn-hp-last-block-at k blocks) :in-theory (disable fn-hp-in-block fn-hp-pair-apart))
          ("Subgoal *1/3" :use ((:instance fn-hp-pair-apart-not-in (c (car blocks)))))))

(defthm fn-hp-last-block-at-apart
  (implies (and (fn-hp-blocks-apart blocks) (alistp blocks))
           (equal (fn-hp-last-block-at k blocks) (fn-hp-block-at k blocks)))
  :hints (("Goal" :induct (fn-hp-block-at k blocks)
           :in-theory (disable fn-hp-in-block fn-hp-pair-apart fn-hp-block-at-member))))

; Which region holds word K.
(defun fn-hp-in-region (k s len)
  (declare (xargs :guard (and (natp k) (natp len))))
  (and (<= (* 2048 (nfix s)) (nfix k)) (< (nfix k) (* 2048 (+ (nfix s) (adt-cap (nfix len)))))))

(defun fn-hp-region-of (k lens starts q)
  ; the first region (counted from Q) whose pages hold word K, or nil
  (declare (xargs :verify-guards nil))
  (if (or (atom lens) (atom starts)) nil
    (if (fn-hp-in-region k (car starts) (car lens)) (nfix q)
      (fn-hp-region-of k (cdr lens) (cdr starts) (+ 1 (nfix q))))))

(defthm fn-hp-region-of-sound
  (implies (fn-hp-region-of k lens starts q)
           (let ((v (fn-hp-region-of k lens starts q)))
             (and (natp v) (<= (nfix q) v) (< v (+ (nfix q) (len lens)))
                  (fn-hp-in-region k (nth (- v (nfix q)) starts) (nth (- v (nfix q)) lens)))))
  :hints (("Goal" :induct (fn-hp-region-of k lens starts q) :in-theory (e/d (nth) (fn-hp-in-region adt-cap))))
  :rule-classes nil)

(defun fn-hp-ri-ind (i starts lens)
  (if (or (zp i) (atom starts)) (list starts lens) (fn-hp-ri-ind (1- i) (cdr starts) (cdr lens))))

(defthm fn-hp-pair-not-in-region
  (implies (and (natp s) (natp c) (natp k) (<= (* 2048 s) k) (< k (* 2048 (+ s c)))
                (fn-hp-in-region k s2 l2)
                (or (zp c) (zp (adt-cap (nfix l2))) (<= (+ s c) (nfix s2)) (<= (+ (nfix s2) (adt-cap (nfix l2))) s)))
           nil)
  :hints (("Goal" :in-theory (disable adt-cap)))
  :rule-classes nil)

(defthm fn-hp-apart-not-in-region
  (implies (and (adt-apart s c starts lens) (natp s) (natp c) (natp k) (<= (* 2048 s) k) (< k (* 2048 (+ s c)))
                (natp i) (< i (len starts)) (< i (len lens))
                (fn-hp-in-region k (nth i starts) (nth i lens)))
           nil)
  :hints (("Goal" :induct (fn-hp-ri-ind i starts lens) :expand ((adt-apart s c starts lens))
           :in-theory (e/d (nth) (adt-cap fn-hp-in-region)))
          ("Subgoal *1/1" :use ((:instance fn-hp-pair-not-in-region (s2 (car starts)) (l2 (car lens))))))
  :rule-classes nil)

(defun fn-hp-ru-ind (q starts lens q0)
  (if (or (zp q) (atom starts)) (list starts lens q0) (fn-hp-ru-ind (1- q) (cdr starts) (cdr lens) (+ 1 (nfix q0)))))

(defthm fn-hp-region-of-unique
  (implies (and (adt-placement-ok starts lens np) (natp q) (< q (len lens)) (< q (len starts)) (natp k)
                (fn-hp-in-region k (nth q starts) (nth q lens)))
           (equal (fn-hp-region-of k lens starts q0) (+ (nfix q0) q)))
  :hints (("Goal" :induct (fn-hp-ru-ind q starts lens q0)
           :expand ((fn-hp-region-of k lens starts q0) (adt-placement-ok starts lens np))
           :in-theory (e/d (nth) (adt-cap fn-hp-in-region adt-apart adt-placement-ok)))
          ("Subgoal *1/2" :use ((:instance fn-hp-apart-not-in-region (s (car starts)) (c (adt-cap (nfix (car lens))))
                                           (starts (cdr starts)) (lens (cdr lens)) (i (1- q))))
           :expand ((fn-hp-in-region k (car starts) (car lens)) (fn-hp-region-of k lens starts q0)
                    (adt-placement-ok starts lens np)))))

(defthm fn-hp-in-block-rblock-is-in-region
  (implies (natp k)
           (equal (fn-hp-in-block k (cons (* 2048 (nfix s)) (fn-hp-wpad r)))
                  (fn-hp-in-region k s (len r))))
  :hints (("Goal" :in-theory (disable fn-hp-wpad adt-cap))))

(defun fn-hp-rrq-ind (regs starts q0)
  (if (or (atom regs) (atom starts)) (list regs starts q0) (fn-hp-rrq-ind (cdr regs) (cdr starts) (+ 1 (nfix q0)))))

(defthm fn-hp-block-at-rblocks-none
  (implies (and (natp k) (not (fn-hp-region-of k (adt-lens regs) starts q0)))
           (not (fn-hp-block-at k (fn-hp-rblocks regs starts))))
  :hints (("Goal" :induct (fn-hp-rrq-ind regs starts q0)
           :in-theory (disable fn-hp-wpad adt-cap fn-hp-in-block fn-hp-in-region nfix))))

(local
 (defthm fn-hp-nth-adt-lens-g
   (implies (and (natp q) (< q (len regs))) (equal (nth q (adt-lens regs)) (len (nth q regs))))
   :hints (("Goal" :in-theory (enable nth)))))

(defun fn-hp-nz-ind (k m) (if (or (zp k) (zp m)) (list k m) (fn-hp-nz-ind (1- k) (1- m))))

(defthm fn-hp-nth-zeros
  (implies (and (natp k) (< k (nfix m))) (equal (nth k (adt-zeros m)) 0))
  :hints (("Goal" :induct (fn-hp-nz-ind k m) :in-theory (enable nth adt-zeros))))

(defthm fn-hp-block-at-rblocks-region
  (implies (and (natp k) (natp q0))
           (equal (fn-hp-block-at k (fn-hp-rblocks regs starts))
                  (if (fn-hp-region-of k (adt-lens regs) starts q0)
                      (nth (- (fn-hp-region-of k (adt-lens regs) starts q0) q0) (fn-hp-rblocks regs starts))
                    nil)))
  :hints (("Goal" :induct (fn-hp-rrq-ind regs starts q0)
           :in-theory (e/d (nfix) (fn-hp-wpad adt-cap fn-hp-in-block fn-hp-in-region)))
          ("Subgoal *1/2" :in-theory (disable fn-hp-wpad adt-cap fn-hp-in-block fn-hp-in-region nfix)
           :use ((:instance fn-hp-region-of-sound (lens (adt-lens (cdr regs))) (starts (cdr starts)) (q (+ 1 q0))))))
  :rule-classes nil)

(defthm fn-hp-nth-wreps-hdr
  (implies (and (natp k) (fn-hp-block-apart (cons 0 hdr) rb) (fn-hp-blocks-apart rb))
           (equal (nth k (fn-hp-wreps w (cons (cons 0 hdr) rb)))
                  (cond ((< k (len hdr)) (nth k hdr))
                        ((fn-hp-block-at k rb) (nth (- k (fn-hp-bj (fn-hp-block-at k rb))) (fn-hp-bw (fn-hp-block-at k rb))))
                        (t (nth k w)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-nth-wreps (blocks (cons (cons 0 hdr) rb))))
           :expand ((fn-hp-block-at k (cons (cons 0 hdr) rb)) (fn-hp-blocks-apart (cons (cons 0 hdr) rb)))
           :in-theory (disable fn-hp-nth-wreps fn-hp-wreps fn-hp-block-at fn-hp-block-apart fn-hp-blocks-apart)))
  :rule-classes nil)

; The placed image's word at K, by what holds K.
(defthm fn-hp-piw-word
  (implies (and (adt-placement-ok starts (fn-hp-lens h salt) np) (equal (len starts) 5) (natp k) (< k (* 2048 np)))
           (equal (nth k (fn-hp-piw h salt starts np))
                  (cond ((< k 2048) (nth k (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np)))
                        ((fn-hp-region-of k (fn-hp-lens h salt) starts 0)
                         (nth (- k (* 2048 (nth (fn-hp-region-of k (fn-hp-lens h salt) starts 0) starts)))
                              (fn-hp-wpad (nth (fn-hp-region-of k (fn-hp-lens h salt) starts 0) (fn-hp-regs h salt)))))
                        (t 0))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-nth-wreps-hdr (w (adt-zeros (* 2048 (nfix np))))
                            (hdr (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))
                            (rb (fn-hp-rblocks (fn-hp-regs h salt) starts)))
                 (:instance fn-hp-rblocks-apart (regs (fn-hp-regs h salt)))
                 (:instance fn-hp-hdr-apart-rblocks (regs (fn-hp-regs h salt))
                            (hdr (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np)))
                 (:instance fn-hp-block-at-rblocks-region (regs (fn-hp-regs h salt)) (q0 0))
                 (:instance fn-hp-region-of-sound (lens (fn-hp-lens h salt)) (q 0))
                 (:instance fn-hp-nth-rblocks (regs (fn-hp-regs h salt)) (r (fn-hp-region-of k (fn-hp-lens h salt) starts 0)))
                 (:instance fn-hp-placement-natp-start (lens (fn-hp-lens h salt))
                            (r (fn-hp-region-of k (fn-hp-lens h salt) starts 0)))
                 (:instance fn-hp-nth-zeros (m (* 2048 (nfix np))))
                 (:instance fn-hp-placement-np-pos (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-consp-when-len-5-w (x (adt-lens (fn-hp-regs h salt))))
                 (:instance fn-hp-consp-when-len-5-w (x starts)))
           :in-theory (e/d (fn-hp-piw fn-hp-lens)
                           (fn-hp-nth-wreps fn-hp-rblocks-apart fn-hp-hdr-apart-rblocks fn-hp-block-at-member
                            fn-hp-nth-rblocks fn-hp-nth-zeros fn-hp-block-at-rblocks-none fn-hp-wreps fn-hp-rblocks fn-hp-hdr2
                            fn-hp-regs adt-placement-ok fn-hp-block-apart fn-hp-blocks-apart fn-hp-wpad adt-cap fn-hp-in-region
                            fn-hp-region-of fn-hp-block-at fn-hp-consp-when-len-5-w adt-len-region-below-body adt-body append-atom-under-list-equiv pgs-append-assoc fn-hp-region-of-unique)))))

(local
 (defthm fn-hp-nth-append-g
   (implies (natp k)
            (equal (nth k (append a b)) (if (< k (len a)) (nth k a) (nth (- k (len a)) b))))
   :hints (("Goal" :in-theory (enable nth) :induct (nth k a)))))

(defun fn-hp-hdr-a ()
  (declare (xargs :guard t))
  (append (list *fn-hp-magic-word* *adt-version*) *fn-hp-schema-words*))

(defthm fn-hp-len-hdr-a (equal (len (fn-hp-hdr-a)) 6))

(defun fn-hp-hdr-m (n lens starts np)
  (declare (xargs :guard (and (true-listp starts) (true-listp lens))))
  (list* n 5 (append (fn-hp-meta-words starts lens) (list np))))

(defthm fn-hp-len-hdr-m
  (equal (len (fn-hp-hdr-m n lens starts np)) (+ 3 (* 2 (len starts)))))

(in-theory (disable fn-hp-hdr-a (:e fn-hp-hdr-a) fn-hp-hdr-m))

(defthmd fn-hp-hdr2-parts
  (equal (fn-hp-hdr2 n lens starts np)
         (append (fn-hp-hdr-a) (fn-hp-hdr-m n lens starts np) (adt-zeros 2029)))
  :hints (("Goal" :in-theory (e/d (fn-hp-hdr2 fn-hp-hdr-a fn-hp-hdr-m) ((:e adt-zeros) adt-zeros)))))

(defthm fn-hp-hdr2-relocated-word
  (implies (and (natp k) (< k 2048) (equal (len starts) 5) (equal (len starts2) 5))
           (equal (nth k (fn-hp-hdr2 n lens starts2 npn))
                  (if (and (<= 6 k) (< k 19))
                      (nth (- k 6) (fn-hp-hdr-m n lens starts2 npn))
                    (nth k (fn-hp-hdr2 n lens starts np)))))
  :hints (("Goal" :in-theory (e/d (fn-hp-hdr2-parts) ((:e adt-zeros) adt-zeros fn-hp-hdr2))))
  :rule-classes nil)

(defun fn-hp-reloc-blocks (n lens starts r tt npn wr)
  ; the writes that move region R (its words WR) to page TT in an image of
  ; NPN pages: the header's words 6-18, the region's old pages zeroed, its
  ; words at TT
  (declare (xargs :guard (and (true-listp lens) (true-listp starts) (natp r) (natp tt) (true-listp wr))))
  (list (cons 6 (fn-hp-hdr-m n lens (update-nth r tt starts) npn))
        (cons (* 2048 (nfix (nth r starts))) (adt-zeros (* 2048 (adt-cap (nfix (nth r lens))))))
        (cons (* 2048 tt) wr)))

; The relocation, word by word.
(defmacro fn-hp-reloc-rhs ()
  '(fn-hp-wreps (append (fn-hp-piw h salt s np) (adt-zeros (* 2048 (- npn np))))
                (fn-hp-reloc-blocks (len h) (fn-hp-lens h salt) s r tt npn
                                    (fn-hp-wpad (nth r (fn-hp-regs h salt))))))

(defmacro fn-hp-reloc-hyps ()
  '(and (adt-placement-ok s (fn-hp-lens h salt) np) (adt-placement-ok (update-nth r tt s) (fn-hp-lens h salt) npn)
        (natp np) (natp npn) (<= np npn) (natp tt) (<= np tt) (equal (len s) 5) (natp r) (< r 5)
        (natp k) (< k (* 2048 npn))))

(defthm fn-hp-len-piw
   (implies (and (adt-placement-ok s (fn-hp-lens h salt) np) (equal (len s) 5) (natp np))
            (equal (len (fn-hp-piw h salt s np)) (* 2048 np)))
   :hints (("Goal" :use ((:instance fn-hp-len-wreps (w (adt-zeros (* 2048 (nfix np))))
                                    (blocks (cons (cons 0 (fn-hp-hdr2 (len h) (fn-hp-lens h salt) s np))
                                                  (fn-hp-rblocks (fn-hp-regs h salt) s))))
                         (:instance fn-hp-rblocks-within (regs (fn-hp-regs h salt)) (starts s))
                         (:instance fn-hp-placement-np-pos (starts s) (lens (fn-hp-lens h salt)))
                         (:instance fn-hp-consp-when-len-5-w (x (adt-lens (fn-hp-regs h salt))))
                         (:instance fn-hp-consp-when-len-5-w (x s)))
            :in-theory (e/d (fn-hp-piw fn-hp-lens) (fn-hp-len-wreps fn-hp-rblocks-within fn-hp-wreps fn-hp-rblocks
                                                    fn-hp-hdr2 adt-placement-ok fn-hp-regs)))))

(local
 (defthm fn-hp-nth-zeros-2
   (implies (and (natp k) (integerp m) (< k m)) (equal (nth k (adt-zeros m)) 0))
   :hints (("Goal" :use ((:instance fn-hp-nth-zeros)) :in-theory (disable fn-hp-nth-zeros)))))

(defthm fn-hp-reloc-rhs-word
  (implies (fn-hp-reloc-hyps)
           (equal (nth k (fn-hp-reloc-rhs))
                  (cond ((and (<= (* 2048 tt) k) (< k (+ (* 2048 tt) (len (fn-hp-wpad (nth r (fn-hp-regs h salt)))))))
                         (nth (- k (* 2048 tt)) (fn-hp-wpad (nth r (fn-hp-regs h salt)))))
                        ((and (<= (* 2048 (nth r s)) k)
                              (< k (+ (* 2048 (nth r s)) (* 2048 (adt-cap (nfix (nth r (fn-hp-lens h salt))))))))
                         0)
                        ((and (<= 6 k) (< k 19)) (nth (- k 6) (fn-hp-hdr-m (len h) (fn-hp-lens h salt) (update-nth r tt s) npn)))
                        ((< k (* 2048 np)) (nth k (fn-hp-piw h salt s np)))
                        (t 0))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-placement-natp-start (starts s) (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-nth-zeros-2 (k (- k (* 2048 np))) (m (- (* 2048 npn) (* 2048 np)))))
           :in-theory (e/d (fn-hp-reloc-blocks)
                           (fn-hp-piw fn-hp-wpad fn-hp-lens fn-hp-regs adt-placement-ok fn-hp-hdr-m adt-cap
                            fn-hp-nth-wreps fn-hp-nth-rep-block)))))

(local
 (defthm fn-hp-len-wpad-nth
   (implies (and (natp r) (< r (len regs)))
            (equal (len (fn-hp-wpad (nth r regs))) (* 2048 (adt-cap (nth r (adt-lens regs))))))
   :hints (("Goal" :in-theory (disable fn-hp-wpad adt-cap)))))

(defthm fn-hp-reloc-region-of
  (implies (and (adt-placement-ok s lens np) (adt-placement-ok (update-nth r tt s) lens npn)
                (natp tt) (<= np tt) (equal (len s) 5) (equal (len lens) 5) (natp r) (< r 5) (natp k))
           (equal (fn-hp-region-of k lens (update-nth r tt s) 0)
                  (cond ((fn-hp-in-region k tt (nth r lens)) r)
                        ((fn-hp-in-region k (nth r s) (nth r lens)) nil)
                        (t (fn-hp-region-of k lens s 0)))))
  :hints (("Goal" :do-not-induct t
           :cases ((fn-hp-in-region k tt (nth r lens)) (fn-hp-in-region k (nth r s) (nth r lens)))
           :use ((:instance fn-hp-region-of-unique (starts (update-nth r tt s)) (np npn) (q r) (q0 0))
                 (:instance fn-hp-region-of-unique (starts s) (q r) (q0 0))
                 (:instance fn-hp-region-of-sound (starts (update-nth r tt s)) (q 0))
                 (:instance fn-hp-region-of-sound (starts s) (q 0))
                 (:instance fn-hp-region-of-unique (starts s) (q0 0)
                            (q (fn-hp-region-of k lens (update-nth r tt s) 0)))
                 (:instance fn-hp-region-of-unique (starts (update-nth r tt s)) (np npn) (q0 0)
                            (q (fn-hp-region-of k lens s 0))))
           :in-theory (disable fn-hp-region-of-unique fn-hp-region-of adt-placement-ok fn-hp-in-region))))

(local (in-theory (disable fn-hp-piw fn-hp-nth-wreps fn-hp-nth-wreps-outside fn-hp-nth-wreps-last fn-hp-block-at-member
                           fn-hp-blocks-apart fn-hp-block-apart fn-hp-pair-apart)))

(defthm fn-hp-reloc-word-hdr
  (implies (and (fn-hp-reloc-hyps) (< k 2048))
           (equal (nth k (fn-hp-piw h salt (update-nth r tt s) npn)) (nth k (fn-hp-reloc-rhs))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-placement-natp-start (starts s) (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-placement-np-pos (starts s) (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-piw-word (starts (update-nth r tt s)) (np npn))
                 (:instance fn-hp-piw-word (starts s))
                 (:instance fn-hp-reloc-rhs-word)
                 (:instance fn-hp-hdr2-relocated-word (n (len h)) (lens (fn-hp-lens h salt)) (starts s)
                            (starts2 (update-nth r tt s))))
           :in-theory (e/d (fn-hp-lens)
                           (fn-hp-piw-word fn-hp-reloc-rhs-word fn-hp-region-of fn-hp-wpad
                            fn-hp-regs adt-placement-ok fn-hp-hdr-m adt-cap fn-hp-hdr2 fn-hp-reloc-blocks fn-hp-wreps)))))

; The LHS by cases (the placed image at the new starts).
(defthm fn-hp-reloc-lhs-word
  (implies (and (fn-hp-reloc-hyps) (<= 2048 k))
           (equal (nth k (fn-hp-piw h salt (update-nth r tt s) npn))
                  (cond ((fn-hp-in-region k tt (nth r (fn-hp-lens h salt)))
                         (nth (- k (* 2048 tt)) (fn-hp-wpad (nth r (fn-hp-regs h salt)))))
                        ((fn-hp-in-region k (nth r s) (nth r (fn-hp-lens h salt))) 0)
                        ((fn-hp-region-of k (fn-hp-lens h salt) s 0)
                         (nth (- k (* 2048 (nth (fn-hp-region-of k (fn-hp-lens h salt) s 0) s)))
                              (fn-hp-wpad (nth (fn-hp-region-of k (fn-hp-lens h salt) s 0) (fn-hp-regs h salt)))))
                        (t 0))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-reloc-region-of (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-region-of-sound (starts s) (lens (fn-hp-lens h salt)) (q 0))
                 (:instance fn-hp-piw-word (starts (update-nth r tt s)) (np npn)))
           :in-theory (e/d (fn-hp-lens) (fn-hp-reloc-region-of fn-hp-piw-word fn-hp-region-of fn-hp-wpad fn-hp-regs
                                         adt-placement-ok adt-cap fn-hp-in-region fn-hp-hdr2)))))

; The RHS by the same cases.
(defthm fn-hp-reloc-rhs-word-2
  (implies (and (fn-hp-reloc-hyps) (<= 2048 k))
           (equal (nth k (fn-hp-reloc-rhs))
                  (cond ((fn-hp-in-region k tt (nth r (fn-hp-lens h salt)))
                         (nth (- k (* 2048 tt)) (fn-hp-wpad (nth r (fn-hp-regs h salt)))))
                        ((fn-hp-in-region k (nth r s) (nth r (fn-hp-lens h salt))) 0)
                        ((fn-hp-region-of k (fn-hp-lens h salt) s 0)
                         (nth (- k (* 2048 (nth (fn-hp-region-of k (fn-hp-lens h salt) s 0) s)))
                              (fn-hp-wpad (nth (fn-hp-region-of k (fn-hp-lens h salt) s 0) (fn-hp-regs h salt)))))
                        (t 0))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-reloc-rhs-word)
                 (:instance fn-hp-piw-word (starts s))
                 (:instance fn-hp-placement-natp-start (starts s) (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-placement-np-pos (starts s) (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-region-of-sound (starts s) (lens (fn-hp-lens h salt)) (q 0))
                 (:instance fn-hp-placement-natp-start (starts s) (lens (fn-hp-lens h salt))
                            (r (fn-hp-region-of k (fn-hp-lens h salt) s 0)))
                 (:instance fn-hp-len-wpad-nth (regs (fn-hp-regs h salt))))
           :in-theory (e/d (fn-hp-lens fn-hp-in-region)
                           (fn-hp-reloc-rhs-word fn-hp-piw-word fn-hp-region-of fn-hp-wpad fn-hp-regs adt-placement-ok
                            adt-cap fn-hp-hdr2 fn-hp-reloc-blocks fn-hp-wreps fn-hp-len-wpad-nth fn-hp-hdr-m)))))

(defthm fn-hp-reloc-word
  (implies (fn-hp-reloc-hyps)
           (equal (nth k (fn-hp-piw h salt (update-nth r tt s) npn)) (nth k (fn-hp-reloc-rhs))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-reloc-word-hdr) (:instance fn-hp-reloc-lhs-word) (:instance fn-hp-reloc-rhs-word-2))
           :in-theory (theory 'minimal-theory))))

(defthm fn-hp-true-listp-piw
  (true-listp (fn-hp-piw h salt starts np))
  :hints (("Goal" :in-theory (enable fn-hp-piw))))

(defmacro fn-hp-reloc-hyps0 ()
  '(and (adt-placement-ok s (fn-hp-lens h salt) np) (adt-placement-ok (update-nth r tt s) (fn-hp-lens h salt) npn)
        (natp np) (natp npn) (<= np npn) (natp tt) (<= np tt) (equal (len s) 5) (natp r) (< r 5)))

(local
 (defthm fn-hp-reloc-agree
   (implies (and (fn-hp-reloc-hyps0) (natp a) (<= (+ a n) (* 2048 npn)))
            (fn-hp-agree a n (fn-hp-piw h salt (update-nth r tt s) npn) (fn-hp-reloc-rhs)))
   :hints (("Goal" :induct (fn-hp-agree-ind a n)
            :in-theory (disable fn-hp-piw fn-hp-wreps fn-hp-reloc-blocks fn-hp-reloc-word adt-placement-ok fn-hp-lens))
           ("Subgoal *1/2" :use ((:instance fn-hp-reloc-word (k a)))))))

(defthm fn-hp-reloc-within
  (implies (fn-hp-reloc-hyps0)
           (fn-hp-blocks-within (fn-hp-reloc-blocks (len h) (fn-hp-lens h salt) s r tt npn
                                                    (fn-hp-wpad (nth r (fn-hp-regs h salt))))
                                (* 2048 npn)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-placement-natp-start (starts s) (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-placement-natp-start (starts (update-nth r tt s)) (lens (fn-hp-lens h salt)) (np npn))
                 (:instance fn-hp-len-wpad-nth (regs (fn-hp-regs h salt))))
           :in-theory (e/d (fn-hp-reloc-blocks fn-hp-lens) (fn-hp-wpad fn-hp-regs adt-placement-ok adt-cap
                                                             fn-hp-len-wpad-nth fn-hp-hdr-m)))))

; The growth step's model: moving region R to page TT of an image grown to
; NPN pages writes three blocks, and the result is the placed image at the
; new starts.
(defthm fn-hp-piw-relocated
  (implies (fn-hp-reloc-hyps0)
           (equal (fn-hp-piw h salt (update-nth r tt s) npn) (fn-hp-reloc-rhs)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-equal-by-agree (x (fn-hp-piw h salt (update-nth r tt s) npn)) (y (fn-hp-reloc-rhs)))
                 (:instance fn-hp-reloc-agree (a 0) (n (* 2048 npn)))
                 (:instance fn-hp-len-piw (s (update-nth r tt s)) (np npn))
                 (:instance fn-hp-len-piw)
                 (:instance fn-hp-reloc-within)
                 (:instance fn-hp-len-wreps (w (append (fn-hp-piw h salt s np) (adt-zeros (* 2048 (- npn np)))))
                            (blocks (fn-hp-reloc-blocks (len h) (fn-hp-lens h salt) s r tt npn
                                                        (fn-hp-wpad (nth r (fn-hp-regs h salt)))))))
           :in-theory (disable fn-hp-reloc-agree fn-hp-len-piw fn-hp-reloc-within fn-hp-len-wreps
                               fn-hp-piw fn-hp-wreps fn-hp-reloc-blocks adt-placement-ok fn-hp-lens fn-hp-agree))))
