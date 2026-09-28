; fn: the history's append over a placed image whose regions grow (lane
; arena-store-4, 2026-09-28).  Prefix fn-hp-.
;
; KEYSTONE (model) fn-hp-piw-of-append1-grown: the append model of
; books/history-pages-placed-write.lisp (fn-hp-piw-of-append1) without its
; cap-equality: when the appended history's lengths are placed at STARTS in
; NP pages -- each region's pages [start, start + new cap) free -- the
; appended history's placed image is the old placed image with the six
; blocks of fn-hp-pblocks in place.  The route: view the old image with the
; new caps (fn-hp-piw-caps-extend, books/history-pages-grow-cap.lisp), then
; the nest machinery (books/history-pages-nest.lisp) over the triples
; fn-hp-rtriples-c, whose outer blocks are padded to the new caps.
(in-package "ACL2")
(include-book "history-pages-grow-cap")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable floor mod pgs-true-list-fix-when-true-listp pgs-ptab-p-true-listp fn-cp-id-length-bound
                           adt-len-region-below-body adt-body append-atom-under-list-equiv pgs-append-assoc
                           fn-hp-lens-col-sizes fn-hp-okp fn-hp-regs)))
; -----------------------------------------------------------------------------
; F. Caps only grow with the lengths.

(local
 (defthm fn-hp-pow2-at-least-mono
   (implies (and (natp k) (natp k2) (<= k k2) (posp acc))
            (<= (adt-pow2-at-least k acc) (adt-pow2-at-least k2 acc)))
   :hints (("Goal" :induct (adt-pow2-at-least k2 acc)))
   :rule-classes :linear))

(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-hp-ceiling-lower-g
     (implies (natp l) (<= l (* 16384 (ceiling l 16384))))
     :rule-classes :linear)
   (defthm fn-hp-ceiling-upper-g
     (implies (natp l) (< (* 16384 (ceiling l 16384)) (+ l 16384)))
     :rule-classes :linear)))

(local
 (defthm fn-hp-ceiling-mono-g
   (implies (and (natp l1) (natp l2) (<= l1 l2))
            (<= (ceiling l1 16384) (ceiling l2 16384)))
   :hints (("Goal" :in-theory (disable ceiling)))
   :rule-classes :linear))

(local
 (defthm fn-hp-cap-mono
   (implies (and (natp u) (natp v) (<= u v))
            (<= (adt-cap u) (adt-cap v)))
   :hints (("Goal" :in-theory (disable adt-pow2-at-least ceiling fn-hp-ceiling-mono-g fn-hp-pow2-at-least-mono)
            :use ((:instance fn-hp-pow2-at-least-mono (k (ceiling u 16384)) (k2 (ceiling v 16384)) (acc 1)) (:instance fn-hp-ceiling-mono-g (l1 u) (l2 v)))))
   :rule-classes :linear))

(defthm fn-hp-caps-le-of-zapp
  (fn-hp-caps-le (adt-lens regs) (adt-lens (fn-hp-zapp regs ds)))
  :hints (("Goal" :induct (fn-hp-zapp regs ds) :in-theory (disable adt-cap))))

; -----------------------------------------------------------------------------
; G. A region padded to C pages grows in place while it fits.

(local
 (defun fn-hp-nz-ind-a (m z) (if (or (zp m) (zp z)) (list m z) (fn-hp-nz-ind-a (1- m) (1- z)))))

(local
 (defthm fn-hp-nthcdr-zeros-any
   (implies (natp m) (equal (nthcdr m (adt-zeros z)) (adt-zeros (- (nfix z) m))))
   :hints (("Goal" :induct (fn-hp-nz-ind-a m z) :in-theory (enable nthcdr adt-zeros)))))

(defthm fn-hp-zpad-of-append
  (implies (and (true-listp r) (true-listp d) (natp n) (<= (+ (len r) (len d)) n))
           (equal (append (append r d) (adt-zeros (- n (+ (len r) (len d)))))
                  (fn-hp-rep (append r (adt-zeros (- n (len r)))) (len r) d)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-take-past-prefix (p r) (j 0) (z (adt-zeros (- n (len r)))))
                 (:instance fn-hp-nthcdr-past-prefix (p r) (j (len d)) (z (adt-zeros (- n (len r)))))
                 (:instance fn-hp-nthcdr-zeros-any (m (len d)) (z (- n (len r)))))
           :in-theory (e/d (fn-hp-rep) (fn-hp-take-past-prefix fn-hp-nthcdr-past-prefix fn-hp-nthcdr-zeros-any adt-zeros)))))

(defthm fn-hp-wpadc-of-append
  (implies (and (true-listp r) (true-listp d)
                (equal (mod (len r) 8) 0) (equal (mod (len d) 8) 0)
                (natp c) (<= (+ (len r) (len d)) (* 16384 c)))
           (equal (fn-hp-wpadc (append r d) c)
                  (fn-hp-rep (fn-hp-wpadc r c) (floor (len r) 8) (fn-hp-pack8 (floor (len d) 8) d))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-zpad-of-append (n (* 16384 c)))
                 (:instance fn-hp-floor-8-exact (x (len r)))
                 (:instance fn-hp-floor-8-exact (x (len d)))
                 (:instance fn-hp-pack8-rep (m (* 2048 c)) (b (append r (adt-zeros (- (* 16384 c) (len r)))))
                            (j (floor (len r) 8)) (k (floor (len d) 8)) (x d)))
           :in-theory (e/d (fn-hp-wpadc) (fn-hp-zpad-of-append fn-hp-pack8-rep fn-hp-floor-8-exact floor mod fn-hp-pack8
                                          adt-zeros)))))

; -----------------------------------------------------------------------------
; H. Word alignment without the cap equality; the triples over the new caps.

(defun fn-hp-deltas-aligned (regs ds)
  ; every region and delta word-aligned (`fn-hp-deltas-ok' without its cap
  ; conjunct: a region's cap may grow)
  (declare (xargs :verify-guards nil))
  (if (atom regs) t
    (and (consp ds) (true-listp (car regs)) (true-listp (car ds))
         (equal (mod (len (car regs)) 8) 0) (equal (mod (len (car ds)) 8) 0)
         (fn-hp-deltas-aligned (cdr regs) (cdr ds)))))

(defthm fn-hp-deltas-ok-aligned
  (implies (fn-hp-deltas-ok regs ds) (fn-hp-deltas-aligned regs ds))
  :hints (("Goal" :in-theory (disable adt-cap mod))))

(defun fn-hp-rtriples-c (regs ds starts lens2)
  ; per region: its block padded to the pages LENS2 needs, at its start, whose
  ; end grows by its delta
  (declare (xargs :verify-guards nil))
  (if (or (atom regs) (atom starts) (atom lens2)) nil
    (cons (list (* 2048 (nfix (car starts))) (fn-hp-wpadc (car regs) (adt-cap (nfix (car lens2))))
                (floor (len (car regs)) 8) (fn-hp-pack8 (floor (len (car ds)) 8) (car ds)))
          (fn-hp-rtriples-c (cdr regs) (cdr ds) (cdr starts) (cdr lens2)))))

(defthm fn-hp-outer-rtriples-c
  (equal (fn-hp-outer (fn-hp-rtriples-c regs ds starts lens2)) (fn-hp-rblocks-c regs starts lens2))
  :hints (("Goal" :induct (fn-hp-rtriples-c regs ds starts lens2) :in-theory (disable fn-hp-wpadc fn-hp-pack8 floor adt-cap))))

(defthm fn-hp-inner-rtriples-c
  (implies (and (<= (len regs) (len ds)) (<= (len regs) (len lens2)))
           (equal (fn-hp-inner (fn-hp-rtriples-c regs ds starts lens2))
                  (fn-hp-bb-list starts (adt-lens regs) (fn-hp-ds-words ds))))
  :hints (("Goal" :induct (fn-hp-rtriples-c regs ds starts lens2) :in-theory (disable fn-hp-wpadc fn-hp-pack8 floor adt-cap))))

(defthm fn-hp-outer2-rtriples-c
  (implies (fn-hp-deltas-aligned regs ds)
           (equal (fn-hp-outer2 (fn-hp-rtriples-c regs ds starts (adt-lens (fn-hp-zapp regs ds))))
                  (fn-hp-rblocks-c (fn-hp-zapp regs ds) starts (adt-lens (fn-hp-zapp regs ds)))))
  :hints (("Goal" :induct (fn-hp-rtriples regs ds starts) :in-theory (disable fn-hp-wpadc fn-hp-pack8 floor adt-cap mod))
          ("Subgoal *1/2" :use ((:instance fn-hp-wpadc-of-append (r (car regs)) (d (car ds))
                                           (c (adt-cap (+ (len (car regs)) (len (car ds))))))
                                (:instance adt-cap-covers (u (+ (len (car regs)) (len (car ds)))))))))

(defthm fn-hp-rblocks-c-own-caps
  (equal (fn-hp-rblocks-c regs starts (adt-lens regs)) (fn-hp-rblocks regs starts))
  :hints (("Goal" :induct (fn-hp-rblocks regs starts) :in-theory (disable fn-hp-wpadc fn-hp-wpad adt-cap))))

(defthm fn-hp-triples-ok-rtriples-c
  (implies (and (fn-hp-deltas-aligned regs ds) (adt-placement-ok starts (adt-lens (fn-hp-zapp regs ds)) np))
           (fn-hp-triples-ok (fn-hp-rtriples-c regs ds starts (adt-lens (fn-hp-zapp regs ds))) (* 2048 np)))
  :hints (("Goal" :induct (fn-hp-rtriples regs ds starts) :in-theory (disable fn-hp-wpadc fn-hp-pack8 adt-cap mod))
          ("Subgoal *1/2" :use ((:instance adt-cap-covers (u (+ (len (car regs)) (len (car ds)))))
                                (:instance fn-hp-floor-8-exact (x (len (car regs))))
                                (:instance fn-hp-floor-8-exact (x (len (car ds))))))))

; -----------------------------------------------------------------------------
; I. The append model over grown regions.

(defthm fn-hp-wreps-nest-hdr
  (implies (and (true-listp w) (true-listp hdr) (true-listp hb) (<= (+ 6 (len hb)) (len hdr)) (<= (len hdr) (len w))
                (fn-hp-triples-ok ts (len w)) (fn-hp-blocks-apart (fn-hp-outer ts))
                (fn-hp-block-apart (cons 0 hdr) (fn-hp-outer ts)))
           (equal (fn-hp-wreps w (cons (cons 0 (fn-hp-rep hdr 6 hb)) (fn-hp-outer2 ts)))
                  (fn-hp-wreps (fn-hp-wreps w (cons (cons 0 hdr) (fn-hp-outer ts))) (cons (cons 6 hb) (fn-hp-inner ts)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-wreps-nest (ts (cons (list 0 hdr 6 hb) ts))))
           :in-theory (disable fn-hp-wreps-nest fn-hp-wreps fn-hp-rep fn-hp-outer fn-hp-outer2 fn-hp-inner fn-hp-triples-ok
                               fn-hp-block-apart fn-hp-blocks-apart)
           :expand ((fn-hp-outer (cons (list 0 hdr 6 hb) ts)) (fn-hp-outer2 (cons (list 0 hdr 6 hb) ts))
                    (fn-hp-inner (cons (list 0 hdr 6 hb) ts)) (fn-hp-triples-ok (cons (list 0 hdr 6 hb) ts) (len w))
                    (fn-hp-blocks-apart (cons (cons 0 hdr) (fn-hp-outer ts)))))))

(local (defthm fn-hp-len-zapp-g (equal (len (fn-hp-zapp xs ys)) (len xs))))

(local (defthm fn-hp-consp-when-len-5-c (implies (equal (len x) 5) (consp x))))

; The appended history's placed image is the old one with the append's six
; blocks in place, whether or not a region's cap grows, when the new lengths
; are placed at STARTS.

(defthm fn-hp-piw-of-append1-grown
  (implies (and (adt-placement-ok starts (fn-hp-lens (append h (list ev)) salt) np) (equal (len starts) 5)
                (fn-hp-deltas-aligned (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))
           (equal (fn-hp-piw (append h (list ev)) salt starts np)
                  (fn-hp-wreps (fn-hp-piw h salt starts np) (fn-hp-pblocks h ev salt starts))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-piw-caps-extend
                            (lens2 (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))))
                 (:instance fn-hp-wreps-nest-hdr (w (adt-zeros (* 2048 np)))
                            (hdr (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))
                            (hb (fn-hp-hb (+ 1 (len h)) starts
                                          (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))))
                            (ts (fn-hp-rtriples-c (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)) starts
                                                  (adt-lens (fn-hp-zapp (fn-hp-regs h salt)
                                                                        (fn-hp-ds ev salt (fn-hp-pes-len h)))))))
                 (:instance fn-hp-hdr2-of-append1 (n (len h)) (lens (fn-hp-lens h salt))
                            (lens2 (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))))
                 (:instance fn-hp-placement-np-pos
                            (lens (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))))
                 (:instance fn-hp-len-regs-5)
                 (:instance fn-hp-consp-when-len-5-c (x starts))
                 (:instance fn-hp-consp-when-len-5-c
                            (x (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))))
                 (:instance adt-lens-starts-shape (regs (fn-hp-regs h salt)))
                 (:instance adt-lens-starts-shape (regs (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))))
                 (:instance fn-hp-rblocks-c-apart (regs (fn-hp-regs h salt))
                            (lens2 (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))))
                 (:instance fn-hp-hdr-apart-rblocks-c (regs (fn-hp-regs h salt))
                            (lens2 (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))))
                            (hdr (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np)))
                 (:instance fn-hp-triples-ok-rtriples-c (regs (fn-hp-regs h salt)) (ds (fn-hp-ds ev salt (fn-hp-pes-len h))))
                 (:instance fn-hp-caps-le-of-zapp (regs (fn-hp-regs h salt)) (ds (fn-hp-ds ev salt (fn-hp-pes-len h)))))
           :in-theory (e/d (fn-hp-piw fn-hp-lens fn-hp-pblocks)
                           (fn-hp-piw-caps-extend fn-hp-wreps-nest-hdr fn-hp-hdr2-of-append1 fn-hp-rblocks-c-apart
                            fn-hp-hdr-apart-rblocks-c fn-hp-triples-ok-rtriples-c fn-hp-caps-le-of-zapp
                            fn-hp-lens-of-append1 fn-hp-wreps fn-hp-rep fn-hp-hdr2 fn-hp-hb fn-hp-rblocks fn-hp-rblocks-c
                            fn-hp-rtriples-c fn-hp-regs fn-hp-ds fn-hp-deltas-aligned adt-placement-ok fn-hp-zapp
                            fn-hp-bb-list fn-hp-ds-words adt-lens adt-zeros (:e adt-zeros) fn-hp-caps-le
                            fn-hp-block-apart fn-hp-blocks-apart fn-hp-lens-of-zapp fn-hp-lens-of-ds
                            fn-hp-triples-ok fn-hp-outer fn-hp-outer2 fn-hp-inner fn-hp-consp-when-len-5-c fn-hp-wreps-append fn-hp-deltas-ok-aligned)))))
