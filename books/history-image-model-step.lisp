; Appending body words while retaining the final header written at open.
(in-package "ACL2")
(include-book "history-pages-grow-append")
(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-his-cover-inner-nth
  (implies (and (natp k) (natp j) (<= (+ j (len b)) (len hdr)))
   (equal (nth k (fn-hp-rep (fn-hp-rep w j b) 0 hdr))
          (nth k (fn-hp-rep w 0 hdr))))
  :hints (("Goal" :in-theory (disable fn-hp-rep)))))

(local
 (defthm fn-his-cover-inner-agree
  (implies (and (natp a) (natp j) (<= (+ j (len b)) (len hdr)))
   (fn-hp-agree a n (fn-hp-rep (fn-hp-rep w j b) 0 hdr) (fn-hp-rep w 0 hdr)))
  :hints (("Goal" :induct (fn-hp-agree-ind a n) :in-theory (disable fn-hp-rep)))))

(defthm fn-his-cover-inner
 (implies (and (natp j) (true-listp w) (<= (+ j (len b)) (len hdr)) (<= (len hdr) (len w)))
  (equal (fn-hp-rep (fn-hp-rep w j b) 0 hdr) (fn-hp-rep w 0 hdr)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hp-equal-by-agree (x (fn-hp-rep (fn-hp-rep w j b) 0 hdr))
                           (y (fn-hp-rep w 0 hdr)))
                (:instance fn-his-cover-inner-agree (a 0) (n (len w))))
          :in-theory (disable fn-hp-rep fn-hp-agree fn-his-cover-inner-agree))))

(defthm fn-his-inner-within
 (implies (fn-hp-triples-ok ts n) (fn-hp-blocks-within (fn-hp-inner ts) n))
 :hints (("Goal" :induct (fn-hp-triples-ok ts n)
          :in-theory (enable fn-hp-inner fn-hp-blocks-within fn-hp-triples-ok))))

(defthm fn-his-header-apart-inner
 (implies (and (natp j) (fn-hp-triples-ok ts n)
               (fn-hp-block-apart (cons j hdr) (fn-hp-outer ts)))
  (fn-hp-block-apart (cons j hdr) (fn-hp-inner ts)))
 :hints (("Goal" :induct (fn-hp-triples-ok ts n)
          :in-theory (enable fn-hp-inner fn-hp-outer fn-hp-block-apart fn-hp-pair-apart))))

(defthm fn-his-fixed-header-body-step
 (implies (and (natp j) (true-listp w) (true-listp hdr)
               (<= (+ j (len hb)) (len hdr)) (<= (len hdr) (len w))
               (fn-hp-blocks-within blocks (len w))
               (fn-hp-block-apart (cons 0 hdr) blocks))
  (equal (fn-hp-rep (fn-hp-wreps (fn-hp-rep w j hb) blocks) 0 hdr)
         (fn-hp-wreps (fn-hp-rep w 0 hdr) blocks)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hp-wreps-commute (u (fn-hp-rep w j hb)) (a 0) (x hdr)))
          :in-theory (disable fn-hp-rep fn-hp-wreps fn-hp-blocks-within fn-hp-block-apart
                              fn-hp-wreps-commute))))

(defmacro fn-his-body-ts ()
 '(fn-hp-rtriples-c (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)) starts
                    (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))))

(local (defthm fn-his-model-lens-length
 (equal (len (adt-lens (fn-hp-regs h salt))) 5)
 :hints (("Goal" :in-theory (disable fn-hp-regs)))))
(local (defthm fn-his-model-consp-five
 (implies (equal (len x) 5) (consp x))))

(defthm fn-his-piw-append-fixed-header
 (implies
  (and (natp np) (nat-listp starts) (equal (len starts) 5)
       (true-listp hdr) (equal (len hdr) 2048)
       (adt-placement-ok starts (fn-hp-lens (append h (list ev)) salt) np)
       (fn-hp-deltas-aligned (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))
  (equal
   (fn-hp-rep (fn-hp-piw (append h (list ev)) salt starts np) 0 hdr)
   (fn-hp-wreps (fn-hp-rep (fn-hp-piw h salt starts np) 0 hdr)
                (fn-hp-bb-list starts (fn-hp-lens h salt)
                               (fn-hp-ds-words (fn-hp-ds ev salt (fn-hp-pes-len h)))))))
 :hints (("Goal" :do-not-induct t
          :use (fn-hp-piw-of-append1-grown
                (:instance fn-hp-placement-mono (lens (fn-hp-lens h salt))
                  (lens2 (fn-hp-lens (append h (list ev)) salt)))
                (:instance fn-hp-caps-le-of-zapp (regs (fn-hp-regs h salt))
                  (ds (fn-hp-ds ev salt (fn-hp-pes-len h))))
                (:instance fn-his-inner-within (ts (fn-his-body-ts)) (n (* 2048 np)))
                (:instance fn-his-header-apart-inner (ts (fn-his-body-ts)) (n (* 2048 np)) (j 0))
                (:instance fn-hp-triples-ok-rtriples-c (regs (fn-hp-regs h salt))
                           (ds (fn-hp-ds ev salt (fn-hp-pes-len h))))
                (:instance fn-hp-hdr-apart-rblocks-c (regs (fn-hp-regs h salt))
                           (lens2 (fn-hp-lens (append h (list ev)) salt)))
                (:instance fn-hp-len-piw (s starts))
                (:instance fn-hp-placement-np-pos (lens (fn-hp-lens (append h (list ev)) salt)))
                (:instance fn-his-fixed-header-body-step
                  (w (fn-hp-piw h salt starts np)) (j 6)
                  (hb (fn-hp-hb (+ 1 (len h)) starts (fn-hp-lens (append h (list ev)) salt)))
                  (blocks (fn-hp-bb-list starts (fn-hp-lens h salt)
                            (fn-hp-ds-words (fn-hp-ds ev salt (fn-hp-pes-len h)))))))
          :in-theory (e/d (fn-hp-pblocks fn-hp-lens fn-hp-wreps)
                          (fn-hp-piw-of-append1-grown fn-his-inner-within fn-his-header-apart-inner
                           fn-hp-triples-ok-rtriples-c fn-hp-hdr-apart-rblocks-c fn-hp-len-piw
                           fn-his-fixed-header-body-step fn-hp-piw fn-hp-rep fn-hp-hb
                           fn-hp-placement-mono fn-hp-caps-le-of-zapp fn-hp-caps-le
                           fn-hp-piw-caps-extend fn-hp-hdr2 adt-zeros (:e adt-zeros)
                           fn-hp-regs fn-hp-ds fn-hp-zapp fn-hp-ds-words fn-hp-bb-list
                           fn-hp-rtriples-c fn-hp-rblocks-c fn-hp-inner fn-hp-outer fn-hp-triples-ok
                           fn-hp-blocks-within fn-hp-block-apart adt-lens adt-placement-ok))))
 :rule-classes nil)

(defthm fn-his-piw-empty
 (implies (and (natp np) (<= 1 np) (nat-listp starts) (equal (len starts) 5)
               (adt-placement-ok starts '(0 0 0 0 0) np))
  (equal (fn-hp-piw nil salt starts np)
         (fn-hp-rep (adt-zeros (* 2048 np)) 0 (fn-hp-hdr2 0 '(0 0 0 0 0) starts np))))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-hp-piw fn-hp-regs fn-hp-rblocks fn-hp-wpad fn-hp-wreps
                                    adt-placement-ok len)
                          (fn-hp-rep fn-hp-hdr2 fn-hp-piw-caps-extend adt-zeros (:e adt-zeros))))))

(defthm fn-his-empty-fixed-header
 (implies (and (natp np) (<= 1 np) (nat-listp starts) (equal (len starts) 5)
               (adt-placement-ok starts '(0 0 0 0 0) np)
               (true-listp hdr) (equal (len hdr) 2048))
  (equal (fn-hp-rep (fn-hp-piw nil salt starts np) 0 hdr)
         (fn-hp-rep (adt-zeros (* 2048 np)) 0 hdr)))
 :hints (("Goal" :do-not-induct t
          :in-theory (disable fn-hp-piw fn-hp-rep fn-hp-hdr2 fn-hp-piw-caps-extend
                              adt-placement-ok adt-zeros (:e adt-zeros)))))

(local
 (defthm fn-his-final-header-nth
  (implies (and (adt-placement-ok starts (fn-hp-lens h salt) np)
                (equal (len starts) 5) (natp k))
   (equal (nth k (fn-hp-rep (fn-hp-piw h salt starts np) 0
                            (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np)))
          (nth k (fn-hp-piw h salt starts np))))
  :hints (("Goal" :in-theory (disable fn-hp-piw fn-hp-rep fn-hp-hdr2 fn-hp-lens
                                      adt-placement-ok fn-hp-piw-caps-extend)))))

(local
 (defthm fn-his-final-header-agree
  (implies (and (adt-placement-ok starts (fn-hp-lens h salt) np)
                (equal (len starts) 5) (natp a))
   (fn-hp-agree a n (fn-hp-rep (fn-hp-piw h salt starts np) 0
                               (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))
                    (fn-hp-piw h salt starts np)))
  :hints (("Goal" :induct (fn-hp-agree-ind a n)
           :in-theory (disable fn-hp-piw fn-hp-rep fn-hp-hdr2 fn-hp-lens
                               adt-placement-ok fn-hp-piw-caps-extend)))))

(defthm fn-his-final-header-is-already-present
 (implies (and (adt-placement-ok starts (fn-hp-lens h salt) np)
               (equal (len starts) 5) (natp np))
  (equal (fn-hp-rep (fn-hp-piw h salt starts np) 0
                    (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))
         (fn-hp-piw h salt starts np)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hp-equal-by-agree
                  (x (fn-hp-rep (fn-hp-piw h salt starts np) 0
                                (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np)))
                  (y (fn-hp-piw h salt starts np)))
                (:instance fn-his-final-header-agree (a 0) (n (* 2048 np)))
                (:instance fn-hp-len-piw (s starts))
                (:instance fn-hp-placement-np-pos (lens (fn-hp-lens h salt))))
          :in-theory (disable fn-hp-piw fn-hp-rep fn-hp-hdr2 fn-hp-lens fn-hp-agree
                              adt-placement-ok fn-hp-piw-caps-extend fn-hp-len-piw
                              fn-his-final-header-agree))))
