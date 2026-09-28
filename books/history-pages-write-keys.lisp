; fn: the history's writer: its blocks are the model's, and the two
; keystones (lane arena-store-3, 2026-09-28).  Prefix fn-hp-.
;
; KEYSTONES
;   fn-hp-x-append-refines  at the canonical placement (STARTS, NP the
;                           header's), over any page store state whose
;                           verified pages hold the history's image words, an
;                           append that answers :ok leaves them holding the
;                           appended history's image words, and answers its
;                           header (the placed, growing case:
;                           books/history-pages-append-grown.lisp)
;   fn-hp-x-append-dirty    every page the append marks dirty is in the
;                           proved dirty list `fn-hp-append-dirty' (so m1's
;                           `fn-hp-append-dirty-bound' bounds the commit)
;                           and is verified
(in-package "ACL2")
(include-book "history-pages-write-exec")
(include-book "history-pages-arith")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable floor)))

; H. The writer's blocks are the model's.

(defun fn-hp-ds-words (ds)
  (declare (xargs :verify-guards nil))
  (if (atom ds) nil (cons (fn-hp-pack8 (floor (len (car ds)) 8) (car ds)) (fn-hp-ds-words (cdr ds)))))

(defthm fn-hp-body-blocks-is-bb-list
  (implies (and (natp base) (<= (len regs) (len ds)))
           (equal (fn-hp-body-blocks regs ds base)
                  (fn-hp-bb-list (adt-starts regs base) (adt-lens regs) (fn-hp-ds-words ds))))
  :hints (("Goal" :induct (fn-hp-body-blocks regs ds base) :in-theory (disable adt-cap fn-hp-pack8 floor))))

(defthm fn-hp-pack8-1-le
  (implies (unsigned-byte-p 64 x) (equal (fn-hp-pack8 1 (adt-le 8 x)) (list x)))
  :hints (("Goal" :use ((:instance fn-hp-pack8-le2 (c 1) (rest nil)))
           :in-theory (disable fn-hp-pack8-le2 fn-hp-pack8-le adt-le))))

(defthm fn-hp-ds-words-of-ds
  (implies (and (unsigned-byte-p 64 (len (fn-scc-encode ev))) (unsigned-byte-p 64 off)
                (unsigned-byte-p 64 (len (fn-hp-pe ev))))
           (equal (fn-hp-ds-words (fn-hp-ds ev salt off))
                  (list (list (fn-hp-mkey ev salt)) (list (len (fn-scc-encode ev))) (list off)
                        (list (len (fn-hp-pe ev)))
                        (fn-hp-pack8 (floor (len (fn-hp-pe ev)) 8) (fn-hp-pe ev)))))
  :hints (("Goal" :in-theory (disable fn-hp-pack8 adt-le fn-scc-encode fn-hp-pe fn-hp-mkey floor))))
(defthm fn-hp-lens-of-zapp
  (implies (<= (len regs) (len ds))
           (equal (adt-lens (fn-hp-zapp regs ds)) (fn-hp-x-add (adt-lens regs) (adt-lens ds)))))

(defthm fn-hp-deltas-ok-from-checks
  (implies (and (true-list-listp regs) (true-list-listp ds) (equal (len ds) (len regs))
                (fn-hp-x-aligned (adt-lens regs)) (fn-hp-x-aligned (adt-lens ds))
                (fn-hp-x-caps-ok (adt-lens regs) (fn-hp-x-add (adt-lens regs) (adt-lens ds))))
           (fn-hp-deltas-ok regs ds))
  :hints (("Goal" :induct (fn-hp-body-blocks regs ds 0) :in-theory (disable adt-cap mod))))

(defthm fn-hp-true-list-listp-regs
  (true-list-listp (fn-hp-regs h salt))
  :hints (("Goal" :in-theory (enable adt-regs))))

(defthm fn-hp-lens-of-ds
  (equal (adt-lens (fn-hp-ds ev salt off)) (list 8 8 8 8 (len (fn-hp-pe ev))))
  :hints (("Goal" :in-theory (disable fn-hp-pe fn-scc-encode fn-hp-mkey fn-scc-program adt-le))))

(defthm fn-hp-true-list-listp-ds
  (true-list-listp (fn-hp-ds ev salt off))
  :hints (("Goal" :in-theory (e/d (fn-hp-pe fn-hp-pad8) (fn-scc-encode fn-hp-mkey fn-scc-program adt-le)))))

(defthmd fn-hp-starts-is-adt-starts
  (equal (fn-hp-starts h salt) (adt-starts (fn-hp-regs h salt) 1))
  :hints (("Goal" :in-theory (e/d (fn-hp-starts fn-hp-lens) (fn-hp-regs)))))

(defthm fn-hp-len-ds (equal (len (fn-hp-ds ev salt off)) 5)
  :hints (("Goal" :in-theory (disable fn-hp-pe fn-scc-encode fn-scc-program fn-hp-mkey adt-le))))

(defthm fn-hp-lens-of-append1
  (equal (fn-hp-lens (append h (list ev)) salt)
         (fn-hp-x-add (fn-hp-lens h salt) (list 8 8 8 8 (len (fn-hp-pe ev)))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-hp-lens) (fn-hp-regs fn-hp-ds fn-hp-pe fn-hp-x-add)))))

(local
 (defthm fn-hp-len-pe-8
   (equal (* 8 (floor (len (fn-hp-pe ev)) 8)) (len (fn-hp-pe ev)))
   :hints (("Goal" :use ((:instance fn-hp-floor-8-exact (x (len (fn-hp-pe ev)))) (:instance fn-hp-pe-mod-8))
            :in-theory (disable fn-hp-floor-8-exact fn-hp-pe-mod-8 floor mod)))))

(defthm fn-hp-u64-listp-of-x-add
  (implies (and (fn-hp-u64-listp (fn-hp-x-add a b)) (nat-listp a) (nat-listp b) (equal (len a) (len b)))
           (and (fn-hp-u64-listp a) (fn-hp-u64-listp b))))

(defthm fn-hp-consp-cddddr-regs
  (consp (cddddr (fn-hp-regs h salt)))
  :hints (("Goal" :use ((:instance fn-hp-len-regs-5)) :in-theory (disable fn-hp-len-regs-5 fn-hp-regs))))

(defthm fn-hp-car-adt-lens
  (implies (consp x) (equal (car (adt-lens x)) (len (car x)))))

(defthm fn-hp-pool-len-is-pes-len
  (equal (len (car (cddddr (fn-hp-regs h salt)))) (fn-hp-pes-len h))
  :hints (("Goal" :use ((:instance fn-hp-lens-4) (:instance fn-hp-len-regs-5))
           :in-theory (e/d (fn-hp-lens) (fn-hp-lens-4 fn-hp-regs fn-hp-len-regs-5)))))

(defthm fn-hp-nat-listp-adt-lens (nat-listp (adt-lens regs)))

(defthm fn-hp-u64-pool-len
  (implies (fn-hp-u64-listp (adt-lens (fn-hp-regs h salt)))
           (unsigned-byte-p 64 (fn-hp-pes-len h)))
  :hints (("Goal" :use ((:instance fn-hp-pool-len-is-pes-len) (:instance fn-hp-len-regs-5))
           :in-theory (disable fn-hp-pool-len-is-pes-len fn-hp-regs fn-hp-len-regs-5)
           :expand ((adt-lens (fn-hp-regs h salt)) (adt-lens (cdr (fn-hp-regs h salt)))
                    (adt-lens (cddr (fn-hp-regs h salt))) (adt-lens (cdddr (fn-hp-regs h salt)))
                    (adt-lens (cddddr (fn-hp-regs h salt)))))))

(defthm fn-hp-x-aligned-ds-lens
  (fn-hp-x-aligned (list 8 8 8 8 (len (fn-hp-pe ev))))
  :hints (("Goal" :use ((:instance fn-hp-pe-mod-8)) :in-theory (disable fn-hp-pe-mod-8 mod fn-hp-pe))))

;; At the canonical placement no cap grows in place: every region is
;; followed by the next (or by the image's end), so a new length that is
;; still placed keeps its cap.  The writer at the canonical placement is
;; therefore the canonical model's append (`fn-hp-x-caps-ok').
(local
 (defthm fn-hp-pow2-at-least-mono-k
   (implies (and (natp k) (natp k2) (<= k k2) (posp acc))
            (<= (adt-pow2-at-least k acc) (adt-pow2-at-least k2 acc)))
   :hints (("Goal" :induct (adt-pow2-at-least k2 acc)))
   :rule-classes :linear))

(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-hp-ceiling-lower-k
     (implies (natp l) (<= l (* 16384 (ceiling l 16384))))
     :rule-classes :linear)
   (defthm fn-hp-ceiling-upper-k
     (implies (natp l) (< (* 16384 (ceiling l 16384)) (+ l 16384)))
     :rule-classes :linear)))

(local
 (defthm fn-hp-ceiling-mono-k
   (implies (and (natp l1) (natp l2) (<= l1 l2))
            (<= (ceiling l1 16384) (ceiling l2 16384)))
   :hints (("Goal" :in-theory (disable ceiling)))
   :rule-classes :linear))

(defthm fn-hp-cap-mono-k
  (implies (and (natp u) (natp v) (<= u v))
           (<= (adt-cap u) (adt-cap v)))
  :hints (("Goal" :in-theory (disable adt-pow2-at-least ceiling fn-hp-ceiling-mono-k fn-hp-pow2-at-least-mono-k)
           :use ((:instance fn-hp-pow2-at-least-mono-k (k (ceiling u 16384)) (k2 (ceiling v 16384)) (acc 1))
                 (:instance fn-hp-ceiling-mono-k (l1 u) (l2 v)))))
  :rule-classes :linear)

(defthm fn-hp-cap-posp
  (implies (posp u) (posp (adt-cap u)))
  :rule-classes :type-prescription)

(defun fn-hp-pos-listp (l)
  (declare (xargs :guard t))
  (if (atom l) t (and (posp (car l)) (fn-hp-pos-listp (cdr l)))))

(defun fn-hp-caps-below (lens2 lens)
  ; each cap of LENS2 at most LENS's
  (declare (xargs :verify-guards nil))
  (if (or (atom lens2) (atom lens)) t
    (and (<= (adt-cap (nfix (car lens2))) (adt-cap (nfix (car lens))))
         (fn-hp-caps-below (cdr lens2) (cdr lens)))))

(local
 (defun fn-hp-canon-ind (lens lens2 s)
   (if (atom lens) (list lens2 s)
     (fn-hp-canon-ind (cdr lens) (cdr lens2) (+ (nfix s) (adt-cap (nfix (car lens))))))))

(defthm fn-hp-canon-head
  (implies (and (natp s) (natp c0) (posp c) (consp rl) (posp (car rl2))
                (adt-apart s c (adt-starts-l rl (+ s c0)) rl2))
           (<= c c0))
  :hints (("Goal" :expand ((adt-starts-l rl (+ s c0)) (:free (x) (adt-apart s c (cons (+ s c0) x) rl2)))
           :in-theory (disable adt-cap)))
  :rule-classes nil)

(defthm fn-hp-canonical-caps-below
  (implies (and (natp s) (<= 1 s) (nat-listp lens) (fn-hp-pos-listp lens2) (equal (len lens2) (len lens))
                (adt-placement-ok (adt-starts-l lens s) lens2 (adt-end-l lens s)))
           (fn-hp-caps-below lens2 lens))
  :hints (("Goal" :induct (fn-hp-canon-ind lens lens2 s) :in-theory (disable adt-cap))
          ("Subgoal *1/2" :use ((:instance fn-hp-canon-head (c0 (adt-cap (car lens))) (c (adt-cap (car lens2)))
                                           (rl (cdr lens)) (rl2 (cdr lens2))))
           :cases ((consp (cdr lens))))))

(defthm fn-hp-caps-ok-when-below
  (implies (and (nat-listp lens) (nat-listp d) (fn-hp-x-aligned lens)
                (fn-hp-caps-below (fn-hp-x-add lens d) lens) (<= (len lens) (len d)))
           (fn-hp-x-caps-ok lens (fn-hp-x-add lens d)))
  :hints (("Goal" :induct (fn-hp-x-add lens d) :in-theory (disable adt-cap mod))
          ("Subgoal *1/2" :use ((:instance fn-hp-cap-mono-k (u (car lens)) (v (+ (car lens) (car d))))))))

(defthm fn-hp-pos-listp-x-add
  (implies (and (nat-listp lens) (fn-hp-pos-listp d)) (fn-hp-pos-listp (fn-hp-x-add lens d))))

(defthm fn-hp-len-x-add-5
  (implies (and (equal (len lens) 5) (equal (len d) 5)) (equal (len (fn-hp-x-add lens d)) 5)))

; The writer's plan at the canonical placement: when it answers blocks, no
; cap changes.
(defthm fn-hp-x-append-plan-canonical-caps
  (implies (not (mv-nth 0 (fn-hp-x-append-plan ev salt n (fn-hp-lens h salt) (fn-hp-starts h salt)
                                               (fn-hp-npages h salt))))
           (fn-hp-x-caps-ok (fn-hp-lens h salt)
                            (fn-hp-x-add (fn-hp-lens h salt) (list 8 8 8 8 (len (fn-hp-pe ev))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-canonical-caps-below (s 1) (lens (fn-hp-lens h salt))
                            (lens2 (fn-hp-x-add (fn-hp-lens h salt) (list 8 8 8 8 (len (fn-hp-pe ev))))))
                 (:instance fn-hp-caps-ok-when-below (lens (fn-hp-lens h salt)) (d (list 8 8 8 8 (len (fn-hp-pe ev)))))
                 (:instance fn-hp-len-pe-pos) (:instance fn-hp-npages-is-end-l)
                 (:instance fn-hp-nat-listp-lens) (:instance fn-hp-len-lens))
           :in-theory (e/d (fn-hp-starts fn-hp-pe)
                           (fn-hp-canonical-caps-below fn-hp-caps-ok-when-below fn-hp-len-pe-pos fn-hp-npages-is-end-l
                            fn-hp-nat-listp-lens fn-hp-len-lens
                            fn-scc-encode fn-scc-program fn-hp-pad8 fn-hp-x-caps-ok fn-hp-x-aligned adt-cap adt-placement-ok
                            fn-hp-x-unfit fn-hp-pack8 floor mod fn-hp-mkey fn-sccb-treep fn-hp-hb fn-hp-x-add fn-hp-x-blocks
                            fn-hp-lens fn-hp-npages adt-starts-l adt-end-l fn-hp-caps-below)))))

(defthm fn-hp-x-append-plan-is-model
  (implies (and (fn-hp-okp h salt)
                (not (mv-nth 0 (fn-hp-x-append-plan ev salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt)
                                                    (fn-hp-npages h salt)))))
           (and (equal (mv-nth 1 (fn-hp-x-append-plan ev salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt)
                                                      (fn-hp-npages h salt)))
                       (fn-hp-blocks h ev salt))
                (equal (mv-nth 2 (fn-hp-x-append-plan ev salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt)
                                                      (fn-hp-npages h salt)))
                       (fn-hp-lens (append h (list ev)) salt))
                (fn-hp-deltas-ok (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))
                (unsigned-byte-p 64 (+ 1 (len h)))
                (fn-hp-u64-listp (adt-starts (fn-hp-regs h salt) 1))
                (fn-hp-u64-listp (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))))
                (fn-hp-evp ev)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-starts-is-adt-starts) (:instance fn-hp-pe-def)
                 (:instance fn-hp-x-append-plan-canonical-caps (n (len h)))
                 (:instance fn-hp-ds-words-of-ds (off (fn-hp-pes-len h))) (:instance fn-hp-u64-pool-len)
                 (:instance fn-hp-u64-listp-of-x-add (a (adt-lens (fn-hp-regs h salt))) (b (list 8 8 8 8 (len (fn-hp-pe ev)))))
                 (:instance fn-hp-deltas-ok-from-checks (regs (fn-hp-regs h salt)) (ds (fn-hp-ds ev salt (fn-hp-pes-len h)))))
           :in-theory (e/d (fn-hp-blocks fn-hp-lens)
                           (fn-hp-deltas-ok-from-checks fn-hp-ds-words-of-ds fn-hp-u64-listp-of-x-add fn-hp-regs fn-hp-ds fn-hp-pe fn-scc-encode fn-scc-program
                            fn-hp-x-append-plan-canonical-caps adt-placement-ok fn-hp-x-unfit fn-hp-npages fn-hp-starts
                            fn-hp-mkey fn-hp-pad8 fn-hp-x-caps-ok fn-hp-x-aligned adt-cap fn-hp-pack8 floor mod
                            fn-hp-deltas-ok fn-hp-okp adt-starts adt-lens fn-hp-zapp fn-hp-body-blocks
                            fn-hp-lens-of-append1 adt-starts-is-starts-l fn-sccb-treep
                            fn-hp-x-add fn-hp-bb-list fn-hp-ds-words)))))
; -----------------------------------------------------------------------------
(defthm fn-hp-u64-meta-words
  (implies (and (fn-hp-u64-listp starts) (fn-hp-u64-listp lens2) (equal (len lens2) (len starts)))
           (fn-hp-u64-listp (fn-hp-meta-words starts lens2))))

(defthm fn-hp-u64-listp-hb
  (implies (and (unsigned-byte-p 64 n2) (fn-hp-u64-listp starts) (fn-hp-u64-listp lens2)
                (equal (len lens2) (len starts)))
           (fn-hp-u64-listp (fn-hp-hb n2 starts lens2)))
  :hints (("Goal" :in-theory (enable fn-hp-hb))))

(defthm fn-hp-consp-pad8-enc
  (consp (fn-hp-pad8 (fn-scc-encode ev)))
  :hints (("Goal" :use ((:instance fn-hp-len-pe-pos) (:instance fn-hp-pe-def))
           :in-theory (disable fn-hp-len-pe-pos fn-hp-pe fn-hp-pad8 fn-scc-encode fn-scc-program))))
(local (in-theory (disable fn-scc-encode-is-program)))

(defthm fn-hp-consp-pack8
  (implies (posp k) (consp (fn-hp-pack8 k b))))

(local
 (defthm fn-hp-floor-pe-posp-w
   (posp (floor (len (fn-hp-pe ev)) 8))
   :hints (("Goal" :use ((:instance fn-hp-floor-8-exact (x (len (fn-hp-pe ev)))) (:instance fn-hp-pe-mod-8)
                         (:instance fn-hp-len-pe-pos))
            :in-theory (disable fn-hp-floor-8-exact fn-hp-pe-mod-8 fn-hp-len-pe-pos floor mod fn-hp-pe)))
   :rule-classes :type-prescription))

(defthm fn-hp-len-x-add
  (implies (equal (len a) (len b)) (equal (len (fn-hp-x-add a b)) (len a))))

(defun fn-hp-wls-okp (wls)
  (declare (xargs :guard t))
  (if (atom wls) t (and (consp (car wls)) (fn-hp-u64-listp (car wls)) (fn-hp-wls-okp (cdr wls)))))

(defthm fn-hp-shape-bb-list
  (implies (fn-hp-wls-okp wls) (fn-hp-blocks-shape (fn-hp-bb-list starts lens wls))))

(defthm fn-hp-x-append-plan-shape
  (implies (and (nat-listp lens) (equal (len lens) 5) (nat-listp starts) (equal (len starts) 5)
                (not (mv-nth 0 (fn-hp-x-append-plan ev salt n lens starts np))))
           (fn-hp-blocks-shape (mv-nth 1 (fn-hp-x-append-plan ev salt n lens starts np))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-u64-listp-of-x-add (a lens) (b (list 8 8 8 8 (len (fn-hp-pe ev)))))
                 (:instance fn-hp-octetsp-pe) (:instance fn-hp-pe-def))
           :in-theory (disable fn-scc-encode fn-scc-program fn-hp-pad8 fn-hp-x-caps-ok fn-hp-x-aligned adt-cap
                               fn-hp-pack8 floor mod fn-hp-mkey fn-sccb-treep fn-hp-hb fn-hp-x-add fn-hp-len-pad8 adt-placement-ok fn-hp-x-unfit
                               fn-hp-u64-listp-of-x-add fn-hp-octetsp-pe fn-hp-pe))))
; -----------------------------------------------------------------------------
; J. The keystones.

(defthm fn-hp-events-okp-append1
  (implies (and (fn-hp-events-okp h) (fn-hp-evp ev))
           (fn-hp-events-okp (append h (list ev))))
  :hints (("Goal" :in-theory (disable fn-hp-evp))))

(defthm fn-hp-okp-of-append1
  (implies (and (fn-hp-okp h salt) (fn-hp-evp ev) (unsigned-byte-p 64 (+ 1 (len h)))
                (fn-hp-deltas-ok (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))
           (fn-hp-okp (append h (list ev)) salt))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-npages-is-caps-sum) (:instance fn-hp-npages-is-caps-sum (h (append h (list ev))))
                 (:instance fn-hp-len-image) (:instance fn-hp-len-image (h (append h (list ev)))))
           :in-theory (e/d (fn-hp-okp) (fn-hp-evp fn-hp-image fn-hp-npages fn-hp-regs fn-hp-ds fn-hp-deltas-ok
                                        fn-hp-len-image fn-hp-npages-is-end-l)))))

(defthm fn-hp-starts-of-append1
  (implies (fn-hp-deltas-ok (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))
           (equal (fn-hp-starts (append h (list ev)) salt) (fn-hp-starts h salt)))
  :hints (("Goal" :use ((:instance fn-hp-starts-is-adt-starts) (:instance fn-hp-starts-is-adt-starts (h (append h (list ev)))))
           :do-not-induct t :in-theory (disable fn-hp-starts fn-hp-regs fn-hp-ds fn-hp-deltas-ok fn-hp-lens adt-starts-is-starts-l adt-starts))))

(defthm fn-hp-x-append-plan-verdict-not-ok
  (not (equal (mv-nth 0 (fn-hp-x-append-plan ev salt n lens starts np)) :ok))
  :hints (("Goal" :in-theory (disable fn-scc-encode fn-hp-pad8 adt-placement-ok fn-hp-x-unfit fn-hp-x-aligned fn-hp-x-blocks
                                      fn-hp-x-add fn-sccb-treep fn-hp-pack8))))

(defthm fn-hp-len-append1 (equal (len (append h (list ev))) (+ 1 (len h))))

;; The writer's answer, unfolded (names the plan, the readiness and the writes).
(defthm fn-hp-x-append-ok-unfolds
  (implies (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok)
           (and (not (mv-nth 0 (fn-hp-x-append-plan ev salt n lens starts np)))
                (equal (fn-hp-x-blocks-ready (mv-nth 1 (fn-hp-x-append-plan ev salt n lens starts np)) pgs-mem) :ok)
                (equal (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem))
                       (fn-hp-x-put-blocks (mv-nth 1 (fn-hp-x-append-plan ev salt n lens starts np)) pgs-mem))
                (equal (mv-nth 1 (fn-hp-x-append ev salt n lens starts np pgs-mem)) (+ 1 n))
                (equal (mv-nth 2 (fn-hp-x-append ev salt n lens starts np pgs-mem))
                       (mv-nth 2 (fn-hp-x-append-plan ev salt n lens starts np)))))
  :hints (("Goal" :use ((:instance fn-hp-x-append-plan-verdict-not-ok))
           :in-theory (e/d (fn-hp-x-append) (fn-hp-x-append-plan fn-hp-x-blocks-ready fn-hp-x-put-blocks fn-hp-x-append-plan-verdict-not-ok)))))

(defthm fn-hp-vhold-after-put-blocks
  (implies (and (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem iw)
                (equal (fn-hp-x-blocks-ready b pgs-mem) :ok) (fn-hp-blocks-shape b))
           (fn-hp-vhold 0 (pgs-v-length (fn-hp-x-put-blocks b pgs-mem)) (fn-hp-x-put-blocks b pgs-mem)
                        (fn-hp-wreps iw b)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-blocks-fit-when-ready (blocks b))
                 (:instance fn-hp-x-put-blocks-words (blocks b))
                 (:instance fn-hp-x-put-blocks-frame (blocks b))
                 (:instance fn-hp-vhold-of-wreps (p 0) (np (pgs-v-length pgs-mem)) (bs b)
                            (mem2 (fn-hp-x-put-blocks b pgs-mem))))
           :in-theory (disable fn-hp-blocks-fit-when-ready fn-hp-x-put-blocks-words fn-hp-x-put-blocks-frame
                               fn-hp-vhold-of-wreps fn-hp-x-put-blocks fn-hp-vhold fn-hp-wreps fn-hp-blocks-fit
                               fn-hp-blocks-shape fn-hp-x-blocks-ready))))

; -----------------------------------------------------------------------------
; K. The pages the writer marks dirty are in the proved dirty list.

(local
 (defthm fn-hp-member-append-w
   (iff (member-equal k (append x y)) (or (member-equal k x) (member-equal k y)))))

(defthm fn-hp-body-blocks-pages-in-dirty
  (implies (and (fn-hp-deltas-ok regs ds) (natp base) (natp p)
                (fn-hp-blocks-pagep p (fn-hp-body-blocks regs ds base)))
           (member-equal p (fn-hp-body-dirty-pages regs (fn-hp-zapp regs ds) base)))
  :hints (("Goal" :induct (fn-hp-body-blocks regs ds base)
           :in-theory (disable adt-cap floor ceiling fn-hp-pack8 mod))
          ("Subgoal *1/2" :use ((:instance fn-hp-floor-block-lo (l (len (car regs))))
                                (:instance fn-hp-floor-block-hi (l (len (car regs))) (d (len (car ds))))))))
(defthm fn-hp-blocks-pages-in-append-dirty
  (implies (and (fn-hp-deltas-ok (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))) (natp p)
                (fn-hp-blocks-pagep p (fn-hp-blocks h ev salt)))
           (member-equal p (fn-hp-append-dirty h (list ev) salt)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-body-blocks-pages-in-dirty (regs (fn-hp-regs h salt))
                            (ds (fn-hp-ds ev salt (fn-hp-pes-len h))) (base 1)))
           :in-theory (e/d (fn-hp-blocks fn-hp-append-dirty)
                           (fn-hp-body-blocks-pages-in-dirty fn-hp-regs fn-hp-ds fn-hp-deltas-ok fn-hp-body-blocks
                            fn-hp-body-dirty-pages fn-hp-hb fn-hp-zapp adt-starts adt-lens)))))

; A page the writer marks dirty is in the proved dirty list of the append
; (`fn-hp-append-dirty'; m1's `fn-hp-append-dirty-bound' then bounds the
; commit) and is verified.
(defthm fn-hp-x-append-dirty
  (implies (and (fn-hp-okp h salt)
                (equal n (len h)) (equal lens (fn-hp-lens h salt)) (equal starts (fn-hp-starts h salt))
                (equal np (fn-hp-npages h salt))
                (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok)
                (natp p)
                (equal (nth p (nth *pgs-di* (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem)))) 1)
                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
           (and (member-equal p (fn-hp-append-dirty h (list ev) salt))
                (equal (pgs-vi p (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem))) 2)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-ok-unfolds)
                 (:instance fn-hp-x-append-plan-is-model)
                 (:instance fn-hp-x-append-plan-shape)
                 (:instance fn-hp-blocks-fit-when-ready (blocks (fn-hp-blocks h ev salt)))
                 (:instance fn-hp-x-put-blocks-dirty (blocks (fn-hp-blocks h ev salt)))
                 (:instance fn-hp-x-put-blocks-frame (blocks (fn-hp-blocks h ev salt)))
                 (:instance fn-hp-blocks-ready-verified (blocks (fn-hp-blocks h ev salt)))
                 (:instance fn-hp-blocks-pages-in-append-dirty)
                 (:instance fn-hp-nat-listp-lens) (:instance fn-hp-len-lens)
                 (:instance fn-hp-starts-okp-of-starts))
           :in-theory (union-theories '(fn-hp-starts-okp pgs-vi) (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; L. The keystone.
;
; KEYSTONE (the writer refines the append): at the canonical placement (the
; header's STARTS and NPAGES, where no cap grows in place:
; `fn-hp-x-append-plan-canonical-caps'; a cap that must grow is the growth
; answer), over any page store state whose
; verified pages hold the history's image words, an append that answers :ok
; leaves every verified page holding the appended history's image words,
; answers the appended history's header (N, the lengths; the region starts
; do not move), and every page it marks dirty is in the proved dirty list
; `fn-hp-append-dirty' and verified: the commit writes the new image's
; pages, O(1 + events + their octets) of them while no region doubles
; (`fn-hp-append-dirty-bound').
(defthm fn-hp-x-append-refines
  (implies (and (fn-hp-okp h salt)
                (equal n (len h)) (equal lens (fn-hp-lens h salt)) (equal starts (fn-hp-starts h salt))
                (equal np (fn-hp-npages h salt))
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))
           (let ((mem2 (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem))))
             (and (fn-hp-okp (append h (list ev)) salt)
                  (equal (mv-nth 1 (fn-hp-x-append ev salt n lens starts np pgs-mem)) (len (append h (list ev))))
                  (equal (mv-nth 2 (fn-hp-x-append ev salt n lens starts np pgs-mem))
                         (fn-hp-lens (append h (list ev)) salt))
                  (equal (fn-hp-starts (append h (list ev)) salt) starts)
                  (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-iw (append h (list ev)) salt))
                  (implies (and (natp p) (equal (nth p (nth *pgs-di* mem2)) 1)
                                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
                           (and (member-equal p (fn-hp-append-dirty h (list ev) salt))
                                (equal (pgs-vi p mem2) 2))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-ok-unfolds)
                 (:instance fn-hp-x-append-plan-is-model)
                 (:instance fn-hp-x-append-plan-shape)
                 (:instance fn-hp-vhold-after-put-blocks (b (fn-hp-blocks h ev salt)) (iw (fn-hp-iw h salt)))
                 (:instance fn-hp-iw-of-append1)
                 (:instance fn-hp-okp-of-append1)
                 (:instance fn-hp-starts-of-append1)
                 (:instance fn-hp-x-append-dirty)
                 (:instance fn-hp-nat-listp-lens) (:instance fn-hp-len-lens)
                 (:instance fn-hp-starts-okp-of-starts) (:instance fn-hp-len-append1))
           :in-theory (union-theories '(fn-hp-starts-okp) (theory 'minimal-theory)))))
