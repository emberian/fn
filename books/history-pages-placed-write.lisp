; fn: the history's writer over a placed image (lane arena-store-3,
; 2026-09-28).  Prefix fn-hp-.
;
; KEYSTONE fn-hp-x-append-refines-placed: the writer the host calls
; (`fn-hp-x-append') over an image whose regions lie wherever the header's
; starts put them: an append that answers :ok keeps every verified page
; holding the appended history's image at the same placement, answers its
; header, keeps the placement valid, and marks dirty only pages of the
; placed dirty list (`fn-hp-append-pdirty'), each verified.  The model:
; `fn-hp-piw-of-append1', proved from generic facts about replacements
; that nest and commute (section A).
(in-package "ACL2")
(include-book "history-pages-nest")
(local (include-book "arithmetic/top" :dir :system))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-scc-octet-listp-facts . 2))))
(local (in-theory (disable floor mod pgs-true-list-fix-when-true-listp pgs-ptab-p-true-listp fn-cp-id-length-bound)))

; -----------------------------------------------------------------------------
; B. The writer's blocks over a placed image.

(defun fn-hp-pblocks (h ev salt starts)
  ; the six blocks of an append of EV to H whose regions lie at STARTS
  (declare (xargs :verify-guards nil))
  (let ((regs (fn-hp-regs h salt)) (ds (fn-hp-ds ev salt (fn-hp-pes-len h))))
    (cons (cons 6 (fn-hp-hb (+ 1 (len h)) starts (adt-lens (fn-hp-zapp regs ds))))
          (fn-hp-bb-list starts (adt-lens regs) (fn-hp-ds-words ds)))))

(defthm fn-hp-hdr2-of-append1
  (implies (and (equal (len starts) 5) (equal (len lens) 5) (equal (len lens2) 5))
           (equal (fn-hp-hdr2 (+ 1 n) lens2 starts np)
                  (fn-hp-rep (fn-hp-hdr2 n lens starts np) 6 (fn-hp-hb (+ 1 n) starts lens2))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-rep-middle (p (append (list *fn-hp-magic-word* *adt-version*) *fn-hp-schema-words*))
                            (j 0) (x (list* n 5 (fn-hp-meta-words starts lens)))
                            (y (cons np (adt-zeros 2029)))
                            (b (fn-hp-hb (+ 1 n) starts lens2))))
           :in-theory (e/d (fn-hp-rep) (fn-hp-rep-middle (:e adt-zeros) adt-zeros)))))

(defun fn-hp-rtriples (regs ds starts)
  ; per region: its block at its start, whose end grows by its delta
  (declare (xargs :verify-guards nil))
  (if (or (atom regs) (atom starts)) nil
    (cons (list (* 2048 (nfix (car starts))) (fn-hp-wpad (car regs)) (floor (len (car regs)) 8)
                (fn-hp-pack8 (floor (len (car ds)) 8) (car ds)))
          (fn-hp-rtriples (cdr regs) (cdr ds) (cdr starts)))))

(defthm fn-hp-outer-rtriples
  (equal (fn-hp-outer (fn-hp-rtriples regs ds starts)) (fn-hp-rblocks regs starts))
  :hints (("Goal" :induct (fn-hp-rtriples regs ds starts) :in-theory (disable fn-hp-wpad fn-hp-pack8 floor))))

(defthm fn-hp-inner-rtriples
  (implies (<= (len regs) (len ds))
           (equal (fn-hp-inner (fn-hp-rtriples regs ds starts))
                  (fn-hp-bb-list starts (adt-lens regs) (fn-hp-ds-words ds))))
  :hints (("Goal" :induct (fn-hp-rtriples regs ds starts) :in-theory (disable fn-hp-wpad fn-hp-pack8 floor))))

(defthm fn-hp-outer2-rtriples
  (implies (fn-hp-deltas-ok regs ds)
           (equal (fn-hp-outer2 (fn-hp-rtriples regs ds starts)) (fn-hp-rblocks (fn-hp-zapp regs ds) starts)))
  :hints (("Goal" :induct (fn-hp-rtriples regs ds starts) :in-theory (disable fn-hp-wpad fn-hp-pack8 floor adt-cap mod))
          ("Subgoal *1/2" :use ((:instance fn-hp-wpad-of-append (r (car regs)) (d (car ds)))))))

(local
 (defthm fn-hp-delta-fits-words
   (implies (and (natp lr) (natp ld) (equal (mod lr 8) 0) (equal (mod ld 8) 0)
                 (equal (adt-cap (+ lr ld)) (adt-cap lr)))
            (<= (+ (floor lr 8) (floor ld 8)) (* 2048 (adt-cap lr))))
   :hints (("Goal" :use ((:instance adt-cap-covers (u (+ lr ld)))
                         (:instance fn-hp-floor-8-exact (x lr)) (:instance fn-hp-floor-8-exact (x ld)))
            :in-theory (disable adt-cap-covers fn-hp-floor-8-exact adt-cap)))
   :rule-classes :linear))

(defthm fn-hp-triples-ok-rtriples
  (implies (and (fn-hp-deltas-ok regs ds) (adt-placement-ok starts (adt-lens regs) np))
           (fn-hp-triples-ok (fn-hp-rtriples regs ds starts) (* 2048 np)))
  :hints (("Goal" :induct (fn-hp-rtriples regs ds starts) :in-theory (disable fn-hp-wpad fn-hp-pack8 adt-cap))))

(defthm fn-hp-placement-np-pos
  (implies (and (adt-placement-ok starts lens np) (consp starts) (consp lens))
           (and (natp np) (<= 1 np)))
  :hints (("Goal" :expand ((adt-placement-ok starts lens np)) :in-theory (disable adt-cap)))
  :rule-classes nil)

(local
 (defthm fn-hp-consp-when-len-5
   (implies (equal (len x) 5) (consp x))))

(local
 (defthm fn-hp-len-lens-regs-5
   (equal (len (adt-lens (fn-hp-regs h salt))) 5)
   :hints (("Goal" :in-theory (disable fn-hp-regs)))))

; The placed model theorem: the appended history's placed image is the old
; placed image with the six blocks of `fn-hp-pblocks' in place, when no
; region's cap changes.
(defthm fn-hp-piw-of-append1
  (implies (and (adt-placement-ok starts (fn-hp-lens h salt) np) (equal (len starts) 5)
                (fn-hp-deltas-ok (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))
           (equal (fn-hp-piw (append h (list ev)) salt starts np)
                  (fn-hp-wreps (fn-hp-piw h salt starts np) (fn-hp-pblocks h ev salt starts))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-wreps-nest (w (adt-zeros (* 2048 (nfix np))))
                            (ts (cons (list 0 (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np) 6
                                            (fn-hp-hb (+ 1 (len h)) starts
                                                      (adt-lens (fn-hp-zapp (fn-hp-regs h salt)
                                                                            (fn-hp-ds ev salt (fn-hp-pes-len h))))))
                                      (fn-hp-rtriples (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)) starts))))
                 (:instance fn-hp-hdr2-of-append1 (n (len h)) (lens (fn-hp-lens h salt))
                            (lens2 (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))))
                 (:instance fn-hp-placement-np-pos (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-len-regs-5)
                 (:instance adt-lens-starts-shape (regs (fn-hp-regs h salt)))
                 (:instance adt-lens-starts-shape (regs (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))))
                 (:instance fn-hp-rblocks-apart (regs (fn-hp-regs h salt)))
                 (:instance fn-hp-hdr-apart-rblocks (regs (fn-hp-regs h salt))
                            (hdr (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np)))
                 (:instance fn-hp-triples-ok-rtriples (regs (fn-hp-regs h salt)) (ds (fn-hp-ds ev salt (fn-hp-pes-len h)))))
           :in-theory (e/d (fn-hp-piw fn-hp-lens fn-hp-pblocks)
                           (fn-hp-wreps-nest fn-hp-hdr2-of-append1 fn-hp-rblocks-apart fn-hp-hdr-apart-rblocks
                            fn-hp-triples-ok-rtriples fn-hp-wreps fn-hp-rep fn-hp-hdr2 fn-hp-hb fn-hp-rblocks
                            fn-hp-rtriples fn-hp-regs fn-hp-ds fn-hp-deltas-ok adt-placement-ok fn-hp-zapp
                            fn-hp-bb-list fn-hp-ds-words adt-lens adt-zeros (:e adt-zeros)
                            fn-hp-block-apart)))))

(local (in-theory (disable fn-hp-consp-when-len-5 fn-scc-encode-is-program)))

; -----------------------------------------------------------------------------
; C. The writer over a placed image.

(defthm fn-hp-x-append-plan-is-pblocks
  (implies (and (fn-hp-okp h salt)
                (not (mv-nth 0 (fn-hp-x-append-plan ev salt (len h) (fn-hp-lens h salt) starts))))
           (and (equal (mv-nth 1 (fn-hp-x-append-plan ev salt (len h) (fn-hp-lens h salt) starts))
                       (fn-hp-pblocks h ev salt starts))
                (equal (mv-nth 2 (fn-hp-x-append-plan ev salt (len h) (fn-hp-lens h salt) starts))
                       (fn-hp-lens (append h (list ev)) salt))
                (fn-hp-deltas-ok (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))
                (unsigned-byte-p 64 (+ 1 (len h)))
                (fn-hp-evp ev)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-pe-def)
                 (:instance fn-hp-ds-words-of-ds (off (fn-hp-pes-len h))) (:instance fn-hp-u64-pool-len)
                 (:instance fn-hp-u64-listp-of-x-add (a (adt-lens (fn-hp-regs h salt))) (b (list 8 8 8 8 (len (fn-hp-pe ev)))))
                 (:instance fn-hp-deltas-ok-from-checks (regs (fn-hp-regs h salt)) (ds (fn-hp-ds ev salt (fn-hp-pes-len h)))))
           :in-theory (e/d (fn-hp-pblocks fn-hp-lens)
                           (fn-hp-deltas-ok-from-checks fn-hp-ds-words-of-ds fn-hp-u64-listp-of-x-add fn-hp-regs fn-hp-ds
                            fn-hp-pe fn-scc-encode fn-scc-program
                            fn-hp-mkey fn-hp-pad8 fn-hp-x-caps-ok fn-hp-x-aligned adt-cap fn-hp-pack8 floor mod
                            fn-hp-deltas-ok fn-hp-okp adt-starts adt-lens fn-hp-zapp fn-hp-body-blocks
                            fn-hp-lens-of-append1 adt-starts-is-starts-l fn-sccb-treep
                            fn-hp-x-add fn-hp-bb-list fn-hp-ds-words)))))

(defun fn-hp-same-caps (lens lens2)
  (declare (xargs :verify-guards nil))
  (if (or (atom lens) (atom lens2)) (and (atom lens) (atom lens2))
    (and (equal (adt-cap (nfix (car lens))) (adt-cap (nfix (car lens2))))
         (fn-hp-same-caps (cdr lens) (cdr lens2)))))

(defthm fn-hp-apart-same-caps
  (implies (fn-hp-same-caps lens lens2)
           (equal (adt-apart s c starts lens2) (adt-apart s c starts lens)))
  :hints (("Goal" :induct (list (adt-apart s c starts lens) (fn-hp-same-caps lens lens2)) :in-theory (disable adt-cap))))

(defthm fn-hp-placement-same-caps
  (implies (fn-hp-same-caps lens lens2)
           (equal (adt-placement-ok starts lens2 np) (adt-placement-ok starts lens np)))
  :hints (("Goal" :induct (list (adt-placement-ok starts lens np) (fn-hp-same-caps lens lens2)) :in-theory (disable adt-cap))))

(defthm fn-hp-same-caps-of-zapp
  (implies (fn-hp-deltas-ok regs ds)
           (fn-hp-same-caps (adt-lens regs) (adt-lens (fn-hp-zapp regs ds))))
  :hints (("Goal" :in-theory (disable adt-cap))))

(defun fn-hp-pdirty-pages (regs regs2 starts)
  ; per region at its start, the pages its new octets overlap
  (declare (xargs :verify-guards nil))
  (if (or (atom regs) (atom regs2) (atom starts)) nil
    (append (fn-hp-range (+ (nfix (car starts)) (floor (len (car regs)) 16384))
                         (+ (nfix (car starts)) (ceiling (len (car regs2)) 16384)))
            (fn-hp-pdirty-pages (cdr regs) (cdr regs2) (cdr starts)))))

(defun fn-hp-append-pdirty (h new salt starts)
  ; the pages an append of NEW to H whose regions lie at STARTS changes:
  ; the header and, per region, the pages its new octets overlap
  (declare (xargs :verify-guards nil))
  (cons 0 (fn-hp-pdirty-pages (fn-hp-regs h salt) (fn-hp-regs (append h new) salt) starts)))

(local
 (defthm fn-hp-member-append-g
   (iff (member-equal k (append x y)) (or (member-equal k x) (member-equal k y)))))

(defthm fn-hp-bb-pages-in-pdirty
  (implies (and (fn-hp-deltas-ok regs ds) (natp p)
                (fn-hp-blocks-pagep p (fn-hp-bb-list starts (adt-lens regs) (fn-hp-ds-words ds))))
           (member-equal p (fn-hp-pdirty-pages regs (fn-hp-zapp regs ds) starts)))
  :hints (("Goal" :induct (fn-hp-rtriples regs ds starts)
           :in-theory (disable adt-cap floor ceiling fn-hp-pack8 mod))
          ("Subgoal *1/2" :use ((:instance fn-hp-floor-block-lo (l (len (car regs))) (base (nfix (car starts))))
                                (:instance fn-hp-floor-block-hi (l (len (car regs))) (d (len (car ds)))
                                           (base (nfix (car starts))))))))

(defthm fn-hp-pblocks-pages-in-pdirty
  (implies (and (fn-hp-deltas-ok (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))) (natp p)
                (equal (len starts) 5)
                (fn-hp-blocks-pagep p (fn-hp-pblocks h ev salt starts)))
           (member-equal p (fn-hp-append-pdirty h (list ev) salt starts)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-bb-pages-in-pdirty (regs (fn-hp-regs h salt))
                            (ds (fn-hp-ds ev salt (fn-hp-pes-len h)))))
           :in-theory (e/d (fn-hp-pblocks fn-hp-append-pdirty)
                           (fn-hp-bb-pages-in-pdirty fn-hp-regs fn-hp-ds fn-hp-deltas-ok fn-hp-bb-list
                            fn-hp-pdirty-pages fn-hp-zapp adt-starts adt-lens fn-hp-ds-words)))))

(defthm fn-hp-x-append-dirty-placed
  (implies (and (fn-hp-okp h salt)
                (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
                (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts pgs-mem)) :ok)
                (natp p)
                (equal (nth p (nth *pgs-di* (mv-nth 3 (fn-hp-x-append ev salt n lens starts pgs-mem)))) 1)
                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
           (and (member-equal p (fn-hp-append-pdirty h (list ev) salt starts))
                (equal (pgs-vi p (mv-nth 3 (fn-hp-x-append ev salt n lens starts pgs-mem))) 2)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-ok-unfolds)
                 (:instance fn-hp-x-append-plan-is-pblocks)
                 (:instance fn-hp-x-append-plan-shape)
                 (:instance fn-hp-blocks-fit-when-ready (blocks (fn-hp-pblocks h ev salt starts)))
                 (:instance fn-hp-x-put-blocks-dirty (blocks (fn-hp-pblocks h ev salt starts)))
                 (:instance fn-hp-x-put-blocks-frame (blocks (fn-hp-pblocks h ev salt starts)))
                 (:instance fn-hp-blocks-ready-verified (blocks (fn-hp-pblocks h ev salt starts)))
                 (:instance fn-hp-pblocks-pages-in-pdirty)
                 (:instance fn-hp-nat-listp-lens) (:instance fn-hp-len-lens))
           :in-theory (union-theories '(fn-hp-starts-okp pgs-vi) (theory 'minimal-theory)))))

(defthm fn-hp-placement-of-append1
  (implies (fn-hp-deltas-ok (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))
           (equal (adt-placement-ok starts (fn-hp-lens (append h (list ev)) salt) np)
                  (adt-placement-ok starts (fn-hp-lens h salt) np)))
  :hints (("Goal" :use ((:instance fn-hp-same-caps-of-zapp (regs (fn-hp-regs h salt)) (ds (fn-hp-ds ev salt (fn-hp-pes-len h)))))
           :in-theory (e/d (fn-hp-lens) (fn-hp-same-caps-of-zapp fn-hp-regs fn-hp-ds fn-hp-deltas-ok adt-placement-ok
                                         fn-hp-zapp adt-lens)))))

; KEYSTONE (the writer over ANY placement): over any page store state whose
; verified pages hold the history's image placed at STARTS in NP pages, an
; append that answers :ok leaves every verified page holding the appended
; history's image at the same placement, answers its header, keeps the
; placement valid, and marks dirty only pages of the placed dirty list,
; each verified.  The canonical keystone `fn-hp-x-append-refines' is its
; instance at the canonical placement (`fn-hp-piw-canonical').
(defthm fn-hp-x-append-refines-placed
  (implies (and (fn-hp-okp h salt)
                (equal n (len h)) (equal lens (fn-hp-lens h salt))
                (fn-hp-starts-okp starts) (adt-placement-ok starts lens np)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts pgs-mem)) :ok))
           (let ((mem2 (mv-nth 3 (fn-hp-x-append ev salt n lens starts pgs-mem))))
             (and (fn-hp-okp (append h (list ev)) salt)
                  (equal (mv-nth 1 (fn-hp-x-append ev salt n lens starts pgs-mem)) (len (append h (list ev))))
                  (equal (mv-nth 2 (fn-hp-x-append ev salt n lens starts pgs-mem))
                         (fn-hp-lens (append h (list ev)) salt))
                  (adt-placement-ok starts (fn-hp-lens (append h (list ev)) salt) np)
                  (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw (append h (list ev)) salt starts np))
                  (implies (and (natp p) (equal (nth p (nth *pgs-di* mem2)) 1)
                                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
                           (and (member-equal p (fn-hp-append-pdirty h (list ev) salt starts))
                                (equal (pgs-vi p mem2) 2))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-ok-unfolds)
                 (:instance fn-hp-x-append-plan-is-pblocks)
                 (:instance fn-hp-x-append-plan-shape)
                 (:instance fn-hp-vhold-after-put-blocks (b (fn-hp-pblocks h ev salt starts))
                            (iw (fn-hp-piw h salt starts np)))
                 (:instance fn-hp-piw-of-append1)
                 (:instance fn-hp-okp-of-append1)
                 (:instance fn-hp-placement-of-append1)
                 (:instance fn-hp-x-append-dirty-placed)
                 (:instance fn-hp-nat-listp-lens) (:instance fn-hp-len-lens)
                 (:instance fn-hp-len-append1))
           :in-theory (union-theories '(fn-hp-starts-okp) (theory 'minimal-theory)))))


; The placed dirty list's size: per region at most two partial pages plus
; the pages its new octets fill -- the same bound as the canonical
; `fn-hp-dirty-pages-bound', wherever the regions lie.
(defthm fn-hp-pdirty-pages-bound
  (implies (fn-hp-prefixes regs regs2)
           (<= (* 16384 (len (fn-hp-pdirty-pages regs regs2 starts)))
               (+ (- (fn-hp-regs-octets regs2) (fn-hp-regs-octets regs)) (* 2 16384 (len regs)))))
  :hints (("Goal" :induct (fn-hp-pdirty-pages regs regs2 starts)
           :in-theory (disable floor ceiling adt-cap))
          ("Subgoal *1/2" :use ((:instance fn-hp-ceiling-16384-upper (l (len (car regs2))))
                                (:instance fn-hp-floor-16384-lower (l (len (car regs))))
                                (:instance fn-hp-floor-le-ceiling-16384 (l1 (len (car regs))) (l2 (len (car regs2))))))))
