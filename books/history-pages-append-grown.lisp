; fn: the writer the host calls over a placed image whose regions grow in
; place (lane arena-store-4, 2026-09-28).  Prefix fn-hp-.
;
; KEYSTONE fn-hp-x-append-refines-placed: `fn-hp-x-append' over an image
; whose regions lie wherever the header's STARTS put them in NP pages: an
; append that answers :ok keeps every verified page holding the appended
; history's image at the same placement (a region whose cap grew grew in
; place: the writer checked that the new lengths are placed at STARTS in
; NP pages), answers its header, and marks dirty only pages of the placed
; dirty list (`fn-hp-append-pdirty'), each verified.  The model:
; `fn-hp-piw-of-append1-grown' (books/history-pages-grow-append.lisp).
(in-package "ACL2")
(include-book "history-pages-grow-append")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable floor mod pgs-true-list-fix-when-true-listp pgs-ptab-p-true-listp fn-cp-id-length-bound
                           fn-scc-encode-is-program)))

; -----------------------------------------------------------------------------
; A. The writer's plan over a placed image.

(defthm fn-hp-deltas-aligned-from-checks
  (implies (and (true-list-listp regs) (true-list-listp ds) (equal (len ds) (len regs))
                (fn-hp-x-aligned (adt-lens regs)) (fn-hp-x-aligned (adt-lens ds)))
           (fn-hp-deltas-aligned regs ds))
  :hints (("Goal" :induct (fn-hp-deltas-aligned regs ds))))

(defthm fn-hp-x-append-plan-is-pblocks-grown
  (implies (and (fn-hp-okp h salt)
                (not (mv-nth 0 (fn-hp-x-append-plan ev salt (len h) (fn-hp-lens h salt) starts np))))
           (and (equal (mv-nth 1 (fn-hp-x-append-plan ev salt (len h) (fn-hp-lens h salt) starts np))
                       (fn-hp-pblocks h ev salt starts))
                (equal (mv-nth 2 (fn-hp-x-append-plan ev salt (len h) (fn-hp-lens h salt) starts np))
                       (fn-hp-lens (append h (list ev)) salt))
                (fn-hp-deltas-aligned (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))
                (adt-placement-ok starts (fn-hp-lens (append h (list ev)) salt) np)
                (unsigned-byte-p 64 (* 16384 (adt-end-l (fn-hp-lens (append h (list ev)) salt) 1)))
                (unsigned-byte-p 64 (+ 1 (len h)))
                (fn-hp-evp ev)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-pe-def) (:instance fn-hp-lens-of-append1)
                 (:instance fn-hp-ds-words-of-ds (off (fn-hp-pes-len h))) (:instance fn-hp-u64-pool-len)
                 (:instance fn-hp-u64-listp-of-x-add (a (adt-lens (fn-hp-regs h salt))) (b (list 8 8 8 8 (len (fn-hp-pe ev)))))
                 (:instance fn-hp-deltas-aligned-from-checks (regs (fn-hp-regs h salt)) (ds (fn-hp-ds ev salt (fn-hp-pes-len h)))))
           :in-theory (e/d (fn-hp-pblocks fn-hp-lens)
                           (fn-hp-deltas-aligned-from-checks fn-hp-ds-words-of-ds fn-hp-u64-listp-of-x-add fn-hp-regs fn-hp-ds
                            fn-hp-pe fn-scc-encode fn-scc-program adt-placement-ok fn-hp-x-unfit adt-end-l
                            fn-hp-mkey fn-hp-pad8 fn-hp-x-aligned adt-cap fn-hp-pack8 floor mod
                            fn-hp-deltas-aligned fn-hp-okp adt-starts adt-lens fn-hp-zapp fn-hp-body-blocks
                            fn-hp-lens-of-append1 adt-starts-is-starts-l fn-sccb-treep
                            fn-hp-x-add fn-hp-bb-list fn-hp-ds-words)))))

(defthm fn-hp-okp-of-append1-grown
  (implies (and (fn-hp-okp h salt) (fn-hp-evp ev) (unsigned-byte-p 64 (+ 1 (len h)))
                (unsigned-byte-p 64 (* 16384 (adt-end-l (fn-hp-lens (append h (list ev)) salt) 1))))
           (fn-hp-okp (append h (list ev)) salt))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-len-image (h (append h (list ev))))
                 (:instance fn-hp-npages-is-end-l (h (append h (list ev)))))
           :in-theory (e/d (fn-hp-okp) (fn-hp-evp fn-hp-image fn-hp-npages fn-hp-regs fn-hp-lens adt-end-l
                                        fn-hp-len-image fn-hp-npages-is-end-l)))))

; -----------------------------------------------------------------------------
; B. The pages the writer marks dirty over grown regions.

(local
 (defthm fn-hp-member-append-ag
   (iff (member-equal k (append x y)) (or (member-equal k x) (member-equal k y)))))

(defthm fn-hp-bb-pages-in-pdirty-aligned
  (implies (and (fn-hp-deltas-aligned regs ds) (natp p)
                (fn-hp-blocks-pagep p (fn-hp-bb-list starts (adt-lens regs) (fn-hp-ds-words ds))))
           (member-equal p (fn-hp-pdirty-pages regs (fn-hp-zapp regs ds) starts)))
  :hints (("Goal" :induct (fn-hp-rtriples regs ds starts)
           :in-theory (disable adt-cap floor ceiling fn-hp-pack8 mod))
          ("Subgoal *1/2" :use ((:instance fn-hp-floor-block-lo (l (len (car regs))) (base (nfix (car starts))))
                                (:instance fn-hp-floor-block-hi (l (len (car regs))) (d (len (car ds)))
                                           (base (nfix (car starts))))))))

(defthm fn-hp-pblocks-pages-in-pdirty-aligned
  (implies (and (fn-hp-deltas-aligned (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))) (natp p)
                (equal (len starts) 5)
                (fn-hp-blocks-pagep p (fn-hp-pblocks h ev salt starts)))
           (member-equal p (fn-hp-append-pdirty h (list ev) salt starts)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-bb-pages-in-pdirty-aligned (regs (fn-hp-regs h salt))
                            (ds (fn-hp-ds ev salt (fn-hp-pes-len h)))))
           :in-theory (e/d (fn-hp-pblocks fn-hp-append-pdirty)
                           (fn-hp-bb-pages-in-pdirty-aligned fn-hp-regs fn-hp-ds fn-hp-deltas-aligned fn-hp-bb-list
                            fn-hp-pdirty-pages fn-hp-zapp adt-starts adt-lens fn-hp-ds-words)))))

(defthm fn-hp-x-append-dirty-placed
  (implies (and (fn-hp-okp h salt)
                (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
                (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok)
                (natp p)
                (equal (nth p (nth *pgs-di* (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem)))) 1)
                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
           (and (member-equal p (fn-hp-append-pdirty h (list ev) salt starts))
                (equal (pgs-vi p (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem))) 2)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-ok-unfolds)
                 (:instance fn-hp-x-append-plan-is-pblocks-grown)
                 (:instance fn-hp-x-append-plan-shape)
                 (:instance fn-hp-blocks-fit-when-ready (blocks (fn-hp-pblocks h ev salt starts)))
                 (:instance fn-hp-x-put-blocks-dirty (blocks (fn-hp-pblocks h ev salt starts)))
                 (:instance fn-hp-x-put-blocks-frame (blocks (fn-hp-pblocks h ev salt starts)))
                 (:instance fn-hp-blocks-ready-verified (blocks (fn-hp-pblocks h ev salt starts)))
                 (:instance fn-hp-pblocks-pages-in-pdirty-aligned)
                 (:instance fn-hp-nat-listp-lens) (:instance fn-hp-len-lens))
           :in-theory (union-theories '(fn-hp-starts-okp pgs-vi) (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; C. The keystone.
;
; KEYSTONE (the writer over ANY placement, growing in place): over any page
; store state whose verified pages hold the history's image placed at
; STARTS in NP pages, an append that answers :ok leaves every verified page
; holding the appended history's image at the same placement, answers its
; header, the new lengths are placed at STARTS in NP pages (a region whose
; cap grew grew in place), and it marks dirty only pages of the placed dirty
; list, each verified.  The placement of the old lengths is not a
; hypothesis: the writer refuses :placement without it.  The canonical
; keystone `fn-hp-x-append-refines' is the canonical placement's case, where
; no cap grows in place (`fn-hp-x-append-plan-canonical-caps').
(defthm fn-hp-x-append-refines-placed
  (implies (and (fn-hp-okp h salt)
                (equal n (len h)) (equal lens (fn-hp-lens h salt))
                (fn-hp-starts-okp starts)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))
           (let ((mem2 (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem))))
             (and (fn-hp-okp (append h (list ev)) salt)
                  (equal (mv-nth 1 (fn-hp-x-append ev salt n lens starts np pgs-mem)) (len (append h (list ev))))
                  (equal (mv-nth 2 (fn-hp-x-append ev salt n lens starts np pgs-mem))
                         (fn-hp-lens (append h (list ev)) salt))
                  (adt-placement-ok starts (fn-hp-lens (append h (list ev)) salt) np)
                  (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw (append h (list ev)) salt starts np))
                  (implies (and (natp p) (equal (nth p (nth *pgs-di* mem2)) 1)
                                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
                           (and (member-equal p (fn-hp-append-pdirty h (list ev) salt starts))
                                (equal (pgs-vi p mem2) 2))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-ok-unfolds)
                 (:instance fn-hp-x-append-plan-is-pblocks-grown)
                 (:instance fn-hp-x-append-plan-shape)
                 (:instance fn-hp-vhold-after-put-blocks (b (fn-hp-pblocks h ev salt starts))
                            (iw (fn-hp-piw h salt starts np)))
                 (:instance fn-hp-piw-of-append1-grown)
                 (:instance fn-hp-okp-of-append1-grown)
                 (:instance fn-hp-x-append-dirty-placed)
                 (:instance fn-hp-nat-listp-lens) (:instance fn-hp-len-lens)
                 (:instance fn-hp-len-append1))
           :in-theory (union-theories '(fn-hp-starts-okp) (theory 'minimal-theory)))))
