; fn: the append step the host calls per committed event (lane
; arena-store-4, 2026-09-28, m3c P1).  Prefix fn-hp-.
;
; `fn-hp-x-append-step' is the one function the host calls per committed
; event: the writer (`fn-hp-x-append'); on (:grow R C) the relocation
; (`fn-hp-x-relocate' R C) and the writer again, at most five relocations
; (`fn-hp-x-append-loop' with fuel 5: six attempts).  The fuel is not a
; ceiling that can bite: by `fn-hp-grow-then-append' each :grow after a
; relocation of R names a later region, so the step never answers :grow
; (`fn-hp-x-append-loop-not-grow', and the keystone's second conjunct).
;
; KEYSTONE fn-hp-x-append-step-refines: over the placed image of H at
; STARTS in NP pages, :ok means the store holds the image of H + EV at the
; answered placement (STARTS2 NP2), with its header answer (N2 LENS2) and
; the placement valid; any other answer means the history is unchanged and
; the store holds H's image at (STARTS2 NP2) -- when a relocation
; completed before a need-verdict or refusal, STARTS2 NP2 is the relocated
; placement (each relocation is a complete step whose invariant holds, and
; its header words are written), so the host keeps STARTS2 NP2, serves the
; need-verdict and calls the step again.  Every page newly dirty is
; verified.
;
; Work per event: the writer's O(dirty pages) block writes, plus per
; relocation 2 * 2048 * cap(R) word copies and zeroings and a resize of the
; store (`pgs-x-grow-image', O(image)).  Caps double (`adt-cap'), so a
; region is relocated O(log size) times; the copy work over a whole import
; is amortized O(1) words per octet appended.  The resize is what the page
; store's growth costs; not proved here, and no bound on the total is
; claimed by a theorem.
(in-package "ACL2")
(include-book "history-pages-grow-then-append")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable floor mod pgs-true-list-fix-when-true-listp pgs-ptab-p-true-listp fn-cp-id-length-bound
                           fn-scc-encode-is-program)))

(defthm fn-hp-x-append-not-ok-unchanged
  (implies (not (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))
           (and (equal (mv-nth 1 (fn-hp-x-append ev salt n lens starts np pgs-mem)) n)
                (equal (mv-nth 2 (fn-hp-x-append ev salt n lens starts np pgs-mem)) lens)
                (equal (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem)) pgs-mem)))
  :hints (("Goal" :in-theory (disable fn-hp-x-append-plan fn-hp-x-blocks-ready fn-hp-x-put-blocks))))

(defthm fn-hp-x-append-grow-shape
  (implies (and (nat-listp lens) (equal (len lens) 5)
                (equal (car (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem))) :grow))
           (let ((v (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem))))
             (and (equal v (list :grow (cadr v) (caddr v)))
                  (natp (cadr v)) (< (cadr v) 5) (natp (caddr v)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-grow-is-plan) (:instance fn-hp-x-append-plan-grow)
                 (:instance fn-hp-x-append-grow-region))
           :in-theory (disable fn-hp-x-append-grow-is-plan fn-hp-x-append-plan-grow fn-hp-x-append-grow-region
                               fn-hp-x-append fn-hp-x-append-plan adt-placement-ok fn-hp-x-unfit adt-cap))))

(local (in-theory (disable fn-hp-x-append-grow-is-plan fn-hp-x-append-plan-grow fn-hp-x-append-grow-region fn-hp-x-append-grow-shape)))

(local
 (defthm fn-hp-nat-listp-update-nth-s
   (implies (and (nat-listp l) (natp v) (natp r) (< r (len l))) (nat-listp (update-nth r v l)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(defun fn-hp-x-append-loop (k ev salt n lens starts np pgs-mem)
  ; the writer; on (:grow R C) with fuel K left, the relocation and the
  ; loop again; a relocation's answer other than :ok is returned with the
  ; placement as it was before that relocation (nothing changed)
  (declare (xargs :stobjs pgs-mem
                  :measure (nfix k)
                  :hints (("Goal" :in-theory (disable fn-hp-x-append fn-hp-x-relocate)))
                  :guard (and (natp k) (natp n) (nat-listp lens) (equal (len lens) 5)
                              (nat-listp starts) (equal (len starts) 5) (natp np))
                  :guard-hints (("Goal" :use ((:instance fn-hp-x-append-grow-shape)
                                              (:instance fn-hp-x-relocate-ok-unfolds
                                                         (r (cadr (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem))))
                                                         (c (caddr (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem))))))
                                 :in-theory (disable fn-hp-x-append-grow-shape fn-hp-x-relocate-ok-unfolds
                                                     fn-hp-x-append fn-hp-x-relocate fn-hp-x-append-plan adt-cap
                                                     fn-hp-x-blocks-ready fn-hp-x-put-blocks adt-placement-ok)))))
  (mv-let (v n2 lens2 pgs-mem)
    (fn-hp-x-append ev salt n lens starts np pgs-mem)
    (if (and (consp v) (eq (car v) :grow) (not (zp k)))
        (mv-let (rv starts2 np2 pgs-mem)
          (fn-hp-x-relocate (cadr v) (caddr v) n lens starts np pgs-mem)
          (if (eq rv :ok)
              (fn-hp-x-append-loop (1- k) ev salt n lens starts2 np2 pgs-mem)
            (mv rv n lens starts np pgs-mem)))
      (mv v n2 lens2 starts np pgs-mem))))

(defun fn-hp-x-append-step (ev salt n lens starts np pgs-mem)
  ; The append of the committed event EV as the host calls it, over the
  ; header answer (N LENS STARTS NP) it carries: (mv VERDICT N2 LENS2
  ; STARTS2 NP2 pgs-mem).  :ok, a need-verdict ((:need-table T P),
  ; (:need-page P PHYS), :out-of-range) or (:refused REASON); never :grow.
  ; The host carries (N2 LENS2 STARTS2 NP2) whatever the verdict.
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp n) (nat-listp lens) (equal (len lens) 5)
                              (nat-listp starts) (equal (len starts) 5) (natp np))))
  (fn-hp-x-append-loop 5 ev salt n lens starts np pgs-mem))

(defthm fn-hp-x-relocate-not-grow
  (not (equal (car (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem))) :grow))
  :hints (("Goal" :use ((:instance fn-hp-x-ready-not-grow (p 0))
                        (:instance fn-hp-x-ready-range-not-grow (p (nth r starts)) (hi (+ (nth r starts) (adt-cap (nth r lens))))))
           :in-theory (disable fn-hp-x-ready-not-grow fn-hp-x-ready-range-not-grow
                               fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark fn-hp-x-ready fn-hp-x-ready-range
                               fn-hp-hdr-m adt-cap adt-placement-ok fn-hp-u64-listp pgs-x-grow-image))))

(local
 (defthm fn-hp-nth-2-below-len
   (implies (and (natp p) (equal (nth p l) 2)) (< p (len l)))
   :hints (("Goal" :in-theory (enable nth)))
   :rule-classes nil))

(local
 (defthm fn-hp-vi-2-below-length
   (implies (and (natp p) (equal (pgs-vi p pgs-mem) 2)) (< p (pgs-v-length pgs-mem)))
   :hints (("Goal" :use ((:instance fn-hp-nth-2-below-len (l (nth *pgs-vi* pgs-mem))))
            :in-theory (enable pgs-vi pgs-v-length)))
   :rule-classes nil))

(defthm fn-hp-x-append-keeps-verified
  (implies (and (fn-hp-starts-okp starts) (nat-listp lens) (equal (len lens) 5)
                (natp p) (equal (pgs-vi p pgs-mem) 2))
           (equal (pgs-vi p (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem))) 2))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))
           :use ((:instance fn-hp-x-append-ok-unfolds)
                 (:instance fn-hp-x-append-plan-shape)
                 (:instance fn-hp-blocks-fit-when-ready (blocks (mv-nth 1 (fn-hp-x-append-plan ev salt n lens starts np))))
                 (:instance fn-hp-x-put-blocks-frame (blocks (mv-nth 1 (fn-hp-x-append-plan ev salt n lens starts np)))))
           :in-theory (e/d (pgs-vi) (fn-hp-x-append-ok-unfolds fn-hp-x-append-plan-shape fn-hp-x-put-blocks-frame
                               fn-hp-x-append fn-hp-x-append-plan fn-hp-x-put-blocks fn-hp-x-blocks-ready)))))

(defthm fn-hp-x-relocate-keeps-verified
  (implies (and (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
                (natp r) (< r 5) (natp c)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                (natp p) (equal (pgs-vi p pgs-mem) 2))
           (equal (pgs-vi p (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem))) 2))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))
           :use ((:instance fn-hp-x-relocate-mem2-frame)
                 (:instance fn-hp-x-relocate-ok-checks)
                 (:instance fn-hp-vi-2-below-length)
                 (:instance fn-hp-grow-image-vi (q p) (npn (+ np c))))
           :in-theory (e/d (pgs-vi) (fn-hp-x-relocate-mem2-frame fn-hp-grow-image-vi fn-hp-x-relocate pgs-x-grow-image
                                     fn-hp-vhold fn-hp-piw fn-hp-lens adt-cap adt-placement-ok fn-hp-x-ready fn-hp-x-ready-range
                                     fn-hp-hdr-m fn-hp-u64-listp)))))

(defmacro fn-hp-av ()
  ; the append's verdict at the loop's arguments
  '(mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)))

(defmacro fn-hp-rel (i)
  ; the relocation the loop makes on (:grow R C)
  `(mv-nth ,i (fn-hp-x-relocate (cadr (fn-hp-av)) (caddr (fn-hp-av)) n lens starts np pgs-mem)))

(defthm fn-hp-x-append-grow-mem
  (implies (equal (car (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem))) :grow)
           (equal (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem)) pgs-mem))
  :hints (("Goal" :use ((:instance fn-hp-x-append-grow-is-plan))
           :in-theory (disable fn-hp-x-append-grow-is-plan fn-hp-x-append))))

(defthm fn-hp-loop-progress
  (implies (and (nat-listp lens) (equal (len lens) 5) (equal (len starts) 5)
                (equal (car (fn-hp-av)) :grow)
                (equal (fn-hp-rel 0) :ok)
                (equal (car (mv-nth 0 (fn-hp-x-append ev salt n lens (fn-hp-rel 1) (fn-hp-rel 2) (fn-hp-rel 3)))) :grow))
           (and (< (cadr (fn-hp-av)) (cadr (mv-nth 0 (fn-hp-x-append ev salt n lens (fn-hp-rel 1) (fn-hp-rel 2) (fn-hp-rel 3)))))
                (equal (len (fn-hp-rel 1)) 5)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-grow-shape)
                 (:instance fn-hp-x-append-grow-shape (starts (fn-hp-rel 1)) (np (fn-hp-rel 2)) (pgs-mem (fn-hp-rel 3)))
                 (:instance fn-hp-x-relocate-ok-unfolds (r (cadr (fn-hp-av))) (c (caddr (fn-hp-av))))
                 (:instance fn-hp-grow-then-append (r (cadr (fn-hp-av))) (c (caddr (fn-hp-av)))
                            (r2 (cadr (mv-nth 0 (fn-hp-x-append ev salt n lens (fn-hp-rel 1) (fn-hp-rel 2) (fn-hp-rel 3)))))
                            (c2 (caddr (mv-nth 0 (fn-hp-x-append ev salt n lens (fn-hp-rel 1) (fn-hp-rel 2) (fn-hp-rel 3)))))))
           :in-theory (union-theories '(len-update-nth car-cons cdr-cons natp max (:e max) nfix)
                                      (theory 'minimal-theory)))))

(local
 (defthm fn-hp-loop-relocated-len
   (implies (and (equal (len starts) 5) (natp (cadr (fn-hp-av))) (< (cadr (fn-hp-av)) 5) (equal (fn-hp-rel 0) :ok))
            (equal (len (fn-hp-rel 1)) 5))
   :hints (("Goal" :use ((:instance fn-hp-x-relocate-ok-unfolds (r (cadr (fn-hp-av))) (c (caddr (fn-hp-av)))))
            :in-theory (disable fn-hp-x-append fn-hp-x-relocate fn-hp-x-relocate-ok-unfolds)))))

(defthm fn-hp-x-append-loop-not-grow
  (implies (and (nat-listp lens) (equal (len lens) 5) (equal (len starts) 5) (natp k)
                (implies (equal (car (fn-hp-av)) :grow) (<= (- 5 k) (cadr (fn-hp-av)))))
           (not (equal (car (mv-nth 0 (fn-hp-x-append-loop k ev salt n lens starts np pgs-mem))) :grow)))
  :hints (("Goal" :induct (fn-hp-x-append-loop k ev salt n lens starts np pgs-mem)
           :in-theory (disable fn-hp-x-append fn-hp-x-relocate adt-cap mv-nth fn-hp-x-relocate-ok-unfolds))
          (and stable-under-simplificationp
               '(:use ((:instance fn-hp-x-append-grow-shape) (:instance fn-hp-loop-progress)
                       (:instance fn-hp-x-append-grow-shape (starts (fn-hp-rel 1)) (np (fn-hp-rel 2)) (pgs-mem (fn-hp-rel 3))))
                 :in-theory (disable fn-hp-x-append fn-hp-x-relocate adt-cap mv-nth fn-hp-x-relocate-ok-unfolds
                                     fn-hp-loop-progress)))))

(defmacro fn-hp-held (h starts np mem)
  ; the invariant the host carries: the store's verified pages hold H's
  ; image placed at STARTS in NP pages
  `(and (fn-hp-okp ,h salt) (fn-hp-starts-okp ,starts)
        (fn-hp-vhold 0 (pgs-v-length ,mem) ,mem (fn-hp-piw ,h salt ,starts ,np))))

(defun-nx fn-hp-step-post (h ev salt n lens res)
  ; what a step's answer RES = (VERDICT N2 LENS2 STARTS2 NP2 MEM2) means
  ; over the history H (N, LENS: H's header answer)
  (let ((v (mv-nth 0 res)) (n2 (mv-nth 1 res)) (lens2 (mv-nth 2 res))
        (starts2 (mv-nth 3 res)) (np2 (mv-nth 4 res)) (mem2 (mv-nth 5 res)))
    (and (fn-hp-starts-okp starts2)
         (if (equal v :ok)
             (and (fn-hp-okp (append h (list ev)) salt)
                  (equal n2 (len (append h (list ev))))
                  (equal lens2 (fn-hp-lens (append h (list ev)) salt))
                  (adt-placement-ok starts2 (fn-hp-lens (append h (list ev)) salt) np2)
                  (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw (append h (list ev)) salt starts2 np2)))
           (and (equal n2 n) (equal lens2 lens)
                (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h salt starts2 np2)))))))

(defthm fn-hp-step-post-not-ok
  (implies (and (fn-hp-held h starts np mem) (not (equal v :ok)))
           (fn-hp-step-post h ev salt n lens (list v n lens starts np mem))))

(defthm fn-hp-step-post-append
  (implies (and (fn-hp-held h starts np pgs-mem) (equal n (len h)) (equal lens (fn-hp-lens h salt)))
           (fn-hp-step-post h ev salt n lens
                            (list (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem))
                                  (mv-nth 1 (fn-hp-x-append ev salt n lens starts np pgs-mem))
                                  (mv-nth 2 (fn-hp-x-append ev salt n lens starts np pgs-mem))
                                  starts np
                                  (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem)))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))
           :use ((:instance fn-hp-x-append-refines-placed) (:instance fn-hp-x-append-not-ok-unchanged))
           :in-theory (union-theories '(fn-hp-step-post mv-nth car-cons cdr-cons (:e zp) zp)
                                      (theory 'minimal-theory)))))

(defthm fn-hp-held-relocated
  (implies (and (fn-hp-held h starts np pgs-mem) (equal n (len h)) (equal lens (fn-hp-lens h salt))
                (natp r) (< r 5) (natp c)
                (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))
           (fn-hp-held h (mv-nth 1 (fn-hp-x-relocate r c n lens starts np pgs-mem))
                       (mv-nth 2 (fn-hp-x-relocate r c n lens starts np pgs-mem))
                       (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-relocate-refines))
           :in-theory (disable fn-hp-x-relocate-refines fn-hp-x-relocate fn-hp-x-relocate-ok-unfolds
                               adt-cap fn-hp-okp fn-hp-vhold fn-hp-piw fn-hp-lens adt-placement-ok))))

(in-theory (disable fn-hp-step-post))

(defthm fn-hp-mv-nth-cons
  (implies (natp i) (equal (mv-nth i (cons a b)) (if (zp i) a (mv-nth (1- i) b)))))

(defthm fn-hp-x-append-loop-post-h
  (implies (fn-hp-held h starts np pgs-mem)
           (fn-hp-step-post h ev salt (len h) (fn-hp-lens h salt)
                            (fn-hp-x-append-loop k ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))
  :hints (("Goal" :induct (fn-hp-x-append-loop k ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)
           :in-theory (set-difference-theories
                       (union-theories '(fn-hp-x-append-loop zp (:e zp) eq not fn-hp-mv-nth-cons natp (:e natp))
                                       (theory 'minimal-theory))
                       '(mv-nth)))
          (and stable-under-simplificationp
               '(:use ((:instance fn-hp-x-append-grow-shape (lens (fn-hp-lens h salt)) (n (len h)))
                       (:instance fn-hp-x-append-grow-mem (lens (fn-hp-lens h salt)) (n (len h)))
                       (:instance fn-hp-step-post-append (lens (fn-hp-lens h salt)) (n (len h)))
                       (:instance fn-hp-step-post-not-ok (lens (fn-hp-lens h salt)) (n (len h))
                                  (v (mv-nth 0 (fn-hp-x-relocate (cadr (mv-nth 0 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))
                                                                 (caddr (mv-nth 0 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))
                                                                 (len h) (fn-hp-lens h salt) starts np pgs-mem)))
                                  (mem pgs-mem))
                       (:instance fn-hp-x-relocate-not-ok-unchanged (lens (fn-hp-lens h salt)) (n (len h))
                                  (r (cadr (mv-nth 0 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem))))
                                  (c (caddr (mv-nth 0 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))))
                       (:instance fn-hp-held-relocated (lens (fn-hp-lens h salt)) (n (len h))
                                  (r (cadr (mv-nth 0 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem))))
                                  (c (caddr (mv-nth 0 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem))))))
                 :in-theory (set-difference-theories
                             (union-theories '(fn-hp-nat-listp-lens fn-hp-len-lens fn-hp-mv-nth-cons natp (:e natp) zp (:e zp))
                                             (theory 'minimal-theory))
                             '(mv-nth))))))

(defmacro fn-hp-newly-dirty (p mem2 mem)
  `(and (natp ,p) (equal (nth ,p (nth *pgs-di* ,mem2)) 1) (not (equal (nth ,p (nth *pgs-di* ,mem)) 1))))

(defthm fn-hp-x-append-dirty-verified
  (implies (and (fn-hp-held h starts np pgs-mem)
                (fn-hp-newly-dirty p (mv-nth 3 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)) pgs-mem))
           (equal (pgs-vi p (mv-nth 3 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem))) 2))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (mv-nth 0 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)) :ok))
           :use ((:instance fn-hp-x-append-refines-placed (n (len h)) (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-x-append-not-ok-unchanged (n (len h)) (lens (fn-hp-lens h salt))))
           :in-theory (union-theories '(natp) (theory 'minimal-theory)))))

(defthm fn-hp-x-relocate-dirty-verified-h
  (implies (and (fn-hp-held h starts np pgs-mem) (natp r) (< r 5) (natp c)
                (fn-hp-newly-dirty p (mv-nth 3 (fn-hp-x-relocate r c (len h) (fn-hp-lens h salt) starts np pgs-mem)) pgs-mem))
           (equal (pgs-vi p (mv-nth 3 (fn-hp-x-relocate r c (len h) (fn-hp-lens h salt) starts np pgs-mem))) 2))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (mv-nth 0 (fn-hp-x-relocate r c (len h) (fn-hp-lens h salt) starts np pgs-mem)) :ok))
           :use ((:instance fn-hp-x-relocate-refines (n (len h)) (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-x-relocate-not-ok-unchanged (n (len h)) (lens (fn-hp-lens h salt))))
           :in-theory (union-theories '(natp) (theory 'minimal-theory)))))

(defmacro fn-hp-loop-theory (&rest names)
  `(set-difference-theories
    (union-theories '(zp (:e zp) eq not fn-hp-mv-nth-cons natp (:e natp) fn-hp-nat-listp-lens fn-hp-len-lens ,@names)
                    (theory 'minimal-theory))
    '(mv-nth)))

(defmacro fn-hp-av-h ()
  '(mv-nth 0 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))

(defthm fn-hp-x-append-loop-keeps-verified
  (implies (and (fn-hp-held h starts np pgs-mem) (natp p) (equal (pgs-vi p pgs-mem) 2))
           (equal (pgs-vi p (mv-nth 5 (fn-hp-x-append-loop k ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem))) 2))
  :hints (("Goal" :induct (fn-hp-x-append-loop k ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)
           :in-theory (fn-hp-loop-theory fn-hp-x-append-loop))
          (and stable-under-simplificationp
               '(:use ((:instance fn-hp-x-append-grow-shape (lens (fn-hp-lens h salt)) (n (len h)))
                       (:instance fn-hp-x-append-grow-mem (lens (fn-hp-lens h salt)) (n (len h)))
                       (:instance fn-hp-x-append-keeps-verified (lens (fn-hp-lens h salt)) (n (len h)))
                       (:instance fn-hp-x-relocate-keeps-verified (lens (fn-hp-lens h salt)) (n (len h))
                                  (r (cadr (fn-hp-av-h))) (c (caddr (fn-hp-av-h))))
                       (:instance fn-hp-x-relocate-not-ok-unchanged (lens (fn-hp-lens h salt)) (n (len h))
                                  (r (cadr (fn-hp-av-h))) (c (caddr (fn-hp-av-h))))
                       (:instance fn-hp-held-relocated (lens (fn-hp-lens h salt)) (n (len h))
                                  (r (cadr (fn-hp-av-h))) (c (caddr (fn-hp-av-h)))))
                 :in-theory (fn-hp-loop-theory fn-hp-starts-okp)))))

(defthm fn-hp-x-append-loop-dirty-verified
  (implies (and (fn-hp-held h starts np pgs-mem)
                (fn-hp-newly-dirty p (mv-nth 5 (fn-hp-x-append-loop k ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem))
                                   pgs-mem))
           (equal (pgs-vi p (mv-nth 5 (fn-hp-x-append-loop k ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem))) 2))
  :hints (("Goal" :induct (fn-hp-x-append-loop k ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)
           :in-theory (fn-hp-loop-theory fn-hp-x-append-loop))
          (and stable-under-simplificationp
               '(:use ((:instance fn-hp-x-append-grow-shape (lens (fn-hp-lens h salt)) (n (len h)))
                       (:instance fn-hp-x-append-grow-mem (lens (fn-hp-lens h salt)) (n (len h)))
                       (:instance fn-hp-x-append-dirty-verified)
                       (:instance fn-hp-x-relocate-dirty-verified-h (r (cadr (fn-hp-av-h))) (c (caddr (fn-hp-av-h))))
                       (:instance fn-hp-x-append-loop-keeps-verified (k (+ -1 k))
                                  (starts (mv-nth 1 (fn-hp-x-relocate (cadr (fn-hp-av-h)) (caddr (fn-hp-av-h)) (len h) (fn-hp-lens h salt) starts np pgs-mem)))
                                  (np (mv-nth 2 (fn-hp-x-relocate (cadr (fn-hp-av-h)) (caddr (fn-hp-av-h)) (len h) (fn-hp-lens h salt) starts np pgs-mem)))
                                  (pgs-mem (mv-nth 3 (fn-hp-x-relocate (cadr (fn-hp-av-h)) (caddr (fn-hp-av-h)) (len h) (fn-hp-lens h salt) starts np pgs-mem))))
                       (:instance fn-hp-x-relocate-not-ok-unchanged (lens (fn-hp-lens h salt)) (n (len h))
                                  (r (cadr (fn-hp-av-h))) (c (caddr (fn-hp-av-h))))
                       (:instance fn-hp-held-relocated (lens (fn-hp-lens h salt)) (n (len h))
                                  (r (cadr (fn-hp-av-h))) (c (caddr (fn-hp-av-h)))))
                 :in-theory (fn-hp-loop-theory fn-hp-starts-okp)))))

; KEYSTONE (the step the host calls per event).  See the head of the book.
(defthm fn-hp-x-append-step-refines
  (implies (and (fn-hp-okp h salt)
                (equal n (len h)) (equal lens (fn-hp-lens h salt))
                (fn-hp-starts-okp starts)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)))
           (let* ((res (fn-hp-x-append-step ev salt n lens starts np pgs-mem))
                  (v (mv-nth 0 res)) (n2 (mv-nth 1 res)) (lens2 (mv-nth 2 res))
                  (starts2 (mv-nth 3 res)) (np2 (mv-nth 4 res)) (mem2 (mv-nth 5 res)))
             (and (fn-hp-starts-okp starts2)
                  (not (equal (car v) :grow))
                  (implies (equal v :ok)
                           (and (fn-hp-okp (append h (list ev)) salt)
                                (equal n2 (len (append h (list ev))))
                                (equal lens2 (fn-hp-lens (append h (list ev)) salt))
                                (adt-placement-ok starts2 lens2 np2)
                                (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw (append h (list ev)) salt starts2 np2))))
                  (implies (not (equal v :ok))
                           (and (equal n2 n) (equal lens2 lens)
                                (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h salt starts2 np2))))
                  (implies (and (natp p) (equal (nth p (nth *pgs-di* mem2)) 1)
                                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
                           (equal (pgs-vi p mem2) 2)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-loop-post-h (k 5))
                 (:instance fn-hp-x-append-loop-dirty-verified (k 5))
                 (:instance fn-hp-x-append-loop-not-grow (k 5) (n (len h)) (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-x-append-grow-shape (n (len h)) (lens (fn-hp-lens h salt))))
           :in-theory (union-theories '(fn-hp-x-append-step fn-hp-step-post fn-hp-nat-listp-lens fn-hp-len-lens
                                        fn-hp-starts-okp natp)
                                      (theory 'minimal-theory)))))
