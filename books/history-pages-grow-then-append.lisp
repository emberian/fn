; fn: the append's growth answer and the relocation make progress (lane
; arena-store-4, 2026-09-28).  Prefix fn-hp-.
;
; PROGRESS fn-hp-grow-then-append: when the writer the host calls
; (`fn-hp-x-append') answers (:grow R C), R is a region below 5 whose cap
; grows (C, its new cap, above its old one); the relocation the host calls
; next (`fn-hp-x-relocate' R C) never refuses :capacity or :placement; and
; after it answers :ok, the append over the new placement answers (:grow R2
; C2) only for a later region R2 > R.  So the host's loop (append, on
; (:grow R C) relocate R C, append again) relocates each outgrown region at
; most once per event, at most five times.  fn-hp-grow-then-append-only-r:
; when no region after R changes its cap, the append after the relocation
; answers no :grow at all.
(in-package "ACL2")
(include-book "history-pages-relocate")
(include-book "history-pages-append-grown")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable floor mod pgs-true-list-fix-when-true-listp pgs-ptab-p-true-listp fn-cp-id-length-bound
                           fn-scc-encode-is-program)))

(defun fn-hp-x-lens-after (ev lens)
  ; the region lengths after appending EV, as `fn-hp-x-append-plan' computes them
  (declare (xargs :verify-guards nil))
  (fn-hp-x-add lens (list 8 8 8 8 (len (fn-hp-pad8 (fn-scc-encode ev))))))

; -----------------------------------------------------------------------------
; A. The mixed lengths.

(defthm fn-hp-x-mix-0 (equal (fn-hp-x-mix 0 lens lens2) lens))

(defthm fn-hp-len-x-mix (equal (len (fn-hp-x-mix k lens lens2)) (len lens)))

(defthm fn-hp-nth-x-mix-below
  (implies (and (natp r) (natp k) (<= k r)) (equal (nth r (fn-hp-x-mix k lens lens2)) (nth r lens)))
  :hints (("Goal" :induct (list (fn-hp-x-mix k lens lens2) (nth r lens)) :in-theory (enable nth))))

(defthm fn-hp-x-mix-step
  (implies (and (natp k) (< k (len lens)) (< k (len lens2)))
           (equal (fn-hp-x-mix (+ 1 k) lens lens2) (update-nth k (nth k lens2) (fn-hp-x-mix k lens lens2))))
  :hints (("Goal" :induct (fn-hp-x-mix k lens lens2) :in-theory (enable update-nth nth))))

(in-theory (disable fn-hp-x-mix-step))

(local (defun fn-hp-cdr2-ind (a b) (if (or (atom a) (atom b)) (list a b) (fn-hp-cdr2-ind (cdr a) (cdr b)))))

(defthm fn-hp-x-mix-full
  (implies (and (true-listp lens) (true-listp lens2) (equal (len lens2) (len lens)))
           (equal (fn-hp-x-mix (len lens) lens lens2) lens2))
  :hints (("Goal" :induct (fn-hp-cdr2-ind lens lens2) :expand ((fn-hp-x-mix (len lens) lens lens2)))))

(defthm fn-hp-caps-le-x-mix-0
  (implies (fn-hp-caps-le lens lens2) (fn-hp-caps-le lens (fn-hp-x-mix m lens lens2)))
  :hints (("Goal" :induct (fn-hp-x-mix m lens lens2) :in-theory (disable adt-cap))))

(local
 (defun fn-hp-mix2-ind (j m lens lens2)
   (if (or (zp j) (atom lens) (atom lens2)) (list m lens lens2)
     (fn-hp-mix2-ind (1- j) (1- m) (cdr lens) (cdr lens2)))))

(defthm fn-hp-caps-le-x-mix
  (implies (and (fn-hp-caps-le lens lens2) (natp j) (natp m) (<= j m))
           (fn-hp-caps-le (fn-hp-x-mix j lens lens2) (fn-hp-x-mix m lens lens2)))
  :hints (("Goal" :induct (fn-hp-mix2-ind j m lens lens2) :in-theory (disable adt-cap))))

(defthm fn-hp-caps-le-refl (fn-hp-caps-le l l) :hints (("Goal" :in-theory (disable adt-cap))))

(defthm fn-hp-caps-le-x-add
  (implies (and (nat-listp lens) (nat-listp d)) (fn-hp-caps-le lens (fn-hp-x-add lens d)))
  :hints (("Goal" :induct (fn-hp-x-add lens d) :in-theory (disable adt-cap))
          ("Subgoal *1/2" :use ((:instance fn-hp-cap-mono-k (u (car lens)) (v (+ (car lens) (car d))))))))

(defthm fn-hp-same-caps-update
  (implies (and (natp r) (< r (len l)) (equal (adt-cap (nfix x)) (adt-cap (nfix (nth r l)))))
           (fn-hp-same-caps l (update-nth r x l)))
  :hints (("Goal" :induct (update-nth r x l) :in-theory (e/d (update-nth nth) (adt-cap)))))

(defthm fn-hp-same-caps-refl (fn-hp-same-caps l l) :hints (("Goal" :in-theory (disable adt-cap))))

(defthm fn-hp-same-caps-x-mix-tail
  (implies (and (natp k) (fn-hp-same-caps (nthcdr k lens) (nthcdr k lens2)) (<= k (len lens)) (equal (len lens2) (len lens)))
           (fn-hp-same-caps (fn-hp-x-mix k lens lens2) lens2))
  :hints (("Goal" :induct (fn-hp-x-mix k lens lens2) :in-theory (disable adt-cap))))

; -----------------------------------------------------------------------------
; B. The chooser `fn-hp-x-unfit'.

(defthm fn-hp-x-unfit-at-least
  (implies (natp k) (<= k (fn-hp-x-unfit k starts lens lens2 np)))
  :rule-classes :linear)

(defthm fn-hp-x-unfit-below
  (implies (and (natp k) (< k (len lens))
                (not (adt-placement-ok starts (fn-hp-x-mix (len lens) lens lens2) np)))
           (< (fn-hp-x-unfit k starts lens lens2 np) (len lens)))
  :hints (("Goal" :induct (fn-hp-x-unfit k starts lens lens2 np) :in-theory (disable adt-placement-ok fn-hp-x-mix))))

(defthm fn-hp-x-unfit-fails
  (implies (and (natp k) (< (fn-hp-x-unfit k starts lens lens2 np) (len lens)))
           (not (adt-placement-ok starts (fn-hp-x-mix (+ 1 (fn-hp-x-unfit k starts lens lens2 np)) lens lens2) np)))
  :hints (("Goal" :induct (fn-hp-x-unfit k starts lens lens2 np) :in-theory (disable adt-placement-ok fn-hp-x-mix))))

(defthm fn-hp-x-unfit-passes
  (implies (and (natp k) (natp j) (<= k j) (< j (fn-hp-x-unfit k starts lens lens2 np)))
           (adt-placement-ok starts (fn-hp-x-mix (+ 1 j) lens lens2) np))
  :hints (("Goal" :induct (fn-hp-x-unfit k starts lens lens2 np) :in-theory (disable adt-placement-ok fn-hp-x-mix))))

(defthm fn-hp-x-unfit-lower
  (implies (and (natp k) (natp m) (<= m (len lens)) (equal (len lens2) (len lens)) (fn-hp-caps-le lens lens2)
                (adt-placement-ok starts (fn-hp-x-mix m lens lens2) np))
           (<= m (fn-hp-x-unfit k starts lens lens2 np)))
  :hints (("Goal" :induct (fn-hp-x-unfit k starts lens lens2 np) :in-theory (disable adt-placement-ok fn-hp-x-mix))
          ("Subgoal *1/2" :use ((:instance fn-hp-placement-mono (lens (fn-hp-x-mix (+ 1 k) lens lens2))
                                           (lens2 (fn-hp-x-mix m lens lens2)))
                                (:instance fn-hp-caps-le-x-mix (j (+ 1 k)))))))

; -----------------------------------------------------------------------------
; C. A region moved to the image's end with any length whose cap fits the
;    pages added.

(local
 (defthm fn-hp-apart-at-end-g
   (implies (and (adt-placement-ok starts lens np) (natp np))
            (adt-apart np c starts lens))
   :hints (("Goal" :in-theory (disable adt-cap)))))

(local
 (defthm fn-hp-apart-update-end-g
   (implies (and (adt-apart s c starts lens) (natp s) (natp c) (<= (+ s c) np) (natp np) (natp j)
                 (< j (len starts)))
            (adt-apart s c (update-nth j np starts) (update-nth j x lens)))
   :hints (("Goal" :induct (list (update-nth j np starts) (update-nth j x lens))
            :in-theory (e/d (update-nth) (adt-cap))))))

(local
 (defthm fn-hp-placement-np-mono-g
   (implies (and (adt-placement-ok starts lens np) (natp np) (natp np2) (<= np np2))
            (adt-placement-ok starts lens np2))
   :hints (("Goal" :induct (adt-placement-ok starts lens np) :in-theory (disable adt-cap adt-apart)))))

(local
 (defun fn-hp-pr-ind-g (r starts lens)
   (if (or (atom starts) (atom lens)) (list r starts lens)
     (fn-hp-pr-ind-g (1- r) (cdr starts) (cdr lens)))))

(defthm fn-hp-placement-relocated-grown
  (implies (and (adt-placement-ok starts lens np) (natp np) (<= 1 np) (natp r) (< r (len starts)) (< r (len lens))
                (natp c) (<= (adt-cap (nfix x)) c))
           (adt-placement-ok (update-nth r np starts) (update-nth r x lens) (+ np c)))
  :hints (("Goal" :induct (fn-hp-pr-ind-g r starts lens) :in-theory (e/d (update-nth) (adt-cap)))))

; -----------------------------------------------------------------------------
; D. The writer's growth answer.

(defthm fn-hp-x-ready-not-grow
  (and (not (equal (car (fn-hp-x-ready p pgs-mem)) :grow))
       (not (equal (car (fn-hp-x-ready p pgs-mem)) :refused))))

(defthm fn-hp-x-ready-range-not-grow
  (and (not (equal (car (fn-hp-x-ready-range p hi pgs-mem)) :grow))
       (not (equal (car (fn-hp-x-ready-range p hi pgs-mem)) :refused)))
  :hints (("Goal" :in-theory (disable fn-hp-x-ready))))

(defthm fn-hp-x-blocks-ready-not-grow
  (not (equal (car (fn-hp-x-blocks-ready blocks pgs-mem)) :grow))
  :hints (("Goal" :in-theory (disable fn-hp-x-ready-range floor))))

(defthm fn-hp-x-append-grow-is-plan
  (implies (equal (car (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem))) :grow)
           (and (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem))
                       (mv-nth 0 (fn-hp-x-append-plan ev salt n lens starts np)))
                (equal (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem)) pgs-mem)))
  :hints (("Goal" :in-theory (disable fn-hp-x-append-plan fn-hp-x-blocks-ready fn-hp-x-put-blocks))))

(defthm fn-hp-x-append-plan-grow
  (implies (equal (car (mv-nth 0 (fn-hp-x-append-plan ev salt n lens starts np))) :grow)
           (let ((lens2 (fn-hp-x-lens-after ev lens)))
             (and (equal (mv-nth 0 (fn-hp-x-append-plan ev salt n lens starts np))
                         (list :grow (fn-hp-x-unfit 0 starts lens lens2 np)
                               (adt-cap (nfix (nth (fn-hp-x-unfit 0 starts lens lens2 np) lens2)))))
                  (adt-placement-ok starts lens np)
                  (not (adt-placement-ok starts lens2 np)))))
  :hints (("Goal" :in-theory (disable fn-scc-encode fn-hp-pad8 adt-placement-ok fn-hp-x-unfit fn-hp-x-aligned fn-hp-x-blocks
                                      fn-hp-x-add fn-sccb-treep fn-hp-pack8 adt-cap fn-hp-mkey fn-hp-u64-listp adt-end-l))))

(local
 (defun fn-hp-nth2-ind (r a b)
   (if (or (zp r) (atom a) (atom b)) (list a b) (fn-hp-nth2-ind (1- r) (cdr a) (cdr b)))))

(defthm fn-hp-cap-nth-caps-le
  (implies (and (fn-hp-caps-le a b) (natp r) (< r (len a)) (< r (len b)))
           (<= (adt-cap (nfix (nth r a))) (adt-cap (nfix (nth r b)))))
  :hints (("Goal" :induct (fn-hp-nth2-ind r a b)
           :in-theory (union-theories '(fn-hp-caps-le nth len natp zp nfix (:induction fn-hp-nth2-ind) car-cons cdr-cons)
                                      (theory 'minimal-theory))))
  :rule-classes nil)

(defthm fn-hp-len-lens-after
  (implies (equal (len lens) 5) (equal (len (fn-hp-x-lens-after ev lens)) 5))
  :hints (("Goal" :in-theory (disable fn-scc-encode fn-hp-pad8))))

(defthm fn-hp-nat-listp-lens-after
  (implies (nat-listp lens) (nat-listp (fn-hp-x-lens-after ev lens)))
  :hints (("Goal" :in-theory (disable fn-scc-encode fn-hp-pad8))))

(defthm fn-hp-caps-le-lens-after
  (implies (nat-listp lens) (fn-hp-caps-le lens (fn-hp-x-lens-after ev lens)))
  :hints (("Goal" :in-theory (disable fn-scc-encode fn-hp-pad8 fn-hp-x-add fn-hp-caps-le))))

(in-theory (disable fn-hp-x-lens-after))

(defthm fn-hp-x-unfit-prefix-placed
  (implies (adt-placement-ok starts lens np)
           (adt-placement-ok starts (fn-hp-x-mix (fn-hp-x-unfit 0 starts lens lens2 np) lens lens2) np))
  :hints (("Goal" :cases ((zp (fn-hp-x-unfit 0 starts lens lens2 np)))
           :use ((:instance fn-hp-x-unfit-passes (k 0) (j (+ -1 (fn-hp-x-unfit 0 starts lens lens2 np)))))
           :in-theory (disable fn-hp-x-unfit-passes adt-placement-ok fn-hp-x-mix fn-hp-x-unfit))))

(defthm fn-hp-placement-update-same-cap
  (implies (and (natp r) (< r (len l)) (adt-placement-ok starts l np)
                (equal (adt-cap (nfix x)) (adt-cap (nfix (nth r l)))))
           (adt-placement-ok starts (update-nth r x l) np))
  :hints (("Goal" :use ((:instance fn-hp-same-caps-update) (:instance fn-hp-placement-same-caps (lens l) (lens2 (update-nth r x l))))
           :in-theory (disable fn-hp-same-caps-update fn-hp-placement-same-caps adt-placement-ok adt-cap))))

; The chooser names a region whose cap grows.
(defthm fn-hp-x-unfit-grows
  (implies (and (nat-listp lens) (nat-listp lens2) (equal (len lens) 5) (equal (len lens2) 5) (fn-hp-caps-le lens lens2)
                (adt-placement-ok starts lens np) (not (adt-placement-ok starts lens2 np)))
           (and (< (fn-hp-x-unfit 0 starts lens lens2 np) 5)
                (< (adt-cap (nth (fn-hp-x-unfit 0 starts lens lens2 np) lens))
                   (adt-cap (nth (fn-hp-x-unfit 0 starts lens lens2 np) lens2)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-unfit-below (k 0))
                 (:instance fn-hp-x-mix-full)
                 (:instance fn-hp-x-unfit-fails (k 0))
                 (:instance fn-hp-x-unfit-prefix-placed)
                 (:instance fn-hp-x-mix-step (k (fn-hp-x-unfit 0 starts lens lens2 np)))
                 (:instance fn-hp-nth-x-mix-below (k (fn-hp-x-unfit 0 starts lens lens2 np))
                            (r (fn-hp-x-unfit 0 starts lens lens2 np)))
                 (:instance fn-hp-placement-update-same-cap
                            (l (fn-hp-x-mix (fn-hp-x-unfit 0 starts lens lens2 np) lens lens2))
                            (r (fn-hp-x-unfit 0 starts lens lens2 np))
                            (x (nth (fn-hp-x-unfit 0 starts lens lens2 np) lens2)))
                 (:instance fn-hp-cap-nth-caps-le (a lens) (b lens2) (r (fn-hp-x-unfit 0 starts lens lens2 np))))
           :in-theory (disable fn-hp-x-unfit-below fn-hp-x-mix-full fn-hp-x-unfit-fails fn-hp-x-unfit-prefix-placed
                               fn-hp-nth-x-mix-below fn-hp-placement-update-same-cap
                               adt-placement-ok fn-hp-x-unfit fn-hp-x-mix adt-cap fn-hp-caps-le))))

(local
 (defthm fn-hp-natp-nth-nat-listp-g
   (implies (and (nat-listp l) (natp r) (< r (len l))) (natp (nth r l)))
   :hints (("Goal" :in-theory (enable nth)))))

; The region the writer names grows: R below 5, C its new cap, above its
; old one; nothing written.
(defthm fn-hp-x-append-grow-region
  (implies (and (nat-listp lens) (equal (len lens) 5)
                (equal (car (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem))) :grow))
           (let* ((v (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem))) (r (cadr v)) (c (caddr v)))
             (and (natp r) (< r 5)
                  (equal r (fn-hp-x-unfit 0 starts lens (fn-hp-x-lens-after ev lens) np))
                  (equal c (adt-cap (nth r (fn-hp-x-lens-after ev lens))))
                  (< (adt-cap (nth r lens)) c)
                  (adt-placement-ok starts lens np)
                  (equal (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem)) pgs-mem))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-grow-is-plan)
                 (:instance fn-hp-x-append-plan-grow)
                 (:instance fn-hp-x-unfit-grows (lens2 (fn-hp-x-lens-after ev lens)))
                 (:instance fn-hp-natp-nth-nat-listp-g (l (fn-hp-x-lens-after ev lens))
                            (r (fn-hp-x-unfit 0 starts lens (fn-hp-x-lens-after ev lens) np))))
           :in-theory (disable fn-hp-x-append-grow-is-plan fn-hp-x-append-plan-grow fn-hp-x-unfit-grows
                               fn-hp-x-append fn-hp-x-append-plan adt-placement-ok fn-hp-x-unfit
                               fn-hp-x-mix adt-cap))))

; -----------------------------------------------------------------------------
; E. The relocation the host calls next, and the append after it.

(defthm fn-hp-x-relocate-not-capacity-placement
  (implies (and (< 0 c) (<= (adt-cap (nth r lens)) c) (adt-placement-ok starts lens np))
           (and (not (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) '(:refused :capacity)))
                (not (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) '(:refused :placement)))))
  :hints (("Goal" :use ((:instance fn-hp-x-ready-not-grow (p 0))
                        (:instance fn-hp-x-ready-range-not-grow (p (nth r starts)) (hi (+ (nth r starts) (adt-cap (nth r lens))))))
           :in-theory (disable fn-hp-x-ready-not-grow fn-hp-x-ready-range-not-grow
                               fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark fn-hp-x-ready fn-hp-x-ready-range
                               fn-hp-hdr-m adt-cap adt-placement-ok fn-hp-u64-listp pgs-x-grow-image))))

(defthm fn-hp-relocated-mix-placed
  (implies (and (nat-listp lens) (equal (len lens) 5) (equal (len starts) 5)
                (nat-listp lens2) (equal (len lens2) 5)
                (adt-placement-ok starts lens np)
                (equal r (fn-hp-x-unfit 0 starts lens lens2 np)) (< r 5)
                (equal c (adt-cap (nth r lens2)))
                (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))
           (adt-placement-ok (update-nth r np starts) (fn-hp-x-mix (+ 1 r) lens lens2) (+ np c)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-relocate-ok-checks)
                 (:instance fn-hp-x-unfit-prefix-placed)
                 (:instance fn-hp-placement-np-pos)
                 (:instance fn-hp-x-mix-step (k r))
                 (:instance fn-hp-natp-nth-nat-listp-g (l lens2))
                 (:instance fn-hp-placement-relocated-grown (lens (fn-hp-x-mix r lens lens2)) (x (nth r lens2))))
           :in-theory (disable fn-hp-x-unfit-prefix-placed fn-hp-x-mix-step fn-hp-natp-nth-nat-listp-g
                               fn-hp-placement-relocated-grown fn-hp-x-relocate adt-placement-ok fn-hp-x-unfit fn-hp-x-mix
                               adt-cap fn-hp-x-ready fn-hp-x-ready-range fn-hp-hdr-m fn-hp-u64-listp))))

;; PROGRESS.  When the writer answers (:grow R C): R is a region below 5
;; whose cap grows to C and nothing was written; the relocation of R to C
;; fresh pages never refuses :capacity or :placement; and after it answers
;; :ok, the append over the new placement (STARTS with R at NP, NP+C pages)
;; answers (:grow R2 C2) only for a later region R2 > R -- whose cap grows
;; too (`fn-hp-x-append-grow-region').  So an event relocates each outgrown
;; region at most once, in increasing order, at most five times.
(defthm fn-hp-grow-then-append
  (implies (and (nat-listp lens) (equal (len lens) 5) (equal (len starts) 5)
                (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) (list :grow r c)))
           (and (natp r) (< r 5)
                (equal c (adt-cap (nth r (fn-hp-x-lens-after ev lens))))
                (< (adt-cap (nth r lens)) c)
                (equal (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem)) pgs-mem)
                (not (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) '(:refused :capacity)))
                (not (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) '(:refused :placement)))
                (implies (and (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok)
                              (equal (mv-nth 0 (fn-hp-x-append ev salt n lens
                                                               (mv-nth 1 (fn-hp-x-relocate r c n lens starts np pgs-mem))
                                                               (mv-nth 2 (fn-hp-x-relocate r c n lens starts np pgs-mem))
                                                               (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem))))
                                     (list :grow r2 c2)))
                         (< r r2))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-grow-region)
                 (:instance fn-hp-x-relocate-not-capacity-placement)
                 (:instance fn-hp-x-relocate-ok-unfolds)
                 (:instance fn-hp-relocated-mix-placed (lens2 (fn-hp-x-lens-after ev lens)))
                 (:instance fn-hp-x-append-grow-region (starts (update-nth r np starts)) (np (+ np c))
                            (pgs-mem (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem))))
                 (:instance fn-hp-x-unfit-lower (k 0) (lens2 (fn-hp-x-lens-after ev lens)) (m (+ 1 r))
                            (starts (update-nth r np starts)) (np (+ np c))))
           :in-theory (union-theories '(fn-hp-len-lens-after fn-hp-nat-listp-lens-after fn-hp-caps-le-lens-after natp car-cons cdr-cons (:type-prescription adt-cap) (:type-prescription fn-hp-x-unfit))
                                      (theory 'minimal-theory))))
  :rule-classes nil)

;; When no region after R changes its cap, the append after the relocation
;; answers no :grow at all.
(defthm fn-hp-grow-then-append-only-r
  (implies (and (nat-listp lens) (equal (len lens) 5) (equal (len starts) 5)
                (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) (list :grow r c))
                (fn-hp-same-caps (nthcdr (+ 1 r) lens) (nthcdr (+ 1 r) (fn-hp-x-lens-after ev lens)))
                (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))
           (not (equal (car (mv-nth 0 (fn-hp-x-append ev salt n lens
                                                      (mv-nth 1 (fn-hp-x-relocate r c n lens starts np pgs-mem))
                                                      (mv-nth 2 (fn-hp-x-relocate r c n lens starts np pgs-mem))
                                                      (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem)))))
                       :grow)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-grow-region)
                 (:instance fn-hp-x-relocate-ok-unfolds)
                 (:instance fn-hp-relocated-mix-placed (lens2 (fn-hp-x-lens-after ev lens)))
                 (:instance fn-hp-same-caps-x-mix-tail (k (+ 1 r)) (lens2 (fn-hp-x-lens-after ev lens)))
                 (:instance fn-hp-placement-same-caps (starts (update-nth r np starts)) (np (+ np c))
                            (lens (fn-hp-x-mix (+ 1 r) lens (fn-hp-x-lens-after ev lens)))
                            (lens2 (fn-hp-x-lens-after ev lens)))
                 (:instance fn-hp-x-append-grow-is-plan (starts (update-nth r np starts)) (np (+ np c))
                            (pgs-mem (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem))))
                 (:instance fn-hp-x-append-plan-grow (starts (update-nth r np starts)) (np (+ np c))))
           :in-theory (union-theories '(fn-hp-len-lens-after fn-hp-nat-listp-lens-after natp car-cons cdr-cons
                                        (:type-prescription adt-cap) (:type-prescription fn-hp-x-unfit))
                                      (theory 'minimal-theory)))))
