; fn: teeth for books/history-pages-grow-then-append.lisp and the writer's
; growth in place (books/history-pages-append-grown.lisp) (lane
; arena-store-4, 2026-09-28).
;
; What this book is evidence FOR.  (1) A region's cap grows in place when
; the new lengths still fit: the pool of a two-event history, placed at
; (1 2 3 4 5) in 7 pages (page 6 free), takes a 16,400-octet event; its
; cap goes from one page to two and the store is exactly the appended
; history's placed image (`fn-hp-x-append-refines-placed' in full).  (2)
; The host's growth loop: at the canonical placement in 6 pages the same
; append answers (:grow 4 2); `fn-hp-x-relocate' 4 2 moves the pool to
; page 6 of 8; the append then answers :ok and the store is exactly the
; appended history's image at (1 2 3 4 6) in 8 pages.  (3) Every region
; outgrowing (lengths 16384): after relocating region 0 the answer is
; (:grow 1 2); the whole five-step loop is
; tests/acl2/history-pages-grow-five-tests.lisp (split for time).  The
; progress theorems get positive witnesses asserting their complete
; antecedent and conclusion, and per hypothesis a removal witness with a
; must-fail-checked of the weakened statement.  Named exceptions: (nat-listp
; lens), (equal (len lens) 5), (equal (len starts) 5) are the writer's
; guard, which the host's call satisfies.
(in-package "ACL2")
(include-book "../../books/history-pages-grow-then-append")
(include-book "must-fail-checked")

(local (in-theory (enable fn-hp-vhold-is-x)))

(defconst *hgt-h* (list (list :retained 1 "<a@x>" (list 1 2 3) "subject line") (list :other 7 nil)))
(defconst *hgt-big* (list :retained 3 "<c@x>" (list 6) (coerce (make-list 16400 :initial-element #\a) 'string)))
(defconst *hgt-h2* (append *hgt-h* (list *hgt-big*)))
(defconst *hgt-lens* (fn-hp-lens *hgt-h* 0))
(defconst *hgt-s* '(1 2 3 4 5))

(defun hgt-mem (w v np)
  (update-nth *pgs-wi* w
              (update-nth *pgs-vi* v
                          (update-nth *pgs-di* (make-list np :initial-element 0)
                                      (update-nth *pgs-tvi* '(2) (list nil nil nil nil nil nil))))))

(defun hgt-v (np) (make-list np :initial-element 2))

; The pool's cap is one page and grows to two with the event.
(assert-event (and (equal (fn-hp-starts *hgt-h* 0) *hgt-s*) (equal (fn-hp-npages *hgt-h* 0) 6)
                   (equal (adt-cap (nth 4 *hgt-lens*)) 1)
                   (equal (adt-cap (nth 4 (fn-hp-lens *hgt-h2* 0))) 2)))

; -----------------------------------------------------------------------------
; (1) The pool grows in place: fn-hp-x-append-refines-placed, every
;     hypothesis and every conclusion.

(defmacro hgt-ap-conc (h ev s np mem res p)
  ; the keystone's conclusion; RES is the append's answer at MEM, bound once
  `(let ((mem2 (mv-nth 3 ,res)))
     (and (fn-hp-okp (append ,h (list ,ev)) 0)
          (equal (mv-nth 1 ,res) (len (append ,h (list ,ev))))
          (equal (mv-nth 2 ,res) (fn-hp-lens (append ,h (list ,ev)) 0))
          (adt-placement-ok ,s (fn-hp-lens (append ,h (list ,ev)) 0) ,np)
          (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw (append ,h (list ,ev)) 0 ,s ,np))
          (implies (and (natp ,p) (equal (nth ,p (nth *pgs-di* mem2)) 1)
                        (not (equal (nth ,p (nth *pgs-di* ,mem)) 1)))
                   (and (member-equal ,p (fn-hp-append-pdirty ,h (list ,ev) 0 ,s))
                        (equal (pgs-vi ,p mem2) 2))))))

(defthm hgt-grow-in-place-w
  (let* ((piw (fn-hp-piw *hgt-h* 0 *hgt-s* 7)) (mem (hgt-mem piw (hgt-v 7) 7))
         (res (fn-hp-x-append *hgt-big* 0 2 *hgt-lens* *hgt-s* 7 mem)) (mem2 (mv-nth 3 res)))
    (and (fn-hp-okp *hgt-h* 0) (equal 2 (len *hgt-h*)) (equal *hgt-lens* (fn-hp-lens *hgt-h* 0))
         (fn-hp-starts-okp *hgt-s*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem piw)
         (equal (mv-nth 0 res) :ok)
         (hgt-ap-conc *hgt-h* *hgt-big* *hgt-s* 7 mem res 0)
         (hgt-ap-conc *hgt-h* *hgt-big* *hgt-s* 7 mem res 5)
         (hgt-ap-conc *hgt-h* *hgt-big* *hgt-s* 7 mem res 6)
         ; the whole store is the appended history's placed image
         (equal (nth *pgs-wi* mem2) (fn-hp-piw *hgt-h2* 0 *hgt-s* 7))
         ; the grown pool's second page was written
         (equal (nth 6 (nth *pgs-di* mem2)) 1)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; (2) Grow, relocate, append.

; (2) and fn-hp-grow-then-append at it: the complete antecedent and
; conclusion (the inner implication's antecedent is false here: the append
; after the relocation answers :ok; (3) exercises it).
(defmacro hgt-gta-conc (ev lens mem r c a0 rel a1 r2 c2)
  ; fn-hp-grow-then-append's conclusion; A0 the append's answer at MEM, REL
  ; the relocation's (R C), A1 the append's after it, each bound once
  `(and (natp ,r) (< ,r 5)
        (equal ,c (adt-cap (nth ,r (fn-hp-x-lens-after ,ev ,lens))))
        (< (adt-cap (nth ,r ,lens)) ,c)
        (equal (mv-nth 3 ,a0) ,mem)
        (not (equal (mv-nth 0 ,rel) '(:refused :capacity)))
        (not (equal (mv-nth 0 ,rel) '(:refused :placement)))
        (implies (and (equal (mv-nth 0 ,rel) :ok) (equal (mv-nth 0 ,a1) (list :grow ,r2 ,c2)))
                 (< ,r ,r2))))

(defthm hgt-gta-pool-w
  (let* ((mem (hgt-mem (fn-hp-piw *hgt-h* 0 *hgt-s* 6) (hgt-v 6) 6))
         (a0 (fn-hp-x-append *hgt-big* 0 2 *hgt-lens* *hgt-s* 6 mem))
         (rel (fn-hp-x-relocate 4 2 2 *hgt-lens* *hgt-s* 6 mem))
         (a1 (fn-hp-x-append *hgt-big* 0 2 *hgt-lens* (mv-nth 1 rel) (mv-nth 2 rel) (mv-nth 3 rel))))
    (and (nat-listp *hgt-lens*) (equal (len *hgt-lens*) 5) (equal (len *hgt-s*) 5)
         (equal (mv-nth 0 a0) (list :grow 4 2))
         (hgt-gta-conc *hgt-big* *hgt-lens* mem 4 2 a0 rel a1 4 2)
         ; fn-hp-grow-then-append-only-r: no region after the pool; the
         ; append after the relocation answers no :grow (it answers :ok)
         (fn-hp-same-caps (nthcdr 5 *hgt-lens*) (nthcdr 5 (fn-hp-x-lens-after *hgt-big* *hgt-lens*)))
         (equal (mv-nth 0 rel) :ok)
         (not (equal (car (mv-nth 0 a1)) :grow))
         (equal (mv-nth 0 a1) :ok)
         ; the store after both is the appended history's image at the new placement
         (equal (mv-nth 1 rel) '(1 2 3 4 6)) (equal (mv-nth 2 rel) 8)
         (equal (nth *pgs-wi* (mv-nth 3 a1)) (fn-hp-piw *hgt-h2* 0 '(1 2 3 4 6) 8))
         (fn-hp-vhold 0 (pgs-v-length (mv-nth 3 a1)) (mv-nth 3 a1) (fn-hp-piw *hgt-h2* 0 '(1 2 3 4 6) 8))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; (3) Every region outgrows (lengths 16384).

(defconst *hgt-ev* (list :other 9 nil))
(defconst *hgt-lm* '(16384 16384 16384 16384 16384))
(defmacro hgt-zmem (np) `(hgt-mem (make-list (* 2048 ,np) :initial-element 0) (hgt-v ,np) ,np))

; fn-hp-grow-then-append at the first step of (3), the inner implication's
; antecedent true: after relocating region 0 the answer is (:grow 1 2).
(defthm hgt-gta-first-w
  (let* ((mem (hgt-zmem 6))
         (a0 (fn-hp-x-append *hgt-ev* 0 0 *hgt-lm* *hgt-s* 6 mem))
         (rel (fn-hp-x-relocate 0 2 0 *hgt-lm* *hgt-s* 6 mem))
         (a1 (fn-hp-x-append *hgt-ev* 0 0 *hgt-lm* (mv-nth 1 rel) (mv-nth 2 rel) (mv-nth 3 rel))))
    (and (nat-listp *hgt-lm*) (equal (len *hgt-lm*) 5) (equal (len *hgt-s*) 5)
         (equal (mv-nth 0 a0) (list :grow 0 2))
         (equal (mv-nth 0 rel) :ok)
         (equal (mv-nth 0 a1) (list :grow 1 2))
         (hgt-gta-conc *hgt-ev* *hgt-lm* mem 0 2 a0 rel a1 1 2)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Hypothesis removals.

; fn-hp-grow-then-append without its verdict hypothesis: the append answers
; :ok (at the moved placement of (1)); R = nil is no region.
(defthm hgt-gta-verdict-removal
  (let* ((piw (fn-hp-piw *hgt-h* 0 *hgt-s* 7)) (mem (hgt-mem piw (hgt-v 7) 7))
         (a0 (fn-hp-x-append *hgt-big* 0 2 *hgt-lens* *hgt-s* 7 mem)))
    (and (nat-listp *hgt-lens*) (equal (len *hgt-lens*) 5) (equal (len *hgt-s*) 5)
         (equal (mv-nth 0 a0) :ok)
         (not (equal (mv-nth 0 a0) (list :grow nil nil)))
         (not (let ((rel (fn-hp-x-relocate nil nil 2 *hgt-lens* *hgt-s* 7 mem)))
                (hgt-gta-conc *hgt-big* *hgt-lens* mem nil nil a0 rel a0 nil nil)))))
  :rule-classes nil)
(must-fail-checked
 (defthm hgt-false-gta-without-verdict
   (implies (and (nat-listp lens) (equal (len lens) 5) (equal (len starts) 5))
            (natp r))
   :hints (("Goal" :in-theory (disable fn-hp-x-append fn-hp-x-relocate))))
 :step-limit 30000)

; fn-hp-grow-then-append-only-r without the caps of the later regions:
; every region outgrows; after relocating region 0 the answer is (:grow 1 2).
(defthm hgt-only-r-caps-removal
  (let* ((mem (hgt-zmem 6))
         (a0 (fn-hp-x-append *hgt-ev* 0 0 *hgt-lm* *hgt-s* 6 mem))
         (rel (fn-hp-x-relocate 0 2 0 *hgt-lm* *hgt-s* 6 mem))
         (a1 (fn-hp-x-append *hgt-ev* 0 0 *hgt-lm* (mv-nth 1 rel) (mv-nth 2 rel) (mv-nth 3 rel))))
    (and (nat-listp *hgt-lm*) (equal (len *hgt-lm*) 5) (equal (len *hgt-s*) 5)
         (equal (mv-nth 0 a0) (list :grow 0 2))
         (not (fn-hp-same-caps (nthcdr 1 *hgt-lm*) (nthcdr 1 (fn-hp-x-lens-after *hgt-ev* *hgt-lm*))))
         (equal (mv-nth 0 rel) :ok)
         (equal (car (mv-nth 0 a1)) :grow)))
  :rule-classes nil)

(defmacro hgt-only-r-mf (name &rest hyps)
  `(must-fail-checked
    (defthm ,name
      (implies (and ,@hyps)
               (not (equal (car (mv-nth 0 (fn-hp-x-append ev salt n lens
                                                          (mv-nth 1 (fn-hp-x-relocate r c n lens starts np pgs-mem))
                                                          (mv-nth 2 (fn-hp-x-relocate r c n lens starts np pgs-mem))
                                                          (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem)))))
                           :grow)))
      :hints (("Goal" :in-theory (disable fn-hp-x-append fn-hp-x-relocate))))
    :step-limit 30000))

(hgt-only-r-mf hgt-false-only-r-without-caps
               (nat-listp lens) (equal (len lens) 5) (equal (len starts) 5)
               (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) (list :grow r c))
               (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))

; ... without the relocation's :ok: the store is five pages, not the six the
; header names; the relocation refuses :image, nothing moves, and the
; append answers (:grow 4 2) again.
(defthm hgt-only-r-reloc-removal
  (let* ((mem (hgt-mem (take (* 2048 5) (fn-hp-piw *hgt-h* 0 *hgt-s* 6)) (hgt-v 5) 5))
         (a0 (fn-hp-x-append *hgt-big* 0 2 *hgt-lens* *hgt-s* 6 mem))
         (rel (fn-hp-x-relocate 4 2 2 *hgt-lens* *hgt-s* 6 mem))
         (a1 (fn-hp-x-append *hgt-big* 0 2 *hgt-lens* (mv-nth 1 rel) (mv-nth 2 rel) (mv-nth 3 rel))))
    (and (nat-listp *hgt-lens*) (equal (len *hgt-lens*) 5) (equal (len *hgt-s*) 5)
         (equal (mv-nth 0 a0) (list :grow 4 2))
         (fn-hp-same-caps (nthcdr 5 *hgt-lens*) (nthcdr 5 (fn-hp-x-lens-after *hgt-big* *hgt-lens*)))
         (equal (mv-nth 0 rel) (list :refused :image))
         (equal (car (mv-nth 0 a1)) :grow)))
  :rule-classes nil)
(hgt-only-r-mf hgt-false-only-r-without-reloc
               (nat-listp lens) (equal (len lens) 5) (equal (len starts) 5)
               (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) (list :grow r c))
               (fn-hp-same-caps (nthcdr (+ 1 r) lens) (nthcdr (+ 1 r) (fn-hp-x-lens-after ev lens))))

; ... without the verdict: the host relocates the pool to ONE page (C = 1,
; not the answered 2); the append after it answers :grow again.
(defthm hgt-only-r-verdict-removal
  (let* ((mem (hgt-mem (fn-hp-piw *hgt-h* 0 *hgt-s* 6) (hgt-v 6) 6))
         (a0 (fn-hp-x-append *hgt-big* 0 2 *hgt-lens* *hgt-s* 6 mem))
         (rel (fn-hp-x-relocate 4 1 2 *hgt-lens* *hgt-s* 6 mem))
         (a1 (fn-hp-x-append *hgt-big* 0 2 *hgt-lens* (mv-nth 1 rel) (mv-nth 2 rel) (mv-nth 3 rel))))
    (and (nat-listp *hgt-lens*) (equal (len *hgt-lens*) 5) (equal (len *hgt-s*) 5)
         (not (equal (mv-nth 0 a0) (list :grow 4 1)))
         (fn-hp-same-caps (nthcdr 5 *hgt-lens*) (nthcdr 5 (fn-hp-x-lens-after *hgt-big* *hgt-lens*)))
         (equal (mv-nth 0 rel) :ok)
         (equal (car (mv-nth 0 a1)) :grow)))
  :rule-classes nil)
(hgt-only-r-mf hgt-false-only-r-without-verdict
               (nat-listp lens) (equal (len lens) 5) (equal (len starts) 5)
               (fn-hp-same-caps (nthcdr (+ 1 r) lens) (nthcdr (+ 1 r) (fn-hp-x-lens-after ev lens)))
               (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))
