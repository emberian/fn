; fn: teeth for books/history-pages-step.lisp and the empty image
; (books/history-pages-import.lisp's fn-hp-x-init) (lane arena-store-4,
; 2026-09-28, m3c P1).
;
; What this book is evidence FOR.  (1) fn-hp-x-init-refines: the empty page
; store becomes the empty history's one-page image, read back by the
; open's header check.  (2) fn-hp-x-append-step-refines, the step the host
; calls per event: at the empty image the first event makes the writer
; answer (:grow 0 1) and the step relocates all five regions and appends
; (starts (1 2 3 4 5), 6 pages; the store is exactly the image); a
; need-verdict AFTER a relocation answers the relocated placement with the
; history unchanged, and the retry appends; a refusal changes nothing; a
; cap grows in place when a free page follows.  Positive witnesses assert
; the keystones' complete antecedent and conclusion; per hypothesis a
; removal witness and a must-fail-checked of the weakened statement.  The
; import loop and the view: tests/acl2/history-pages-import-tests.lisp.
(in-package "ACL2")
(include-book "../../books/history-pages-import")
(include-book "must-fail-checked")

(local (in-theory (enable fn-hp-vhold-is-x)))

(defconst *hst-m0* '(nil nil nil nil nil nil))   ; the empty page store
(defconst *hst-big* (list :retained 3 "<c@x>" (list 6) (coerce (make-list 16400 :initial-element #\a) 'string)))
(defconst *hst-evs*
  (list (list :retained 1 "<a@x>" (list 1 2 3) "subject line")
        (list :other 7 nil)
        *hst-big*
        (list :other 8 nil)
        (list :retained 4 "<d@x>" (list 7 8) (coerce (make-list 1000 :initial-element #\b) 'string))
        (list :other 9 (list 1))))
(defconst *hst-e* '(0 0 0 0 0))
(defconst *hst-s1* '(1 1 1 1 1))

(defmacro hst-step-conc (h ev n lens mem res p)
  ; fn-hp-x-append-step-refines' conclusion at salt 0; RES the step's answer at MEM
  `(let* ((v (mv-nth 0 ,res)) (n2 (mv-nth 1 ,res)) (lens2 (mv-nth 2 ,res))
          (starts2 (mv-nth 3 ,res)) (np2 (mv-nth 4 ,res)) (mem2 (mv-nth 5 ,res)))
     (and (fn-hp-starts-okp starts2)
          (not (equal (car v) :grow))
          (implies (equal v :ok)
                   (and (fn-hp-okp (append ,h (list ,ev)) 0)
                        (equal n2 (len (append ,h (list ,ev))))
                        (equal lens2 (fn-hp-lens (append ,h (list ,ev)) 0))
                        (adt-placement-ok starts2 lens2 np2)
                        (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw (append ,h (list ,ev)) 0 starts2 np2))))
          (implies (not (equal v :ok))
                   (and (equal n2 ,n) (equal lens2 ,lens)
                        (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw ,h 0 starts2 np2))))
          (implies (and (natp ,p) (equal (nth ,p (nth *pgs-di* mem2)) 1)
                        (not (equal (nth ,p (nth *pgs-di* ,mem)) 1)))
                   (equal (pgs-vi ,p mem2) 2)))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-x-init-refines, and the header the open reads back.
(defthm hst-init-w
  (let* ((res (fn-hp-x-init *hst-m0*)) (mem2 (mv-nth 5 res)))
    (and (pgs-memp *hst-m0*) (equal (pgs-v-length *hst-m0*) 0)
         (equal (mv-nth 0 res) :ok)
         (fn-hp-okp nil 0)
         (equal (mv-nth 1 res) (len nil))
         (equal (mv-nth 2 res) (fn-hp-lens nil 0)) (equal (mv-nth 2 res) *hst-e*)
         (equal (mv-nth 3 res) *hst-s1*) (equal (mv-nth 4 res) 1)
         (fn-hp-starts-okp (mv-nth 3 res))
         (adt-placement-ok (mv-nth 3 res) (mv-nth 2 res) (mv-nth 4 res))
         (equal (pgs-v-length mem2) 1)
         (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw nil 0 (mv-nth 3 res) (mv-nth 4 res)))
         (equal (pgs-vi 0 mem2) 2)
         (equal (nth 0 (nth *pgs-di* mem2)) 1)
         ; the whole store is the empty history's image
         (equal (nth *pgs-wi* mem2) (fn-hp-piw nil 0 *hst-s1* 1))
         ; the open reads its header back (fn-hp-x-header-is-placed)
         (equal (mv-nth 0 (fn-hp-x-header 1 mem2)) :ok)
         (equal (mv-nth 1 (fn-hp-x-header 1 mem2)) (list :ok 0 *hst-e* *hst-s1*))))
  :rule-classes nil)

;; fn-hp-x-init-refines without its verdict: a store that is not empty (one
;; page) is refused :image and holds no empty image.
(defthm hst-init-verdict-removal
  (let* ((m (update-nth *pgs-wi* (make-list 2048 :initial-element 5)
                        (update-nth *pgs-vi* '(2) (update-nth *pgs-di* '(0) (update-nth *pgs-tvi* '(2) *hst-m0*)))))
         (res (fn-hp-x-init m)))
    (and (equal (mv-nth 0 res) '(:refused :image))
         (not (equal (mv-nth 4 res) 1))
         (not (fn-hp-vhold 0 (pgs-v-length (mv-nth 5 res)) (mv-nth 5 res) (fn-hp-piw nil 0 *hst-s1* 1)))))
  :rule-classes nil)
(must-fail-checked
 (defthm hst-false-init-without-verdict
   (fn-hp-vhold 0 (pgs-v-length (mv-nth 5 (fn-hp-x-init pgs-mem))) (mv-nth 5 (fn-hp-x-init pgs-mem))
                (fn-hp-piw nil salt (mv-nth 3 (fn-hp-x-init pgs-mem)) (mv-nth 4 (fn-hp-x-init pgs-mem))))
   :hints (("Goal" :in-theory (disable fn-hp-vhold-is-x fn-hp-vhold-x fn-hp-vhold fn-hp-x-init fn-hp-piw))))
 :step-limit 30000)

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-x-append-step-refines at the empty image: the first event
; outgrows every region (caps 0 -> 1); the step relocates all five, in
; order, and appends.
(defthm hst-step-first-w
  (let* ((mem (mv-nth 5 (fn-hp-x-init *hst-m0*))) (ev (car *hst-evs*))
         (a0 (fn-hp-x-append ev 0 0 *hst-e* *hst-s1* 1 mem))
         (res (fn-hp-x-append-step ev 0 0 *hst-e* *hst-s1* 1 mem)))
    (and (fn-hp-okp nil 0) (equal 0 (len nil)) (equal *hst-e* (fn-hp-lens nil 0))
         (fn-hp-starts-okp *hst-s1*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw nil 0 *hst-s1* 1))
         (equal (mv-nth 0 a0) (list :grow 0 1))       ; the writer alone asks for growth
         (equal (mv-nth 0 res) :ok)
         (equal (mv-nth 3 res) '(1 2 3 4 5)) (equal (mv-nth 4 res) 6)   ; five relocations
         (hst-step-conc nil ev 0 *hst-e* mem res 0)
         (hst-step-conc nil ev 0 *hst-e* mem res 1)
         (hst-step-conc nil ev 0 *hst-e* mem res 5)
         (equal (nth *pgs-wi* (mv-nth 5 res)) (fn-hp-piw (list ev) 0 '(1 2 3 4 5) 6))))
  :rule-classes nil)

(defconst *hst-bad-ev* (list 1/2))
; -----------------------------------------------------------------------------
; The step's other answers.

; A need-verdict after a relocation: two events imaged at (1 2 3 4 5) in 6
; pages, page 1 (region 0) evicted (not verified).  The big event outgrows
; the pool; the relocation needs only the header page and the pool's old
; page, so it completes (pool at 6, 8 pages); the append after it touches
; page 1 and answers (:need-page 1 ..).  The step answers the relocated
; placement with the history unchanged -- the store is the TWO events'
; image at (1 2 3 4 6) in 8 pages; the host keeps it, fills page 1 and
; calls the step again, which appends with no further relocation.
(defun hst-evict (p mem) (update-nth *pgs-vi* (update-nth p 0 (nth *pgs-vi* mem)) mem))
(defun hst-fill (p mem) (update-nth *pgs-vi* (update-nth p 2 (nth *pgs-vi* mem)) mem))

(defthm hst-step-need-w
  (let* ((h (take 2 *hst-evs*))
         (mem0 (mv-nth 6 (fn-hp-x-append-all h 0 0 0 *hst-e* *hst-s1* 1 (mv-nth 5 (fn-hp-x-init *hst-m0*)))))
         (mem (hst-evict 1 mem0))
         (lens (fn-hp-lens h 0))
         (res (fn-hp-x-append-step *hst-big* 0 2 lens (quote (1 2 3 4 5)) 6 mem))
         (mem2 (hst-fill 1 (mv-nth 5 res)))
         (res2 (fn-hp-x-append-step *hst-big* 0 2 lens (mv-nth 3 res) (mv-nth 4 res) mem2)))
    (and (fn-hp-okp h 0) (fn-hp-starts-okp '(1 2 3 4 5))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 '(1 2 3 4 5) 6))
         (not (equal (pgs-vi 1 mem) 2))
         (equal (car (mv-nth 0 res)) :need-page) (equal (cadr (mv-nth 0 res)) 1)
         (equal (mv-nth 3 res) '(1 2 3 4 6)) (equal (mv-nth 4 res) 8)
         (hst-step-conc h *hst-big* 2 lens mem res 0)
         (hst-step-conc h *hst-big* 2 lens mem res 6)
         (equal (nth *pgs-wi* (mv-nth 5 res)) (fn-hp-piw h 0 '(1 2 3 4 6) 8))
         ; the retry
         (equal (mv-nth 0 res2) :ok) (equal (mv-nth 3 res2) '(1 2 3 4 6)) (equal (mv-nth 4 res2) 8)
         (equal (nth *pgs-wi* (mv-nth 5 res2)) (fn-hp-piw (take 3 *hst-evs*) 0 '(1 2 3 4 6) 8))))
  :rule-classes nil)

; A refusal: an event that is no tree; nothing changes.
(defthm hst-step-refused-w
  (let* ((h (take 2 *hst-evs*))
         (mem (mv-nth 6 (fn-hp-x-append-all h 0 0 0 *hst-e* *hst-s1* 1 (mv-nth 5 (fn-hp-x-init *hst-m0*)))))
         (lens (fn-hp-lens h 0))
         (res (fn-hp-x-append-step *hst-bad-ev* 0 2 lens '(1 2 3 4 5) 6 mem)))
    (and (fn-hp-okp h 0) (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 '(1 2 3 4 5) 6))
         (equal res (list '(:refused :event) 2 lens '(1 2 3 4 5) 6 mem))
         (hst-step-conc h *hst-bad-ev* 2 lens mem res 0)))
  :rule-classes nil)

; A cap that grows in place: the two events' image with the pool at page 5
; of 7 (page 6 free); the big event grows the pool's cap to two pages
; without a relocation.
(defthm hst-step-in-place-w
  (let* ((h (take 2 *hst-evs*)) (lens (fn-hp-lens h 0))
         (piw (fn-hp-piw h 0 '(1 2 3 4 5) 7))
         (mem (update-nth *pgs-wi* piw
                          (update-nth *pgs-vi* (make-list 7 :initial-element 2)
                                      (update-nth *pgs-di* (make-list 7 :initial-element 0)
                                                  (update-nth *pgs-tvi* '(2) *hst-m0*)))))
         (res (fn-hp-x-append-step *hst-big* 0 2 lens '(1 2 3 4 5) 7 mem)))
    (and (fn-hp-okp h 0) (fn-hp-starts-okp '(1 2 3 4 5)) (fn-hp-vhold 0 (pgs-v-length mem) mem piw)
         (< (adt-cap (nth 4 lens)) (adt-cap (nth 4 (fn-hp-lens (append h (list *hst-big*)) 0))))
         (equal (mv-nth 0 res) :ok) (equal (mv-nth 3 res) '(1 2 3 4 5)) (equal (mv-nth 4 res) 7)
         (hst-step-conc h *hst-big* 2 lens mem res 6)
         (equal (nth *pgs-wi* (mv-nth 5 res)) (fn-hp-piw (take 3 *hst-evs*) 0 '(1 2 3 4 5) 7))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; fn-hp-x-append-step-refines: hypothesis removals.  Named exception:
; (fn-hp-starts-okp starts) is the writer's guard, which the host's call
; satisfies.

(defmacro hst-step-mf (name &rest hyps)
  `(must-fail-checked
    (defthm ,name
      (implies (and ,@hyps)
               (let* ((res (fn-hp-x-append-step ev salt n lens starts np pgs-mem)) (v (mv-nth 0 res)))
                 (and (implies (equal v :ok)
                               (and (fn-hp-okp (append h (list ev)) salt)
                                    (equal (mv-nth 1 res) (len (append h (list ev))))
                                    (equal (mv-nth 2 res) (fn-hp-lens (append h (list ev)) salt))
                                    (fn-hp-vhold 0 (pgs-v-length (mv-nth 5 res)) (mv-nth 5 res)
                                                 (fn-hp-piw (append h (list ev)) salt (mv-nth 3 res) (mv-nth 4 res))))))))
      :hints (("Goal" :in-theory (disable fn-hp-vhold-is-x fn-hp-vhold-x fn-hp-vhold fn-hp-x-append-step
                                          fn-hp-okp fn-hp-lens fn-hp-piw))))
    :step-limit 30000))

(defmacro hst-h1-mem ()
  '(mv-nth 5 (fn-hp-x-append-step (car *hst-evs*) 0 0 *hst-e* *hst-s1* 1 (mv-nth 5 (fn-hp-x-init *hst-m0*)))))

; (equal n (len h)): N = 1 over the empty image; the header answers 2.
(defthm hst-step-n-removal
  (let* ((mem (mv-nth 5 (fn-hp-x-init *hst-m0*))) (ev (car *hst-evs*))
         (res (fn-hp-x-append-step ev 0 1 *hst-e* *hst-s1* 1 mem)))
    (and (fn-hp-okp nil 0) (not (equal 1 (len nil))) (equal *hst-e* (fn-hp-lens nil 0)) (fn-hp-starts-okp *hst-s1*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw nil 0 *hst-s1* 1))
         (equal (mv-nth 0 res) :ok)
         (not (equal (mv-nth 1 res) (len (list ev))))))
  :rule-classes nil)
(hst-step-mf hst-false-step-without-n
             (fn-hp-okp h salt) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
             (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)))

; (equal lens (fn-hp-lens h salt)): the empty lengths over one event's
; image; the append writes over record 0 and answers the wrong lengths.
(defthm hst-step-lens-removal
  (let* ((h (take 1 *hst-evs*)) (mem (hst-h1-mem)) (ev (cadr *hst-evs*))
         (res (fn-hp-x-append-step ev 0 1 *hst-e* '(1 2 3 4 5) 6 mem)))
    (and (fn-hp-okp h 0) (equal 1 (len h)) (not (equal *hst-e* (fn-hp-lens h 0))) (fn-hp-starts-okp '(1 2 3 4 5))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 '(1 2 3 4 5) 6))
         (equal (mv-nth 0 res) :ok)
         (not (equal (mv-nth 2 res) (fn-hp-lens (append h (list ev)) 0)))))
  :rule-classes nil)
(hst-step-mf hst-false-step-without-lens
             (fn-hp-okp h salt) (equal n (len h)) (fn-hp-starts-okp starts)
             (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)))

; (fn-hp-okp h salt): a history holding a rational (no tree), imaged; the
; step appends a good event, and the result is no image of a history.
(defconst *hst-bad-h* (list (car *hst-evs*) *hst-bad-ev*))
(defthm hst-step-okp-removal
  (let* ((h *hst-bad-h*) (lens (fn-hp-lens h 0)) (s (fn-hp-starts h 0)) (np (fn-hp-npages h 0))
         (piw (fn-hp-piw h 0 s np))
         (mem (update-nth *pgs-wi* piw
                          (update-nth *pgs-vi* (make-list np :initial-element 2)
                                      (update-nth *pgs-di* (make-list np :initial-element 0)
                                                  (update-nth *pgs-tvi* '(2) *hst-m0*)))))
         (ev (cadr *hst-evs*))
         (res (fn-hp-x-append-step ev 0 2 lens s np mem)))
    (and (not (fn-hp-okp h 0)) (equal 2 (len h)) (fn-hp-starts-okp s)
         (fn-hp-vhold 0 (pgs-v-length mem) mem piw)
         (equal (mv-nth 0 res) :ok)
         (not (fn-hp-okp (append h (list ev)) 0))))
  :rule-classes nil)
(hst-step-mf hst-false-step-without-okp
             (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
             (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)))

; (fn-hp-vhold ..): one event's image with a verified pool word past the
; pool's end set to 7; the append leaves it, and the store is no image.
(defthm hst-step-vhold-removal
  (let* ((h (take 1 *hst-evs*))
         (m1 (hst-h1-mem))
         (mem (update-nth *pgs-wi* (update-nth (+ (* 2048 5) 2000) 7 (nth *pgs-wi* m1)) m1))
         (ev (cadr *hst-evs*))
         (res (fn-hp-x-append-step ev 0 1 (fn-hp-lens h 0) '(1 2 3 4 5) 6 mem)))
    (and (fn-hp-okp h 0) (equal 1 (len h)) (fn-hp-starts-okp '(1 2 3 4 5))
         (not (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 '(1 2 3 4 5) 6)))
         (equal (mv-nth 0 res) :ok)
         (not (fn-hp-vhold 0 (pgs-v-length (mv-nth 5 res)) (mv-nth 5 res)
                           (fn-hp-piw (append h (list ev)) 0 (mv-nth 3 res) (mv-nth 4 res))))))
  :rule-classes nil)
(hst-step-mf hst-false-step-without-vhold
             (fn-hp-okp h salt) (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts))
