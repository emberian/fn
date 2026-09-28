; fn: teeth for books/history-pages-relocate.lisp (lane arena-store-4,
; 2026-09-28).
;
; What this book is evidence FOR.  The growth step the host calls when an
; append answers (:grow R): over a page store state whose verified pages
; hold a two-event history's canonical image (starts (1 2 3 4 5), 6 pages),
; `fn-hp-x-relocate' moves the pool (region 4) to 2 fresh pages at the end.
; The keystone `fn-hp-x-relocate-refines' gets a positive witness asserting
; its complete antecedent and conclusion; the grown store is exactly the
; placed image at (1 2 3 4 6) in 8 pages and the open's header check reads
; that placement back.  Per hypothesis a removal witness (the retained ones
; hold, the omitted one fails, the conclusion fails) with a
; must-fail-checked of the weakened statement.  Refused and need verdicts
; leave the store unchanged (`fn-hp-x-relocate-not-ok-unchanged').  Named
; exceptions: (natp r), (< r 5), (natp c), (fn-hp-starts-okp starts) are the
; function's guard, which the host's call satisfies.
(in-package "ACL2")
(include-book "../../books/history-pages-relocate")
(include-book "must-fail-checked")

(local (in-theory (enable fn-hp-vhold-is-x)))

(defconst *hrt-h* (list (list :retained 1 "<a@x>" (list 1 2 3) "subject line") (list :other 7 nil)))
(defconst *hrt-lens* (fn-hp-lens *hrt-h* 0))
(defconst *hrt-s* '(1 2 3 4 5))
(defconst *hrt-np* 6)
(defconst *hrt-piw* (fn-hp-piw *hrt-h* 0 *hrt-s* *hrt-np*))
(defconst *hrt-v* (make-list *hrt-np* :initial-element 2))

(defun hrt-mem (w v np)
  (update-nth *pgs-wi* w
              (update-nth *pgs-vi* v
                          (update-nth *pgs-di* (make-list np :initial-element 0)
                                      (update-nth *pgs-tvi* '(2) (list nil nil nil nil nil nil))))))

; The canonical placement, and the pool's cap is one page.
(assert-event (and (equal (fn-hp-starts *hrt-h* 0) *hrt-s*) (equal (fn-hp-npages *hrt-h* 0) *hrt-np*)
                   (adt-placement-ok *hrt-s* *hrt-lens* *hrt-np*) (equal (adt-cap (nth 4 *hrt-lens*)) 1)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-x-relocate-refines.

(defmacro hrt-conc (h r c lens s np mem res p)
  ; RES is the relocation's answer, evaluated once
  `(let ((starts2 (mv-nth 1 ,res)) (np2 (mv-nth 2 ,res)) (mem2 (mv-nth 3 ,res)))
     (and (equal starts2 (update-nth ,r ,np ,s))
          (equal np2 (+ ,np ,c))
          (fn-hp-starts-okp starts2)
          (adt-placement-ok starts2 ,lens np2)
          (equal (pgs-v-length mem2) np2)
          (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw ,h 0 starts2 np2))
          (implies (and (natp ,p) (equal (nth ,p (nth *pgs-di* mem2)) 1)
                        (not (equal (nth ,p (nth *pgs-di* ,mem)) 1)))
                   (and (or (equal ,p 0)
                            (and (<= (nth ,r ,s) ,p) (< ,p (+ (nth ,r ,s) (adt-cap (nth ,r ,lens)))))
                            (and (<= ,np ,p) (< ,p np2)))
                        (equal (pgs-vi ,p mem2) 2))))))
(defmacro hrt-ok (res)
  `(equal (mv-nth 0 ,res) :ok))

(defthm hrt-relocate-w
  (let* ((mem (hrt-mem *hrt-piw* *hrt-v* *hrt-np*))
         (res (fn-hp-x-relocate 4 2 2 *hrt-lens* *hrt-s* *hrt-np* mem))
         (mem2 (mv-nth 3 res)))
    (and (equal 2 (len *hrt-h*)) (equal *hrt-lens* (fn-hp-lens *hrt-h* 0)) (fn-hp-starts-okp *hrt-s*)
         (natp 4) (< 4 5) (natp 2)
         (fn-hp-vhold 0 (pgs-v-length mem) mem *hrt-piw*)
         (hrt-ok res)
         (hrt-conc *hrt-h* 4 2 *hrt-lens* *hrt-s* *hrt-np* mem res 0)
         (hrt-conc *hrt-h* 4 2 *hrt-lens* *hrt-s* *hrt-np* mem res 5)
         (hrt-conc *hrt-h* 4 2 *hrt-lens* *hrt-s* *hrt-np* mem res 6)
         (hrt-conc *hrt-h* 4 2 *hrt-lens* *hrt-s* *hrt-np* mem res 7)
         ; the whole grown store is the placed image at the new placement
         (equal (nth *pgs-wi* mem2) (fn-hp-piw *hrt-h* 0 '(1 2 3 4 6) 8))
         ; and the open's header check reads the new placement back
         (equal (mv-nth 1 (fn-hp-x-header 8 mem2)) (list :ok 2 *hrt-lens* '(1 2 3 4 6)))
         ; the dirty part is not vacuous: header, old pool page, both new pages
         (equal (nth 0 (nth *pgs-di* mem2)) 1) (equal (nth 5 (nth *pgs-di* mem2)) 1)
         (equal (nth 6 (nth *pgs-di* mem2)) 1) (equal (nth 7 (nth *pgs-di* mem2)) 1)
         ; the other regions' pages were not touched
         (equal (nth 1 (nth *pgs-di* mem2)) 0) (equal (nth 4 (nth *pgs-di* mem2)) 0)
         ; the moved image differs from the old one at the old pool page
         (not (equal (fn-hp-piw *hrt-h* 0 '(1 2 3 4 6) 8)
                     (append *hrt-piw* (adt-zeros (* 2048 2)))))))
  :rule-classes nil)

; Relocating a column (region 1) the same way.
(defthm hrt-relocate-col-w
  (let* ((mem (hrt-mem *hrt-piw* *hrt-v* *hrt-np*))
         (res (fn-hp-x-relocate 1 1 2 *hrt-lens* *hrt-s* *hrt-np* mem))
         (mem2 (mv-nth 3 res)))
    (and (fn-hp-vhold 0 (pgs-v-length mem) mem *hrt-piw*)
         (hrt-ok res)
         (hrt-conc *hrt-h* 1 1 *hrt-lens* *hrt-s* *hrt-np* mem res 2)
         (equal (nth *pgs-wi* mem2) (fn-hp-piw *hrt-h* 0 '(1 6 3 4 5) 7))))
  :rule-classes nil)

(defmacro hrt-mf (name &rest hyps)
  ; the weakened statement must not prove
  `(must-fail-checked
    (defthm ,name
      (implies (and ,@hyps)
               (let ((mem2 (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem))))
                 (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h salt (update-nth r np starts) (+ np c)))))
      :hints (("Goal" :in-theory (disable fn-hp-vhold-is-x fn-hp-vhold-x fn-hp-vhold))))
    :step-limit 30000))

; (equal n (len h)): N carried as 5; the header's N word is not the image's.
(defthm hrt-relocate-n-removal
  (let* ((mem (hrt-mem *hrt-piw* *hrt-v* *hrt-np*)) (res (fn-hp-x-relocate 4 2 5 *hrt-lens* *hrt-s* *hrt-np* mem)))
    (and (not (equal 5 (len *hrt-h*))) (equal *hrt-lens* (fn-hp-lens *hrt-h* 0)) (fn-hp-starts-okp *hrt-s*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem *hrt-piw*)
         (hrt-ok res)
         (not (hrt-conc *hrt-h* 4 2 *hrt-lens* *hrt-s* *hrt-np* mem res 0))))
  :rule-classes nil)
(hrt-mf hrt-false-relocate-without-n
        (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts) (natp r) (< r 5) (natp c)
        (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
        (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))

; (equal lens (fn-hp-lens h salt)): the MKEY column's length carried as 8
; (same cap); the header's length word is not the image's.
(defthm hrt-relocate-lens-removal
  (let* ((mem (hrt-mem *hrt-piw* *hrt-v* *hrt-np*)) (lens (update-nth 0 8 *hrt-lens*))
         (res (fn-hp-x-relocate 4 2 2 lens *hrt-s* *hrt-np* mem)))
    (and (equal 2 (len *hrt-h*)) (not (equal lens (fn-hp-lens *hrt-h* 0))) (fn-hp-starts-okp *hrt-s*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem *hrt-piw*)
         (hrt-ok res)
         (not (hrt-conc *hrt-h* 4 2 lens *hrt-s* *hrt-np* mem res 0))))
  :rule-classes nil)
(hrt-mf hrt-false-relocate-without-lens
        (equal n (len h)) (fn-hp-starts-okp starts) (natp r) (< r 5) (natp c)
        (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
        (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))

; The verified-pages relation: a verified word of the pool's old page
; changed; the copy carries it to the new page.
(defthm hrt-relocate-vhold-removal
  (let* ((mem (hrt-mem (update-nth (+ (* 2048 5) 3) 7 *hrt-piw*) *hrt-v* *hrt-np*))
         (res (fn-hp-x-relocate 4 2 2 *hrt-lens* *hrt-s* *hrt-np* mem)))
    (and (equal 2 (len *hrt-h*)) (equal *hrt-lens* (fn-hp-lens *hrt-h* 0)) (fn-hp-starts-okp *hrt-s*)
         (not (fn-hp-vhold 0 (pgs-v-length mem) mem *hrt-piw*))
         (hrt-ok res)
         (not (hrt-conc *hrt-h* 4 2 *hrt-lens* *hrt-s* *hrt-np* mem res 0))))
  :rule-classes nil)
(hrt-mf hrt-false-relocate-without-vhold
        (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts) (natp r) (< r 5) (natp c)
        (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))

; The verdict: the pool's old page not verified; the answer is the fill
; the host serves, and nothing changed.
(defthm hrt-relocate-verdict-removal
  (let* ((mem (hrt-mem *hrt-piw* (update-nth 5 0 *hrt-v*) *hrt-np*))
         (res (fn-hp-x-relocate 4 2 2 *hrt-lens* *hrt-s* *hrt-np* mem)))
    (and (equal 2 (len *hrt-h*)) (equal *hrt-lens* (fn-hp-lens *hrt-h* 0)) (fn-hp-starts-okp *hrt-s*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem *hrt-piw*)
         (not (hrt-ok res))
         (equal (car (mv-nth 0 res)) :need-page)
         (equal (mv-nth 3 res) mem)
         (not (hrt-conc *hrt-h* 4 2 *hrt-lens* *hrt-s* *hrt-np* mem res 0))))
  :rule-classes nil)
(hrt-mf hrt-false-relocate-without-verdict
        (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts) (natp r) (< r 5) (natp c)
        (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)))

; -----------------------------------------------------------------------------
; The refusals: distinct verdicts, the store, placement and page count as
; given.

(defmacro hrt-refused (r c n lens s np mem reason)
  `(let ((res (fn-hp-x-relocate ,r ,c ,n ,lens ,s ,np ,mem)))
     (and (equal (mv-nth 0 res) (list :refused ,reason))
          (equal (mv-nth 1 res) ,s) (equal (mv-nth 2 res) ,np) (equal (mv-nth 3 res) ,mem))))

(defthm hrt-relocate-refusals
  (let ((mem (hrt-mem *hrt-piw* *hrt-v* *hrt-np*)))
    (and (hrt-refused 4 0 2 *hrt-lens* *hrt-s* *hrt-np* mem :capacity)            ; C = 0
         (hrt-refused 4 2 2 *hrt-lens* *hrt-s* 7 mem :image)                      ; the header names 7 pages
         (hrt-refused 4 2 2 *hrt-lens* '(1 2 3 4 4) *hrt-np* mem :placement)      ; pool over a column
         (hrt-refused 4 2 (expt 2 64) *hrt-lens* *hrt-s* *hrt-np* mem :out-of-range)))
  :rule-classes nil)
