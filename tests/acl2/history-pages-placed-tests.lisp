; fn: teeth for books/history-pages-placed.lisp and the placed writer's
; keystone (books/history-pages-append-grown.lisp; lanes arena-store-3 and
; arena-store-4, 2026-09-28).
;
; What this book is evidence FOR.  FNADTSN2's free placement: over a page
; store state whose verified pages hold the history's image with its pool
; MOVED to a new page at the image's end (starts (1 2 3 4 6), 7 pages, page
; 5 free), the open's header check, the row read and the writer the host
; calls behave as over the canonical image.  Each keystone gets a positive
; witness asserting its complete antecedent and conclusion at the moved
; placement, and per hypothesis a removal witness (the retained ones hold,
; the omitted one fails, the conclusion fails) with a must-fail-checked of
; the weakened statement.  Named exceptions: the `fn-hp-okp' u64 bounds
; (need 2^64 octets).
(in-package "ACL2")
(include-book "../../books/history-pages-append-grown")
(include-book "must-fail-checked")

(local (in-theory (enable fn-hp-vhold-is-x)))

(defconst *hpt-h* (list (list :retained 1 "<a@x>" (list 1 2 3) "subject line") (list :other 7 nil)))
(defconst *hpt-ev* (list :retained 2 "<b@x>" (list 4 5) "another"))
(defconst *hpt-lens* (fn-hp-lens *hpt-h* 0))
(defconst *hpt-s* '(1 2 3 4 6))      ; the pool moved from page 5 to page 6
(defconst *hpt-np* 7)
(defconst *hpt-piw* (fn-hp-piw *hpt-h* 0 *hpt-s* *hpt-np*))
(defconst *hpt-v* (make-list *hpt-np* :initial-element 2))
(defconst *hpt-bad* (list 1/2))

(defun hpt-mem (w v np)
  (update-nth *pgs-wi* w
              (update-nth *pgs-vi* v
                          (update-nth *pgs-di* (make-list np :initial-element 0)
                                      (update-nth *pgs-tvi* '(2) (list nil nil nil nil nil nil))))))

; The moved image is not the canonical one, and its placement is valid.
(assert-event (and (equal (fn-hp-starts *hpt-h* 0) '(1 2 3 4 5)) (equal (fn-hp-npages *hpt-h* 0) 6)
                   (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*)
                   (not (adt-placement-ok '(1 2 3 4 4) *hpt-lens* *hpt-np*))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-x-header-is-placed.

(defmacro hpt-hdr-conc (h s np mem)
  `(equal (mv-nth 1 (fn-hp-x-header ,np ,mem)) (list :ok (len ,h) (fn-hp-lens ,h 0) ,s)))

(defthm hpt-header-w
  (let ((mem (hpt-mem *hpt-piw* *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (fn-hp-starts-okp *hpt-s*) (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*)
         (equal (mv-nth 0 (fn-hp-x-header *hpt-np* mem)) :ok)
         (hpt-hdr-conc *hpt-h* *hpt-s* *hpt-np* mem)))
  :rule-classes nil)

(defmacro hpt-mf (name hyps conc)
  ; the weakened statement must not prove
  `(must-fail-checked
    (defthm ,name (implies (and ,@hyps) ,conc)
      :hints (("Goal" :in-theory (disable fn-hp-vhold-is-x fn-hp-vhold-x fn-hp-vhold))))
    :step-limit 30000))

; (fn-hp-okp h salt) in the header keystone is a named exception, as in
; arena-store-2's `fn-hp-x-header-is-image': the header of a history whose
; events are not trees still reads back its N and regions (no ground
; counterexample); it is kept, not witnessed.

; (fn-hp-starts-okp starts): four starts; the pool is placed nowhere.
(defthm hpt-header-starts-removal
  (let* ((s '(1 2 3 4)) (piw (fn-hp-piw *hpt-h* 0 s *hpt-np*)) (mem (hpt-mem piw *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (not (fn-hp-starts-okp s)) (adt-placement-ok s *hpt-lens* *hpt-np*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem piw)
         (equal (mv-nth 0 (fn-hp-x-header *hpt-np* mem)) :ok)
         (not (hpt-hdr-conc *hpt-h* s *hpt-np* mem))))
  :rule-classes nil)
(hpt-mf hpt-false-header-without-starts-okp
        ((fn-hp-okp h salt) (adt-placement-ok starts (fn-hp-lens h salt) np)
         (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
         (equal (mv-nth 0 (fn-hp-x-header np pgs-mem)) :ok))
        (equal (mv-nth 1 (fn-hp-x-header np pgs-mem)) (list :ok (len h) (fn-hp-lens h salt) starts)))

; (adt-placement-ok ...): the pool over the MKEY... over the offset column's
; page: refused :placement.
(defthm hpt-header-placement-removal
  (let* ((s '(1 2 3 4 4)) (piw (fn-hp-piw *hpt-h* 0 s *hpt-np*)) (mem (hpt-mem piw *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (fn-hp-starts-okp s) (not (adt-placement-ok s *hpt-lens* *hpt-np*))
         (fn-hp-vhold 0 (pgs-v-length mem) mem piw)
         (equal (mv-nth 0 (fn-hp-x-header *hpt-np* mem)) :ok)
         (not (hpt-hdr-conc *hpt-h* s *hpt-np* mem))))
  :rule-classes nil)
(hpt-mf hpt-false-header-without-placement
        ((fn-hp-okp h salt) (fn-hp-starts-okp starts)
         (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
         (equal (mv-nth 0 (fn-hp-x-header np pgs-mem)) :ok))
        (equal (mv-nth 1 (fn-hp-x-header np pgs-mem)) (list :ok (len h) (fn-hp-lens h salt) starts)))

; The verified-pages relation: the verified header's N word changed.
(defthm hpt-header-vhold-removal
  (let ((mem (hpt-mem (update-nth 6 5 *hpt-piw*) *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (fn-hp-starts-okp *hpt-s*) (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*)
         (not (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*))
         (equal (mv-nth 0 (fn-hp-x-header *hpt-np* mem)) :ok)
         (not (hpt-hdr-conc *hpt-h* *hpt-s* *hpt-np* mem))))
  :rule-classes nil)
(hpt-mf hpt-false-header-without-vhold
        ((fn-hp-okp h salt) (fn-hp-starts-okp starts) (adt-placement-ok starts (fn-hp-lens h salt) np)
         (equal (mv-nth 0 (fn-hp-x-header np pgs-mem)) :ok))
        (equal (mv-nth 1 (fn-hp-x-header np pgs-mem)) (list :ok (len h) (fn-hp-lens h salt) starts)))

; The verdict: the header page not verified.
(defthm hpt-header-verdict-removal
  (let ((mem (hpt-mem *hpt-piw* (update-nth 0 0 *hpt-v*) *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (fn-hp-starts-okp *hpt-s*) (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*)
         (not (equal (mv-nth 0 (fn-hp-x-header *hpt-np* mem)) :ok))
         (not (hpt-hdr-conc *hpt-h* *hpt-s* *hpt-np* mem))))
  :rule-classes nil)
(hpt-mf hpt-false-header-without-verdict
        ((fn-hp-okp h salt) (fn-hp-starts-okp starts) (adt-placement-ok starts (fn-hp-lens h salt) np)
         (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)))
        (equal (mv-nth 1 (fn-hp-x-header np pgs-mem)) (list :ok (len h) (fn-hp-lens h salt) starts)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-x-at-is-nth-placed (the row read at the moved placement).

(defmacro hpt-at-conc (h seq s mem)
  `(equal (mv-nth 1 (fn-hp-x-at ,seq 0 (len ,h) (fn-hp-lens ,h 0) ,s ,mem)) (list :ok (nth ,seq ,h))))
(defmacro hpt-at-ok (h seq s mem)
  `(equal (mv-nth 0 (fn-hp-x-at ,seq 0 (len ,h) (fn-hp-lens ,h 0) ,s ,mem)) :ok))
(defconst *hpt-pool-word* (+ (* 2048 6) (floor (fn-hp-pes-len (take 1 *hpt-h*)) 8)))

(defthm hpt-at-w
  (let ((mem (hpt-mem *hpt-piw* *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (natp 1) (< 1 (len *hpt-h*)) (fn-hp-starts-okp *hpt-s*)
         (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*)
         (hpt-at-ok *hpt-h* 1 *hpt-s* mem) (hpt-at-conc *hpt-h* 1 *hpt-s* mem)))
  :rule-classes nil)

(defmacro hpt-at-mf (name &rest hyps)
  `(hpt-mf ,name ,hyps
           (equal (mv-nth 1 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) starts pgs-mem)) (list :ok (nth seq h)))))

; (fn-hp-okp h salt): a rational is no tree; the read does not answer it.
(defthm hpt-at-okp-removal
  (let* ((piw (fn-hp-piw *hpt-bad* 0 '(1 2 3 4 5) 6)) (mem (hpt-mem piw (make-list 6 :initial-element 2) 6)))
    (and (not (fn-hp-okp *hpt-bad* 0)) (natp 0) (< 0 (len *hpt-bad*)) (fn-hp-starts-okp '(1 2 3 4 5))
         (adt-placement-ok '(1 2 3 4 5) (fn-hp-lens *hpt-bad* 0) 6)
         (fn-hp-vhold 0 (pgs-v-length mem) mem piw)
         (hpt-at-ok *hpt-bad* 0 '(1 2 3 4 5) mem) (not (hpt-at-conc *hpt-bad* 0 '(1 2 3 4 5) mem))))
  :rule-classes nil)
(hpt-at-mf hpt-false-at-without-okp
           (natp seq) (< seq (len h)) (fn-hp-starts-okp starts) (adt-placement-ok starts (fn-hp-lens h salt) np)
           (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
           (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) starts pgs-mem)) :ok))

; (natp seq): -1.
(defthm hpt-at-natp-removal
  (let ((mem (hpt-mem *hpt-piw* *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (not (natp -1)) (< -1 (len *hpt-h*)) (fn-hp-starts-okp *hpt-s*)
         (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*) (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*)
         (hpt-at-ok *hpt-h* -1 *hpt-s* mem) (not (hpt-at-conc *hpt-h* -1 *hpt-s* mem))))
  :rule-classes nil)
(hpt-at-mf hpt-false-at-without-natp
           (fn-hp-okp h salt) (< seq (len h)) (fn-hp-starts-okp starts) (adt-placement-ok starts (fn-hp-lens h salt) np)
           (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
           (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) starts pgs-mem)) :ok))

; (< seq (len h)): past the end the read refuses :seq.
(defthm hpt-at-bound-removal
  (let ((mem (hpt-mem *hpt-piw* *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (natp 2) (not (< 2 (len *hpt-h*))) (fn-hp-starts-okp *hpt-s*)
         (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*) (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*)
         (hpt-at-ok *hpt-h* 2 *hpt-s* mem) (not (hpt-at-conc *hpt-h* 2 *hpt-s* mem))))
  :rule-classes nil)
(hpt-at-mf hpt-false-at-without-bound
           (fn-hp-okp h salt) (natp seq) (fn-hp-starts-okp starts) (adt-placement-ok starts (fn-hp-lens h salt) np)
           (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
           (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) starts pgs-mem)) :ok))

; (fn-hp-starts-okp starts): four starts; the pool is read at page 0.
(defthm hpt-at-starts-removal
  (let* ((s '(1 2 3 4)) (piw (fn-hp-piw *hpt-h* 0 s *hpt-np*)) (mem (hpt-mem piw *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (natp 1) (< 1 (len *hpt-h*)) (not (fn-hp-starts-okp s))
         (adt-placement-ok s *hpt-lens* *hpt-np*) (fn-hp-vhold 0 (pgs-v-length mem) mem piw)
         (hpt-at-ok *hpt-h* 1 s mem) (not (hpt-at-conc *hpt-h* 1 s mem))))
  :rule-classes nil)
(hpt-at-mf hpt-false-at-without-starts-okp
           (fn-hp-okp h salt) (natp seq) (< seq (len h)) (adt-placement-ok starts (fn-hp-lens h salt) np)
           (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
           (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) starts pgs-mem)) :ok))

; (adt-placement-ok ...): the pool over the length-offset column's page.
(defthm hpt-at-placement-removal
  (let* ((s '(1 2 3 4 4)) (piw (fn-hp-piw *hpt-h* 0 s *hpt-np*)) (mem (hpt-mem piw *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (natp 1) (< 1 (len *hpt-h*)) (fn-hp-starts-okp s)
         (not (adt-placement-ok s *hpt-lens* *hpt-np*)) (fn-hp-vhold 0 (pgs-v-length mem) mem piw)
         (hpt-at-ok *hpt-h* 1 s mem) (not (hpt-at-conc *hpt-h* 1 s mem))))
  :rule-classes nil)
(hpt-at-mf hpt-false-at-without-placement
           (fn-hp-okp h salt) (natp seq) (< seq (len h)) (fn-hp-starts-okp starts)
           (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
           (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) starts pgs-mem)) :ok))

; The verified-pages relation: a verified pool word at the moved place changed.
(defthm hpt-at-vhold-removal
  (let ((mem (hpt-mem (update-nth *hpt-pool-word* 7 *hpt-piw*) *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (natp 1) (< 1 (len *hpt-h*)) (fn-hp-starts-okp *hpt-s*)
         (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*) (not (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*))
         (hpt-at-ok *hpt-h* 1 *hpt-s* mem) (not (hpt-at-conc *hpt-h* 1 *hpt-s* mem))))
  :rule-classes nil)
(hpt-at-mf hpt-false-at-without-vhold
           (fn-hp-okp h salt) (natp seq) (< seq (len h)) (fn-hp-starts-okp starts)
           (adt-placement-ok starts (fn-hp-lens h salt) np)
           (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) starts pgs-mem)) :ok))

; The verdict: the moved pool's page not verified; a need-verdict, no event.
(defthm hpt-at-verdict-removal
  (let ((mem (hpt-mem *hpt-piw* (update-nth 6 0 *hpt-v*) *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (natp 1) (< 1 (len *hpt-h*)) (fn-hp-starts-okp *hpt-s*)
         (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*) (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*)
         (not (hpt-at-ok *hpt-h* 1 *hpt-s* mem)) (not (hpt-at-conc *hpt-h* 1 *hpt-s* mem))))
  :rule-classes nil)
(hpt-at-mf hpt-false-at-without-verdict
           (fn-hp-okp h salt) (natp seq) (< seq (len h)) (fn-hp-starts-okp starts)
           (adt-placement-ok starts (fn-hp-lens h salt) np)
           (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-x-append-refines-placed (the writer at the moved placement).

(defmacro hpt-ap-conc (h ev n lens s np mem p)
  `(let ((mem2 (mv-nth 3 (fn-hp-x-append ,ev 0 ,n ,lens ,s ,np ,mem))))
     (and (fn-hp-okp (append ,h (list ,ev)) 0)
          (equal (mv-nth 1 (fn-hp-x-append ,ev 0 ,n ,lens ,s ,np ,mem)) (len (append ,h (list ,ev))))
          (equal (mv-nth 2 (fn-hp-x-append ,ev 0 ,n ,lens ,s ,np ,mem)) (fn-hp-lens (append ,h (list ,ev)) 0))
          (adt-placement-ok ,s (fn-hp-lens (append ,h (list ,ev)) 0) ,np)
          (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw (append ,h (list ,ev)) 0 ,s ,np))
          (implies (and (natp ,p) (equal (nth ,p (nth *pgs-di* mem2)) 1)
                        (not (equal (nth ,p (nth *pgs-di* ,mem)) 1)))
                   (and (member-equal ,p (fn-hp-append-pdirty ,h (list ,ev) 0 ,s))
                        (equal (pgs-vi ,p mem2) 2))))))
(defmacro hpt-ap-ok (ev n lens s np mem)
  `(equal (mv-nth 0 (fn-hp-x-append ,ev 0 ,n ,lens ,s ,np ,mem)) :ok))

(defthm hpt-append-w
  (let ((mem (hpt-mem *hpt-piw* *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (equal 2 (len *hpt-h*)) (equal *hpt-lens* (fn-hp-lens *hpt-h* 0))
         (fn-hp-starts-okp *hpt-s*) (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*)
         (hpt-ap-ok *hpt-ev* 2 *hpt-lens* *hpt-s* *hpt-np* mem)
         (hpt-ap-conc *hpt-h* *hpt-ev* 2 *hpt-lens* *hpt-s* *hpt-np* mem 0)
         (hpt-ap-conc *hpt-h* *hpt-ev* 2 *hpt-lens* *hpt-s* *hpt-np* mem 6)
         ; the dirty part is not vacuous: the header page and the MOVED pool page were marked
         (equal (nth 6 (nth *pgs-di* (mv-nth 3 (fn-hp-x-append *hpt-ev* 0 2 *hpt-lens* *hpt-s* *hpt-np* mem)))) 1)
         (equal (nth 0 (nth *pgs-di* (mv-nth 3 (fn-hp-x-append *hpt-ev* 0 2 *hpt-lens* *hpt-s* *hpt-np* mem)))) 1)
         ; the free page 5 was not touched
         (equal (nth 5 (nth *pgs-di* (mv-nth 3 (fn-hp-x-append *hpt-ev* 0 2 *hpt-lens* *hpt-s* *hpt-np* mem)))) 0)))
  :rule-classes nil)

(defmacro hpt-ap-mf (name &rest hyps)
  `(hpt-mf ,name ,hyps
           (let ((mem2 (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem))))
             (and (fn-hp-okp (append h (list ev)) salt)
                  (equal (mv-nth 1 (fn-hp-x-append ev salt n lens starts np pgs-mem)) (len (append h (list ev))))
                  (equal (mv-nth 2 (fn-hp-x-append ev salt n lens starts np pgs-mem))
                         (fn-hp-lens (append h (list ev)) salt))
                  (adt-placement-ok starts (fn-hp-lens (append h (list ev)) salt) np)
                  (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw (append h (list ev)) salt starts np))))))

; (fn-hp-okp h salt): a rational event in H.
(defthm hpt-append-okp-removal
  (let* ((piw (fn-hp-piw *hpt-bad* 0 '(1 2 3 4 5) 6)) (mem (hpt-mem piw (make-list 6 :initial-element 2) 6)))
    (and (not (fn-hp-okp *hpt-bad* 0)) (equal 1 (len *hpt-bad*))
         (fn-hp-starts-okp '(1 2 3 4 5)) (adt-placement-ok '(1 2 3 4 5) (fn-hp-lens *hpt-bad* 0) 6)
         (fn-hp-vhold 0 (pgs-v-length mem) mem piw)
         (hpt-ap-ok *hpt-ev* 1 (fn-hp-lens *hpt-bad* 0) '(1 2 3 4 5) 6 mem)
         (not (hpt-ap-conc *hpt-bad* *hpt-ev* 1 (fn-hp-lens *hpt-bad* 0) '(1 2 3 4 5) 6 mem 0))))
  :rule-classes nil)
(hpt-ap-mf hpt-false-append-without-okp
           (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
           (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
           (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))

; (equal n (len h)): N carried as 5.
(defthm hpt-append-n-removal
  (let ((mem (hpt-mem *hpt-piw* *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (not (equal 5 (len *hpt-h*))) (equal *hpt-lens* (fn-hp-lens *hpt-h* 0))
         (fn-hp-starts-okp *hpt-s*) (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*)
         (hpt-ap-ok *hpt-ev* 5 *hpt-lens* *hpt-s* *hpt-np* mem)
         (not (hpt-ap-conc *hpt-h* *hpt-ev* 5 *hpt-lens* *hpt-s* *hpt-np* mem 0))))
  :rule-classes nil)
(hpt-ap-mf hpt-false-append-without-n
           (fn-hp-okp h salt) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
           (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
           (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))

; (equal lens (fn-hp-lens h salt)): the MKEY column's length carried as 8.
(defthm hpt-append-lens-removal
  (let ((mem (hpt-mem *hpt-piw* *hpt-v* *hpt-np*)) (lens (update-nth 0 8 *hpt-lens*)))
    (and (fn-hp-okp *hpt-h* 0) (equal 2 (len *hpt-h*)) (not (equal lens (fn-hp-lens *hpt-h* 0)))
         (fn-hp-starts-okp *hpt-s*) (adt-placement-ok *hpt-s* lens *hpt-np*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*)
         (hpt-ap-ok *hpt-ev* 2 lens *hpt-s* *hpt-np* mem)
         (not (hpt-ap-conc *hpt-h* *hpt-ev* 2 lens *hpt-s* *hpt-np* mem 0))))
  :rule-classes nil)
(hpt-ap-mf hpt-false-append-without-lens
           (fn-hp-okp h salt) (equal n (len h)) (fn-hp-starts-okp starts)
           (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
           (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))

; (fn-hp-starts-okp starts) in the writer's keystone is a named exception:
; with four starts the pool is placed nowhere in both the image and the
; writes, and the conclusion holds; the failing case (six starts: the
; header's block holds a nil, is not u64 words, and is skipped) has no
; ground witness here (its image does not evaluate under the ground
; prover).  The hypothesis is the one `fn-hp-x-append-plan-shape' needs.

; The placement of the old lengths is not a hypothesis: the writer checks
; it.  The pool carried over the length-offset column's page: refused
; :placement, nothing written.
(defthm hpt-append-placement-refused
  (let* ((s '(1 2 3 4 4)) (piw (fn-hp-piw *hpt-h* 0 s *hpt-np*)) (mem (hpt-mem piw *hpt-v* *hpt-np*)))
    (and (not (adt-placement-ok s *hpt-lens* *hpt-np*))
         (equal (mv-nth 0 (fn-hp-x-append *hpt-ev* 0 2 *hpt-lens* s *hpt-np* mem)) (list :refused :placement))
         (equal (mv-nth 3 (fn-hp-x-append *hpt-ev* 0 2 *hpt-lens* s *hpt-np* mem)) mem)))
  :rule-classes nil)

; The verified-pages relation: a verified word the append does not write
; (on the moved pool's page, past its entries) changed; it stays changed.
(defthm hpt-append-vhold-removal
  (let ((mem (hpt-mem (update-nth (+ (* 2048 6) 1000) 7 *hpt-piw*) *hpt-v* *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (equal 2 (len *hpt-h*)) (equal *hpt-lens* (fn-hp-lens *hpt-h* 0))
         (fn-hp-starts-okp *hpt-s*) (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*)
         (not (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*))
         (hpt-ap-ok *hpt-ev* 2 *hpt-lens* *hpt-s* *hpt-np* mem)
         (not (hpt-ap-conc *hpt-h* *hpt-ev* 2 *hpt-lens* *hpt-s* *hpt-np* mem 0))))
  :rule-classes nil)
(hpt-ap-mf hpt-false-append-without-vhold
           (fn-hp-okp h salt) (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
          
           (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))

; The verdict: the moved pool's page not verified; nothing written.
(defthm hpt-append-verdict-removal
  (let ((mem (hpt-mem *hpt-piw* (update-nth 6 0 *hpt-v*) *hpt-np*)))
    (and (fn-hp-okp *hpt-h* 0) (equal 2 (len *hpt-h*)) (equal *hpt-lens* (fn-hp-lens *hpt-h* 0))
         (fn-hp-starts-okp *hpt-s*) (adt-placement-ok *hpt-s* *hpt-lens* *hpt-np*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem *hpt-piw*)
         (not (hpt-ap-ok *hpt-ev* 2 *hpt-lens* *hpt-s* *hpt-np* mem))
         (not (hpt-ap-conc *hpt-h* *hpt-ev* 2 *hpt-lens* *hpt-s* *hpt-np* mem 0))))
  :rule-classes nil)
(hpt-ap-mf hpt-false-append-without-verdict
           (fn-hp-okp h salt) (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
          
           (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)))
