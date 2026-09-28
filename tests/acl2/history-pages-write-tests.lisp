; fn: teeth for books/history-pages-write-keys.lisp (lane arena-store-3,
; 2026-09-28).
;
; What this book is evidence FOR.  The writer the host calls
; (`fn-hp-x-append') appends an event into the page store's words: over a
; state whose verified pages hold the history's image words, an :ok leaves
; them holding the appended history's image words, answers the new header,
; and marks dirty only pages of the proved dirty list, verified.  A ground
; history's image is installed as the stobj's words (as the host's fills
; leave them); the keystone gets a positive witness asserting its complete
; antecedent and conclusion, and per hypothesis a witness where the
; retained ones hold, the omitted one fails and the conclusion fails, with a
; must-fail-checked of the weakened statement.  The writer takes the page
; count NP (FNADTSN2 header's NPAGES); at the canonical one no cap grows in
; place.  Named exceptions: the
; `fn-hp-okp' u64 bounds (need 2^64 octets).
(in-package "ACL2")
(include-book "../../books/history-pages-write-keys")
(include-book "must-fail-checked")

(local (in-theory (enable fn-hp-vhold-is-x)))

(assert-event
 (and (eq (symbol-class 'fn-hp-x-append (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hp-x-append-plan (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hp-x-put-blocks (w state)) :common-lisp-compliant)))

(defconst *hwt-h* (list (list :retained 1 "<a@x>" (list 1 2 3) "subject line") (list :other 7 nil)))
(defconst *hwt-ev* (list :retained 2 "<b@x>" (list 4 5) "another"))
(defconst *hwt-h2* (append *hwt-h* (list *hwt-ev*)))
(defconst *hwt-iw* (fn-hp-iw *hwt-h* 0))
(defconst *hwt-np* (fn-hp-npages *hwt-h* 0))
(defconst *hwt-v2* (make-list *hwt-np* :initial-element 2))
(defconst *hwt-lens* (fn-hp-lens *hwt-h* 0))
(defconst *hwt-starts* (fn-hp-starts *hwt-h* 0))

(defun hwt-mem (w v np)
  ; a page store state: words W, page flags V, nothing dirty, every table
  ; page verified
  (update-nth *pgs-wi* w
              (update-nth *pgs-vi* v
                          (update-nth *pgs-di* (make-list np :initial-element 0)
                                      (update-nth *pgs-tvi* '(2) (list nil nil nil nil nil nil))))))

(defmacro hwt-conc (h ev n lens starts np mem p)
  ; the keystone's conclusion at H EV N LENS STARTS NP MEM, the dirty part at P
  `(let ((mem2 (mv-nth 3 (fn-hp-x-append ,ev 0 ,n ,lens ,starts ,np ,mem))))
     (and (fn-hp-okp (append ,h (list ,ev)) 0)
          (equal (mv-nth 1 (fn-hp-x-append ,ev 0 ,n ,lens ,starts ,np ,mem)) (len (append ,h (list ,ev))))
          (equal (mv-nth 2 (fn-hp-x-append ,ev 0 ,n ,lens ,starts ,np ,mem)) (fn-hp-lens (append ,h (list ,ev)) 0))
          (equal (fn-hp-starts (append ,h (list ,ev)) 0) ,starts)
          (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-iw (append ,h (list ,ev)) 0))
          (implies (and (natp ,p) (equal (nth ,p (nth *pgs-di* mem2)) 1)
                        (not (equal (nth ,p (nth *pgs-di* ,mem)) 1)))
                   (and (member-equal ,p (fn-hp-append-dirty ,h (list ,ev) 0))
                        (equal (pgs-vi ,p mem2) 2))))))

; -----------------------------------------------------------------------------
; Positive witness: every hypothesis and every conclusion, the dirty part at
; the header page and at the pool's page.

(defthm hwt-append-w
  (let ((mem (hwt-mem *hwt-iw* *hwt-v2* *hwt-np*)))
    (and (fn-hp-okp *hwt-h* 0)
         (equal 2 (len *hwt-h*)) (equal *hwt-lens* (fn-hp-lens *hwt-h* 0))
         (equal *hwt-starts* (fn-hp-starts *hwt-h* 0)) (equal *hwt-np* (fn-hp-npages *hwt-h* 0))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hwt-h* 0))
         (equal (mv-nth 0 (fn-hp-x-append *hwt-ev* 0 2 *hwt-lens* *hwt-starts* *hwt-np* mem)) :ok)
         (hwt-conc *hwt-h* *hwt-ev* 2 *hwt-lens* *hwt-starts* *hwt-np* mem 0)
         (hwt-conc *hwt-h* *hwt-ev* 2 *hwt-lens* *hwt-starts* *hwt-np* mem (nth 4 *hwt-starts*))
         ; the dirty part is not vacuous: both pages were marked
         (equal (nth 0 (nth *pgs-di* (mv-nth 3 (fn-hp-x-append *hwt-ev* 0 2 *hwt-lens* *hwt-starts* *hwt-np* mem)))) 1)
         (equal (nth (nth 4 *hwt-starts*)
                     (nth *pgs-di* (mv-nth 3 (fn-hp-x-append *hwt-ev* 0 2 *hwt-lens* *hwt-starts* *hwt-np* mem))))
                1)))
  :rule-classes nil)

; A region whose new cap does not fit is the named verdict (:grow R C), and
; nothing is written: the empty history has zero-page columns at page 1 of
; a one-page image; the MKEY column needs C = 1 page.
(defthm hwt-append-grow
  (let* ((iw0 (fn-hp-iw nil 0)) (mem (hwt-mem iw0 (list 2) 1)))
    (and (equal (mv-nth 0 (fn-hp-x-append *hwt-ev* 0 0 (fn-hp-lens nil 0) (fn-hp-starts nil 0) (fn-hp-npages nil 0) mem))
                (list :grow 0 1))
         (equal (mv-nth 3 (fn-hp-x-append *hwt-ev* 0 0 (fn-hp-lens nil 0) (fn-hp-starts nil 0) (fn-hp-npages nil 0) mem)) mem)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Hypothesis removals.

; (equal n (len h)): the host carries N = 5; the append answers N 6.
(defthm hwt-append-n-removal
  (let ((mem (hwt-mem *hwt-iw* *hwt-v2* *hwt-np*)))
    (and (fn-hp-okp *hwt-h* 0)
         (not (equal 5 (len *hwt-h*))) (equal *hwt-lens* (fn-hp-lens *hwt-h* 0))
         (equal *hwt-starts* (fn-hp-starts *hwt-h* 0)) (equal *hwt-np* (fn-hp-npages *hwt-h* 0))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hwt-h* 0))
         (equal (mv-nth 0 (fn-hp-x-append *hwt-ev* 0 5 *hwt-lens* *hwt-starts* *hwt-np* mem)) :ok)
         (not (hwt-conc *hwt-h* *hwt-ev* 5 *hwt-lens* *hwt-starts* *hwt-np* mem 0))))
  :rule-classes nil)
(must-fail-checked
 (defthm hwt-false-append-without-n
   (implies (and (fn-hp-okp h salt)
                 (equal lens (fn-hp-lens h salt)) (equal starts (fn-hp-starts h salt)) (equal np (fn-hp-npages h salt))
                 (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                 (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))
            (equal (mv-nth 1 (fn-hp-x-append ev salt n lens starts np pgs-mem)) (len (append h (list ev)))))
   :hints (("Goal" :in-theory (disable fn-hp-vhold-is-x fn-hp-vhold-x fn-hp-vhold))))
 :step-limit 30000)

; (equal lens (fn-hp-lens h salt)): the MKEY column's length is carried as
; 8; the cell lands inside the column and the answered lengths are wrong.
(defconst *hwt-lens-bad* (update-nth 0 8 *hwt-lens*))
(defthm hwt-append-lens-removal
  (let ((mem (hwt-mem *hwt-iw* *hwt-v2* *hwt-np*)))
    (and (fn-hp-okp *hwt-h* 0)
         (equal 2 (len *hwt-h*)) (not (equal *hwt-lens-bad* (fn-hp-lens *hwt-h* 0)))
         (equal *hwt-starts* (fn-hp-starts *hwt-h* 0)) (equal *hwt-np* (fn-hp-npages *hwt-h* 0))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hwt-h* 0))
         (equal (mv-nth 0 (fn-hp-x-append *hwt-ev* 0 2 *hwt-lens-bad* *hwt-starts* *hwt-np* mem)) :ok)
         (not (hwt-conc *hwt-h* *hwt-ev* 2 *hwt-lens-bad* *hwt-starts* *hwt-np* mem 0))))
  :rule-classes nil)
(must-fail-checked
 (defthm hwt-false-append-without-lens
   (implies (and (fn-hp-okp h salt)
                 (equal n (len h)) (equal starts (fn-hp-starts h salt)) (equal np (fn-hp-npages h salt))
                 (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                 (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))
            (fn-hp-vhold 0 (pgs-v-length (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem)))
                         (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem))
                         (fn-hp-iw (append h (list ev)) salt)))
   :hints (("Goal" :in-theory (disable fn-hp-vhold-is-x fn-hp-vhold-x fn-hp-vhold))))
 :step-limit 30000)

; (equal starts (fn-hp-starts h salt)): the last column and the pool are
; carried swapped (a valid placement, not the image's); the cell and the
; tree land on each other's pages.
(defconst *hwt-starts-bad* (list (nth 0 *hwt-starts*) (nth 1 *hwt-starts*) (nth 2 *hwt-starts*)
                                 (nth 4 *hwt-starts*) (nth 3 *hwt-starts*)))
(defthm hwt-append-starts-removal
  (let ((mem (hwt-mem *hwt-iw* *hwt-v2* *hwt-np*)))
    (and (fn-hp-okp *hwt-h* 0)
         (equal 2 (len *hwt-h*)) (equal *hwt-lens* (fn-hp-lens *hwt-h* 0))
         (not (equal *hwt-starts-bad* (fn-hp-starts *hwt-h* 0))) (equal *hwt-np* (fn-hp-npages *hwt-h* 0))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hwt-h* 0))
         (equal (mv-nth 0 (fn-hp-x-append *hwt-ev* 0 2 *hwt-lens* *hwt-starts-bad* *hwt-np* mem)) :ok)
         (not (hwt-conc *hwt-h* *hwt-ev* 2 *hwt-lens* *hwt-starts-bad* *hwt-np* mem 0))))
  :rule-classes nil)
(must-fail-checked
 (defthm hwt-false-append-without-starts
   (implies (and (fn-hp-okp h salt)
                 (equal n (len h)) (equal lens (fn-hp-lens h salt)) (equal np (fn-hp-npages h salt))
                 (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                 (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))
            (fn-hp-vhold 0 (pgs-v-length (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem)))
                         (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem))
                         (fn-hp-iw (append h (list ev)) salt)))
   :hints (("Goal" :in-theory (disable fn-hp-vhold-is-x fn-hp-vhold-x fn-hp-vhold))))
 :step-limit 30000)

; The verified-pages relation: a verified header word the append does not
; write is changed; it stays changed.
(defthm hwt-append-vhold-removal
  (let ((mem (hwt-mem (update-nth 100 7 *hwt-iw*) *hwt-v2* *hwt-np*)))
    (and (fn-hp-okp *hwt-h* 0)
         (equal 2 (len *hwt-h*)) (equal *hwt-lens* (fn-hp-lens *hwt-h* 0))
         (equal *hwt-starts* (fn-hp-starts *hwt-h* 0)) (equal *hwt-np* (fn-hp-npages *hwt-h* 0))
         (not (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hwt-h* 0)))
         (equal (mv-nth 0 (fn-hp-x-append *hwt-ev* 0 2 *hwt-lens* *hwt-starts* *hwt-np* mem)) :ok)
         (not (hwt-conc *hwt-h* *hwt-ev* 2 *hwt-lens* *hwt-starts* *hwt-np* mem 0))))
  :rule-classes nil)
(must-fail-checked
 (defthm hwt-false-append-without-vhold
   (implies (and (fn-hp-okp h salt)
                 (equal n (len h)) (equal lens (fn-hp-lens h salt)) (equal starts (fn-hp-starts h salt)) (equal np (fn-hp-npages h salt))
                 (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))
            (fn-hp-vhold 0 (pgs-v-length (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem)))
                         (mv-nth 3 (fn-hp-x-append ev salt n lens starts np pgs-mem))
                         (fn-hp-iw (append h (list ev)) salt)))
   :hints (("Goal" :in-theory (disable fn-hp-vhold-is-x fn-hp-vhold-x fn-hp-vhold))))
 :step-limit 30000)

; The verdict: the header page is not verified; the append answers a need,
; writes nothing, and the answered N is the old one.
(defthm hwt-append-verdict-removal
  (let ((mem (hwt-mem *hwt-iw* (update-nth 0 0 *hwt-v2*) *hwt-np*)))
    (and (fn-hp-okp *hwt-h* 0)
         (equal 2 (len *hwt-h*)) (equal *hwt-lens* (fn-hp-lens *hwt-h* 0))
         (equal *hwt-starts* (fn-hp-starts *hwt-h* 0)) (equal *hwt-np* (fn-hp-npages *hwt-h* 0))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hwt-h* 0))
         (not (equal (mv-nth 0 (fn-hp-x-append *hwt-ev* 0 2 *hwt-lens* *hwt-starts* *hwt-np* mem)) :ok))
         (not (hwt-conc *hwt-h* *hwt-ev* 2 *hwt-lens* *hwt-starts* *hwt-np* mem 0))))
  :rule-classes nil)
(must-fail-checked
 (defthm hwt-false-append-without-verdict
   (implies (and (fn-hp-okp h salt)
                 (equal n (len h)) (equal lens (fn-hp-lens h salt)) (equal starts (fn-hp-starts h salt)) (equal np (fn-hp-npages h salt))
                 (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt)))
            (equal (mv-nth 1 (fn-hp-x-append ev salt n lens starts np pgs-mem)) (len (append h (list ev)))))
   :hints (("Goal" :in-theory (disable fn-hp-vhold-is-x fn-hp-vhold-x fn-hp-vhold))))
 :step-limit 30000)

; (fn-hp-okp h salt): a rational is no tree; its image still takes an
; append, and the appended history is not addressable as an image.
(defconst *hwt-bad* (list 1/2))
(defthm hwt-append-okp-removal
  (let* ((np (fn-hp-npages *hwt-bad* 0))
         (mem (hwt-mem (fn-hp-iw *hwt-bad* 0) (make-list np :initial-element 2) np)))
    (and (not (fn-hp-okp *hwt-bad* 0))
         (equal 1 (len *hwt-bad*))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-iw *hwt-bad* 0))
         (equal (mv-nth 0 (fn-hp-x-append *hwt-ev* 0 1 (fn-hp-lens *hwt-bad* 0) (fn-hp-starts *hwt-bad* 0) np mem)) :ok)
         (not (hwt-conc *hwt-bad* *hwt-ev* 1 (fn-hp-lens *hwt-bad* 0) (fn-hp-starts *hwt-bad* 0) np mem 0))))
  :rule-classes nil)
(must-fail-checked
 (defthm hwt-false-append-without-okp
   (implies (and (equal n (len h)) (equal lens (fn-hp-lens h salt)) (equal starts (fn-hp-starts h salt)) (equal np (fn-hp-npages h salt))
                 (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                 (equal (mv-nth 0 (fn-hp-x-append ev salt n lens starts np pgs-mem)) :ok))
            (fn-hp-okp (append h (list ev)) salt))
   :hints (("Goal" :in-theory (disable fn-hp-vhold-is-x fn-hp-vhold-x fn-hp-vhold))))
 :step-limit 30000)

; (equal np (fn-hp-npages h salt)) is a named exception: at the canonical
; starts only the pool (the last region) can grow in place, onto pages past
; the image's end; a counterexample needs such a page verified and holding
; what the image holds there (nothing), which no page store state's u64
; words do, so it has no ground witness.  The hypothesis is the host
; carrying the header's NPAGES (`fn-hp-x-header-is-image' answers it).
; What a larger NP does over an honest store: the event's tree is 16,400
; octets, the pool's cap would grow from one page to two onto page 6, which
; the six-page store does not have: :out-of-range, nothing written.
(defconst *hwt-big* (list :retained 3 "<c@x>" (list 6) (coerce (make-list 16400 :initial-element #\a) 'string)))
(defthm hwt-append-np-past-end
  (let ((mem (hwt-mem *hwt-iw* *hwt-v2* *hwt-np*)))
    (and (equal *hwt-np* 6)
         (< (adt-cap (nth 4 *hwt-lens*)) (adt-cap (nth 4 (fn-hp-lens (append *hwt-h* (list *hwt-big*)) 0))))
         (equal (mv-nth 0 (fn-hp-x-append *hwt-big* 0 2 *hwt-lens* *hwt-starts* 7 mem)) :out-of-range)
         (equal (mv-nth 3 (fn-hp-x-append *hwt-big* 0 2 *hwt-lens* *hwt-starts* 7 mem)) mem)
         ; at the canonical NP the same append is the growth answer
         (equal (mv-nth 0 (fn-hp-x-append *hwt-big* 0 2 *hwt-lens* *hwt-starts* 6 mem)) (list :grow 4 2))))
  :rule-classes nil)
