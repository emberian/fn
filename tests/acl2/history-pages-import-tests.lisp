; fn: teeth for the import loop and the record view
; (books/history-pages-import.lisp, books/history-pages-view.lisp) (lane
; arena-store-4, 2026-09-28, m3c P1).
;
; What this book is evidence FOR.  fn-hp-x-append-all-refines: init, then
; the import of six events of varied sizes (the first relocates all five
; regions, the 16,400-octet third relocates the pool); the store is exactly
; the six events' image at (1 2 3 4 6) in 8 pages, and the import stops at
; the first refusal with the prefix imaged.  fn-hp-records-at-is-nth reads
; the image's records, then the in-memory suffix, then refuses (:seq); a
; need-verdict when a row's page is evicted.  Positive witnesses assert
; the complete antecedent and conclusion; per hypothesis a removal witness
; and a must-fail-checked of the weakened statement.  Named exceptions:
; (fn-hp-starts-okp starts) and (natp i) are guards the host's call
; satisfies.
(in-package "ACL2")
(include-book "../../books/history-pages-import")
(include-book "../../books/history-pages-view")
(include-book "must-fail-checked")

(local (in-theory (enable fn-hp-vhold-is-x)))

(defconst *hsi-m0* '(nil nil nil nil nil nil))   ; the empty page store
(defconst *hsi-big* (list :retained 3 "<c@x>" (list 6) (coerce (make-list 16400 :initial-element #\a) 'string)))
(defconst *hsi-evs*
  (list (list :retained 1 "<a@x>" (list 1 2 3) "subject line")
        (list :other 7 nil)
        *hsi-big*
        (list :other 8 nil)
        (list :retained 4 "<d@x>" (list 7 8) (coerce (make-list 1000 :initial-element #\b) 'string))
        (list :other 9 (list 1))))
(defconst *hsi-e* '(0 0 0 0 0))
(defconst *hsi-s1* '(1 1 1 1 1))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-x-append-all-refines: init, then the import of six events
; of varied sizes.  The first relocates all five regions; the third (16,400
; octets) outgrows the pool's one page and the step relocates it to pages
; 6-7 of 8; the rest append in place.  The whole store is exactly the
; image of the six events at the answered placement.
(defmacro hsi-all-conc (h evs lens starts np mem res p)
  `(let* ((v (mv-nth 0 ,res)) (j (mv-nth 1 ,res)) (n2 (mv-nth 2 ,res)) (lens2 (mv-nth 3 ,res))
          (starts2 (mv-nth 4 ,res)) (np2 (mv-nth 5 ,res)) (mem2 (mv-nth 6 ,res))
          (h2 (append ,h (take j ,evs))))
     (and (natp j) (<= j (len ,evs))
          (implies (equal v :ok) (equal j (len ,evs)))
          (not (equal (car v) :grow))
          (fn-hp-okp h2 0)
          (equal n2 (len h2)) (equal lens2 (fn-hp-lens h2 0))
          (fn-hp-starts-okp starts2)
          (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h2 0 starts2 np2))
          (implies (and (equal v :ok) (or (consp ,evs) (adt-placement-ok ,starts ,lens ,np)))
                   (adt-placement-ok starts2 lens2 np2))
          (implies (and (natp ,p) (equal (nth ,p (nth *pgs-di* mem2)) 1)
                        (not (equal (nth ,p (nth *pgs-di* ,mem)) 1)))
                   (equal (pgs-vi ,p mem2) 2)))))

(defthm hsi-all-w
  (let* ((mem (mv-nth 5 (fn-hp-x-init *hsi-m0*)))
         (res (fn-hp-x-append-all *hsi-evs* 0 0 0 *hsi-e* *hsi-s1* 1 mem)))
    (and (fn-hp-okp nil 0) (equal 0 (len nil)) (equal *hsi-e* (fn-hp-lens nil 0))
         (fn-hp-starts-okp *hsi-s1*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw nil 0 *hsi-s1* 1))
         (equal (mv-nth 0 res) :ok) (equal (mv-nth 1 res) 6)
         (equal (mv-nth 4 res) '(1 2 3 4 6)) (equal (mv-nth 5 res) 8)
         (hsi-all-conc nil *hsi-evs* *hsi-e* *hsi-s1* 1 mem res 0)
         (hsi-all-conc nil *hsi-evs* *hsi-e* *hsi-s1* 1 mem res 5)
         (hsi-all-conc nil *hsi-evs* *hsi-e* *hsi-s1* 1 mem res 7)
         (equal (nth *pgs-wi* (mv-nth 6 res)) (fn-hp-piw *hsi-evs* 0 '(1 2 3 4 6) 8))
         ; and the view reads every record back, then the suffix, then refuses
         (equal (mv-nth 1 (fn-hp-records-at 2 6 '(x y) 0 (mv-nth 3 res) '(1 2 3 4 6) (mv-nth 6 res)))
                (list :ok *hsi-big*))
         (equal (mv-nth 1 (fn-hp-records-at 5 6 '(x y) 0 (mv-nth 3 res) '(1 2 3 4 6) (mv-nth 6 res)))
                (list :ok (nth 5 *hsi-evs*)))
         (equal (fn-hp-records-at 7 6 '(x y) 0 (mv-nth 3 res) '(1 2 3 4 6) (mv-nth 6 res)) (list :ok (list :ok 'y)))
         (equal (fn-hp-records-at 8 6 '(x y) 0 (mv-nth 3 res) '(1 2 3 4 6) (mv-nth 6 res)) (list :ok '(:refused :seq)))))
  :rule-classes nil)

; The import stops at the first answer other than :ok: an event that is no
; tree ((:refused :event)) after two good ones; two were appended and the
; store holds their image.
(defconst *hsi-bad-ev* (list 1/2))
(defthm hsi-all-stop-w
  (let* ((mem (mv-nth 5 (fn-hp-x-init *hsi-m0*)))
         (evs (list (car *hsi-evs*) (cadr *hsi-evs*) *hsi-bad-ev* (car *hsi-evs*)))
         (res (fn-hp-x-append-all evs 0 0 0 *hsi-e* *hsi-s1* 1 mem)))
    (and (equal (mv-nth 0 res) '(:refused :event)) (equal (mv-nth 1 res) 2)
         (hsi-all-conc nil evs *hsi-e* *hsi-s1* 1 mem res 1)
         (equal (nth *pgs-wi* (mv-nth 6 res)) (fn-hp-piw (take 2 *hsi-evs*) 0 '(1 2 3 4 5) 6))))
  :rule-classes nil)


; -----------------------------------------------------------------------------
; fn-hp-x-append-all-refines: hypothesis removals.

(defmacro hsi-all-mf (name &rest hyps)
  `(must-fail-checked
    (defthm ,name
      (implies (and ,@hyps)
               (let* ((res (fn-hp-x-append-all evs 0 salt n lens starts np pgs-mem))
                      (h2 (append h (take (mv-nth 1 res) evs))))
                 (implies (equal (mv-nth 0 res) :ok)
                          (and (fn-hp-okp h2 salt)
                               (equal (mv-nth 2 res) (len h2)) (equal (mv-nth 3 res) (fn-hp-lens h2 salt))
                               (fn-hp-vhold 0 (pgs-v-length (mv-nth 6 res)) (mv-nth 6 res)
                                            (fn-hp-piw h2 salt (mv-nth 4 res) (mv-nth 5 res)))))))
      :hints (("Goal" :in-theory (disable fn-hp-vhold-is-x fn-hp-vhold-x fn-hp-vhold fn-hp-x-append-all
                                          fn-hp-okp fn-hp-lens fn-hp-piw))))
    :step-limit 30000))

(defmacro hsi-h1-mem ()
  '(mv-nth 6 (fn-hp-x-append-all (take 1 *hsi-evs*) 0 0 0 *hsi-e* *hsi-s1* 1 (mv-nth 5 (fn-hp-x-init *hsi-m0*)))))
(defconst *hsi-tail* (list (nth 1 *hsi-evs*) (nth 3 *hsi-evs*) (nth 5 *hsi-evs*)))   ; three small events

; (equal n (len h)): N = 1 over the empty image.
(defthm hsi-all-n-removal
  (let* ((mem (mv-nth 5 (fn-hp-x-init *hsi-m0*)))
         (res (fn-hp-x-append-all *hsi-tail* 0 0 1 *hsi-e* *hsi-s1* 1 mem)))
    (and (fn-hp-okp nil 0) (not (equal 1 (len nil))) (equal *hsi-e* (fn-hp-lens nil 0)) (fn-hp-starts-okp *hsi-s1*)
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw nil 0 *hsi-s1* 1))
         (equal (mv-nth 0 res) :ok)
         (not (equal (mv-nth 2 res) (len (append nil (take (mv-nth 1 res) *hsi-tail*)))))))
  :rule-classes nil)
(hsi-all-mf hsi-false-all-without-n
            (fn-hp-okp h salt) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
            (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)))

; (equal lens (fn-hp-lens h salt)): the empty lengths over one event's image.
(defthm hsi-all-lens-removal
  (let* ((h (take 1 *hsi-evs*)) (mem (hsi-h1-mem))
         (res (fn-hp-x-append-all *hsi-tail* 0 0 1 *hsi-e* '(1 2 3 4 5) 6 mem)))
    (and (fn-hp-okp h 0) (equal 1 (len h)) (not (equal *hsi-e* (fn-hp-lens h 0))) (fn-hp-starts-okp '(1 2 3 4 5))
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 '(1 2 3 4 5) 6))
         (equal (mv-nth 0 res) :ok)
         (not (equal (mv-nth 3 res) (fn-hp-lens (append h (take (mv-nth 1 res) *hsi-tail*)) 0)))))
  :rule-classes nil)
(hsi-all-mf hsi-false-all-without-lens
            (fn-hp-okp h salt) (equal n (len h)) (fn-hp-starts-okp starts)
            (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)))

; (fn-hp-okp h salt): a history holding a rational, imaged.
(defthm hsi-all-okp-removal
  (let* ((h (list (car *hsi-evs*) *hsi-bad-ev*)) (lens (fn-hp-lens h 0)) (s (fn-hp-starts h 0)) (np (fn-hp-npages h 0))
         (piw (fn-hp-piw h 0 s np))
         (mem (update-nth *pgs-wi* piw
                          (update-nth *pgs-vi* (make-list np :initial-element 2)
                                      (update-nth *pgs-di* (make-list np :initial-element 0)
                                                  (update-nth *pgs-tvi* '(2) *hsi-m0*)))))
         (res (fn-hp-x-append-all *hsi-tail* 0 0 2 lens s np mem)))
    (and (not (fn-hp-okp h 0)) (equal 2 (len h)) (fn-hp-starts-okp s)
         (fn-hp-vhold 0 (pgs-v-length mem) mem piw)
         (equal (mv-nth 0 res) :ok)
         (not (fn-hp-okp (append h (take (mv-nth 1 res) *hsi-tail*)) 0))))
  :rule-classes nil)
(hsi-all-mf hsi-false-all-without-okp
            (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
            (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)))

; (fn-hp-vhold ..): a verified pool word past the pool's end set to 7.
(defthm hsi-all-vhold-removal
  (let* ((h (take 1 *hsi-evs*)) (m1 (hsi-h1-mem))
         (mem (update-nth *pgs-wi* (update-nth (+ (* 2048 5) 2000) 7 (nth *pgs-wi* m1)) m1))
         (evs (list (cadr *hsi-evs*)))
         (res (fn-hp-x-append-all evs 0 0 1 (fn-hp-lens h 0) '(1 2 3 4 5) 6 mem)))
    (and (fn-hp-okp h 0) (equal 1 (len h)) (fn-hp-starts-okp '(1 2 3 4 5))
         (not (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 '(1 2 3 4 5) 6)))
         (equal (mv-nth 0 res) :ok)
         (not (fn-hp-vhold 0 (pgs-v-length (mv-nth 6 res)) (mv-nth 6 res)
                           (fn-hp-piw (append h (take (mv-nth 1 res) evs)) 0 (mv-nth 4 res) (mv-nth 5 res))))))
  :rule-classes nil)
(hsi-all-mf hsi-false-all-without-vhold
            (fn-hp-okp h salt) (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hp-records-at-is-nth.

(defmacro hsi-view-conc (h i n suffix lens starts mem)
  `(let ((res (fn-hp-records-at ,i ,n ,suffix 0 ,lens ,starts ,mem)))
     (and (implies (and (< ,i (+ ,n (len ,suffix))) (equal (mv-nth 0 res) :ok))
                   (equal (mv-nth 1 res) (list :ok (nth ,i (append ,h ,suffix)))))
          (implies (< ,i (+ ,n (len ,suffix)))
                   (or (equal (mv-nth 0 res) :ok) (fn-hp-need-verdictp (mv-nth 0 res))))
          (implies (not (< ,i (+ ,n (len ,suffix))))
                   (and (equal (mv-nth 0 res) :ok) (equal (mv-nth 1 res) '(:refused :seq)))))))

; The view is exercised over four events without the big one (the pool
; stays at page 5 of 6); hsi-all-w reads the six events' image back too.
(defconst *hsi-v4* (list (nth 0 *hsi-evs*) (nth 1 *hsi-evs*) (nth 3 *hsi-evs*) (nth 4 *hsi-evs*)))
(defmacro hsi-six-mem ()
  '(mv-nth 6 (fn-hp-x-append-all *hsi-v4* 0 0 0 *hsi-e* *hsi-s1* 1 (mv-nth 5 (fn-hp-x-init *hsi-m0*)))))
(defconst *hsi-s6* '(1 2 3 4 5))

(defthm hsi-view-w
  (let* ((mem (hsi-six-mem)) (lens (fn-hp-lens *hsi-v4* 0)) (sfx '(x y))
         (mev (update-nth *pgs-vi* (update-nth 1 0 (nth *pgs-vi* mem)) mem)))
    (and (fn-hp-okp *hsi-v4* 0) (equal 4 (len *hsi-v4*)) (fn-hp-starts-okp *hsi-s6*)
         (adt-placement-ok *hsi-s6* lens 6)
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw *hsi-v4* 0 *hsi-s6* 6))
         (hsi-view-conc *hsi-v4* 2 4 sfx lens *hsi-s6* mem)
         (equal (mv-nth 0 (fn-hp-records-at 2 4 sfx 0 lens *hsi-s6* mem)) :ok)
         (hsi-view-conc *hsi-v4* 5 4 sfx lens *hsi-s6* mem)
         (equal (fn-hp-records-at 5 4 sfx 0 lens *hsi-s6* mem) (list :ok '(:ok y)))
         (hsi-view-conc *hsi-v4* 6 4 sfx lens *hsi-s6* mem)
         ; a row's page evicted: a need-verdict, and the relation still holds
         (fn-hp-vhold 0 (pgs-v-length mev) mev (fn-hp-piw *hsi-v4* 0 *hsi-s6* 6))
         (equal (car (mv-nth 0 (fn-hp-records-at 2 4 sfx 0 lens *hsi-s6* mev))) :need-page)
         (hsi-view-conc *hsi-v4* 2 4 sfx lens *hsi-s6* mev)))
  :rule-classes nil)

(defmacro hsi-view-mf (name &rest hyps)
  `(must-fail-checked
    (defthm ,name
      (implies (and ,@hyps)
               (let ((res (fn-hp-records-at i n suffix salt lens starts pgs-mem)))
                 (implies (and (< i (+ n (len suffix))) (equal (mv-nth 0 res) :ok))
                          (equal (mv-nth 1 res) (list :ok (nth i (append h suffix)))))))
      :hints (("Goal" :in-theory (disable fn-hp-vhold-is-x fn-hp-vhold-x fn-hp-vhold fn-hp-records-at fn-hp-x-at
                                          fn-hp-okp fn-hp-lens fn-hp-piw adt-placement-ok))))
    :step-limit 30000))

; (equal n (len h)): N = 3 over the four events' image; record 3 is read
; from the suffix.
(defthm hsi-view-n-removal
  (let* ((mem (hsi-six-mem)) (lens (fn-hp-lens *hsi-v4* 0)) (res (fn-hp-records-at 3 3 '(x y) 0 lens *hsi-s6* mem)))
    (and (fn-hp-okp *hsi-v4* 0) (not (equal 3 (len *hsi-v4*))) (fn-hp-starts-okp *hsi-s6*)
         (adt-placement-ok *hsi-s6* lens 6) (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw *hsi-v4* 0 *hsi-s6* 6))
         (natp 3) (< 3 (+ 3 2)) (equal (mv-nth 0 res) :ok)
         (not (equal (mv-nth 1 res) (list :ok (nth 3 (append *hsi-v4* '(x y))))))))
  :rule-classes nil)
(hsi-view-mf hsi-false-view-without-n
             (fn-hp-okp h salt) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
             (adt-placement-ok starts lens np) (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
             (natp i))

; (equal lens (fn-hp-lens h salt)): three events' lengths; the last row's
; pool entry lies past the pool length, refused.
(defthm hsi-view-lens-removal
  (let* ((mem (hsi-six-mem)) (lens (fn-hp-lens (take 3 *hsi-v4*) 0)) (res (fn-hp-records-at 3 4 nil 0 lens *hsi-s6* mem)))
    (and (fn-hp-okp *hsi-v4* 0) (equal 4 (len *hsi-v4*)) (not (equal lens (fn-hp-lens *hsi-v4* 0)))
         (fn-hp-starts-okp *hsi-s6*) (adt-placement-ok *hsi-s6* lens 6)
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw *hsi-v4* 0 *hsi-s6* 6))
         (natp 3) (equal (mv-nth 0 res) :ok)
         (not (equal (mv-nth 1 res) (list :ok (nth 3 *hsi-v4*))))))
  :rule-classes nil)
(hsi-view-mf hsi-false-view-without-lens
             (fn-hp-okp h salt) (equal n (len h)) (fn-hp-starts-okp starts)
             (adt-placement-ok starts lens np) (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
             (natp i))

; (fn-hp-vhold ..): record 0's first pool word changed on a verified page.
(defthm hsi-view-vhold-removal
  (let* ((m6 (hsi-six-mem)) (lens (fn-hp-lens *hsi-v4* 0))
         (mem (update-nth *pgs-wi* (update-nth (* 2048 5) 7 (nth *pgs-wi* m6)) m6))
         (res (fn-hp-records-at 0 4 nil 0 lens *hsi-s6* mem)))
    (and (fn-hp-okp *hsi-v4* 0) (equal 4 (len *hsi-v4*)) (fn-hp-starts-okp *hsi-s6*) (adt-placement-ok *hsi-s6* lens 6)
         (not (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw *hsi-v4* 0 *hsi-s6* 6)))
         (natp 0) (equal (mv-nth 0 res) :ok)
         (not (equal (mv-nth 1 res) (list :ok (nth 0 *hsi-v4*))))))
  :rule-classes nil)
(hsi-view-mf hsi-false-view-without-vhold
             (fn-hp-okp h salt) (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
             (adt-placement-ok starts lens np) (natp i))

; (adt-placement-ok ..): two events imaged with the pool over the
; length-offset column's page (starts (1 2 3 4 4)).
(defthm hsi-view-placement-removal
  (let* ((h (take 2 *hsi-v4*)) (lens (fn-hp-lens h 0)) (s '(1 2 3 4 4))
         (piw (fn-hp-piw h 0 s 7))
         (mem (update-nth *pgs-wi* piw
                          (update-nth *pgs-vi* (make-list 7 :initial-element 2)
                                      (update-nth *pgs-di* (make-list 7 :initial-element 0)
                                                  (update-nth *pgs-tvi* '(2) *hsi-m0*)))))
         (res (fn-hp-records-at 1 2 nil 0 lens s mem)))
    (and (fn-hp-okp h 0) (equal 2 (len h)) (fn-hp-starts-okp s) (not (adt-placement-ok s lens 7))
         (fn-hp-vhold 0 (pgs-v-length mem) mem piw)
         (natp 1) (equal (mv-nth 0 res) :ok)
         (not (equal (mv-nth 1 res) (list :ok (nth 1 h))))))
  :rule-classes nil)
(hsi-view-mf hsi-false-view-without-placement
             (fn-hp-okp h salt) (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
             (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np)) (natp i))

; (fn-hp-okp h salt): a rational is no tree; the read does not answer it.
(defthm hsi-view-okp-removal
  (let* ((h (list 1/2)) (lens (fn-hp-lens h 0)) (piw (fn-hp-piw h 0 '(1 2 3 4 5) 6))
         (mem (update-nth *pgs-wi* piw
                          (update-nth *pgs-vi* (make-list 6 :initial-element 2)
                                      (update-nth *pgs-di* (make-list 6 :initial-element 0)
                                                  (update-nth *pgs-tvi* '(2) *hsi-m0*)))))
         (res (fn-hp-records-at 0 1 nil 0 lens '(1 2 3 4 5) mem)))
    (and (not (fn-hp-okp h 0)) (equal 1 (len h)) (fn-hp-starts-okp '(1 2 3 4 5)) (adt-placement-ok '(1 2 3 4 5) lens 6)
         (fn-hp-vhold 0 (pgs-v-length mem) mem piw)
         (natp 0) (equal (mv-nth 0 res) :ok)
         (not (equal (mv-nth 1 res) (list :ok (nth 0 h))))))
  :rule-classes nil)
(hsi-view-mf hsi-false-view-without-okp
             (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
             (adt-placement-ok starts lens np) (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
             (natp i))
