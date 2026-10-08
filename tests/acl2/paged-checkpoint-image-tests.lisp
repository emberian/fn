; Teeth and a ground run for books/paged-checkpoint-image.lisp.
;
;   1. the residency premise is needed: `fn-pck-x-prestate's first conclusion
;      (every delta position writable) fails for an image whose tape window is
;      right but whose pages are not marked resident (lazy open);
;   2. the window premise is needed: an image whose tape window is the prefix's
;      words followed by a nonzero word does not give the model's dirty set;
;   3. the ground run, over real stobjs, is the satisfiability witness of the
;      invariant and of the loop: from an empty image of ten pages, staging a
;      prefix record and marking the dirty page durable leaves `pcki-img' of the
;      prefix's words; growing to twelve pages and staging a delta record at the
;      prefix's word count leaves `pcki-img' of the two; and the keystone's
;      pre-state equation holds on the grown image.

(in-package "ACL2")
(include-book "../../books/paged-checkpoint-image")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

;; The constrained seam, attached: the frame trailer's words.
(defun pckit-trailer (p) (declare (xargs :guard t) (ignore p)) (list 11 22 33 44))
(defattach (fn-cpl-trailer-words pckit-trailer))

(must-fail-checked
 (defthm pckit-no-residency
   (implies (and (true-listp pw) (natp wl) (natp npn)
                 (<= 8 (pgs-v-length pgs-mem))
                 (equal (pgs-d-length pgs-mem) (pgs-v-length pgs-mem))
                 (equal (pgs-w-length pgs-mem) (* 2048 (pgs-v-length pgs-mem)))
                 (<= (len pw) (* 2048 (- (pgs-v-length pgs-mem) 8)))
                 (equal (pgs-x-words 0 16384 (* 2048 (- (pgs-v-length pgs-mem) 8)) pgs-mem)
                        (append pw (adt-tp-zeros (- (* 2048 (- (pgs-v-length pgs-mem) 8)) (len pw)))))
                 (<= (+ 8 (floor (+ (len pw) wl 2047) 2048)) npn))
            (pcks-res (len pw) (+ (len pw) wl) (pgs-x-grow-image npn pgs-mem)))
   :hints (("Goal" :do-not-induct t :in-theory (disable pcks-res-hi pcki-res pcki-prestate-res)))))

(must-fail-checked
 (defthm pckit-nonzero-after-prefix
   (implies (and (pcki-resident 8 (pgs-v-length pgs-mem) pgs-mem)
                 (true-listp pw) (natp wl) (natp npn) (posp wl)
                 (<= 8 (pgs-v-length pgs-mem))
                 (equal (pgs-d-length pgs-mem) (pgs-v-length pgs-mem))
                 (equal (pgs-w-length pgs-mem) (* 2048 (pgs-v-length pgs-mem)))
                 (<= (+ (len pw) 1) (* 2048 (- (pgs-v-length pgs-mem) 8)))
                 (equal (pgs-x-words 0 16384 (* 2048 (- (pgs-v-length pgs-mem) 8)) pgs-mem)
                        (append pw (cons 1 (adt-tp-zeros (- (- (* 2048 (- (pgs-v-length pgs-mem) 8)) (len pw)) 1)))))
                 (<= (+ 8 (floor (+ (len pw) wl 2047) 2048)) npn))
            (let* ((cnt (len pw))
                   (tail (nthcdr (* 2048 (floor cnt 2048)) pw))
                   (d (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros wl)))))
              (equal (pgs-x-abs-dirty (pgs-dirty-lpages d) (pgs-x-grow-image npn pgs-mem)) d)))
   :hints (("Goal" :do-not-induct t :in-theory (disable pcks-res-hi pcki-dirty-pos pcki-prestate-dirty fn-pck-x-prestate)))))

(defun pckit-rec (i n)
  (declare (xargs :mode :program))
  (fn-record-make i (+ 1 i) 0 "<a@x>" (make-list n :initial-element 7)
                  '("fn.test") "o" "s" "e" 1 5))

(defconst *pckit-prefix* (pckit-rec 0 5))
(defconst *pckit-delta* (pckit-rec 1 3))

; Attachments are not callable in a defconst, hence functions.
(defun pckit-w1 ()
  (declare (xargs :verify-guards nil))
  (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows (list *pckit-prefix*))))
(defun pckit-w2 ()
  (declare (xargs :verify-guards nil))
  (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows (list *pckit-prefix* *pckit-delta*))))
(defun pckit-base ()
  (declare (xargs :verify-guards nil))
  (fn-pck-plen (list *pckit-prefix*) 0))

; (list (pcki-img of the empty image) (pcki-img of the prefix after its commit)
; (the keystone's pre-state equation on the grown image) (pcki-img of both after
; the delta's commit)).
(defun pckit-run ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-mem
    (mv-let (out pgs-mem)
      (with-local-stobj fn-octets
        (mv-let (out pgs-mem fn-octets)
          (with-local-stobj fn-arena
            (mv-let (out pgs-mem fn-octets fn-arena)
              (let* ((pgs-mem (pgs-x-grow-image 10 pgs-mem))
                     (c0 (pcki-img nil pgs-mem)))
                (mv-let (v0 fn-octets pgs-mem)
                  (fn-pck-x-stage-rows (list *pckit-prefix*) 0 0 fn-arena fn-octets pgs-mem)
                  (declare (ignore v0))
                  (let* ((pgs-mem (pgs-x-commit-durable '(8) pgs-mem))
                         (c1 (pcki-img (pckit-w1) pgs-mem))
                         (pgs-mem (pgs-x-grow-image 12 pgs-mem))
                         (cnt (len (pckit-w1)))
                         (wl (- (len (pckit-w2)) cnt))
                         (d (pck-shift 8 (adt-tp-dirty-at cnt (nthcdr (* 2048 (floor cnt 2048)) (pckit-w1))
                                                          (adt-tp-zeros wl))))
                         (c2 (equal (pgs-x-abs-dirty (pgs-dirty-lpages d) pgs-mem) d)))
                    (mv-let (v1 fn-octets pgs-mem)
                      (fn-pck-x-stage-rows (list *pckit-delta*) cnt (pckit-base) fn-arena fn-octets pgs-mem)
                      (declare (ignore v1))
                      (let* ((pgs-mem (pgs-x-commit-durable '(8) pgs-mem))
                             (c3 (pcki-img (pckit-w2) pgs-mem)))
                        (mv (list c0 c1 c2 c3) pgs-mem fn-octets fn-arena))))))
              (mv out pgs-mem fn-octets)))
          (mv out pgs-mem)))
      out)))

(assert-event
 (and (fn-sccb-treep *pckit-prefix*) (fn-sccb-treep *pckit-delta*)
      (fn-pck-sccb-listp (list *pckit-prefix* *pckit-delta*))
      (> (pckit-base) 0)
      (< (len (pckit-w2)) 2048)
      (equal (pckit-run) (list t t t t))))
