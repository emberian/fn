; Teeth and a ground run for books/paged-checkpoint-stage.lisp.
;
;   1. staging the delta one word early (at P - 1, not at the prefix's word
;      count P) is not the model's dirty set: the keystone's statement with
;      the stage started at P - 1 fails;
;   2. staging the delta with its payload frames starting at the wrong base (0,
;      not the prefix's payload-file length) is not the model's dirty set: the
;      keystone's statement without the base premise fails;
;   3. the ground run, over real stobjs: a prefix record staged from position 0
;      (frame at 0) and a delta record staged at P (frame at the prefix's
;      payload-file length) gives, on the one dirty page, the words of the
;      model's dirty set (:ok, the premises hold); the same delta staged at
;      P - 1, P + 1, or with its frame at base 0 does not.  The run is the
;      satisfiability witness of the keystone's premise set (resident pages,
;      tail then zeros, trees, payload frames).

(in-package "ACL2")
(include-book "../../books/paged-checkpoint-stage")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

;; The constrained seam, attached: the frame trailer's words.
(defun pckst-trailer (p) (declare (xargs :guard t) (ignore p)) (list 11 22 33 44))

(must-fail-checked
 (defthm pckst-stage-one-word-early
   (let* ((delta (fn-rows-wire-of rows fn-arena))
          (pw (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix)))
          (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from delta base st)))
          (tape (pck-shift *fn-pck-root-pages*
                           (fn-pck-row-extend-dirty (fn-pck-rows prefix) (fn-pck-rows-from delta base st))))
          (lp (pgs-dirty-lpages tape)))
     (implies (and (equal cnt (len pw)) (posp cnt)
                   (equal tail (nthcdr (* *pgs-page-words* (floor (len pw) *pgs-page-words*)) pw))
                   (equal base (fn-pck-plen prefix 0))
                   (equal st (fn-pck-st-of (fn-pck-seed) prefix))
                   (fn-pck-sccb-listp delta st)
                   (fn-pck-plen-okp (append prefix delta))
                   (adt-tp-seq-lens-ok *fn-pck-row-schema* (fn-pck-rows-from delta base st))
                   (pcks-res (1- cnt) (+ cnt (len w)) pgs-mem)
                   (equal (pgs-x-abs-dirty lp pgs-mem)
                          (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros (len w))))))
              (equal (pgs-x-abs-dirty lp (mv-nth 2 (fn-pck-x-stage-rows rows (1- cnt) base st fn-arena fn-octets pgs-mem)))
                     tape)))))

(must-fail-checked
 (defthm pckst-stage-frames-at-the-wrong-base
   (let* ((delta (fn-rows-wire-of rows fn-arena))
          (pw (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix)))
          (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from delta base st)))
          (tape (pck-shift *fn-pck-root-pages*
                           (fn-pck-row-extend-dirty (fn-pck-rows prefix) (fn-pck-rows-from delta base st))))
          (lp (pgs-dirty-lpages tape)))
     (implies (and (equal cnt (len pw))
                   (equal tail (nthcdr (* *pgs-page-words* (floor (len pw) *pgs-page-words*)) pw))
                   (equal st (fn-pck-st-of (fn-pck-seed) prefix))
                   (fn-pck-sccb-listp delta st)
                   (fn-pck-plen-okp (append prefix delta))
                   (adt-tp-seq-lens-ok *fn-pck-row-schema* (fn-pck-rows-from delta base st))
                   (pcks-res cnt (+ cnt (len w)) pgs-mem)
                   (equal (pgs-x-abs-dirty lp pgs-mem)
                          (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros (len w))))))
              (equal (pgs-x-abs-dirty lp (mv-nth 2 (fn-pck-x-stage-rows rows cnt 0 st fn-arena fn-octets pgs-mem)))
                     tape)))))

(defun pckst-rec (i n)
  (declare (xargs :mode :program))
  (fn-record-make i (+ 1 i) 0 "<a@x>" (make-list n :initial-element 7)
                  '("fn.test") "o" "s" "e" 1 5))

(defconst *pckst-prefix* (pckst-rec 0 5))
(defconst *pckst-delta* (pckst-rec 1 3))
(defun pckst-base () (declare (xargs :verify-guards nil)) (fn-pck-plen (list *pckst-prefix*) 0))

(defun pckst-st1 ()
  ; the fold state after the prefix record, the delta's start state
  (declare (xargs :verify-guards nil))
  (fn-pck-st-of (fn-pck-seed) (list *pckst-prefix*)))

; The dirty page (page 8) after staging the prefix row from 0 and the delta
; row at P2 with its payload frame at BASE2, in an image of ten zero pages.
(defun pckst-run (p2 base2)
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-mem
    (mv-let (out pgs-mem)
      (with-local-stobj fn-octets
        (mv-let (out pgs-mem fn-octets)
          (with-local-stobj fn-arena
            (mv-let (out pgs-mem fn-octets fn-arena)
              (let ((pgs-mem (pgs-x-grow-image 10 pgs-mem)))
                (mv-let (v0 fn-octets pgs-mem)
                  (fn-pck-x-stage-rows (list *pckst-prefix*) 0 0 (fn-pck-seed) fn-arena fn-octets pgs-mem)
                  (mv-let (v1 fn-octets pgs-mem)
                    (fn-pck-x-stage-rows (list *pckst-delta*) p2 base2 (pckst-st1) fn-arena fn-octets pgs-mem)
                    (mv (list v0 v1 (pgs-x-abs-dirty '(8) pgs-mem)) pgs-mem fn-octets fn-arena))))
              (mv out pgs-mem fn-octets)))
          (mv out pgs-mem)))
      out)))

(defun pckst-cnt ()
  (declare (xargs :verify-guards nil))
  (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows (list *pckst-prefix*)))))

(defun pckst-model ()
  ; attachments are not callable in a defconst, hence functions
  (declare (xargs :verify-guards nil))
  (pck-shift *fn-pck-root-pages*
             (fn-pck-row-extend-dirty (fn-pck-rows (list *pckst-prefix*))
                                      (fn-pck-rows-from (list *pckst-delta*) (pckst-base) (pckst-st1)))))

(assert-event
 (and (fn-sccb-treep *pckst-prefix*) (fn-sccb-treep *pckst-delta*)
      (fn-pck-sccb-listp (list *pckst-prefix* *pckst-delta*) (fn-pck-seed))
      (not (equal (fn-pck-st-of (fn-pck-seed) (list *pckst-prefix* *pckst-delta*)) :bad))
      (adt-tp-seq-lens-ok *fn-pck-row-schema* (fn-pck-rows-from (list *pckst-delta*) (pckst-base) (pckst-st1)))
      (> (pckst-base) 0)
      (equal (pckst-run (pckst-cnt) (pckst-base)) (list :ok :ok (pckst-model)))
      (not (equal (caddr (pckst-run (1- (pckst-cnt)) (pckst-base))) (pckst-model)))
      (not (equal (caddr (pckst-run (1+ (pckst-cnt)) (pckst-base))) (pckst-model)))
      (not (equal (caddr (pckst-run (pckst-cnt) 0)) (pckst-model)))))
