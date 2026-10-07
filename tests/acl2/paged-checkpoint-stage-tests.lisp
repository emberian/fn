; Teeth and a ground run for books/paged-checkpoint-stage.lisp.
;
;   1. staging the delta one word early (at P - 1, not at the prefix's word
;      count P) is not the model's dirty set: the keystone's statement with
;      the stage started at P - 1 fails;
;   2. the ground run, over real stobjs: a prefix record staged from position 0
;      and a delta record staged at P gives, on the one dirty page, the words
;      of the model's dirty set (:ok, the premises hold); the same delta
;      staged at P - 1 does not.  The run is the satisfiability witness of the
;      keystone's premise set (resident pages, tail then zeros, trees).

(in-package "ACL2")
(include-book "../../books/paged-checkpoint-stage")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(must-fail-checked
 (defthm pckst-stage-one-word-early
   (let* ((delta (fn-rows-wire-of rows fn-arena))
          (pw (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix)))
          (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows delta)))
          (tape (pck-shift *fn-pck-root-pages*
                           (fn-pck-row-extend-dirty (fn-pck-rows prefix) (fn-pck-rows delta))))
          (lp (pgs-dirty-lpages tape)))
     (implies (and (equal cnt (len pw)) (posp cnt)
                   (equal tail (nthcdr (* *pgs-page-words* (floor (len pw) *pgs-page-words*)) pw))
                   (fn-pck-sccb-listp delta)
                   (adt-tp-seq-lens-ok *fn-pck-row-schema* (fn-pck-rows delta))
                   (pcks-res (1- cnt) (+ cnt (len w)) pgs-mem)
                   (equal (pgs-x-abs-dirty lp pgs-mem)
                          (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros (len w))))))
              (equal (pgs-x-abs-dirty lp (mv-nth 2 (fn-pck-x-stage-rows rows (1- cnt) fn-arena fn-octets pgs-mem)))
                     tape)))))

(defconst *pckst-prefix* (cons '(1 . 2) '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17)))
(defconst *pckst-delta* (cons '(3 . 4) '(9 8 7)))

; The dirty page (page 8) after staging the prefix row from 0 and the delta
; row at P2, in an image of ten zero pages.
(defun pckst-run (p2)
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-mem
    (mv-let (out pgs-mem)
      (with-local-stobj fn-octets
        (mv-let (out pgs-mem fn-octets)
          (with-local-stobj fn-arena
            (mv-let (out pgs-mem fn-octets fn-arena)
              (let ((pgs-mem (pgs-x-grow-image 10 pgs-mem)))
                (mv-let (v0 fn-octets pgs-mem)
                  (fn-pck-x-stage-rows (list *pckst-prefix*) 0 fn-arena fn-octets pgs-mem)
                  (mv-let (v1 fn-octets pgs-mem)
                    (fn-pck-x-stage-rows (list *pckst-delta*) p2 fn-arena fn-octets pgs-mem)
                    (mv (list v0 v1 (pgs-x-abs-dirty '(8) pgs-mem)) pgs-mem fn-octets fn-arena))))
              (mv out pgs-mem fn-octets)))
          (mv out pgs-mem)))
      out)))

(defconst *pckst-cnt*
  (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows (list *pckst-prefix*)))))

(defconst *pckst-model*
  (pck-shift *fn-pck-root-pages*
             (fn-pck-row-extend-dirty (fn-pck-rows (list *pckst-prefix*))
                                      (fn-pck-rows (list *pckst-delta*)))))

(assert-event
 (and (fn-sccb-treep *pckst-prefix*) (fn-sccb-treep *pckst-delta*)
      (equal (pckst-run *pckst-cnt*) (list :ok :ok *pckst-model*))
      (not (equal (caddr (pckst-run (1- *pckst-cnt*))) *pckst-model*))
      (not (equal (caddr (pckst-run (1+ *pckst-cnt*))) *pckst-model*))))
