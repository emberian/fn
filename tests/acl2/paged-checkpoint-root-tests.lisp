; Teeth and a ground run for books/paged-checkpoint-root.lisp.
;
;   1. the ground run, over real stobjs: a root tree staged into an image of ten
;      pages whose root region holds stale nonzero words (a previous, longer
;      root) gives, on pages 0..7, exactly the model's root pages: the
;      keystone's premise set is satisfiable and its conclusion holds;
;   2. must-fail: the same stage without the zero fill (only the root row's own
;      words written) leaves the stale words: not the model's root pages;
;   3. a root page that is not in the image: the verdict is not :ok;
;   4. a root over K pages is refused by name before a word is written.

(in-package "ACL2")
(include-book "../../books/paged-checkpoint-root")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *pckr-tree* '((1 2 3) (4 5) nil nil (9) 5))

; The variant without the zero fill: the loop stops at the row's last word.
(defun pckr-put-nofill (j nw fn-octets pgs-mem)
  (declare (xargs :stobjs (fn-octets pgs-mem) :verify-guards nil
                  :measure (nfix (- (nfix nw) (nfix j)))))
  (if (and (natp j) (natp nw) (< j nw))
      (mv-let (v pgs-mem)
        (pgs-x-write (floor j 2048) (mod j 2048) (fn-pck-x-root-word j nw fn-octets) pgs-mem)
        (if (eq v :ok) (pckr-put-nofill (1+ j) nw fn-octets pgs-mem) (mv v pgs-mem)))
    (mv :ok pgs-mem)))

(defun pckr-run (mode npages)
  ; (list VERDICT PAGES0-7) after staging *pckr-tree* (MODE :stage, :nofill) or
  ; the over-K tree (:over-k) into NPAGES pages that hold stale words.
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-mem
    (mv-let (out pgs-mem)
      (with-local-stobj fn-octets
        (mv-let (out pgs-mem fn-octets)
          (let ((pgs-mem (pgs-x-grow-image npages pgs-mem)))
            (mv-let (v0 pgs-mem) (if (< 7 npages) (pgs-x-write 7 2000 999 pgs-mem) (mv :skip pgs-mem))
              (declare (ignore v0))
              (mv-let (v1 pgs-mem) (if (< 7 npages) (pgs-x-write 0 3 888 pgs-mem) (mv :skip pgs-mem))
                (declare (ignore v1))
                (case mode
                  (:nofill
                   (let ((fn-octets (fn-pck-x-encode *pckr-tree* fn-octets)))
                     (mv-let (v pgs-mem)
                       (pckr-put-nofill 0 (fn-pck-x-row-words (fn-octets-len fn-octets)) fn-octets pgs-mem)
                       (mv (list v (pgs-x-abs-dirty '(0 1 2 3 4 5 6 7) pgs-mem)) pgs-mem fn-octets))))
                  (:over-k
                   (mv-let (v fn-octets pgs-mem)
                     (fn-pck-x-stage-root (make-list 140000 :initial-element 7) fn-octets pgs-mem)
                     (mv (list v (pgs-x-words 0 0 8 pgs-mem)) pgs-mem fn-octets)))
                  (otherwise
                   (mv-let (v fn-octets pgs-mem)
                     (fn-pck-x-stage-root *pckr-tree* fn-octets pgs-mem)
                     (mv (list v (if (< 7 npages) (pgs-x-abs-dirty '(0 1 2 3 4 5 6 7) pgs-mem) nil)) pgs-mem fn-octets)))))))
          (mv out pgs-mem)))
      out)))

(defun pckr-model ()
  (declare (xargs :verify-guards nil))
  (adt-tp-number 0 (fn-pck-root-pages-of-tree *pckr-tree*)))

(assert-event
 (and (fn-sccb-treep *pckr-tree*)
      (fn-pck-root-fitsp-tree *pckr-tree*)
      (adt-tp-seq-lens-ok *fn-pck-row-schema* (list (fn-pck-enc-root *pckr-tree*)))
      ;; 1. the keystone, run
      (equal (pckr-run :stage 10) (list :ok (pckr-model)))
      ;; 2. no zero fill: the stale words stay
      (equal (car (pckr-run :nofill 10)) :ok)
      (not (equal (cadr (pckr-run :nofill 10)) (pckr-model)))
      ;; 3. root pages not in the image
      (not (equal (car (pckr-run :stage 4)) :ok))
      ;; 4. over K pages: refused by name, nothing written (the stale word 888 stays)
      (equal (pckr-run :over-k 10) (list :checkpoint-root-over-k '(0 0 0 888 0 0 0 0)))))
