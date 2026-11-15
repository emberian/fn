; Schema inventory is evaluated once by ACL2 at declaration time. No served
; operation scans declarations, and no article-specific field limit is used.
(in-package "ACL2")
(include-book "runs-served")
(include-book "successor-workspace-geometry")
(fn2-book-layer :c)
(defun fn2-succ-octets-total (sid f n)
 (declare (xargs :verify-guards nil :measure (nfix (- (nfix n) (nfix f)))))
 (if (<= (nfix n) (nfix f)) 0 (+ (nfix (fn2-run-layout-octets-max sid f)) (fn2-succ-octets-total sid (+ 1 (nfix f)) n))))
(defun fn2-successor-fold-args-max (sid kinds)
 (declare (xargs :verify-guards nil))
 (if (atom kinds) 0
  (max (nfix (fn2-fold-arity sid (car kinds))) (fn2-successor-fold-args-max sid (cdr kinds)))))
(defun fn2-successor-schema-bounds (ids)
 (declare (xargs :verify-guards nil))
 (if (atom ids) '(0 0 0)
  (let* ((sid (car ids)) (nf (nfix (fn2-run-layout-fields sid 0)))
         (nk (nfix (fn2-run-layout-keys sid)))
         (rest (fn2-successor-schema-bounds (cdr ids))))
   (list (max nf (fn2-successor-fold-args-max sid *fn2-run-fold-kinds*) (nfix (car rest)))
         (max (nfix (- nf nk)) (nfix (cadr rest)))
         (max (fn2-succ-octets-total sid 0 nf) (nfix (caddr rest)))))))
; The same declaration metadata used by public PUT/replay admission. Internal
; archive codecs remain in the run assembly and its decoder guard geometry;
; they are not successor writes and do not require public successor scratch.
(defun fn2-successor-declared-schema-ids (rows assembled)
 (declare (xargs :verify-guards nil))
 (if (atom rows) nil
  (let ((row (cdar rows)))
   (if (and (member-equal (fn2-decl-get :id row) assembled)
            (not (fn2-decl-get :internal row)))
       (cons (fn2-decl-get :id row) (fn2-successor-declared-schema-ids (cdr rows) assembled))
    (fn2-successor-declared-schema-ids (cdr rows) assembled)))))
(make-event
 (let* ((ids (fn2-successor-declared-schema-ids (fn2-decl-rows :schema (w state)) *fn2-run-assembled-ids*))
        (bounds (fn2-successor-schema-bounds ids)))
  (value `(progn
    (defconst *fn2-successor-schema-ids* ',ids)
    (defconst *fn2-succ-fields-max* ,(car bounds))
    (defconst *fn2-succ-values-max* ,(cadr bounds))
    (defconst *fn2-succ-octets-max* ,(caddr bounds))))))
(defconst *fn2-succ-entry* 0)
(defconst *fn2-succ-raw* *fn2-succ-fields-max*)
(defconst *fn2-succ-eval* (+ *fn2-succ-raw* *fn2-succ-fields-max*))
(defconst *fn2-succ-res* (+ *fn2-succ-eval* *fn2-succ-fields-max*))
(defconst *fn2-succ-fresh* (+ *fn2-succ-res* *fn2-succ-values-max*))
(defconst *fn2-succ-block* (fn2-successor-block-fields *fn2-succ-fields-max* *fn2-succ-values-max*))
(defconst *fn2-idc-scratch-bytes* (fn2-successor-scratch-bytes *fn2-succ-octets-max*))
; Bind cost propagation is a separate actual-call audit, not an inferred
; bound from per-entry scratch size. This book changes no byte-cost claim.
(assert-event
 (and (<= *fn2-succ-fields-max* 32)
      (<= *fn2-succ-values-max* *fn2-succ-fields-max*)
      (< *fn2-succ-fresh* 256)
      (<= *fn2-succ-fields-max* *fn2-succ-raw*)
      (<= (+ *fn2-succ-raw* *fn2-succ-fields-max*) *fn2-succ-eval*)
      (<= (+ *fn2-succ-eval* *fn2-succ-fields-max*) *fn2-succ-res*)
      (<= (+ *fn2-succ-res* *fn2-succ-values-max*) *fn2-succ-fresh*)
      (< *fn2-succ-fresh* *fn2-succ-block*)
      (<= *fn2-succ-octets-max* *fn2-idc-scratch-bytes*)))
