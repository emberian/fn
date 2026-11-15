; Per-active-cursor physical page ownership. Catalog leases protect idle
; cursors; operation pins protect each in-flight sector independently.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-summary-leases")
(fn2-book-layer :c)
(defcolumns fn2-run-loads
 ((phase (:enum fn2-run-load-phase (:idle :reserved :read :wait :copy :context :verify :header :ready :uncertain)))
  (lease-mode (:enum fn2-run-load-lease-mode (:owned :root1-borrowed))) (borrow-token :u60)
  (kind :u8) (owner :u32) (generation :u60) (source :u32) (tag :u60)
  (windows :u8) (page :u32) (page-gen :u60) (scratch :u32) (scratch-gen :u60) (checker :u32)
  (unit :u60) (epoch :u60) (allocation :u60) (schema :u60) (run :u60) (level :u8)
  (history :u60) (incarnation :u60) (sector :u8) (copied :u32)
  (pending :bool) (op-slot :u32) (op-gen :u60)
  (hash-0 :u32) (hash-1 :u32) (hash-2 :u32) (hash-3 :u32)
  (hash-4 :u32) (hash-5 :u32) (hash-6 :u32) (hash-7 :u32))
 :extra-fields
 ((fn2-run-loads-admissions :type (unsigned-byte 60) :initially 0
   :why "Every actual IDLE-to-owned admission invalidates a cold initialized-loader scan before allocating.")))
(defun fn2-run-load-admission-begin (fn2-run-loads)
 (declare (xargs :stobjs fn2-run-loads :guard (fn2-run-loads-wfp fn2-run-loads)))
 (let ((next (+ 1 (fn2-run-loads-admissions fn2-run-loads))))
  (if (not (unsigned-byte-p 60 next)) (mv :generation-exhausted fn2-run-loads)
   (let ((fn2-run-loads (update-fn2-run-loads-admissions next fn2-run-loads)))
    (mv :ok fn2-run-loads)))))
(fn2-run-loads-preserves fn2-run-load-admission-begin (fn2-run-loads) :position 1)

; Direct operation routing avoids a whole-job scan at host completion. A
; stale generation cannot deliver into a reused cursor or clear its pending bit.
(defcolumns fn2-run-load-ops ((live :bool) (generation :u60) (cursor :u32)))
(defun fn2-run-load-ownerp (c kind owner generation fn2-run-loads)
 (declare (xargs :stobjs fn2-run-loads :guard (fn2-run-loads-wfp fn2-run-loads)))
 (and (natp c) (< c (fn2-run-loads-rows fn2-run-loads))
      (not (equal (fn2-run-loads-phase c fn2-run-loads) *fn2-run-load-phase-idle*))
      (equal kind (fn2-run-loads-kind c fn2-run-loads))
      (equal owner (fn2-run-loads-owner c fn2-run-loads))
      (equal generation (fn2-run-loads-generation c fn2-run-loads))))
(defun fn2-run-load-word (c i fn2-run-loads)
 (declare (xargs :stobjs fn2-run-loads :guard (and (fn2-run-loads-wfp fn2-run-loads)
  (natp c) (< c (fn2-run-loads-rows fn2-run-loads)) (natp i) (< i 8))))
 (case i
  (0 (fn2-run-loads-hash-0 c fn2-run-loads)) (1 (fn2-run-loads-hash-1 c fn2-run-loads))
  (2 (fn2-run-loads-hash-2 c fn2-run-loads)) (3 (fn2-run-loads-hash-3 c fn2-run-loads))
  (4 (fn2-run-loads-hash-4 c fn2-run-loads)) (5 (fn2-run-loads-hash-5 c fn2-run-loads))
  (6 (fn2-run-loads-hash-6 c fn2-run-loads)) (otherwise (fn2-run-loads-hash-7 c fn2-run-loads))))

; One source declaration emits operation-domain TYPE/WFP/ROWS contracts for
; every returned carrier. Readonly carriers remain only in the antecedent.
(defun fn2-run-load-frame-hyps (carriers)
 (declare (xargs :guard t :verify-guards nil))
 (if (atom carriers) nil
  (append (list (list (fn2-columns-sym (car carriers) "P") (car carriers))
                (list (fn2-columns-sym (car carriers) "-WFP") (car carriers)))
          (fn2-run-load-frame-hyps (cdr carriers)))))
(defun fn2-run-load-frame-specs (outputs)
 (declare (xargs :guard t :verify-guards nil))
 (if (atom outputs) nil
  (let* ((obj (caar outputs)) (pos (cadar outputs)) (stem (symbol-name obj)))
   (append (list (list (concatenate 'string "-" stem "-TYPE") (fn2-columns-sym obj "P") pos)
                 (list (concatenate 'string "-" stem "-WFP") (fn2-columns-sym obj "-WFP") pos)
                 (list (concatenate 'string "-" stem "-ROWS") (fn2-columns-sym obj "-ROWS") pos :frame obj))
           (fn2-run-load-frame-specs (cdr outputs))))))
(defmacro fn2-run-load-frames (name formals carriers outputs)
 `(fn2-run-loads-preserves ,name ,formals
   :position ,(cadar outputs) :hyps ,(fn2-run-load-frame-hyps carriers)
   :specs ,(fn2-run-load-frame-specs outputs)))
