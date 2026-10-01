; Immutable compiled operation readout. This is source, not SAMEpool admission.
; Only the image build may select source producer roots. Their four-MV results
; are evaluated in ACL2 and retained in the generated constant table; metadata
; or a representation predicate does not establish bounded phase evidence.
(in-package "ACL2")
(include-book "runtime-operation-compiled-table")

(defun fn-runtime-operation-compiled-source (kind)
 (declare (xargs :guard t))
 (let ((entry (fn-roc-entry kind *fn-runtime-operation-compiled-table*)))
  (if (and *fn-runtime-operation-compiled-binding*
           (consp entry) (eq (cadr entry) :compiled-operation-source))
      (mv :compiled-operation-source (caddr entry)
          (cadddr entry) (car (cddddr entry)))
    (mv :runtime-operation-unavailable nil nil nil))))

(defun fn-runtime-operation-compiled-coordinate ()
 (declare (xargs :guard t))
 (if *fn-runtime-operation-compiled-binding*
     (mv :compiled-operation-source *fn-runtime-operation-compiled-binding*)
   (mv :runtime-operation-unavailable nil)))

(defun fn-runtime-operation-compiled-body-cost (kind request cached)
 (declare (xargs :guard t))
 (fn-roc-selected-body-cost kind request cached))

; Constant-table lookup preserves the actual selected producer's full result;
; it performs neither a demand conversion nor STATE/pool mutation.
(defthm fn-roc-readout-is-selected-result-by-definition
 (let ((entry (fn-roc-entry kind *fn-runtime-operation-compiled-table*)))
  (implies (and *fn-runtime-operation-compiled-binding*
                (consp entry) (eq (cadr entry) :compiled-operation-source))
   (equal (fn-runtime-operation-compiled-source kind) (cdr entry))))
 :rule-classes nil)

(in-theory (disable fn-roc-entry fn-runtime-operation-compiled-source
                    fn-runtime-operation-compiled-coordinate
                    fn-runtime-operation-compiled-body-cost))

; The build retains the original complete kind roster and its scalar positions.
; Neither readout validates a live ATS association or current nonce.
(defun fn-runtime-operation-compiled-kinds ()
 (declare (xargs :guard t))
 *fn-runtime-operation-compiled-kinds*)
(defun fn-runtime-operation-compiled-slot (kind)
 (declare (xargs :guard t))
 (let ((row (fn-roc-entry kind *fn-runtime-operation-compiled-slots*)))
  (if (and *fn-runtime-operation-compiled-binding* (consp row))
      (mv :compiled-operation-source (fn-roc-at 1 row))
    (mv :runtime-operation-unavailable nil))))
(in-theory (disable fn-runtime-operation-compiled-kinds
                    fn-runtime-operation-compiled-slot))
