; PRF-1281: direct line windows for an immutable NEWNEWS render continuation.
; No arena/catalog read occurs in this phase; the response retains its captured
; roots. Other cursor phases still use the existing serialized cursor entry.
(in-package "ACL2")
(include-book "string-line-fill")
(include-book "newnews-stream-cursor")
(include-book "served-plan-window")

(defun fn-splan-line-ready-p (p)
  (declare (xargs :guard t))
  (let* ((rest (fn-splan-rest p))
         (effect (fn-ag-car rest))
         (cur (fn-cur-at 1 effect))
         (progress (fn-cur-progress cur)))
    (and (atom (fn-splan-cur p))
         (fn-nnw-meta-effectp effect)
         (not (fn-cur-dependency cur))
         (not (consp (fn-cur-pending cur)))
         (fn-nnw-stream-renderp progress)
         (if (member-eq (fn-cur-at 2 (fn-cur-at 1 progress))
                       '(:stuff :text :cr :lf)) t nil))))

(defun fn-splan-line-window (p bytes fn-octets)
  (declare (xargs :guard (natp bytes) :stobjs fn-octets))
  (let ((fn-octets (fn-octets-clear fn-octets)))
    (if (or (zp bytes) (not (fn-splan-line-ready-p p)))
        (mv :ineligible p fn-octets)
      (let* ((rest (fn-splan-rest p))
             (cur (fn-cur-at 1 (fn-ag-car rest)))
             (progress (fn-cur-progress cur)))
        (mv-let (line fn-octets)
          (fn-sl-fill (fn-cur-at 1 progress) bytes fn-octets)
          (let* ((next-progress
                  (if line
                      (fn-nnw-stream-render line (fn-cur-at 2 progress))
                    (or (fn-cur-at 2 progress) '(:terminator))))
                 (next (fn-cur-make (fn-cur-context cur) next-progress nil nil)))
            (mv :ok (cons nil (cons (fn-nnw-meta-effect next) (fn-ag-cdr rest)))
                fn-octets)))))))
