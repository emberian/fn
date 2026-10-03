;;; Trusted developer source admission in an initialized full ACL2 process.
;;; Called before native entry, when no owner or Store has been constructed.
;;; This is execution support, not a certificate or a new logical assumption.
(in-package "ACL2")

(cl:defun fnn-source-admit-files (paths)
  "Ordinary LD with fail-closed completion. Files control their own explicit
redefinition policy; existing stobj/attachment compatibility is not bypassed."
  (dolist (path paths)
    (let ((old-output (get *standard-co* *open-output-channel-key*)))
      (unwind-protect
          (progn
            ;; Saved channel properties refer to streams from initialization.
            ;; Source startup must use the current diagnostic stream, never fd1.
            (setf (get *standard-co* *open-output-channel-key*) *error-output*)
            (multiple-value-bind (erp reason next-state)
                (ld-fn (list (cons 'standard-oi path)
                             (cons 'standard-co *standard-co*)
                             (cons 'proofs-co *standard-co*)
                             (cons 'ld-prompt nil)
                             (cons 'ld-error-action :return))
                       *the-live-state* nil)
              (declare (ignore next-state))
              (unless (and (null erp) (eq reason :eof))
                (error "Source admission refused ~a: ~s" path reason))))
        (setf (get *standard-co* *open-output-channel-key*) old-output))))
  :loaded)
