; INITIAL reader construction. Load after history-auth-reader and owner.
; The caller retains the third result on the same job before exposing READER.
(in-package "ACL2")

(define-condition fnn-snapshot-initial-reader-retained (error)
  ((packet :initarg :packet :reader fnn-snapshot-initial-reader-retained-packet)
   (digest :initarg :digest :reader fnn-snapshot-initial-reader-retained-digest)
   (reader :initarg :reader :reader fnn-snapshot-initial-reader-retained-reader)
   (cause :initarg :cause :reader fnn-snapshot-initial-reader-retained-cause)))

(defun fnn-snapshot-initial-reader-begin
    (service coldsource maintenance page-source root-ticket)
  "Owner mutex held. Claim the actual core reader role before digest/reader
creation. A creator error retains the issued packet and every created alias.
No page boundary or NIL alias returns this whole reader role."
  (declare (ignore service))
  (destructuring-bind (erp packet pool state)
      (fnn-call 'fn-owner-recovery-initial-reader-begin
                coldsource maintenance page-source root-ticket
                (fnn-live-page-read-pool) *the-live-state*)
    (declare (ignore pool state))
    (when erp (fnn-fault "INITIAL reader core call failed"))
    (unless (eq (first packet) :reader)
      (return-from fnn-snapshot-initial-reader-begin (values :unavailable nil packet)))
    (let ((digest nil) (reader nil))
      (handler-case
          (progn
            (setq digest (fnn-core 'create-pgs-digest-state))
            (setq reader (%make-fnn-hsr-source
                          :cursor (third packet) :binding (fourth packet)
                          :root-ticket (fifth packet) :digest digest))
            (values :idle reader (second packet)))
        (error (condition)
          (error 'fnn-snapshot-initial-reader-retained
                 :packet packet :digest digest :reader reader :cause condition))))))
