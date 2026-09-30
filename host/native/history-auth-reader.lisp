; Actual byte-at-a-time authenticated page driver. Loaded after owner.lisp.
; The controller owns the root pin and maintenance admission throughout.
(in-package "ACL2")

(defstruct (fnn-hsr-source (:constructor %make-fnn-hsr-source))
  cursor binding digest root-ticket buffer token buffer-id)

(defun fnn-hsr-source-begin (root source root-ticket lease)
  (destructuring-bind (verdict cursor binding)
      (fnn-call 'fn-hsr-source-begin root source root-ticket lease)
    (if (eq verdict :idle)
        (values verdict (%make-fnn-hsr-source
                         :cursor cursor :binding binding :root-ticket root-ticket
                         :digest (fnn-core 'create-pgs-digest-state)))
      (values verdict nil))))

(defun fnn-hsr-source-release-buffer (reader)
  "The caller has consumed the returned scalar and retains no vector alias."
  (let ((token (fnn-hsr-source-token reader))
        (id (fnn-hsr-source-buffer-id reader)))
    (setf (fnn-hsr-source-buffer reader) nil)
    (when token
      (fnn-snapshot-source-page-release token)
      (setf (fnn-hsr-source-token reader) nil
            (fnn-hsr-source-buffer-id reader) nil)
      (destructuring-bind (verdict cursor)
          (fnn-call 'fn-hsr-auth-release id (fnn-hsr-source-cursor reader))
        (setf (fnn-hsr-source-cursor reader) cursor)
        verdict))))

(defun fnn-hsr-source-step (service root-pin maintenance reader current-source demand)
  "One actual reader action; controller scheduling decides when to resume.
No page vector escapes. A READY result contains only one copied octet."
  (let* ((ticket (fnn-hsr-source-root-ticket reader))
         (binding (fnn-core 'fn-hsr-source-bind current-source ticket (fnn-hsr-source-cursor reader))))
    (setf (fnn-hsr-source-binding reader) binding)
    (let ((action (fnn-core 'fn-hsr-source-action demand binding ticket
                             (fnn-hsr-source-cursor reader))))
      (case (first action)
        (:select
         (destructuring-bind (verdict cursor digest)
             (fnn-call 'fn-hsr-auth-select-page (second action)
                       (fnn-hsr-source-cursor reader) (fnn-hsr-source-digest reader))
           (setf (fnn-hsr-source-cursor reader) cursor (fnn-hsr-source-digest reader) digest)
           verdict))
        (:request
         (destructuring-bind (verdict request cursor)
             (fnn-call 'fn-hsr-auth-request (fnn-hsr-source-cursor reader))
           (setf (fnn-hsr-source-cursor reader) cursor)
           (if (eq verdict :need-read)
               (multiple-value-bind (buffer token returned-request id count status)
                   (fnn-snapshot-source-read-page service root-pin request maintenance)
                 (setf (fnn-hsr-source-buffer reader) buffer
                       (fnn-hsr-source-token reader) token (fnn-hsr-source-buffer-id reader) id)
                 (destructuring-bind (completed next)
                     (fnn-call 'fn-hsr-auth-complete returned-request id count status cursor)
                   (setf (fnn-hsr-source-cursor reader) next)
                   completed))
             verdict)))
        (:feed
         (let* ((d (second action)) (id (fnn-core 'fn-hsr-field 1 d))
                (offset (fnn-core 'fn-hsr-field 2 d))
                (octet (aref (fnn-hsr-source-buffer reader) offset)))
           (destructuring-bind (verdict cursor)
               (fnn-call 'fn-hsr-auth-feed-byte id offset octet (fnn-hsr-source-cursor reader))
             (setf (fnn-hsr-source-cursor reader) cursor)
             verdict)))
        (:digest
         (destructuring-bind (verdict cursor digest)
             (fnn-call 'fn-hsr-auth-digest-tick (fnn-hsr-source-cursor reader)
                       (fnn-hsr-source-digest reader))
           (setf (fnn-hsr-source-cursor reader) cursor (fnn-hsr-source-digest reader) digest)
           verdict))
        (:release (fnn-hsr-source-release-buffer reader))
        (:ready
         (let* ((d (second action)) (offset (fnn-core 'fn-hsr-field 2 d))
                (octet (aref (fnn-hsr-source-buffer reader) offset)))
           (values :ready (fnn-core 'fn-hsr-source-byte-complete (third action) octet))))
        (otherwise action)))))
