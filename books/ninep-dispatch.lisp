; Actual concrete-buffer parser outputs feed the connection machine.
; Directory/article provider actions are separate funded continuations.
(in-package "ACL2")
(include-book "ninep-session")

(defun fn-9p-error-reply (msize tag reason)
 (declare (xargs :guard t))
 (let* ((text (case reason
                (:unknown-fid '(117 110 107 110 111 119 110 32 102 105 100))
                (:duplicate-tag '(116 97 103 32 105 110 32 117 115 101))
                (:provider-unavailable '(112 114 111 118 105 100 101 114 32 117 110 97 118 97 105 108 97 98 108 101))
                (otherwise nil)))
        (size (+ 9 (len text))))
  (if (not (and (fn-9p-profile-msizep msize) (natp tag) (< tag 65535) text (<= size msize)))
      '(:close :reply-unrepresentable)
    (list :refused reason (append (fn-9p-u32-octets size) '(107)
                                 (fn-9p-u16-octets tag) (fn-9p-u16-octets (len text)) text)))))

(defun fn-9p-empty-reply (msize tag type)
 (declare (xargs :guard t))
 (if (not (and (fn-9p-profile-msizep msize) (natp tag) (< tag 65535)
               (member-equal type '(109 121)))) '(:close :invalid-reply)
   (list :reply (append '(7 0 0 0) (list type) (fn-9p-u16-octets tag)))))

(defun fn-9p-dispatch-begin (cursor)
 (declare (xargs :guard t))
 (list :ninep-dispatch cursor 0))

; One tag/fid lookup cell per call. A Flush releases the wire tag but keeps
; the cancelled physical record. Clunk releases protocol fid use while the
; old slot/selection survives until actual borrowers return.
(defun fn-9p-dispatch-step (server-msize dispatch fn-octets fn-ninep-session)
 (declare (xargs :stobjs (fn-octets fn-ninep-session) :guard t :verify-guards nil))
 (let* ((cursor (fn-9p-metadata-at 1 dispatch))
        (slot (fn-9p-metadata-at 2 dispatch))
        (kind (fn-9p-metadata-at 1 cursor)) (tag (fn-9p-metadata-at 2 cursor))
        (values (fn-9p-metadata-at 6 cursor)) (fid (fn-9p-metadata-at 0 values))
        (msize (fn-9ps-msize fn-ninep-session)))
  (cond
   ((not (and (eq (fn-9p-metadata-at 0 dispatch) :ninep-dispatch)
               (eq (fn-9p-metadata-at 0 cursor) :ninep-fields)
               (member-eq (fn-9p-metadata-at 9 cursor) '(:parsed :readonly))
               (natp slot)))
    (mv '(:close :invalid-dispatch) dispatch fn-ninep-session))
   ((equal kind 100)
    (mv-let (answer fn-ninep-session)
     (fn-9ps-version-at server-msize cursor fn-octets fn-ninep-session)
     (mv answer dispatch fn-ninep-session)))
   ((not (eq (fn-9ps-phase fn-ninep-session) :base))
    (mv '(:close :version-required) dispatch fn-ninep-session))
   ((not (and (natp tag) (< tag 65535)))
    (mv '(:close :invalid-tag) dispatch fn-ninep-session))
   ((equal kind 108)
    (mv-let (word found next-slot) (fn-9ps-find-tag-step fid slot fn-ninep-session)
     (cond ((eq word :yield)
            (mv '(:yield) (list :ninep-dispatch cursor next-slot) fn-ninep-session))
           ((member-eq word '(:found :missing))
            (mv-let (answer fn-ninep-session)
             (fn-9ps-flush-at tag fid found fn-ninep-session)
             (mv answer dispatch fn-ninep-session)))
           (t (mv '(:close :invalid-flush) dispatch fn-ninep-session)))))
   ((equal kind 102)
    (mv (fn-9p-refusal-reply msize tag :no-authentication) dispatch fn-ninep-session))
   ((fn-9p-readonly-kindp kind)
    (mv (fn-9p-refusal-reply msize tag :read-only) dispatch fn-ninep-session))
   ((equal kind 104)
    ; Actual mount operation entry is fn-ninep-mount-acquire. Missing family
    ; cannot fall back to a source-shaped tuple, latest pointer, or host tree.
    (if (equal (fn-9p-metadata-at 1 values) 4294967295)
        (mv (list :mount-acquire fid) dispatch fn-ninep-session)
      (mv (fn-9p-refusal-reply msize tag :no-authentication) dispatch fn-ninep-session)))
   ((member-equal kind '(110 112 116 120 124))
    (mv-let (word found next-slot) (fn-9ps-find-fid-step fid slot fn-ninep-session)
     (cond ((eq word :yield)
            (mv '(:yield) (list :ninep-dispatch cursor next-slot) fn-ninep-session))
           ((not (eq word :found))
            (mv (fn-9p-error-reply msize tag :unknown-fid) dispatch fn-ninep-session))
           ((equal kind 120)
            (mv-let (word fn-ninep-session) (fn-9ps-clunk-at fid found fn-ninep-session)
             (if (eq word :clunking)
                 (mv (fn-9p-empty-reply msize tag 121) dispatch fn-ninep-session)
               (mv (fn-9p-error-reply msize tag :unknown-fid) dispatch fn-ninep-session))))
           ((and (equal kind 112) (not (equal (fn-9p-metadata-at 1 values) 0)))
            (mv (fn-9p-refusal-reply msize tag :read-only) dispatch fn-ninep-session))
           (t
            ; Issued selected-query/QPG and stat/name producers are still
            ; missing. Do not synthesize article bytes, qids or tree entries.
            (mv (fn-9p-error-reply msize tag :provider-unavailable) dispatch fn-ninep-session)))))
   (t (mv '(:close :unsupported-message) dispatch fn-ninep-session)))))

(verify-guards fn-9p-dispatch-step)

(defthm fn-9p-error-reply-fits-negotiated-message
 (implies (equal (car (fn-9p-error-reply msize tag reason)) :refused)
  (<= (len (caddr (fn-9p-error-reply msize tag reason))) msize)))
