; Core-owned fixed base9P2000 refusal wire replies. No mount authorization.
(in-package "ACL2")
(include-book "ninep-version")

(defun fn-9p-refusal-text (reason)
 (declare (xargs :guard t))
 (case reason
  (:read-only '(114 101 97 100 32 111 110 108 121))
  (:no-authentication '(110 111 32 97 117 116 104 101 110 116 105 99 97 116 105 111 110))
  (:mount-unavailable '(109 111 117 110 116 32 117 110 97 118 97 105 108 97 98 108 101))
  (otherwise nil)))

; The caller supplies a core refusal outcome, never rendered host text.
; NOTAG belongs to Version and cannot label this Rerror.
(defun fn-9p-refusal-reply (msize tag reason)
 (declare (xargs :guard t))
 (let* ((text (fn-9p-refusal-text reason)) (size (+ 9 (len text))))
  (cond ((not (and (fn-9p-profile-msizep msize) (natp tag) (< tag 65535)
                   (consp text))) '(:close :invalid-refusal))
        ((< msize size) '(:close :msize-too-small))
        (t (list :refused reason
             (append (fn-9p-u32-octets size) (list 107)
                     (fn-9p-u16-octets tag) (fn-9p-u16-octets (len text)) text))))))

(defthm fn-9p-refusal-reply-fits-negotiated-message
 (implies (equal (car (fn-9p-refusal-reply msize tag reason)) :refused)
  (and (<= (len (caddr (fn-9p-refusal-reply msize tag reason))) msize)
       (<= (len (caddr (fn-9p-refusal-reply msize tag reason))) 26)))
 :hints (("Goal" :in-theory
          (enable fn-9p-refusal-reply fn-9p-refusal-text fn-9p-u16-octets
                  fn-9p-u32-octets fn-9p-profile-msizep))))
