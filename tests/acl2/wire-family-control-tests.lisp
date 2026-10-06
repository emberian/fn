; Teeth for books/wire-family-control (fnct.reasoned-reply, kind 18, and
; fnct.line-reply, kind 23).
;
; Positive: refused, uncertain and accepted replies with a named reason and
; with NONE: the host's encoding is the grammar's and both decoders accept it
; with the same value.  Agreement on refusals: an empty reason, a reason past
; 512 octets, an unknown status code, a trailing octet and the wrong kind are
; refused by both.  A lined reply without a line is sent as kind 18, which
; the kind-23 grammar refuses.
(in-package "ACL2")
(include-book "../../books/wire-family-control")

(defun wfctl-reasoned-agrees (status reason)
  (let* ((x (fn-native-control-reasoned-reply-encode status reason))
         (v (list status (fn-nctrl-reason-word reason))))
    (and (not (equal x :bad))
         (equal x (fn-wg-encode *fn-wf-ctl-reasoned-reply-grammar* v))
         (equal (fn-nctrl-reasoned-reply-payload-decode (fn-nctrl-open x 18)) v)
         (equal (fn-wg-decode *fn-wf-ctl-reasoned-reply-grammar* x) (fn-wg-ok v nil)))))

(defun wfctl-lined-agrees (status reason line)
  (let* ((x (fn-native-control-lined-reply-encode status reason line))
         (v (list status (fn-nctrl-reason-word reason) (fn-ncline-line line))))
    (and (not (equal x :bad))
         (equal x (fn-wg-encode *fn-wf-ctl-lined-reply-grammar* v))
         (equal (fn-ncline-reply-payload-decode (fn-nctrl-open x 23)) v)
         (equal (fn-wg-decode *fn-wf-ctl-lined-reply-grammar* x) (fn-wg-ok v nil)))))

(assert-event
 (and (wfctl-reasoned-agrees :refused :no-owner)
      (wfctl-reasoned-agrees :uncertain nil)
      (wfctl-reasoned-agrees :accepted nil)
      (wfctl-lined-agrees :accepted nil "applied: max-connections 64")
      (wfctl-lined-agrees :refused :limit-exceeds-profile "x")))

(defun wfctl-both-refuse-18 (x)
  (and (equal (fn-nctrl-reasoned-reply-payload-decode (fn-nctrl-open x 18)) :bad)
       (not (and (fn-wg-okp (fn-wg-decode *fn-wf-ctl-reasoned-reply-grammar* x))
                 (null (fn-wg-rest (fn-wg-decode *fn-wf-ctl-reasoned-reply-grammar* x)))))))

(assert-event
 (let ((good (fn-native-control-reasoned-reply-encode :refused :no-owner)))
   (and (wfctl-both-refuse-18 (fn-wg-encode *fn-wf-ctl-reasoned-reply-grammar* '(:refused nil)))
        (wfctl-both-refuse-18 (fn-wg-encode *fn-wf-ctl-reasoned-reply-grammar*
                                            (list :refused (make-list 513 :initial-element 97))))
        (wfctl-both-refuse-18 (fn-nctrl-seal 18 (list 99 0 0 0 1 97)))
        (wfctl-both-refuse-18 (append good '(0)))
        (wfctl-both-refuse-18 (fn-nctrl-seal 23 (list 3 0 0 0 1 97)))
        ; no line: kind 18, refused by the kind-23 grammar
        (not (fn-wg-okp (fn-wg-decode *fn-wf-ctl-lined-reply-grammar*
                                      (fn-native-control-lined-reply-encode :refused :no-owner nil)))))))
