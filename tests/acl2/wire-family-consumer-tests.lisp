; Teeth for books/wire-family-consumer (fnct.consumer.status-reply) and the
; frame half in books/wire-family-fnct.
;
; Positive: every arm (accepted at both uint32 bounds, refused, uncertain,
; fault): the host's encoding is the grammar's, both decoders accept it
; whole, and the host's answer is the grammar's value under
; fn-wf-cs-status-value.  Agreement on refusals: an ack past the frontier
; and a wrong distance (the two `where' checks), a flipped trailer octet, a
; trailing octet and the wrong FNCT kind are refused by both decoders; the
; encoder refuses the first two outright (:bad), so
; fn-wf-cs-status-encode-agrees' hypothesis is not vacuous.
(in-package "ACL2")
(include-book "../../books/wire-family-consumer")

(defun wfcs-agree-on-accept (status ack frontier gap)
  (let* ((x (fn-ncl-status-reply-encode status ack frontier gap))
         (v (fn-wf-cs-status-value status ack frontier gap))
         (r (fn-ncl-status-reply-decode x))
         (w (fn-wg-decode *fn-wf-cs-status-reply-grammar* x)))
    (and (not (equal x :bad))
         (equal x (fn-wg-encode *fn-wf-cs-status-reply-grammar* v))
         (equal r (list :consumer-status-reply status ack frontier gap))
         (equal w (fn-wg-ok v nil)))))

(assert-event
 (and (wfcs-agree-on-accept :accepted 3 10 7)
      (wfcs-agree-on-accept :accepted 0 4294967295 4294967295)
      (wfcs-agree-on-accept :accepted 4294967295 4294967295 0)
      (wfcs-agree-on-accept :refused nil nil nil)
      (wfcs-agree-on-accept :uncertain nil nil nil)
      (wfcs-agree-on-accept :fault nil nil nil)))

(defun wfcs-both-refuse (x)
  (and (equal (car (fn-ncl-status-reply-decode x)) :refused)
       (not (and (fn-wg-okp (fn-wg-decode *fn-wf-cs-status-reply-grammar* x))
                 (null (fn-wg-rest (fn-wg-decode *fn-wf-cs-status-reply-grammar* x)))))))

(assert-event
 (let* ((good (fn-ncl-status-reply-encode :accepted 3 10 7))
        (past (fn-wg-encode *fn-wf-cs-status-reply-grammar* '(:accepted (11 10 1))))
        (dist (fn-wg-encode *fn-wf-cs-status-reply-grammar* '(:accepted (3 10 6))))
        (kind (fn-wg-encode (list :frame '(70 78 67 84) 1 5 13 *fn-wf-cs-status-payload*)
                            '(:accepted (3 10 7)))))
   (and (equal (fn-ncl-status-reply-encode :accepted 11 10 1) :bad)
        (equal (fn-ncl-status-reply-encode :accepted 3 10 6) :bad)
        (equal (fn-wg-decode *fn-wf-cs-status-reply-grammar* past) (fn-wg-refused :where))
        (equal (fn-wg-decode *fn-wf-cs-status-reply-grammar* dist) (fn-wg-refused :where))
        (wfcs-both-refuse past)
        (wfcs-both-refuse dist)
        (wfcs-both-refuse (update-nth (1- (len good)) (logxor 1 (car (last good))) good))
        (wfcs-both-refuse (append good '(0)))
        (wfcs-both-refuse kind))))
