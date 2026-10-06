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

; fnct.consumer.request (kind 4, the wait codec the host calls) and kind 22:
; every command's host encoding is the grammar's, both decoders accept it
; with the same value; a timeout past 3600 and an empty id are refused by
; both, and the encoder refuses them (:bad).
(defun wfcs-request-agrees (kind first second)
  (let* ((x (fn-cwait-request-encode kind first second))
         (y (fn-ncr-request-encode kind first second))
         (v (fn-wf-cs-request-value kind first second))
         (r (fn-cwait-request-decode x)))
    (and (not (equal x :bad)) (not (equal y :bad))
         (equal x (fn-wg-encode *fn-wf-cs-request-grammar* v))
         (equal y (fn-wg-encode *fn-wf-cs-reasoned-request-grammar* v))
         (equal (car r) :consumer)
         (equal (fn-wg-decode *fn-wf-cs-request-grammar* x) (fn-wg-ok v nil))
         (equal (fn-wg-decode *fn-wf-cs-reasoned-request-grammar* y) (fn-wg-ok v nil))
         (equal (fn-ncr-request-decode y) r)
         (equal v (fn-wf-cs-request-value (nth 1 r) (nth 2 r) (nth 3 r))))))

(assert-event
 (let ((cursor (fn-cp-cursor-encode
                (list :cursor '(1) '(2) '(3) '(4) '(5) 0 0 1 7))))
   (and (wfcs-request-agrees :register '(1) '(2 3))
        (wfcs-request-agrees :ack cursor nil)
        (wfcs-request-agrees :position '(7) nil)
        (wfcs-request-agrees :bootstrap nil nil)
        (wfcs-request-agrees :status (make-list 64 :initial-element 9) nil)
        (wfcs-request-agrees :bound-poll '(7) '(115 101 99))
        (wfcs-request-agrees :bound-ack cursor (make-list 496 :initial-element 5))
        (wfcs-request-agrees :wait '(7) 3600)
        (wfcs-request-agrees :bound-wait '(7) (list 0 '(115 101 99))))))

(assert-event
 (let ((past (fn-wg-encode *fn-wf-cs-request-grammar* '(:wait ((7) 3601))))
       (empty (fn-wg-encode *fn-wf-cs-request-grammar* '(:position (nil)))))
   (and (equal (fn-cwait-request-encode :wait '(7) 3601) :bad)
        (equal (fn-cwait-request-encode :position nil nil) :bad)
        (not (equal (car (fn-cwait-request-decode past)) :consumer))
        (not (equal (car (fn-cwait-request-decode empty)) :consumer))
        (not (fn-wg-okp (fn-wg-decode *fn-wf-cs-request-grammar* past)))
        (not (fn-wg-okp (fn-wg-decode *fn-wf-cs-request-grammar* empty))))))

; fnct.consumer.reply (kind 5): with and without a cursor, every status.
(defun wfcs-reply-agrees (status cursor)
  (let* ((x (fn-ncl-reply-encode status cursor))
         (v (fn-wf-cs-reply-value status cursor)))
    (and (not (equal x :bad))
         (equal x (fn-wg-encode *fn-wf-cs-reply-grammar* v))
         (equal (fn-ncl-reply-decode x) (list :consumer-reply status cursor))
         (equal (fn-wg-decode *fn-wf-cs-reply-grammar* x) (fn-wg-ok v nil)))))

(assert-event
 (let ((cursor (fn-cp-cursor-encode
                (list :cursor '(1) '(2) '(3) '(4) '(5) 0 0 1 7))))
   (and (wfcs-reply-agrees :accepted cursor)
        (wfcs-reply-agrees :accepted nil)
        (wfcs-reply-agrees :refused nil)
        (wfcs-reply-agrees :uncertain nil)
        (wfcs-reply-agrees :fault nil)
        (equal (fn-ncl-reply-encode :refused cursor) :bad))))
