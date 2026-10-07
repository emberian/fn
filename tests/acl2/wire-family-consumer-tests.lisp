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

; fnct.consumer.poll-reply (kind 6): every status, accepted with an empty and
; a non-empty report.  The host's encoding is the grammar's, both decoders
; accept it whole, and the host's answer is the grammar's value under
; fn-wf-cs-poll-value.  Negatives, each refused by both decoders: a cursor
; length past 346, one under 31 (the :sized bounds), a report length that
; is not the octets present, an inner cursor the cursor grammar refuses, a
; non-accepted status carrying a cursor, and the wrong FNCT kind; the encoder
; refuses a cursor that does not decode and a status with a cursor (:bad), so
; fn-wf-cs-poll-encode-agrees' hypothesis is not vacuous.
(defun wfcp-agrees (status cursor report)
  (let* ((x (fn-ncl-poll-reply-encode status cursor report))
         (v (fn-wf-cs-poll-value status cursor report))
         (w (fn-wg-decode *fn-wf-cs-poll-reply-grammar* x)))
    (and (not (equal x :bad))
         (equal x (fn-wg-encode *fn-wf-cs-poll-reply-grammar* v))
         (equal (fn-ncl-poll-reply-decode x) (list :consumer-poll-reply status cursor report))
         (equal w (fn-wg-ok v nil)))))

(defun wfcp-both-refuse (x)
  (and (equal (car (fn-ncl-poll-reply-decode x)) :refused)
       (not (and (fn-wg-okp (fn-wg-decode *fn-wf-cs-poll-reply-grammar* x))
                 (null (fn-wg-rest (fn-wg-decode *fn-wf-cs-poll-reply-grammar* x)))))))

(defun wfcp-seal (payload)
  (fn-ncl-poll-seal payload))

(assert-event
 (let ((cursor (fn-cp-cursor-encode
                (list :cursor '(1) '(2) '(3) '(4) '(5) 0 0 1 7))))
   (and (wfcp-agrees :accepted cursor nil)
        (wfcp-agrees :accepted cursor '(1 2 3 4 5 6 7 8))
        (wfcp-agrees :accepted cursor (make-list 1000 :initial-element 9))
        (wfcp-agrees :refused nil nil)
        (wfcp-agrees :uncertain nil nil)
        (wfcp-agrees :fault nil nil)
        (equal (fn-ncl-poll-reply-encode :accepted '(1 2 3) nil) :bad)
        (equal (fn-ncl-poll-reply-encode :refused cursor nil) :bad)
        (equal (fn-ncl-poll-reply-encode :refused nil '(1)) :bad))))

(assert-event
 (let* ((cursor (fn-cp-cursor-encode
                 (list :cursor '(1) '(2) '(3) '(4) '(5) 0 0 1 7)))
        (zero8 '(0 0 0 0 0 0 0 0))
        (good (fn-ncl-poll-reply-encode :accepted cursor '(1 2 3)))
        (kind (fn-wg-encode (list :frame '(70 78 67 84) 1 5 *fn-ncl-poll-max-payload*
                                  *fn-wf-cs-poll-payload*)
                            (fn-wf-cs-poll-value :accepted cursor '(1 2 3))))
        ; a cursor length one past the cursor's octets: the :sized node reads
        ; one octet of the report as cursor, the cursor grammar leaves it over
        (long (wfcp-seal (append '(0) (fn-cbor-u32-bytes (+ 1 (len cursor))) cursor
                                 (fn-cbor-u32-bytes 3) '(1 2 3))))
        ; a cursor length past 346 octets, and one under 31
        (past (wfcp-seal (append '(0) (fn-cbor-u32-bytes 347) (make-list 347 :initial-element 1)
                                 (fn-cbor-u32-bytes 0))))
        (under (wfcp-seal (append '(0) (fn-cbor-u32-bytes 30) (make-list 30 :initial-element 1)
                                  (fn-cbor-u32-bytes 0))))
        ; a report length that is not the octets present
        (short (wfcp-seal (append '(0) (fn-cbor-u32-bytes (len cursor)) cursor
                                  (fn-cbor-u32-bytes 4) '(1 2 3))))
        (extra (wfcp-seal (append '(0) (fn-cbor-u32-bytes (len cursor)) cursor
                                  (fn-cbor-u32-bytes 2) '(1 2 3))))
        ; a refused status that carries a cursor
        (carry (wfcp-seal (append '(1) (fn-cbor-u32-bytes (len cursor)) cursor
                                  (fn-cbor-u32-bytes 0)))))
   (and (not (equal good :bad))
        (wfcp-both-refuse long)
        (wfcp-both-refuse past)
        (wfcp-both-refuse under)
        (wfcp-both-refuse short)
        (wfcp-both-refuse extra)
        (wfcp-both-refuse carry)
        (wfcp-both-refuse kind)
        (wfcp-both-refuse (update-nth (1- (len good)) (logxor 1 (car (last good))) good))
        (wfcp-both-refuse (append good '(0)))
        (equal (fn-wg-decode *fn-wf-cs-poll-reply-grammar*
                             (wfcp-seal (append '(1) zero8)))
               (fn-wg-ok '(:refused nil) nil)))))
