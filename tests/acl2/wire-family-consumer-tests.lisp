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
(include-book "../../books/defkeystone")

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

; ---------------------------------------------------------------------------
; The agreement keystones with their teeth (TEETH CONTRACT v1).  Each decoder
; keystone's only hypothesis is the octet-list type, which no decoder
; answer depends on (a non-octet list is refused by both sides), so the claim
; keeps it inside the implication and the teeth are two conclusion
; mutations: a wrong value, and a decoder that accepts trailing octets.  Each
; encoder keystone's hypothesis (the encoder answers) is removed at an input
; the encoder refuses, where the conclusion fails: the refused input has no
; grammar value.
(defconst *wfcs-status-good* (fn-ncl-status-reply-encode :accepted 3 10 7))

(defteeth fn-wf-cs-status-decode-agrees
  :claim (() (implies (fn-cbor-octet-listp x)
                      (let ((r (fn-ncl-status-reply-decode x))
                            (w (fn-wg-decode *fn-wf-cs-status-reply-grammar* x)))
                        (and (iff (equal (car r) :consumer-status-reply)
                                  (and (fn-wg-okp w) (null (fn-wg-rest w))))
                             (implies (equal (car r) :consumer-status-reply)
                                      (equal (fn-wg-value w)
                                             (fn-wf-cs-status-value (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r))))))))
  :subject fn-ncl-status-reply-decode
  :witness ((x *wfcs-status-good*))
  :mutations ((value-skewed
               (:conclusion (implies (fn-cbor-octet-listp x)
                             (let ((r (fn-ncl-status-reply-decode x))
                                   (w (fn-wg-decode *fn-wf-cs-status-reply-grammar* x)))
                               (and (iff (equal (car r) :consumer-status-reply)
                                         (and (fn-wg-okp w) (null (fn-wg-rest w))))
                                    (implies (equal (car r) :consumer-status-reply)
                                             (equal (fn-wg-value w)
                                                    (fn-wf-cs-status-value (nth 1 r) (nth 3 r) (nth 2 r) (nth 4 r))))))))
               ((x *wfcs-status-good*))
               :fault "a decoder that reads the frontier as the ack and the ack as the frontier")
              (trailing-octets-accepted
               (:conclusion (implies (fn-cbor-octet-listp x)
                             (let ((r (fn-ncl-status-reply-decode x))
                                   (w (fn-wg-decode *fn-wf-cs-status-reply-grammar* x)))
                               (and (iff (equal (car r) :consumer-status-reply)
                                         (fn-wg-okp w))
                                    (implies (equal (car r) :consumer-status-reply)
                                             (equal (fn-wg-value w)
                                                    (fn-wf-cs-status-value (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r))))))))
               ((x (append *wfcs-status-good* '(0))))
               :fault "a decoder that accepts a frame followed by a trailing octet")))

(defconst *wfcs-cursor*
  (fn-cp-cursor-encode (list :cursor '(1) '(2) '(3) '(4) '(5) 0 0 1 7)))
(defconst *wfcs-reply-good* (fn-ncl-reply-encode :accepted *wfcs-cursor*))
(defconst *wfcs-request-good* (fn-cwait-request-encode :register '(1) '(2 3)))
(defconst *wfcs-reasoned-good* (fn-ncr-request-encode :register '(1) '(2 3)))

(defteeth fn-wf-cs-reply-encode-agrees
  :claim (((encodes (not (equal (fn-ncl-reply-encode status cursor) :bad))))
          (and (fn-wg-valuep *fn-wf-cs-reply-grammar* (fn-wf-cs-reply-value status cursor))
               (equal (fn-ncl-reply-encode status cursor)
                      (fn-wg-encode *fn-wf-cs-reply-grammar* (fn-wf-cs-reply-value status cursor)))))
  :subject fn-ncl-reply-encode
  :witness ((status :accepted) (cursor *wfcs-cursor*))
  :breaks ((encodes ((status :refused) (cursor *wfcs-cursor*))))
  :mutations ((encodes-the-fault-reply
               (:conclusion (and (fn-wg-valuep *fn-wf-cs-reply-grammar* (fn-wf-cs-reply-value status cursor))
                                 (equal (fn-ncl-reply-encode status cursor)
                                        (fn-wg-encode *fn-wf-cs-reply-grammar* (fn-wf-cs-reply-value :fault nil)))))
               ((status :accepted) (cursor *wfcs-cursor*))
               :fault "an encoder that answers every status with the fault frame")))

(defteeth fn-wf-cs-reply-decode-agrees
  :claim (() (implies (fn-cbor-octet-listp x)
                      (let ((r (fn-ncl-reply-decode x))
                            (w (fn-wg-decode *fn-wf-cs-reply-grammar* x)))
                        (and (iff (equal (car r) :consumer-reply)
                                  (and (fn-wg-okp w) (null (fn-wg-rest w))))
                             (implies (equal (car r) :consumer-reply)
                                      (equal (fn-wg-value w) (fn-wf-cs-reply-value (nth 1 r) (nth 2 r))))))))
  :subject fn-ncl-reply-decode
  :witness ((x *wfcs-reply-good*))
  :mutations ((status-dropped
               (:conclusion (implies (fn-cbor-octet-listp x)
                             (let ((r (fn-ncl-reply-decode x))
                                   (w (fn-wg-decode *fn-wf-cs-reply-grammar* x)))
                               (and (iff (equal (car r) :consumer-reply)
                                         (and (fn-wg-okp w) (null (fn-wg-rest w))))
                                    (implies (equal (car r) :consumer-reply)
                                             (equal (fn-wg-value w) (fn-wf-cs-reply-value :refused (nth 2 r))))))))
               ((x *wfcs-reply-good*))
               :fault "a decoder that reports every reply as refused")
              (trailing-octets-accepted
               (:conclusion (implies (fn-cbor-octet-listp x)
                             (let ((r (fn-ncl-reply-decode x))
                                   (w (fn-wg-decode *fn-wf-cs-reply-grammar* x)))
                               (and (iff (equal (car r) :consumer-reply) (fn-wg-okp w))
                                    (implies (equal (car r) :consumer-reply)
                                             (equal (fn-wg-value w) (fn-wf-cs-reply-value (nth 1 r) (nth 2 r))))))))
               ((x (append *wfcs-reply-good* '(0))))
               :fault "a decoder that accepts a frame followed by a trailing octet")))

(defteeth fn-wf-cs-request-decode-agrees
  :claim (() (implies (fn-cbor-octet-listp x)
                      (let ((r (fn-cwait-request-decode x))
                            (w (fn-wg-decode *fn-wf-cs-request-grammar* x)))
                        (and (iff (equal (car r) :consumer)
                                  (and (fn-wg-okp w) (null (fn-wg-rest w))))
                             (implies (equal (car r) :consumer)
                                      (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 r) (nth 2 r) (nth 3 r))))))))
  :subject fn-cwait-request-decode
  :witness ((x *wfcs-request-good*))
  :mutations ((fields-swapped
               (:conclusion (implies (fn-cbor-octet-listp x)
                             (let ((r (fn-cwait-request-decode x))
                                   (w (fn-wg-decode *fn-wf-cs-request-grammar* x)))
                               (and (iff (equal (car r) :consumer)
                                         (and (fn-wg-okp w) (null (fn-wg-rest w))))
                                    (implies (equal (car r) :consumer)
                                             (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 r) (nth 3 r) (nth 2 r))))))))
               ((x *wfcs-request-good*))
               :fault "a decoder that reads the group id as the consumer id and the consumer id as the group id")
              (trailing-octets-accepted
               (:conclusion (implies (fn-cbor-octet-listp x)
                             (let ((r (fn-cwait-request-decode x))
                                   (w (fn-wg-decode *fn-wf-cs-request-grammar* x)))
                               (and (iff (equal (car r) :consumer) (fn-wg-okp w))
                                    (implies (equal (car r) :consumer)
                                             (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 r) (nth 2 r) (nth 3 r))))))))
               ((x (append *wfcs-request-good* '(0))))
               :fault "a decoder that accepts a frame followed by a trailing octet")))

(defteeth fn-wf-cs-request-encode-agrees
  :claim (((encodes (not (equal (fn-cwait-request-encode kind first second) :bad))))
          (and (fn-wg-valuep *fn-wf-cs-request-grammar* (fn-wf-cs-request-value kind first second))
               (equal (fn-cwait-request-encode kind first second)
                      (fn-wg-encode *fn-wf-cs-request-grammar* (fn-wf-cs-request-value kind first second)))))
  :subject fn-cwait-request-encode
  :witness ((kind :register) (first '(1)) (second '(2 3)))
  :breaks ((encodes ((kind :wait) (first '(7)) (second 3601))))
  :mutations ((encodes-the-status-request
               (:conclusion (and (fn-wg-valuep *fn-wf-cs-request-grammar* (fn-wf-cs-request-value kind first second))
                                 (equal (fn-cwait-request-encode kind first second)
                                        (fn-wg-encode *fn-wf-cs-request-grammar*
                                                      (fn-wf-cs-request-value :position first nil)))))
               ((kind :register) (first '(1)) (second '(2 3)))
               :fault "an encoder that answers every command with the position request")))

(defteeth fn-wf-cs-reasoned-request-decode-agrees
  :claim (() (implies (fn-cbor-octet-listp x)
                      (let ((r (fn-ncr-request-decode x))
                            (w (fn-wg-decode *fn-wf-cs-reasoned-request-grammar* x)))
                        (and (iff (equal (car r) :consumer)
                                  (and (fn-wg-okp w) (null (fn-wg-rest w))))
                             (implies (equal (car r) :consumer)
                                      (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 r) (nth 2 r) (nth 3 r))))))))
  :subject fn-ncr-request-decode
  :witness ((x *wfcs-reasoned-good*))
  :mutations ((fields-swapped
               (:conclusion (implies (fn-cbor-octet-listp x)
                             (let ((r (fn-ncr-request-decode x))
                                   (w (fn-wg-decode *fn-wf-cs-reasoned-request-grammar* x)))
                               (and (iff (equal (car r) :consumer)
                                         (and (fn-wg-okp w) (null (fn-wg-rest w))))
                                    (implies (equal (car r) :consumer)
                                             (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 r) (nth 3 r) (nth 2 r))))))))
               ((x *wfcs-reasoned-good*))
               :fault "a decoder that reads the group id as the consumer id and the consumer id as the group id")
              (trailing-octets-accepted
               (:conclusion (implies (fn-cbor-octet-listp x)
                             (let ((r (fn-ncr-request-decode x))
                                   (w (fn-wg-decode *fn-wf-cs-reasoned-request-grammar* x)))
                               (and (iff (equal (car r) :consumer) (fn-wg-okp w))
                                    (implies (equal (car r) :consumer)
                                             (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 r) (nth 2 r) (nth 3 r))))))))
               ((x (append *wfcs-reasoned-good* '(0))))
               :fault "a decoder that accepts a frame followed by a trailing octet")))

(defteeth fn-wf-cs-reasoned-request-encode-agrees
  :claim (((encodes (not (equal (fn-ncr-request-encode kind first second) :bad))))
          (and (fn-wg-valuep *fn-wf-cs-reasoned-request-grammar* (fn-wf-cs-request-value kind first second))
               (equal (fn-ncr-request-encode kind first second)
                      (fn-wg-encode *fn-wf-cs-reasoned-request-grammar*
                                    (fn-wf-cs-request-value kind first second)))))
  :subject fn-ncr-request-encode
  :witness ((kind :register) (first '(1)) (second '(2 3)))
  :breaks ((encodes ((kind :wait) (first '(7)) (second 3601))))
  :mutations ((encodes-the-position-request
               (:conclusion (and (fn-wg-valuep *fn-wf-cs-reasoned-request-grammar* (fn-wf-cs-request-value kind first second))
                                 (equal (fn-ncr-request-encode kind first second)
                                        (fn-wg-encode *fn-wf-cs-reasoned-request-grammar*
                                                      (fn-wf-cs-request-value :position first nil)))))
               ((kind :register) (first '(1)) (second '(2 3)))
               :fault "an encoder that answers every command with the position request")))
