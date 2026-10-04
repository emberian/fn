; Teeth for books/wire-family-fncu.
;
; Positive: a cursor whose fields sit at both bounds (a 1-octet and a
; 64-octet id, epoch 1, position 2^32-1): the host encodes it to the
; grammar's octets, both decoders accept them whole with the same cursor,
; and fn-cp-cursor-encode-decode-roundtrip's antecedent and conclusion hold.
; Hypothesis witness for fn-cp-cursor-encode-decode-roundtrip: octets the
; host refuses (epoch 0) -- the conclusion fails.  Agreement on refusals:
; a wrong version octet, a trailing octet and an id of 65 octets are refused
; by both decoders.
(in-package "ACL2")
(include-book "../../books/wire-family-fncu")

(defconst *wfct-cursor*
  (list :cursor '(1) (make-list 64 :initial-element 7) '(2 3) '(4) '(5 6 7)
        0 9 1 4294967295))

(assert-event
 (let* ((c *wfct-cursor*) (x (fn-cp-cursor-encode c))
        (w (fn-wg-decode *fn-wf-fncu-grammar* x)))
   (and (fn-cp-cursorp c)
        (equal x (fn-wg-encode *fn-wf-fncu-grammar* (fn-wf-fncu-value c)))
        (equal (fn-cp-cursor-decode x) (list :ok c))
        (fn-wg-okp w) (null (fn-wg-rest w))
        (equal (fn-wf-fncu-cursor (fn-wg-value w)) c)
        (equal (car (fn-cp-cursor-decode x)) :ok)
        (equal (fn-cp-cursor-encode (cadr (fn-cp-cursor-decode x))) x))))

; Epoch 0 (field 8) is refused by both; the round trip's conclusion fails.
(assert-event
 (let* ((x (update-nth (- (len (fn-cp-cursor-encode *wfct-cursor*)) 5) 0
                       (update-nth (- (len (fn-cp-cursor-encode *wfct-cursor*)) 6) 0
                                   (update-nth (- (len (fn-cp-cursor-encode *wfct-cursor*)) 7) 0
                                               (update-nth (- (len (fn-cp-cursor-encode *wfct-cursor*)) 8) 0
                                                           (fn-cp-cursor-encode *wfct-cursor*)))))))
   (and (fn-cbor-octet-listp x)
        (not (equal (car (fn-cp-cursor-decode x)) :ok))
        (not (fn-wg-okp (fn-wg-decode *fn-wf-fncu-grammar* x)))
        (not (equal (fn-cp-cursor-encode (cadr (fn-cp-cursor-decode x))) x)))))

; Refusals agree.
(assert-event
 (let* ((x (fn-cp-cursor-encode *wfct-cursor*))
        (bad-version (update-nth 4 2 x))
        (trailing (append x '(0)))
        (long-id (fn-cp-cursor-encode
                  (list :cursor (make-list 65 :initial-element 1) '(1) '(1) '(1) '(1) 0 0 1 0))))
   (and (null long-id)
        (not (equal (car (fn-cp-cursor-decode bad-version)) :ok))
        (not (fn-wg-okp (fn-wg-decode *fn-wf-fncu-grammar* bad-version)))
        (not (equal (car (fn-cp-cursor-decode trailing)) :ok))
        (fn-wg-okp (fn-wg-decode *fn-wf-fncu-grammar* trailing))
        (consp (fn-wg-rest (fn-wg-decode *fn-wf-fncu-grammar* trailing))))))
