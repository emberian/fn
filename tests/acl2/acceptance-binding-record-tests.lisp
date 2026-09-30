; Literal mandatory current-format binding fixtures, source codec only.
(in-package "ACL2")
(include-book "../../books/records-canonicality")
(include-book "../../books/crypto-attach")
(defconst *abrt-received* '(65 13 10))
; Explicit abstract fixture descriptor; production never substitutes it.
(defconst *abrt-binding*
  (fn-ab-make :relay-v1 (fn-ab-received-subject *fn-record-golden-binding*)))
(defconst *abrt-record*
  (fn-record-make 1 2 3 "<binding@example.invalid>" '(66 13 10)
                  '("fn.test") "o" "stored-subject" "e" 4 5 *abrt-binding*))
(assert-event (and (fn-record-p *abrt-record*)
                   (fn-ab-p *abrt-binding*)
                   (equal (fn-record-binding *abrt-record*) *abrt-binding*)
                   (equal (fn-record-decode-exact-impl
                           (fn-record-encode-impl *abrt-record*))
                          (list :ok *abrt-record*))))
(assert-event
 (let ((w (fn-record-encode-impl *abrt-record*)))
   (and (equal (car (fn-record-decode-exact-impl w)) :ok)
        (equal (fn-record-encode-impl
                (cadr (fn-record-decode-exact-impl w))) w))))
; Received and stored payload commitments are distinct.
(assert-event
 (not (equal (fn-id-subject-of-payload *abrt-received*)
             (fn-id-subject-of-payload (fn-record-payload *abrt-record*)))))
(assert-event (equal (len (fn-ab-encode *abrt-binding*)) 56))
(assert-event
 (equal (fn-ab-decode (fn-ab-encode *abrt-binding*)) (list :ok *abrt-binding*)))
(assert-event (fn-ab-p (fn-ab-for-received :post-d25 *abrt-received*)))
(assert-event (fn-ab-p (fn-ab-for-received :native-source *abrt-received*)))
; Corrupted-state witnesses: never fill a missing field or infer a profile.
(assert-event (not (fn-record-p (take 11 *abrt-record*))))
(assert-event (equal (fn-record-encode-impl (take 11 *abrt-record*)) nil))
(assert-event (equal (fn-ab-for-received :unknown *abrt-received*) nil))
(assert-event (equal (fn-ab-for-received :relay-v1 '(256)) nil))
(assert-event (equal (fn-ab-decode nil) '(:error :invalid-binding)))
(assert-event
 (equal (fn-ab-decode (update-nth 7 0 (fn-ab-encode *abrt-binding*)))
        '(:error :invalid-binding)))
(assert-event
 (equal (fn-ab-decode (append (fn-ab-encode *abrt-binding*) '(0)))
        '(:error :invalid-binding)))
; Missing binary descriptor: same current schema, entire descriptor cut.
(assert-event
 (let* ((w (fn-record-encode-impl *abrt-record*))
        (missing (take (- (len w) 58) w)))
   (equal (fn-record-decode-exact-impl missing) '(:error :invalid-binding))))
; Old schema is refused even with the otherwise complete current tuple.
(assert-event
 (equal (fn-record-decode-exact-impl
         (update-nth 5 1 (fn-record-encode-impl *abrt-record*)))
        '(:error :unknown-version)))
