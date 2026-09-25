; Teeth for books/records-concrete.lisp.
(in-package "ACL2")
(include-book "../../books/records-concrete")
(include-book "std/testing/must-fail" :dir :system)
(include-book "owner-served-invariants-tests")

; Reachable witness: the article record owner-served-invariants-tests'
; *osi-completing* is completing (reached by fn-own-run from owner-tests).
; Its Message-ID is 65 ASCII characters, its payload 328 octets, its three
; metadata strings 73, 77 and 77 characters.
(defconst *rcon-t-r*
  (car (last (fn-sf-records (fn-sn-files (fn-own-store *osi-completing*))))))
(assert-event (fn-record-p *rcon-t-r*))
(assert-event (fn-rcon-record-p *rcon-t-r*))
(assert-event (equal (length (fn-record-msgid *rcon-t-r*)) 65))
(assert-event (equal (len (fn-record-payload *rcon-t-r*)) 328))
(assert-event (equal (list (length (fn-record-obligation-id *rcon-t-r*))
                           (length (fn-record-content-subject *rcon-t-r*))
                           (length (fn-record-release-evidence *rcon-t-r*)))
                     '(73 77 77)))

; The twins on the witness, and on the non-records the dispatchers see.
(defconst *rcon-t-retention*
  (fn-store-retention-event-make :undertake 7 9 9
                                 (fn-record-obligation-id *rcon-t-r*)
                                 (fn-record-content-subject *rcon-t-r*)
                                 (fn-record-release-evidence *rcon-t-r*) 1))
(assert-event (fn-store-retention-event-p *rcon-t-retention*))
(assert-event
 (let ((xs (list *rcon-t-r* *rcon-t-retention* nil 5 "x" (list 1 2))))
   (and (equal (fn-rcon-store-event-p *rcon-t-r*) t)
        (equal (fn-rcon-store-event-p *rcon-t-retention*) t)
        (equal (fn-rcon-store-event-sequence *rcon-t-retention*) 7)
        (equal (fn-rcon-store-event-txid *rcon-t-retention*) 9)
        (equal (fn-rcon-sf-record-pair *rcon-t-r*)
               (cons (fn-record-sequence *rcon-t-r*) (fn-record-txid *rcon-t-r*)))
        (fn-rcon-sn-record-bindsp (fn-sn-node (fn-own-store *osi-completing*))
                                  *rcon-t-r*)
        (fn-sn-record-bindsp (fn-sn-node (fn-own-store *osi-completing*))
                             *rcon-t-r*)
        (equal (fn-rcon-th-prefix-step (fn-sn-topic (fn-own-store *osi-completing*))
                                       *rcon-t-r*)
               (fn-th-prefix-step (fn-sn-topic (fn-own-store *osi-completing*))
                                  *rcon-t-r*))
        (equal (fn-rcon-cpe-projection-step
                (fn-sn-consumer (fn-own-store *osi-completing*)) *rcon-t-r*
                (fn-sn-identity-next (fn-own-store *osi-completing*)))
               (fn-cpe-projection-step
                (fn-sn-consumer (fn-own-store *osi-completing*)) *rcon-t-r*
                (fn-sn-identity-next (fn-own-store *osi-completing*))))
        (let ((p (fn-rcon-cpe-projection-step
                  (fn-sn-consumer (fn-own-store *osi-completing*)) *rcon-t-r*
                  (fn-sn-identity-next (fn-own-store *osi-completing*)))))
          (eq (car p) :ok))
        (equal (fn-record-msgid *rcon-t-r*)
               (fn-record-msgid *rcon-t-r*))
        ;; every element: the twins agree with their references
        (equal (list (fn-rcon-record-p xs)
                     (fn-rcon-store-event-p xs)
                     (fn-rcon-store-event-sequence xs)
                     (fn-rcon-store-event-txid xs)
                     (fn-rcon-store-event-generation xs))
               (list (fn-record-p xs)
                     (fn-store-event-p xs)
                     (fn-store-event-sequence xs)
                     (fn-store-event-txid xs)
                     (fn-store-event-generation xs))))))

; -----------------------------------------------------------------------------
; The string clauses separate.  Each variant of the witness fails exactly the
; one clause named, with every other conjunct of fn-record-p intact, and
; the concrete recognizer refuses it as the reference does.

(defun rcon-t-with-msgid (r m)
  (fn-record-make (fn-record-sequence r) (fn-record-txid r)
                  (fn-record-generation r) m (fn-record-payload r)
                  (fn-record-groups r) (fn-record-obligation-id r)
                  (fn-record-content-subject r) (fn-record-release-evidence r)
                  (fn-record-charge r) (fn-record-stamp r)))
(defun rcon-t-with-subject (r s)
  (fn-record-make (fn-record-sequence r) (fn-record-txid r)
                  (fn-record-generation r) (fn-record-msgid r)
                  (fn-record-payload r) (fn-record-groups r)
                  (fn-record-obligation-id r) s (fn-record-release-evidence r)
                  (fn-record-charge r) (fn-record-stamp r)))
(defun rcon-t-repeat (c n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons c (rcon-t-repeat c (1- n)))))
(defconst *rcon-t-s250* (coerce (rcon-t-repeat #\a 250) 'string))
(defconst *rcon-t-s251* (coerce (rcon-t-repeat #\a 251) 'string))
(defconst *rcon-t-s256* (coerce (rcon-t-repeat #\a 256) 'string))
(defconst *rcon-t-s257* (coerce (rcon-t-repeat #\a 257) 'string))
; 250 ASCII characters and then one character with code 200.
(defconst *rcon-t-s-high*
  (coerce (append (rcon-t-repeat #\a 249) (list (code-char 200))) 'string))

; The witness with the identity that the reference keeps: the constructor of
; the accessors is the record.
(assert-event (equal (rcon-t-with-msgid *rcon-t-r* (fn-record-msgid *rcon-t-r*))
                     *rcon-t-r*))

; Message-ID: the ASCII walk and the two bounds, one at a time.
(assert-event (and (fn-record-p (rcon-t-with-msgid *rcon-t-r* *rcon-t-s250*))
                   (fn-rcon-record-p (rcon-t-with-msgid *rcon-t-r* *rcon-t-s250*))))
(assert-event (and (not (fn-record-p (rcon-t-with-msgid *rcon-t-r* *rcon-t-s251*)))
                   (not (fn-rcon-record-p (rcon-t-with-msgid *rcon-t-r* *rcon-t-s251*)))))
(assert-event (and (not (fn-record-p (rcon-t-with-msgid *rcon-t-r* "")))
                   (not (fn-rcon-record-p (rcon-t-with-msgid *rcon-t-r* "")))))
(assert-event (and (stringp *rcon-t-s-high*)
                   (equal (length *rcon-t-s-high*) 250)
                   (fn-record-octet-stringp *rcon-t-s-high*)
                   (not (fn-record-msgidp *rcon-t-s-high*))
                   (not (fn-rcon-msgidp *rcon-t-s-high*))
                   (not (fn-record-p (rcon-t-with-msgid *rcon-t-r* *rcon-t-s-high*)))
                   (not (fn-rcon-record-p (rcon-t-with-msgid *rcon-t-r* *rcon-t-s-high*)))))
(assert-event (and (not (fn-record-p (rcon-t-with-msgid *rcon-t-r* '(1 2))))
                   (not (fn-rcon-record-p (rcon-t-with-msgid *rcon-t-r* '(1 2))))))

; Metadata: the bounds, one at a time.  A 257-character string is a string
; and an octet string; the bound is what refuses it, so the concrete test
; is more than stringp.
(assert-event (and (fn-record-p (rcon-t-with-subject *rcon-t-r* *rcon-t-s256*))
                   (fn-rcon-record-p (rcon-t-with-subject *rcon-t-r* *rcon-t-s256*))))
(assert-event (and (stringp *rcon-t-s257*)
                   (fn-record-octet-stringp *rcon-t-s257*)
                   (not (fn-record-metadata-bytes-p *rcon-t-s257*))
                   (not (fn-rcon-metadata-bytes-p *rcon-t-s257*))
                   (not (fn-record-p (rcon-t-with-subject *rcon-t-r* *rcon-t-s257*)))
                   (not (fn-rcon-record-p (rcon-t-with-subject *rcon-t-r* *rcon-t-s257*)))))
(assert-event (and (not (fn-record-p (rcon-t-with-subject *rcon-t-r* "")))
                   (not (fn-rcon-record-p (rcon-t-with-subject *rcon-t-r* "")))))
(assert-event (and (not (fn-record-p (rcon-t-with-subject *rcon-t-r* 7)))
                   (not (fn-rcon-record-p (rcon-t-with-subject *rcon-t-r* 7)))))

; The octet domain is the string domain: every ACL2 string, with any codes.
(assert-event (and (fn-record-octet-stringp *rcon-t-s-high*)
                   (fn-record-octet-stringp (coerce (list (code-char 255) (code-char 0)) 'string))
                   (not (fn-record-octet-stringp '(1 2)))
                   (not (fn-record-octet-stringp nil))))

; -----------------------------------------------------------------------------
; The hypotheses of the index-walk lemma.  fn-rcon-ascii-from's equation
; with the list walk is stated for a string and a natural index; the
; keystones have no hypothesis.  Without (natp i) the walk answers t
; without looking, and the list walk from nthcdr's zp case sees the whole
; string: on the string with a high code they differ.
(assert-event (equal (fn-rcon-ascii-from *rcon-t-s-high* 0) nil))
(assert-event (equal (fn-rcon-ascii-from *rcon-t-s-high* 249) nil))
(assert-event (equal (fn-rcon-ascii-from *rcon-t-s-high* 250) t))
(assert-event (equal (fn-rcon-ascii-from *rcon-t-s250* 0) t))
(assert-event
 (with-guard-checking :none
  (and (equal (fn-rcon-ascii-from *rcon-t-s-high* -1) t)
       (equal (fn-record-ascii-octet-listp
               (fn-record-string-octets-aux (nthcdr -1 (coerce *rcon-t-s-high* 'list))))
              nil))))
(must-fail
 (defthm rcon-t-ascii-walk-without-natp
   (equal (fn-rcon-ascii-from *rcon-t-s-high* -1)
          (fn-record-ascii-octet-listp
           (fn-record-string-octets-aux (nthcdr -1 (coerce *rcon-t-s-high* 'list)))))
   :hints (("Goal" :in-theory (enable fn-rcon-ascii-from)))))

; -----------------------------------------------------------------------------
; The host runs compiled code: every concrete function is guard-verified.
(assert-event
 (and (eq (symbol-class 'fn-rcon-record-p (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-msgidp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-metadata-bytes-p (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-ascii-from (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-store-event-p (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-store-event-sequence (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-store-event-txid (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-store-event-generation (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-sf-record-pair (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-sn-record-bindsp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-cpe-projection-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-th-prefix-step (w state)) :common-lisp-compliant)))
; The guards are the references' guards.
(assert-event (and (equal (guard 'fn-rcon-record-p nil (w state))
                          (guard 'fn-record-p nil (w state)))
                   (equal (guard 'fn-rcon-sn-record-bindsp nil (w state))
                          (guard 'fn-sn-record-bindsp nil (w state)))
                   (equal (guard 'fn-rcon-store-event-sequence nil (w state))
                          (guard 'fn-store-event-sequence nil (w state)))))
