; Teeth for books/records-concrete.lisp, books/records-concrete-owner.lisp,
; books/records-codec-concrete.lisp and books/records-attach-concrete.lisp.
(in-package "ACL2")
(include-book "../../books/records-concrete")
(include-book "../../books/records-concrete-owner")
(include-book "../../books/records-attach-concrete")
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

; -----------------------------------------------------------------------------
; The dispatchers at write (lane/rep-records-2).  Witness: the same POST as
; *osi-completing*, stopped before its :record-directory observation, so the
; store is :record-attempted with the article record staged.  The encoder,
; the staged sequence and the observation each run on it through the twin.

(defconst *rcon-t-attempted*
  (fn-own-run *own-taken*
              (osi-drop-last
               (osi-drop-last (own-post-events (osi-sub-record 2 2 *osi-sub*))))))
(defconst *rcon-t-staged*
  (fn-sf-record-candidate (fn-sn-files (fn-own-store *rcon-t-attempted*))))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store *rcon-t-attempted*)))
                     :record-attempted))
(assert-event (fn-rcon-record-p *rcon-t-staged*))
(assert-event (equal *rcon-t-staged* *rcon-t-r*))

; The encoder: the staged record's octets, equal to the reference and to the
; codec's own encoding, and nil on a non-event.  A retention event takes the
; second arm.
(assert-event (consp (fn-rcon-store-event-encode *rcon-t-staged*)))
(assert-event (equal (fn-rcon-store-event-encode *rcon-t-staged*)
                     (fn-store-event-encode *rcon-t-staged*)))
(assert-event (equal (fn-rcon-store-event-encode *rcon-t-staged*)
                     (fn-record-encode *rcon-t-staged*)))
(assert-event (consp (fn-rcon-store-event-encode *rcon-t-retention*)))
(assert-event (equal (fn-rcon-store-event-encode *rcon-t-retention*)
                     (fn-store-event-encode *rcon-t-retention*)))
(assert-event (and (null (fn-rcon-store-event-encode nil))
                   (null (fn-rcon-store-event-encode (list 1 2)))
                   (null (fn-store-event-encode (list 1 2)))))
; A record the recognizer refuses (a 251-character Message-ID) is not
; encoded by either.
(assert-event (null (fn-rcon-store-event-encode (rcon-t-with-msgid *rcon-t-r* *rcon-t-s251*))))
(assert-event (null (fn-store-event-encode (rcon-t-with-msgid *rcon-t-r* *rcon-t-s251*))))

; The staged sequence: 2, from the twin and the reference; nil with nothing
; staged.
(assert-event (equal (fn-rcon-sbud-pending-sequence (fn-own-store *rcon-t-attempted*)) 2))
(assert-event (equal (fn-sbud-pending-sequence (fn-own-store *rcon-t-attempted*)) 2))
(assert-event (null (fn-rcon-sbud-pending-sequence (fn-own-store *own-taken*))))
(assert-event (null (fn-sbud-pending-sequence (fn-own-store *own-taken*))))

; The observation, at the owner the host calls: the :record-directory event
; moves the store to :completing with the staged pair, and the owner it
; produces is the reference step's, which is the owner *osi-completing*.
(defconst *rcon-t-oc* (fn-ocfg-make *rcon-t-attempted* *osi-cfg* nil nil))
(defconst *rcon-t-io* (fn-rcon-ocfg-io *rcon-t-oc* :record-directory :ok))
(assert-event (equal *rcon-t-io*
                     (fn-ocfg-step *rcon-t-oc* '(:store (:io :record-directory :ok)))))
(assert-event (equal (fn-ocfg-owner *rcon-t-io*) *osi-completing*))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner *rcon-t-io*))))
                     :completing))
(assert-event (equal (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner *rcon-t-io*))))
                     (cons (fn-record-sequence *rcon-t-r*) (fn-record-txid *rcon-t-r*))))
; An :error observation fences the record, the same in both.
(assert-event (equal (fn-rcon-ocfg-io *rcon-t-oc* :record-directory :error)
                     (fn-ocfg-step *rcon-t-oc* '(:store (:io :record-directory :error)))))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store
                                                 (fn-ocfg-owner
                                                  (fn-rcon-ocfg-io *rcon-t-oc* :record-directory :error)))))
                     :fenced-record))
; Another operation, and the same observation in a phase that does not take
; it, leave the twin and the reference equal.
(assert-event (equal (fn-rcon-ocfg-io *rcon-t-oc* :record-file :ok)
                     (fn-ocfg-step *rcon-t-oc* '(:store (:io :record-file :ok)))))
(assert-event (equal (fn-rcon-sn-io (fn-own-store *own-taken*) :record-directory :ok)
                     (fn-sn-io (fn-own-store *own-taken*) :record-directory :ok)))

; The keystones have no hypothesis.  The guards are the references': the
; store-level observation's guard, fn-sn-statep, is needed for its compiled
; code (the file step reads the files' phase, fn-sf-statep's), so a copy
; with guard t is refused.
(must-fail
 (defun rcon-t-sn-io-unguarded (s operation result)
   (declare (xargs :guard t :verify-guards t))
   (let* ((old-files (fn-sn-files s))
          (files (fn-rcon-sn-file-step old-files operation result)))
     (fn-sn-update s files (fn-sn-node s)))))
(assert-event
 (and (eq (symbol-class 'fn-rcon-store-event-encode (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-sbud-pending-sequence (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-sf-record-dir-result (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-sn-file-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-sn-io (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-own-store-io (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rcon-ocfg-io (w state)) :common-lisp-compliant)))
(assert-event (and (equal (guard 'fn-rcon-sn-io nil (w state))
                          (guard 'fn-sn-io nil (w state)))
                   (equal (guard 'fn-rcon-sf-record-dir-result nil (w state))
                          (guard 'fn-sf-record-dir-result nil (w state)))
                   (equal (guard 'fn-rcon-store-event-encode nil (w state))
                          (guard 'fn-store-event-encode nil (w state)))))

; -----------------------------------------------------------------------------
; The codec's encoder behind the seam (books/records-codec-concrete.lisp),
; attached by books/records-attach-concrete.lisp, which this book includes
; after codec-attach as the host images do.  On the staged record of the POST
; above it is the implementation's encoding, non-empty, and the encoding
; every ground fn-record-encode now evaluates through; on a record the
; recognizer refuses and on non-records it is nil, as the implementation.

(assert-event (consp (fn-rcon-record-encode-impl *rcon-t-staged*)))
(assert-event (equal (fn-rcon-record-encode-impl *rcon-t-staged*)
                     (fn-record-encode-impl *rcon-t-staged*)))
(assert-event (equal (fn-record-encode *rcon-t-staged*)
                     (fn-rcon-record-encode-impl *rcon-t-staged*)))
(assert-event (equal (fn-rcon-record-encode-impl *rcon-t-retention*) nil))
(assert-event (and (null (fn-rcon-record-encode-impl nil))
                   (null (fn-rcon-record-encode-impl "x"))
                   (null (fn-rcon-record-encode-impl (list 1 2)))))
; The recognizer is what refuses: a 251-character Message-ID keeps the
; record's shape, and neither encoder encodes it; the 250-character one is
; encoded by both.
(defconst *rcon-t-msgid-251* (rcon-t-with-msgid *rcon-t-r* *rcon-t-s251*))
(defconst *rcon-t-msgid-250* (rcon-t-with-msgid *rcon-t-r* *rcon-t-s250*))
(assert-event (and (fn-record-shapep *rcon-t-msgid-251*)
                   (null (fn-rcon-record-encode-impl *rcon-t-msgid-251*))
                   (null (fn-record-encode-impl *rcon-t-msgid-251*))))
(assert-event (and (consp (fn-rcon-record-encode-impl *rcon-t-msgid-250*))
                   (equal (fn-rcon-record-encode-impl *rcon-t-msgid-250*)
                          (fn-record-encode-impl *rcon-t-msgid-250*))))
; So "the encoder encodes every shaped record" is refuted at that record.
(must-fail
 (defthm rcon-t-encode-shaped-251
   (implies (fn-record-shapep *rcon-t-msgid-251*)
            (consp (fn-rcon-record-encode-impl *rcon-t-msgid-251*)))))
; The attachment: fn-record-encode evaluates through the twin.
(assert-event
 (eq (cdr (assoc-eq 'fn-record-encode
                    (getpropc 'fn-record-decode-exact 'attachment nil (w state))))
     'fn-rcon-record-encode-impl))
(assert-event
 (and (eq (symbol-class 'fn-rcon-record-encode-impl (w state)) :common-lisp-compliant)
      (equal (guard 'fn-rcon-record-encode-impl nil (w state))
             (guard 'fn-record-encode-impl nil (w state)))))
