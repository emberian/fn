; Provenance test book: the guard audit, the ground witness behind each
; per-kind rendering equality, the codec round trip evaluated on a real value
; of every kind, and the teeth of the two hypotheses that carry weight.
;
; The rendering witnesses are the point of the book.  Each one is the EXACT
; string that kind's writer put in the evidence slot before the typed record
; existed, so the equalities in books/provenance.lisp are checked here against
; a value and not only against a variable.
(in-package "ACL2")
(include-book "../../books/provenance-codec")

; -----------------------------------------------------------------------------
; Guard audit.  Every provenance function is total.

(assert-event (equal (guard 'fn-provp nil (w state)) ''t))
(assert-event (equal (guard 'fn-prov-kind nil (w state)) ''t))
(assert-event (equal (guard 'fn-prov-render nil (w state)) ''t))
(assert-event (equal (guard 'fn-prov-describe nil (w state)) ''t))
(assert-event (equal (guard 'fn-prov-wire nil (w state)) ''t))
(assert-event (equal (guard 'fn-prov-of-wire nil (w state)) ''t))
(assert-event (equal (guard 'fn-prov-durablep nil (w state)) ''t))

; Records are opaque: an accessor of a non-record is total, not an error.
(assert-event (equal (fn-prov-post-principal 7) nil))
(assert-event (equal (fn-prov-transit-peer '(:fn-prov-transit . tail)) nil))
(assert-event (not (fn-provp 7)))
(assert-event (not (fn-provp nil)))
(assert-event (not (fn-provp '(:fn-prov-post "who"))))   ; wrong width

; -----------------------------------------------------------------------------
; The four kinds, and the widening
;
; Every string is a provenance.  This is the fact that makes the retention
; slot's widening free: an evidence value in a store written before this lane
; is admissible unchanged, as the `:legacy' kind.

(assert-event (fn-provp "unsigned-legacy-v0"))
(assert-event (fn-provp "peer-transit:innA"))
(assert-event (fn-provp ""))
(assert-event (equal (fn-prov-kind "peer-transit:innA") :legacy))

(defconst *prov-post* (fn-prov-make-post "operator@example.invalid" 7))
(defconst *prov-transit*
  (fn-prov-make-transit "innA" :takethis (fn-prov-diagnostic-match) 12))
(defconst *prov-transit-mismatch*
  (fn-prov-make-transit "innA" :ihave
                        (fn-prov-diagnostic-mismatch
                         '(110 101 119 115 46 102 110))      ; "news.fn"
                        12))
(defconst *prov-bp*
  (fn-prov-make-bp "ipn:5.1" "ipn:9.1-1758300000-3" "bp-archive-policy-v1"))
(defconst *prov-local* (fn-prov-make-local "container-import"))

(assert-event (fn-provp *prov-post*))
(assert-event (fn-provp *prov-transit*))
(assert-event (fn-provp *prov-transit-mismatch*))
(assert-event (fn-provp *prov-bp*))
(assert-event (fn-provp *prov-local*))

(assert-event (equal (fn-prov-kind *prov-post*) :post))
(assert-event (equal (fn-prov-kind *prov-transit*) :peer-transit))
(assert-event (equal (fn-prov-kind *prov-bp*) :bp-receive))
(assert-event (equal (fn-prov-kind *prov-local*) :local))

; The kinds are disjoint on real values, not only in the theorem.
(assert-event (not (fn-prov-transitp *prov-post*)))
(assert-event (not (fn-prov-postp *prov-transit*)))
(assert-event (not (fn-prov-localp *prov-bp*)))
(assert-event (not (stringp *prov-transit*)))

; A transit kind outside the closed pair is refused, and a diagnostic that is
; neither answer is refused: the field types are checked, not assumed.
(assert-event (not (fn-provp (fn-prov-make-transit "innA" :check
                                                   (fn-prov-diagnostic-match) 12))))
(assert-event (not (fn-provp (fn-prov-make-transit "innA" :ihave '(:maybe) 12))))
(assert-event (not (fn-provp (fn-prov-make-post 7 7))))
(assert-event (not (fn-provp (fn-prov-make-post "who" -1))))

; -----------------------------------------------------------------------------
; The rendering witnesses
;
; `fn-peer-evidence' (books/peer-inbound.lisp) answered
; (string-append "peer-transit:" peer); the host's `metadata'
; (tools/run_store.py) answered the constant "unsigned-legacy-v0"; the BP
; ingress path answered its policy's own evidence string.  These three lines
; are those three answers.

(assert-event (equal (fn-prov-render *prov-post*) "unsigned-legacy-v0"))
(assert-event (equal (fn-prov-render *prov-transit*) "peer-transit:innA"))
(assert-event (equal (fn-prov-render *prov-transit-mismatch*) "peer-transit:innA"))
(assert-event (equal (fn-prov-render *prov-bp*) "bp-archive-policy-v1"))
(assert-event (equal (fn-prov-render *prov-local*) "container-import"))
(assert-event (equal (fn-prov-render "peer-transit:innA") "peer-transit:innA"))

; The lossless line.  It carries what the legacy rendering throws away: the
; principal and generation of a POST, the command, Path diagnostic and
; configuration generation of a transit.
(assert-event
 (equal (fn-prov-describe *prov-post*)
        "post principal=operator@example.invalid generation=7"))
(assert-event
 (equal (fn-prov-describe *prov-transit*)
        "peer-transit peer=innA kind=TAKETHIS diagnostic=path-match generation=12"))
(assert-event
 (equal (fn-prov-describe *prov-transit-mismatch*)
        "peer-transit peer=innA kind=IHAVE diagnostic=path-mismatch generation=12"))
(assert-event
 (equal (fn-prov-describe *prov-local*) "local reason=container-import"))
(assert-event
 (equal (fn-prov-describe "peer-transit:innA") "legacy peer-transit:innA"))

; -----------------------------------------------------------------------------
; The codec, evaluated
;
; K-PROV-1: a legacy value's wire form IS the value, so a store written
; before this lane holds the same octets it held before.

(assert-event (equal (fn-prov-wire "peer-transit:innA") "peer-transit:innA"))
(assert-event (equal (fn-prov-wire "unsigned-legacy-v0") "unsigned-legacy-v0"))

; K-PROV-2: and it reads back as itself, as the `:legacy' kind.
(assert-event (fn-prov-plain-stringp "peer-transit:innA"))
(assert-event (equal (fn-prov-of-wire "peer-transit:innA") "peer-transit:innA"))
(assert-event (equal (fn-prov-kind (fn-prov-of-wire "peer-transit:innA")) :legacy))
(assert-event (equal (fn-prov-of-wire "unsigned-legacy-v0") "unsigned-legacy-v0"))

; K-PROV-3, on a value of every structured kind.
(assert-event (fn-prov-encodablep *prov-post*))
(assert-event (fn-prov-encodablep *prov-transit*))
(assert-event (fn-prov-encodablep *prov-transit-mismatch*))
(assert-event (fn-prov-encodablep *prov-bp*))
(assert-event (fn-prov-encodablep *prov-local*))

(assert-event (equal (fn-prov-of-wire (fn-prov-wire *prov-post*)) *prov-post*))
(assert-event (equal (fn-prov-of-wire (fn-prov-wire *prov-transit*)) *prov-transit*))
(assert-event (equal (fn-prov-of-wire (fn-prov-wire *prov-transit-mismatch*))
                     *prov-transit-mismatch*))
(assert-event (equal (fn-prov-of-wire (fn-prov-wire *prov-bp*)) *prov-bp*))
(assert-event (equal (fn-prov-of-wire (fn-prov-wire *prov-local*)) *prov-local*))

; The encoding is not the rendering, and it is not degenerate: the wire form
; of a transit carries the peer, the command, the diagnostic and the
; generation, and it is longer than the string the same event used to write.
(assert-event (not (equal (fn-prov-wire *prov-transit*)
                          (fn-prov-render *prov-transit*))))
; The command is carried: the same peer, generation and diagnostic under
; IHAVE and under TAKETHIS are different wire forms, where the legacy string
; was the same for both.
(assert-event
 (not (equal (fn-prov-wire *prov-transit*)
             (fn-prov-wire (fn-prov-make-transit "innA" :ihave
                                                 (fn-prov-diagnostic-match) 12)))))
(assert-event
 (equal (fn-prov-render *prov-transit*)
        (fn-prov-render (fn-prov-make-transit "innA" :ihave
                                              (fn-prov-diagnostic-match) 12))))
(assert-event (equal (car (fn-prov-octets *prov-transit*)) 0))   ; the octet sentinel
(assert-event (not (fn-prov-plain-stringp (fn-prov-wire *prov-transit*))))
(assert-event (not (equal (fn-prov-of-wire (fn-prov-wire *prov-transit*))
                          (fn-prov-of-wire (fn-prov-wire *prov-transit-mismatch*)))))

; Every kind's wire form fits the record's evidence field, so a durable
; writer may put it there without a second bound.
(assert-event (fn-prov-durablep *prov-post*))
(assert-event (fn-prov-durablep *prov-transit*))
(assert-event (fn-prov-durablep *prov-transit-mismatch*))
(assert-event (fn-prov-durablep *prov-bp*))
(assert-event (fn-prov-durablep *prov-local*))
(assert-event (fn-record-metadata-bytes-p (fn-prov-wire *prov-transit*)))
(assert-event (fn-record-metadata-bytes-p (fn-prov-wire *prov-bp*)))

; -----------------------------------------------------------------------------
; Teeth
;
; One concrete violating value per hypothesis that carries weight.

; `fn-prov-plain-stringp' in K-PROV-2 and K-PROV-3.  The violating value is a
; string whose octets ARE a structured encoding: it is a `fn-provp' (every
; string is), it is not `fn-prov-plain-stringp', and it reads back as the
; record it encodes rather than as itself.  Without the hypothesis the
; conclusion is false on this value.
(defconst *prov-forged-legacy* (fn-prov-wire *prov-local*))
(assert-event (stringp *prov-forged-legacy*))
(assert-event (fn-provp *prov-forged-legacy*))
(assert-event (not (fn-prov-plain-stringp *prov-forged-legacy*)))
(assert-event (not (equal (fn-prov-of-wire *prov-forged-legacy*)
                          *prov-forged-legacy*)))
(assert-event (equal (fn-prov-of-wire *prov-forged-legacy*) *prov-local*))
(assert-event (not (fn-prov-encodablep *prov-forged-legacy*)))

; A string that merely starts with the prefix but is not a well-formed wire
; form is refused by `fn-prov-plain-stringp' and still reads back as itself:
; the recognizer excludes the whole prefixed set, and the decoder is
; conservative about the part of it the encoder cannot produce.
(defconst *prov-forged-prefix* "fnprov1:zz")
(assert-event (not (fn-prov-plain-stringp *prov-forged-prefix*)))
(assert-event (equal (fn-prov-of-wire *prov-forged-prefix*) *prov-forged-prefix*))
(assert-event (not (fn-prov-encodablep *prov-forged-prefix*)))

; A NUL-bearing string is a plain string under this codec: the wire form is
; printable, so nothing about octet 0 is special any more.
(defconst *prov-nul-string* (coerce (list (code-char 0)) 'string))
(assert-event (fn-prov-plain-stringp *prov-nul-string*))
(assert-event (equal (fn-prov-of-wire *prov-nul-string*) *prov-nul-string*))

; The wire form is printable ASCII, which is what the host boundary guard
; `fn-store-text-octetsp' (host/store-host.lisp, octets 33 to 126) admits and
; what `fn-record-metadata-bytes-p' bounds at 256.  The four witnesses below
; are the check that the two bounds are compatible with *fn-prov-max-field*.
(defun prov-test-printablep (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (<= 33 (car xs)) (<= (car xs) 126)
           (prov-test-printablep (cdr xs)))
    (null xs)))
(assert-event (prov-test-printablep (fn-record-string-octets (fn-prov-wire *prov-post*))))
(assert-event (prov-test-printablep (fn-record-string-octets (fn-prov-wire *prov-transit*))))
(assert-event (prov-test-printablep
               (fn-record-string-octets (fn-prov-wire *prov-transit-mismatch*))))
(assert-event (prov-test-printablep (fn-record-string-octets (fn-prov-wire *prov-bp*))))
(assert-event (prov-test-printablep (fn-record-string-octets (fn-prov-wire *prov-local*))))
(assert-event (<= (len (fn-record-string-octets (fn-prov-wire *prov-bp*))) 256))

; `fn-record-metadata-bytes-p' in `fn-prov-durablep'.  A provenance whose
; fields are each inside `*fn-prov-max-field*' is durable; one whose reason
; exceeds it is `fn-provp' and renderable but NOT encodable, so a writer may
; not put it in a record.
(defconst *prov-long-reason*
  (fn-prov-make-local
   "0123456789012345678901234567890123456789012345678901234567890123456789"))
(assert-event (fn-provp *prov-long-reason*))
(assert-event (< *fn-prov-max-field*
                 (len (fn-record-string-octets
                       (fn-prov-local-reason *prov-long-reason*)))))
(assert-event (not (fn-prov-encodablep *prov-long-reason*)))
(assert-event (not (fn-prov-durablep *prov-long-reason*)))

; The empty string is a `fn-provp' and a plain string, but it is not durable:
; `fn-record-metadata-bytes-p' requires a nonempty field, which is the record
; grammar's rule and not this book's.
(assert-event (fn-provp ""))
(assert-event (fn-prov-plain-stringp ""))
(assert-event (not (fn-prov-durablep "")))

; The `:post' rendering is lossy by construction, and the test says so: two
; different POST provenances render to the same legacy string and are
; distinguished only by the record and its wire form.
(defconst *prov-post-other* (fn-prov-make-post "other@example.invalid" 9))
(assert-event (equal (fn-prov-render *prov-post*)
                     (fn-prov-render *prov-post-other*)))
(assert-event (not (equal *prov-post* *prov-post-other*)))
(assert-event (not (equal (fn-prov-wire *prov-post*)
                          (fn-prov-wire *prov-post-other*))))
