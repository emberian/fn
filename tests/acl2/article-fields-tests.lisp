; Executable grammar and provenance tests for bounded article fields.
(in-package "ACL2")
(include-book "../../books/article-fields")

(defun fn-af-test-octets-aux (chars)
  (if (consp chars)
      (cons (char-code (car chars)) (fn-af-test-octets-aux (cdr chars)))
    nil))

(defun fn-af-test-octets (text)
  (fn-af-test-octets-aux (coerce text 'list)))

(defun fn-af-test-repeat (n byte)
  (if (zp n) nil (cons byte (fn-af-test-repeat (1- n) byte))))

(defun fn-af-test-parse (source)
  (fn-article-result-article (fn-article-parse source)))

(defconst *fn-af-msgid*
  (fn-af-test-octets "<A.B+tag@example.invalid>"))
(defconst *fn-af-groups*
  (list (fn-af-test-octets "fn.letters") (fn-af-test-octets "fn.test")))

(defconst *fn-af-good-source*
  (append (fn-af-test-octets "Message-ID:   <A.B+tag@example.invalid>  ") '(13 10)
          (fn-af-test-octets "Newsgroups: fn.letters, ") '(13 10)
          '(9 102 110 46 116 101 115 116) '(13 10)
          (fn-af-test-octets "X-Unknown: keep") '(13 10 13 10)
          '(66 111 100 121 13 10)))
(defconst *fn-af-good-article* (fn-af-test-parse *fn-af-good-source*))

(assert-event (fn-article-syntax-p *fn-af-good-article*))
(assert-event (equal (fn-af-message-id-status *fn-af-good-article*)
                     (list :single *fn-af-msgid*
                           (fn-article-get-header *fn-af-good-article*
                                                  *fn-af-message-id-name*))))
(assert-event (equal (fn-af-newsgroups-status *fn-af-good-article*)
                     (list :single *fn-af-groups*
                           (fn-article-get-header *fn-af-good-article*
                                                  *fn-af-newsgroups-name*))))
(assert-event (equal (fn-article-source *fn-af-good-article*) *fn-af-good-source*))
(assert-event (equal (len (fn-article-get-headers *fn-af-good-article*
                                                (fn-af-test-octets "x-unknown")))
                     1))
(assert-event (equal (fn-af-proto-article-check *fn-af-good-article*)
                     (list :ok *fn-af-msgid* *fn-af-groups*
                           (fn-article-get-header *fn-af-good-article*
                                                  *fn-af-message-id-name*)
                           (fn-article-get-header *fn-af-good-article*
                                                  *fn-af-newsgroups-name*))))

; Message-ID grammar, exact identity, literal form, and RFC 5536's 250 bound.
(assert-event (fn-af-message-idp *fn-af-msgid*))
(assert-event (fn-af-message-idp (fn-af-test-octets "<a@[x@y]>")))
(assert-event (not (fn-af-message-idp (fn-af-test-octets "<a..b@example>"))))
(assert-event (not (fn-af-message-idp (fn-af-test-octets "<a@ex..ample>"))))
(assert-event (not (fn-af-message-idp (fn-af-test-octets "<a@[]>x"))))
(assert-event (not (fn-af-message-idp (fn-af-test-octets "<a@[x\\y]>"))))
(assert-event (not (fn-af-message-id-equalp *fn-af-msgid*
                                             (fn-af-test-octets "<a.b+tag@example.invalid>"))))
(assert-event (fn-af-message-id-equalp *fn-af-msgid* *fn-af-msgid*))
(assert-event
 (fn-af-message-idp
  (append '(60 97 64) (fn-af-test-repeat 246 98) '(62))))
(assert-event
 (not (fn-af-message-idp
       (append '(60 97 64) (fn-af-test-repeat 247 98) '(62)))))
; Guard-T standalone grammar entry points retain their malformed-input result
; behavior for improper lists; no host guard fault is part of that contract.
(assert-event (not (fn-af-message-idp '(60 . 62))))

; Newsgroups preserves order and accepts RFC FWS, while rejecting empty dots,
; reserved punctuation, and a dangling comma without changing any field bytes.
(assert-event
 (equal (fn-af-newsgroup-list-parse
         (append (fn-af-test-octets "  fn.letters ,")
                 '(9)
                 (fn-af-test-octets "fn.test  ")))
        (list :ok *fn-af-groups*)))
(assert-event
 (equal (fn-af-newsgroup-list-parse (fn-af-test-octets "fn..letters"))
        '(:error :invalid-newsgroups)))
(assert-event
 (equal (fn-af-newsgroup-list-parse (fn-af-test-octets "fn/letters"))
        '(:error :invalid-newsgroups)))
(assert-event
 (equal (fn-af-newsgroup-list-parse (fn-af-test-octets "fn.letters,"))
        '(:error :invalid-newsgroups)))
(assert-event (equal (fn-af-newsgroup-list-parse '(102 . 110))
                     '(:error :limit)))

; Folded Message-ID is invalid for its *WSP grammar; duplicate semantic fields
; are classified and are never reduced to a first field.
(defconst *fn-af-folded-id-article*
  (fn-af-test-parse
   (append (fn-af-test-octets "Message-ID: <a@example>") '(13 10)
           '(9 60 111 116 104 101 114 64 101 120 97 109 112 108 101 62) '(13 10)
           (fn-af-test-octets "Newsgroups: fn.letters") '(13 10 13 10))))
(assert-event (equal (fn-af-status-kind
                      (fn-af-message-id-status *fn-af-folded-id-article*))
                     :invalid))

(defconst *fn-af-duplicate-article*
  (fn-af-test-parse
   (append (fn-af-test-octets "Message-ID: <a@example>") '(13 10)
           (fn-af-test-octets "Message-ID: <b@example>") '(13 10)
           (fn-af-test-octets "Newsgroups: fn.letters") '(13 10)
           (fn-af-test-octets "Newsgroups: fn.test") '(13 10 13 10))))
(assert-event (equal (fn-af-status-kind
                      (fn-af-message-id-status *fn-af-duplicate-article*))
                     :duplicate))
(assert-event (equal (fn-af-status-kind
                      (fn-af-newsgroups-status *fn-af-duplicate-article*))
                     :duplicate))
(assert-event (equal (fn-af-proto-article-check *fn-af-duplicate-article*)
                     '(:error :newsgroups-duplicate)))

; A proto-article may lack Message-ID for a later injector, but not Newsgroups,
; Injection-Info, or Xref.  This check creates no trace fields itself.
(defconst *fn-af-no-id-article*
  (fn-af-test-parse
   (append (fn-af-test-octets "Newsgroups: fn.letters") '(13 10)
           (fn-af-test-octets "Subject: draft") '(13 10 13 10))))
(assert-event (equal (fn-af-proto-article-check *fn-af-no-id-article*)
                     (list :ok nil (list (fn-af-test-octets "fn.letters")) nil
                           (fn-article-get-header *fn-af-no-id-article*
                                                  *fn-af-newsgroups-name*))))

(defconst *fn-af-forbidden-injection-article*
  (fn-af-test-parse
   (append (fn-af-test-octets "Newsgroups: fn.letters") '(13 10)
           (fn-af-test-octets "Injection-Info: host.example") '(13 10 13 10))))
(assert-event (equal (fn-af-proto-article-check *fn-af-forbidden-injection-article*)
                     '(:error :injection-info)))

(defconst *fn-af-forbidden-xref-article*
  (fn-af-test-parse
   (append (fn-af-test-octets "Newsgroups: fn.letters") '(13 10)
           (fn-af-test-octets "Xref: host fn.letters:1") '(13 10 13 10))))
(assert-event (equal (fn-af-proto-article-check *fn-af-forbidden-xref-article*)
                     '(:error :xref)))

(defconst *fn-af-missing-groups-article*
  (fn-af-test-parse
   (append (fn-af-test-octets "Message-ID: <a@example>") '(13 10 13 10))))
(assert-event (equal (fn-af-proto-article-check *fn-af-missing-groups-article*)
                     '(:error :newsgroups-missing)))

(defconst *fn-af-invalid-id-article*
  (fn-af-test-parse
   (append (fn-af-test-octets "Message-ID: <a.example>") '(13 10)
           (fn-af-test-octets "Newsgroups: fn.letters") '(13 10 13 10))))
(assert-event (equal (fn-af-proto-article-check *fn-af-invalid-id-article*)
                     '(:error :message-id-invalid)))

; The relaying agent's check (RFC 5537 section 3.6 step 1) against the
; injecting agent's (section 3.4.1), on the two articles that separate them.
; These two assertions are the whole difference: an injected article carries
; Injection-Info and a relayed one may carry Xref, and a relaying agent that
; refused either would refuse every article any injecting agent has made.
(assert-event (equal (fn-af-relayed-article-check *fn-af-forbidden-injection-article*)
                     (list :ok nil (list (fn-af-test-octets "fn.letters")) nil
                           (fn-article-get-header *fn-af-forbidden-injection-article*
                                                  *fn-af-newsgroups-name*))))
(assert-event (equal (fn-af-relayed-article-check *fn-af-forbidden-xref-article*)
                     (list :ok nil (list (fn-af-test-octets "fn.letters")) nil
                           (fn-article-get-header *fn-af-forbidden-xref-article*
                                                  *fn-af-newsgroups-name*))))
; And everywhere else the two agree, so the split moved no other decision.
(assert-event (equal (fn-af-relayed-article-check *fn-af-good-article*)
                     (fn-af-proto-article-check *fn-af-good-article*)))
(assert-event (equal (fn-af-relayed-article-check *fn-af-missing-groups-article*)
                     '(:error :newsgroups-missing)))
(assert-event (equal (fn-af-relayed-article-check *fn-af-invalid-id-article*)
                     '(:error :message-id-invalid)))
