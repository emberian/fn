; fn: teeth for books/article-kind-codec.lisp.
;
; fn-ak-decode-of-encode: inhabited at the example values and four payloads
; (empty, short, two full lines, a third line); its kind hypothesis is
; needed -- the grammar encoding of a value outside the kind (a From that is
; no mailbox-list) decodes to the refusal :from, not to the value.
; fn-ak-encode-of-decode (canonicity): a source outside the one encoding
; (unpadded base64, a bare LF, a trailing octet, a folded header) is refused,
; and the refusal of another version or kind is named.
; fn-ak-grammar-encode-is-the-layout: equal at every example; its payload
; ceiling is needed (above it the layout is octets and the codec refuses).

(in-package "ACL2")
(include-book "../../books/article-kind-codec")

(defun akc-crlf (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal (car xs) 124)
          (list* 13 10 (akc-crlf (cdr xs)))
        (cons (car xs) (akc-crlf (cdr xs))))
    nil))

(defun akc-src (s) (declare (xargs :guard (stringp s))) (akc-crlf (fn-ak-text s)))

(defconst *akc-head*
  "From: a@b|Date: x|Newsgroups: a.b|Subject: s|Message-ID: <a@b>|FN-Kind: opaque 1|Content-Type: t|Content-Transfer-Encoding: base64||")

(defun akc-round-trips (payloads)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp payloads)
      (and (equal (fn-ak-decode (fn-ak-encode (fn-ak-example-values) (car payloads)))
                  (list :ok (fn-ak-example-values) (car payloads)))
           (equal (fn-ak-encode (fn-ak-example-values) (car payloads))
                  (fn-ak-layout (fn-ak-example-values) (car payloads)))
           (akc-round-trips (cdr payloads)))
    t))

(assert-event (akc-round-trips (fn-ak-example-payloads)))
(assert-event (equal (len (fn-ak-example-payloads)) 4))

; The kind hypothesis of fn-ak-decode-of-encode is needed.
(defconst *akc-bad-from*
  (fn-ak-values (fn-ak-text "nomailbox") (fn-ak-text "x") (fn-ak-text "a.b")
                (fn-ak-text "s") (fn-ak-text "<a@b>") (fn-ak-text "t")))
(assert-event (not (fn-ak-rows-valuesp *fn-ak-v1-rows* *akc-bad-from*)))
(assert-event (null (fn-ak-encode *akc-bad-from* nil)))
(assert-event
 (equal (fn-ak-decode (fn-wg-encode *fn-ak-grammar* (fn-ak-grammar-value *akc-bad-from* nil)))
        '(:refused :from)))

; Accepted: the head with no payload and with "hello".
(assert-event (equal (car (fn-ak-decode (akc-src *akc-head*))) :ok))
(assert-event (equal (caddr (fn-ak-decode (akc-src (concatenate 'string *akc-head* "aGVsbG8=|"))))
                     (fn-ak-text "hello")))
; Canonicity: every other spelling refused.
(assert-event (equal (fn-ak-decode (akc-src (concatenate 'string *akc-head* "aGVsbG8|")))
                     '(:refused :malformed)))
(assert-event (equal (fn-ak-decode (append (akc-src (concatenate 'string *akc-head* "aGVsbG8=")) '(10)))
                     '(:refused :malformed)))
(assert-event (equal (fn-ak-decode (append (akc-src (concatenate 'string *akc-head* "aGVsbG8=|")) '(65)))
                     '(:refused :malformed)))
(assert-event (equal (fn-ak-decode (akc-src "From: a@b|Date: x|Newsgroups: a.b|Subject: s| more|Message-ID: <a@b>|FN-Kind: opaque 1|Content-Type: t|Content-Transfer-Encoding: base64||"))
                     '(:refused :malformed)))
; Versions and kinds by name.
(assert-event (equal (fn-ak-decode (akc-src "From: a@b|Date: x|Newsgroups: a.b|Subject: s|Message-ID: <a@b>|FN-Kind: opaque 2|Content-Type: t|Content-Transfer-Encoding: base64||"))
                     '(:refused :kind-version)))
(assert-event (equal (fn-ak-decode (akc-src "From: a@b|Date: x|Newsgroups: a.b|Subject: s|Message-ID: <a@b>|FN-Kind: blob 1|Content-Type: t|Content-Transfer-Encoding: base64||"))
                     '(:refused :kind)))
(assert-event (equal (fn-ak-decode (akc-src "From: nomailbox|Date: x|Newsgroups: a.b|Subject: s|Message-ID: <a@b>|FN-Kind: opaque 1|Content-Type: t|Content-Transfer-Encoding: base64||"))
                     '(:refused :from)))
(assert-event (equal (fn-ak-decode '(256)) '(:refused :malformed)))

; The bridge's payload ceiling is needed: above it the codec refuses while
; the layout is octets.
(defthm akc-bridge-ceiling-is-needed
  (implies (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
                (fn-cbor-octet-listp payload)
                (< *fn-article-max-octets* (len payload)))
           (and (null (fn-ak-encode vals payload))
                (consp (fn-ak-layout vals payload))))
  :hints (("Goal" :in-theory (disable fn-ak-rows-valuesp (:e fn-ak-rows-valuesp)
                                      fn-ak-render-rows fn-ak-frame))))
