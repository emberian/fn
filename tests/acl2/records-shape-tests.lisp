; Teeth for the newsgroup-name recognizer `fn-record-group-namep'
; (books/records-shape.lisp), the one predicate the host applies to a group
; name at `operator init', `group create', the configuration codec and the
; record codec.
;
; The grammar is RFC 5536 s3.1.4:
;   newsgroup-name = component *( "." component )
;   component      = 1*component-char
;   component-char = ALPHA / DIGIT / "+" / "-" / "_"
; The octet bound is the configuration label's 256 octets (the narrowest
; codec that carries a group name; books/records-shape); RFC 5536 sets none.  The keystone
; `fn-record-group-namep-is-the-rfc-5536-grammar' equates the one-pass
; recognizer with the component-at-a-time grammar; each rejection theorem
; below has one `must-fail' per hypothesis and a ground witness showing the
; weakened statement is false on a reachable value.

(in-package "ACL2")
(include-book "../../books/records-shape")
(include-book "../../books/article-fields")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; Witness set: accepted names.  Uppercase, all-digit components and a leading
; "_", "+" or "-" are SHOULD NOTs for generation that a server MUST accept
; (RFC 5536 s3.1.4), so they are admitted.

(defconst *rst-valid-names*
  '("a" "fn.test" "fn.letters" "comp.lang.lisp" "alt.binaries.x"
    "_x.+y.-z.123.ABC" "de.soc.recht.misc" "a.b.c.d.e.f.g.h"))

(defconst *rst-max-name*
  (coerce (make-list *fn-record-max-group-name* :initial-element #\a) 'string))
(defconst *rst-overlong-name*
  (coerce (make-list (+ 1 *fn-record-max-group-name*) :initial-element #\a)
          'string))
(assert-event (equal (length *rst-max-name*) *fn-record-max-group-name*))
(assert-event (equal (length *rst-overlong-name*)
                     (+ 1 *fn-record-max-group-name*)))

(defun rst-all-namep (xs)
  (if (consp xs)
      (and (fn-record-group-namep (car xs)) (rst-all-namep (cdr xs)))
    t))

(defun rst-none-namep (xs)
  (if (consp xs)
      (and (not (fn-record-group-namep (car xs))) (rst-none-namep (cdr xs)))
    t))

(assert-event (rst-all-namep *rst-valid-names*))
(assert-event (fn-record-group-namep *rst-max-name*))

; Rejected names, one or more per violation class.  Every one of these is an
; ASCII string within the octet bound, so the old recognizer admitted it.
(defconst *rst-invalid-names*
  '("Not A Group"          ; space (the native-subsets finding)
    "fn test" "fn.test "   ; space inside and trailing
    ".fn" ".fn.test"       ; leading dot
    "fn..test"             ; empty component
    "fn.test."             ; trailing dot
    "."                    ; no component at all
    "fn/test" "fn*" "fn!x" "fn,test" "fn:test" "fn@x" "fn~x"))
(assert-event (rst-none-namep *rst-invalid-names*))
(assert-event (not (fn-record-group-namep "")))
(assert-event (not (fn-record-group-namep *rst-overlong-name*)))
(assert-event (not (fn-record-group-namep (coerce (list #\a (code-char 200)) 'string))))
(assert-event (not (fn-record-group-namep (coerce (list #\a (code-char 9)) 'string))))

; The invalid names are exactly the ones the length/ASCII conjuncts alone
; would have admitted: the syntax conjunct is what separates them.
(defun rst-all-old-namep (xs)
  (if (consp xs)
      (and (fn-record-ascii-stringp (car xs))
           (fn-record-nonempty-at-mostp (fn-record-string-octets (car xs))
                                        *fn-record-max-group-name*)
           (rst-all-old-namep (cdr xs)))
    t))
(assert-event (rst-all-old-namep *rst-invalid-names*))

; -----------------------------------------------------------------------------
; The keystone on the witness sets: the recognizer agrees with the
; component-at-a-time grammar, which is neither always true nor always false.

(defun rst-agrees (xs)
  (if (consp xs)
      (and (equal (fn-record-group-namep (car xs))
                  (and (fn-record-ascii-stringp (car xs))
                       (fn-record-nonempty-at-mostp
                        (fn-record-string-octets (car xs))
                        *fn-record-max-group-name*)
                       (fn-record-group-name-grammarp
                        (fn-record-string-octets (car xs)))))
           (rst-agrees (cdr xs)))
    t))
(assert-event (rst-agrees *rst-valid-names*))
(assert-event (rst-agrees *rst-invalid-names*))
(assert-event (fn-record-group-name-grammarp (fn-record-string-octets "comp.lang.lisp")))
(assert-event (not (fn-record-group-name-grammarp (fn-record-string-octets "Not A Group"))))
(assert-event (not (fn-record-group-name-grammarp (fn-record-string-octets "fn..test"))))

; The article parser's Newsgroups grammar (books/article-fields.lisp) is the
; same RFC 5536 s3.1.4 production written independently over octets.  The two
; agree on every octet list, so a name an accepted article carries and a name
; the store admits differ only by the wire's octet bound.
(defthm rst-record-group-syntax-is-the-article-newsgroup-syntax
  (equal (fn-record-group-name-octets-aux xs need)
         (fn-af-newsgroup-name-aux xs need))
  :hints (("Goal" :in-theory (enable fn-record-group-name-octets-aux)
           :induct (fn-record-group-name-octets-aux xs need)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Teeth for `fn-record-group-namep-rejects-a-forbidden-octet'
;   (implies (and (member-equal x (fn-record-string-octets text))
;                 (not (equal x 46))
;                 (not (fn-record-group-component-octetp x)))
;            (not (fn-record-group-namep text)))
; Witness: "Not A Group" with x = 32.
(assert-event (member-equal 32 (fn-record-string-octets "Not A Group")))
(assert-event (not (fn-record-group-component-octetp 32)))

; Without membership: x = 32 is not in "fn.test", which is a name.
(assert-event (and (not (member-equal 32 (fn-record-string-octets "fn.test")))
                   (fn-record-group-namep "fn.test")))
(local
 (must-fail
  (defthm rst-forbidden-without-member
    (implies (and (not (equal x 46))
                  (not (fn-record-group-component-octetp x)))
             (not (fn-record-group-namep text))))))

; Without "not a dot": the dot of "fn.test" is a member and not a
; component-char.
(assert-event (not (fn-record-group-component-octetp 46)))
(local
 (must-fail
  (defthm rst-forbidden-without-not-dot
    (implies (and (member-equal x (fn-record-string-octets text))
                  (not (fn-record-group-component-octetp x)))
             (not (fn-record-group-namep text))))))

; Without "not a component-char": "f" (102) is a member of "fn.test".
(assert-event (member-equal 102 (fn-record-string-octets "fn.test")))
(local
 (must-fail
  (defthm rst-forbidden-without-not-component
    (implies (and (member-equal x (fn-record-string-octets text))
                  (not (equal x 46)))
             (not (fn-record-group-namep text))))))

; -----------------------------------------------------------------------------
; Teeth for `fn-record-group-namep-rejects-a-leading-dot'
;   (implies (equal (car (fn-record-string-octets text)) 46)
;            (not (fn-record-group-namep text)))
(assert-event (equal (car (fn-record-string-octets ".fn")) 46))
(assert-event (not (equal (car (fn-record-string-octets "fn.test")) 46)))
(local
 (must-fail
  (defthm rst-leading-dot-without-hypothesis
    (not (fn-record-group-namep text)))))

; Teeth for `fn-record-group-namep-rejects-an-empty-component'
;   (implies (equal (fn-record-string-octets text)
;                   (append xs (cons 46 (cons 46 ys))))
;            (not (fn-record-group-namep text)))
(assert-event (equal (fn-record-string-octets "fn..test")
                     (append (fn-record-string-octets "fn")
                             (cons 46 (cons 46 (fn-record-string-octets "test"))))))
(local
 (must-fail
  (defthm rst-empty-component-without-hypothesis
    (implies (equal (fn-record-string-octets text) (append xs ys))
             (not (fn-record-group-namep text))))))

; Teeth for `fn-record-group-namep-rejects-a-trailing-dot'
;   (implies (equal (fn-record-string-octets text) (append xs (list 46)))
;            (not (fn-record-group-namep text)))
(assert-event (equal (fn-record-string-octets "fn.test.")
                     (append (fn-record-string-octets "fn.test") (list 46))))
(local
 (must-fail
  (defthm rst-trailing-dot-without-hypothesis
    (implies (equal (fn-record-string-octets text) (append xs ys))
             (not (fn-record-group-namep text))))))

; Teeth for `fn-record-group-namep-bounds-length-by-definition'
;   (implies (< *fn-record-max-group-name* (len (fn-record-string-octets text)))
;            (not (fn-record-group-namep text)))
(assert-event (< *fn-record-max-group-name*
                 (len (fn-record-string-octets *rst-overlong-name*))))
(local
 (must-fail
  (defthm rst-length-without-hypothesis
    (implies (<= 1 (len (fn-record-string-octets text)))
             (not (fn-record-group-namep text))))))
