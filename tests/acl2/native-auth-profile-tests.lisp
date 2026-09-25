; Executable cases for the native AUTHINFO credential-file boundary.
(in-package "ACL2")
(include-book "../../books/native-auth-profile")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; These are the executable subjects the saved image reaches through the host
; wrapper.  Admission without Common Lisp compliance would not be deployment
; evidence.
(assert-event
 (equal (symbol-class 'fn-native-auth-load (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-native-auth-load nil (w state)) *t*))
(assert-event
 (equal (symbol-class 'fn-native-auth-parse-lines (w state))
        :common-lisp-compliant))
(assert-event
 (equal (symbol-class 'fn-native-auth-login-namep (w state))
        :common-lisp-compliant))

(defun fn-native-auth-test-lines (lines)
  (if (consp lines)
      (append (fn-record-string-octets (car lines)) (list 10)
              (fn-native-auth-test-lines (cdr lines)))
    nil))

(defconst *fn-native-auth-test-principal*
  "0000000000000000000000000000000000000000000000000000000000000000")
(defconst *fn-native-auth-test-salt*
  "00000000000000000000000000000000")
(defconst *fn-native-auth-test-digest*
  "1111111111111111111111111111111111111111111111111111111111111111")
(defconst *fn-native-auth-test-file*
  (fn-native-auth-test-lines
   (list "# canonical writer output"
         "[login.\"reader\"]"
         (concatenate 'string "principal = \"" *fn-native-auth-test-principal* "\"")
         (concatenate 'string "salt = \"" *fn-native-auth-test-salt* "\"")
         (concatenate 'string "digest = \"" *fn-native-auth-test-digest* "\"")
         "posting = false")))

(defconst *fn-native-auth-test-result*
  (fn-native-auth-load *fn-native-auth-test-file* t t nil nil 128))
(defconst *fn-native-auth-test-config*
  (fn-native-auth-result-config *fn-native-auth-test-result*))

(assert-event (equal (fn-native-auth-result-status *fn-native-auth-test-result*)
                     :accepted))
(assert-event (fn-auth-configp *fn-native-auth-test-config*))
(assert-event (fn-auth-config-requiredp *fn-native-auth-test-config*))
(assert-event (equal (len (fn-auth-config-creds *fn-native-auth-test-config*)) 1))
(assert-event (not (fn-auth-cred-postingp
                    (car (fn-auth-config-creds *fn-native-auth-test-config*)))))

; Reachable witness for fn-native-auth-load-accepted-pins-policy: required is
; true in the accepted host-installed config.  Its acceptance hypothesis has
; teeth: protected-only with no TLS is refused, result-config falls back to
; the open policy, and therefore does not carry the requested required bit.
(assert-event
 (equal (fn-auth-config-requiredp *fn-native-auth-test-config*) t))
(assert-event
 (not
  (equal
   (fn-auth-config-requiredp
    (fn-native-auth-result-config
     (fn-native-auth-load *fn-native-auth-test-file* t t t nil 128)))
   t)))

; Missing is an explicit observation and preserves the policy with no creds.
(assert-event
 (equal (fn-native-auth-load nil nil t nil nil 128)
        (list :accepted (fn-auth-make-config t nil nil nil))))

; Protected-only cannot become live until a real native TLS facility can
; deliver :tls-established.  File contents cannot weaken that prerequisite.
(assert-event
 (equal (fn-native-auth-load *fn-native-auth-test-file* t t t nil 128)
        '(:refused :protected-transport-unavailable)))

; Legacy cleartext is refused by name rather than read or migrated.
(assert-event
 (equal (fn-native-auth-result-reason
         (fn-native-auth-load
          (fn-native-auth-test-lines
           '("[login.\"old\"]" "secret = \"do-not-read\""
             "principal = \"0000000000000000000000000000000000000000000000000000000000000000\""
             "salt = \"00000000000000000000000000000000\""
             "digest = \"1111111111111111111111111111111111111111111111111111111111111111\""
             "posting = true"))
          t nil nil nil 128))
        :cleartext-credential))

; Each name and field has one meaning.  A later table/value never wins.
(assert-event
 (equal (fn-native-auth-result-reason
         (fn-native-auth-load
          (append *fn-native-auth-test-file* *fn-native-auth-test-file*)
          t nil nil nil 128))
        :duplicate-login))
(assert-event
 (equal (fn-native-auth-result-reason
         (fn-native-auth-load
          (fn-native-auth-test-lines
           '("[login.\"reader\"]" "posting = true" "posting = false"))
          t nil nil nil 128))
        :duplicate-field))

; Widths are ACL2's.  A short salt never reaches the served verifier.
(assert-event
 (equal (fn-native-auth-result-reason
         (fn-native-auth-load
          (fn-native-auth-test-lines
           '("[login.\"reader\"]"
             "principal = \"0000000000000000000000000000000000000000000000000000000000000000\""
             "salt = \"00\""
             "digest = \"1111111111111111111111111111111111111111111111111111111111111111\""
             "posting = true"))
          t nil nil nil 128))
        :credential-shape))

; The table key is the exact unescaped canonical writer subset.  Quote and
; backslash are valid NNTP token octets but not values bin/fn's toml_quote can
; emit, so accepting either would give the native reader a second registry
; grammar that the operator cannot read back.
(assert-event
 (equal (fn-native-auth-result-reason
         (fn-native-auth-load
          (fn-native-auth-test-lines
           (list "[login.\"bad\"name\"]"
                 (concatenate 'string "principal = \"" *fn-native-auth-test-principal* "\"")
                 (concatenate 'string "salt = \"" *fn-native-auth-test-salt* "\"")
                 (concatenate 'string "digest = \"" *fn-native-auth-test-digest* "\"")
                 "posting = false"))
          t nil nil nil 128))
        :table))
(assert-event
 (equal (fn-native-auth-result-reason
         (fn-native-auth-load
          (fn-native-auth-test-lines
           (list "[login.\"bad\\name\"]"
                 (concatenate 'string "principal = \"" *fn-native-auth-test-principal* "\"")
                 (concatenate 'string "salt = \"" *fn-native-auth-test-salt* "\"")
                 (concatenate 'string "digest = \"" *fn-native-auth-test-digest* "\"")
                 "posting = false"))
          t nil nil nil 128))
        :table))
(assert-event
 (fn-native-auth-login-namep '(33 126)))

; A conventional newline-terminated file has one line per LF, with no extra
; line attributed to the parser's terminal empty segment.  Exercise both
; sides of the exact 1,024-line ceiling.
(assert-event
 (equal (fn-native-auth-result-status
         (fn-native-auth-load
          (make-list (fn-native-auth-max-lines 128) :initial-element 10)
          t nil nil nil 128))
        :accepted))
(assert-event
 (equal (fn-native-auth-result-reason
         (fn-native-auth-load
          (make-list (1+ (fn-native-auth-max-lines 128)) :initial-element 10)
          t nil nil nil 128))
        :bounds-or-encoding))

; D27, PRF-102: the credential count is the operator's.  K distinct
; canonical credentials, "u1" .. "uK".
(defun fn-native-auth-test-creds (k)
  (declare (xargs :mode :program))
  (if (zp k) nil
    (append (fn-native-auth-test-creds (1- k))
            (list (concatenate 'string "[login.\"u"
                               (coerce (explode-nonnegative-integer k 10 nil) 'string)
                               "\"]")
                  (concatenate 'string "principal = \"" *fn-native-auth-test-principal* "\"")
                  (concatenate 'string "salt = \"" *fn-native-auth-test-salt* "\"")
                  (concatenate 'string "digest = \"" *fn-native-auth-test-digest* "\"")
                  "posting = false"
                  ""))))
(defconst *fn-native-auth-test-129*
  (fn-native-auth-test-lines (fn-native-auth-test-creds 129)))
; Above the old cap: 129 credentials load under a profile of 129 (or the
; default 2^20), and are refused by name under 128, the pre-D27 figure.
(assert-event
 (equal (len (fn-auth-config-creds
              (fn-native-auth-result-config
               (fn-native-auth-load *fn-native-auth-test-129* t nil nil nil 129))))
        129))
(assert-event
 (equal (fn-native-auth-result-status
         (fn-native-auth-load *fn-native-auth-test-129* t nil nil nil 1048576))
        :accepted))
(assert-event
 (equal (fn-native-auth-result-reason
         (fn-native-auth-load *fn-native-auth-test-129* t nil nil nil 128))
        :too-many-credentials))
; Exactly at the bound: two credentials under 2 accepted, under 1 refused.
(assert-event
 (equal (fn-native-auth-result-status
         (fn-native-auth-load (fn-native-auth-test-lines (fn-native-auth-test-creds 2))
                              t nil nil nil 2))
        :accepted))
(assert-event
 (equal (fn-native-auth-result-reason
         (fn-native-auth-load (fn-native-auth-test-lines (fn-native-auth-test-creds 2))
                              t nil nil nil 1))
        :too-many-credentials))
; The parser keystone's hypothesis on the credentials already collected is
; needed: two collected, bound 1, no more lines -- accepted with two.
(must-fail
 (defthm fn-native-auth-test-parse-without-collected-bound
   (<= (len (fn-ncfg-second (fn-native-auth-parse-lines nil nil nil '(a b) 1)))
       1)
   :rule-classes nil))
