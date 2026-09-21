; Executable cases for the native AUTHINFO credential-file boundary.
(in-package "ACL2")
(include-book "../../books/native-auth-profile")

; These are the executable subjects the saved image reaches through the host
; wrapper.  Admission without Common Lisp compliance would not be deployment
; evidence.
(assert-event
 (equal (symbol-class 'fn-native-auth-load (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-native-auth-load nil (w state)) *t*))
(assert-event
 (equal (symbol-class 'fn-native-auth-parse-lines (w state))
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
  (fn-native-auth-load *fn-native-auth-test-file* t t nil nil))
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
     (fn-native-auth-load *fn-native-auth-test-file* t t t nil)))
   t)))

; Missing is an explicit observation and preserves the policy with no creds.
(assert-event
 (equal (fn-native-auth-load nil nil t nil nil)
        (list :accepted (fn-auth-make-config t nil nil nil))))

; Protected-only cannot become live until a real native TLS facility can
; deliver :tls-established.  File contents cannot weaken that prerequisite.
(assert-event
 (equal (fn-native-auth-load *fn-native-auth-test-file* t t t nil)
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
          t nil nil nil))
        :cleartext-credential))

; Each name and field has one meaning.  A later table/value never wins.
(assert-event
 (equal (fn-native-auth-result-reason
         (fn-native-auth-load
          (append *fn-native-auth-test-file* *fn-native-auth-test-file*)
          t nil nil nil))
        :duplicate-login))
(assert-event
 (equal (fn-native-auth-result-reason
         (fn-native-auth-load
          (fn-native-auth-test-lines
           '("[login.\"reader\"]" "posting = true" "posting = false"))
          t nil nil nil))
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
          t nil nil nil))
        :credential-shape))
