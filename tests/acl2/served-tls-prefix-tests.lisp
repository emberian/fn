; Tests and teeth for the STARTTLS physical receive-prefix projection.
(in-package "ACL2")
(include-book "../../books/served-tls-prefix")

(defconst *stp-groups* (list (fn-nntp-string-octets "fn.test")))
(defconst *stp-config*
  (fn-inj-make-config t (fn-nntp-string-octets "fn.example.invalid")
                      *stp-groups* 1048576))
(defconst *stp-observation*
  (fn-clock-observation 1000000 843004800000 500 t))
(defconst *stp-auth* (fn-auth-make-config nil nil t nil))
(defconst *stp-open*
  (fn-served-open nil *fn-nntp-max-initial-line-octets* 1048576
                  *stp-config* *stp-observation* *stp-observation* *stp-auth*))
(defconst *stp-conn* (fn-served-result-conn *stp-open*))
(defconst *stp-command*
  (append (fn-record-string-octets "STARTTLS") '(13 10)))
(defconst *stp-client-hello-prefix* '(22 3 1 0 5 1 0 0 1 0))
(defconst *stp-together* (append *stp-command* *stp-client-hello-prefix*))

; The command line is the complete plaintext prefix.  The bytes following it
; are retained for the TLS facility, and the whole-buffer served transition
; is exactly the prefix transition.
(assert-event
 (equal (fn-served-tls-consumed *stp-conn* *stp-together*)
        (len *stp-command*)))
(assert-event
 (equal (nthcdr (fn-served-tls-consumed *stp-conn* *stp-together*)
                *stp-together*)
        *stp-client-hello-prefix*))
(assert-event
 (equal (append
         (take (fn-served-tls-consumed *stp-conn* *stp-together*)
               *stp-together*)
         (nthcdr (fn-served-tls-consumed *stp-conn* *stp-together*)
                 *stp-together*))
        *stp-together*))
(assert-event
 (equal (fn-served-step
         *stp-conn*
         (take (fn-served-tls-consumed *stp-conn* *stp-together*)
               *stp-together*))
        (fn-served-step *stp-conn* *stp-together*)))

; Teeth: before the line terminator every observed byte is still plaintext;
; with no configured TLS facility, STARTTLS is refused and the alleged hello
; bytes remain part of the ordinary served input rather than a TLS suffix.
(assert-event
 (equal (fn-served-tls-consumed *stp-conn* (butlast *stp-command* 1))
        (len (butlast *stp-command* 1))))
(defconst *stp-no-tls-open*
  (fn-served-open nil *fn-nntp-max-initial-line-octets* 1048576
                  *stp-config* *stp-observation* *stp-observation*
                  (fn-auth-make-config nil nil nil nil)))
(assert-event
 (equal (fn-served-tls-consumed
         (fn-served-result-conn *stp-no-tls-open*) *stp-together*)
        (len *stp-together*)))
