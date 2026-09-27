; Tests and teeth for the STARTTLS physical receive-prefix projection.
(in-package "ACL2")
(include-book "../../books/served-tls-prefix")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

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

(defun stp-consumed (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-served-counted-consumed (fn-served-step-counted conn octets fn-arena)))

; The command line is the complete plaintext prefix.  The bytes following it
; are retained for the TLS facility, and the whole-buffer served transition
; is exactly the prefix transition.
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).
(defconst *sr-arena* nil)
(bpr-lift fn-served-step 2)
(bpr-lift fn-served-step-counted 2)
(bpr-lift fn-served-step-counted-fast 2)
(bpr-lift stp-consumed 2)
(assert-event
 (equal (in-arena-stp-consumed *sr-arena* *stp-conn* *stp-together*)
        (len *stp-command*)))
(assert-event
 (equal (nthcdr (in-arena-stp-consumed *sr-arena* *stp-conn* *stp-together*)
                *stp-together*)
        *stp-client-hello-prefix*))
(assert-event
 (equal (append
         (take (in-arena-stp-consumed *sr-arena* *stp-conn* *stp-together*)
               *stp-together*)
         (nthcdr (in-arena-stp-consumed *sr-arena* *stp-conn* *stp-together*)
                 *stp-together*))
        *stp-together*))
(assert-event
 (equal (fn-served-counted-result
         (in-arena-fn-served-step-counted *sr-arena* *stp-conn* *stp-together*))
        (in-arena-fn-served-step *sr-arena* *stp-conn* *stp-together*)))
(assert-event
 (equal (in-arena-fn-served-step-counted-fast *sr-arena* *stp-conn* *stp-together*)
        (in-arena-fn-served-step-counted *sr-arena* *stp-conn* *stp-together*)))

; The full maintained invariant is necessary for correspondence.  This wire
; has the right fixed spine and scalar counters, but retains a non-octet.  The
; fast entry may execute safely; the total reference must reject it unchanged.
(defconst *stp-cheap-only-wire*
  (fn-wire-make-state :command '(300) 1 nil nil 0 510 1048576))
(defconst *stp-cheap-only-conn*
  (fn-served-make-conn *stp-cheap-only-wire*
                       (fn-served-conn-session *stp-conn*)
                       (fn-served-conn-archive *stp-conn*)
                       (fn-served-conn-config *stp-conn*)
                       (fn-served-conn-observation *stp-conn*)
                       (fn-served-conn-injection *stp-conn*)))
(assert-event (fn-wire-fast-statep *stp-cheap-only-wire*))
(assert-event (not (fn-wire-statep *stp-cheap-only-wire*)))
(local
 (must-fail
  (defthm stp-fast-equals-reference-without-full-invariant
    (equal (fn-served-step-counted-fast *stp-cheap-only-conn* '(65) fn-arena)
           (fn-served-step-counted *stp-cheap-only-conn* '(65) fn-arena)))))

; Teeth: before the line terminator every observed byte is still plaintext;
; with no configured TLS facility, STARTTLS is refused and the alleged hello
; bytes remain part of the ordinary served input rather than a TLS suffix.
(assert-event
 (equal (in-arena-stp-consumed *sr-arena* *stp-conn* (butlast *stp-command* 1))
        (len (butlast *stp-command* 1))))
(defconst *stp-no-tls-open*
  (fn-served-open nil *fn-nntp-max-initial-line-octets* 1048576
                  *stp-config* *stp-observation* *stp-observation*
                  (fn-auth-make-config nil nil nil nil)))
(assert-event
 (equal (in-arena-stp-consumed *sr-arena* (fn-served-result-conn *stp-no-tls-open*) *stp-together*)
        (len *stp-together*)))
