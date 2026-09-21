(in-package "ACL2")
(include-book "../../books/hybrid-store")
(include-book "std/testing/assert-equal" :dir :system)

(defconst *hst-principal* (repeat 32 7))
(defconst *hst-ed-key* (repeat 32 11))
(defconst *hst-ml-key* (repeat 1952 13))
(defconst *hst-keys* (list (cons :ed25519 *hst-ed-key*)
                           (cons :ml-dsa-65 *hst-ml-key*)))
(defconst *hst-signatures* (list (cons :ed25519 (repeat 64 17))
                                 (cons :ml-dsa-65 (repeat 3309 19))))
(defconst *hst-source* '(65 13 10))
(defconst *hst-record*
  (fn-record-make 2 3 4 "<hybrid@example.invalid>" *hst-source* '("example")
                  "obligation" "subject" "release" 3))
(defconst *hst-record-octets* (fn-record-encode *hst-record*))

(assert! (fn-stxk-p
          (fn-hsig-keyring-event 1 2 3 4 *hst-principal* *hst-keys*)))

(defconst *hst-event*
  (fn-hsig-authorized-article-event
   2 3 4 4 "<hybrid@example.invalid>"
   (fn-record-string-octets "subject") *hst-record-octets*
   *hst-principal* *hst-keys* *hst-source* *hst-signatures* *hst-ml-key*
   :verified :verified))

(assert! (fn-stxa-bindsp *hst-event*))
(assert-equal
 (fn-hsig-authorized-article-event
  2 3 4 4 "<hybrid@example.invalid>"
  (fn-record-string-octets "subject") *hst-record-octets*
  *hst-principal* *hst-keys* *hst-source* *hst-signatures* *hst-ml-key*
  :verified :invalid)
 nil)
(assert-equal
 (fn-hsig-authorized-article-event
  2 3 4 4 "<hybrid@example.invalid>"
  (fn-record-string-octets "subject") *hst-record-octets*
  *hst-principal* *hst-keys* '(65 13 10 0) *hst-signatures* *hst-ml-key*
  :verified :verified)
 nil)

