; Exact account-row trie component: reachable positives and literal removal
; witnesses. This is not an authorization/funding/publication qualification.
(in-package "ACL2")
(include-book "../../books/consumer-account-index")
(defconst *cait-a* '(:account (97) 11 t (1 2 3)))
(defconst *cait-ab* '(:account (97 98) 12 t (4 5 6)))
(defconst *cait-a-next* '(:account (97) 11 t (7 8 9)))
(defconst *cait-root*
  (fn-cai-put-octets '(97) *cait-a*
                     (fn-cai-put-octets '(97 98) *cait-ab* nil)))

; Complete literal antecedent/conclusion: exact key, and prefix name remains
; a separate terminal. Updating a descriptor preserves the other whole row.
(assert-event
 (and (fn-cbor-octet-listp '(97)) (fn-cbor-octet-listp '(97 98))
      (not (equal '(97) '(97 98)))
      (equal (fn-cai-get-octets '(97) *cait-root*) *cait-a*)
      (equal (fn-cai-get-octets '(97 98) *cait-root*) *cait-ab*)
      (equal (fn-cai-get-octets '(97)
                (fn-cai-put-octets '(97) *cait-a-next* *cait-root*)) *cait-a-next*)
      (equal (fn-cai-get-octets '(97 98)
                (fn-cai-put-octets '(97) *cait-a-next* *cait-root*))
             (if (equal '(97 98) '(97)) *cait-a-next*
               (fn-cai-get-octets '(97 98) *cait-root*)))))

(assert-event
 (let ((name (make-list 64 :initial-element 255)))
   (and (fn-cai-namep name 64) (fn-cbor-octet-listp name)
        (equal (fn-cai-lookup name 64 (fn-cai-put-octets name *cait-a* nil))
               *cait-a*)
        (equal (fn-cai-get-octets name (fn-cai-put-octets name *cait-a* nil))
               (fn-midx-get-chars (fn-cai-key name)
                 (fn-midx-put-chars (fn-cai-key name) *cait-a* nil))))))

; Both octet-key domain hypotheses are necessary for the total fallback:
; each removal checks the other domain, different keys and failed conclusion.
(assert-event
 (and (fn-cbor-octet-listp '(0)) (not (fn-cbor-octet-listp '(256)))
      (not (equal '(256) '(0)))
      (not (equal (equal (fn-cai-key '(256)) (fn-cai-key '(0)))
                   (equal '(256) '(0))))
      (not (equal (fn-cai-get-octets '(0)
                         (fn-cai-put-octets '(256) *cait-a* nil))
                   (if (equal '(0) '(256)) *cait-a* (fn-cai-get-octets '(0) nil))))))
(assert-event
 (and (not (fn-cbor-octet-listp '(256))) (fn-cbor-octet-listp '(0))
      (not (equal (fn-cai-get-octets '(256)
                         (fn-cai-put-octets '(0) *cait-a* nil))
                   (if (equal '(256) '(0)) *cait-a*
                     (fn-cai-get-octets '(256) nil))))))

; Invalid/empty/overlong native names never get authorized through fallback
; or prefix truncation. The raw index itself supports full arbitrary keys.
(assert-event
 (let ((long (make-list 65 :initial-element 97)))
   (and (not (fn-cai-namep '(256) 64)) (not (fn-cai-namep nil 64))
        (not (fn-cai-namep long 64))
        (not (fn-cai-lookup '(256) 64 (fn-cai-put-octets '(0) *cait-a* nil)))
        (not (fn-cai-lookup long 64 (fn-cai-put-octets long *cait-a* nil)))
        (equal (fn-cai-get-octets long (fn-cai-put-octets long *cait-a* nil))
               *cait-a*))))
