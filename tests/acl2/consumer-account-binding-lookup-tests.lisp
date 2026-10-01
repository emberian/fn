(in-package "ACL2")
(include-book "../../books/consumer-account-binding-lookup")

(defconst *bcilt-long* (coerce (make-list 65 :initial-element #\a) 'string))
(defconst *bcilt-trie* (fn-cai-put-octets '(97) :intent nil))
;@positive-witness fn-bcp-intent-lookup-is-complete-reference
(assert-event
 (and (stringp "a") (fn-cakd-domainp *bcilt-trie* 64)
      (equal (fn-bcp-intent-lookup "a" *bcilt-trie*)
             (fn-cai-get-octets (fn-record-string-octets "a") *bcilt-trie*))))
; The string hypothesis is necessary: the old totalized reference can read
; an empty terminal for a non-string name; the bounded helper refuses that
; malformed name. This witness affirms the other retained hypothesis.
;@hyp-removal-witness fn-bcp-intent-lookup-is-complete-reference omitted=string-name
(assert-event
 (let ((trie (fn-cai-put-octets nil :terminal nil)))
  (and (not (stringp 7)) (fn-cakd-domainp trie 64)
       (not (equal (fn-bcp-intent-lookup 7 trie)
                   (fn-cai-get-octets (fn-record-string-octets 7) trie))))))
;@hyp-removal-witness fn-bcp-intent-lookup-is-complete-reference omitted=maintained-key-domain
(assert-event
 (let ((trie (fn-cai-put-octets (fn-record-string-octets *bcilt-long*) :foreign nil)))
  (and (stringp *bcilt-long*) (not (fn-cakd-domainp trie 64))
       (not (equal (fn-bcp-intent-lookup *bcilt-long* trie)
                   (fn-cai-get-octets (fn-record-string-octets *bcilt-long*) trie))))))
;@mutation-witness bounded-lookup-retains-long-config-name-without-a-binding
(assert-event
 (and (stringp *bcilt-long*) (fn-cakd-domainp *bcilt-trie* 64)
      (> (length *bcilt-long*) 64)
      (equal (fn-bcp-intent-lookup *bcilt-long* *bcilt-trie*)
             (fn-cai-get-octets (fn-record-string-octets *bcilt-long*) *bcilt-trie*))))
