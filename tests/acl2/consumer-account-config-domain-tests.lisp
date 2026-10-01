(in-package "ACL2")
(include-book "../../books/consumer-account-config-domain")
(local (include-book "consumer-account-config-preparation-tests"))

(defconst *bcpdt-bad-trie* (fn-cai-put-octets (make-list 65 :initial-element 97) :foreign nil))
(defconst *bcpdt-before* (fn-cp-nth 1 (fn-bcp-expect *bcpt-start* '(97) :row)))
(defconst *bcpdt-event* (fn-bcpt-event '(97) 0 1 *fn-cab-zero-principal* 1))
;@positive-witness fn-bcp-begin-establishes-intent-domain
(assert-event (fn-cakd-domainp (fn-cp-nth 7 (fn-bcp-begin '(65) *bcpt-base* 3)) 64))
;@positive-witness fn-bcp-stage-preserves-intent-domain
(assert-event
 (and (fn-cakd-domainp (fn-cp-nth 7 *bcpdt-before*) 64)
      (equal (fn-cp-nth 0 (fn-bcp-stage *bcpdt-before* *bcpdt-event*)) :ok)
      (fn-cakd-domainp (fn-cp-nth 7 (fn-cp-nth 1 (fn-bcp-stage *bcpdt-before* *bcpdt-event*))) 64)))
;@corrupted-state-witness fn-bcp-stage-preserves-intent-domain omitted=intent-domain
(assert-event
 (let ((bad (update-nth 7 *bcpdt-bad-trie* *bcpdt-before*)))
  (and (not (fn-cakd-domainp (fn-cp-nth 7 bad) 64))
       (equal (fn-cp-nth 0 (fn-bcp-stage bad *bcpdt-event*)) :ok)
       (not (fn-cakd-domainp (fn-cp-nth 7 (fn-cp-nth 1 (fn-bcp-stage bad *bcpdt-event*))) 64)))))
;@positive-witness fn-bcp-tick-preserves-intent-domain
(assert-event
 (and (fn-cakd-domainp (fn-cp-nth 7 *bcpt-ready*) 64)
      (equal (fn-cp-nth 0 (fn-bcp-tick *bcpt-ready* nil)) :ready)
      (fn-cakd-domainp (fn-cp-nth 7 (fn-cp-nth 1 (fn-bcp-tick *bcpt-ready* nil))) 64)))
;@corrupted-state-witness fn-bcp-tick-preserves-intent-domain omitted=intent-domain
(assert-event
 (let ((bad (update-nth 7 *bcpdt-bad-trie* *bcpt-ready*)))
  (and (not (fn-cakd-domainp (fn-cp-nth 7 bad) 64))
       (not (fn-cakd-domainp (fn-cp-nth 7 (fn-cp-nth 1 (fn-bcp-tick bad nil))) 64)))))
;@positive-witness fn-bcp-expect-and-seal-preserve-intent-domain
(assert-event
 (and (fn-cakd-domainp (fn-cp-nth 7 *bcpt-start*) 64)
      (fn-cakd-domainp (fn-cp-nth 7 (fn-cp-nth 1 (fn-bcp-expect *bcpt-start* '(97) :row))) 64)
      (fn-cakd-domainp (fn-cp-nth 7 (fn-cp-nth 1 (fn-bcp-seal *bcpt-start*))) 64)))
;@corrupted-state-witness fn-bcp-expect-and-seal-preserve-intent-domain omitted=intent-domain
(assert-event
 (let ((bad (update-nth 7 *bcpdt-bad-trie* *bcpt-start*)))
  (and (not (fn-cakd-domainp (fn-cp-nth 7 bad) 64))
       (not (fn-cakd-domainp (fn-cp-nth 7 (fn-cp-nth 1 (fn-bcp-expect bad '(97) :row))) 64))
       (not (fn-cakd-domainp (fn-cp-nth 7 (fn-cp-nth 1 (fn-bcp-seal bad))) 64)))))
