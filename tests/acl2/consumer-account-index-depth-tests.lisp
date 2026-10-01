(in-package "ACL2")
(include-book "../../books/consumer-account-index-depth")

(defconst *cakdt-short* '(97 98))
(defconst *cakdt-long* (make-list 65 :initial-element 97))
(defconst *cakdt-trie* (fn-cai-put-octets *cakdt-short* :present nil))

;@positive-witness fn-cakd-put-preserves-domain
(assert-event
 (and (natp 64) (fn-cakd-domainp *cakdt-trie* 64)
      (<= (len '(99 100)) 64)
      (fn-cakd-domainp (fn-cai-put-octets '(99 100) :new *cakdt-trie*) 64)))
;@hyp-removal-witness fn-cakd-put-preserves-domain omitted=natural-depth
(assert-event
 (and (not (natp 3/2)) (fn-cakd-domainp nil 3/2) (<= (len '(97)) 3/2)
      (not (fn-cakd-domainp (fn-cai-put-octets '(97) :new nil) 3/2))))
;@hyp-removal-witness fn-cakd-put-preserves-domain omitted=maintained-domain
(assert-event
 (let ((bad '((:foreign . :value))))
  (and (natp 64) (not (fn-cakd-domainp bad 64)) (<= (len '(97)) 64)
       (not (fn-cakd-domainp (fn-cai-put-octets '(97) :new bad) 64)))))
;@hyp-removal-witness fn-cakd-put-preserves-domain omitted=path-bound
(assert-event
 (and (natp 64) (fn-cakd-domainp nil 64) (not (<= (len *cakdt-long*) 64))
      (not (fn-cakd-domainp (fn-cai-put-octets *cakdt-long* :new nil) 64))))

;@positive-witness fn-cakd-long-key-has-no-binding
(assert-event
 (and (natp 64) (fn-cakd-domainp *cakdt-trie* 64) (< 64 (len *cakdt-long*))
      (not (fn-cai-get-octets *cakdt-long* *cakdt-trie*))))
;@hyp-removal-witness fn-cakd-long-key-has-no-binding omitted=natural-depth
(assert-event
 (let ((trie (fn-cai-put-octets nil :present nil)))
  (and (not (natp -1)) (fn-cakd-domainp trie -1) (< -1 (len nil))
       (fn-cai-get-octets nil trie))))
;@hyp-removal-witness fn-cakd-long-key-has-no-binding omitted=maintained-domain
(assert-event
 (let ((trie (fn-cai-put-octets *cakdt-long* :present nil)))
  (and (natp 64) (not (fn-cakd-domainp trie 64)) (< 64 (len *cakdt-long*))
       (fn-cai-get-octets *cakdt-long* trie))))
;@hyp-removal-witness fn-cakd-long-key-has-no-binding omitted=long-key
(assert-event
 (and (natp 64) (fn-cakd-domainp *cakdt-trie* 64)
      (not (< 64 (len *cakdt-short*)))
      (fn-cai-get-octets *cakdt-short* *cakdt-trie*)))
