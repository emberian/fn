; Actual bounded intent lookup called by configuration preparation.
(in-package "ACL2")
(include-book "consumer-account-index-depth")
(include-book "records-shape")

(defun fn-bcp-intent-lookup (name trie)
 (declare (xargs :guard t))
 (and (stringp name) (<= (length name) 64)
      (fn-cai-get-octets (fn-record-string-octets name) trie)))

(local
 (defthm fn-bcp-string-octet-aux-length
  (equal (len (fn-record-string-octets-aux chars)) (len chars))
  :hints (("Goal" :induct (fn-record-string-octets-aux chars)
           :in-theory (enable fn-record-string-octets-aux)))))

(local
 (defthm fn-bcp-string-octet-length
  (implies (stringp name)
           (equal (len (fn-record-string-octets name)) (length name)))
  :hints (("Goal" :in-theory (enable fn-record-string-octets
                                    fn-record-string-octets-aux)))))

(defthm fn-bcp-intent-lookup-is-complete-reference
 (implies (and (stringp name) (fn-cakd-domainp trie 64))
          (equal (fn-bcp-intent-lookup name trie)
                 (fn-cai-get-octets (fn-record-string-octets name) trie)))
 :hints (("Goal" :use ((:instance fn-cakd-long-key-has-no-binding
                                  (depth 64) (name (fn-record-string-octets name))))
          :in-theory (e/d (fn-bcp-intent-lookup)
                           (fn-cai-get-octets fn-cakd-domainp
                            fn-cakd-long-key-has-no-binding)))))

(in-theory (disable fn-bcp-intent-lookup))
