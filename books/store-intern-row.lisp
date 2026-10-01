; Exact modern served producer; body and guard unchanged.
(in-package "ACL2")
(include-book "catalog-record")

(defun fn-intern-row-at (w keyring generation h)
  (declare (xargs :guard (and (fn-record-p w) (fn-prin-keyringp keyring)
                              (natp generation) (natp h))
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let ((bytes (fn-record-payload w)))
    (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                  (fn-record-generation w) (fn-record-msgid w) h
                  (fn-record-groups w) (fn-record-obligation-id w)
                  (fn-record-content-subject w) (fn-record-release-evidence w)
                  (fn-record-charge w) (fn-record-stamp w)
                  (fn-held-facts-of bytes)
                  (fn-held-context-of bytes keyring generation)
                  nil nil)))
