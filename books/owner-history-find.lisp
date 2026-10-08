; The redecision entry reads only the synchronized, carried memory history.
(in-package "ACL2")
(include-book "owner-history-carried")
(include-book "history-served-find")
(include-book "store-octet-entry")

(defun fn-owner-key-statement-redecide-find (msgid fn-hist state)
  (declare (xargs :stobjs (fn-hist state)
                  :guard (and (boundp-global 'fn-owner state)
                              (fn-cbor-octet-listp msgid))))
  (mv-let (fn-hist state)
      (fn-host-hist-sync (fn-owner-store state) fn-hist state)
    (mv nil (fn-hist-key-statement (fn-store-octets->string msgid) fn-hist)
        fn-hist state)))

(defthm fn-owner-key-statement-redecide-find-is-reference
  (implies (fn-hist-of-storep
            (mv-nth 0 (fn-host-hist-sync (fn-owner-store st) hist st))
            (fn-owner-store st))
           (equal (mv-nth 1 (fn-owner-key-statement-redecide-find msgid hist st))
                  (fn-ks-find-statement
                   (fn-store-octets->string msgid)
                   (fn-sf-records (fn-sn-files (fn-owner-store st))))))
  :hints (("Goal" :in-theory '(fn-owner-key-statement-redecide-find
                               fn-hist-key-statement-is-store-reader))))

(defthm fn-owner-key-statement-redecide-find-preserves-state
  (equal (mv-nth 3 (fn-owner-key-statement-redecide-find msgid hist st)) st)
  :hints (("Goal" :in-theory '(fn-owner-key-statement-redecide-find
                               fn-host-hist-sync-preserves-state))))

(in-theory (disable fn-owner-key-statement-redecide-find))
