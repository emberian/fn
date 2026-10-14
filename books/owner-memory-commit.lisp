; The exact committed suffix of the real store-node I/O transition.
(in-package "ACL2")
(include-book "store-node")
(include-book "owner-memory-stored")
(local (in-theory (disable (tau-system))))
(local
 (defthm pin-commit-files-statep
  (implies (fn-sn-statep s) (fn-sf-statep (fn-sn-files s)))
  :hints (("Goal" :in-theory (enable fn-sn-statep)))))
(local (set-default-hints
 '((quote (:in-theory (e/d (fn-sn-io fn-sn-file-step fn-sf-start-frontier
                          fn-sf-frontier-file-result fn-sf-frontier-replace-result
                          fn-sf-frontier-dir-result fn-sf-record-file-result
                          fn-sf-record-link-result fn-sf-record-dir-result
                          fn-sf-recovery-barrier)
                         (fn-sn-statep fn-sf-statep fn-sn-update fn-sf-records
                          fn-sf-make-fields fn-sf-records-field fn-sfr-snoc)))))))
(defthm fn-sn-io-appends-only-the-committed-record
  (implies (fn-sn-statep s)
           (equal (fn-sf-records (fn-sn-files (fn-sn-io s operation result)))
                  (append (fn-sf-records (fn-sn-files s))
                          (if (and (equal operation :record-directory)
                                   (equal result :ok)
                                   (equal (fn-sf-phase (fn-sn-files s)) :record-attempted))
                              (list (fn-sf-record-candidate (fn-sn-files s)))
                            nil))))
  :rule-classes nil)

(local (set-default-hints nil))
(defthm fn-adm-stored-most-cache-valid-after-sn-io
 (implies (and (fn-sn-statep s)
               (fn-adm-stored-most-cache-validp cache (fn-sf-records (fn-sn-files s))))
  (fn-adm-stored-most-cache-validp cache
    (fn-sf-records (fn-sn-files (fn-sn-io s operation result)))))
 :hints (("Goal"
  :use (fn-sn-io-appends-only-the-committed-record
        (:instance fn-adm-stored-most-cache-valid-after-commit
          (records (fn-sf-records (fn-sn-files s)))
          (more (if (and (equal operation :record-directory) (equal result :ok)
                         (equal (fn-sf-phase (fn-sn-files s)) :record-attempted))
                    (list (fn-sf-record-candidate (fn-sn-files s))) nil))))
  :in-theory (theory 'minimal-theory))))
