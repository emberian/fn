; Remote query metadata on the CP kernel. Durable codec and authenticated
; host dispatch remain separate obligations (CNS-011 / PRF-1125).
(in-package "ACL2")
(include-book "consumer-position")

(defthm fn-cp-remote-register-installs-exact-definition
  (let ((d (fn-cp-remote-register s max caller consumer query qver view groups account)))
    (implies (equal (car d) :write)
             (equal (fn-cp-find consumer
                                (fn-cp-nth 5 (fn-cp-apply s (cadr d))))
                    (append (fn-cp-entry consumer caller query qver view
                                         (fn-cp-nth 4 s) 0)
                            (list groups account)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-cp-remote-register fn-cp-register-within fn-cp-register
                 fn-cp-apply fn-cp-event-entry fn-cp-find fn-cp-entry
                 fn-cp-state fn-cp-nth)
                (fn-cp-idp fn-cp-remote-metadatap fn-cp-remove)))))

(defthm fn-cp-remote-rebase-installs-exact-definition
  (let ((d (fn-cp-remote-rebase s caller consumer query qver view groups account)))
    (implies (equal (car d) :write)
             (equal (fn-cp-find consumer
                                (fn-cp-nth 5 (fn-cp-apply s (cadr d))))
                    (append (fn-cp-entry consumer caller query qver view
                                         (fn-cp-nth 4 s) 0)
                            (list groups account)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-cp-remote-rebase fn-cp-rebase fn-cp-apply fn-cp-event-entry
                 fn-cp-find fn-cp-entry fn-cp-state fn-cp-nth)
                (fn-cp-idp fn-cp-remote-metadatap fn-cp-remove)))))

(defthm fn-cp-remote-ack-preserves-exact-definition
  (let* ((entry (fn-cp-find (fn-cp-nth 3 cursor) (fn-cp-nth 5 s)))
         (d (fn-cp-ack s caller qver view cursor)))
    (implies (and (equal (len entry) 10) (equal (car d) :write))
             (let ((after (fn-cp-find (fn-cp-nth 3 cursor)
                                      (fn-cp-nth 5 (fn-cp-apply s (cadr d))))))
               (and (equal (fn-cp-nth 7 after) (fn-cp-nth 9 cursor))
                    (equal (fn-cp-nth 8 after) (fn-cp-nth 8 entry))
                    (equal (fn-cp-nth 9 after) (fn-cp-nth 9 entry))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-cp-ack fn-cp-apply fn-cp-entry-with-ack fn-cp-scope-matchp
                 fn-cp-find fn-cp-entry fn-cp-state fn-cp-nth)
                (fn-cp-idp fn-cp-cursorp fn-cp-remove)))))
