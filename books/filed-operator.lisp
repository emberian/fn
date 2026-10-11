; fn: O1 packet 4, arm 2 (the operator post, `fn operator CONFIG post').
; The operator's decision (books/owner.lisp fn-own-operator-decision) has two
; injecting arms.  The fresh injection checks the CLI's groups equal to the
; injection decision's (fn-inj-decide over the operator's octets), so its
; record files as the served POST's does (P4-1,
; fn-o1-served-post-files-within-the-stored, books/filed-stored.lisp).  The
; reinjection arm keeps the CLI's groups over the octets the node already
; stores under the Message-ID; it is taken only when the node holds that
; Message-ID, and then the commit's existing-action check (the host's
; fnn-owner-attempt through fn-store-existing-action, books/store-intern.lisp)
; answers :duplicate or :conflict whatever payload and groups it carries, so
; no record with unchecked groups is ever appended.  A completion between the
; decision and the commit keeps that answer
; (fn-hma-a-completion-keeps-the-held-answer, books/held-message-id-answer.lisp).
; The subject is what the host's entry reads: host/owner-host.lisp
; fn-owner-operator-submit passes fn-own-operator-stored-octets as STORED.
(in-package "ACL2")

(include-book "owner-served-invariants")

;; Held Message-ID: the existing-action check answers :duplicate or :conflict.
(local
 (defthm o1-existing-action-of-a-held-msgid
  (implies (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))
           (member-equal (fn-store-existing-action msgid payload groups s fn-arena)
                         '(:duplicate :conflict)))
  :hints (("Goal" :in-theory (union-theories '(fn-store-existing-action member-equal)
                                             (theory 'minimal-theory))))))

;; The operator decision is the fresh injection unless the node holds the
;; article (the reinjection arm reads stored octets, :absent otherwise).
(local
 (defthm o1-reinjection-arm-has-a-held-msgid
  (let* ((stored (fn-own-operator-stored-octets o msgid fn-arena))
         (d (fn-own-operator-decision-of o msgid groups octets stored)))
    (implies (not (equal d (fn-inj-decide octets (fn-own-config o) (fn-own-clock o))))
             (or (not (fn-inj-injectedp d))
                 (fn-find-article (fn-record-octets-string msgid)
                                  (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store o))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-operator-decision-of fn-own-operator-decision fn-own-operator-stored-octets)
                                  (fn-inj-decide fn-inj-reinjectionp fn-handle-bytes fn-find-article
                                   fn-inj-injectedp fn-inj-refuse fn-inj-make-decision))))))

; KEYSTONE P4-2.  Every injecting operator decision over what the entry
; reads is the fresh injection at the owner's clock, or the node holds the
; Message-ID and the existing-action check answers :duplicate or :conflict
; for any payload and groups the commit carries.
(defthm fn-o1-operator-decision-is-fresh-or-held
  (let* ((stored (fn-own-operator-stored-octets o msgid fn-arena))
         (d (fn-own-operator-decision-of o msgid groups octets stored)))
    (implies (fn-inj-injectedp d)
             (or (equal d (fn-inj-decide octets (fn-own-config o) (fn-own-clock o)))
                 (member-equal
                  (fn-store-existing-action (fn-record-octets-string msgid)
                                            payload store-groups
                                            (fn-own-store o) fn-arena)
                  '(:duplicate :conflict)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-own-operator-decision-of fn-own-operator-stored-octets
                                      fn-inj-decide fn-inj-injectedp fn-store-existing-action
                                      fn-find-article fn-record-octets-string)
           :use (o1-reinjection-arm-has-a-held-msgid
                 (:instance o1-existing-action-of-a-held-msgid
                            (msgid (fn-record-octets-string msgid))
                            (groups store-groups) (s (fn-own-store o)))))))
