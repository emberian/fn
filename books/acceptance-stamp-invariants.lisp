; T2a: the host-called constructor and durable stamp carrier.
(in-package "ACL2")
(include-book "store-node-invariants")

; This projects the stamp conjunct of the actual durable completion theorem.
; The work is in fn-sn-actual-durable-completion-installs-record, whose proof
; follows the live node completion and whose predicate now binds the stamp.
(defthm fn-sn-finish-installs-the-stamp-the-record-carries
  (implies (and (fn-sn-completion-enabledp s)
                (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                (not (fn-stxe-p (fn-sn-completion-record s)))
                (not (fn-stxk-p (fn-sn-completion-record s)))
                (not (fn-stxa-p (fn-sn-completion-record s))))
           (equal (fn-article-stamp
                   (fn-find-article
                    (fn-record-msgid (fn-sn-completion-record s))
                    (fn-state-articles
                     (fn-node-acceptance (fn-sn-node (fn-sn-finish s))))))
                  (fn-record-stamp (fn-sn-completion-record s))))
  :hints (("Goal" :use (fn-sn-finish-installs-exact-article-and-archive-pin)
           :in-theory (disable fn-sn-finish
                               fn-sn-completion-enabledp
                               fn-sn-completion-record
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-store-retention-event-p))))
