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
           :in-theory (e/d (fn-sn-committed-recordp)
                           (fn-sn-finish-installs-exact-article-and-archive-pin
                            fn-sn-finish
                            fn-sn-completion-enabledp
                            fn-sn-completion-record
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-store-retention-event-p)))))

; These two projections are deliberately independent of the replay step.
; Article state is newest first; the Store journal is oldest first.
(defun fn-articles-msgid-stamps (articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (append (fn-articles-msgid-stamps (cdr articles))
              (list (cons (fn-article-msgid (car articles))
                          (fn-article-stamp (car articles)))))
    nil))

(defun fn-replay-article-record (record)
  (declare (xargs :guard t))
  (if (fn-stxa-p record)
      (fn-replay-composite-record record)
    record))

(defun fn-replay-article-eventp (record)
  (declare (xargs :guard t))
  (and (not (fn-store-retention-event-p record))
       (not (fn-stxe-p record))
       (not (fn-stxk-p record))))

(defun fn-replay-journal-article-stamps (records)
  (declare (xargs :guard t))
  (if (consp records)
      (if (fn-replay-article-eventp (car records))
          (cons (cons (fn-record-msgid (fn-replay-article-record (car records)))
                      (fn-record-stamp (fn-replay-article-record (car records))))
                (fn-replay-journal-article-stamps (cdr records)))
        (fn-replay-journal-article-stamps (cdr records)))
    nil))

(local
 (defthm fn-stamp-node-acceptance-statep
   (implies (fn-node-statep node)
            (fn-statep (fn-node-acceptance node)))
   :hints (("Goal" :in-theory (enable fn-node-statep)))))

(defthm fn-node-complete-installs-pending-stamp
  (implies (fn-node-pending-matchesp node txid generation)
           (equal
            (fn-article-stamp
             (fn-find-article
              (fn-pending-msgid (fn-state-pending (fn-node-acceptance node)))
              (fn-state-articles
               (fn-node-acceptance
                (fn-node-complete node txid generation :durable)))))
            (fn-pending-stamp (fn-state-pending (fn-node-acceptance node)))))
  :hints (("Goal" :use ((:instance fn-durable-completion-installs-exact-pending-article
                                  (s (fn-node-acceptance node))))
           :in-theory (e/d (fn-node-complete fn-node-pending-matchesp
                                            fn-article-from-pending)
                           (fn-durable-completion-installs-exact-pending-article
                            fn-accept-complete fn-find-article fn-node-statep
                            fn-statep))))
  :rule-classes nil)

(defthm fn-replay-apply-record-installs-the-stamp
  (let ((article (fn-replay-article-record record)))
    (implies (and (fn-node-statep node)
                  (fn-store-event-p record)
                  (fn-replay-article-eventp record)
                  (consp (fn-replay-apply-record node record)))
             (equal (fn-article-stamp
                     (fn-find-article
                      (fn-record-msgid article)
                      (fn-state-articles
                       (fn-node-acceptance
                        (fn-replay-apply-record node record)))))
                    (fn-record-stamp article))))
  :hints (("Goal" :do-not-induct t
           :in-theory
           (e/d (fn-replay-apply-record
                 fn-node-prepare fn-node-complete
                 fn-accept-prepare fn-accept-complete fn-install-pending
                 fn-article-from-pending fn-find-article)
                (fn-record-shape-vocabulary
                 fn-stxe-p fn-stxk-p fn-stxa-p
                 fn-store-retention-event-p))))
  :rule-classes nil)
