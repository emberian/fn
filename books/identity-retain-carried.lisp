; fn: a signed POST's (identity event's) retention admission from the carried
; obligation-id trie (Q5b's residual, served-costs-3).
;
; The profile of the signed POST at N = 100,000 stored articles (sb-sprof on
; the prof image, planning/evidence/served-costs-3-2026-09-29/) put 35
; percent of the owner's samples under fn-retain-known-id-scanp, all of it
; from fn-replay-apply-record -> fn-node-prepare: an identity event (a
; composite signed article) is staged and gated by applying its record to the
; store's node three times per POST (fn-ccar-sn-prepare-identity, and the
; completion's fn-ccar-completion-core-enabledp and fn-ccar-sn-finish-enabled),
; and each application's fn-node-prepare scans every pin and release twice
; (fn-retain-admissiblep, then fn-retain-admit's own test).  The unsigned POST
; already answers that admission from the carried trie
; (books/post-retain-carried.lisp fn-prc-node-prepare).  This book is the
; same substitution for the record application: fn-irc-node-prepare is
; fn-node-prepare with the admission through fn-prc-admissiblep and the admit
; built directly, and fn-irc-apply-record is fn-replay-apply-record with it.
; Each is proved EQUAL to its reference under (fn-prc-carryp carry), the
; carry's only premise, which names no owner state.

(in-package "ACL2")
(include-book "post-retain-carried")

(defun fn-irc-node-prepare (s generation msgid payload groups
                              obligation-id subject evidence charge stamp carry)
  (declare (xargs :guard (fn-node-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-node-statep s)) :exec nil)
      s
    (let ((retention (fn-node-retention s)))
      (if (not (fn-prc-admissiblep retention obligation-id subject :archive
                                   evidence charge carry))
          s
        (let ((next-acceptance
               (fn-accept-prepare (fn-node-acceptance s)
                                  generation msgid payload groups stamp)))
          (if (equal next-acceptance (fn-node-acceptance s))
              s
            (fn-node-make-state
             next-acceptance
             retention
             (fn-node-make-stage
              msgid generation obligation-id subject evidence charge
              (fn-retain-make-state
               (fn-retain-capacity retention)
               (+ (fn-retain-reserved retention) charge)
               (cons (fn-retain-make-obligation obligation-id subject :archive
                                                evidence charge)
                     (fn-retain-pins retention))
               (fn-retain-releases retention)))
             (fn-node-bindings s))))))))

(encapsulate ()
  (local (in-theory (enable (tau-system)))) ; tau-cost: as fn-prc-node-prepare's
  (verify-guards fn-irc-node-prepare
    :hints (("Goal" :in-theory (enable fn-node-statep)))))

(defthm fn-irc-node-prepare-is-node-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-node-prepare s generation msgid payload groups
                                       obligation-id subject evidence charge
                                       stamp carry)
                  (fn-node-prepare s generation msgid payload groups
                                   obligation-id subject evidence charge stamp)))
  :hints (("Goal" :in-theory (e/d (fn-irc-node-prepare fn-node-prepare
                                   fn-retain-admit)
                                  (fn-node-statep fn-retain-admissiblep
                                   fn-accept-prepare fn-retain-make-state
                                   fn-retain-make-obligation)))))

(defun fn-irc-apply-record (node record carry)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record)
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (if (fn-store-retention-event-p record)
      (fn-replay-apply-retention-event node record)
    (if (or (fn-stxe-p record) (fn-stxk-p record) (fn-cpe-eventp record)
            (fn-th-topic-eventp record))
        (if (and (or (fn-cpe-eventp record) (fn-th-topic-eventp record))
                 (not (null (fn-node-stage node))))
            nil
          (fn-replay-apply-identity-neutral node record))
      ; Unreachable-in-composition: journal replay enters with no pending
      ; transaction.  A standalone article step refuses a staged node, lest a
      ; record with matching coordinates complete that different article.
      (if (not (null (fn-node-stage node)))
          nil
      (let* ((article (if (fn-hstxa-p record)
                          (fn-replay-composite-held record)
                        record))
             (advanced (fn-replay-advance-txid node (fn-store-event-txid record))))
      (if (not (equal (fn-state-next-txid (fn-node-acceptance advanced))
                      (fn-store-event-txid record)))
          nil
        (if (not (fn-held-p article)) nil
          (let ((prepared
               (fn-irc-node-prepare advanced
                                (fn-record-generation article)
                                (fn-record-msgid article)
                                (fn-record-payload article)
                                (fn-record-groups article)
                                (fn-record-obligation-id article)
                                (fn-record-content-subject article)
                                (fn-record-release-evidence article)
                                (fn-record-charge article)
                                (fn-record-stamp article)
                                carry)))
          (if (not (fn-node-pending-matchesp
                    prepared
                    (fn-record-txid article)
                    (fn-record-generation article)))
              nil
            (fn-node-complete prepared
                              (fn-record-txid article)
                              (fn-record-generation article)
                              :durable))))))))))

(defthm fn-irc-apply-record-is-replay-apply-record
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-apply-record node record carry)
                  (fn-replay-apply-record node record)))
  :hints (("Goal" :in-theory (e/d (fn-irc-apply-record fn-replay-apply-record)
                                  (fn-irc-node-prepare fn-node-prepare
                                   fn-store-event-p fn-record-p fn-stxe-p
                                   fn-stxk-p fn-stxa-p fn-store-retention-event-p
                                   fn-cpe-eventp fn-th-topic-eventp
                                   fn-replay-apply-retention-event
                                   fn-replay-apply-identity-neutral
                                   fn-replay-advance-txid fn-node-complete
                                   fn-node-pending-matchesp fn-held-p)))))

(verify-guards fn-irc-apply-record
  :hints (("Goal" :in-theory (disable fn-store-event-p fn-record-p fn-stxe-p
                                      fn-stxk-p fn-stxa-p
                                      fn-store-retention-event-p fn-cpe-eventp
                                      fn-replay-composite-record))))

(in-theory (disable fn-irc-node-prepare fn-irc-apply-record))
