; fn: a local consumer bound to an account (PRF-234, CNS-006;
; specs/consumer-progress.md "Bound consumers").
;
; The local consumer (books/consumer-owner-local.lisp) runs over the owner's
; 0600 control socket as the one local principal, so it reads every group:
; the operator's power.  The configuration may BIND a consumer to an
; account login (books/config.lisp `fn-cfg-consumer-bind', delta code 24,
; a row (NAME LOGIN "" 6) of the accounts slot).  A bound consumer is the
; account's, not the operator's:
;
;   * its poll and ack arrive as `bound-poll' / `bound-ack'
;     (books/consumer-local-control.lisp codes 7 and 8) carrying the
;     account's password, which ACL2 checks with `fn-auth-checkp' against
;     the same credential table AUTHINFO checks (auth.toml's credentials,
;     then the redeemed accounts: `fn-auth-config-with-accounts').  No new
;     secret exists: the consumer holds the password its account already
;     has, and revoking or changing the account's credential revokes the
;     consumer with it.
;   * it is served only while its query group is readable under the
;     account's read rule (books/group-access.lisp `fn-gac-pattern' /
;     `fn-gac-readablep', the rule the account's NNTP connections see,
;     read from the LATEST configuration at each request).  Otherwise the
;     poll or ack is refused `:access' at the unchanged position.
;   * the plain `poll' / `ack' (codes 5 and 1) refuse a bound consumer
;     (`:bound'), so no request form serves it outside its account.
;
; An unbound consumer (no mark-6 row names it) is served exactly as before
; (`fn-cbind-plain-poll-of-an-unbound-consumer-is-the-consumer-poll').
;
; Why a refusal and not a skip: a consumer's query is one group
; (`fn-col-register'), so within one configuration the account's rule
; admits all of the query's events or none of them.  Skipping them would
; move the position past events a later rule might admit again, which is a
; silent loss and breaks at-least-once across a rule change; the refusal
; keeps the position, and delivery resumes where it stopped when the rule
; admits the group again.  So the events a bound consumer receives are the
; unbound consumer's, in order, each only while readable: a subsequence
; with the same cursor (`fn-cbind-poll-is-the-consumer-poll-or-a-refusal',
; `fn-cbind-ack-is-the-consumer-ack-or-a-refusal'), and every guarantee
; PRF-116 proves of `fn-col-poll' / `fn-col-ack' (a page is a read; an ack
; writes only a forward declaration in scope; the committed ack's repeat is
; a no-op) holds of every answer that is not a refusal.
;
; Host callers: host/owner-host.lisp `fn-owner-consumer-local-bound-poll',
; `-bound-ack', and the plain `fn-owner-consumer-local-poll' / `-ack', each
; reached from host/native/owner.lisp `fnn-owner-consumer-local-serialized'.
;
; The records flip: the Store retains HELD rows, and a held article row's
; report is its wire form read through the payload arena
; (books/history-fold-refinement.lisp `fn-col-poll-report-over');
; `fn-col-poll-report' refuses such a row `:report'.  The polls over the
; arena, `fn-cbind-poll-over' and `fn-cbind-plain-poll-over' (section at the
; end), carry KEYSTONES 1, 2 and 4 to that report, and equal the polls above
; whenever the selected event is not a held row
; (`fn-cbind-poll-over-is-poll-unless-a-held-row').  The host's two poll
; lines switch to them with the live arena (flip-bridge REQUEST to the host
; lane; the acks read no payload and are unchanged).
(in-package "ACL2")
(include-book "consumer-owner-local-progress")
(include-book "history-fold-refinement")
(include-book "owner-config")

; -----------------------------------------------------------------------------
; The binding and the credential

; The LOGIN text of the first consumer binding row whose name spells
; CONSUMER's octets, or nil (unbound).
(defun fn-cbind-login (rows consumer)
  (declare (xargs :guard t))
  (if (consp rows)
      (let ((row (car rows)))
        (if (and (fn-cfg-consumer-bind-rowp row)
                 (equal (fn-record-string-octets (fn-cfg-row-a row))
                        (true-list-fix consumer))
                 (stringp (fn-cfg-row-b row))
                 (not (equal (fn-cfg-row-b row) "")))
            (fn-cfg-row-b row)
          (fn-cbind-login (cdr rows) consumer)))
    nil))

(defun fn-cbind-config-login (oc consumer)
  (declare (xargs :guard t))
  (fn-cbind-login (fn-cfg-accounts (fn-cfg-value (fn-ocfg-config oc)))
                  consumer))

; The account's credential accepts SECRET: the AUTHINFO comparison over the
; connection-independent credential table of the latest configuration.
(defun fn-cbind-authenticp (oc acfg login secret)
  (declare (xargs :guard t))
  (and (fn-auth-checkp
        (fn-auth-find-cred
         (fn-record-string-octets login)
         (fn-auth-config-creds
          (fn-auth-config-with-accounts acfg
                                        (fn-cfg-value (fn-ocfg-config oc)))))
        secret)
       t))

; LOGIN's read pattern in the latest configuration (nil: unrestricted),
; the text group-access's served view reads.
(defun fn-cbind-read-pattern (oc login)
  (declare (xargs :guard t))
  (fn-gac-pattern (fn-cfg-access-table
                   (fn-cfg-accounts (fn-cfg-value (fn-ocfg-config oc))))
                  (fn-record-string-octets login) 1))

(defun fn-cbind-group-readablep (text group)
  ; GROUP (a group name string) is readable under TEXT, or TEXT restricts
  ; nothing.
  (declare (xargs :guard t))
  (or (null text) (fn-gac-readablep text group)))

; -----------------------------------------------------------------------------
; The decisions the host calls

; nil when the bound consumer may be served, else the refusal.
(defun fn-cbind-gate (oc acfg consumer secret)
  (declare (xargs :guard t))
  (let* ((login (fn-cbind-config-login oc consumer))
         (s (fn-sn-consumer (fn-own-store (fn-ocfg-owner oc))))
         (scoped (fn-col-scope-entry s consumer)))
    (cond ((not login) (list :refused :unbound))
          ((not (fn-cbind-authenticp oc acfg login secret))
           (list :refused :credential))
          ((not (eq (car scoped) :scope)) (list :refused :scope))
          ((not (fn-cbind-group-readablep
                 (fn-cbind-read-pattern oc login)
                 (fn-record-octets-string
                  (fn-cp-nth 3 (fn-cp-nth 1 scoped)))))
           (list :refused :access))
          (t nil))))

(defun fn-cbind-poll (oc acfg consumer secret)
  (declare (xargs :guard t :verify-guards nil))
  (or (fn-cbind-gate oc acfg consumer secret)
      (fn-col-poll-report (fn-ocfg-owner oc) consumer)))

; The consumer a cursor names (its fourth field), or nil.
(defun fn-cbind-cursor-consumer (cursor-octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cp-nth 3 (fn-cp-nth 1 (fn-cp-cursor-decode cursor-octets))))

(defun fn-cbind-ack (oc acfg cursor-octets secret)
  (declare (xargs :guard t :verify-guards nil))
  (let ((decoded (fn-cp-cursor-decode cursor-octets)))
    (if (not (eq (fn-cp-nth 0 decoded) :ok)) decoded
      (or (fn-cbind-gate oc acfg (fn-cbind-cursor-consumer cursor-octets) secret)
          (fn-col-ack (fn-ocfg-owner oc) cursor-octets)))))

; The plain forms: exactly today's answer for an unbound consumer; a bound
; consumer is refused, so it is served only through its account.
(defun fn-cbind-plain-poll (oc consumer)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-cbind-config-login oc consumer)
      (list :refused :bound)
    (fn-col-poll-report (fn-ocfg-owner oc) consumer)))

(defun fn-cbind-plain-ack (oc cursor-octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((decoded (fn-cp-cursor-decode cursor-octets)))
    (if (and (eq (fn-cp-nth 0 decoded) :ok)
             (fn-cbind-config-login oc (fn-cbind-cursor-consumer cursor-octets)))
        (list :refused :bound)
      (fn-col-ack (fn-ocfg-owner oc) cursor-octets))))

; -----------------------------------------------------------------------------
; What a delivered event is

; Some group of the event's article is readable under TEXT.
(defun fn-cbind-some-readablep (text groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (or (fn-cbind-group-readablep text (car groups))
          (fn-cbind-some-readablep text (cdr groups)))
    nil))

; The article is the poll's: a held row or a wire record (fn-col-poll-articlep,
; records-flip); its groups are read the same way on both.
(defun fn-cbind-event-readablep (text event)
  (declare (xargs :guard t :verify-guards nil))
  (let ((article (fn-col-poll-article event)))
    (and (fn-col-poll-articlep article)
         (fn-cbind-some-readablep text (fn-record-groups article))
         t)))

(local
 (defthm fn-cbind-some-readablep-of-member
   (implies (and (member-equal g groups)
                 (fn-cbind-group-readablep text g))
            (fn-cbind-some-readablep text groups))
   :hints (("Goal" :in-theory (disable fn-cbind-group-readablep)))))

(local
 (defthm fn-cbind-gate-nil-facts
   (implies (not (fn-cbind-gate oc acfg consumer secret))
            (let* ((login (fn-cbind-config-login oc consumer))
                   (s (fn-sn-consumer (fn-own-store (fn-ocfg-owner oc))))
                   (scoped (fn-col-scope-entry s consumer)))
              (and login
                   (fn-cbind-authenticp oc acfg login secret)
                   (equal (car scoped) :scope)
                   (fn-cbind-group-readablep
                    (fn-cbind-read-pattern oc login)
                    (fn-record-octets-string
                     (fn-cp-nth 3 (fn-cp-nth 1 scoped)))))))
   :hints (("Goal" :in-theory '(fn-cbind-gate)))))

(local
 (defthm fn-cbind-gate-is-a-refusal
   (implies (fn-cbind-gate oc acfg consumer secret)
            (equal (car (fn-cbind-gate oc acfg consumer secret)) :refused))
   :hints (("Goal" :in-theory (e/d (fn-cbind-gate fn-col-scope-entry)
                                   (fn-cbind-authenticp fn-cbind-read-pattern
                                    fn-cbind-group-readablep
                                    fn-cbind-config-login))))))

; The event a scan selects matches the scanned group (PRF-116's page
; contract, over variables).
(local
 (defthm fn-cbind-scan-event-matches
   (let ((scan (fn-col-poll-scan events group position frontier budget)))
     (implies (and (eq (car scan) :scan) (natp position) (caddr scan))
              (fn-col-matchp (caddr scan) group)))
   :hints (("Goal" :use ((:instance fn-col-poll-scan-page-contract))
            :in-theory (disable fn-col-poll-scan fn-col-matchp
                                fn-col-none-matchp
                                fn-col-poll-scan-page-contract)))))

(local
 (defthm fn-cbind-cp-nth-2-is-caddr
   (equal (fn-cp-nth 2 x) (caddr x))
   :hints (("Goal" :expand ((fn-cp-nth 2 x) (fn-cp-nth 1 (cdr x))
                            (fn-cp-nth 0 (cddr x)))))))

; The event fn-col-poll selects matches its entry's query group.
(local
 (defthm fn-cbind-col-poll-event-matches-its-query
   (let ((d (fn-col-poll o consumer)))
     (implies (and (equal (car d) :poll) (caddr d))
              (fn-col-matchp
               (caddr d)
               (fn-cp-nth 3 (fn-cp-nth 1 (fn-col-scope-entry
                                          (fn-sn-consumer (fn-own-store o))
                                          consumer))))))
   :hints (("Goal"
            :use ((:instance fn-col-poll-is-the-index-window-scan-unfolds)
                  (:instance fn-col-scope-entry-position-is-natural
                             (s (fn-sn-consumer (fn-own-store o)))))
            :in-theory (e/d (fn-cbind-cp-nth-2-is-caddr
                             fn-cbind-scan-event-matches)
                            (fn-col-poll fn-col-poll-scan fn-col-scope-entry
                             fn-col-poll-index-window fn-col-matchp
                             fn-cp-cursor-encode fn-cp-scope-cursor
                             fn-cp-nth update-nth
                             fn-col-poll-is-the-index-window-scan-unfolds
                             fn-col-scope-entry-position-is-natural))))))

(local
 (defthm fn-cbind-poll-when-gate-admits
   (implies (not (fn-cbind-gate oc acfg consumer secret))
            (equal (fn-cbind-poll oc acfg consumer secret)
                   (fn-col-poll-report (fn-ocfg-owner oc) consumer)))
   :hints (("Goal" :in-theory '(fn-cbind-poll)))))

(local
 (defthm fn-cbind-poll-page-means-gate-admits
   (implies (equal (car (fn-cbind-poll oc acfg consumer secret)) :poll)
            (not (fn-cbind-gate oc acfg consumer secret)))
   :hints (("Goal" :use ((:instance fn-cbind-gate-is-a-refusal))
            :in-theory '(fn-cbind-poll)))))

(local
 (defthm fn-cbind-report-page-means-poll-page
   (implies (equal (car (fn-col-poll-report o consumer)) :poll)
            (equal (car (fn-col-poll o consumer)) :poll))
   :hints (("Goal" :use ((:instance fn-col-poll-report-fits-or-refuses-by-name)
                         (:instance fn-col-poll-is-a-page-or-a-refusal))
            :in-theory (disable fn-col-poll fn-col-poll-report
                                fn-col-poll-report-octets
                                fn-col-poll-is-a-page-or-a-refusal
                                fn-ncl-poll-event-bytesp)))))

(local
 (defthm fn-cbind-matching-event-of-a-readable-group-is-readable
   (implies (and (fn-col-matchp event group)
                 (fn-cbind-group-readablep text (fn-record-octets-string group)))
            (fn-cbind-event-readablep text event))
   :hints (("Goal" :in-theory (e/d (fn-cbind-event-readablep fn-col-matchp)
                                   (fn-col-poll-article fn-record-octets-string
                                    fn-cbind-group-readablep fn-col-poll-articlep
                                    fn-record-groups))))))

(local
 (defthm fn-cbind-readable-query-reads-the-event
   (let ((d (fn-col-poll o consumer)))
     (implies (and (equal (car d) :poll) (caddr d)
                   (fn-cbind-group-readablep
                    text
                    (fn-record-octets-string
                     (fn-cp-nth 3 (fn-cp-nth 1 (fn-col-scope-entry
                                                (fn-sn-consumer (fn-own-store o))
                                                consumer))))))
              (fn-cbind-event-readablep text (caddr d))))
   :hints (("Goal" :use ((:instance fn-cbind-col-poll-event-matches-its-query)
                         (:instance fn-cbind-matching-event-of-a-readable-group-is-readable
                                    (event (caddr (fn-col-poll o consumer)))
                                    (group (fn-cp-nth 3 (fn-cp-nth 1 (fn-col-scope-entry
                                                                      (fn-sn-consumer (fn-own-store o))
                                                                      consumer))))))
            :in-theory nil))))

; KEYSTONE 1 (confinement).  A bound poll that answers a page is the
; consumer poll's own page (so its report is the selected event's exact
; encoding, PRF-177's fn-col-poll-report-fits-or-refuses-by-name); the
; consumer is bound, the request carried the account's credential, and the
; selected event, if any, has an article with a group readable under the
; bound account's read rule in the latest configuration.
(defthm fn-cbind-poll-delivers-only-readable-events
  (let ((r (fn-cbind-poll oc acfg consumer secret))
        (d (fn-col-poll (fn-ocfg-owner oc) consumer))
        (login (fn-cbind-config-login oc consumer)))
    (implies (equal (car r) :poll)
             (and login
                  (fn-cbind-authenticp oc acfg login secret)
                  (equal r (fn-col-poll-report (fn-ocfg-owner oc) consumer))
                  (equal (car d) :poll)
                  (implies (caddr d)
                           (fn-cbind-event-readablep
                            (fn-cbind-read-pattern oc login) (caddr d))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cbind-poll-page-means-gate-admits)
                 (:instance fn-cbind-poll-when-gate-admits)
                 (:instance fn-cbind-gate-nil-facts)
                 (:instance fn-cbind-report-page-means-poll-page
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-cbind-readable-query-reads-the-event
                            (o (fn-ocfg-owner oc))
                            (text (fn-cbind-read-pattern
                                   oc (fn-cbind-config-login oc consumer)))))
           :in-theory nil)))

; KEYSTONE 2 (delivery over the filtered sequence).  A bound poll answers
; the consumer poll's own answer or a refusal; a refusal proposes no write,
; so the position does not move.  With KEYSTONE 3 this carries PRF-116's
; guarantees of fn-col-poll-report and fn-col-ack to the bound consumer.
(defthm fn-cbind-poll-is-the-consumer-poll-or-a-refusal
  (let ((r (fn-cbind-poll oc acfg consumer secret)))
    (or (equal r (fn-col-poll-report (fn-ocfg-owner oc) consumer))
        (equal (car r) :refused)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cbind-gate-is-a-refusal))
           :in-theory (e/d (fn-cbind-poll)
                           (fn-cbind-gate fn-col-poll-report
                            fn-cbind-gate-is-a-refusal)))))

(local
 (defthm fn-cbind-cursor-decode-tag
   (implies (not (equal (fn-cp-nth 0 (fn-cp-cursor-decode bytes)) :ok))
            (equal (car (fn-cp-cursor-decode bytes)) :refused))
   :hints (("Goal" :in-theory (e/d (fn-cp-cursor-decode)
                                   (fn-cp-read-fields fn-cp-cursorp
                                    fn-cbor-at-mostp fn-cbor-octet-listp))))))

(local
 (defthm fn-cbind-ack-of-an-undecodable-cursor
   (implies (not (equal (fn-cp-nth 0 (fn-cp-cursor-decode bytes)) :ok))
            (and (equal (fn-cbind-ack oc acfg bytes secret)
                        (fn-cp-cursor-decode bytes))
                 (equal (fn-col-ack o bytes) (fn-cp-cursor-decode bytes))))
   :hints (("Goal" :in-theory (e/d (fn-cbind-ack fn-col-ack)
                                   (fn-cp-cursor-decode fn-cbind-gate
                                    fn-cbind-cursor-consumer
                                    fn-cp-ack fn-col-result-event))))))

(local
 (defthm fn-cbind-ack-of-a-decodable-cursor
   (implies (equal (fn-cp-nth 0 (fn-cp-cursor-decode bytes)) :ok)
            (equal (fn-cbind-ack oc acfg bytes secret)
                   (or (fn-cbind-gate oc acfg
                                      (fn-cbind-cursor-consumer bytes)
                                      secret)
                       (fn-col-ack (fn-ocfg-owner oc) bytes))))
   :hints (("Goal" :in-theory (e/d (fn-cbind-ack)
                                   (fn-cp-cursor-decode fn-cbind-gate fn-col-ack
                                    fn-cbind-cursor-consumer))))))

; KEYSTONE 3.  A bound ack answers the consumer ack's own answer (the same
; kernel: a write only of a forward declaration in scope, a no-op when
; repeated) or a refusal; it is the consumer ack only when the cursor's
; consumer is bound, the credential checks and its query group is readable.
(defthm fn-cbind-ack-is-the-consumer-ack-or-a-refusal
  (let ((r (fn-cbind-ack oc acfg bytes secret))
        (consumer (fn-cbind-cursor-consumer bytes)))
    (and (or (equal r (fn-col-ack (fn-ocfg-owner oc) bytes))
             (equal (car r) :refused))
         (implies (not (equal (car r) :refused))
                  (and (fn-cbind-config-login oc consumer)
                       (fn-cbind-authenticp oc acfg
                                            (fn-cbind-config-login oc consumer)
                                            secret)
                       (fn-cbind-group-readablep
                        (fn-cbind-read-pattern
                         oc (fn-cbind-config-login oc consumer))
                        (fn-record-octets-string
                         (fn-cp-nth 3 (fn-cp-nth 1 (fn-col-scope-entry
                                                    (fn-sn-consumer
                                                     (fn-own-store (fn-ocfg-owner oc)))
                                                    consumer)))))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cbind-gate-is-a-refusal
                                   (consumer (fn-cbind-cursor-consumer bytes)))
                        (:instance fn-cbind-gate-nil-facts
                                   (consumer (fn-cbind-cursor-consumer bytes)))
                        (:instance fn-cbind-cursor-decode-tag)
                        (:instance fn-cbind-ack-of-an-undecodable-cursor
                                   (o (fn-ocfg-owner oc)))
                        (:instance fn-cbind-ack-of-a-decodable-cursor))
           :in-theory nil)))

; KEYSTONE 4 (the default).  An unbound consumer's plain poll and ack are
; today's, and a bound consumer's plain poll and ack are refused.
(defthm fn-cbind-plain-poll-of-an-unbound-consumer-is-the-consumer-poll
  (and (implies (not (fn-cbind-config-login oc consumer))
                (equal (fn-cbind-plain-poll oc consumer)
                       (fn-col-poll-report (fn-ocfg-owner oc) consumer)))
       (implies (fn-cbind-config-login oc consumer)
                (equal (fn-cbind-plain-poll oc consumer)
                       '(:refused :bound))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cbind-plain-poll)
                                  (fn-cbind-config-login fn-col-poll-report)))))

(defthm fn-cbind-plain-ack-of-an-unbound-consumer-is-the-consumer-ack
  (let ((consumer (fn-cbind-cursor-consumer bytes)))
    (and (implies (not (fn-cbind-config-login oc consumer))
                  (equal (fn-cbind-plain-ack oc bytes)
                         (fn-col-ack (fn-ocfg-owner oc) bytes)))
         (implies (and (equal (fn-cp-nth 0 (fn-cp-cursor-decode bytes)) :ok)
                       (fn-cbind-config-login oc consumer))
                  (equal (fn-cbind-plain-ack oc bytes) '(:refused :bound)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cbind-plain-ack)
                                  (fn-cbind-config-login fn-col-ack
                                   fn-cp-cursor-decode fn-cbind-cursor-consumer)))))

(verify-guards fn-cbind-cursor-consumer)
(verify-guards fn-cbind-poll)
(verify-guards fn-cbind-ack)
(verify-guards fn-cbind-plain-poll)
(verify-guards fn-cbind-plain-ack)

; -----------------------------------------------------------------------------
; The polls over the payload arena (records flip)

(defun fn-cbind-poll-over (oc acfg consumer secret fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (or (fn-cbind-gate oc acfg consumer secret)
      (fn-col-poll-report-over (fn-ocfg-owner oc) consumer fn-arena)))

(defun fn-cbind-plain-poll-over (oc consumer fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (fn-cbind-config-login oc consumer)
      (list :refused :bound)
    (fn-col-poll-report-over (fn-ocfg-owner oc) consumer fn-arena)))

(verify-guards fn-cbind-poll-over)
(verify-guards fn-cbind-plain-poll-over)

; The bridge: on a selection that is no held row the arena is not read and
; each poll over the arena is the poll above.
(defthm fn-cbind-poll-over-is-poll-unless-a-held-row
  (implies (not (fn-held-p (caddr (fn-col-poll (fn-ocfg-owner oc) consumer))))
           (and (equal (fn-cbind-poll-over oc acfg consumer secret fn-arena)
                       (fn-cbind-poll oc acfg consumer secret))
                (equal (fn-cbind-plain-poll-over oc consumer fn-arena)
                       (fn-cbind-plain-poll oc consumer))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-col-poll-report-over-is-the-report-unless-a-held-row
                                   (o (fn-ocfg-owner oc))))
           :in-theory (e/d (fn-cbind-poll-over fn-cbind-poll
                            fn-cbind-plain-poll-over fn-cbind-plain-poll)
                           (fn-cbind-gate fn-col-poll-report-over fn-col-poll-report
                            fn-col-poll fn-cbind-config-login)))))

(local
 (defthm fn-cbind-poll-over-when-gate-admits
   (implies (not (fn-cbind-gate oc acfg consumer secret))
            (equal (fn-cbind-poll-over oc acfg consumer secret fn-arena)
                   (fn-col-poll-report-over (fn-ocfg-owner oc) consumer fn-arena)))
   :hints (("Goal" :in-theory '(fn-cbind-poll-over)))))

(local
 (defthm fn-cbind-poll-over-page-means-gate-admits
   (implies (equal (car (fn-cbind-poll-over oc acfg consumer secret fn-arena)) :poll)
            (not (fn-cbind-gate oc acfg consumer secret)))
   :hints (("Goal" :use ((:instance fn-cbind-gate-is-a-refusal))
            :in-theory '(fn-cbind-poll-over)))))

(local
 (defthm fn-cbind-report-over-page-means-poll-page
   (implies (equal (car (fn-col-poll-report-over o consumer fn-arena)) :poll)
            (equal (car (fn-col-poll o consumer)) :poll))
   :hints (("Goal" :in-theory (e/d (fn-col-poll-report-over)
                                   (fn-col-poll fn-col-poll-report-octets
                                    fn-row-wire-of fn-ncl-poll-event-bytesp))))))

; KEYSTONE 1 over the arena (confinement): a bound poll that answers a page
; is the consumer poll's own page over the arena; the consumer is bound, the
; credential checks, and the selected event's article has a group readable
; under the bound account's read rule.
(defthm fn-cbind-poll-over-delivers-only-readable-events
  (let ((r (fn-cbind-poll-over oc acfg consumer secret fn-arena))
        (d (fn-col-poll (fn-ocfg-owner oc) consumer))
        (login (fn-cbind-config-login oc consumer)))
    (implies (equal (car r) :poll)
             (and login
                  (fn-cbind-authenticp oc acfg login secret)
                  (equal r (fn-col-poll-report-over (fn-ocfg-owner oc) consumer fn-arena))
                  (equal (car d) :poll)
                  (implies (caddr d)
                           (fn-cbind-event-readablep
                            (fn-cbind-read-pattern oc login) (caddr d))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cbind-poll-over-page-means-gate-admits)
                 (:instance fn-cbind-poll-over-when-gate-admits)
                 (:instance fn-cbind-gate-nil-facts)
                 (:instance fn-cbind-report-over-page-means-poll-page
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-cbind-readable-query-reads-the-event
                            (o (fn-ocfg-owner oc))
                            (text (fn-cbind-read-pattern
                                   oc (fn-cbind-config-login oc consumer)))))
           :in-theory nil)))

; KEYSTONE 2 over the arena: the consumer poll's own answer or a refusal.
(defthm fn-cbind-poll-over-is-the-consumer-poll-or-a-refusal
  (let ((r (fn-cbind-poll-over oc acfg consumer secret fn-arena)))
    (or (equal r (fn-col-poll-report-over (fn-ocfg-owner oc) consumer fn-arena))
        (equal (car r) :refused)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cbind-gate-is-a-refusal))
           :in-theory (e/d (fn-cbind-poll-over)
                           (fn-cbind-gate fn-col-poll-report-over
                            fn-cbind-gate-is-a-refusal)))))

; KEYSTONE 4 over the arena (the default).
(defthm fn-cbind-plain-poll-over-of-an-unbound-consumer-is-the-consumer-poll
  (and (implies (not (fn-cbind-config-login oc consumer))
                (equal (fn-cbind-plain-poll-over oc consumer fn-arena)
                       (fn-col-poll-report-over (fn-ocfg-owner oc) consumer fn-arena)))
       (implies (fn-cbind-config-login oc consumer)
                (equal (fn-cbind-plain-poll-over oc consumer fn-arena)
                       '(:refused :bound))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cbind-plain-poll-over)
                                  (fn-cbind-config-login fn-col-poll-report-over)))))
