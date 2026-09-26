; fn: the outbound feed's loop freedom over the function the host calls.
;
; books/owner-feed.lisp proves the scope and loop properties of
; `fn-own-feed-targets' and of `fn-own-feed-accept'.  Neither is what the
; host reaches.  The host projects the acceptance-time intent at
; host/owner-host.lisp fn-owner-submission-intent (the call of
; fn-own-submission-intent-records, which names fn-own-submission-targets),
; and the durable enqueue is fn-own-feed-durable, folded into the owner by
; fn-own-transit-outcome (host fn-owner-transit-outcome), fn-own-outcome
; (fn-owner-outcome) and fn-own-control-outcome (fn-owner-control-outcome).
; Both use `fn-own-submission-targets' (books/owner.lisp), which filters
; `fn-own-feed-targets' by fn-own-feed-new-targets (a peer whose queue
; already holds the Message-ID needs no new obligation).  `fn-own-feed-accept'
; has no caller in books/ or host/: its two theorems are about a sibling.
;
; This book supplies the subject equation AGENTS.md rule 1 asks for (the
; filtered targets are among the unfiltered ones) and restates loop freedom
; over the called functions: no target of the intent is the origin peer or a
; peer whose path-identity the article's Path names, and the durable enqueue
; and the transit outcome the host installs leave the origin peer's feed as
; it was.

(in-package "ACL2")
(include-book "owner")

; The filter keeps a sublist of what it is given.
(defthm fn-own-feed-new-targets-are-among-the-names
  (implies (member-equal name (fn-own-feed-new-targets names tbl msgid))
           (member-equal name names))
  :hints (("Goal" :in-theory (enable fn-own-feed-new-targets))))

; KEYSTONE (subject equation).  Every peer the host's intent and durable
; enqueue name is a peer fn-own-feed-targets names for the in-flight
; submission's origin, groups and Path.
(defthm fn-own-submission-targets-are-feed-targets
  (implies (member-equal name (fn-own-submission-targets o))
           (member-equal name
                         (fn-own-feed-targets
                          (fn-own-feeds o)
                          (fn-own-sub-origin (fn-own-inflight o))
                          (fn-own-sub-feed-groups (fn-own-inflight o))
                          (fn-own-feed-path-of
                           (fn-own-sub-octets (fn-own-inflight o))))))
  :hints (("Goal" :in-theory (e/d (fn-own-submission-targets)
                                  (fn-own-feed-targets fn-own-sub-feed-groups
                                   fn-own-sub-origin fn-own-sub-octets
                                   fn-own-feed-path-of fn-own-feed-new-targets))
           :use ((:instance fn-own-feed-new-targets-are-among-the-names
                            (names (fn-own-feed-targets
                                    (fn-own-feeds o)
                                    (fn-own-sub-origin (fn-own-inflight o))
                                    (fn-own-sub-feed-groups (fn-own-inflight o))
                                    (fn-own-feed-path-of
                                     (fn-own-sub-octets (fn-own-inflight o)))))
                            (tbl (fn-own-feeds o))
                            (msgid (fn-own-sub-msgid (fn-own-inflight o))))))))

; K2's outbound half over the host-called function: no peer the host's intent
; and durable enqueue name is the peer the article arrived from, or a peer
; whose path-identity the accepted article's Path already names (RFC 5537
; section 3.6).  fn-own-feed-never-offers-a-loop does the work; the subject
; equation above moves it to fn-own-submission-targets.
(defthm fn-own-submission-never-targets-a-loop
  (implies (and (fn-own-feed-tablep (fn-own-feeds o))
                (member-equal name (fn-own-submission-targets o)))
           (and (not (equal name (fn-own-sub-origin (fn-own-inflight o))))
                (not (fn-path-names-p
                      (fn-own-feed-path-of (fn-own-sub-octets (fn-own-inflight o)))
                      (fn-record-string-octets
                       (fn-cfg-peer-path-identity
                        (fn-own-feed-record-of name (fn-own-feeds o))))))))
  :hints (("Goal" :use (fn-own-submission-targets-are-feed-targets
                        (:instance fn-own-feed-never-offers-a-loop
                                   (tbl (fn-own-feeds o))
                                   (origin (fn-own-sub-origin (fn-own-inflight o)))
                                   (groups (fn-own-sub-feed-groups (fn-own-inflight o)))
                                   (path (fn-own-feed-path-of
                                          (fn-own-sub-octets (fn-own-inflight o))))))
           :in-theory (disable fn-own-submission-targets-are-feed-targets
                               fn-own-feed-never-offers-a-loop
                               fn-own-submission-targets fn-own-feed-targets
                               fn-own-feed-tablep fn-own-sub-origin
                               fn-own-sub-feed-groups fn-own-sub-octets
                               fn-own-feed-path-of fn-own-feed-record-of
                               fn-path-names-p fn-record-string-octets))))

; The durable enqueue reaches exactly the submission's targets: every other
; peer's feed is unchanged.  fn-own-feed-accept-touches-only-its-targets's
; statement, over the function the outcomes call.
(defthm fn-own-feed-durable-touches-only-the-submission-targets
  (implies (not (member-equal other (fn-own-submission-targets o)))
           (equal (fn-own-feed-entry-of other (fn-own-feed-durable o sub))
                  (fn-own-feed-entry-of other (fn-own-feeds o))))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-durable)
                                  (fn-own-submission-targets)))))

; KEYSTONE.  The peer a transit article came from never has it enqueued
; back by the durable enqueue.  fn-own-feed-accept-never-enqueues-on-the-origin's
; statement, over fn-own-feed-durable.
(defthm fn-own-feed-durable-never-enqueues-on-the-origin
  (implies (fn-own-feed-tablep (fn-own-feeds o))
           (equal (fn-own-feed-entry-of (fn-own-sub-origin (fn-own-inflight o))
                                        (fn-own-feed-durable o sub))
                  (fn-own-feed-entry-of (fn-own-sub-origin (fn-own-inflight o))
                                        (fn-own-feeds o))))
  :hints (("Goal" :use ((:instance fn-own-feed-durable-touches-only-the-submission-targets
                                   (other (fn-own-sub-origin (fn-own-inflight o))))
                        (:instance fn-own-submission-never-targets-a-loop
                                   (name (fn-own-sub-origin (fn-own-inflight o)))))
           :in-theory (disable fn-own-feed-durable-touches-only-the-submission-targets
                               fn-own-submission-never-targets-a-loop
                               fn-own-feed-durable fn-own-submission-targets
                               fn-own-feed-tablep fn-own-sub-origin))))

; The advance a durable outcome takes re-pins one connection and moves no feed.
(defthm fn-own-feeds-of-fn-own-advance
  (equal (fn-own-feeds (fn-own-advance o id))
         (fn-own-feeds o))
  :hints (("Goal" :in-theory (enable fn-own-advance fn-own-advance-result
                                     fn-own-set-conns))))

; KEYSTONE, over the transition the host installs for a transit article
; (host/owner-host.lisp fn-owner-transit-outcome calls fn-own-transit-outcome).
; Whatever the decision and whatever the store answered, the owner the host
; keeps has the origin peer's feed exactly as it was: a transit article is
; never enqueued back towards the peer it came from.
(defthm fn-own-transit-outcome-never-enqueues-on-the-origin
  (implies (fn-own-feed-tablep (fn-own-feeds o))
           (equal (fn-own-feed-entry-of
                   (fn-own-sub-origin (fn-own-inflight o))
                   (fn-own-feeds (cdr (fn-own-transit-outcome o id kind reason word))))
                  (fn-own-feed-entry-of
                   (fn-own-sub-origin (fn-own-inflight o))
                   (fn-own-feeds o))))
  :hints (("Goal" :in-theory (e/d (fn-own-transit-outcome)
                                  (fn-own-advance fn-own-feed-durable
                                   fn-own-outcome-completion
                                   fn-served-transit-outcome
                                   fn-served-result-effects
                                   fn-own-feed-tablep fn-own-sub-origin
                                   fn-own-feed-entry-of)))))

(in-theory (disable fn-own-feed-new-targets-are-among-the-names
                    fn-own-submission-targets-are-feed-targets
                    fn-own-submission-never-targets-a-loop
                    fn-own-feed-durable-touches-only-the-submission-targets
                    fn-own-feed-durable-never-enqueues-on-the-origin
                    fn-own-feeds-of-fn-own-advance
                    fn-own-transit-outcome-never-enqueues-on-the-origin))

; -----------------------------------------------------------------------------
; A control article's scope (PKT-400; RFC 5537 sections 3.6 and 5.3).
;
; fn-own-sub-feed-groups (books/owner.lisp) is what the host's intent
; (host/owner-host.lisp fn-owner-submission-intent, through
; fn-icar-submission-targets, equal to fn-own-submission-targets) and the
; durable enqueue (fn-own-feed-durable, from fn-owner-outcome,
; fn-owner-control-outcome and fn-owner-transit-outcome) match each peer's
; outbound wildmat against.  For a control article it is the submission's
; base groups (its filing group, control.<verb>, for a local or signed
; control submission; the Newsgroups names for transit) plus the article's
; Newsgroups names and its filing group, from one parse.

; The classification the scope reads is the one the filing plan reads
; (books/peer-authored-accept.lisp fn-pa-filing-plan calls
; fn-ctl-classify-octets): whenever the article parses, they are equal.
(defthm fn-own-feed-control-of-is-the-filing-classification
  (implies (fn-own-feed-article-of octets)
           (equal (fn-own-feed-control-of octets)
                  (fn-ctl-classify-octets octets)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-control-of fn-own-feed-article-of
                                   fn-ctl-classify-octets)
                                  (fn-ctl-classify fn-article-parse)))))

; A :control classification always names its verb, so the filing group is
; read from a real word.
(defthm fn-ctl-classify-control-has-a-verb
  (implies (equal (car (fn-ctl-classify a)) :control)
           (consp (cdr (fn-ctl-classify a))))
  :hints (("Goal" :in-theory (enable fn-ctl-classify fn-ctl-classify-fields
                                     fn-ctl-parse-command))))

(defthm fn-own-feed-any-matchp-of-append
  (equal (fn-own-feed-any-matchp w (append a b))
         (or (fn-own-feed-any-matchp w a)
             (fn-own-feed-any-matchp w b)))
  :hints (("Goal" :in-theory (disable fn-own-feed-group-matchp))))

(defthm fn-own-feed-any-matchp-of-true-list-fix
  (equal (fn-own-feed-any-matchp w (true-list-fix a))
         (fn-own-feed-any-matchp w a))
  :hints (("Goal" :in-theory (disable fn-own-feed-group-matchp))))

(defthm fn-own-feed-control-groups-of-names-newsgroups-and-filing-group
  (implies (equal (car (fn-own-feed-control-of octets)) :control)
           (equal (fn-own-feed-control-groups-of octets)
                  (cons (fn-record-string-octets
                         (fn-ctl-filing-group (cadr (fn-own-feed-control-of octets))))
                        (fn-own-feed-groups-of octets))))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-control-of fn-own-feed-control-groups-of
                                   fn-own-feed-groups-of)
                                  (fn-ctl-classify fn-ctl-filing-group
                                   fn-record-string-octets fn-af-relayed-article-check
                                   fn-own-feed-article-of))
           :use ((:instance fn-ctl-classify-control-has-a-verb
                            (a (fn-own-feed-article-of octets)))))))

; KEYSTONE.  An ordinary article's scope is exactly what it was before
; PKT-400: the base groups, untouched.  Only control articles gain groups.
(defthm fn-own-sub-feed-groups-of-an-ordinary-article
  (implies (not (equal (car (fn-own-feed-control-of (fn-own-sub-octets sub))) :control))
           (equal (fn-own-sub-feed-groups sub)
                  (fn-own-sub-feed-base-groups sub)))
  :hints (("Goal" :in-theory (e/d (fn-own-sub-feed-groups fn-own-feed-control-of
                                   fn-own-feed-control-groups-of)
                                  (fn-ctl-classify fn-own-feed-article-of
                                   fn-own-sub-feed-base-groups fn-own-sub-octets)))))

(defthm fn-own-sub-feed-groups-match-of-a-control-article
  (implies (equal (car (fn-own-feed-control-of (fn-own-sub-octets sub))) :control)
           (equal (fn-own-feed-any-matchp w (fn-own-sub-feed-groups sub))
                  (or (fn-own-feed-any-matchp w (fn-own-sub-feed-base-groups sub))
                      (fn-own-feed-group-matchp
                       w (fn-record-string-octets
                          (fn-ctl-filing-group
                           (cadr (fn-own-feed-control-of (fn-own-sub-octets sub))))))
                      (fn-own-feed-any-matchp w (fn-own-feed-groups-of (fn-own-sub-octets sub))))))
  :hints (("Goal" :in-theory (e/d (fn-own-sub-feed-groups)
                                  (fn-own-feed-control-of fn-own-feed-control-groups-of
                                   fn-own-feed-group-matchp fn-ctl-filing-group
                                   fn-record-string-octets fn-own-feed-groups-of
                                   fn-own-sub-feed-base-groups fn-own-sub-octets)))))

(defthm fn-own-feed-new-targets-keeps-an-unqueued-name
  (implies (and (member-equal name names)
                (not (consp (fn-feed-find msgid (fn-feed-queue (fn-own-feed-find name tbl))))))
           (member-equal name (fn-own-feed-new-targets names tbl msgid)))
  :hints (("Goal" :in-theory (enable fn-own-feed-new-targets))))

; KEYSTONE (PKT-400), over the function the host calls.  A control article
; in flight is a target of every peer of the table whose outbound half is
; configured, whose wildmat matches a group the article's Newsgroups names OR
; its filing group (control.cancel for a cancel), whose path-identity the
; Path does not name, which is not the peer it came from, and whose feed does
; not already hold the Message-ID.  Before PKT-400 a signed cancel of a
; local.general article was offered under control.cancel alone, so a friend
; whose wildmat was local.* never received it.
(defthm fn-own-submission-offers-a-control-article-under-its-newsgroups-and-filing-group
  (let* ((sub (fn-own-inflight o))
         (octets (fn-own-sub-octets sub))
         (tbl (fn-own-feeds o))
         (rec (fn-own-feed-record-of name tbl))
         (wildmat (fn-cfg-peer-outbound-groups rec)))
    (implies (and sub
                  (fn-own-feed-tablep tbl)
                  (fn-own-feed-entry-of name tbl)
                  (equal (car (fn-own-feed-control-of octets)) :control)
                  (fn-own-feed-outboundp rec)
                  (or (fn-own-feed-any-matchp wildmat (fn-own-feed-groups-of octets))
                      (fn-own-feed-group-matchp
                       wildmat
                       (fn-record-string-octets
                        (fn-ctl-filing-group (cadr (fn-own-feed-control-of octets))))))
                  (not (fn-path-names-p (fn-own-feed-path-of octets)
                                        (fn-record-string-octets
                                         (fn-cfg-peer-path-identity rec))))
                  (not (equal (fn-own-sub-origin sub) name))
                  (not (consp (fn-feed-find (fn-own-sub-msgid sub)
                                            (fn-feed-queue (fn-own-feed-find name tbl))))))
             (member-equal name (fn-own-submission-targets o))))
  :hints (("Goal"
           :use ((:instance fn-own-feed-targets-omit-no-offerable-peer
                            (tbl (fn-own-feeds o))
                            (origin (fn-own-sub-origin (fn-own-inflight o)))
                            (groups (fn-own-sub-feed-groups (fn-own-inflight o)))
                            (path (fn-own-feed-path-of (fn-own-sub-octets (fn-own-inflight o)))))
                 (:instance fn-own-sub-feed-groups-match-of-a-control-article
                            (sub (fn-own-inflight o))
                            (w (fn-cfg-peer-outbound-groups
                                (fn-own-feed-record-of name (fn-own-feeds o)))))
                 (:instance fn-own-feed-new-targets-keeps-an-unqueued-name
                            (names (fn-own-feed-targets
                                    (fn-own-feeds o)
                                    (fn-own-sub-origin (fn-own-inflight o))
                                    (fn-own-sub-feed-groups (fn-own-inflight o))
                                    (fn-own-feed-path-of
                                     (fn-own-sub-octets (fn-own-inflight o)))))
                            (tbl (fn-own-feeds o))
                            (msgid (fn-own-sub-msgid (fn-own-inflight o)))))
           :in-theory (e/d (fn-own-submission-targets fn-own-feed-offerablep)
                           (fn-own-feed-targets-omit-no-offerable-peer
                            fn-own-sub-feed-groups-match-of-a-control-article
                            fn-own-feed-new-targets-keeps-an-unqueued-name
                            fn-own-feed-targets fn-own-feed-new-targets
                            fn-own-sub-feed-groups fn-own-feed-control-of
                            fn-own-feed-groups-of fn-own-feed-path-of
                            fn-own-feed-group-matchp fn-own-feed-any-matchp
                            fn-ctl-filing-group fn-record-string-octets
                            fn-path-names-p fn-own-feed-tablep
                            fn-own-feed-entry-of fn-own-feed-record-of
                            fn-own-feed-find fn-own-sub-octets fn-own-sub-origin
                            fn-own-sub-msgid fn-own-feed-outboundp
                            fn-own-sub-feed-base-groups)))))

; KEYSTONE (the other direction).  The widening is exactly those groups: a
; target of a control article matches its base groups, its Newsgroups names
; or its filing group, and nothing else put it there.
(defthm fn-own-submission-target-of-a-control-article-is-in-its-scope
  (let* ((sub (fn-own-inflight o))
         (octets (fn-own-sub-octets sub))
         (tbl (fn-own-feeds o))
         (wildmat (fn-cfg-peer-outbound-groups (fn-own-feed-record-of name tbl))))
    (implies (and (fn-own-feed-tablep tbl)
                  (member-equal name (fn-own-submission-targets o))
                  (equal (car (fn-own-feed-control-of octets)) :control))
             (or (fn-own-feed-any-matchp wildmat (fn-own-sub-feed-base-groups sub))
                 (fn-own-feed-any-matchp wildmat (fn-own-feed-groups-of octets))
                 (fn-own-feed-group-matchp
                  wildmat
                  (fn-record-string-octets
                   (fn-ctl-filing-group (cadr (fn-own-feed-control-of octets))))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-submission-targets-are-feed-targets)
                 (:instance fn-own-feed-target-is-in-scope
                            (tbl (fn-own-feeds o))
                            (origin (fn-own-sub-origin (fn-own-inflight o)))
                            (groups (fn-own-sub-feed-groups (fn-own-inflight o)))
                            (path (fn-own-feed-path-of (fn-own-sub-octets (fn-own-inflight o)))))
                 (:instance fn-own-sub-feed-groups-match-of-a-control-article
                            (sub (fn-own-inflight o))
                            (w (fn-cfg-peer-outbound-groups
                                (fn-own-feed-record-of name (fn-own-feeds o))))))
           :in-theory (disable fn-own-submission-targets-are-feed-targets
                               fn-own-feed-target-is-in-scope
                               fn-own-sub-feed-groups-match-of-a-control-article
                               fn-own-submission-targets fn-own-feed-targets
                               fn-own-sub-feed-groups fn-own-feed-control-of
                               fn-own-feed-groups-of fn-own-feed-path-of
                               fn-own-feed-group-matchp fn-own-feed-any-matchp
                               fn-ctl-filing-group fn-record-string-octets
                               fn-own-feed-tablep fn-own-feed-record-of
                               fn-own-sub-octets fn-own-sub-origin
                               fn-own-sub-feed-base-groups))))

; The rules above rewrite the classification to the article parse; a book
; that includes this one must not see the parser open.
(in-theory (disable fn-own-feed-control-of-is-the-filing-classification
                    fn-ctl-classify-control-has-a-verb
                    fn-own-feed-any-matchp-of-append
                    fn-own-feed-any-matchp-of-true-list-fix
                    fn-own-feed-control-groups-of-names-newsgroups-and-filing-group
                    fn-own-sub-feed-groups-of-an-ordinary-article
                    fn-own-sub-feed-groups-match-of-a-control-article
                    fn-own-feed-new-targets-keeps-an-unqueued-name
                    fn-own-submission-offers-a-control-article-under-its-newsgroups-and-filing-group))
