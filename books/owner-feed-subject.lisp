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
