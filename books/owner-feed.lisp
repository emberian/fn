; fn: the owner's outbound feed table (specs/peering.md sec. 3, milestone 3).
;
; books/peer-feed.lisp is ONE peer's feed machine and says so: "whether the
; article is IN SCOPE for this peer is the caller's decision
; (`fn-feed-offerablep' of the design, which reads the peer record and the
; Path): the feed never re-derives it".  This book is that caller's half, and
; nothing else:
;
;   * the feed TABLE, one entry per configured peer that has an outbound half.
;     An entry is (name record feed): the peer name string the configuration
;     and the scheduler use, the `fn-cfg-peerp' the scope decision reads, and
;     the peer's `fn-feedp'.  `fn-own-feed-tablep' binds the three names of
;     one peer that the w6 handoff left as an unproved owner obligation -- the
;     key, `fn-feed-peer' (the same name as octets, which is what the FNFD
;     journal carries) and `fn-sched-contact-peer' of the feed's contact.
;     Carrying the record is what lets the enqueue arm decide scope without
;     the configuration value: the configuration is read once, at
;     `fn-own-feed-reconfigure', and never on the durable path.
;
;   * the SCOPE decision -- RFC 5537 sec. 3.6, a relaying agent's duty -- as
;     one function of the peer record and the article's own octets:
;     `fn-own-feed-offerablep'.  Its three refusals are the peer's outbound
;     wildmat, the Path loop check and the origin peer.  ACL2 decides which
;     peers get which article; no wildmat, no Path test and no code map runs
;     in Python or in host Lisp.
;
;   * `fn-own-feed-targets', the peers one article is offered to;
;     `fn-own-feed-accept', the enqueue on exactly those; `fn-own-feed-tick',
;     one `fn-feed-tick-step' per peer; and the FNFD records each of those
;     authorizes, which the host writes BEFORE the effect.
;
; What is NOT here: the owner record (books/owner.lisp holds the table as a
; field and calls these from its arms) and the journal I/O.
;
; The dependency on books/peer-feed-invariants is the feed cluster's
; preservation keystones: fn-feed-enqueue-preserves-feedp,
; fn-feed-restart-preserves-feedp and fn-feed-tick-step-preserves-feedp are
; what make fn-own-feed-tablep a CARRIED invariant rather than a check.  They
; are cited, never restated here.
;
; A note on the twin.  `fn-own-feed-group-matchp' is the same wildmat call as
; `fn-peer-wildmat-matchp' (books/peer-inbound.lisp).  It is repeated here
; rather than imported because books/peer-inbound sits above nntp-post and
; nntp-effects and this book must certify without them; the two are proved
; equal in books/owner-invariants.lisp, where both are visible
; (`fn-own-feed-group-matchp-is-the-inbound-matcher').

(in-package "ACL2")
(include-book "peer-feed-invariants")
(include-book "peer-config")
(include-book "article-fields")

; -----------------------------------------------------------------------------
; The peer names a configuration value holds
;
; `fn-cfg-peers' is a flat list of rows keyed by peer name, not a list of
; records: the one row every peer has exactly once is "path-identity"
; (books/peer-config.lisp, `fn-cfg-peer-rows'), so the names in row order are
; the peers.  host/store-node-host.lisp's `fn-store-cfg-peer-name-list' was a
; :program-mode copy of this fold for the CLI and now calls this function, so
; the enumeration has one owner.

(defun fn-own-feed-peer-names (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-cfg-row-b (car rows)) "path-identity")
          (cons (fn-cfg-row-a (car rows)) (fn-own-feed-peer-names (cdr rows)))
        (fn-own-feed-peer-names (cdr rows)))
    nil))

(defthm fn-own-feed-peer-names-true-listp
  (true-listp (fn-own-feed-peer-names rows)))

; -----------------------------------------------------------------------------
; The table entry: (name record feed)

(defun fn-own-feed-entry (name record f)
  (declare (xargs :guard t))
  (list name record f))
(defun fn-own-feed-entry-name (e)
  (declare (xargs :guard t))
  (fn-frame-item 0 e))
(defun fn-own-feed-entry-record (e)
  (declare (xargs :guard t))
  (fn-frame-item 1 e))
(defun fn-own-feed-entry-feed (e)
  (declare (xargs :guard t))
  (fn-frame-item 2 e))

(defthm fn-own-feed-entry-name-of-entry
  (equal (fn-own-feed-entry-name (fn-own-feed-entry name record f)) name))
(defthm fn-own-feed-entry-record-of-entry
  (equal (fn-own-feed-entry-record (fn-own-feed-entry name record f)) record))
(defthm fn-own-feed-entry-feed-of-entry
  (equal (fn-own-feed-entry-feed (fn-own-feed-entry name record f)) f))

(in-theory (disable (:d fn-own-feed-entry) (:d fn-own-feed-entry-name)
                    (:d fn-own-feed-entry-record) (:d fn-own-feed-entry-feed)))

; The record half of an entry: the peer record the scope decision reads is
; THIS peer's, and it has an outbound half.  (A peer with no outbound half
; has no feed and no entry.)
(defun fn-own-feed-outboundp (record)
  (declare (xargs :guard t))
  (and (fn-cfg-peerp record) (consp (fn-cfg-peer-outbound record)) t))

(defun fn-own-feed-record-okp (name record)
  (declare (xargs :guard t))
  (and (stringp name)
       (fn-own-feed-outboundp record)
       (equal (fn-cfg-peer-name record) name)))

; The feed half: the three names of one peer are one name.  The key is the
; string the configuration and the scheduler use; `fn-feed-peer' is the same
; name as the octets the FNFD journal carries; the feed's contact names the
; same peer.  This is the binding the w6 handoff recorded as the owner's
; obligation and did not prove.
(defun fn-own-feed-feed-okp (name f)
  (declare (xargs :guard t))
  (and (fn-feedp f)
       (equal (fn-feed-peer f) (fn-record-string-octets name))
       (fn-sched-contactp (fn-feed-contact f))
       (equal (fn-sched-contact-peer (fn-feed-contact f)) name)))

(defun fn-own-feed-entry-okp (e)
  (declare (xargs :guard t))
  (and (fn-own-feed-record-okp (fn-own-feed-entry-name e)
                               (fn-own-feed-entry-record e))
       (fn-own-feed-feed-okp (fn-own-feed-entry-name e)
                             (fn-own-feed-entry-feed e))))

; -----------------------------------------------------------------------------
; The table

(defun fn-own-feed-boundp (peer tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (or (equal (fn-own-feed-entry-name (car tbl)) peer)
          (fn-own-feed-boundp peer (cdr tbl)))
    nil))

(defun fn-own-feed-entry-of (peer tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (if (equal (fn-own-feed-entry-name (car tbl)) peer)
          (car tbl)
        (fn-own-feed-entry-of peer (cdr tbl)))
    nil))

(defun fn-own-feed-find (peer tbl)
  (declare (xargs :guard t))
  (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl)))

(defun fn-own-feed-record-of (peer tbl)
  (declare (xargs :guard t))
  (fn-own-feed-entry-record (fn-own-feed-entry-of peer tbl)))

(defun fn-own-feed-put (peer record f tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (if (equal (fn-own-feed-entry-name (car tbl)) peer)
          (cons (fn-own-feed-entry peer record f) (cdr tbl))
        (cons (car tbl) (fn-own-feed-put peer record f (cdr tbl))))
    (list (fn-own-feed-entry peer record f))))

(defun fn-own-feed-forget (peer tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (if (equal (fn-own-feed-entry-name (car tbl)) peer)
          (cdr tbl)
        (cons (car tbl) (fn-own-feed-forget peer (cdr tbl))))
    nil))

(defun fn-own-feed-names (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (cons (fn-own-feed-entry-name (car tbl)) (fn-own-feed-names (cdr tbl)))
    nil))

(defun fn-own-feed-tablep (tbl)
  (declare (xargs :guard t))
  (if (atom tbl)
      (null tbl)
    (and (fn-own-feed-entry-okp (car tbl))
         (not (fn-own-feed-boundp (fn-own-feed-entry-name (car tbl)) (cdr tbl)))
         (fn-own-feed-tablep (cdr tbl)))))

(defthm fn-own-feed-tablep-forward-true-listp
  (implies (fn-own-feed-tablep tbl) (true-listp tbl))
  :rule-classes :forward-chaining)

(defthm fn-own-feed-entry-of-of-put-same
  (equal (fn-own-feed-entry-of peer (fn-own-feed-put peer record f tbl))
         (fn-own-feed-entry peer record f)))

(defthm fn-own-feed-entry-of-of-put-other
  (implies (not (equal other peer))
           (equal (fn-own-feed-entry-of other (fn-own-feed-put peer record f tbl))
                  (fn-own-feed-entry-of other tbl))))

; A put never unbinds another peer.
(defthm fn-own-feed-entry-of-of-put-keeps-bindings
  (implies (fn-own-feed-entry-of other tbl)
           (fn-own-feed-entry-of other (fn-own-feed-put peer record f tbl)))
  :hints (("Goal" :cases ((equal other peer)))))

(defthm fn-own-feed-find-of-put-same
  (equal (fn-own-feed-find peer (fn-own-feed-put peer record f tbl)) f))

(defthm fn-own-feed-find-of-put-other
  (implies (not (equal other peer))
           (equal (fn-own-feed-find other (fn-own-feed-put peer record f tbl))
                  (fn-own-feed-find other tbl))))

(defthm fn-own-feed-boundp-of-put
  (fn-own-feed-boundp peer (fn-own-feed-put peer record f tbl)))

(defthm fn-own-feed-boundp-of-put-cases
  (implies (not (fn-own-feed-boundp other tbl))
           (iff (fn-own-feed-boundp other (fn-own-feed-put peer record f tbl))
                (equal other peer))))

(defthm fn-own-feed-boundp-when-entry
  (implies (fn-own-feed-entry-of peer tbl)
           (fn-own-feed-boundp peer tbl)))

(defthm fn-own-feed-entry-of-is-okp
  (implies (and (fn-own-feed-tablep tbl)
                (fn-own-feed-entry-of peer tbl))
           (and (fn-own-feed-entry-okp (fn-own-feed-entry-of peer tbl))
                (equal (fn-own-feed-entry-name (fn-own-feed-entry-of peer tbl))
                       peer)))
  :hints (("Goal" :induct (fn-own-feed-entry-of peer tbl)
           :in-theory (disable fn-own-feed-entry-okp))))

; What every caller of the table needs, and the only reason it has a
; recognizer: a bound peer's feed is an `fn-feedp' whose three names agree,
; and its record is that peer's own outbound-feeding record.
(defthm fn-own-feed-find-is-a-feed
  (implies (and (fn-own-feed-tablep tbl)
                (fn-own-feed-entry-of peer tbl))
           (and (fn-own-feed-feed-okp peer (fn-own-feed-find peer tbl))
                (fn-own-feed-record-okp peer (fn-own-feed-record-of peer tbl))))
  :hints (("Goal" :use fn-own-feed-entry-of-is-okp
           :in-theory (e/d (fn-own-feed-entry-okp)
                           (fn-own-feed-entry-of-is-okp fn-own-feed-record-okp
                            fn-own-feed-feed-okp
                            fn-own-feed-entry-of fn-own-feed-tablep)))))

; What the two halves give a caller, in one place.
(defthm fn-own-feed-find-is-typed
  (implies (and (fn-own-feed-tablep tbl)
                (fn-own-feed-entry-of peer tbl))
           (and (fn-feedp (fn-own-feed-find peer tbl))
                (equal (fn-feed-peer (fn-own-feed-find peer tbl))
                       (fn-record-string-octets peer))
                (fn-sched-contactp (fn-feed-contact (fn-own-feed-find peer tbl)))
                (equal (fn-sched-contact-peer
                        (fn-feed-contact (fn-own-feed-find peer tbl)))
                       peer)
                (fn-cfg-peerp (fn-own-feed-record-of peer tbl))
                (equal (fn-cfg-peer-name (fn-own-feed-record-of peer tbl))
                       peer)))
  :hints (("Goal" :use fn-own-feed-find-is-a-feed
           :in-theory (e/d (fn-own-feed-feed-okp fn-own-feed-record-okp
                            fn-own-feed-outboundp)
                           (fn-own-feed-find-is-a-feed
                            fn-own-feed-entry-of fn-own-feed-tablep
                            fn-own-feed-find fn-own-feed-record-of)))))

; From here down the two projections stay CLOSED: every rule about the table
; is stated in `fn-own-feed-find' / `fn-own-feed-record-of' vocabulary and the
; goals stay in it (docs/proof-style.md sec. 4).  Opening them turns every
; such rule into one about `fn-own-feed-entry-feed' of an `fn-own-feed-entry-of'
; and the folds below stop matching.
(local (in-theory (disable fn-own-feed-find fn-own-feed-record-of)))

(defthm fn-own-feed-tablep-of-put
  (implies (and (fn-own-feed-tablep tbl)
                (fn-own-feed-entry-okp (fn-own-feed-entry peer record f)))
           (fn-own-feed-tablep (fn-own-feed-put peer record f tbl))))

(defthm fn-own-feed-boundp-of-forget-weakens
  (implies (fn-own-feed-boundp k (fn-own-feed-forget peer tbl))
           (fn-own-feed-boundp k tbl)))

(defthm fn-own-feed-tablep-of-forget
  (implies (fn-own-feed-tablep tbl)
           (fn-own-feed-tablep (fn-own-feed-forget peer tbl)))
  :hints (("Goal" :in-theory (disable fn-own-feed-entry-okp))))

(defthm fn-own-feed-forget-is-unbound
  (implies (fn-own-feed-tablep tbl)
           (not (fn-own-feed-boundp peer (fn-own-feed-forget peer tbl)))))

; Removing the first entry named `peer' cannot change the first entry named
; anything else, whether or not the keys are distinct.
(defthm fn-own-feed-entry-of-of-forget-other
  (implies (not (equal other peer))
           (equal (fn-own-feed-entry-of other (fn-own-feed-forget peer tbl))
                  (fn-own-feed-entry-of other tbl))))

; -----------------------------------------------------------------------------
; Opening a feed from a peer record
;
; A TCP peer is an always-on contact (specs/peering.md sec. 3.1): the window is
; the whole monotonic range, so `fn-sched-contact-holdsp' inside
; `fn-feed-selection' answers "is the connection up", which is what
; `fn-feed-conn' carries.  A BP peer's window is its contact plan and is not
; built here.
;
; The retry bound is NOT a slot of the peer record (books/peer-config.lisp's
; outbound half is groups, streaming, max-queue, backoff).  It is a local
; policy constant, the same default tools/run_feed.py used; making it
; configurable is a peer-record change, which is an open item and not a host
; argument.

(defconst *fn-own-feed-horizon* *fn-clock-max*)
(defconst *fn-own-feed-retry-bound* 3)

(defun fn-own-feed-contact-of (peer)
  (declare (xargs :guard t))
  (fn-sched-contact (if (stringp peer) peer "") 0 *fn-own-feed-horizon*))

(defthm fn-own-feed-contact-of-is-a-contact
  (implies (stringp peer)
           (and (fn-sched-contactp (fn-own-feed-contact-of peer))
                (equal (fn-sched-contact-peer (fn-own-feed-contact-of peer))
                       peer)))
  :hints (("Goal" :in-theory (enable fn-sched-contactp fn-clock-timep))))

(defun fn-own-feed-limits-of (record)
  (declare (xargs :guard t))
  (fn-feed-limits (if (posp (fn-cfg-peer-max-queue record))
                      (fn-cfg-peer-max-queue record)
                    1)
                  (nfix (fn-cfg-peer-backoff record))
                  *fn-own-feed-retry-bound*
                  (and (fn-cfg-peer-streamingp record) t)))

(defthm fn-own-feed-limits-of-is-limits
  (fn-feed-limitsp (fn-own-feed-limits-of record))
  :hints (("Goal" :in-theory (enable fn-feed-limitsp))))

; The feed a configured peer with an outbound half gets at open; nil for a
; peer that is inbound-only or not a well-formed record.
; A peer name that the FNFD journal cannot carry as one `:text' field gets no
; feed: the test is here, executably, rather than as a hypothesis on the
; theorems below.  `fn-cfg-labelp' bounds the name at 256 octets of ASCII, so
; this refuses nothing a live configuration can hold; it is the one place a
; name crosses from the configuration's vocabulary into the journal's.
(defun fn-own-feed-open-one (record)
  (declare (xargs :guard t))
  (if (not (fn-own-feed-outboundp record))
      nil
    (let ((octets (fn-record-string-octets (fn-cfg-peer-name record))))
      (if (not (fn-feed-namep octets))
          nil
        (fn-feed-open octets (fn-own-feed-limits-of record)
                      (fn-own-feed-contact-of (fn-cfg-peer-name record))
                      nil)))))

(defthm fn-own-feed-record-okp-of-a-peer-record
  (implies (fn-own-feed-outboundp record)
           (fn-own-feed-record-okp (fn-cfg-peer-name record) record))
  :hints (("Goal" :in-theory (enable fn-own-feed-record-okp
                                     fn-own-feed-outboundp
                                     fn-cfg-peerp fn-cfg-labelp))))

(defthm fn-own-feed-open-one-is-a-feed
  (implies (and (fn-own-feed-outboundp record)
                (fn-own-feed-open-one record))
           (fn-own-feed-feed-okp (fn-cfg-peer-name record)
                                 (fn-own-feed-open-one record)))
  :hints (("Goal" :use ((:instance fn-own-feed-contact-of-is-a-contact
                                   (peer (fn-cfg-peer-name record))))
           :in-theory (e/d (fn-own-feed-feed-okp fn-own-feed-open-one
                            fn-own-feed-outboundp fn-feedp
                            fn-own-feed-limits-of fn-feed-limitsp
                            fn-feed-open fn-feed-distinctp
                            fn-feed-inflight-count
                            fn-feed-attempts-belowp
                            fn-cfg-peerp fn-cfg-labelp)
                           (fn-own-feed-contact-of
                            fn-own-feed-contact-of-is-a-contact
                            fn-feed-namep)))))

(defthm fn-own-feed-open-one-is-an-entry
  (implies (and (fn-own-feed-outboundp record)
                (fn-own-feed-open-one record))
           (fn-own-feed-entry-okp
            (fn-own-feed-entry (fn-cfg-peer-name record) record
                               (fn-own-feed-open-one record))))
  :hints (("Goal" :use (fn-own-feed-record-okp-of-a-peer-record
                        fn-own-feed-open-one-is-a-feed)
           :in-theory (e/d (fn-own-feed-entry-okp)
                           (fn-own-feed-record-okp-of-a-peer-record
                            fn-own-feed-open-one-is-a-feed
                            fn-own-feed-record-okp fn-own-feed-feed-okp
                            fn-own-feed-open-one)))))

; -----------------------------------------------------------------------------
; Building the table from a configuration value's peer rows
;
; Merge, never replace.  A peer already in the table keeps its LIVE feed: the
; queue is durable state and a reconfiguration is a decision change, not a
; loss of committed work (specs/reconfiguration.md; K7).  Its RECORD is
; refreshed, because the scope decision is a decision and must follow the
; configuration.  A peer that is gone from the configuration, or has lost its
; outbound half, is forgotten only when its feed is idle -- nothing in flight
; and nothing queued (the w6 handoff's feed-idle condition) -- and is
; otherwise kept until it drains.

(defun fn-own-feed-idlep (f)
  (declare (xargs :guard t))
  (and (equal (fn-feed-inflight-count (fn-feed-queue f)) 0)
       (null (fn-feed-head-queued (fn-feed-queue f)))))

(defun fn-own-feed-install-one (name peers tbl)
  (declare (xargs :guard t))
  (let* ((record (fn-cfg-peer-find name peers))
         (f (if (fn-own-feed-entry-of name tbl)
                (fn-own-feed-find name tbl)
              (fn-own-feed-open-one record))))
    (if (and (fn-own-feed-outboundp record)
             (equal (fn-cfg-peer-name record) name)
             f)
        (fn-own-feed-put name record f tbl)
      tbl)))

(defun fn-own-feed-install (names peers tbl)
  (declare (xargs :guard t))
  (if (consp names)
      (fn-own-feed-install (cdr names) peers
                           (fn-own-feed-install-one (car names) peers tbl))
    tbl))

; The peers of the table the configuration no longer feeds, whose feed has
; drained.
(defun fn-own-feed-retire-one (key peers tbl)
  (declare (xargs :guard t))
  (if (and (fn-own-feed-entry-of key tbl)
           (fn-own-feed-idlep (fn-own-feed-find key tbl))
           (not (fn-own-feed-outboundp (fn-cfg-peer-find key peers))))
      (fn-own-feed-forget key tbl)
    tbl))

(defun fn-own-feed-retire (keys peers tbl)
  (declare (xargs :guard t))
  (if (consp keys)
      (fn-own-feed-retire (cdr keys) peers
                          (fn-own-feed-retire-one (car keys) peers tbl))
    tbl))

; The table the owner holds for one configuration value.  Called at open and
; again after every (:set-peer ...) / (:remove-peer ...) delta.
(defun fn-own-feed-reconfigure (tbl peers)
  (declare (xargs :guard t))
  (fn-own-feed-install (fn-own-feed-peer-names peers) peers
                       (fn-own-feed-retire (fn-own-feed-names tbl) peers tbl)))

; Refreshing a bound peer's record keeps the entry well formed: the record
; half comes from the configuration and the feed half from the entry that was
; already there.  This is what makes a reconfiguration a change of DECISIONS
; and not of committed state.
(local (defthm fn-own-feed-entry-okp-of-refresh
  (implies (and (fn-own-feed-tablep tbl)
                (fn-own-feed-entry-of name tbl)
                (fn-own-feed-outboundp record)
                (equal (fn-cfg-peer-name record) name))
           (fn-own-feed-entry-okp
            (fn-own-feed-entry name record (fn-own-feed-find name tbl))))
  :hints (("Goal" :use ((:instance fn-own-feed-find-is-a-feed (peer name))
                        fn-own-feed-record-okp-of-a-peer-record)
           :in-theory (e/d (fn-own-feed-entry-okp)
                           (fn-own-feed-find-is-a-feed
                            fn-own-feed-record-okp-of-a-peer-record
                            fn-own-feed-record-okp fn-own-feed-feed-okp
                            fn-own-feed-entry-of fn-own-feed-tablep
                            fn-own-feed-find))))))

; The two ways an entry is well formed at a key, each stated AT the key the
; installer puts it under, so the lift below is a substitution and not a
; search for an equality to orient.
(local (defthm fn-own-feed-open-one-is-an-entry-at
  (implies (and (fn-own-feed-outboundp record)
                (fn-own-feed-open-one record)
                (equal (fn-cfg-peer-name record) name))
           (fn-own-feed-entry-okp
            (fn-own-feed-entry name record (fn-own-feed-open-one record))))
  :hints (("Goal" :use fn-own-feed-open-one-is-an-entry
           :in-theory (disable fn-own-feed-open-one-is-an-entry
                               fn-own-feed-entry-okp fn-own-feed-open-one
                               fn-own-feed-outboundp)))))

(defthm fn-own-feed-tablep-of-install-one
  (implies (fn-own-feed-tablep tbl)
           (fn-own-feed-tablep (fn-own-feed-install-one name peers tbl)))
  :hints (("Goal" :in-theory (disable fn-own-feed-entry-okp
                                      fn-own-feed-open-one
                                      fn-own-feed-outboundp))))

(defthm fn-own-feed-tablep-of-install
  (implies (fn-own-feed-tablep tbl)
           (fn-own-feed-tablep (fn-own-feed-install names peers tbl)))
  :hints (("Goal" :induct (fn-own-feed-install names peers tbl)
           :in-theory (disable fn-own-feed-install-one))))

(defthm fn-own-feed-tablep-of-retire-one
  (implies (fn-own-feed-tablep tbl)
           (fn-own-feed-tablep (fn-own-feed-retire-one key peers tbl))))

(defthm fn-own-feed-tablep-of-retire
  (implies (fn-own-feed-tablep tbl)
           (fn-own-feed-tablep (fn-own-feed-retire keys peers tbl)))
  :hints (("Goal" :induct (fn-own-feed-retire keys peers tbl)
           :in-theory (disable fn-own-feed-retire-one))))

(defthm fn-own-feed-tablep-of-reconfigure
  (implies (fn-own-feed-tablep tbl)
           (fn-own-feed-tablep (fn-own-feed-reconfigure tbl peers))))

; KEYSTONE.  A reconfiguration never loses queued or in-flight work: only an
; idle feed is retired, and only when the configuration stopped feeding it.
(local (defthm fn-own-feed-retire-one-keeps-a-busy-feed
  (implies (not (fn-own-feed-idlep (fn-own-feed-find peer tbl)))
           (equal (fn-own-feed-entry-of peer
                                        (fn-own-feed-retire-one key peers tbl))
                  (fn-own-feed-entry-of peer tbl)))
  :hints (("Goal" :do-not-induct t :cases ((equal peer key))
           :in-theory (e/d (fn-own-feed-retire-one)
                           (fn-own-feed-idlep fn-own-feed-find
                            fn-own-feed-entry-of fn-own-feed-forget))))))

(local (defthm fn-own-feed-retire-one-keeps-a-busy-find
  (implies (not (fn-own-feed-idlep (fn-own-feed-find peer tbl)))
           (equal (fn-own-feed-find peer (fn-own-feed-retire-one key peers tbl))
                  (fn-own-feed-find peer tbl)))
  :hints (("Goal" :use fn-own-feed-retire-one-keeps-a-busy-feed
           :in-theory (e/d (fn-own-feed-find)
                           (fn-own-feed-retire-one-keeps-a-busy-feed
                            fn-own-feed-retire-one fn-own-feed-entry-of
                            fn-own-feed-idlep))))))

(defthm fn-own-feed-retire-keeps-a-busy-feed
  (implies (not (fn-own-feed-idlep (fn-own-feed-find peer tbl)))
           (equal (fn-own-feed-entry-of peer
                                        (fn-own-feed-retire keys peers tbl))
                  (fn-own-feed-entry-of peer tbl)))
  :hints (("Goal" :induct (fn-own-feed-retire keys peers tbl)
           :in-theory (disable fn-own-feed-retire-one))))

(local (defthm fn-own-feed-install-one-keeps-the-queue
  (implies (fn-own-feed-entry-of peer tbl)
           (equal (fn-own-feed-find peer
                                    (fn-own-feed-install-one name peers tbl))
                  (fn-own-feed-find peer tbl)))
  :hints (("Goal" :in-theory (enable fn-own-feed-find)))))

(local (defthm fn-own-feed-install-one-keeps-the-binding
  (implies (fn-own-feed-entry-of peer tbl)
           (fn-own-feed-entry-of peer (fn-own-feed-install-one name peers tbl)))))

(defthm fn-own-feed-install-keeps-the-queue
  (implies (fn-own-feed-entry-of peer tbl)
           (equal (fn-own-feed-find peer (fn-own-feed-install names peers tbl))
                  (fn-own-feed-find peer tbl)))
  :hints (("Goal" :induct (fn-own-feed-install names peers tbl)
           :in-theory (disable fn-own-feed-install-one))))

; -----------------------------------------------------------------------------
; Restart: the owner's reopen fences every feed
;
; A process death loses every outbound connection, so on reopen every feed is
; `fn-feed-restart'ed: the in-flight entry returns to :queued with its attempt
; retired and the connection forgotten, so the next command for it is a
; CHECK or an IHAVE and never a blind TAKETHIS (K5, specs/peering.md sec. 3.3).

(defun fn-own-feed-restart-all (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (cons (fn-own-feed-entry (fn-own-feed-entry-name (car tbl))
                               (fn-own-feed-entry-record (car tbl))
                               (fn-feed-restart (fn-own-feed-entry-feed (car tbl))))
            (fn-own-feed-restart-all (cdr tbl)))
    nil))

; Each of the three is `fn-feedp' from the feed cluster's own preservation
; keystone (books/peer-feed-invariants.lisp), CITED and never restated, plus
; the two name equalities, which hold because every transition rebuilds the
; record through `fn-feed-make' with this feed's peer and contact.
(local (defthm fn-feed-restart-keeps-peer-and-contact
  (and (equal (fn-feed-peer (fn-feed-restart f)) (fn-feed-peer f))
       (equal (fn-feed-contact (fn-feed-restart f)) (fn-feed-contact f)))
  :hints (("Goal" :in-theory (e/d (fn-feed-restart fn-feed-with-conn
                                   fn-feed-with-queue)
                                  (fn-feedp))))))

(local (defthm fn-own-feed-restart-keeps-the-feed-half
  (implies (fn-own-feed-feed-okp name f)
           (fn-own-feed-feed-okp name (fn-feed-restart f)))
  :hints (("Goal" :use (fn-feed-restart-preserves-feedp
                        fn-feed-restart-keeps-peer-and-contact)
           :in-theory (e/d (fn-own-feed-feed-okp)
                           (fn-feedp fn-feed-restart
                            fn-feed-restart-preserves-feedp
                            fn-feed-restart-keeps-peer-and-contact
                            fn-record-string-octets))))))

(local (defthm fn-own-feed-restart-keeps-the-entry
  (implies (fn-own-feed-entry-okp e)
           (fn-own-feed-entry-okp
            (fn-own-feed-entry (fn-own-feed-entry-name e)
                               (fn-own-feed-entry-record e)
                               (fn-feed-restart (fn-own-feed-entry-feed e)))))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-entry-okp)
                                  (fn-own-feed-feed-okp fn-feedp
                                   fn-record-string-octets
                                   fn-feed-restart fn-feed-enqueue
                                   fn-feed-tick-step fn-feed-offer mv-nth
                                   fn-own-feed-record-okp))))))

(local (defthm fn-own-feed-boundp-of-restart-all
  (equal (fn-own-feed-boundp peer (fn-own-feed-restart-all tbl))
         (fn-own-feed-boundp peer tbl))))

(defthm fn-own-feed-tablep-of-restart-all
  (implies (fn-own-feed-tablep tbl)
           (fn-own-feed-tablep (fn-own-feed-restart-all tbl)))
  :hints (("Goal" :in-theory (disable fn-own-feed-entry-okp fn-feed-restart
                                      fn-feedp fn-record-string-octets))))

(defthm fn-own-feed-restart-all-restarts-each-feed
  (implies (fn-own-feed-entry-of peer tbl)
           (equal (fn-own-feed-find peer (fn-own-feed-restart-all tbl))
                  (fn-feed-restart (fn-own-feed-find peer tbl))))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-find)
                                  (fn-feed-restart fn-feedp
                                   fn-own-feed-entry-okp)))))

; -----------------------------------------------------------------------------
; Scope: what an article's own octets say
;
; The article is parsed once, here, from the octets the submission carried;
; the Newsgroups names and the Path value are read through the proved field
; views (books/article-fields.lisp, books/path.lisp) and never by a second
; parser.

(defun fn-own-feed-article-of (octets)
  (declare (xargs :guard t))
  (let ((parsed (fn-article-parse octets)))
    (if (and (fn-article-result-okp parsed)
             (true-listp parsed)
             (fn-article-syntax-p (fn-article-result-article parsed)))
        (fn-article-result-article parsed)
      nil)))

(defthm fn-own-feed-article-of-is-syntax
  (implies (fn-own-feed-article-of octets)
           (fn-article-syntax-p (fn-own-feed-article-of octets))))

(defun fn-own-feed-groups-of (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((a (fn-own-feed-article-of octets)))
    (if (null a)
        nil
      (let ((check (fn-af-proto-article-check a)))
        (if (equal (fn-af-status-kind check) :ok)
            (fn-frame-item 2 check)
          nil)))))

(defun fn-own-feed-path-of (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((a (fn-own-feed-article-of octets)))
    (if (null a) nil (fn-af-path-field-value a))))

; The parser stays SHUT below this line.  Opened, one goal about the feed
; table pays for `fn-article-parse', `fn-af-proto-article-check' and the
; whole newsgroups grammar: the accept keystone went over two million steps
; before this (docs/proof-style.md sec. 9).
(local (in-theory (disable fn-own-feed-article-of fn-own-feed-groups-of
                           fn-own-feed-path-of)))

; -----------------------------------------------------------------------------
; The offer decision, RFC 5537 sec. 3.6
;
; One wildmat call; see the twin note in this book's header.
(defun fn-own-feed-group-matchp (wildmat-text name-octets)
  (declare (xargs :guard t))
  (let ((r (fn-wildmat-match (fn-record-string-octets wildmat-text)
                             name-octets)))
    (and (fn-wildmat-result-okp r) (fn-wildmat-result-value r) t)))

(defun fn-own-feed-any-matchp (wildmat-text groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (or (fn-own-feed-group-matchp wildmat-text (car groups))
          (fn-own-feed-any-matchp wildmat-text (cdr groups)))
    nil))

; `origin' is the name of the peer the article arrived from, or nil for a
; local POST.  The three refusals, in the order the RFC reads them:
;   * the peer has no outbound half, or no group of the article matches its
;     outbound wildmat (RFC 3977 sec. 4 wildmat; which groups is local policy);
;   * the peer's own path-identity is already in the article's Path, so it has
;     seen it (RFC 5537 sec. 3.6: a relaying agent does not offer an article
;     to a site already named in Path);
;   * the peer IS the peer it came from.  This is stronger than the RFC: the
;     origin's identity is normally in Path already, but fn does not depend on
;     a peer having prepended it.
(defun fn-own-feed-offerablep (record origin groups path)
  (declare (xargs :guard t))
  (and (fn-own-feed-outboundp record)
       (fn-own-feed-any-matchp (fn-cfg-peer-outbound-groups record) groups)
       (not (fn-path-names-p
             path (fn-record-string-octets
                   (fn-cfg-peer-path-identity record))))
       (not (equal origin (fn-cfg-peer-name record)))
       t))

(defun fn-own-feed-targets (tbl origin groups path)
  (declare (xargs :guard t))
  (if (consp tbl)
      (let ((rest (fn-own-feed-targets (cdr tbl) origin groups path)))
        (if (fn-own-feed-offerablep (fn-own-feed-entry-record (car tbl))
                                    origin groups path)
            (cons (fn-own-feed-entry-name (car tbl)) rest)
          rest))
    nil))

(defthm fn-own-feed-targets-true-listp
  (true-listp (fn-own-feed-targets tbl origin groups path)))

(defthm fn-own-feed-target-is-bound
  (implies (member-equal name (fn-own-feed-targets tbl origin groups path))
           (fn-own-feed-boundp name tbl))
  :hints (("Goal" :induct (fn-own-feed-targets tbl origin groups path)
           :in-theory (disable fn-own-feed-offerablep fn-own-feed-entry-okp
                               fn-feedp fn-record-string-octets))))

; A key bound in a TABLE finds a real entry.  Without the recognizer this is
; false and the degenerate value says why: the table (nil), whose only entry
; is the atom nil, binds the key nil and finds nil.  A table's keys are
; strings, so the case cannot arise.
(defthm fn-own-feed-boundp-is-an-entry
  (implies (and (fn-own-feed-tablep tbl) (fn-own-feed-boundp peer tbl))
           (fn-own-feed-entry-of peer tbl))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-entry-okp
                                   fn-own-feed-record-okp)
                                  (fn-own-feed-feed-okp fn-feedp
                                   fn-own-feed-outboundp
                                   fn-record-string-octets)))))

(defthm fn-own-feed-target-has-an-entry
  (implies (and (fn-own-feed-tablep tbl)
                (member-equal name (fn-own-feed-targets tbl origin groups path)))
           (fn-own-feed-entry-of name tbl))
  :hints (("Goal" :use (fn-own-feed-target-is-bound
                        (:instance fn-own-feed-boundp-is-an-entry (peer name)))
           :in-theory (disable fn-own-feed-target-is-bound
                               fn-own-feed-boundp-is-an-entry
                               fn-own-feed-targets fn-own-feed-tablep
                               fn-own-feed-entry-of fn-own-feed-boundp))))

; KEYSTONE (first half).  Every peer the owner offers to is a peer of the
; table whose own record passes the scope decision.
(defthm fn-own-feed-target-is-offerable
  (implies (and (fn-own-feed-tablep tbl)
                (member-equal name (fn-own-feed-targets tbl origin groups path)))
           (fn-own-feed-offerablep (fn-own-feed-record-of name tbl)
                                   origin groups path))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-record-of)
                                  (fn-own-feed-offerablep)))))

; KEYSTONE (second half).  No peer of the table that passes is left out: the
; two halves together are "exactly the matching peers".
(defthm fn-own-feed-targets-omit-no-offerable-peer
  (implies (and (fn-own-feed-tablep tbl)
                (fn-own-feed-entry-of name tbl)
                (fn-own-feed-offerablep (fn-own-feed-record-of name tbl)
                                        origin groups path))
           (member-equal name (fn-own-feed-targets tbl origin groups path)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-record-of)
                                  (fn-own-feed-offerablep)))))

; KEYSTONE.  K2's outbound half: the feed never offers a loop.  Neither the
; peer the article came from nor a peer whose path-identity the Path already
; names is ever a target.
(defthm fn-own-feed-never-offers-a-loop
  (implies (and (fn-own-feed-tablep tbl)
                (member-equal name (fn-own-feed-targets tbl origin groups path)))
           (and (not (equal name origin))
                (not (fn-path-names-p
                      path (fn-record-string-octets
                            (fn-cfg-peer-path-identity
                             (fn-own-feed-record-of name tbl)))))))
  :hints (("Goal" :use (fn-own-feed-target-is-offerable
                        fn-own-feed-target-has-an-entry
                        (:instance fn-own-feed-find-is-typed (peer name)))
           :in-theory (e/d (fn-own-feed-offerablep)
                           (fn-own-feed-target-is-offerable
                            fn-own-feed-target-has-an-entry
                            fn-own-feed-find-is-typed fn-own-feed-outboundp
                            fn-own-feed-any-matchp fn-own-feed-record-of
                            fn-own-feed-entry-of
                            fn-record-string-octets
                            fn-own-feed-targets fn-own-feed-tablep)))))

; KEYSTONE.  Scope: a target's outbound wildmat matches one of the article's
; own Newsgroups names.
(defthm fn-own-feed-target-is-in-scope
  (implies (and (fn-own-feed-tablep tbl)
                (member-equal name (fn-own-feed-targets tbl origin groups path)))
           (fn-own-feed-any-matchp
            (fn-cfg-peer-outbound-groups (fn-own-feed-record-of name tbl))
            groups))
  :hints (("Goal" :use fn-own-feed-target-is-offerable
           :in-theory (e/d (fn-own-feed-offerablep)
                           (fn-own-feed-target-is-offerable
                            fn-own-feed-outboundp fn-own-feed-any-matchp
                            fn-own-feed-record-of fn-own-feed-entry-of
                            fn-record-string-octets
                            fn-own-feed-targets fn-own-feed-tablep)))))

; -----------------------------------------------------------------------------
; The enqueue, on exactly the targets

(defun fn-own-feed-enqueue-all (names tbl msgid tick)
  (declare (xargs :guard t))
  (if (consp names)
      (fn-own-feed-enqueue-all
       (cdr names)
       (let ((e (fn-own-feed-entry-of (car names) tbl)))
         (if (null e)
             tbl
           (fn-own-feed-put (car names) (fn-own-feed-entry-record e)
                            (fn-feed-enqueue (fn-own-feed-entry-feed e)
                                             msgid tick)
                            tbl)))
       msgid tick)
    tbl))

; The one function books/owner.lisp calls when a submission becomes durable.
; `origin' is nil for a POST and the peer name for a transit article; `msgid'
; is the Message-ID as octets and `octets' the article as accepted.
(defun fn-own-feed-accept (tbl origin msgid octets tick)
  (declare (xargs :guard t :verify-guards nil))
  (fn-own-feed-enqueue-all
   (fn-own-feed-targets tbl origin (fn-own-feed-groups-of octets)
                        (fn-own-feed-path-of octets))
   tbl msgid tick))

(local (defthm fn-feed-enqueue-keeps-peer-and-contact
  (and (equal (fn-feed-peer (fn-feed-enqueue f msgid tick)) (fn-feed-peer f))
       (equal (fn-feed-contact (fn-feed-enqueue f msgid tick))
              (fn-feed-contact f)))
  :hints (("Goal" :in-theory (e/d (fn-feed-enqueue fn-feed-with-queue)
                                  (fn-feedp))))))

(local (defthm fn-own-feed-enqueue-keeps-the-feed-half
  (implies (fn-own-feed-feed-okp name f)
           (fn-own-feed-feed-okp name (fn-feed-enqueue f msgid tick)))
  :hints (("Goal" :use (fn-feed-enqueue-preserves-feedp
                        fn-feed-enqueue-keeps-peer-and-contact)
           :in-theory (e/d (fn-own-feed-feed-okp)
                           (fn-feedp fn-feed-enqueue
                            fn-feed-enqueue-preserves-feedp
                            fn-feed-enqueue-keeps-peer-and-contact
                            fn-record-string-octets))))))

(local (defthm fn-own-feed-enqueue-keeps-the-entry
  (implies (fn-own-feed-entry-okp e)
           (fn-own-feed-entry-okp
            (fn-own-feed-entry (fn-own-feed-entry-name e)
                               (fn-own-feed-entry-record e)
                               (fn-feed-enqueue (fn-own-feed-entry-feed e)
                                                msgid tick))))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-entry-okp)
                                  (fn-own-feed-feed-okp fn-feedp
                                   fn-record-string-octets
                                   fn-feed-restart fn-feed-enqueue
                                   fn-feed-tick-step fn-feed-offer mv-nth
                                   fn-own-feed-record-okp))))))

(local (defthm fn-own-feed-entry-okp-of-enqueue-at
  (implies (and (fn-own-feed-tablep tbl) (fn-own-feed-entry-of peer tbl))
           (fn-own-feed-entry-okp
            (fn-own-feed-entry
             peer
             (fn-own-feed-entry-record (fn-own-feed-entry-of peer tbl))
             (fn-feed-enqueue
              (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))
              msgid tick))))
  :hints (("Goal" :use ((:instance fn-own-feed-enqueue-keeps-the-entry
                                   (e (fn-own-feed-entry-of peer tbl)))
                        fn-own-feed-entry-of-is-okp)
           :in-theory (disable fn-own-feed-enqueue-keeps-the-entry
                               fn-own-feed-entry-of-is-okp
                               fn-own-feed-entry-okp fn-own-feed-entry-of
                               fn-own-feed-tablep fn-feed-enqueue)))))

(defthm fn-own-feed-tablep-of-enqueue-all
  (implies (fn-own-feed-tablep tbl)
           (fn-own-feed-tablep (fn-own-feed-enqueue-all names tbl msgid tick))))

(defthm fn-own-feed-tablep-of-accept
  (implies (fn-own-feed-tablep tbl)
           (fn-own-feed-tablep (fn-own-feed-accept tbl origin msgid octets tick))))

; KEYSTONE.  The enqueue reaches no peer outside the list: a peer that is not
; named keeps the feed it had.
(defthm fn-own-feed-enqueue-all-touches-only-its-names
  (implies (not (member-equal other names))
           (equal (fn-own-feed-entry-of
                   other (fn-own-feed-enqueue-all names tbl msgid tick))
                  (fn-own-feed-entry-of other tbl))))

; KEYSTONE.  The enqueue on a durable acceptance reaches exactly the peers
; `fn-own-feed-targets' names: every other peer's feed is unchanged.
(defthm fn-own-feed-accept-touches-only-its-targets
  (implies (not (member-equal
                 other
                 (fn-own-feed-targets tbl origin (fn-own-feed-groups-of octets)
                                      (fn-own-feed-path-of octets))))
           (equal (fn-own-feed-entry-of
                   other (fn-own-feed-accept tbl origin msgid octets tick))
                  (fn-own-feed-entry-of other tbl)))
  :hints (("Goal" :in-theory (disable fn-own-feed-targets))))

; KEYSTONE.  The peer an article arrived from never has it enqueued back:
; `fn-own-feed-never-offers-a-loop' transported to the table the owner holds.
(defthm fn-own-feed-accept-never-enqueues-on-the-origin
  (implies (fn-own-feed-tablep tbl)
           (equal (fn-own-feed-entry-of
                   origin (fn-own-feed-accept tbl origin msgid octets tick))
                  (fn-own-feed-entry-of origin tbl)))
  :hints (("Goal"
           :use ((:instance fn-own-feed-accept-touches-only-its-targets
                            (other origin))
                 (:instance fn-own-feed-never-offers-a-loop
                            (name origin)
                            (groups (fn-own-feed-groups-of octets))
                            (path (fn-own-feed-path-of octets))))
           :in-theory (disable fn-own-feed-accept-touches-only-its-targets
                               fn-own-feed-never-offers-a-loop
                               fn-own-feed-targets fn-own-feed-accept
                               fn-own-feed-tablep))))

; -----------------------------------------------------------------------------
; The tick: one feed step per peer
;
; `fn-feed-tick-step' is the function the host calls (books/peer-feed.lisp
; says so, and every feed keystone is stated over it).  The fold below is one
; call per peer in table order; the result is (table . effects), each effect
; list tagged with the peer whose feed emitted it so the host knows which
; connection to write to.  Selection is gated inside `fn-feed-selection' by
; `fn-sched-contact-holdsp' on that peer's own contact, which is the
; scheduler's contact model and the reason a feed carries an
; `fn-sched-contactp' at all.

(defun fn-own-feed-tick-peer (peer tbl obs)
  (declare (xargs :guard t))
  (let ((e (fn-own-feed-entry-of peer tbl)))
    (if (null e)
        (cons tbl nil)
      (mv-let (g effects) (fn-feed-tick-step (fn-own-feed-entry-feed e) obs)
        (cons (fn-own-feed-put peer (fn-own-feed-entry-record e) g tbl)
              (if (null effects) nil (list (cons peer effects))))))))

(defun fn-own-feed-tick (names tbl obs)
  (declare (xargs :guard t))
  (if (consp names)
      (let* ((one (fn-own-feed-tick-peer (car names) tbl obs))
             (rest (fn-own-feed-tick (cdr names) (car one) obs)))
        (cons (car rest) (append (cdr one) (cdr rest))))
    (cons tbl nil)))

(local (defthm fn-feed-tick-step-keeps-peer-and-contact
  (and (equal (fn-feed-peer (mv-nth 0 (fn-feed-tick-step f obs)))
              (fn-feed-peer f))
       (equal (fn-feed-contact (mv-nth 0 (fn-feed-tick-step f obs)))
              (fn-feed-contact f)))
  :hints (("Goal" :in-theory (e/d (fn-feed-tick-step fn-feed-offer)
                                  (fn-feedp fn-feed-selection))))))

(local (defthm fn-own-feed-tick-step-keeps-the-feed-half
  (implies (fn-own-feed-feed-okp name f)
           (fn-own-feed-feed-okp name (mv-nth 0 (fn-feed-tick-step f obs))))
  :hints (("Goal" :use (fn-feed-tick-step-preserves-feedp
                        fn-feed-tick-step-keeps-peer-and-contact)
           :in-theory (e/d (fn-own-feed-feed-okp)
                           (fn-feedp fn-feed-tick-step
                            fn-feed-tick-step-preserves-feedp
                            fn-feed-tick-step-keeps-peer-and-contact
                            fn-record-string-octets))))))

(local (defthm fn-own-feed-tick-step-keeps-the-entry
  (implies (fn-own-feed-entry-okp e)
           (fn-own-feed-entry-okp
            (fn-own-feed-entry
             (fn-own-feed-entry-name e) (fn-own-feed-entry-record e)
             (mv-nth 0 (fn-feed-tick-step (fn-own-feed-entry-feed e) obs)))))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-entry-okp)
                                  (fn-own-feed-feed-okp fn-feedp
                                   fn-record-string-octets
                                   fn-feed-restart fn-feed-enqueue
                                   fn-feed-tick-step fn-feed-offer mv-nth
                                   fn-own-feed-record-okp))))))

(local (defthm fn-own-feed-entry-okp-of-tick-at
  (implies (and (fn-own-feed-tablep tbl) (fn-own-feed-entry-of peer tbl))
           (fn-own-feed-entry-okp
            (fn-own-feed-entry
             peer
             (fn-own-feed-entry-record (fn-own-feed-entry-of peer tbl))
             (mv-nth 0 (fn-feed-tick-step
                        (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))
                        obs)))))
  :hints (("Goal" :use ((:instance fn-own-feed-tick-step-keeps-the-entry
                                   (e (fn-own-feed-entry-of peer tbl)))
                        fn-own-feed-entry-of-is-okp)
           :in-theory (disable fn-own-feed-tick-step-keeps-the-entry
                               fn-own-feed-entry-of-is-okp
                               fn-own-feed-entry-okp fn-own-feed-entry-of
                               fn-own-feed-tablep fn-feed-tick-step mv-nth)))))

(defthm fn-own-feed-tablep-of-tick-peer
  (implies (fn-own-feed-tablep tbl)
           (fn-own-feed-tablep (car (fn-own-feed-tick-peer peer tbl obs))))
  :hints (("Goal" :in-theory (disable mv-nth fn-feed-tick-step
                                      fn-own-feed-entry-okp fn-feedp
                                      fn-record-string-octets))))

(defthm fn-own-feed-tablep-of-tick
  (implies (fn-own-feed-tablep tbl)
           (fn-own-feed-tablep (car (fn-own-feed-tick names tbl obs))))
  :hints (("Goal" :in-theory (disable fn-own-feed-tick-peer))))

; KEYSTONE.  One peer's tick is that peer's own `fn-feed-tick-step' and
; touches no other peer: the subject rule for the fold, the shape
; `fn-sched-table-tick-is-the-peer-tick' has for the scheduler table.
(defthm fn-own-feed-tick-peer-is-the-feed-tick
  (implies (fn-own-feed-entry-of peer tbl)
           (and (equal (fn-own-feed-find peer
                                         (car (fn-own-feed-tick-peer peer tbl obs)))
                       (mv-nth 0 (fn-feed-tick-step (fn-own-feed-find peer tbl)
                                                    obs)))
                (equal (cdr (fn-own-feed-tick-peer peer tbl obs))
                       (if (null (mv-nth 1 (fn-feed-tick-step
                                            (fn-own-feed-find peer tbl) obs)))
                           nil
                         (list (cons peer
                                     (mv-nth 1 (fn-feed-tick-step
                                                (fn-own-feed-find peer tbl)
                                                obs))))))))
  :hints (("Goal" :in-theory (enable fn-own-feed-find))))

(defthm fn-own-feed-tick-peer-touches-only-its-peer
  (implies (not (equal other peer))
           (equal (fn-own-feed-entry-of
                   other (car (fn-own-feed-tick-peer peer tbl obs)))
                  (fn-own-feed-entry-of other tbl))))

; The two projections the host takes of a tagged feed effect list, in the
; shape `fn-served-reply-octets' and `fn-served-closingp' have for the served
; path: which peer's connection to write to, and what to write.  The host
; reads these and decides nothing.
(defun fn-own-feed-effect-peer (tagged)
  (declare (xargs :guard t))
  (fn-frame-item 0 (fn-frame-item 0 tagged)))

(defun fn-own-feed-effect-octets (tagged)
  (declare (xargs :guard t))
  (let* ((entry (fn-frame-item 0 tagged))
         (effects (if (consp entry) (cdr entry) nil))
         (command (fn-frame-item 0 effects)))
    (if (equal (fn-frame-item 0 command) :command)
        (fn-frame-item 2 command)
      nil)))

; The tick's effect list names the peer whose feed emitted it, and carries
; the command line that peer's offer rendered.
(defthm fn-own-feed-tick-peer-effect-names-its-peer
  (implies (cdr (fn-own-feed-tick-peer peer tbl obs))
           (and (equal (fn-own-feed-effect-peer
                        (cdr (fn-own-feed-tick-peer peer tbl obs)))
                       peer)
                (equal (fn-own-feed-effect-octets
                        (cdr (fn-own-feed-tick-peer peer tbl obs)))
                       (fn-frame-item
                        2 (car (mv-nth 1 (fn-feed-tick-step
                                          (fn-own-feed-find peer tbl) obs)))))))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-tick-peer fn-own-feed-find)
                                  (fn-feed-tick-step mv-nth)))))

; -----------------------------------------------------------------------------
; The FNFD records each transition authorizes
;
; "Durable before the effect": the host appends these to
; <journal>/feed/<peer>.fnfd and only then emits the wire effect.  The record
; VALUES are built here so that the host frames what ACL2 decided and encodes
; no field of its own (books/peer-feed.lisp, `fn-feed-encode').

(defun fn-own-feed-enqueue-records (names msgid tick)
  (declare (xargs :guard t))
  (if (consp names)
      (cons (fn-feed-journal-entry
             :feed-enqueue (list (fn-record-string-octets (car names))
                                 msgid (nfix tick)))
            (fn-own-feed-enqueue-records (cdr names) msgid tick))
    nil))

(defun fn-own-feed-accept-records (tbl origin msgid octets tick)
  (declare (xargs :guard t :verify-guards nil))
  (fn-own-feed-enqueue-records
   (fn-own-feed-targets tbl origin (fn-own-feed-groups-of octets)
                        (fn-own-feed-path-of octets))
   msgid tick))

(defun fn-own-feed-offer-record (peer msgid attempt tick)
  (declare (xargs :guard t))
  (fn-feed-journal-entry :feed-offer
                         (list (fn-record-string-octets peer) msgid
                               (nfix attempt) (nfix tick))))

(defun fn-own-feed-sent-record (peer msgid attempt)
  (declare (xargs :guard t))
  (fn-feed-journal-entry :feed-sent
                         (list (fn-record-string-octets peer) msgid
                               (nfix attempt))))

(defun fn-own-feed-outcome-record (peer msgid attempt code)
  (declare (xargs :guard t))
  (fn-feed-journal-entry :feed-outcome
                         (list (fn-record-string-octets peer) msgid
                               (nfix attempt) (nfix code))))

(defun fn-own-feed-restart-record (peer)
  (declare (xargs :guard t))
  (fn-feed-journal-entry :feed-restart
                         (list (fn-record-string-octets peer))))

(defun fn-own-feed-restart-records (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (cons (fn-own-feed-restart-record (fn-own-feed-entry-name (car tbl)))
            (fn-own-feed-restart-records (cdr tbl)))
    nil))

; -----------------------------------------------------------------------------
; The reply reader (RFC 3977 sec. 3.2), in ACL2
;
; tools/run_feed.py split the three-digit status in Python and the w6 handoff
; recorded that as an open twin.  It is here now: the host hands the owner one
; reply LINE and ACL2 reads the code.  The Message-ID a CHECK or TAKETHIS
; reply echoes is not read back from the wire -- at most one entry is in
; flight per peer (`fn-feedp'), so the in-flight Message-ID the owner already
; holds is the unambiguous subject, which is also how `fn-feed-observe' reads
; an IHAVE reply that carries none.

(defun fn-own-feed-digitp (b)
  (declare (xargs :guard t))
  (and (natp b) (<= 48 b) (<= b 57)))

; RFC 3977 sec. 3.2: the first digit of a reply code is 1 to 5, so a line
; that starts "0.." or "9.." is not a reply and reads as no code at all.
(defun fn-own-feed-response-code (octets)
  (declare (xargs :guard t))
  (let ((a (fn-frame-item 0 octets))
        (b (fn-frame-item 1 octets))
        (c (fn-frame-item 2 octets)))
    (if (and (fn-own-feed-digitp a) (<= 49 a) (<= a 53)
             (fn-own-feed-digitp b) (fn-own-feed-digitp c)
             (or (not (consp (cdr (cdr (cdr octets)))))
                 (equal (fn-frame-item 3 octets) 32)
                 (equal (fn-frame-item 3 octets) 13)))
        (+ (* 100 (- a 48)) (* 10 (- b 48)) (- c 48))
      nil)))

(defthm fn-own-feed-response-code-is-a-nat
  (implies (fn-own-feed-response-code octets)
           (and (natp (fn-own-feed-response-code octets))
                (<= 100 (fn-own-feed-response-code octets))
                (<= (fn-own-feed-response-code octets) 599)))
  :rule-classes nil)

(defun fn-own-feed-inflight-msgid (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (fn-feed-state-inflightp (fn-feed-entry-state (car xs)))
          (fn-feed-entry-msgid (car xs))
        (fn-own-feed-inflight-msgid (cdr xs)))
    nil))

(defun fn-own-feed-parse-response (octets msgid)
  (declare (xargs :guard t))
  (let ((code (fn-own-feed-response-code octets)))
    (if (or (null code) (not (fn-feed-namep msgid)))
        nil
      (fn-feed-response code msgid))))

(defthm fn-own-feed-parse-response-is-a-response
  (implies (fn-own-feed-parse-response octets msgid)
           (fn-feed-responsep (fn-own-feed-parse-response octets msgid)))
  :hints (("Goal" :use fn-own-feed-response-code-is-a-nat
           :in-theory (e/d (fn-feed-responsep fn-feed-response)
                           (fn-own-feed-response-code)))))

; -----------------------------------------------------------------------------
; Durable before the effect: the FNFD records a tick and a reply authorize
;
; 335 and 238 are go-aheads, not outcomes: the record they authorize is
; `(:feed-sent peer msgid attempt)', written before the TAKETHIS or the
; article block.  Every other code is an outcome record.  A code outside
; `*fn-feed-outcome-codes*' is journaled as 400, which is exactly what
; `fn-feed-observe' does with it (`fn-feed-lost') and what
; `fn-feed-apply-record' replays, so the journal's enumeration stays closed
; and replay stays faithful to the live machine.

(defun fn-own-feed-reply-records-of (peer msgid attempt code)
  (declare (xargs :guard t))
  (cond ((member-equal code '(335 238))
         (list (fn-own-feed-sent-record peer msgid attempt)))
        ((member-equal code *fn-feed-outcome-codes*)
         (list (fn-own-feed-outcome-record peer msgid attempt code)))
        (t (list (fn-own-feed-outcome-record peer msgid attempt 400)))))

(defun fn-own-feed-tick-peer-records (peer tbl obs)
  (declare (xargs :guard t))
  (let* ((e (fn-own-feed-entry-of peer tbl))
         (f (fn-own-feed-entry-feed e))
         (selected (and e (fn-feed-selection f obs))))
    (if (null selected)
        nil
      (list (fn-own-feed-offer-record peer selected (fn-feed-next-attempt f)
                                      (nfix (fn-clock-monotonic obs)))))))

(defun fn-own-feed-tick-records (names tbl obs)
  (declare (xargs :guard t))
  (if (consp names)
      (append (fn-own-feed-tick-peer-records (car names) tbl obs)
              (fn-own-feed-tick-records
               (cdr names) (car (fn-own-feed-tick-peer (car names) tbl obs))
               obs))
    nil))

; KEYSTONE.  A record is built exactly when a command goes out, and it names
; the Message-ID that command offers: this is what "durable before the effect"
; means at the one place the owner emits a feed command.
(defthm fn-own-feed-tick-peer-records-the-command-it-emits
  (implies (fn-own-feed-entry-of peer tbl)
           (and (iff (consp (fn-own-feed-tick-peer-records peer tbl obs))
                     (consp (cdr (fn-own-feed-tick-peer peer tbl obs))))
                (implies (consp (cdr (fn-own-feed-tick-peer peer tbl obs)))
                         (equal (fn-feed-record-msgid
                                 (fn-feed-journal-values
                                  (car (fn-own-feed-tick-peer-records peer tbl
                                                                      obs))))
                                (fn-feed-selection (fn-own-feed-find peer tbl)
                                                   obs)))))
  :hints (("Goal" :in-theory (enable fn-own-feed-tick-peer fn-feed-tick-step
                                     fn-own-feed-offer-record
                                     fn-feed-journal-entry
                                     fn-feed-journal-values
                                     fn-own-feed-find
                                     fn-feed-record-msgid fn-feed-offer))))

; -----------------------------------------------------------------------------
; Export theory.  What leaves enabled: the table lemmas above, the
; list-recursive vocabulary proofs induct on and the glue predicates written
; in accessor vocabulary.  Withdrawn: the table recognizer, the scope
; decision, the builders and the folds; books/owner-invariants.lisp opens
; them locally.

(deftheory fn-own-feed-vocabulary
  '(fn-own-feed-entry-okp fn-own-feed-record-okp fn-own-feed-feed-okp
    fn-own-feed-tablep fn-own-feed-contact-of
    fn-own-feed-limits-of fn-own-feed-outboundp fn-own-feed-open-one
    fn-own-feed-idlep fn-own-feed-install-one fn-own-feed-install
    fn-own-feed-retire-one fn-own-feed-retire
    fn-own-feed-reconfigure fn-own-feed-restart-all
    fn-own-feed-article-of fn-own-feed-groups-of fn-own-feed-path-of
    fn-own-feed-group-matchp fn-own-feed-offerablep
    fn-own-feed-accept fn-own-feed-tick-peer fn-own-feed-tick
    fn-own-feed-effect-peer fn-own-feed-effect-octets
    fn-own-feed-accept-records fn-own-feed-response-code
    fn-own-feed-parse-response fn-own-feed-reply-records-of
    fn-own-feed-tick-peer-records fn-own-feed-tick-records))

(in-theory (disable fn-own-feed-vocabulary))
