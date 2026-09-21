; Transcripts and teeth for the owner's outbound feed table
; (books/owner-feed.lisp; specs/peering.md sec. 3, milestone 3).  Every form
; is a computation on specific peer records, a specific article and a
; specific table.  Guard-world audit first, then the configuration, then the
; scope decision, then the transcripts, then the teeth: one concrete
; violating value per hypothesis of each keystone.

(in-package "ACL2")
(include-book "../../books/owner-feed")

; -----------------------------------------------------------------------------
; Guard-world audit: every function this book calls is guard verified in the
; logic, so the assertions below evaluate the :exec path.

(defun oft-o (s) (declare (xargs :guard (stringp s))) (fn-record-string-octets s))
(defun oft-line (s)
  (declare (xargs :guard (stringp s)))
  (append (fn-record-string-octets s) '(13 10)))

; -----------------------------------------------------------------------------
; Three peers: one streaming outbound peer whose wildmat matches, one
; outbound peer whose wildmat does not, and one inbound-only peer.

(defconst *oft-b*
  (fn-cfg-peer-make "nodeB" "b.fn.test" '(:nntp "127.0.0.1" 1120)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.2")))
(defconst *oft-c*
  (fn-cfg-peer-make "nodeC" "c.fn.test" '(:nntp "127.0.0.1" 1121)
                    '("fn.*" 32768 16) '("fn.other" nil 256 1000)
                    '(:source-address "127.0.0.3")))
(defconst *oft-d*
  (fn-cfg-peer-make "nodeD" "d.fn.test" '(:nntp "127.0.0.1" 1122)
                    '("fn.*" 32768 16) nil
                    '(:source-address "127.0.0.4")))
(assert-event (fn-cfg-peerp *oft-b*))
(assert-event (fn-cfg-peerp *oft-c*))
(assert-event (fn-cfg-peerp *oft-d*))
(assert-event (fn-own-feed-outboundp *oft-b*))
(assert-event (fn-own-feed-outboundp *oft-c*))
(assert-event (not (fn-own-feed-outboundp *oft-d*)))

(defconst *oft-change*
  (append *fn-cfg-default-change*
          (list (fn-cfg-set-policy "path-identity" "a.fn.test")
                (fn-cfg-set-peer-delta *oft-b*)
                (fn-cfg-set-peer-delta *oft-c*)
                (fn-cfg-set-peer-delta *oft-d*))))
(defconst *oft-cfg*
  (fn-config-replay 0 510
                    (list (fn-cfg-record-make 0 0 1 *oft-change*
                                              *fn-cfg-default-stamp*))))
(assert-event (fn-cfgp *oft-cfg*))
(defconst *oft-peers* (fn-cfg-peers (fn-cfg-value *oft-cfg*)))
(assert-event (equal (fn-cfg-peer-find "nodeB" *oft-peers*) *oft-b*))
(assert-event (equal (fn-cfg-peer-find "nodeC" *oft-peers*) *oft-c*))
(assert-event (equal (fn-cfg-peer-find "nodeD" *oft-peers*) *oft-d*))

; The peer enumeration: one name per peer, in row order, and it is the
; enumeration the CLI shows (host/store-node-host.lisp calls this function).
(assert-event (equal (fn-own-feed-peer-names *oft-peers*)
                     '("nodeB" "nodeC" "nodeD")))

; -----------------------------------------------------------------------------
; The table the owner builds at open

(defconst *oft-tbl* (fn-own-feed-reconfigure nil *oft-peers*))
(assert-event (fn-own-feed-tablep *oft-tbl*))
; The inbound-only peer gets no feed; the two outbound peers do.
(assert-event (equal (fn-own-feed-names *oft-tbl*) '("nodeB" "nodeC")))
(assert-event (not (fn-own-feed-boundp "nodeD" *oft-tbl*)))
; The three names of one peer are one name.
(assert-event (equal (fn-feed-peer (fn-own-feed-find "nodeB" *oft-tbl*))
                     (oft-o "nodeB")))
(assert-event (equal (fn-sched-contact-peer
                      (fn-feed-contact (fn-own-feed-find "nodeB" *oft-tbl*)))
                     "nodeB"))
(assert-event (equal (fn-cfg-peer-name (fn-own-feed-record-of "nodeB" *oft-tbl*))
                     "nodeB"))
; The limits come from the peer record's outbound half.
(assert-event (equal (fn-feed-max-queue
                      (fn-feed-limits-of (fn-own-feed-find "nodeB" *oft-tbl*)))
                     256))
(assert-event (equal (fn-feed-backoff-base
                      (fn-feed-limits-of (fn-own-feed-find "nodeB" *oft-tbl*)))
                     1000))
(assert-event (fn-feed-streamingp
               (fn-feed-limits-of (fn-own-feed-find "nodeB" *oft-tbl*))))
(assert-event (not (fn-feed-streamingp
                    (fn-feed-limits-of (fn-own-feed-find "nodeC" *oft-tbl*)))))
; Reconfiguring an unchanged configuration is idempotent.
(assert-event (equal (fn-own-feed-reconfigure *oft-tbl* *oft-peers*) *oft-tbl*))

; -----------------------------------------------------------------------------
; One article, and what its own octets say

(defconst *oft-article*
  (append (oft-line "Path: a.fn.test!not-for-mail")
          (oft-line "From: writer@a.fn.test")
          (oft-line "Newsgroups: fn.test")
          (oft-line "Subject: one")
          (oft-line "Message-ID: <1@a.fn.test>")
          (oft-line "Date: Sat, 20 Sep 2026 12:00:00 -0000")
          '(13 10)
          (oft-line "one body")))
(defconst *oft-msgid* (oft-o "<1@a.fn.test>"))
(assert-event (fn-feed-namep *oft-msgid*))
(assert-event (fn-own-feed-article-of *oft-article*))
(assert-event (equal (fn-own-feed-groups-of *oft-article*)
                     (list (oft-o "fn.test"))))
(assert-event (equal (fn-own-feed-path-of *oft-article*)
                     (oft-o "a.fn.test!not-for-mail")))

; The same article after it has passed through nodeB, so nodeB's own
; path-identity is in Path.
(defconst *oft-seen*
  (append (oft-line "Path: b.fn.test!a.fn.test!not-for-mail")
          (oft-line "From: writer@a.fn.test")
          (oft-line "Newsgroups: fn.test")
          (oft-line "Subject: one")
          (oft-line "Message-ID: <1@a.fn.test>")
          (oft-line "Date: Sat, 20 Sep 2026 12:00:00 -0000")
          '(13 10)
          (oft-line "one body")))
(assert-event (fn-path-names-p (fn-own-feed-path-of *oft-seen*) (oft-o "b.fn.test")))
(assert-event (not (fn-path-names-p (fn-own-feed-path-of *oft-article*)
                                    (oft-o "b.fn.test"))))

; -----------------------------------------------------------------------------
; The scope decision, and the targets it picks

(defconst *oft-groups* (fn-own-feed-groups-of *oft-article*))
(defconst *oft-path* (fn-own-feed-path-of *oft-article*))
(assert-event (fn-own-feed-group-matchp "fn.*" (oft-o "fn.test")))
(assert-event (not (fn-own-feed-group-matchp "fn.other" (oft-o "fn.test"))))
(assert-event (fn-own-feed-any-matchp "fn.*" *oft-groups*))
(assert-event (not (fn-own-feed-any-matchp "fn.other" *oft-groups*)))

(assert-event (fn-own-feed-offerablep *oft-b* nil *oft-groups* *oft-path*))
(assert-event (equal (fn-own-feed-targets *oft-tbl* nil *oft-groups* *oft-path*)
                     '("nodeB")))

; TEETH.  One concrete violating value per conjunct of fn-own-feed-offerablep,
; each an assertion on the negated conclusion.
; 1. no outbound half (the peer is inbound-only).
(assert-event (not (fn-own-feed-offerablep *oft-d* nil *oft-groups* *oft-path*)))
; 2. the outbound wildmat matches no group of the article.
(assert-event (not (fn-own-feed-offerablep *oft-c* nil *oft-groups* *oft-path*)))
; 3. the peer's own path-identity is already in Path (RFC 5537 sec. 3.6).
(assert-event (not (fn-own-feed-offerablep *oft-b* nil
                                           (fn-own-feed-groups-of *oft-seen*)
                                           (fn-own-feed-path-of *oft-seen*))))
; 4. the peer IS the peer the article came from.
(assert-event (not (fn-own-feed-offerablep *oft-b* "nodeB" *oft-groups* *oft-path*)))

; The same four, at the level of the targets the owner computes.
(assert-event (equal (fn-own-feed-targets *oft-tbl* "nodeB" *oft-groups* *oft-path*)
                     nil))
(assert-event (equal (fn-own-feed-targets *oft-tbl* nil
                                          (fn-own-feed-groups-of *oft-seen*)
                                          (fn-own-feed-path-of *oft-seen*))
                     nil))
(assert-event (equal (fn-own-feed-targets *oft-tbl* nil nil *oft-path*) nil))

; -----------------------------------------------------------------------------
; The enqueue on a durable acceptance

(defconst *oft-accepted*
  (fn-own-feed-accept *oft-tbl* nil *oft-msgid* *oft-article* 7))
(assert-event (fn-own-feed-tablep *oft-accepted*))
(assert-event (equal (len (fn-feed-queue (fn-own-feed-find "nodeB" *oft-accepted*)))
                     1))
(assert-event (equal (fn-feed-entry-msgid
                      (car (fn-feed-queue (fn-own-feed-find "nodeB" *oft-accepted*))))
                     *oft-msgid*))
; Every other peer's feed is the feed it was.
(assert-event (equal (fn-own-feed-find "nodeC" *oft-accepted*)
                     (fn-own-feed-find "nodeC" *oft-tbl*)))
; The article that came FROM nodeB is never enqueued back on nodeB.
(assert-event (equal (fn-own-feed-accept *oft-tbl* "nodeB" *oft-msgid*
                                         *oft-article* 7)
                     *oft-tbl*))
; Nor is an article whose Path already names nodeB.
(assert-event (equal (fn-own-feed-accept *oft-tbl* nil *oft-msgid* *oft-seen* 7)
                     *oft-tbl*))

; The FNFD records the enqueue authorizes: one per target, each a record the
; codec accepts and the journal can carry.
(defconst *oft-enq-records*
  (fn-own-feed-accept-records *oft-tbl* nil *oft-msgid* *oft-article* 7))
(assert-event (equal (len *oft-enq-records*) 1))
(assert-event (equal (fn-feed-journal-kind (car *oft-enq-records*)) :feed-enqueue))
(assert-event (equal (fn-feed-record-peer
                      (fn-feed-journal-values (car *oft-enq-records*)))
                     (oft-o "nodeB")))
(assert-event (equal (fn-feed-record-msgid
                      (fn-feed-journal-values (car *oft-enq-records*)))
                     *oft-msgid*))
(assert-event (fn-feed-record-okp (fn-feed-journal-kind (car *oft-enq-records*))
                                  (fn-feed-journal-values (car *oft-enq-records*))))
; Replaying that record into the same feed gives the same feed the live
; machine reached: the journal and the state agree at the one record.
(assert-event (equal (fn-feed-apply-record
                      (fn-own-feed-find "nodeB" *oft-tbl*)
                      (fn-feed-journal-kind (car *oft-enq-records*))
                      (fn-feed-journal-values (car *oft-enq-records*)))
                     (fn-own-feed-find "nodeB" *oft-accepted*)))

; -----------------------------------------------------------------------------
; The tick: nothing without a connection, an offer with one

(defconst *oft-obs* (fn-clock-observation 5000 0 0 nil))
(assert-event (fn-clock-observationp *oft-obs*))
; No connection: fn-feed-selection refuses, so no command and no record.
(assert-event (equal (cdr (fn-own-feed-tick-peer "nodeB" *oft-accepted* *oft-obs*))
                     nil))
(assert-event (equal (fn-own-feed-tick-peer-records "nodeB" *oft-accepted* *oft-obs*)
                     nil))

(defconst *oft-connected*
  (fn-own-feed-put "nodeB" (fn-own-feed-record-of "nodeB" *oft-accepted*)
                   (fn-feed-with-conn (fn-own-feed-find "nodeB" *oft-accepted*) 3)
                   *oft-accepted*))
(assert-event (fn-own-feed-tablep *oft-connected*))
(defconst *oft-ticked* (fn-own-feed-tick-peer "nodeB" *oft-connected* *oft-obs*))
(assert-event (fn-own-feed-tablep (car *oft-ticked*)))
; One command, on nodeB's connection, and it is a CHECK (the peer is
; streaming) naming this Message-ID.
(assert-event (equal (len (cdr *oft-ticked*)) 1))
(assert-event (equal (car (car (cdr *oft-ticked*))) "nodeB"))
(assert-event (fn-feed-command-offersp
               (caddr (car (cdr (car (cdr *oft-ticked*)))))
               *oft-msgid*))
; Durable before the effect: exactly one (:feed-offer ...) record, naming the
; Message-ID the command offers and the attempt the offer allocated.
(defconst *oft-tick-records*
  (fn-own-feed-tick-peer-records "nodeB" *oft-connected* *oft-obs*))
(assert-event (equal (len *oft-tick-records*) 1))
(assert-event (equal (fn-feed-journal-kind (car *oft-tick-records*)) :feed-offer))
(assert-event (equal (fn-feed-record-msgid
                      (fn-feed-journal-values (car *oft-tick-records*)))
                     *oft-msgid*))
(assert-event (fn-feed-record-okp (fn-feed-journal-kind (car *oft-tick-records*))
                                  (fn-feed-journal-values (car *oft-tick-records*))))
(assert-event (equal (fn-feed-apply-record
                      (fn-own-feed-find "nodeB" *oft-connected*)
                      (fn-feed-journal-kind (car *oft-tick-records*))
                      (fn-feed-journal-values (car *oft-tick-records*)))
                     (fn-own-feed-find "nodeB" (car *oft-ticked*))))
; The tick reaches nodeB alone.
(assert-event (equal (fn-own-feed-find "nodeC" (car *oft-ticked*))
                     (fn-own-feed-find "nodeC" *oft-connected*)))

; -----------------------------------------------------------------------------
; The reply reader (RFC 3977 sec. 3.2), in ACL2

(assert-event (equal (fn-own-feed-response-code (oft-o "238 <1@a.fn.test>")) 238))
(assert-event (equal (fn-own-feed-response-code (oft-o "239")) 239))
(assert-event (equal (fn-own-feed-response-code (oft-o "438 <1@a.fn.test>")) 438))
; Teeth: not three digits, not a code; a fourth digit is not a code either.
(assert-event (equal (fn-own-feed-response-code (oft-o "hello")) nil))
(assert-event (equal (fn-own-feed-response-code (oft-o "23")) nil))
(assert-event (equal (fn-own-feed-response-code (oft-o "2381")) nil))
(assert-event (equal (fn-own-feed-response-code nil) nil))

(defconst *oft-inflight*
  (fn-own-feed-inflight-msgid
   (fn-feed-queue (fn-own-feed-find "nodeB" (car *oft-ticked*)))))
(assert-event (equal *oft-inflight* *oft-msgid*))
(assert-event (fn-feed-responsep
               (fn-own-feed-parse-response (oft-o "238 <1@a.fn.test>")
                                           *oft-inflight*)))
(assert-event (null (fn-own-feed-parse-response (oft-o "nope") *oft-inflight*)))

; 238: the article follows.  The bytes are the store's, supplied by the owner.
(defconst *oft-sent*
  (mv-let (g effects)
    (fn-feed-observe (fn-own-feed-find "nodeB" (car *oft-ticked*))
                     (fn-own-feed-parse-response (oft-o "238 <1@a.fn.test>")
                                                 *oft-inflight*)
                     *oft-article* *oft-obs*)
    (cons g effects)))
(assert-event (fn-feed-sentp (fn-feed-state-of *oft-msgid*
                                               (fn-feed-queue (car *oft-sent*)))))
(assert-event (equal (len (cdr *oft-sent*)) 1))
; The record that authorized it is a (:feed-sent ...), not an outcome.
(assert-event (equal (fn-feed-journal-kind
                      (car (fn-own-feed-reply-records-of "nodeB" *oft-msgid* 1 238)))
                     :feed-sent))
; 239: accepted, and the entry is done.
(assert-event (equal (fn-feed-journal-kind
                      (car (fn-own-feed-reply-records-of "nodeB" *oft-msgid* 1 239)))
                     :feed-outcome))
; 438: the peer already has it -- also done, and journaled as itself.
(assert-event (equal (fn-feed-record-nat
                      3 (fn-feed-journal-values
                         (car (fn-own-feed-reply-records-of "nodeB" *oft-msgid* 1 438))))
                     438))
; A code the map does not know is journaled as 400, which is what
; fn-feed-observe does with it and what replay applies.
(assert-event (equal (fn-feed-record-nat
                      3 (fn-feed-journal-values
                         (car (fn-own-feed-reply-records-of "nodeB" *oft-msgid* 1 503))))
                     400))

; -----------------------------------------------------------------------------
; Restart by offer (K5): a process death fences the in-flight entry

(defconst *oft-restarted* (fn-own-feed-restart-all (car *oft-sent*)))
(assert-event (equal (fn-feed-state-of *oft-msgid* (fn-feed-queue
                                                    (car (fn-own-feed-restart-all
                                                          (list (fn-own-feed-entry
                                                                 "nodeB"
                                                                 (fn-own-feed-record-of "nodeB" *oft-tbl*)
                                                                 (car *oft-sent*)))))))
                     nil))
(defconst *oft-fenced*
  (fn-own-feed-restart-all
   (fn-own-feed-put "nodeB" (fn-own-feed-record-of "nodeB" *oft-tbl*)
                    (car *oft-sent*) *oft-tbl*)))
(assert-event (fn-own-feed-tablep *oft-fenced*))
; The entry is queued again, its attempt retired, and the connection gone: the
; next command for it is therefore an offer and never a blind TAKETHIS.
(assert-event (equal (fn-feed-state-of *oft-msgid*
                                       (fn-feed-queue (fn-own-feed-find "nodeB" *oft-fenced*)))
                     :queued))
(assert-event (null (fn-feed-conn (fn-own-feed-find "nodeB" *oft-fenced*))))
(assert-event (equal (fn-own-feed-tick-peer-records "nodeB" *oft-fenced* *oft-obs*)
                     nil))

; -----------------------------------------------------------------------------
; Retiring a peer: only when its feed has drained

(defconst *oft-peers-without-b*
  (fn-cfg-peers
   (fn-cfg-value
    (fn-config-replay
     0 510
     (list (fn-cfg-record-make 0 0 1 *oft-change* *fn-cfg-default-stamp*)
           (fn-cfg-record-make 1 1 2 (list (fn-cfg-remove-peer-delta "nodeB"))
                               *fn-cfg-default-stamp*))))))
(assert-event (null (fn-cfg-peer-find "nodeB" *oft-peers-without-b*)))
; An idle feed goes.
(assert-event (equal (fn-own-feed-names
                      (fn-own-feed-reconfigure *oft-tbl* *oft-peers-without-b*))
                     '("nodeC")))
; A feed with a queued entry stays until it drains.
(assert-event (equal (fn-own-feed-names
                      (fn-own-feed-reconfigure *oft-accepted* *oft-peers-without-b*))
                     '("nodeB" "nodeC")))
(assert-event (equal (fn-own-feed-find
                      "nodeB" (fn-own-feed-reconfigure *oft-accepted*
                                                       *oft-peers-without-b*))
                     (fn-own-feed-find "nodeB" *oft-accepted*)))

; -----------------------------------------------------------------------------
; TEETH for fn-own-feed-tablep: one concrete violating value per conjunct

; A duplicate key.
(assert-event (not (fn-own-feed-tablep (append *oft-tbl* (list (car *oft-tbl*))))))
; A key that is not the peer name the record carries.
(assert-event (not (fn-own-feed-tablep
                    (list (fn-own-feed-entry "other" *oft-b*
                                             (fn-own-feed-find "nodeB" *oft-tbl*))))))
; A record with no outbound half.
(assert-event (not (fn-own-feed-tablep
                    (list (fn-own-feed-entry "nodeD" *oft-d*
                                             (fn-own-feed-find "nodeB" *oft-tbl*))))))
; A feed whose fn-feed-peer octets are another peer's.
(assert-event (not (fn-own-feed-tablep
                    (list (fn-own-feed-entry "nodeB" *oft-b*
                                             (fn-own-feed-find "nodeC" *oft-tbl*))))))
; A value that is not a feed at all.
(assert-event (not (fn-own-feed-tablep
                    (list (fn-own-feed-entry "nodeB" *oft-b* :not-a-feed)))))
; A table that is not a true list.
(assert-event (not (fn-own-feed-tablep (cons (car *oft-tbl*) :tail))))

; -----------------------------------------------------------------------------
; A LOST CONNECTION, per peer (K5's first blocker)
;
; `fn-own-feed-lost-one' is what the host calls when a peer's socket is
; gone. `*oft-sent*' is the feed with the article in flight: the CHECK went
; out, the peer answered 238 and the article was written. Everything below
; is over THAT state, because an entry that is not in flight is the case the
; transition must leave alone.

(defconst *oft-in-flight*
  (fn-own-feed-put "nodeB" (fn-own-feed-record-of "nodeB" *oft-connected*)
                   (car *oft-sent*) *oft-connected*))
(assert-event (fn-own-feed-tablep *oft-in-flight*))
(assert-event (fn-feed-sentp
               (fn-feed-state-of *oft-msgid*
                                 (fn-feed-queue (fn-own-feed-find "nodeB"
                                                                  *oft-in-flight*)))))
(assert-event (equal (fn-feed-conn (fn-own-feed-find "nodeB" *oft-in-flight*)) 3))

(defconst *oft-lost* (fn-own-feed-lost-one "nodeB" *oft-in-flight* *oft-obs*))
(assert-event (fn-own-feed-tablep *oft-lost*))
; The entry is QUEUED again, its attempt counted, and the connection gone --
; so the next command for it is an offer and never a blind TAKETHIS.
(assert-event (equal (fn-feed-state-of *oft-msgid*
                                       (fn-feed-queue (fn-own-feed-find "nodeB" *oft-lost*)))
                     :queued))
(assert-event (equal (fn-feed-entry-attempts
                      (fn-feed-find *oft-msgid*
                                    (fn-feed-queue (fn-own-feed-find "nodeB" *oft-lost*))))
                     1))
(assert-event (null (fn-feed-conn (fn-own-feed-find "nodeB" *oft-lost*))))
; Nothing left the queue.
(assert-event (equal (len (fn-feed-queue (fn-own-feed-find "nodeB" *oft-lost*)))
                     (len (fn-feed-queue (fn-own-feed-find "nodeB" *oft-in-flight*)))))
; PER PEER: nodeC's feed is the one it was. This is the conjunct that keeps
; the transition from being fn-own-feed-restart-all, whose settle of another
; peer's genuinely in-flight entry is the second transfer K5 forbids.
(assert-event (equal (fn-own-feed-find "nodeC" *oft-lost*)
                     (fn-own-feed-find "nodeC" *oft-in-flight*)))

; The record it authorizes: one (:feed-outcome peer msgid attempt 400), the
; same record a 400 on the wire writes.
(defconst *oft-lost-records* (fn-own-feed-lost-records-of "nodeB" *oft-in-flight*))
(assert-event (equal (len *oft-lost-records*) 1))
(assert-event (equal (fn-feed-journal-kind (car *oft-lost-records*)) :feed-outcome))
(assert-event (equal (fn-feed-record-msgid (fn-feed-journal-values (car *oft-lost-records*)))
                     *oft-msgid*))
(assert-event (equal (fn-feed-record-nat 3 (fn-feed-journal-values (car *oft-lost-records*)))
                     400))
(assert-event (fn-feed-record-okp (fn-feed-journal-kind (car *oft-lost-records*))
                                  (fn-feed-journal-values (car *oft-lost-records*))))
(assert-event (equal *oft-lost-records*
                     (fn-own-feed-reply-records-of "nodeB" *oft-msgid* 1 400)))

; Replay reaches the same entry. `fn-feed-apply-record' requeues with tick 0
; where the live transition records the observation's own tick, and the tick
; is provenance that no decision reads (`fn-feed-entry-tick' is read by
; nothing but the two requeue builders), so the Message-ID, the state and the
; attempt count are what is compared.
(defconst *oft-lost-replayed*
  (fn-feed-apply-record (fn-own-feed-find "nodeB" *oft-in-flight*)
                        (fn-feed-journal-kind (car *oft-lost-records*))
                        (fn-feed-journal-values (car *oft-lost-records*))))
(assert-event (equal (fn-feed-state-of *oft-msgid* (fn-feed-queue *oft-lost-replayed*))
                     :queued))
(assert-event (equal (fn-feed-entry-attempts
                      (fn-feed-find *oft-msgid* (fn-feed-queue *oft-lost-replayed*)))
                     1))

; TEETH.  One concrete violating value per hypothesis of the transition.
; No entry in flight: no record at all, and nothing to requeue.
(assert-event (null (fn-own-feed-lost-records-of "nodeB" *oft-accepted*)))
(assert-event (equal (fn-feed-state-of *oft-msgid*
                                       (fn-feed-queue
                                        (fn-own-feed-find
                                         "nodeB" (fn-own-feed-lost-one
                                                  "nodeB" *oft-accepted* *oft-obs*))))
                     :queued))
; A peer with no entry in the table: the table is the table.
(assert-event (equal (fn-own-feed-lost-one "nodeD" *oft-in-flight* *oft-obs*)
                     *oft-in-flight*))
(assert-event (null (fn-own-feed-lost-records-of "nodeD" *oft-in-flight*)))
; A :done entry is NOT requeued by a loss -- the peer answered and the
; outcome is settled; requeueing it would be the second transfer K5 forbids.
(defconst *oft-done*
  (fn-own-feed-put "nodeB" (fn-own-feed-record-of "nodeB" *oft-in-flight*)
                   (mv-let (g effects)
                     (fn-feed-observe (fn-own-feed-find "nodeB" *oft-in-flight*)
                                      (fn-own-feed-parse-response
                                       (oft-o "239 <1@a.fn.test>") *oft-msgid*)
                                      *oft-article* *oft-obs*)
                     (declare (ignore effects))
                     g)
                   *oft-in-flight*))
(assert-event (equal (fn-feed-state-of *oft-msgid*
                                       (fn-feed-queue (fn-own-feed-find "nodeB" *oft-done*)))
                     :done))
(assert-event (null (fn-own-feed-lost-records-of "nodeB" *oft-done*)))
(assert-event (equal (fn-feed-state-of *oft-msgid*
                                       (fn-feed-queue
                                        (fn-own-feed-find
                                         "nodeB" (fn-own-feed-lost-one
                                                  "nodeB" *oft-done* *oft-obs*))))
                     :done))
