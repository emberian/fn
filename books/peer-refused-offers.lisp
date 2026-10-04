; fn: the refused-offer memory is sound (PRF-235).
;
; books/refused-offers.lisp is the memory (bounded, oldest-first eviction);
; books/peer-inbound.lisp admits to it only `fn-peer-intrinsic-refusal' of
; the transferred octets (`fn-peer-refused-record') and answers an offer from
; it (`fn-peer-decide-offer', the arm after the history test).  This book
; states what that buys:
;
;   * the transfer decision refuses exactly what the octets refuse, whatever
;     the node, the peer's other settings or the clock, once the peer is an
;     inbound peer, the Message-ID is well formed and the octets fit the
;     peer's size (`fn-peer-decide-transfer-refuses-what-the-octets-refuse');
;   * every entry of a memory built by `fn-peer-refused-record' names a
;     transfer that drew that refusal (`fn-prof-run-is-sound');
;   * so the answer the memory gives at offer time is the answer the parse
;     of the remembered transfer gives (`fn-prof-offer-answer-is-the-reparse').
;
;   * the memory is per offering peer: a record for one peer changes no
;     lookup of another's key (`fn-peer-refused-record-keeps-every-other-key')
;     and so no other peer's offer decision
;     (`fn-peer-refused-record-never-changes-another-peers-offer').
;
; Nothing here assumes two peers send the same octets under one Message-ID.
; Until rp-refused-memory-poison (2026-10-04) the key was the Message-ID
; alone, INN's reject-history behaviour: one peer's mismatched or garbage
; transfer of <v> made every other peer's offer of <v> draw a final 438.
; The key is now (peer . Message-ID), and the soundness statement names the
; peer whose octets the remembered reason is about.
;
; This book owns the prefix `fn-prof-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "peer-inbound")
(include-book "article-line-bound")

; -----------------------------------------------------------------------------
; The octets' refusal is one of the remembered reasons

(defthm fn-peer-intrinsic-refusal-of-is-an-intrinsic-reason
  (implies (fn-peer-intrinsic-refusal-of msgid okp article check limitp)
           (member-equal (fn-peer-intrinsic-refusal-of msgid okp article check limitp)
                         *fn-peer-intrinsic-reasons*))
  :hints (("Goal" :in-theory (e/d (fn-peer-intrinsic-refusal-of)
                                  (fn-af-message-id-equalp fn-path-date-presentp
                                   fn-af-path-field-value
                                   fn-rck-path-wellformedp
                                   fn-rck-article-instant)))))

(defthm fn-peer-intrinsic-refusal-is-an-intrinsic-reason
  (implies (fn-peer-intrinsic-refusal msgid octets)
           (member-equal (fn-peer-intrinsic-refusal msgid octets)
                         *fn-peer-intrinsic-reasons*))
  :hints (("Goal" :in-theory (e/d (fn-peer-intrinsic-refusal)
                                  (fn-peer-intrinsic-refusal-of
                                   fn-peer-intrinsic-refusal-of-is-an-intrinsic-reason
                                   fn-peer-article-of fn-article-syntax-p
                                   fn-af-relayed-article-check))
           :use ((:instance fn-peer-intrinsic-refusal-of-is-an-intrinsic-reason
                            (article (fn-peer-article-of octets))
                            (okp (and (fn-peer-article-of octets)
                                      (fn-article-syntax-p
                                       (fn-peer-article-of octets))))
                            (check (if (and (fn-peer-article-of octets)
                                            (fn-article-syntax-p
                                             (fn-peer-article-of octets)))
                                       (fn-af-relayed-article-check
                                        (fn-peer-article-of octets))
                                     nil))
                            (limitp (and (not (fn-peer-article-of octets))
                                         (fn-peer-parse-limitp
                                          (fn-article-parse octets) octets))))))))

; -----------------------------------------------------------------------------
; KEYSTONE: the transfer refuses what the octets refuse

(defthm fn-peer-decide-transfer-refuses-what-the-octets-refuse
  (let ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))))
    (implies (and record
                  (fn-cfg-peer-inbound record)
                  (fn-af-message-idp msgid)
                  (<= (len octets) (fn-cfg-peer-inbound-max-octets record))
                  (fn-peer-intrinsic-refusal msgid octets))
             (equal (fn-peer-decide-transfer node cfg peer msgid octets clock
                                             id subject)
                    (fn-peer-decision :refuse
                                      (fn-peer-intrinsic-refusal msgid octets)))))
  :hints (("Goal" :in-theory (e/d (fn-peer-decide-transfer
                                   fn-peer-intrinsic-refusal
                                   fn-peer-article-of)
                                  (fn-peer-intrinsic-refusal-of
                                   fn-article-parse fn-article-syntax-p
                                   fn-af-relayed-article-check
                                   fn-cfg-peer-find fn-af-message-idp
                                   fn-peer-history-hasp fn-peer-stagedp
                                   fn-retain-admissiblep fn-peer-relayed-octets
                                   fn-peer-scope-groups fn-peer-date-futurep
                                   fn-path-names-p fn-af-path-field-value)))))

; -----------------------------------------------------------------------------
; The memory, over the transfers it was built from

; -----------------------------------------------------------------------------
; The memory is per peer (rp-refused-memory-poison)

; No entry of XS is keyed K.
(defun fn-prof-keylessp (k xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (not (and (consp (car xs)) (equal (car (car xs)) k)))
           (fn-prof-keylessp k (cdr xs)))
    t))

(local (defthm fn-prof-lookup-of-append-keyless
  (implies (fn-prof-keylessp k a)
           (equal (fn-rof-lookup k (append a b)) (fn-rof-lookup k b)))
  :hints (("Goal" :in-theory (enable fn-rof-lookup)))))

(local (defthm fn-prof-keyless-of-first
  (implies (fn-prof-keylessp k xs)
           (fn-prof-keylessp k (fn-rof-first n xs)))
  :hints (("Goal" :in-theory (enable fn-rof-first)))))

(local (defthm fn-prof-keyless-of-record
  (implies (and (fn-prof-keylessp k xs) (not (equal k key)))
           (fn-prof-keylessp k (fn-rof-record xs cap key reason)))
  :hints (("Goal" :in-theory (enable fn-rof-record)))))

(local (defthm fn-prof-keyless-of-own-entries
  (implies (not (and (consp k) (equal (car k) peer)))
           (fn-prof-keylessp k (fn-peer-refused-of mem peer)))
  :hints (("Goal" :in-theory (enable fn-peer-refused-of fn-peer-refused-ownp)))))

(local (defthm fn-prof-lookup-of-others
  (implies (not (and (consp k) (equal (car k) peer)))
           (equal (fn-rof-lookup k (fn-peer-refused-others mem peer))
                  (fn-rof-lookup k mem)))
  :hints (("Goal" :in-theory (enable fn-peer-refused-others fn-peer-refused-ownp
                                     fn-rof-lookup)))))

; KEYSTONE (rp-refused-memory-poison).  A record made for PEER's transfer
; changes no lookup of a key that is not PEER's: another peer's entries, and
; a shed read's posture entry, answer exactly as before.
(defthm fn-peer-refused-record-keeps-every-other-key
  (implies (not (and (consp k) (equal (car k) peer)))
           (equal (fn-rof-lookup k (fn-peer-refused-record mem cfg peer msgid octets))
                  (fn-rof-lookup k mem)))
  :hints (("Goal" :in-theory (e/d (fn-peer-refused-record fn-peer-refused-key)
                                  (fn-peer-intrinsic-refusal fn-rof-record
                                   fn-af-message-idp fn-record-octets-string)))))

(local (defthm fn-prof-remembered-reason-of-another-peer
  (implies (not (equal (fn-peer-session-peer session) peer))
           (equal (fn-peer-remembered-reason
                   m (fn-peer-with-refused
                      session (fn-peer-refused-record mem cfg2 peer msgid octets)))
                  (fn-peer-remembered-reason m (fn-peer-with-refused session mem))))
  :hints (("Goal" :in-theory (e/d (fn-peer-remembered-reason fn-peer-with-refused
                                   fn-peer-make-session fn-peer-session-refused
                                   fn-peer-session-peer fn-peer-refused-key
                                   fn-ag-car fn-ag-cdr)
                                  (fn-peer-refused-record fn-record-octets-string))))))

(local (defthm fn-prof-shed-of-another-peer
  (equal (fn-peer-shed-p
          (fn-peer-with-refused
           session (fn-peer-refused-record mem cfg2 peer msgid octets)))
         (fn-peer-shed-p (fn-peer-with-refused session mem)))
  :hints (("Goal" :in-theory (e/d (fn-peer-shed-p fn-peer-with-refused
                                   fn-peer-make-session fn-peer-session-refused
                                   fn-ag-car fn-ag-cdr)
                                  (fn-peer-refused-record))))))

; KEYSTONE (the ruling: one peer's offer never changes the answer another
; peer gets).  Whatever PEER transferred and however it was refused, the
; offer decision on a session of any other peer is unchanged by the record --
; for every Message-ID, held or not.
(defthm fn-peer-refused-record-never-changes-another-peers-offer
  (implies (not (equal (fn-peer-session-peer session) peer))
           (equal (fn-peer-decide-offer
                   node cfg q
                   (fn-peer-with-refused session
                                         (fn-peer-refused-record mem cfg2 peer msgid octets))
                   m clock inflight)
                  (fn-peer-decide-offer node cfg q (fn-peer-with-refused session mem)
                                        m clock inflight)))
  :hints (("Goal" :in-theory (e/d (fn-peer-decide-offer)
                                  (fn-peer-remembered-reason fn-peer-shed-p
                                   fn-peer-with-refused
                                   fn-peer-refused-record fn-cfg-peer-find
                                   fn-af-message-idp fn-peer-history-hasp
                                   fn-peer-stagedp fn-retain-admissiblep
                                   fn-record-octets-string)))))

; A transfer is (peer msgid . octets), as the owner holds it in flight.
(defun fn-prof-run (mem cfg transfers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp transfers)
      (fn-prof-run (fn-peer-refused-record mem cfg (car (car transfers))
                                           (car (cdr (car transfers)))
                                           (cdr (cdr (car transfers))))
                   cfg (cdr transfers))
    mem))

; The first transfer that drew reason R under the memory key K.
(defun fn-prof-witness (k r transfers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp transfers)
      (if (and (consp (car transfers))
               (consp (cdr (car transfers)))
               (fn-af-message-idp (car (cdr (car transfers))))
               (equal (fn-peer-refused-key (car (car transfers))
                                           (car (cdr (car transfers))))
                      k)
               (equal (fn-peer-intrinsic-refusal (car (cdr (car transfers)))
                                                 (cdr (cdr (car transfers))))
                      r))
          (car transfers)
        (fn-prof-witness k r (cdr transfers)))
    nil))

; Every entry of MEM has a witness in TRANSFERS.
(defun fn-prof-soundp (mem transfers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp mem)
      (and (consp (car mem))
           (fn-prof-witness (car (car mem)) (cdr (car mem)) transfers)
           (fn-prof-soundp (cdr mem) transfers))
    t))

(defthm fn-prof-witness-of-append
  (implies (fn-prof-witness k r a)
           (equal (fn-prof-witness k r (append a b))
                  (fn-prof-witness k r a))))

(defthm fn-prof-soundp-of-append-right
  (implies (fn-prof-soundp mem ts)
           (fn-prof-soundp mem (append ts b))))

(defthm fn-prof-witness-of-appended-transfer
  (implies (and (consp e) (consp (cdr e))
                (fn-af-message-idp (car (cdr e)))
                (equal (fn-peer-refused-key (car e) (car (cdr e))) k)
                (equal (fn-peer-intrinsic-refusal (car (cdr e)) (cdr (cdr e))) r))
           (fn-prof-witness k r (append ts (list e))))
  :hints (("Goal" :in-theory (disable fn-peer-intrinsic-refusal fn-peer-refused-key
                                      fn-af-message-idp fn-record-octets-string))))

(defthm fn-prof-soundp-of-first
  (implies (fn-prof-soundp mem ts)
           (fn-prof-soundp (fn-rof-first n mem) ts))
  :hints (("Goal" :in-theory (enable fn-rof-first))))

(local (defthm fn-prof-soundp-of-append
  (equal (fn-prof-soundp (append a b) ts)
         (and (fn-prof-soundp a ts) (fn-prof-soundp b ts)))))

(local (defthm fn-prof-soundp-of-own-entries
  (implies (fn-prof-soundp mem ts)
           (fn-prof-soundp (fn-peer-refused-of mem peer) ts))
  :hints (("Goal" :in-theory (e/d (fn-peer-refused-of) (fn-prof-witness))))))

(local (defthm fn-prof-soundp-of-others
  (implies (fn-prof-soundp mem ts)
           (fn-prof-soundp (fn-peer-refused-others mem peer) ts))
  :hints (("Goal" :in-theory (e/d (fn-peer-refused-others) (fn-prof-witness))))))

(local (defthm fn-prof-soundp-of-record-entry
  (implies (and (fn-prof-soundp mem ts) (fn-prof-witness k r ts))
           (fn-prof-soundp (fn-rof-record mem cap k r) ts))
  :hints (("Goal" :in-theory (e/d (fn-rof-record) (fn-prof-witness fn-rof-first))
           :use ((:instance fn-prof-soundp-of-first (n cap)
                            (mem (cons (cons k r) mem))))))))

(defthm fn-prof-lookup-of-sound-has-a-witness
  (implies (and (fn-prof-soundp mem ts) (fn-rof-lookup k mem))
           (fn-prof-witness k (fn-rof-lookup k mem) ts)))

; One record keeps the memory sound over the transfers so far and this one.
(defthm fn-prof-record-keeps-soundness
  (implies (fn-prof-soundp mem ts)
           (fn-prof-soundp (fn-peer-refused-record mem cfg (car e) (car (cdr e)) (cdr (cdr e)))
                           (append ts (list e))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-peer-refused-record)
                           (fn-peer-intrinsic-refusal fn-rof-record fn-prof-soundp
                            fn-prof-witness fn-peer-refused-key
                            fn-af-message-idp fn-record-octets-string))
           :use ((:instance fn-prof-soundp-of-append-right (b (list e)))
                 (:instance fn-prof-witness-of-appended-transfer
                            (k (fn-peer-refused-key (car e) (car (cdr e))))
                            (r (fn-peer-intrinsic-refusal (car (cdr e)) (cdr (cdr e)))))))))

(defun fn-prof-run-ind (mem cfg transfers done)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp transfers)
      (fn-prof-run-ind (fn-peer-refused-record mem cfg (car (car transfers))
                                               (car (cdr (car transfers)))
                                               (cdr (cdr (car transfers))))
                       cfg (cdr transfers)
                       (append done (list (car transfers))))
    (list mem done)))

(local (defthm fn-prof-append-assoc
  (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-prof-run-sound-from
  (implies (fn-prof-soundp mem done)
           (fn-prof-soundp (fn-prof-run mem cfg transfers)
                           (append done transfers)))
  :hints (("Goal" :induct (fn-prof-run-ind mem cfg transfers done)
           :in-theory (disable fn-peer-refused-record fn-prof-soundp))
          ("Subgoal *1/1" :use ((:instance fn-prof-record-keeps-soundness
                                           (ts done)
                                           (e (car transfers)))))))

(defthm fn-prof-witness-facts
  (implies (fn-prof-witness k r ts)
           (and (member-equal (fn-prof-witness k r ts) ts)
                (fn-af-message-idp (car (cdr (fn-prof-witness k r ts))))
                (equal (fn-peer-refused-key (car (fn-prof-witness k r ts))
                                            (car (cdr (fn-prof-witness k r ts))))
                       k)
                (equal (fn-peer-intrinsic-refusal (car (cdr (fn-prof-witness k r ts)))
                                                  (cdr (cdr (fn-prof-witness k r ts))))
                       r)))
  :hints (("Goal" :induct (fn-prof-witness k r ts)
           :in-theory (disable fn-peer-intrinsic-refusal fn-af-message-idp
                               fn-peer-refused-key fn-record-octets-string))))

; KEYSTONE: a memory built from nothing by the owner's record step names, for
; every key (PEER . Message-ID) it holds, a transfer BY THAT PEER of that
; Message-ID whose octets drew exactly the remembered refusal.
(defthm fn-prof-run-is-sound
  (implies (fn-rof-lookup k (fn-prof-run nil cfg transfers))
           (let ((w (fn-prof-witness k (fn-rof-lookup k (fn-prof-run nil cfg transfers))
                                     transfers)))
             (and (member-equal w transfers)
                  (fn-af-message-idp (car (cdr w)))
                  (equal (fn-peer-refused-key (car w) (car (cdr w))) k)
                  (equal (fn-peer-intrinsic-refusal (car (cdr w)) (cdr (cdr w)))
                         (fn-rof-lookup k (fn-prof-run nil cfg transfers))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-prof-run-sound-from (mem nil) (done nil))
                 (:instance fn-prof-witness-facts
                            (r (fn-rof-lookup k (fn-prof-run nil cfg transfers)))
                            (ts transfers))
                 (:instance fn-prof-lookup-of-sound-has-a-witness
                            (mem (fn-prof-run nil cfg transfers))
                            (ts transfers)))
           :in-theory (disable fn-prof-run-sound-from fn-prof-witness-facts
                               fn-prof-lookup-of-sound-has-a-witness
                               fn-prof-run fn-peer-intrinsic-refusal
                               fn-prof-witness fn-prof-soundp fn-rof-lookup
                               fn-peer-refused-key
                               fn-af-message-idp fn-record-octets-string))))

; -----------------------------------------------------------------------------
; The offer answers the memory

; The owner's memory, built from transfers, is keyed (peer . Message-ID):
; it never holds the disk-slow posture's entry (books/peer-inbound.lisp
; fn-peer-shed-p), which a shed read adds for itself and takes out after it
; (books/owner-time-admission.lisp fn-otm-read-span, PKT-858).
(defthm fn-prof-first-keeps-no-posture
  (implies (not (fn-rof-lookup :disk-slow xs))
           (not (fn-rof-lookup :disk-slow (fn-rof-first n xs))))
  :hints (("Goal" :in-theory (enable fn-rof-first fn-rof-lookup))))

(defthm fn-prof-run-keeps-no-posture
  (implies (not (fn-rof-lookup :disk-slow mem))
           (not (fn-rof-lookup :disk-slow (fn-prof-run mem cfg transfers))))
  :hints (("Goal" :in-theory (e/d (fn-prof-run) (fn-peer-refused-record)))))

(defthm fn-peer-decide-offer-answers-the-memory
  (let ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))))
    (implies (and record
                  (fn-cfg-peer-inbound record)
                  (fn-af-message-idp msgid)
                  (not (fn-peer-shed-p session))
                  (not (fn-peer-history-hasp (fn-record-octets-string msgid) node))
                  (fn-peer-remembered-reason msgid session))
             (equal (fn-peer-decide-offer node cfg peer session msgid clock
                                          inflight)
                    (fn-peer-decision :refuse
                                      (fn-peer-remembered-reason msgid session)))))
  :hints (("Goal" :in-theory (e/d (fn-peer-decide-offer)
                                  (fn-peer-shed-p fn-peer-remembered-reason fn-cfg-peer-find
                                   fn-af-message-idp fn-peer-history-hasp
                                   fn-record-octets-string)))))

; KEYSTONE (the brief's statement, now per peer).  An offer on PEER's
; session whose memory the owner built from TRANSFERS, of a Message-ID the
; memory holds for PEER and the node has not accepted, is refused for the
; reason the parse of a remembered transfer gives -- a transfer BY PEER of
; that Message-ID; and that transfer's own decision, on this node, is the
; same refusal whenever its octets fit the peer's size.
(defthm fn-prof-offer-answer-is-the-reparse
  (let* ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
         (mem (fn-prof-run nil cfg0 transfers))
         (k (fn-peer-refused-key peer msgid))
         (r (fn-rof-lookup k mem))
         (w (fn-prof-witness k r transfers)))
    (implies (and record
                  (fn-cfg-peer-inbound record)
                  (fn-af-message-idp msgid)
                  (not (fn-peer-history-hasp (fn-record-octets-string msgid) node))
                  (equal (fn-peer-session-peer session) peer)
                  (equal (fn-peer-session-refused session) mem)
                  r)
             (and (equal (fn-peer-decide-offer node cfg peer session msgid clock
                                               inflight)
                         (fn-peer-decision :refuse r))
                  (member-equal w transfers)
                  (equal (car w) peer)
                  (equal (fn-record-octets-string (car (cdr w)))
                         (fn-record-octets-string msgid))
                  (equal (fn-peer-intrinsic-refusal (car (cdr w)) (cdr (cdr w))) r)
                  (implies (<= (len (cdr (cdr w)))
                               (fn-cfg-peer-inbound-max-octets record))
                           (equal (fn-peer-decide-transfer node cfg peer (car (cdr w))
                                                           (cdr (cdr w)) clock2 id
                                                           subject)
                                  (fn-peer-decision :refuse r))))))
  :hints (("Goal" :use ((:instance fn-prof-run-is-sound
                                   (k (fn-peer-refused-key peer msgid))
                                   (cfg cfg0))
                        (:instance fn-prof-witness-facts
                                   (k (fn-peer-refused-key peer msgid))
                                   (r (fn-rof-lookup (fn-peer-refused-key peer msgid)
                                                     (fn-prof-run nil cfg0 transfers)))
                                   (ts transfers))
                        (:instance fn-peer-intrinsic-refusal-is-an-intrinsic-reason
                                   (msgid (car (cdr (fn-prof-witness
                                                     (fn-peer-refused-key peer msgid)
                                                     (fn-rof-lookup (fn-peer-refused-key peer msgid)
                                                                    (fn-prof-run nil cfg0 transfers))
                                                     transfers))))
                                   (octets (cdr (cdr (fn-prof-witness
                                                      (fn-peer-refused-key peer msgid)
                                                      (fn-rof-lookup (fn-peer-refused-key peer msgid)
                                                                     (fn-prof-run nil cfg0 transfers))
                                                      transfers)))))
                        (:instance fn-peer-decide-offer-answers-the-memory)
                        (:instance fn-prof-run-keeps-no-posture (mem nil) (cfg cfg0))
                        (:instance fn-peer-decide-transfer-refuses-what-the-octets-refuse
                                   (clock clock2)
                                   (msgid (car (cdr (fn-prof-witness
                                                     (fn-peer-refused-key peer msgid)
                                                     (fn-rof-lookup (fn-peer-refused-key peer msgid)
                                                                    (fn-prof-run nil cfg0 transfers))
                                                     transfers))))
                                   (octets (cdr (cdr (fn-prof-witness
                                                      (fn-peer-refused-key peer msgid)
                                                      (fn-rof-lookup (fn-peer-refused-key peer msgid)
                                                                     (fn-prof-run nil cfg0 transfers))
                                                      transfers))))))
           :in-theory (e/d (fn-peer-remembered-reason fn-peer-shed-p fn-peer-refused-key
                            fn-peer-session-peer)
                           (fn-prof-run-keeps-no-posture fn-prof-run-is-sound fn-prof-witness-facts
                            fn-peer-decide-offer-answers-the-memory
                            fn-peer-decide-transfer-refuses-what-the-octets-refuse
                            fn-peer-intrinsic-refusal-is-an-intrinsic-reason
                            fn-prof-run fn-prof-witness fn-peer-decide-offer
                            fn-peer-decide-transfer fn-peer-intrinsic-refusal
                            fn-cfg-peer-find fn-af-message-idp
                            fn-peer-history-hasp fn-record-octets-string)))))

; -----------------------------------------------------------------------------
; KEYSTONE (I5): a transfer refused :line-length met a header line over RFC
; 5322 section 2.1.1's 998 octets.  Subject: fn-peer-decide-transfer, which
; every IHAVE and TAKETHIS transfer runs (books/peer-inbound.lisp
; fn-peer-command, reached from host/owner-host.lisp's peer arm).  The peer
; path names the bound as POST does (books/injection.lisp
; fn-inj-decide-line-length-is-a-long-header-line), from the same parse
; theorem (books/article-line-bound.lisp).  No hypothesis.
(defthm fn-peer-decide-transfer-line-length-is-a-long-header-line
  (implies (equal (fn-peer-decision-reason
                   (fn-peer-decide-transfer node cfg peer msgid octets clock id subject))
                  :line-length)
           (fn-alb-long-header-linep octets (1+ *fn-article-max-octets*)))
  :hints (("Goal" :in-theory (e/d (fn-peer-decide-transfer fn-peer-intrinsic-refusal-of
                                   fn-peer-parse-limitp)
                                  (fn-article-parse fn-alb-long-header-linep
                                   fn-cbor-at-mostp fn-article-syntax-p
                                   fn-af-relayed-article-check fn-cfg-peer-find
                                   fn-af-message-idp fn-peer-history-hasp fn-peer-stagedp
                                   fn-retain-admissiblep fn-peer-relayed-octets
                                   fn-peer-scope-groups fn-peer-date-futurep
                                   fn-path-names-p fn-af-path-field-value
                                   fn-rck-path-wellformedp fn-rck-article-instant
                                   fn-peer-path-missingp))
           :use ((:instance fn-article-parse-limit-is-a-long-header-line)))))
