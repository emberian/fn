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
; The Message-ID is a transfer's; nothing here assumes two peers send the
; same octets under one Message-ID.  If they do not (RFC 5536 section 3.1.3:
; a Message-ID names one article), the memory refuses the second on the
; first's refusal, which is the reject-history behaviour of INN; the
; statement below says whose octets the reason is about.
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

; A transfer is (msgid . octets), as the owner holds it in flight.
(defun fn-prof-run (mem cfg transfers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp transfers)
      (fn-prof-run (fn-peer-refused-record mem cfg (car (car transfers))
                                           (cdr (car transfers)))
                   cfg (cdr transfers))
    mem))

; The first transfer that drew reason R for the Message-ID string M.
(defun fn-prof-witness (m r transfers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp transfers)
      (if (and (consp (car transfers))
               (fn-af-message-idp (car (car transfers)))
               (equal (fn-record-octets-string (car (car transfers))) m)
               (equal (fn-peer-intrinsic-refusal (car (car transfers))
                                                 (cdr (car transfers)))
                      r))
          (car transfers)
        (fn-prof-witness m r (cdr transfers)))
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
  (implies (fn-prof-witness m r a)
           (equal (fn-prof-witness m r (append a b))
                  (fn-prof-witness m r a))))

(defthm fn-prof-soundp-of-append-right
  (implies (fn-prof-soundp mem ts)
           (fn-prof-soundp mem (append ts b))))

(defthm fn-prof-witness-of-appended-transfer
  (implies (and (consp e)
                (fn-af-message-idp (car e))
                (equal (fn-record-octets-string (car e)) m)
                (equal (fn-peer-intrinsic-refusal (car e) (cdr e)) r))
           (fn-prof-witness m r (append ts (list e))))
  :hints (("Goal" :in-theory (disable fn-peer-intrinsic-refusal
                                      fn-af-message-idp fn-record-octets-string))))

(defthm fn-prof-soundp-of-first
  (implies (fn-prof-soundp mem ts)
           (fn-prof-soundp (fn-rof-first n mem) ts))
  :hints (("Goal" :in-theory (enable fn-rof-first))))

(defthm fn-prof-lookup-of-sound-has-a-witness
  (implies (and (fn-prof-soundp mem ts) (fn-rof-lookup m mem))
           (fn-prof-witness m (fn-rof-lookup m mem) ts)))

(local (defthm fn-prof-refused-record-of-a-non-message-id
  (implies (not (fn-af-message-idp msgid))
           (equal (fn-peer-refused-record mem cfg msgid octets) mem))
  :hints (("Goal" :in-theory (enable fn-peer-refused-record)))))

(local (defthm fn-prof-message-idp-of-nil
  (not (fn-af-message-idp nil))
  :hints (("Goal" :in-theory (enable fn-af-message-idp)))))

; One record keeps the memory sound over the transfers so far and this one.
(defthm fn-prof-record-keeps-soundness
  (implies (fn-prof-soundp mem ts)
           (fn-prof-soundp (fn-peer-refused-record mem cfg (car e) (cdr e))
                           (append ts (list e))))
  :hints (("Goal" :do-not-induct t
           :cases ((consp e))
           :in-theory (e/d (fn-peer-refused-record fn-rof-record)
                           (fn-peer-intrinsic-refusal fn-rof-first fn-prof-soundp
                            fn-prof-soundp-of-first fn-prof-witness
                            fn-af-message-idp fn-record-octets-string))
           :expand ((fn-prof-soundp
                     (cons (cons (fn-record-octets-string (car e))
                                 (fn-peer-intrinsic-refusal (car e) (cdr e)))
                           mem)
                     (append ts (list e))))
           :use ((:instance fn-prof-soundp-of-first
                            (n (fn-rck-refused-capacity cfg))
                            (mem (cons (cons (fn-record-octets-string (car e))
                                             (fn-peer-intrinsic-refusal (car e)
                                                                        (cdr e)))
                                       mem))
                            (ts (append ts (list e))))
                 (:instance fn-prof-witness-of-appended-transfer
                            (m (fn-record-octets-string (car e)))
                            (r (fn-peer-intrinsic-refusal (car e) (cdr e))))
                 (:instance fn-prof-soundp-of-append-right
                            (b (list e)))))))

(defun fn-prof-run-ind (mem cfg transfers done)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp transfers)
      (fn-prof-run-ind (fn-peer-refused-record mem cfg (car (car transfers))
                                               (cdr (car transfers)))
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
  (implies (fn-prof-witness m r ts)
           (and (member-equal (fn-prof-witness m r ts) ts)
                (fn-af-message-idp (car (fn-prof-witness m r ts)))
                (equal (fn-record-octets-string (car (fn-prof-witness m r ts))) m)
                (equal (fn-peer-intrinsic-refusal (car (fn-prof-witness m r ts))
                                                  (cdr (fn-prof-witness m r ts)))
                       r)))
  :hints (("Goal" :induct (fn-prof-witness m r ts)
           :in-theory (disable fn-peer-intrinsic-refusal fn-af-message-idp
                               fn-record-octets-string))))

; KEYSTONE: a memory built from nothing by the owner's record step names, for
; every Message-ID it holds, a transfer of that Message-ID whose octets drew
; exactly the remembered refusal.
(defthm fn-prof-run-is-sound
  (implies (fn-rof-lookup m (fn-prof-run nil cfg transfers))
           (let ((w (fn-prof-witness m (fn-rof-lookup m (fn-prof-run nil cfg transfers))
                                     transfers)))
             (and (member-equal w transfers)
                  (fn-af-message-idp (car w))
                  (equal (fn-record-octets-string (car w)) m)
                  (equal (fn-peer-intrinsic-refusal (car w) (cdr w))
                         (fn-rof-lookup m (fn-prof-run nil cfg transfers))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-prof-run-sound-from (mem nil) (done nil))
                 (:instance fn-prof-witness-facts
                            (r (fn-rof-lookup m (fn-prof-run nil cfg transfers)))
                            (ts transfers))
                 (:instance fn-prof-lookup-of-sound-has-a-witness
                            (mem (fn-prof-run nil cfg transfers))
                            (ts transfers)))
           :in-theory (disable fn-prof-run-sound-from fn-prof-witness-facts
                               fn-prof-lookup-of-sound-has-a-witness
                               fn-prof-run fn-peer-intrinsic-refusal
                               fn-prof-witness fn-prof-soundp fn-rof-lookup
                               fn-af-message-idp fn-record-octets-string))))

; -----------------------------------------------------------------------------
; The offer answers the memory

; The owner's memory, built from transfers, is keyed by Message-ID strings:
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
  :hints (("Goal" :in-theory (enable fn-prof-run fn-peer-refused-record fn-rof-record
                                     fn-rof-lookup fn-record-octets-string))))

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

; KEYSTONE (the brief's statement).  An offer on a session whose memory the
; owner built from TRANSFERS, of a Message-ID the memory holds and the node
; has not accepted, is refused for the reason the parse of a remembered
; transfer of that Message-ID gives; and that transfer's own decision, on
; this node, from this peer, is the same refusal whenever its octets fit the
; peer's size.  The one re-parse the memory saves is equal to the answer.
(defthm fn-prof-offer-answer-is-the-reparse
  (let* ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
         (mem (fn-prof-run nil cfg0 transfers))
         (m (fn-record-octets-string msgid))
         (r (fn-rof-lookup m mem))
         (w (fn-prof-witness m r transfers)))
    (implies (and record
                  (fn-cfg-peer-inbound record)
                  (fn-af-message-idp msgid)
                  (not (fn-peer-history-hasp m node))
                  (equal (fn-peer-session-refused session) mem)
                  r)
             (and (equal (fn-peer-decide-offer node cfg peer session msgid clock
                                               inflight)
                         (fn-peer-decision :refuse r))
                  (member-equal w transfers)
                  (equal (fn-record-octets-string (car w)) m)
                  (equal (fn-peer-intrinsic-refusal (car w) (cdr w)) r)
                  (implies (<= (len (cdr w))
                               (fn-cfg-peer-inbound-max-octets record))
                           (equal (fn-peer-decide-transfer node cfg peer (car w)
                                                           (cdr w) clock2 id
                                                           subject)
                                  (fn-peer-decision :refuse r))))))
  :hints (("Goal" :use ((:instance fn-prof-run-is-sound
                                   (m (fn-record-octets-string msgid))
                                   (cfg cfg0))
                        (:instance fn-prof-witness-facts
                                   (m (fn-record-octets-string msgid))
                                   (r (fn-rof-lookup (fn-record-octets-string msgid)
                                                     (fn-prof-run nil cfg0 transfers)))
                                   (ts transfers))
                        (:instance fn-peer-intrinsic-refusal-is-an-intrinsic-reason
                                   (msgid (car (fn-prof-witness
                                                (fn-record-octets-string msgid)
                                                (fn-rof-lookup (fn-record-octets-string msgid)
                                                               (fn-prof-run nil cfg0 transfers))
                                                transfers)))
                                   (octets (cdr (fn-prof-witness
                                                 (fn-record-octets-string msgid)
                                                 (fn-rof-lookup (fn-record-octets-string msgid)
                                                                (fn-prof-run nil cfg0 transfers))
                                                 transfers))))
                        (:instance fn-peer-decide-offer-answers-the-memory)
                        (:instance fn-prof-run-keeps-no-posture (mem nil) (cfg cfg0))
                        (:instance fn-peer-decide-transfer-refuses-what-the-octets-refuse
                                   (clock clock2)
                                   (msgid (car (fn-prof-witness
                                                (fn-record-octets-string msgid)
                                                (fn-rof-lookup (fn-record-octets-string msgid)
                                                               (fn-prof-run nil cfg0 transfers))
                                                transfers)))
                                   (octets (cdr (fn-prof-witness
                                                 (fn-record-octets-string msgid)
                                                 (fn-rof-lookup (fn-record-octets-string msgid)
                                                                (fn-prof-run nil cfg0 transfers))
                                                 transfers)))))
           :in-theory (e/d (fn-peer-remembered-reason fn-peer-shed-p)
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
