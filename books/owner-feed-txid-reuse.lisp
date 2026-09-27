; fn: a transaction id reused after a crash, against the FNFD feed journal's
; durable intents (lane log-2, 2026-09-27; PKT-COL-8 of lane
; commit-onto-log's record).
;
; On the record log (format 9) the next transaction id is derived from the
; log at open (host/native/io.lisp fnn-recover-log: fn-store-log-next-txid),
; so a txid the owner handed out and never logged is handed out again after
; a crash (the design's PostgreSQL rule).  A served POST journals its FNFD
; feed INTENT, naming its txid, before the store mutation
; (host/owner-host.lisp fn-owner-submission-intent), so the feed journal may
; hold a dead intent with txid T and, after the open, a new intent with the
; same T.  Which fix the model supports:
;
;   (i)  floor the log's next txid at the journals' largest intent + 1, or
;   (ii) the journal's rule already tolerates the repeat.
;
; It is (ii), for two reasons proved here over the functions the host calls:
;
;   fn-own-feed-intent-reconcile-kind-reads-no-txid -- the open's
;       reconciliation of a pending intent (books/owner.lisp
;       fn-own-feed-intent-reconcile-kind, called through
;       host/owner-host.lisp fn-owner-feed-reconcile-next by
;       host/native/owner.lisp fnn-owner-feed-reconcile) decides from the
;       intent's Message-ID, identity and evidence against the recovered
;       store; the txid (and generation and tick) are not read.  A dead
;       intent is resolved by what the store holds, whatever txid it named.
;   fn-own-feed-intent-reuse-is-a-fresh-intent (KEYSTONE) -- the journal's
;       fold (books/owner-feed.lisp fn-own-feed-intent-apply, host:
;       fn-owner-feed-reconcile-apply and the journal replay) keys an intent
;       by its complete tuple (peer, Message-ID, identity, evidence,
;       generation, txid, tick).  When no intent of that key is pending --
;       and the open resolves EVERY pending intent before the owner serves
;       (fnn-owner-feed-reconcile loops to :done before the service starts)
;       -- a new intent adds exactly its key, and its resolution restores the
;       pending set exactly: an earlier incarnation with the same txid (or
;       the same whole key) is neither resolved by it nor resolves it.
;
; The feed's offerable state (books/peer-feed.lisp) never admits an intent
; or an abort, and nothing orders by txid, so no other reader sees the
; repeat.  Flooring the txid (i) is therefore not needed; it would add a
; decision the host must feed from every journal at open.
(in-package "ACL2")
(include-book "owner")

; The decision reads the tuple's slots 1 to 3 (Message-ID, identity,
; evidence) only: any tail after them decides the same.
(local
 (defthm fn-own-feed-intent-reconcile-kind-reads-three-slots
   (equal (fn-own-feed-intent-reconcile-kind node (list* p m i e rest))
          (fn-own-feed-intent-reconcile-kind node (list* p2 m i e rest2)))
   :rule-classes nil
   :hints (("Goal" :in-theory '(fn-own-feed-intent-reconcile-kind fn-frame-item
                                car-cons cdr-cons (:e zp) (:e fn-frame-item))
            :expand ((fn-frame-item 1 (list* p m i e rest)) (fn-frame-item 2 (list* p m i e rest))
                     (fn-frame-item 3 (list* p m i e rest))
                     (fn-frame-item 1 (list* p2 m i e rest2)) (fn-frame-item 2 (list* p2 m i e rest2))
                     (fn-frame-item 3 (list* p2 m i e rest2)))))))

; The intent tuple (books/owner-feed.lisp fn-own-feed-intent-values).
(defthm fn-own-feed-intent-reconcile-kind-reads-no-txid
  (equal (fn-own-feed-intent-reconcile-kind
          node (fn-own-feed-intent-values peer msgid identity evidence generation txid tick))
         (fn-own-feed-intent-reconcile-kind
          node (fn-own-feed-intent-values peer msgid identity evidence generation2 txid2 tick2)))
  :hints (("Goal" :in-theory '(fn-own-feed-intent-values)
           :use ((:instance fn-own-feed-intent-reconcile-kind-reads-three-slots
                            (p (fn-record-string-octets peer)) (p2 (fn-record-string-octets peer))
                            (m msgid) (i identity) (e evidence)
                            (rest (list (nfix generation) (nfix txid) (nfix tick)))
                            (rest2 (list (nfix generation2) (nfix txid2) (nfix tick2))))))))

(local
 (defthm fn-own-feed-intent-remove-of-non-member
   (implies (and (true-listp intents) (not (fn-own-feed-intent-memberp key intents)))
            (equal (fn-own-feed-intent-remove key intents) intents))
   :hints (("Goal" :induct (fn-own-feed-intent-remove key intents)
            :in-theory '(fn-own-feed-intent-remove fn-own-feed-intent-memberp true-listp
                         car-cons cdr-cons cons-car-cdr)))))

(defthm fn-own-feed-intent-reuse-is-a-fresh-intent
  (implies (and (true-listp intents)
                (not (fn-own-feed-intent-memberp (fn-own-feed-intent-key values) intents))
                (member-equal kind '(:feed-commit :feed-abort)))
           (let ((pending (fn-own-feed-intent-apply intents :feed-intent values)))
             (and (equal pending (cons (fn-own-feed-intent-key values) intents))
                  (equal (fn-own-feed-intent-apply pending kind values) intents))))
  :hints (("Goal" :do-not-induct t
           :in-theory '(fn-own-feed-intent-apply fn-own-feed-intent-remove-of-non-member
                        fn-own-feed-intent-remove member-equal car-cons cdr-cons
                        (:e equal) (:e member-equal)))))
