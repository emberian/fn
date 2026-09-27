; fn: D25 over the octets a served submission stores (SEC-006, PRF-210; D25
; restored under gpt-6's wave-5 review section 3, binding).
;
; The node generates RFC 8315 lines for the posting account in front of the
; injected block (books/cancel-lock.lisp fn-cl-served-payload, the local arm
; of books/owner-served-invariants.lisp fn-own-sub-stored-octets, which
; host/owner-host.lisp fn-owner-take stages).  Those lines are injecting-node
; metadata, outside the authored source: the host's verdict
; (fn-rcl-existing-action, reached through fn-rclb-existing-action and
; fn-pidx-existing-action at host/owner-host.lisp
; fn-owner-existing-action-buffer and fn-owner-prepare-buffer) reads both
; payloads through books/cancel-lock-lines.lisp fn-cll-skip.  So:
;
;   * a same-source retry under the held Message-ID is "already stored
;     here" whatever account and key epoch posted either copy
;     (`fn-cld-a-retry-by-any-account-or-epoch-is-already-stored'); a
;     duplicate writes nothing (books/poster-bytes-invariants.lisp
;     fn-pb-an-existing-action-writes-nothing), so the held lock is not
;     replaced and ownership does not move;
;   * a changed authored source, a changed user-supplied Cancel-Lock
;     included, is still a conflict
;     (`fn-cld-a-changed-source-is-a-conflict-whatever-the-account').
;
; The retrying account's cancel is refused because its key is its own
; (books/cancel-lock.lisp fn-cl-account-key-opens-exactly-its-lock; the
; collision figure in the record); the teeth show the concrete refusal.
;
; Prefix `fn-cld-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "source-routes")
(include-book "owner-served-invariants")

(local (in-theory (disable fn-inj-decide fn-inj-injectedp fn-inj-source-of
                           fn-inj-decision-octets fn-inj-decision-msgid
                           fn-find-article fn-cl-served-payload
                           fn-ctl-received-fields fn-cll-lines)))

; The verdict reads the two projections: when both projections are this
; agent's injections, the payloads are the same article exactly when the
; projections are.
(defthm fn-cld-same-article-reads-the-projections
  (implies (and (equal (fn-cll-skip p) x) (equal (fn-cll-skip h) y)
                (equal (fn-cll-skip x) x) (equal (fn-cll-skip y) y)
                (fn-inj-source-of x (fn-pb-path-agent x msgid) msgid)
                (fn-inj-source-of y (fn-pb-path-agent x msgid) msgid))
           (equal (fn-pb-same-articlep msgid p h) (fn-pb-same-articlep msgid x y)))
  :hints (("Goal" :in-theory (enable fn-pb-same-articlep fn-pb-subject fn-pb-path-agent))))

(local
 (defthm fn-cld-a-tombstone-opens-with-nul
   (implies (and (consp x) (not (equal (car x) 0)))
            (not (fn-rcl-tombstonep x)))
   :hints (("Goal" :in-theory (enable fn-rcl-tombstonep fn-rcl-prefixp)))))

(local
 (defthm fn-cld-car-of-append
   (implies (consp a) (equal (car (append a b)) (car a)))))

(local
 (defthm fn-cld-lines-open-with-c
   (implies (consp (fn-cll-lines lock keys))
            (equal (car (fn-cll-lines lock keys)) 67))
   :hints (("Goal" :in-theory (enable fn-cll-lines fn-cll-line fn-cll-key-line)))))

(local
 (defthm fn-cld-no-tombstone-behind-the-lines
   (implies (not (fn-rcl-tombstonep x))
            (not (fn-rcl-tombstonep (append (fn-cll-lines lock keys) x))))
   :hints (("Goal" :cases ((consp (fn-cll-lines lock keys)))
            :in-theory (e/d (fn-rcl-tombstonep fn-rcl-prefixp) (fn-cll-lines))))))

; The stored octets of an injected submission are never a tombstone.
(defthm fn-cld-stored-octets-of-an-injection-are-not-a-tombstone
  (implies (and (equal (fn-own-sub-decision sub) (fn-inj-decide source config obs))
                (fn-inj-injectedp (fn-inj-decide source config obs)))
           (not (fn-rcl-tombstonep (fn-own-sub-stored-octets cfg sub ring))))
  :hints (("Goal" :use ((:instance fn-own-sub-stored-octets-of-a-local-submission-by-definition
                                   (secret ring))
                        (:instance fn-cl-served-payload-is-the-lines-then-the-payload-by-definition
                                   (account (fn-own-sub-account sub))
                                   (msgid (fn-own-sub-msgid sub))
                                   (payload (fn-own-sub-octets sub)))
                        (:instance fn-sr-an-injection-is-not-a-tombstone (obs obs))
                        (:instance fn-cld-no-tombstone-behind-the-lines
                                   (x (fn-own-sub-octets sub))
                                   (lock (fn-cl-lock-value ring (fn-own-sub-account sub)
                                                           (fn-own-sub-msgid sub)
                                                           (fn-ctl-received-fields
                                                            (fn-own-sub-octets sub))))
                                   (keys (fn-cl-key-values ring (fn-own-sub-account sub)
                                                           (fn-ctl-received-fields
                                                            (fn-own-sub-octets sub))))))
           :in-theory (e/d (fn-own-sub-octets fn-own-sub-msgid)
                           (fn-own-sub-stored-octets fn-rcl-tombstonep
                            fn-cld-no-tombstone-behind-the-lines
                            fn-cl-lock-value fn-cl-key-values)))))

; The projection of what an injected submission stores is its injected
; octets, and those are their own projection.
(local
 (defthm fn-cld-projection-of-a-stored-injection
   (implies (and (equal (fn-own-sub-decision sub) (fn-inj-decide source config obs))
                 (fn-inj-injectedp (fn-inj-decide source config obs)))
            (equal (fn-cll-skip (fn-own-sub-stored-octets cfg sub ring))
                   (fn-inj-decision-octets (fn-inj-decide source config obs))))
   :hints (("Goal" :use ((:instance fn-own-stored-octets-keep-the-injected-octets
                                    (secret ring))
                         (:instance fn-pb-an-injection-does-not-open-with-c))
            :in-theory (disable fn-own-sub-stored-octets)))))

(local
 (defthm fn-cld-an-injection-reads-its-source
   (implies (fn-inj-injectedp (fn-inj-decide source config obs))
            (fn-inj-source-of (fn-inj-decision-octets (fn-inj-decide source config obs))
                              (fn-inj-config-agent config)
                              (fn-inj-decision-msgid (fn-inj-decide source config obs))))
   :hints (("Goal" :use ((:instance fn-inj-source-of-inverts-the-injection
                                    (observation obs)))))))

; KEYSTONE (D25 restored: a retry is a duplicate across accounts and key
; epochs).  The held article is the octets a submission SUB-A stored for a
; source injected at clock A, under any key ring RING-A and account; the
; same source submitted again at clock B by any account under any key ring
; RING-B, under the same Message-ID and groups, is "already stored here".
; Subject: fn-rcl-existing-action over fn-own-sub-stored-octets, the host's
; verdict over the octets fn-owner-take stages.
(defthm fn-cld-a-retry-by-any-account-or-epoch-is-already-stored
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
        (da (fn-inj-decide source config a))
        (db (fn-inj-decide source config b)))
    (implies (and (equal (fn-own-sub-decision sub-a) da)
                  (equal (fn-own-sub-decision sub-b) db)
                  (equal (fn-article-payload held)
                         (fn-own-sub-stored-octets cfg-a sub-a ring-a))
                  (fn-inj-injectedp da)
                  (fn-inj-injectedp db)
                  (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                  (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                  (equal groups (fn-article-groups held)))
             (equal (fn-rcl-existing-action
                     msgid (fn-own-sub-stored-octets cfg-b sub-b ring-b) groups s)
                    :duplicate)))
  :hints (("Goal" :cases ((fn-find-article
                            msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
                  :use ((:instance fn-cld-stored-octets-of-an-injection-are-not-a-tombstone
                                   (sub sub-a) (obs a) (cfg cfg-a) (ring ring-a))
                        (:instance fn-cld-projection-of-a-stored-injection
                                   (sub sub-a) (obs a) (cfg cfg-a) (ring ring-a))
                        (:instance fn-cld-projection-of-a-stored-injection
                                   (sub sub-b) (obs b) (cfg cfg-b) (ring ring-b))
                        (:instance fn-pb-an-injection-is-its-own-projection (obs a))
                        (:instance fn-pb-an-injection-is-its-own-projection (obs b))
                        (:instance fn-cld-an-injection-reads-its-source (obs a))
                        (:instance fn-cld-an-injection-reads-its-source (obs b))
                        (:instance fn-pb-path-agent-of-an-injection (obs b))
                        (:instance fn-cld-same-article-reads-the-projections
                                   (msgid (fn-record-string-octets msgid))
                                   (p (fn-own-sub-stored-octets cfg-b sub-b ring-b))
                                   (h (fn-own-sub-stored-octets cfg-a sub-a ring-a))
                                   (x (fn-inj-decision-octets (fn-inj-decide source config b)))
                                   (y (fn-inj-decision-octets (fn-inj-decide source config a))))
                        (:instance fn-pb-one-source-at-two-clocks-is-one-article
                                   (msgid (fn-record-string-octets msgid))))
                  :in-theory (e/d (fn-rcl-existing-action fn-rcl-same-articlep)
                                  (fn-rcl-tombstonep fn-article-groups
                                   fn-own-sub-stored-octets fn-pb-same-articlep
                                   fn-pb-path-agent fn-cll-skip))))
  :rule-classes nil)

; KEYSTONE (no over-normalization survives the lines).  A different authored
; source under the held Message-ID -- one changed authored byte, a changed or
; added user-supplied Cancel-Lock -- is a conflict, whatever accounts and key
; rings stored and submit the two.
(defthm fn-cld-a-changed-source-is-a-conflict-whatever-the-account
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
        (da (fn-inj-decide source1 config a))
        (db (fn-inj-decide source2 config b)))
    (implies (and (equal (fn-own-sub-decision sub-a) da)
                  (equal (fn-own-sub-decision sub-b) db)
                  (equal (fn-article-payload held)
                         (fn-own-sub-stored-octets cfg-a sub-a ring-a))
                  (fn-inj-injectedp da)
                  (fn-inj-injectedp db)
                  (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                  (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                  (not (equal source1 source2)))
             (equal (fn-rcl-existing-action
                     msgid (fn-own-sub-stored-octets cfg-b sub-b ring-b) groups s)
                    :conflict)))
  :hints (("Goal" :cases ((fn-find-article
                            msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
                  :use ((:instance fn-cld-stored-octets-of-an-injection-are-not-a-tombstone
                                   (sub sub-a) (source source1) (obs a) (cfg cfg-a)
                                   (ring ring-a))
                        (:instance fn-cld-projection-of-a-stored-injection
                                   (sub sub-a) (source source1) (obs a) (cfg cfg-a)
                                   (ring ring-a))
                        (:instance fn-cld-projection-of-a-stored-injection
                                   (sub sub-b) (source source2) (obs b) (cfg cfg-b)
                                   (ring ring-b))
                        (:instance fn-pb-an-injection-is-its-own-projection
                                   (source source1) (obs a))
                        (:instance fn-pb-an-injection-is-its-own-projection
                                   (source source2) (obs b))
                        (:instance fn-cld-an-injection-reads-its-source
                                   (source source1) (obs a))
                        (:instance fn-cld-an-injection-reads-its-source
                                   (source source2) (obs b))
                        (:instance fn-pb-path-agent-of-an-injection
                                   (source source2) (obs b))
                        (:instance fn-cld-same-article-reads-the-projections
                                   (msgid (fn-record-string-octets msgid))
                                   (p (fn-own-sub-stored-octets cfg-b sub-b ring-b))
                                   (h (fn-own-sub-stored-octets cfg-a sub-a ring-a))
                                   (x (fn-inj-decision-octets (fn-inj-decide source2 config b)))
                                   (y (fn-inj-decision-octets (fn-inj-decide source1 config a))))
                        (:instance fn-pb-two-sources-are-two-articles
                                   (msgid (fn-record-string-octets msgid))))
                  :in-theory (e/d (fn-rcl-existing-action fn-rcl-same-articlep)
                                  (fn-rcl-tombstonep fn-article-groups
                                   fn-own-sub-stored-octets fn-pb-same-articlep
                                   fn-pb-path-agent fn-cll-skip))))
  :rule-classes nil)
