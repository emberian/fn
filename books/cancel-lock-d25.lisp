; fn: D25 over the octets a served submission stores (SEC-006, PRF-210; D25
; restored under gpt-6's wave-5 review section 3, binding).
;
; The node generates RFC 8315 lines for the posting account in front of the
; injected block (books/cancel-lock.lisp fn-cl-served-payload, the local arm
; of books/owner-served-invariants.lisp fn-own-sub-stored-octets, which
; host/owner-host.lisp fn-owner-take stages).  Those lines are injecting-node
; metadata, outside the authored source: the host's verdict
; (fn-store-existing-action, books/store-intern.lisp, reached through
; fn-pidx-existing-action at host/owner-host.lisp
; fn-owner-existing-action-buffer and fn-owner-prepare-buffer; the held
; payload read through the payload arena by its handle) reads both payloads
; through books/cancel-lock-lines.lisp fn-cll-skip.  So:
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
; PKT-597: the injected octets carry the Injection-Info parameters.
(include-book "injection-info-params-invariants")

(local (in-theory (disable fn-inj-decide fn-inj-injectedp fn-inj-source-of
                           fn-inj-decision-octets fn-inj-decision-msgid
                           fn-find-article fn-cl-served-payload
                           fn-ctl-received-fields fn-cll-lines)))

; An absent article's payload (nil) reads as no bytes.
(local (defthm fn-cld-no-handle-reads-no-bytes
  (equal (fn-handle-bytes nil fn-arena) nil)
  :hints (("Goal" :in-theory (enable fn-handle-bytes)))))

; The verdict reads the two projections: when both projections are this
; agent's injections, the payloads are the same article exactly when the
; projections are.
(defthm fn-cld-same-article-reads-the-projections
  (implies (and (equal (fn-cll-skip p) x) (equal (fn-cll-skip h) y)
                (equal (fn-cll-skip x) x) (equal (fn-cll-skip y) y)
                (fn-inj-source-of x (fn-pb-path-agent x msgid) msgid)
                (fn-inj-source-of y (fn-pb-path-agent x msgid) msgid))
           (equal (fn-pb-same-articlep msgid p h) (fn-pb-same-articlep msgid x y)))
  :hints (("Goal" :in-theory (union-theories '(fn-pb-same-articlep fn-pb-subject
                                               fn-pb-path-agent car-cons cdr-cons
                                               cons-equal)
                                             (theory 'minimal-theory)))))

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

(local
 (defthm fn-cld-injected-car
   (implies (fn-inj-injectedp d) (equal (car d) :injected))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-inj-injectedp fn-inj-decision-status fn-inj-car)
            :expand ((fn-inj-nth 0 d))))))

(local
 (defthm fn-cld-an-injection-is-not-transit
   (implies (fn-inj-injectedp d) (not (fn-peer-submissionp d)))
   :hints (("Goal" :in-theory (e/d (fn-peer-submissionp fn-ag-car)
                                   (fn-inj-injectedp fn-nntp-printable-tokenp
                                    fn-af-message-idp fn-peer-submission-shapep))
            :use fn-cld-injected-car))))

; The stored octets of an injected submission are never a tombstone: they
; open with the node's Cancel-Lock ("C") or, without one, with the injected
; block ("P" or "I"; fn-ipp-an-injection-does-not-open-with-c).
(local
 (defthm fn-cld-injected-octets-are-a-cons-not-opening-with-nul
   (let ((x (fn-ipp-injected-octets (fn-inj-decide source config obs) ring login cfg)))
     (implies (fn-inj-injectedp (fn-inj-decide source config obs))
              (not (fn-rcl-tombstonep x))))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use ((:instance fn-ipp-an-injection-opens-with-p-or-i (secret ring))
                  (:instance fn-cld-a-tombstone-opens-with-nul
                             (x (fn-ipp-injected-octets (fn-inj-decide source config obs)
                                                        ring login cfg))))))))

(defthm fn-cld-stored-octets-of-an-injection-are-not-a-tombstone
  (implies (and (equal (fn-own-sub-decision sub) (fn-inj-decide source config obs))
                (fn-inj-injectedp (fn-inj-decide source config obs)))
           (not (fn-rcl-tombstonep (fn-own-sub-stored-octets cfg sub ring))))
  :hints (("Goal" :use ((:instance fn-own-sub-stored-octets-of-a-local-submission-by-definition
                                   (secret ring))
                        (:instance fn-cl-served-payload-is-the-lines-then-the-payload-by-definition
                                   (account (fn-own-sub-account sub))
                                   (msgid (fn-own-sub-msgid sub))
                                   (payload (fn-ipp-injected-octets (fn-own-sub-decision sub)
                                                                    ring (fn-own-sub-login sub)
                                                                    cfg)))
                        (:instance fn-cld-injected-octets-are-a-cons-not-opening-with-nul
                                   (login (fn-own-sub-login sub)))
                        (:instance fn-cld-an-injection-is-not-transit
                                   (d (fn-inj-decide source config obs)))
                        (:instance fn-cld-no-tombstone-behind-the-lines
                                   (x (fn-ipp-injected-octets (fn-own-sub-decision sub)
                                                              ring (fn-own-sub-login sub) cfg))
                                   (lock (fn-cl-lock-value ring (fn-own-sub-account sub)
                                                           (fn-own-sub-msgid sub)
                                                           (fn-ctl-received-fields
                                                            (fn-ipp-injected-octets
                                                             (fn-own-sub-decision sub) ring
                                                             (fn-own-sub-login sub) cfg))))
                                   (keys (fn-cl-key-values ring (fn-own-sub-account sub)
                                                           (fn-ctl-received-fields
                                                            (fn-ipp-injected-octets
                                                             (fn-own-sub-decision sub) ring
                                                             (fn-own-sub-login sub) cfg))))))
           :in-theory (e/d (fn-own-sub-msgid)
                           (fn-own-sub-stored-octets fn-rcl-tombstonep fn-ipp-injected-octets
                            fn-cld-no-tombstone-behind-the-lines
                            fn-cl-lock-value fn-cl-key-values)))))

; The projection of what an injected submission stores is its injected
; octets, and those are their own projection.
(local
 (defthm fn-cld-projection-of-a-stored-injection
   (implies (and (equal (fn-own-sub-decision sub) (fn-inj-decide source config obs))
                 (fn-inj-injectedp (fn-inj-decide source config obs)))
            (equal (fn-cll-skip (fn-own-sub-stored-octets cfg sub ring))
                   (fn-ipp-injected-octets (fn-inj-decide source config obs) ring
                                           (fn-own-sub-login sub) cfg)))
   :hints (("Goal" :use ((:instance fn-own-stored-octets-keep-the-injected-octets
                                    (secret ring))
                         (:instance fn-ipp-an-injection-does-not-open-with-c
                                    (secret ring) (login (fn-own-sub-login sub)))
                         (:instance fn-cld-an-injection-is-not-transit
                                    (d (fn-inj-decide source config obs))))
            :in-theory (disable fn-own-sub-stored-octets fn-ipp-injected-octets)))))

; What an injected submission stores is not empty (an absent held article's
; payload reads as no bytes, so it is no retry's held article).
(local
 (defthm fn-cld-stored-octets-of-an-injection-are-not-empty
   (implies (and (equal (fn-own-sub-decision sub) (fn-inj-decide source config obs))
                 (fn-inj-injectedp (fn-inj-decide source config obs)))
            (fn-own-sub-stored-octets cfg sub ring))
   :rule-classes nil
   :hints (("Goal" :use (fn-cld-projection-of-a-stored-injection
                         (:instance fn-ipp-an-injection-opens-with-p-or-i
                                    (secret ring) (login (fn-own-sub-login sub))))
            :in-theory (disable fn-own-sub-stored-octets fn-ipp-injected-octets
                                fn-cld-projection-of-a-stored-injection
                                fn-ipp-an-injection-opens-with-p-or-i)))))

(local
 (defthm fn-cld-injected-octets-are-their-own-projection
   (implies (fn-inj-injectedp (fn-inj-decide source config obs))
            (equal (fn-cll-skip (fn-ipp-injected-octets (fn-inj-decide source config obs)
                                                        ring login cfg))
                   (fn-ipp-injected-octets (fn-inj-decide source config obs)
                                           ring login cfg)))
   :hints (("Goal" :in-theory (disable fn-ipp-injected-octets fn-cll-skip)
            :use ((:instance fn-ipp-an-injection-does-not-open-with-c (secret ring))
                  (:instance fn-cll-skip-of-an-article-not-opening-with-c
                             (x (fn-ipp-injected-octets (fn-inj-decide source config obs)
                                                        ring login cfg))))))))

(local
 (defthm fn-cld-injected-octets-read-their-source
   (implies (fn-inj-injectedp (fn-inj-decide source config obs))
            (fn-inj-source-of (fn-ipp-injected-octets (fn-inj-decide source config obs)
                                                      ring login cfg)
                              (fn-inj-config-agent config)
                              (fn-inj-decision-msgid (fn-inj-decide source config obs))))
   :hints (("Goal" :in-theory (disable fn-ipp-injected-octets)
            :use ((:instance fn-ipp-injected-octets-carry-the-parameters
                             (secret ring)))))))

(local
 (defthm fn-cld-an-injection-reads-its-source
   (implies (fn-inj-injectedp (fn-inj-decide source config obs))
            (fn-inj-source-of (fn-inj-decision-octets (fn-inj-decide source config obs))
                              (fn-inj-config-agent config)
                              (fn-inj-decision-msgid (fn-inj-decide source config obs))))
   :hints (("Goal" :use ((:instance fn-inj-source-of-inverts-the-injection
                                    (observation obs)))))))

; Two stored injections under one Message-ID are one article exactly when
; their sources are one, whatever account, login, key ring and complaints
; address stored each (the node's Cancel-Lock lines and Injection-Info
; parameters are outside the source; PKT-597).
(defthm fn-cld-two-stored-injections-are-one-article-iff-one-source
  (let ((da (fn-inj-decide source1 config a))
        (db (fn-inj-decide source2 config b)))
    (implies (and (equal (fn-own-sub-decision sub-a) da)
                  (equal (fn-own-sub-decision sub-b) db)
                  (fn-inj-injectedp da) (fn-inj-injectedp db)
                  (equal (fn-inj-decision-msgid da) (fn-inj-decision-msgid db)))
             (equal (fn-pb-same-articlep (fn-inj-decision-msgid db)
                                         (fn-own-sub-stored-octets cfg-b sub-b ring-b)
                                         (fn-own-sub-stored-octets cfg-a sub-a ring-a))
                    (equal source1 source2))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-cld-projection-of-a-stored-injection
                            (sub sub-a) (source source1) (obs a) (cfg cfg-a) (ring ring-a))
                 (:instance fn-cld-projection-of-a-stored-injection
                            (sub sub-b) (source source2) (obs b) (cfg cfg-b) (ring ring-b))
                 (:instance fn-cld-injected-octets-are-their-own-projection
                            (source source1) (obs a) (cfg cfg-a) (ring ring-a)
                            (login (fn-own-sub-login sub-a)))
                 (:instance fn-cld-injected-octets-are-their-own-projection
                            (source source2) (obs b) (cfg cfg-b) (ring ring-b)
                            (login (fn-own-sub-login sub-b)))
                 (:instance fn-cld-injected-octets-read-their-source
                            (source source1) (obs a) (cfg cfg-a) (ring ring-a)
                            (login (fn-own-sub-login sub-a)))
                 (:instance fn-cld-injected-octets-read-their-source
                            (source source2) (obs b) (cfg cfg-b) (ring ring-b)
                            (login (fn-own-sub-login sub-b)))
                 (:instance fn-ipp-path-agent-of-the-injected-octets
                            (source source2) (obs b) (cfg cfg-b) (secret ring-b)
                            (login (fn-own-sub-login sub-b)))
                 (:instance fn-cld-same-article-reads-the-projections
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source2 config b)))
                            (p (fn-own-sub-stored-octets cfg-b sub-b ring-b))
                            (h (fn-own-sub-stored-octets cfg-a sub-a ring-a))
                            (x (fn-ipp-injected-octets (fn-inj-decide source2 config b)
                                                       ring-b (fn-own-sub-login sub-b) cfg-b))
                            (y (fn-ipp-injected-octets (fn-inj-decide source1 config a)
                                                       ring-a (fn-own-sub-login sub-a) cfg-a)))
                 (:instance fn-ipp-same-articlep-of-two-injections
                            (obs1 a) (obs2 b) (secret1 ring-a) (secret2 ring-b)
                            (login1 (fn-own-sub-login sub-a)) (login2 (fn-own-sub-login sub-b))
                            (cfg1 cfg-a) (cfg2 cfg-b))))))

; KEYSTONE (D25 restored: a retry is a duplicate across accounts and key
; epochs).  The held article is the octets a submission SUB-A stored for a
; source injected at clock A, under any key ring RING-A and account; the
; same source submitted again at clock B by any account under any key ring
; RING-B, under the same Message-ID and groups, is "already stored here".
; Subject: fn-store-existing-action over fn-own-sub-stored-octets, the
; host's verdict over the octets fn-owner-take stages; the held article's
; bytes are read through the arena FN-ARENA by its handle.
(defthm fn-cld-a-retry-by-any-account-or-epoch-is-already-stored
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
        (da (fn-inj-decide source config a))
        (db (fn-inj-decide source config b)))
    (implies (and (equal (fn-own-sub-decision sub-a) da)
                  (equal (fn-own-sub-decision sub-b) db)
                  (equal (fn-handle-bytes (fn-article-payload held) fn-arena)
                         (fn-own-sub-stored-octets cfg-a sub-a ring-a))
                  (fn-inj-injectedp da)
                  (fn-inj-injectedp db)
                  (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                  (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                  (equal groups (fn-article-groups held)))
             (equal (fn-store-existing-action
                     msgid (fn-own-sub-stored-octets cfg-b sub-b ring-b) groups s fn-arena)
                    :duplicate)))
  :hints (("Goal" :cases ((fn-find-article
                            msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
                  :use ((:instance fn-cld-stored-octets-of-an-injection-are-not-a-tombstone
                                   (sub sub-a) (source source) (obs a) (cfg cfg-a) (ring ring-a))
                        (:instance fn-cld-stored-octets-of-an-injection-are-not-empty
                                   (sub sub-a) (source source) (obs a) (cfg cfg-a) (ring ring-a))
                        (:instance fn-cld-projection-of-a-stored-injection
                                   (sub sub-a) (source source) (obs a) (cfg cfg-a) (ring ring-a))
                        (:instance fn-ipp-an-injection-opens-with-p-or-i
                                   (source source) (obs a) (cfg cfg-a) (secret ring-a)
                                   (login (fn-own-sub-login sub-a)))
                        (:instance fn-cld-two-stored-injections-are-one-article-iff-one-source
                                   (source1 source) (source2 source)))
                  :in-theory (e/d (fn-store-existing-action fn-rcl-same-articlep)
                                  (fn-handle-bytes
                                   fn-store-existing-action-is-the-verdict-over-alpha
                                   fn-rcl-tombstonep fn-article-groups fn-ipp-injected-octets
                                   fn-own-sub-stored-octets fn-pb-same-articlep
                                   fn-pb-path-agent fn-cll-skip fn-inj-decide
                                   fn-inj-injectedp))))
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
                  (equal (fn-handle-bytes (fn-article-payload held) fn-arena)
                         (fn-own-sub-stored-octets cfg-a sub-a ring-a))
                  (fn-inj-injectedp da)
                  (fn-inj-injectedp db)
                  (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                  (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                  (not (equal source1 source2)))
             (equal (fn-store-existing-action
                     msgid (fn-own-sub-stored-octets cfg-b sub-b ring-b) groups s fn-arena)
                    :conflict)))
  :hints (("Goal" :cases ((fn-find-article
                            msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
                  :use ((:instance fn-cld-stored-octets-of-an-injection-are-not-a-tombstone
                                   (sub sub-a) (source source1) (obs a) (cfg cfg-a) (ring ring-a))
                        (:instance fn-cld-stored-octets-of-an-injection-are-not-empty
                                   (sub sub-a) (source source1) (obs a) (cfg cfg-a) (ring ring-a))
                        (:instance fn-cld-projection-of-a-stored-injection
                                   (sub sub-a) (source source1) (obs a) (cfg cfg-a) (ring ring-a))
                        (:instance fn-ipp-an-injection-opens-with-p-or-i
                                   (source source1) (obs a) (cfg cfg-a) (secret ring-a)
                                   (login (fn-own-sub-login sub-a)))
                        (:instance fn-cld-two-stored-injections-are-one-article-iff-one-source
                                   (source1 source1) (source2 source2)))
                  :in-theory (e/d (fn-store-existing-action fn-rcl-same-articlep)
                                  (fn-handle-bytes
                                   fn-store-existing-action-is-the-verdict-over-alpha
                                   fn-rcl-tombstonep fn-article-groups fn-ipp-injected-octets
                                   fn-own-sub-stored-octets fn-pb-same-articlep
                                   fn-pb-path-agent fn-cll-skip fn-inj-decide
                                   fn-inj-injectedp))))
  :rule-classes nil)
