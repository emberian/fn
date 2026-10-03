; fn: the acceptance node's articles ARE the retained rows' (W5b, lane
; stx-model-2, 2026-09-29): the carried correspondence PRF-995 named.
;
; books/stx-lace-rows.lisp fn-stx-lace-of-node-is-the-rows-lace (PRF-995)
; equates the node lace (books/stx-node-lace.lisp fn-stx-lace, the octet
; model over each handle's bytes) with the retained rows' lace under a
; hypothesis nothing carried: that ALPHA of the acceptance node's articles is
; the rows' articles read through the same arena.  The lace reads one field
; of an article -- its payload -- so what the served path must carry is
; arena-free: the node's articles and the indexed rows name the same
; Message-IDs and the same HANDLES, in the same (newest-first) order.  That
; is fn-snc-correspondp below, a relation between two fields of the store
; state, carried the way books/store-node.lisp carries fn-sn-indexedp
; (deliberately NOT a conjunct of fn-sn-statep, the guard the host checks on
; every call: D20, D21) and stated over the same rows, fn-sn-indexed-rows --
; in :completing the last row is durable but the node has not installed it
; (fn-install-pending and the record move are two steps of one completion),
; after a crash the node is the empty one and no row is indexed.
;
; The keystone fn-snc-node-lace-is-the-rows-lace: under the carried
; correspondence and the rows' context invariant, fn-stx-lace of the node IS
; fn-sn-lace-of-rows of the indexed rows -- PRF-995's conclusion with its
; open hypothesis replaced by the carried one.  The lace depends on the
; payloads alone (fn-snc-lace-of-store-reads-only-payloads), the payloads of
; ALPHA are the handles' bytes, and so are the rows' articles' payloads
; (fn-row-bytes is fn-handle-bytes of the row's handle).
;
; Establishment and preservation: fn-sn-initial (no articles, no rows) and
; fn-sn-crash (the empty node, no indexed row); then every transition that
; adds an article or changes the rows (lane stx-model-3): the finish (its
; article arm is gated on fn-sn-record-bindsp, which names the pending's
; Message-ID and payload as the completion record's; its composite arm
; installs the retained composite's held record; the other arms keep the
; store and add a row that is neither), the recovery (the replay equality:
; the loop conses one article per article row, with its record's Message-ID
; and payload, and keeps the store on every other row -- the two arm facts
; of books/acceptance-payload-ref.lisp, reproved here because that book
; includes the owner), prepare and the I/O steps (store and rows unchanged),
; set-keyring (fn-sn-recontext-rows changes contexts only), the two
; resolutions (books/store-node-resolution: store and rows unchanged) and
; the sweep (books/store-sweep: the store is returned as it was).
(in-package "ACL2")
(include-book "store-node-invariants")
(include-book "stx-lace-rows")
; The resolutions and the sweep add transitions to the machine; their
; preservation is stated here, so the correspondence is carried by every
; transition the host calls (D21), not by the core ones alone.
(include-book "store-node-resolution")
(include-book "store-sweep")

; -----------------------------------------------------------------------------
; The keys: (Message-ID . handle), newest first on both sides

(defun fn-snc-article-keys (articles)
  (declare (xargs :guard t))
  (if (atom articles)
      nil
    (cons (cons (fn-article-msgid (car articles))
                (fn-article-payload (car articles)))
          (fn-snc-article-keys (cdr articles)))))
(fn-payload-kind fn-snc-article-keys :handle "returns each article's handle beside its Message-ID")

(defun fn-snc-row-key (row)
  (declare (xargs :guard t))
  (cons (fn-record-msgid row) (fn-record-payload row)))

; Mirrors store-intern.lisp fn-rows-articles-newest-first arm for arm.
(defun fn-snc-row-keys-newest-first (rows)
  (declare (xargs :guard t))
  (cond ((atom rows) nil)
        ((fn-held-p (car rows))
         (append (fn-snc-row-keys-newest-first (cdr rows))
                 (list (fn-snc-row-key (car rows)))))
        ((fn-hstxa-p (car rows))
         (append (fn-snc-row-keys-newest-first (cdr rows))
                 (list (fn-snc-row-key (fn-hstxa-held (car rows))))))
        (t (fn-snc-row-keys-newest-first (cdr rows)))))

; THE CARRIED CORRESPONDENCE.
(defun fn-snc-correspondp (s)
  (declare (xargs :guard t))
  (equal (fn-snc-article-keys (fn-stx-store (fn-sn-node s)))
         (fn-snc-row-keys-newest-first (fn-sn-indexed-rows s))))

; -----------------------------------------------------------------------------
; The lace reads the payloads alone

(defun fn-snc-payloads (articles)
  (declare (xargs :guard t))
  (if (atom articles)
      nil
    (cons (fn-article-payload (car articles)) (fn-snc-payloads (cdr articles)))))
(fn-payload-kind fn-snc-payloads :handle "returns each article's handle")

(defun fn-snc-lace-of-payloads (payloads keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (consp payloads)
      (append (fn-snc-lace-of-payloads (cdr payloads) keyring)
              (fn-stx-delta (car payloads) keyring))
    nil))

(defthm fn-snc-lace-of-store-reads-only-payloads
  (equal (fn-stx-lace-of-store articles keyring)
         (fn-snc-lace-of-payloads (fn-snc-payloads articles) keyring))
  :hints (("Goal" :in-theory (e/d ((:d fn-stx-lace-of-store)) (fn-stx-delta)))))

; The bytes each handle denotes, in order.
(defun fn-snc-bytes-of-handles (handles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom handles)
      nil
    (cons (fn-handle-bytes (car handles) fn-arena)
          (fn-snc-bytes-of-handles (cdr handles) fn-arena))))

(defthm fn-snc-payloads-of-alpha
  (equal (fn-snc-payloads (fn-articles-wire-of articles fn-arena))
         (fn-snc-bytes-of-handles (strip-cdrs (fn-snc-article-keys articles)) fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-articles-wire-of) (fn-handle-bytes)))))

(local (defthm fn-snc-row-bytes-is-handle-bytes
  (equal (fn-row-bytes row fn-arena)
         (fn-handle-bytes (fn-record-payload row) fn-arena))
  :hints (("Goal" :in-theory (enable fn-row-bytes fn-handle-bytes)))))

(local (defthm fn-snc-payloads-of-append
  (equal (fn-snc-payloads (append a b))
         (append (fn-snc-payloads a) (fn-snc-payloads b)))))

(local (defthm fn-snc-bytes-of-handles-of-append
  (equal (fn-snc-bytes-of-handles (append a b) fn-arena)
         (append (fn-snc-bytes-of-handles a fn-arena)
                 (fn-snc-bytes-of-handles b fn-arena)))))

(local (defthm fn-snc-strip-cdrs-of-append
  (equal (strip-cdrs (append a b)) (append (strip-cdrs a) (strip-cdrs b)))))

(defthm fn-snc-payloads-of-the-rows-articles
  (equal (fn-snc-payloads (fn-rows-articles-newest-first rows fn-arena))
         (fn-snc-bytes-of-handles (strip-cdrs (fn-snc-row-keys-newest-first rows)) fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-rows-articles-newest-first)
                                  (fn-handle-bytes fn-row-bytes fn-held-p fn-hstxa-p)))))

; -----------------------------------------------------------------------------
; KEYSTONE: under the carried correspondence the node lace is the rows' lace.

(defthm fn-snc-node-lace-is-the-rows-lace
  (implies (and (fn-snc-correspondp s)
                (fn-rows-contexts-okp (fn-sn-indexed-rows s) keyring generation fn-arena))
           (equal (fn-stx-lace (fn-sn-node s) keyring fn-arena)
                  (fn-sn-lace-of-rows (fn-sn-indexed-rows s))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sn-lace-of-rows-is-the-wire-lace
                            (rows (fn-sn-indexed-rows s)))
                 (:instance fn-snc-lace-of-store-reads-only-payloads
                            (articles (fn-articles-wire-of (fn-stx-store (fn-sn-node s)) fn-arena)))
                 (:instance fn-snc-lace-of-store-reads-only-payloads
                            (articles (fn-rows-articles-newest-first (fn-sn-indexed-rows s) fn-arena))))
           :in-theory (e/d (fn-stx-lace fn-snc-correspondp)
                           (fn-sn-lace-of-rows-is-the-wire-lace fn-sn-lace-of-rows
                            fn-stx-lace-of-store fn-rows-articles-newest-first
                            fn-rows-contexts-okp fn-articles-wire-of fn-sn-indexed-rows
                            fn-snc-article-keys fn-snc-row-keys-newest-first
                            fn-snc-lace-of-store-reads-only-payloads fn-stx-store)))))

; -----------------------------------------------------------------------------
; Establishment at the initial store; preservation by a crash

(defthm fn-snc-initial-corresponds
  (fn-snc-correspondp (fn-sn-initial groups capacity))
  :hints (("Goal" :in-theory (enable fn-sn-initial fn-sn-indexed-rows fn-sn-indexed-rows-of
                                     fn-stx-store fn-node-initial-state fn-initial-state
                                     fn-sf-initial-state))))

(local (defthm fn-snc-statep-files
  (implies (fn-sn-statep s) (fn-sf-statep (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep))))))

; -by-recomputation, as fn-sn-crash-preserves-indexedp-by-recomputation: the
; node is reset to the empty one and no row is indexed after a crash.
(defthm fn-snc-crash-preserves-correspondp-by-recomputation
  (implies (and (fn-sn-statep s) (fn-snc-correspondp s))
           (fn-snc-correspondp (fn-sn-crash s frontier-choice record-choice)))
  :hints (("Goal" :in-theory (e/d (fn-sn-crash fn-sn-indexed-rows fn-stx-store
                                   fn-node-initial-state fn-initial-state)
                                  (fn-sn-statep fn-sf-crash fn-sf-crash-choicep
                                   fn-sn-indexed-rows-of))
           :use ((:instance fn-sn-indexed-rows-of-crash (files (fn-sn-files s)))))))

(in-theory (disable (:d fn-snc-correspondp)))

; =============================================================================
; PRESERVATION BY EVERY TRANSITION THAT ADDS AN ARTICLE OR CHANGES THE ROWS
; (lane stx-model-3).  The pattern is store-node-invariants' preservation
; set: the store side is one fact per arm (which article the node conses,
; if any), the rows side is the indexed rows after each transition (the
; exported fn-sn-indexed-rows-of-* facts), and the two meet on the keys.

; -----------------------------------------------------------------------------
; The row kinds are disjoint (local in the base book and in the invariants
; book; copied, as fn-sni-*-is-not-a-row are).

(local
 (defthm fn-snc-an-article-record-is-no-other-store-event
   (implies (fn-held-p record)
            (and (not (fn-store-retention-event-p record))
                 (not (fn-stxe-p record))
                 (not (fn-stxk-p record))
                 (not (fn-hstxa-p record))
                 (not (fn-th-topic-eventp record))
                 (not (fn-cpe-eventp record))))
   :hints (("Goal"
            :in-theory (e/d ((:d fn-held-p) (:d fn-held-shapep)
                             (:d fn-record-uint64p)
                             (:d fn-store-retention-event-p)
                             (:d fn-stxe-p) (:d fn-stxe-shapep)
                             (:d fn-stxk-p) (:d fn-stxk-shapep)
                             (:d fn-hstxa-p)
                             (:d fn-cpe-eventp)
                             (:d fn-th-topic-eventp)
                             (:d fn-th-local-admin-eventp))
                            ((:d fn-stxe-bounded-octetsp)
                             (:d fn-record-uint32p) (:d fn-record-msgidp)
                             (:d fn-record-payloadp)
                             (:d fn-record-groups-validp)
                             (:d fn-record-metadata-bytes-p)
                             (:d fn-record-stampp)
                             (:d fn-hf-p) (:d fn-hc-p)))))))

(local
 (defthm fn-snc-composite-kind-disjoint
   (implies (fn-hstxa-p record)
            (and (not (fn-store-retention-event-p record))
                 (not (fn-stxe-p record))
                 (not (fn-stxk-p record))
                 (not (fn-held-p record))
                 (not (fn-cpe-eventp record))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-stxe-p fn-stxe-shapep fn-record-uint32p
                             fn-stxk-p fn-stxk-shapep
                             fn-store-retention-event-p fn-cpe-eventp)
                            (fn-stxe-bounded-octetsp fn-record-msgidp
                             fn-record-metadata-bytes-p))))))

; The contrapositives the row walk needs, one per kind.
(local (defthm fn-snc-retention-is-not-a-row
  (implies (fn-store-retention-event-p x)
           (and (not (fn-held-p x)) (not (fn-hstxa-p x))))
  :hints (("Goal" :use ((:instance fn-snc-an-article-record-is-no-other-store-event (record x))
                        (:instance fn-snc-composite-kind-disjoint (record x)))
           :in-theory (disable fn-snc-an-article-record-is-no-other-store-event
                               fn-snc-composite-kind-disjoint)))))
(local (defthm fn-snc-stxe-is-not-a-row
  (implies (fn-stxe-p x) (and (not (fn-held-p x)) (not (fn-hstxa-p x))))
  :hints (("Goal" :use ((:instance fn-snc-an-article-record-is-no-other-store-event (record x))
                        (:instance fn-snc-composite-kind-disjoint (record x)))
           :in-theory (disable fn-snc-an-article-record-is-no-other-store-event
                               fn-snc-composite-kind-disjoint)))))
(local (defthm fn-snc-stxk-is-not-a-row
  (implies (fn-stxk-p x) (and (not (fn-held-p x)) (not (fn-hstxa-p x))))
  :hints (("Goal" :use ((:instance fn-snc-an-article-record-is-no-other-store-event (record x))
                        (:instance fn-snc-composite-kind-disjoint (record x)))
           :in-theory (disable fn-snc-an-article-record-is-no-other-store-event
                               fn-snc-composite-kind-disjoint)))))
(local (defthm fn-snc-cpe-is-not-a-row
  (implies (fn-cpe-eventp x) (and (not (fn-held-p x)) (not (fn-hstxa-p x))))
  :hints (("Goal" :use ((:instance fn-snc-an-article-record-is-no-other-store-event (record x))
                        (:instance fn-snc-composite-kind-disjoint (record x)))
           :in-theory (disable fn-snc-an-article-record-is-no-other-store-event
                               fn-snc-composite-kind-disjoint)))))
(local (defthm fn-snc-topic-is-not-held
  (implies (fn-th-topic-eventp x) (not (fn-held-p x)))
  :hints (("Goal" :use ((:instance fn-snc-an-article-record-is-no-other-store-event (record x)))
           :in-theory (disable fn-snc-an-article-record-is-no-other-store-event)))))
(local (defthm fn-snc-hstxa-is-not-held
  (implies (fn-hstxa-p x) (not (fn-held-p x)))
  :hints (("Goal" :use ((:instance fn-snc-composite-kind-disjoint (record x)))
           :in-theory (disable fn-snc-composite-kind-disjoint)))))

; -----------------------------------------------------------------------------
; The keys of a history that grew by one row, and of one split at its last

(local (defthm fn-snc-keys-true-listp
  (true-listp (fn-snc-row-keys-newest-first rows))))

(local (defthm fn-snc-append-nil
  (implies (true-listp x) (equal (append x nil) x))))

(local (defthm fn-snc-append-assoc
  (equal (append (append a b) c) (append a (append b c)))))

(local (defthm fn-snc-keys-of-append-one
  (equal (fn-snc-row-keys-newest-first (append rows (list r)))
         (cond ((fn-held-p r)
                (cons (fn-snc-row-key r) (fn-snc-row-keys-newest-first rows)))
               ((fn-hstxa-p r)
                (cons (fn-snc-row-key (fn-hstxa-held r)) (fn-snc-row-keys-newest-first rows)))
               (t (fn-snc-row-keys-newest-first rows))))
  :hints (("Goal" :in-theory (disable fn-held-p fn-hstxa-p fn-snc-row-key fn-hstxa-held)))))

(local (defthm fn-snc-rows-split-at-last
  (implies (and (true-listp records) (consp records))
           (equal (append (fn-sn-all-but-last records) (list (car (last records))))
                  records))
  :hints (("Goal" :in-theory (enable fn-sn-all-but-last)))))

(local (defthm fn-snc-keys-at-last
  (implies (and (true-listp records) (consp records))
           (equal (fn-snc-row-keys-newest-first records)
                  (let ((r (car (last records)))
                        (rest (fn-snc-row-keys-newest-first (fn-sn-all-but-last records))))
                    (cond ((fn-held-p r) (cons (fn-snc-row-key r) rest))
                          ((fn-hstxa-p r) (cons (fn-snc-row-key (fn-hstxa-held r)) rest))
                          (t rest)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-snc-keys-of-append-one
                                   (rows (fn-sn-all-but-last records))
                                   (r (car (last records)))))
           :in-theory (disable fn-snc-keys-of-append-one fn-held-p fn-hstxa-p
                               fn-snc-row-key fn-hstxa-held fn-sn-all-but-last
                               fn-snc-row-keys-newest-first)))))

(local (defthm fn-snc-records-true-listp
  (implies (fn-sf-statep files) (true-listp (fn-sf-records files)))
  :hints (("Goal" :in-theory (enable fn-sf-statep)))))

(local (defthm fn-snc-statep-node
  (implies (fn-sn-statep s) (fn-node-statep (fn-sn-node s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep))))))

; -----------------------------------------------------------------------------
; The store side: what each node step does to the articles

(local (defthm fn-snc-articles-of-advance-txid
  (equal (fn-state-articles (fn-node-acceptance (fn-replay-advance-txid node txid)))
         (fn-state-articles (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid)))))

(local (defthm fn-snc-store-of-advance-txid
  (equal (fn-stx-store (fn-replay-advance-txid node txid))
         (fn-stx-store node))
  :hints (("Goal" :in-theory (enable fn-stx-store)))))

; A retention completion keeps the articles (the node advances and its
; retention changes).
(local (defthm fn-snc-retention-event-keeps-the-store
  (implies (consp (fn-replay-apply-retention-event node e))
           (equal (fn-stx-store (fn-replay-apply-retention-event node e))
                  (fn-stx-store node)))
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-retention-event
                                   fn-replay-complete-retention
                                   fn-replay-node-with-retention fn-stx-store)
                                  (fn-replay-advance-txid fn-node-statep
                                   fn-retain-admissiblep fn-retain-admit
                                   fn-retain-release fn-retain-find-id
                                   fn-retain-matching-releasep
                                   fn-store-retention-event-p))))))

; The arms that carry no article keep the store
; (acceptance-payload-ref.lisp fn-apr-other-arms-keep-articles).
(local (defthm fn-snc-other-arms-keep-the-store
  (implies (and (or (fn-store-retention-event-p e) (fn-stxe-p e) (fn-stxk-p e)
                    (fn-cpe-eventp e) (fn-th-topic-eventp e))
                (consp (fn-replay-apply-record node e)))
           (equal (fn-stx-store (fn-replay-apply-record node e))
                  (fn-stx-store node)))
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-record
                                   fn-replay-apply-identity-neutral)
                                  (fn-stx-store fn-replay-advance-txid fn-node-statep
                                   fn-replay-apply-retention-event
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p
                                   fn-cpe-eventp fn-th-topic-eventp fn-hstxa-p fn-held-p))))))

; What the arm's own tests give (acceptance-payload-ref.lisp's locals): an
; unstaged node has no pending, through the advance; the prepare stages its
; arguments; the durable completion conses the pending.
(local
 (defthm fn-snc-idle-node-has-no-pending
   (implies (and (fn-node-statep node) (not (fn-node-stage node)))
            (not (fn-state-pending (fn-node-acceptance node))))
   :hints (("Goal" :in-theory (enable fn-node-statep)))))

(local
 (defthm fn-snc-idle-advance-has-no-pending
   (implies (and (fn-node-statep node) (not (fn-node-stage node)))
            (not (fn-state-pending
                  (fn-node-acceptance (fn-replay-advance-txid node x)))))
   :hints (("Goal" :in-theory (enable fn-replay-advance-txid)))))

(local
 (defthm fn-snc-prepare-stages-its-arguments
   (implies (and (fn-statep s)
                 (not (consp (fn-state-pending s)))
                 (consp (fn-state-pending (fn-accept-prepare s g m p gr st))))
            (let ((prep (fn-accept-prepare s g m p gr st)))
              (and (equal (fn-pending-msgid (fn-state-pending prep)) m)
                   (equal (fn-pending-payload (fn-state-pending prep)) p)
                   (equal (fn-state-articles prep) (fn-state-articles s))
                   (not (fn-state-fenced prep)))))
   :hints (("Goal" :in-theory (e/d (fn-accept-prepare) (fn-statep))))))

(local
 (defthm fn-snc-durable-complete-conses-the-pending
   (implies (and (fn-statep s) (not (fn-state-fenced s))
                 (fn-pending-matchesp (fn-state-pending s) txid gen))
            (equal (fn-state-articles (fn-accept-complete s txid gen :durable))
                   (cons (fn-article-from-pending (fn-state-pending s))
                         (fn-state-articles s))))
   :hints (("Goal" :in-theory (e/d (fn-accept-complete fn-install-pending)
                                   (fn-statep fn-article-from-pending))))))

(local
 (defthm fn-snc-node-acceptance-is-state
   (implies (fn-node-statep node) (fn-statep (fn-node-acceptance node)))
   :hints (("Goal" :in-theory (enable fn-node-statep)))))

; The article arm conses exactly its record's article
; (acceptance-payload-ref.lisp fn-apr-article-arm-installs-the-record-payload;
; the stage test is the arm's own first test, so it is not assumed here).
(local (defthm fn-snc-article-arm-installs-the-record
  (implies (and (fn-node-statep node)
                (not (fn-store-retention-event-p e)) (not (fn-stxe-p e))
                (not (fn-stxk-p e)) (not (fn-cpe-eventp e))
                (not (fn-th-topic-eventp e))
                (consp (fn-replay-apply-record node e)))
           (let ((art (if (fn-hstxa-p e) (fn-hstxa-held e) e))
                 (after (fn-stx-store (fn-replay-apply-record node e))))
             (and (fn-held-p art)
                  (consp after)
                  (equal (fn-article-msgid (car after)) (fn-record-msgid art))
                  (equal (fn-article-payload (car after)) (fn-record-payload art))
                  (equal (cdr after) (fn-stx-store node)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-node-prepare-preserves-state
                            (s (fn-replay-advance-txid node (fn-store-event-txid e)))
                            (generation (fn-record-generation (if (fn-hstxa-p e) (fn-hstxa-held e) e)))
                            (msgid (fn-record-msgid (if (fn-hstxa-p e) (fn-hstxa-held e) e)))
                            (payload (fn-record-payload (if (fn-hstxa-p e) (fn-hstxa-held e) e)))
                            (groups (fn-record-groups (if (fn-hstxa-p e) (fn-hstxa-held e) e)))
                            (obligation-id (fn-record-obligation-id (if (fn-hstxa-p e) (fn-hstxa-held e) e)))
                            (subject (fn-record-content-subject (if (fn-hstxa-p e) (fn-hstxa-held e) e)))
                            (evidence (fn-record-release-evidence (if (fn-hstxa-p e) (fn-hstxa-held e) e)))
                            (charge (fn-record-charge (if (fn-hstxa-p e) (fn-hstxa-held e) e)))
                            (stamp (fn-record-stamp (if (fn-hstxa-p e) (fn-hstxa-held e) e)))))
           :in-theory (e/d (fn-replay-apply-record fn-replay-composite-held
                            fn-node-complete fn-node-prepare fn-stx-store
                            fn-node-pending-matchesp fn-article-from-pending)
                           (fn-statep fn-node-statep fn-record-shape-vocabulary
                            fn-record-record-vocabulary fn-accept-prepare
                            fn-accept-complete fn-node-prepare-preserves-state
                            fn-replay-composite-record fn-replay-advance-txid
                            fn-store-retention-event-p fn-stxe-p fn-stxk-p
                            fn-cpe-eventp fn-th-topic-eventp fn-hstxa-p fn-held-p
                            fn-hstxa-held))))))

; The durable completion of the node's own pending article conses exactly
; that article: the finish's article arm, after a prepare.
(local (defthm fn-snc-durable-completion-installs-the-pending
  (implies (and (fn-node-statep node)
                (fn-node-pending-matchesp node txid generation))
           (equal (fn-stx-store (fn-node-complete node txid generation :durable))
                  (cons (fn-article-from-pending
                         (fn-state-pending (fn-node-acceptance node)))
                        (fn-stx-store node))))
  :hints (("Goal" :in-theory (e/d (fn-stx-store fn-node-complete fn-accept-complete
                                   fn-install-pending fn-node-pending-matchesp
                                   fn-pending-matchesp)
                                  (fn-statep fn-node-statep))))))

(local (defthm fn-snc-key-of-the-pending
  (equal (cons (fn-article-msgid (fn-article-from-pending p))
               (fn-article-payload (fn-article-from-pending p)))
         (cons (fn-pending-msgid p) (fn-pending-payload p)))
  :hints (("Goal" :in-theory (enable fn-article-from-pending)))))

; What fn-sn-record-bindsp says about the pending, as rewrite rules on the
; node (the theorem in the base book is :rule-classes nil).
(local (defthm fn-snc-binds-names-the-pending
  (implies (fn-sn-record-bindsp node record)
           (and (fn-held-p record)
                (fn-node-pending-matchesp node (fn-record-txid record)
                                          (fn-record-generation record))
                (equal (fn-pending-msgid (fn-state-pending (fn-node-acceptance node)))
                       (fn-record-msgid record))
                (equal (fn-pending-payload (fn-state-pending (fn-node-acceptance node)))
                       (fn-record-payload record))))
  :hints (("Goal" :use ((:instance fn-sn-record-binds-pending-fields))
           :in-theory (e/d (fn-sn-record-bindsp)
                           (fn-sn-pending-record fn-node-pending-matchesp fn-held-p
                            fn-held-wire fn-node-statep))))))

; -----------------------------------------------------------------------------
; Prepare and the I/O steps: store and rows unchanged

(defthm fn-snc-prepare-preserves-correspondp
  (implies (and (fn-sn-statep s) (fn-snc-correspondp s))
           (fn-snc-correspondp (fn-sn-prepare s record)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare fn-snc-correspondp fn-sn-indexed-rows
                                   fn-sn-update fn-sn-make-v6 fn-sn-node fn-sn-files)
                                  (fn-sn-statep fn-sf-statep fn-node-statep
                                   fn-sn-prepare-node fn-sf-prepare-record
                                   fn-sn-record-bindsp fn-cpe-projection-step
                                   fn-sn-indexed-rows-of fn-stx-store
                                   fn-snc-article-keys fn-snc-row-keys-newest-first
                                   fn-held-p fn-hc-generation fn-held-context
                                   fn-sn-keyring-generation fn-sn-consumer
                                   fn-sn-identity-next fn-node-stage))
           :use ((:instance fn-snc-statep-node) (:instance fn-snc-statep-files)))))

(defthm fn-snc-io-preserves-correspondp
  (implies (and (fn-sn-statep s) (fn-snc-correspondp s))
           (fn-snc-correspondp (fn-sn-io s operation result)))
  :hints (("Goal" :in-theory (e/d (fn-sn-io fn-snc-correspondp fn-sn-indexed-rows
                                   fn-sn-update fn-sn-make-v6 fn-sn-node fn-sn-files)
                                  (fn-sn-statep fn-sf-statep fn-node-statep
                                   fn-sn-file-step fn-sn-indexed-rows-of fn-stx-store
                                   fn-snc-article-keys fn-snc-row-keys-newest-first))
           :use ((:instance fn-snc-statep-files)))))

; -----------------------------------------------------------------------------
; The finish: the one transition that adds an article to the served node

(local (defthm fn-snc-enabled-is-completing
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sf-phase (fn-sn-files s)) :completing))
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp fn-sn-completion-core-enabledp)
                                  (fn-sn-statep fn-sn-completion-record
                                   fn-replay-apply-record fn-replay-apply-retention-event
                                   fn-replay-identity-step fn-sn-identity-context
                                   fn-sn-record-bindsp fn-cpe-projection-step fn-th-prefix-step
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp))))))

; What the gate says about the arm it enables: the node accepts the record
; (the arms that carry no article), or the record binds the pending.
(local (defthm fn-snc-enabled-facts
  (implies (fn-sn-completion-enabledp s)
           (let ((r (fn-sn-completion-record s))
                 (node (fn-sn-node s)))
             (and (fn-sn-statep s)
                  (implies (fn-store-retention-event-p r)
                           (consp (fn-replay-apply-retention-event node r)))
                  (implies (and (not (fn-store-retention-event-p r))
                                (or (fn-stxe-p r) (fn-stxk-p r) (fn-hstxa-p r)
                                    (fn-cpe-eventp r) (fn-th-topic-eventp r)))
                           (consp (fn-replay-apply-record node r)))
                  (implies (and (not (fn-store-retention-event-p r))
                                (not (fn-stxe-p r)) (not (fn-stxk-p r)) (not (fn-hstxa-p r))
                                (not (fn-cpe-eventp r)) (not (fn-th-topic-eventp r)))
                           (fn-sn-record-bindsp node r)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp fn-sn-completion-core-enabledp)
                                  (fn-sn-statep fn-sn-completion-record
                                   fn-replay-apply-record fn-replay-apply-retention-event
                                   fn-replay-identity-step fn-sn-identity-context
                                   fn-sn-record-bindsp fn-cpe-projection-step fn-th-prefix-step
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp))))))

; The completion of the files names the completion record's pair.
(local (defthm fn-snc-find-record-pair
  (implies (fn-sn-find-record pair records)
           (equal (fn-sf-record-pair (fn-sn-find-record pair records)) pair))
  :hints (("Goal" :in-theory (enable fn-sn-find-record)))))

(local (defthm fn-snc-completion-pair
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sf-completion (fn-sn-files s))
                  (cons (fn-store-event-sequence (fn-sn-completion-record s))
                        (fn-store-event-txid (fn-sn-completion-record s)))))
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp fn-sn-completion-core-enabledp
                                   fn-sn-completion-record)
                                  (fn-sn-statep fn-replay-apply-record
                                   fn-replay-apply-retention-event fn-replay-identity-step
                                   fn-sn-identity-context fn-sn-record-bindsp
                                   fn-cpe-projection-step fn-th-prefix-step
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp fn-sn-find-record))
           :use ((:instance fn-snc-find-record-pair
                            (pair (fn-sf-completion (fn-sn-files s)))
                            (records (fn-sf-records (fn-sn-files s)))))
           :expand ((fn-sf-record-pair (fn-sn-find-record (fn-sf-completion (fn-sn-files s))
                                                          (fn-sf-records (fn-sn-files s)))))))))

; The completion record is the last row (the invariants book's local chain).
(local (defthm fn-snc-last-sequence-at-least
  (implies (and (fn-sf-record-listp records sequence lower frontier) (consp records))
           (and (natp (fn-store-event-sequence (car (last records))))
                (<= sequence (fn-store-event-sequence (car (last records))))))
  :hints (("Goal" :induct (fn-sf-record-listp records sequence lower frontier)
           :in-theory (enable fn-sf-record-listp)))))

(local (defthm fn-snc-last-sequence-at-least-linear
  (implies (and (fn-sf-record-listp records sequence lower frontier) (consp records))
           (<= sequence (fn-store-event-sequence (car (last records)))))
  :rule-classes :linear
  :hints (("Goal" :use fn-snc-last-sequence-at-least))))

(local (defthm fn-snc-cdr-last-sequence-above
  (implies (and (fn-sf-record-listp records sequence lower frontier)
                (consp records) (consp (cdr records)))
           (< (fn-store-event-sequence (car records))
              (fn-store-event-sequence (car (last records)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :expand ((fn-sf-record-listp records sequence lower frontier))
           :use ((:instance fn-snc-last-sequence-at-least
                            (records (cdr records)) (sequence (1+ sequence))
                            (lower (1+ (fn-store-event-txid (car records))))))
           :in-theory (disable fn-snc-last-sequence-at-least)))))

(local (defthm fn-snc-find-record-of-last-pair
  (implies (and (fn-sf-record-listp records sequence lower frontier) (consp records))
           (equal (fn-sn-find-record (fn-sf-record-pair (car (last records))) records)
                  (car (last records))))
  :hints (("Goal" :induct (fn-sf-record-listp records sequence lower frontier)
           :in-theory (e/d (fn-sf-record-listp fn-sn-find-record fn-sf-record-pair)
                           (fn-store-event-p fn-snc-last-sequence-at-least))))))

; Oriented from the last row to the completion record, so the keys of the
; split history meet the record the arm facts are stated over.
(local (defthm fn-snc-last-row-is-the-completion-record
  (implies (and (fn-sn-statep s)
                (fn-sn-completion-is-last-p (fn-sn-files s))
                (equal (fn-sf-phase (fn-sn-files s)) :completing))
           (equal (car (last (fn-sf-records (fn-sn-files s))))
                  (fn-sn-completion-record s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-record fn-sn-completion-is-last-p
                                   fn-sn-statep fn-sf-statep)
                                  (fn-sf-phase-shapep fn-sf-success-listp fn-node-statep
                                   fn-sn-find-record fn-sf-record-pair))
           :use ((:instance fn-snc-find-record-of-last-pair
                            (records (fn-sf-records (fn-sn-files s)))
                            (sequence 0) (lower 0)
                            (frontier (fn-sf-frontier (fn-sn-files s)))))))))

(local (defthm fn-snc-completing-has-a-row
  (implies (and (fn-sn-completion-is-last-p files)
                (equal (fn-sf-phase files) :completing))
           (consp (fn-sf-records files)))
  :hints (("Goal" :in-theory (enable fn-sn-completion-is-last-p)))))

; The node and the files of an enabled finish, per arm, with the arms'
; steps closed (store-node-invariants' fn-sn-finish-*-arm-* facts, in one).
(local (defthm fn-snc-finish-node-and-files
  (implies (fn-sn-completion-enabledp s)
           (let ((r (fn-sn-completion-record s)))
             (and (equal (fn-sn-node (fn-sn-finish s))
                         (cond ((fn-store-retention-event-p r)
                                (fn-replay-apply-retention-event (fn-sn-node s) r))
                               ((or (fn-stxe-p r) (fn-stxk-p r) (fn-hstxa-p r)
                                    (fn-cpe-eventp r) (fn-th-topic-eventp r))
                                (fn-replay-apply-record (fn-sn-node s) r))
                               (t (fn-node-complete (fn-sn-node s) (fn-record-txid r)
                                                    (fn-record-generation r) :durable))))
                  (equal (fn-sn-files (fn-sn-finish s))
                         (fn-sf-emit-success
                          (fn-sf-core-completion (fn-sn-files s)
                                                 (fn-store-event-sequence r)
                                                 (fn-store-event-txid r))
                          (fn-store-event-sequence r) (fn-store-event-txid r))))))
  :hints (("Goal" :in-theory (e/d (fn-sn-finish fn-sn-finish-identity
                                   fn-sn-advance-identity-next fn-sn-update-indexed
                                   fn-sn-update-accepted fn-sn-with-topic fn-sn-with-consumer
                                   fn-sn-make-v6 fn-sn-node fn-sn-files)
                                  (fn-sn-completion-enabledp fn-sn-statep
                                   fn-sn-completion-record
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp fn-held-p
                                   fn-replay-apply-record fn-replay-apply-retention-event
                                   fn-replay-identity-step fn-sn-identity-context
                                   fn-sf-core-completion fn-sf-emit-success
                                   fn-node-complete fn-stx-index-add fn-sn-accepted-delta
                                   fn-sn-composite-delta fn-cpe-projection-step
                                   fn-th-prefix-step fn-cp-nth fn-th-at
                                   fn-hc-verdict fn-held-context fn-replay-verdict-pairs
                                   fn-stxk-context-verdicts fn-stxk-context-snapshots
                                   fn-stxk-context-next
                                   fn-record-shape-vocabulary fn-record-record-vocabulary))))))

; The rows of an enabled finish: before, all but the last; after, all.
(local (defthm fn-snc-finish-rows
  (implies (and (fn-sn-statep s)
                (fn-sn-completion-is-last-p (fn-sn-files s))
                (fn-sn-completion-enabledp s))
           (and (equal (fn-sn-indexed-rows (fn-sn-finish s))
                       (fn-sf-records (fn-sn-files s)))
                (equal (fn-sn-indexed-rows s)
                       (fn-sn-all-but-last (fn-sf-records (fn-sn-files s))))))
  :hints (("Goal" :in-theory (e/d (fn-sn-indexed-rows fn-sn-indexed-rows-of)
                                  (fn-sn-finish fn-sn-completion-enabledp fn-sn-statep
                                   fn-sf-statep fn-sn-completion-record
                                   fn-sf-core-completion fn-sf-emit-success
                                   fn-sn-completion-is-last-p fn-sn-all-but-last
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p
                                   fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp))
           :use ((:instance fn-snc-statep-files)
                 (:instance fn-sn-indexed-rows-of-completion (files (fn-sn-files s))
                            (sequence (fn-store-event-sequence (fn-sn-completion-record s)))
                            (txid (fn-store-event-txid (fn-sn-completion-record s)))))))))

; The keys of the whole history are the completion record's key, if it is a
; row, on the keys of all but the last.
(local (defthm fn-snc-finish-keys
  (implies (and (fn-sn-statep s)
                (fn-sn-completion-is-last-p (fn-sn-files s))
                (fn-sn-completion-enabledp s))
           (equal (fn-snc-row-keys-newest-first (fn-sf-records (fn-sn-files s)))
                  (let ((r (fn-sn-completion-record s))
                        (rest (fn-snc-row-keys-newest-first
                               (fn-sn-all-but-last (fn-sf-records (fn-sn-files s))))))
                    (cond ((fn-held-p r) (cons (fn-snc-row-key r) rest))
                          ((fn-hstxa-p r) (cons (fn-snc-row-key (fn-hstxa-held r)) rest))
                          (t rest)))))
  :hints (("Goal" :use ((:instance fn-snc-keys-at-last (records (fn-sf-records (fn-sn-files s))))
                        (:instance fn-snc-statep-files))
           :in-theory (e/d () (fn-sn-finish fn-sn-completion-enabledp fn-sn-statep
                               fn-sf-statep fn-sn-completion-record fn-sn-all-but-last
                               fn-snc-row-keys-newest-first fn-snc-row-key fn-hstxa-held
                               fn-held-p fn-hstxa-p fn-sn-completion-is-last-p))))))

(defthm fn-snc-finish-preserves-correspondp
  (implies (and (fn-sn-statep s)
                (fn-sn-completion-is-last-p (fn-sn-files s))
                (fn-snc-correspondp s))
           (fn-snc-correspondp (fn-sn-finish s)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sn-finish-disabled-is-no-op)
                 (:instance fn-snc-enabled-facts))
           :cases ((not (fn-sn-completion-enabledp s))
                   (and (fn-sn-completion-enabledp s)
                        (fn-store-retention-event-p (fn-sn-completion-record s)))
                   (and (fn-sn-completion-enabledp s)
                        (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                        (fn-hstxa-p (fn-sn-completion-record s)))
                   (and (fn-sn-completion-enabledp s)
                        (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                        (not (fn-hstxa-p (fn-sn-completion-record s)))
                        (or (fn-stxe-p (fn-sn-completion-record s))
                            (fn-stxk-p (fn-sn-completion-record s))
                            (fn-cpe-eventp (fn-sn-completion-record s))
                            (fn-th-topic-eventp (fn-sn-completion-record s))))
                   (and (fn-sn-completion-enabledp s)
                        (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                        (not (fn-hstxa-p (fn-sn-completion-record s)))
                        (not (fn-stxe-p (fn-sn-completion-record s)))
                        (not (fn-stxk-p (fn-sn-completion-record s)))
                        (not (fn-cpe-eventp (fn-sn-completion-record s)))
                        (not (fn-th-topic-eventp (fn-sn-completion-record s)))))
           :in-theory (e/d (fn-snc-correspondp fn-snc-row-key)
                           (fn-sn-finish fn-sn-completion-enabledp fn-sn-statep fn-sf-statep
                            fn-sn-completion-record fn-sn-completion-is-last-p
                            fn-sn-indexed-rows fn-sn-indexed-rows-of fn-sn-all-but-last
                            fn-snc-row-keys-newest-first fn-hstxa-held
                            fn-stx-store fn-node-complete fn-replay-apply-record
                            fn-replay-apply-retention-event fn-sn-record-bindsp
                            fn-node-pending-matchesp fn-node-statep
                            fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-hstxa-p
                            fn-cpe-eventp fn-th-topic-eventp fn-held-p
                            fn-article-from-pending fn-sf-core-completion fn-sf-emit-success)))))

; -----------------------------------------------------------------------------
; Recovery: the replayed node's articles are the history's article rows

(local (defthm fn-snc-fault-is-not-ok
  (not (fn-replay-okp (fn-replay-fault node sequence reason)))
  :hints (("Goal" :in-theory (enable fn-replay-okp)))))

(local (defthm fn-snc-apply-record-keys
  (implies (and (fn-node-statep node)
                (fn-store-event-p e)
                (fn-node-statep (fn-replay-apply-record node e)))
           (equal (fn-snc-article-keys (fn-stx-store (fn-replay-apply-record node e)))
                  (cond ((fn-held-p e)
                         (cons (fn-snc-row-key e) (fn-snc-article-keys (fn-stx-store node))))
                        ((fn-hstxa-p e)
                         (cons (fn-snc-row-key (fn-hstxa-held e))
                               (fn-snc-article-keys (fn-stx-store node))))
                        (t (fn-snc-article-keys (fn-stx-store node))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-replay-apply-record-statep-iff-consp (record e))
                 (:instance fn-snc-article-arm-installs-the-record))
           :in-theory (e/d ()
                           (fn-replay-apply-record fn-node-statep fn-stx-store
                            fn-snc-article-arm-installs-the-record
                            fn-store-retention-event-p fn-stxe-p fn-stxk-p
                            fn-cpe-eventp fn-th-topic-eventp fn-hstxa-p fn-held-p
                            fn-hstxa-held fn-store-event-p))))))

(local (defun fn-snc-loop-induct (node records sequence)
  (declare (xargs :measure (len records)))
  (if (and (fn-node-statep node)
           (consp records)
           (fn-store-event-p (car records))
           (equal (fn-store-event-sequence (car records)) sequence)
           (fn-node-statep (fn-replay-apply-record node (car records))))
      (fn-snc-loop-induct (fn-replay-apply-record node (car records))
                          (cdr records) (1+ sequence))
    (list node records sequence))))

(local (defthm fn-snc-replay-loop-keys
  (implies (fn-replay-okp (fn-replay-loop node records sequence))
           (equal (fn-snc-article-keys
                   (fn-stx-store (fn-replay-result-node (fn-replay-loop node records sequence))))
                  (append (fn-snc-row-keys-newest-first records)
                          (fn-snc-article-keys (fn-stx-store node)))))
  :hints (("Goal" :induct (fn-snc-loop-induct node records sequence)
           :in-theory (e/d (fn-replay-loop)
                           (fn-snc-article-keys fn-stx-store fn-replay-apply-record
                            fn-node-statep fn-store-event-p fn-held-p fn-hstxa-p
                            fn-hstxa-held fn-snc-row-key fn-replay-okp))))))

(local (defthm fn-snc-article-keys-of-nil
  (equal (fn-snc-article-keys nil) nil)))

(local (defthm fn-snc-replay-node-keys
  (implies (consp (fn-sf-replay-node groups capacity records frontier))
           (equal (fn-snc-article-keys
                   (fn-stx-store (fn-sf-replay-node groups capacity records frontier)))
                  (fn-snc-row-keys-newest-first records)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-snc-replay-loop-keys
                            (node (fn-node-initial-state groups capacity)) (sequence 0)))
           :in-theory (e/d (fn-sf-replay-node fn-replay)
                           (fn-replay-loop fn-stx-store fn-replay-advance-txid
                            fn-replay-advance-okp fn-node-statep fn-snc-article-keys
                            fn-snc-row-keys-newest-first fn-node-initial-state
                            fn-replay-okp fn-replay-result-node))))))

(local (defthm fn-snc-recovering-means-recoverable
  (implies (and (fn-sf-statep files)
                (equal (fn-sf-phase files) :replaying)
                (equal (fn-sf-phase (fn-sf-recover files groups capacity)) :recovering))
           (consp (fn-sf-replay-node groups capacity
                                     (fn-sf-records (fn-sf-recover files groups capacity))
                                     (fn-sf-frontier (fn-sf-recover files groups capacity)))))
  :hints (("Goal" :in-theory (e/d (fn-sf-recover fn-sf-history-recoverablep)
                                  (fn-sf-statep fn-sf-replay-node fn-node-statep))))))

(local (defthm fn-snc-fault-files-facts
  (equal (fn-sn-indexed-rows-of (fn-sf-make :fault fr nil rs nil nil su 0)) nil)
  :hints (("Goal" :in-theory (enable fn-sn-indexed-rows-of)))))

(local (defthm fn-snc-replaying-has-no-indexed-rows
  (implies (equal (fn-sf-phase files) :replaying)
           (equal (fn-sn-indexed-rows-of files) nil))
  :hints (("Goal" :in-theory (enable fn-sn-indexed-rows-of)))))

(local (defthm fn-snc-row-keys-of-nil
  (equal (fn-snc-row-keys-newest-first nil) nil)))

; -by-recomputation, as fn-sn-recover-preserves-indexedp-by-recomputation:
; the node is the replay of the history, so its articles are the rows'.
(defthm fn-snc-recover-preserves-correspondp-by-recomputation
  (implies (and (fn-sn-statep s) (fn-snc-correspondp s))
           (fn-snc-correspondp (fn-sn-recover s)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-snc-statep-files)
                 (:instance fn-sn-indexed-rows-of-recover (files (fn-sn-files s))
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s)))
                 (:instance fn-snc-recovering-means-recoverable (files (fn-sn-files s))
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (e/d (fn-sn-recover fn-snc-correspondp fn-sn-indexed-rows
                            fn-sn-update fn-sn-update-replayed fn-sn-with-topic
                            fn-sn-with-consumer fn-sn-with-event-index
                            fn-sn-make-v6 fn-sn-node fn-sn-files)
                           (fn-sn-statep fn-sf-statep fn-node-statep fn-sf-recover
                            fn-sf-replay-node fn-replay-identity fn-cpe-projection-replay
                            fn-th-prefix-project fn-sn-index-of-rows fn-sn-indexed-rows-of
                            fn-stx-store fn-snc-article-keys fn-snc-row-keys-newest-first
                            fn-stxk-context-kind fn-th-at fn-cp-nth
                            fn-sn-completion-is-last-p fn-replay-verdict-pairs
                            fn-stxk-context-verdicts fn-stxk-context-snapshots
                            fn-stxk-context-next fn-sf-make fn-sn-groups fn-sn-capacity
                            fn-snc-recovering-means-recoverable)))))

; -----------------------------------------------------------------------------
; The keyring installation: the rows keep their Message-IDs and handles

(local (defthm fn-snc-keys-of-recontext
  (implies (not (equal (fn-sn-recontext-rows rows contexts generation) :mismatch))
           (equal (fn-snc-row-keys-newest-first
                   (fn-sn-recontext-rows rows contexts generation))
                  (fn-snc-row-keys-newest-first rows)))
  :hints (("Goal" :induct (fn-sn-recontext-rows rows contexts generation)
           :in-theory (e/d (fn-sn-recontext-rows fn-snc-row-key)
                           (fn-held-p fn-hstxa-p fn-hc-p fn-held-with-context
                            fn-hstxa-make fn-hstxa-held fn-hstxa-stxa fn-hc-generation))))))

(defthm fn-snc-set-keyring-preserves-correspondp
  (implies (and (fn-sn-statep s) (fn-snc-correspondp s))
           (fn-snc-correspondp (fn-sn-set-keyring s keyring contexts)))
  :hints (("Goal" :in-theory (e/d (fn-sn-set-keyring fn-snc-correspondp fn-sn-indexed-rows
                                   fn-sn-make-v6 fn-sn-node fn-sn-files fn-sn-indexed-rows-of)
                                  (fn-sn-statep fn-sf-statep fn-node-statep
                                   fn-sn-recontext-rows fn-sn-index-of-rows fn-stx-store
                                   fn-snc-article-keys fn-snc-row-keys-newest-first
                                   fn-prin-keyringp fn-sf-make fn-sn-keyring-generation)))))

; -----------------------------------------------------------------------------
; The two resolutions (books/store-node-resolution): store and rows unchanged

(local (defthm fn-snc-aborted-completion-keeps-the-store
  (equal (fn-stx-store (fn-node-complete node txid generation :aborted))
         (fn-stx-store node))
  :hints (("Goal" :in-theory (enable fn-stx-store fn-node-complete
                                     fn-accept-complete fn-clear-pending)))))

(local (defthm fn-snc-indexed-rows-of-refuse-reservation
  (implies (fn-sf-statep files)
           (equal (fn-sn-indexed-rows-of (fn-sf-refuse-reservation files txid))
                  (fn-sn-indexed-rows-of files)))
  :hints (("Goal" :in-theory (e/d (fn-sf-refuse-reservation fn-sn-indexed-rows-of)
                                  (fn-sf-statep))))))

(local (defthm fn-snc-indexed-rows-of-known-abort-files
  (implies (fn-sf-statep files)
           (equal (fn-sn-indexed-rows-of (fn-sn-known-abort-files files))
                  (fn-sn-indexed-rows-of files)))
  :hints (("Goal" :in-theory (e/d (fn-sn-known-abort-files fn-sn-known-abort-file-start
                                   fn-sf-record-file-result
                                   fn-sf-prepublish-abort fn-sf-abort-completion
                                   fn-sn-indexed-rows-of)
                                  (fn-sf-statep))))))

(defthm fn-snc-refuse-reservation-preserves-correspondp
  (implies (and (fn-sn-statep s) (fn-snc-correspondp s))
           (fn-snc-correspondp (fn-sn-refuse-reservation s txid)))
  :hints (("Goal" :in-theory (e/d (fn-sn-refuse-reservation fn-snc-correspondp fn-sn-indexed-rows
                                   fn-sn-update fn-sn-make-v6 fn-sn-node fn-sn-files)
                                  (fn-sn-refuse-reservation-enabledp fn-sn-statep fn-sf-statep
                                   fn-node-statep fn-sf-refuse-reservation fn-replay-advance-txid
                                   fn-sn-indexed-rows-of fn-stx-store
                                   fn-snc-article-keys fn-snc-row-keys-newest-first))
           :use ((:instance fn-snc-statep-files)))))

(defthm fn-snc-known-abort-preserves-correspondp
  (implies (and (fn-sn-statep s) (fn-snc-correspondp s))
           (fn-snc-correspondp (fn-sn-known-abort s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-known-abort fn-snc-correspondp fn-sn-indexed-rows
                                   fn-sn-update fn-sn-make-v6 fn-sn-node fn-sn-files)
                                  (fn-sn-known-abort-enabledp fn-sn-statep fn-sf-statep
                                   fn-node-statep fn-sn-known-abort-files fn-node-complete
                                   fn-replay-advance-txid fn-sn-record-bindsp fn-held-p
                                   fn-sn-indexed-rows-of fn-stx-store
                                   fn-snc-article-keys fn-snc-row-keys-newest-first))
           :use ((:instance fn-snc-statep-files)))))

; -----------------------------------------------------------------------------
; The sweep (books/store-sweep) returns the store as it was.  -by-definition,
; a corollary of fn-sn-sweep-staging-keeps-the-store; cited, not registered
; as a proof event.
(defthm fn-snc-sweep-staging-preserves-correspondp-by-definition
  (implies (fn-snc-correspondp s)
           (fn-snc-correspondp (cdr (fn-sn-sweep-staging s observed held))))
  :rule-classes nil
  :hints (("Goal" :use fn-sn-sweep-staging-keeps-the-store
           :in-theory (disable fn-sn-sweep-staging fn-snc-correspondp))))
