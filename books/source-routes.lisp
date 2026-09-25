; fn: one authored source keeps one identity through every route (D25, D32;
; the Fable mandate section 5.3).
;
; The duplicate-versus-conflict verdict the host calls on every route that
; stores a served or operator-injected article is fn-rcl-existing-action
; (books/store-reclaim.lisp), reached through fn-rclb-existing-action on
; the buffer path (fn-rclb-existing-action-is-rcl-existing-action): at
; host/owner-host.lisp fn-owner-existing-action, fn-owner-existing-action-
; buffer and fn-owner-prepare, and host/store-node-host.lisp
; fn-store-sn-existing-action and its prepare site.  Its held payload is
; either the injected article or, after `store reclaim', that article's
; tombstone (fn-rcl-tombstone-of).  books/poster-bytes-invariants.lisp
; proves the retry and conflict keystones over fn-pb-existing-action, the
; decision without tombstones; this book closes the two joins the corpus
; table showed without a theorem:
;
;   * the injected octets are never a tombstone, so the host's
;     tombstone-aware verdict is the D25 one on a live article;
;   * the tombstone keeps the authored-source identity: its source digest
;     is SHA-256 of the poster's exact source, and its agent is the
;     injecting one, so a retry after reclamation is still "already stored
;     here" and a changed authored byte is still a conflict (up to a
;     SHA-256 collision between the two sources, the stated limit).

(in-package "ACL2")
(include-book "poster-bytes-invariants")
(include-book "store-reclaim")

(local (in-theory (disable fn-inj-decide fn-inj-injectedp fn-inj-source-of
                           fn-inj-decision-octets fn-inj-decision-msgid
                           fn-pb-same-articlep fn-pb-path-agent fn-pb-subject
                           fn-find-article fn-sha256 fn-rcl-tombstone-of
                           fn-rcl-tomb-sourcep fn-rcl-tomb-agent
                           fn-rcl-tomb-source-digest fn-rcl-tomb-octets-digest)))

; -----------------------------------------------------------------------------
; An injected article is never a tombstone: it opens with "Path: " (recipe
; v2) or "Injection-" (recipe v3), and a tombstone opens with NUL.

(local
 (defthm fn-sr-car-of-inj-append
   (implies (consp a)
            (and (consp (fn-inj-append a b))
                 (equal (car (fn-inj-append a b)) (car a))))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-sr-a-prefix-opens-with-p
   (and (consp (fn-inj-prefix date msgid agent gid gdate))
        (equal (car (fn-inj-prefix date msgid agent gid gdate)) 80))
   :hints (("Goal" :in-theory (enable fn-inj-prefix fn-inj-path-line)))))

(encapsulate ()
 (local (defthm fn-sr-inj-append-of-nil
   (equal (fn-inj-append nil b) b)
   :hints (("Goal" :in-theory (enable fn-inj-append)))))
 (local (defthm fn-sr-first-octets-of-the-lines
   (and (consp (fn-inj-injection-date-line date))
        (equal (car (fn-inj-injection-date-line date)) 73)
        (consp (fn-inj-injection-info-line agent))
        (equal (car (fn-inj-injection-info-line agent)) 73)
        (consp (fn-inj-message-id-line msgid))
        (equal (car (fn-inj-message-id-line msgid)) 77)
        (consp (fn-inj-date-line date))
        (equal (car (fn-inj-date-line date)) 68))
   :hints (("Goal" :in-theory (enable fn-inj-injection-date-line
                                      fn-inj-injection-info-line
                                      fn-inj-message-id-line fn-inj-date-line
                                      fn-inj-append)))))
 (defthm fn-sr-a-block-opens-with-a-field-name
   (and (consp (fn-inj-block date msgid agent gid gdate))
        (not (equal (car (fn-inj-block date msgid agent gid gdate)) 0)))
   :hints (("Goal" :in-theory (e/d (fn-inj-block)
                                   (fn-inj-injection-date-line
                                    fn-inj-message-id-line fn-inj-date-line
                                    fn-inj-injection-info-line))))))


(encapsulate ()
(local
 (defthm fn-sr-a-tombstone-opens-with-nul
   (implies (and (consp x) (not (equal (car x) 0)))
            (not (fn-rcl-tombstonep x)))
   :hints (("Goal" :in-theory (enable fn-rcl-tombstonep fn-rcl-prefixp)))))
(local
(defthm fn-sr-an-injected-article-is-not-a-tombstone
  (implies (fn-inj-injectedp (fn-inj-decide source config obs))
           (not (fn-rcl-tombstonep
                 (fn-inj-decision-octets (fn-inj-decide source config obs)))))
  :hints (("Goal" :cases ((fn-inj-supplies-pathp source))
                  :use (fn-inj-injected-octets-are-the-block-and-the-source
                        fn-inj-injected-octets-are-the-block-and-the-prefixed-source)
                  :in-theory (disable fn-inj-prefix fn-inj-block fn-inj-splice
                                      fn-inj-supplies-pathp fn-rcl-tombstonep
                                      fn-article-parse fn-af-proto-article-check
                                      fn-article-result-article fn-inj-absentp
                                      fn-inj-nth fn-inj-date-octets fn-inj-instant-of
                                      fn-inj-path-offset fn-inj-path-insert)))))

; KEYSTONE (the two representations are disjoint).  No injection decision's
; octets are a tombstone: an injected article opens with "Path: " (recipe v2)
; or "Injection-" (recipe v3) and a refusal has no octets, while a tombstone
; opens with NUL.  So the host's tombstone-aware verdict
; (fn-rcl-existing-action) is the D25 one on every live injected article.
(defthm fn-sr-an-injection-is-not-a-tombstone
  (not (fn-rcl-tombstonep
        (fn-inj-decision-octets (fn-inj-decide source config obs))))
  :hints (("Goal" :cases ((fn-inj-injectedp (fn-inj-decide source config obs)))
                  :use (fn-sr-an-injected-article-is-not-a-tombstone
                        (:instance fn-inj-refusal-produces-no-octets (observation obs)))
                  :in-theory (disable fn-rcl-tombstonep)))
  :rule-classes nil))


; An injected article is at least its Path or Injection- line.
(defthm fn-sr-an-injection-is-a-cons
  (implies (fn-inj-injectedp (fn-inj-decide source config obs))
           (consp (fn-inj-decision-octets (fn-inj-decide source config obs))))
  :hints (("Goal" :cases ((fn-inj-supplies-pathp source))
                  :use (fn-inj-injected-octets-are-the-block-and-the-source
                        fn-inj-injected-octets-are-the-block-and-the-prefixed-source)
                  :in-theory (disable fn-inj-prefix fn-inj-block fn-inj-splice
                                      fn-inj-supplies-pathp fn-rcl-tombstonep
                                      fn-article-parse fn-af-proto-article-check
                                      fn-article-result-article fn-inj-absentp
                                      fn-inj-nth fn-inj-date-octets fn-inj-instant-of
                                      fn-inj-path-offset fn-inj-path-insert))))

; -----------------------------------------------------------------------------
; The host's verdict on a live held article.

; KEYSTONE (retry, the host's tombstone-aware verdict).  The held article is
; one source injected at clock A; the same source injected at clock B under
; the same Message-ID and groups is "already stored here".  The node-added
; fields (Path's injecting agent, Injection-Date, Injection-Info, a
; generated Date) never make the retry a conflict.
(defthm fn-sr-a-retry-is-already-stored
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
        (da (fn-inj-decide source config a))
        (db (fn-inj-decide source config b)))
    (implies (and (equal (fn-article-payload held) (fn-inj-decision-octets da))
                  (fn-inj-injectedp da)
                  (fn-inj-injectedp db)
                  (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                  (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                  (equal groups (fn-article-groups held)))
             (equal (fn-rcl-existing-action msgid (fn-inj-decision-octets db) groups s)
                    :duplicate)))
  :hints (("Goal" :cases ((fn-find-article
                            msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
                  :use ((:instance fn-sr-an-injection-is-a-cons (source source) (obs a))
                        (:instance fn-sr-an-injection-is-not-a-tombstone (obs a))
                        (:instance fn-pb-one-source-at-two-clocks-is-one-article
                                   (msgid (fn-record-string-octets msgid))))
                  :in-theory (e/d (fn-rcl-existing-action fn-rcl-same-articlep)
                                  (fn-rcl-tombstonep fn-article-groups))))
  :rule-classes nil)

; KEYSTONE (no over-normalization).  A different source under the held
; Message-ID -- one changed authored byte, an authored Date changed or
; removed, a changed signature line -- is a conflict, at every pair of
; clock readings and for any groups.
(defthm fn-sr-a-changed-source-is-a-conflict
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
        (da (fn-inj-decide source1 config a))
        (db (fn-inj-decide source2 config b)))
    (implies (and (equal (fn-article-payload held) (fn-inj-decision-octets da))
                  (fn-inj-injectedp da)
                  (fn-inj-injectedp db)
                  (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                  (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                  (not (equal source1 source2)))
             (equal (fn-rcl-existing-action msgid (fn-inj-decision-octets db) groups s)
                    :conflict)))
  :hints (("Goal" :cases ((fn-find-article
                            msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
                  :use ((:instance fn-sr-an-injection-is-a-cons (source source1) (obs a))
                        (:instance fn-sr-an-injection-is-not-a-tombstone
                                   (source source1) (obs a))
                        (:instance fn-pb-two-sources-are-two-articles
                                   (msgid (fn-record-string-octets msgid))))
                  :in-theory (e/d (fn-rcl-existing-action fn-rcl-same-articlep)
                                  (fn-rcl-tombstonep fn-article-groups))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The tombstone keeps the authored-source identity.

; KEYSTONE (tombstone).  Reclaiming an injected article writes a tombstone
; that names the poster's source: its source digest is SHA-256 of the exact
; source, its agent is the injecting one, and its octet digest is SHA-256 of
; the stored octets.  A digest is an identity only up to SHA-256 collision
; (about 2^128 work, the stated limit, not proved).
(defthm fn-sr-the-tombstone-keeps-the-source
  (let* ((d (fn-inj-decide source config obs))
         (tomb (fn-rcl-tombstone-of (fn-inj-decision-octets d)
                                    (fn-inj-decision-msgid d))))
    (implies (fn-inj-injectedp d)
             (and (fn-rcl-tombstonep tomb)
                  (fn-rcl-tomb-sourcep tomb)
                  (equal (fn-rcl-tomb-source-digest tomb) (fn-sha256 source))
                  (equal (fn-rcl-tomb-agent tomb) (fn-inj-config-agent config))
                  (equal (fn-rcl-tomb-octets-digest tomb)
                         (fn-sha256 (fn-inj-decision-octets d))))))
  :hints (("Goal" :use ((:instance fn-rcl-tombstone-of-fields
                                   (payload (fn-inj-decision-octets
                                             (fn-inj-decide source config obs)))
                                   (msgid (fn-inj-decision-msgid
                                           (fn-inj-decide source config obs))))
                        (:instance fn-pb-path-agent-of-an-injection)
                        (:instance fn-inj-source-of-inverts-the-injection
                                   (observation obs)))
                  :in-theory (e/d (fn-pb-subject) (fn-rcl-tombstonep)))))

; KEYSTONE (retry after reclamation).  The held payload is the tombstone of
; the source injected at A; the same source injected at B under the same
; Message-ID and groups is still "already stored here".
(defthm fn-sr-a-retry-after-reclaim-is-already-stored
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
        (da (fn-inj-decide source config a))
        (db (fn-inj-decide source config b)))
    (implies (and (equal (fn-article-payload held)
                         (fn-rcl-tombstone-of (fn-inj-decision-octets da)
                                              (fn-record-string-octets msgid)))
                  (fn-inj-injectedp da)
                  (fn-inj-injectedp db)
                  (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                  (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                  (equal groups (fn-article-groups held)))
             (equal (fn-rcl-existing-action msgid (fn-inj-decision-octets db) groups s)
                    :duplicate)))
  :hints (("Goal" :cases ((fn-find-article
                            msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
                  :use ((:instance fn-sr-the-tombstone-keeps-the-source (obs a))
                        (:instance fn-pb-path-agent-of-an-injection (obs b))
                        (:instance fn-inj-source-of-inverts-the-injection
                                   (observation b)))
                  :in-theory (e/d (fn-rcl-existing-action fn-rcl-same-articlep
                                   fn-rcl-same-as-tombstonep fn-pb-subject)
                                  (fn-rcl-tombstonep))))
  :rule-classes nil)

; KEYSTONE (conflict after reclamation).  A different source under the
; reclaimed Message-ID is a conflict, unless SHA-256 collides on the two
; sources (the stated limit).
(defthm fn-sr-a-changed-source-after-reclaim-is-a-conflict
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
        (da (fn-inj-decide source1 config a))
        (db (fn-inj-decide source2 config b)))
    (implies (and (equal (fn-article-payload held)
                         (fn-rcl-tombstone-of (fn-inj-decision-octets da)
                                              (fn-record-string-octets msgid)))
                  (fn-inj-injectedp da)
                  (fn-inj-injectedp db)
                  (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                  (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                  (not (equal source1 source2)))
             (or (equal (fn-rcl-existing-action msgid (fn-inj-decision-octets db)
                                                groups s)
                        :conflict)
                 (fn-rcl-collisionp source2 source1))))
  :hints (("Goal" :cases ((fn-find-article
                            msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
                  :use ((:instance fn-sr-the-tombstone-keeps-the-source
                                   (source source1) (obs a))
                        (:instance fn-pb-path-agent-of-an-injection
                                   (source source2) (obs b))
                        (:instance fn-inj-source-of-inverts-the-injection
                                   (source source2) (observation b)))
                  :in-theory (e/d (fn-rcl-existing-action fn-rcl-same-articlep
                                   fn-rcl-same-as-tombstonep fn-pb-subject
                                   fn-rcl-collisionp)
                                  (fn-rcl-tombstonep))))
  :rule-classes nil)
