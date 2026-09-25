; fn: content reclamation under D13 (STO-014, PRF-088).
;
; Three things live here, and nothing else.
;
; 1. The decision.  `fn-rcl-reclaimable' says, for one stored article,
;    whether the operator's retention rule (books/reclaim-rule) and every
;    holder permit removing its payload.  The holders are the active
;    references of specs/storage.md's lifetimes table: a reader's pin on the
;    article, a consumer cursor that has not acknowledged past it, an
;    outbound feed that has not delivered it to a live peer, and a BP
;    obligation that names it.  The executable test reads one floor per
;    consumer group; the keystone says it is exactly "no obligation in the
;    flattened obligation list names the article" plus the rule.
;
; 2. The tombstone (books/reclaim-tombstone).  `fn-rcl-tombstone-of'
;    builds the block a payload becomes: its digest, its D25 source digest
;    under its own agent, its length and that agent.
;
; 3. What reclamation keeps.  `fn-rcl-reclaim-state' is the acceptance
;    state after one article's payload became its tombstone.  The keystones
;    say every decision the lifetimes table lists reads the same afterwards:
;    the duplicate history (a reclaimed Message-ID is still accepted, so it
;    never resurrects), the group numbering, each article's group bindings
;    and stamp, and -- through `fn-pb-existing-action', which the host
;    calls -- the duplicate-versus-conflict verdict.  A held article is never
;    touched.
;
; The durable step is not here: `store reclaim' rewrites the article's
; transaction record with the tombstone as its payload, and the open
; replays it through the unchanged record path.  Acceptance never reads a
; stored payload (`fn-accept-prepare' compares Message-IDs only), which is
; why the replayed state is `fn-rcl-reclaim-state' of the state before
; (`fn-rcl-prepare-commutes-with-reclaim', below).
(in-package "ACL2")
(include-book "reclaim-rule")
(include-book "reclaim-tombstone")
(include-book "poster-bytes")
(include-book "sha256")

(defun fn-rcl-car (x) (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun fn-rcl-cdr (x) (declare (xargs :guard t)) (if (consp x) (cdr x) nil))
(defun fn-rcl-nth (n x)
  (declare (xargs :guard (natp n)))
  (if (consp x) (if (zp n) (car x) (fn-rcl-nth (1- n) (cdr x))) nil))

; -----------------------------------------------------------------------------
; Holders.
;
; pins     ((group . number) ...)          a reader holds that one article
; cursors  ((group . acknowledged) ...)    a consumer holds every article
;                                          numbered above what it acknowledged
; feeds    ((peer retiredp msgid ...) ...)  a live peer holds what it has
;                                          not been delivered
; bp       (msgid ...)                     an unresolved BP obligation

(defun fn-rcl-pairsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (consp (car xs))
           (stringp (car (car xs)))
           (natp (cdr (car xs)))
           (fn-rcl-pairsp (cdr xs)))
    (null xs)))

(defun fn-rcl-feedsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (consp (car xs))
           (consp (cdr (car xs)))
           (true-listp (cddr (car xs)))
           (fn-rcl-feedsp (cdr xs)))
    (null xs)))

(defun fn-rcl-holdersp (h)
  (declare (xargs :guard t))
  (and (true-listp h)
       (equal (len h) 4)
       (fn-rcl-pairsp (nth 0 h))
       (fn-rcl-pairsp (nth 1 h))
       (fn-rcl-feedsp (nth 2 h))
       (true-listp (nth 3 h))))

(defun fn-rcl-pins (h) (declare (xargs :guard t)) (and (true-listp h) (nth 0 h)))
(defun fn-rcl-cursors (h) (declare (xargs :guard t)) (and (true-listp h) (nth 1 h)))
(defun fn-rcl-feeds (h) (declare (xargs :guard t)) (and (true-listp h) (nth 2 h)))
(defun fn-rcl-bp (h) (declare (xargs :guard t)) (and (true-listp h) (nth 3 h)))

; The article's number in GROUP, or nil.
(defun fn-rcl-number (group memberships)
  (declare (xargs :guard t))
  (if (consp memberships)
      (if (and (consp (car memberships))
               (equal (car (car memberships)) group))
          (cdr (car memberships))
        (fn-rcl-number group (cdr memberships)))
    nil))

; -----------------------------------------------------------------------------
; The specification: the obligation list and what each obligation names.

(defun fn-rcl-pin-obligations (pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (cons (list :reader-pin (fn-rcl-car (car pins))
                  (fn-rcl-cdr (car pins)))
            (fn-rcl-pin-obligations (cdr pins)))
    nil))

(defun fn-rcl-cursor-obligations (cursors)
  (declare (xargs :guard t))
  (if (consp cursors)
      (cons (list :consumer-cursor (fn-rcl-car (car cursors))
                  (fn-rcl-cdr (car cursors)))
            (fn-rcl-cursor-obligations (cdr cursors)))
    nil))

(defun fn-rcl-feed-msgid-obligations (peer msgids)
  (declare (xargs :guard t))
  (if (consp msgids)
      (cons (list :feed peer (car msgids))
            (fn-rcl-feed-msgid-obligations peer (cdr msgids)))
    nil))

(defun fn-rcl-feed-obligations-list (feeds)
  (declare (xargs :guard t))
  (if (consp feeds)
      (append (let ((feed (car feeds)))
                (if (and (consp feed) (consp (cdr feed)) (not (cadr feed)))
                    (fn-rcl-feed-msgid-obligations (car feed) (cddr feed))
                  nil))
              (fn-rcl-feed-obligations-list (cdr feeds)))
    nil))

(defun fn-rcl-bp-obligations (msgids)
  (declare (xargs :guard t))
  (if (consp msgids)
      (cons (list :bp-obligation (car msgids))
            (fn-rcl-bp-obligations (cdr msgids)))
    nil))

; Every active reference the lifetimes table lists, one entry each.
(defun fn-rcl-obligations (h)
  (declare (xargs :guard t))
  (append (fn-rcl-pin-obligations (fn-rcl-pins h))
          (fn-rcl-cursor-obligations (fn-rcl-cursors h))
          (fn-rcl-feed-obligations-list (fn-rcl-feeds h))
          (fn-rcl-bp-obligations (fn-rcl-bp h))))

; A consumer that acknowledged ACK in GROUP holds the article when one of
; its memberships in GROUP is numbered above ACK.
(defun fn-rcl-above-p (group ack memberships)
  (declare (xargs :guard t))
  (if (consp memberships)
      (or (let ((m (car memberships)))
            (and (consp m) (equal (car m) group)
                 (natp (cdr m)) (natp ack) (< ack (cdr m))))
          (fn-rcl-above-p group ack (cdr memberships)))
    nil))

(defun fn-rcl-names-p (ob msgid memberships)
  (declare (xargs :guard t))
  (let ((kind (fn-rcl-car ob)))
    (cond ((equal kind :reader-pin)
           (if (member-equal (cons (fn-rcl-nth 1 ob) (fn-rcl-nth 2 ob))
                             (true-list-fix memberships))
               t nil))
          ((equal kind :consumer-cursor)
           (fn-rcl-above-p (fn-rcl-nth 1 ob) (fn-rcl-nth 2 ob) memberships))
          ((equal kind :feed) (equal (fn-rcl-nth 2 ob) msgid))
          ((equal kind :bp-obligation) (equal (fn-rcl-nth 1 ob) msgid))
          (t nil))))

(defun fn-rcl-some-names-p (obs msgid memberships)
  (declare (xargs :guard t))
  (if (consp obs)
      (or (fn-rcl-names-p (car obs) msgid memberships)
          (fn-rcl-some-names-p (cdr obs) msgid memberships))
    nil))

; -----------------------------------------------------------------------------
; The executable decision.

(defun fn-rcl-pinned-p (pins memberships)
  (declare (xargs :guard t))
  (if (consp pins)
      (or (if (member-equal (cons (fn-rcl-car (car pins)) (fn-rcl-cdr (car pins)))
                            (true-list-fix memberships))
              t nil)
          (fn-rcl-pinned-p (cdr pins) memberships))
    nil))

(defun fn-rcl-unacknowledged-p (memberships cursors)
  (declare (xargs :guard t))
  (if (consp cursors)
      (or (fn-rcl-above-p (fn-rcl-car (car cursors)) (fn-rcl-cdr (car cursors))
                          memberships)
          (fn-rcl-unacknowledged-p memberships (cdr cursors)))
    nil))

(defun fn-rcl-undelivered-p (feeds msgid)
  (declare (xargs :guard t))
  (if (consp feeds)
      (or (let ((feed (car feeds)))
            (and (consp feed) (consp (cdr feed)) (not (cadr feed))
                 (if (member-equal msgid (true-list-fix (cddr feed))) t nil)))
          (fn-rcl-undelivered-p (cdr feeds) msgid))
    nil))

; The rule's own condition, before holders.
(defun fn-rcl-rule-permits (rule now stamp)
  (declare (xargs :guard t))
  (cond ((equal rule '(:released-by-all-holders)) t)
        ((and (fn-rcl-rulep rule) (equal (car rule) :release-after))
         (and (natp now) (natp stamp)
              (<= (+ stamp (* (cadr rule) *fn-rcl-seconds-per-day*)) now)))
        (t nil)))

; Whether the Store's verdict list holds MSGID's payload: some entry for
; MSGID whose token (`fn-stx-verdict-token', the car of the verdict) is not
; :absent.  The statement index is re-derived from the stored payloads at
; open (`fn-stx-index-of-store'), and a payload that verifies under the
; keyring of that open contributes to it; an :unverified article can verify
; under a later keyring, so its payload stays.  An :absent verdict is the
; article with no authorship field, which contributes nothing under ANY
; keyring (books/store-reclaim-holders
; `fn-rcl-absent-verdict-contributes-nothing'), so it holds nothing.  Every
; accepted article has a verdict entry (`fn-sn-finish-records-the-acceptance-
; verdict', books/store-node-invariants), so without this test no article of
; a real store was ever reclaimable.
(defun fn-rcl-verdict-heldp (msgid verdicts)
  (declare (xargs :guard t))
  (if (consp verdicts)
      (or (and (consp (car verdicts)) (equal (car (car verdicts)) msgid)
               (not (and (consp (cdr (car verdicts)))
                         (equal (car (cdr (car verdicts))) :absent))))
          (fn-rcl-verdict-heldp msgid (cdr verdicts)))
    nil))

; Why an article stays, or :reclaimable.  VERDICTS is the Store's
; newest-first (msgid . verdict) list: an article with an authorship
; verdict other than :absent keeps its payload (above; STO-008).
(defun fn-rcl-verdict (rule now h verdicts article)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-rcl-rulep
                                                            fn-rcl-tombstonep
                                                            fn-rcl-rule-permits)))))
  (let ((msgid (fn-article-msgid article))
        (memberships (fn-article-memberships article)))
    (cond ((fn-rcl-tombstonep (fn-article-payload article)) :already-reclaimed)
          ((equal rule '(:keep-forever)) :rule-keeps)
          ((not (fn-rcl-rulep rule)) :rule-refused)
          ((not (fn-rcl-rule-permits rule now (fn-article-stamp article)))
           :too-recent)
          ((fn-rcl-verdict-heldp msgid verdicts) :verdict-needs-payload)
          ((fn-rcl-pinned-p (fn-rcl-pins h) memberships) :held-reader-pin)
          ((fn-rcl-unacknowledged-p memberships (fn-rcl-cursors h))
           :held-consumer-cursor)
          ((fn-rcl-undelivered-p (fn-rcl-feeds h) msgid) :held-feed)
          ((member-equal msgid (true-list-fix (fn-rcl-bp h))) :held-bp-obligation)
          (t :reclaimable))))

(defun fn-rcl-reclaimable (rule now h verdicts article)
  (declare (xargs :guard t))
  (equal (fn-rcl-verdict rule now h verdicts article) :reclaimable))

; -----------------------------------------------------------------------------
; The keystone: the executable decision is the obligation test.

(local
 (defthm pin-obligations-name
   (iff (fn-rcl-some-names-p (fn-rcl-pin-obligations pins) msgid memberships)
        (fn-rcl-pinned-p pins memberships))))

(local
 (defthm some-names-append
   (iff (fn-rcl-some-names-p (append a b) msgid memberships)
        (or (fn-rcl-some-names-p a msgid memberships)
            (fn-rcl-some-names-p b msgid memberships)))))

(local
 (defthm feed-msgid-obligations-name
   (iff (fn-rcl-some-names-p (fn-rcl-feed-msgid-obligations peer msgids)
                             msgid memberships)
        (member-equal msgid (true-list-fix msgids)))))

(local
 (defthm feed-obligations-name
   (iff (fn-rcl-some-names-p (fn-rcl-feed-obligations-list feeds)
                             msgid memberships)
        (fn-rcl-undelivered-p feeds msgid))))

(local
 (defthm bp-obligations-name
   (iff (fn-rcl-some-names-p (fn-rcl-bp-obligations msgids) msgid memberships)
        (member-equal msgid (true-list-fix msgids)))))

(local
 (defthm cursor-obligations-name
   (iff (fn-rcl-some-names-p (fn-rcl-cursor-obligations cursors) msgid memberships)
        (fn-rcl-unacknowledged-p memberships cursors))))

;  KEYSTONE (PRF-088, the decision).  An article is reclaimable exactly when
; it is not already a tombstone, the rule is not keep-forever and permits it
; by age, it carries no authorship verdict but :absent, and NO obligation in the list the
; lifetimes table names -- reader pin, consumer cursor, undelivered feed to a
; live peer, BP obligation -- names it.  The executable side reads one fl
; per consumer group; the obligation side reads every cursor.
(defthm fn-rcl-reclaimable-is-no-obligation-names-it
  (equal (fn-rcl-reclaimable rule now h verdicts article)
         (and (not (fn-rcl-tombstonep (fn-article-payload article)))
              (not (equal rule '(:keep-forever)))
              (fn-rcl-rulep rule)
              (fn-rcl-rule-permits rule now (fn-article-stamp article))
              (not (fn-rcl-verdict-heldp (fn-article-msgid article) verdicts))
              (not (fn-rcl-some-names-p (fn-rcl-obligations h)
                                        (fn-article-msgid article)
                                        (fn-article-memberships article)))))
  :hints (("Goal" :in-theory (disable fn-rcl-rulep fn-rcl-rule-permits
                                      fn-rcl-tombstonep))))

; -----------------------------------------------------------------------------
; What reclamation keeps.
;
; `fn-rcl-reclaim-articles' replaces the payload of the article under MSGID
; by TOMB and leaves every other field, and every other article, as it was.
; `fn-rcl-reclaim-state' does so only for an octet tombstone, so the stored
; payload stays an octet list.

(defun fn-rcl-reclaim-articles (articles msgid tomb)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp articles)
      (if (equal (fn-article-msgid (car articles)) msgid)
          (cons (fn-make-article (fn-article-msgid (car articles))
                                 tomb
                                 (fn-article-groups (car articles))
                                 (fn-article-memberships (car articles))
                                 (fn-article-pin (car articles))
                                 (fn-article-stamp (car articles)))
                (cdr articles))
        (cons (car articles)
              (fn-rcl-reclaim-articles (cdr articles) msgid tomb)))
    articles))

(defun fn-rcl-reclaim-state (s msgid tomb)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-octet-listp tomb)
      (fn-make-state (fn-state-groups s)
                     (fn-state-nexts s)
                     (fn-rcl-reclaim-articles (fn-state-articles s) msgid tomb)
                     (fn-state-next-txid s)
                     (fn-state-pending s)
                     (fn-state-fenced s))
    s))

(defthm fn-rcl-reclaim-articles-keeps-msgids-by-definition
  (equal (fn-article-msgids (fn-rcl-reclaim-articles articles msgid tomb))
         (fn-article-msgids articles)))

;  KEYSTONE (anti-resurrection).  After reclaiming any article, exactly the
; same Message-IDs are accepted as before, so a re-offer of the reclaimed
; one is refused by the duplicate test that `fn-accept-prepare' applies.
(defthm fn-rcl-reclaim-keeps-the-duplicate-history
  (equal (fn-acceptedp x (fn-rcl-reclaim-articles articles msgid tomb))
         (fn-acceptedp x articles)))

; Each article keeps its identity, groups, numbers, archive pin and stamp;
; an article other than the reclaimed one keeps its payload too.
(defthm fn-rcl-reclaim-keeps-every-binding
  (let ((before (fn-find-article x articles))
        (after (fn-find-article x (fn-rcl-reclaim-articles articles msgid tomb))))
    (and (equal (fn-article-msgid after) (fn-article-msgid before))
         (equal (fn-article-groups after) (fn-article-groups before))
         (equal (fn-article-memberships after) (fn-article-memberships before))
         (equal (fn-article-pin after) (fn-article-pin before))
         (equal (fn-article-stamp after) (fn-article-stamp before))
         (implies (not (equal x msgid))
                  (equal after before)))))

(defthm fn-rcl-reclaimed-article-is-the-tombstone
  (implies (fn-find-article msgid articles)
           (equal (fn-article-payload
                   (fn-find-article msgid (fn-rcl-reclaim-articles articles msgid tomb)))
                  tomb)))

; The group numbering: the per-group next numbers are the same state field.
(defthm fn-rcl-reclaim-keeps-the-numbering
  (and (equal (fn-state-nexts (fn-rcl-reclaim-state s msgid tomb))
              (fn-state-nexts s))
       (equal (fn-state-groups (fn-rcl-reclaim-state s msgid tomb))
              (fn-state-groups s))
       (equal (fn-state-next-txid (fn-rcl-reclaim-state s msgid tomb))
              (fn-state-next-txid s))
       (equal (fn-state-pending (fn-rcl-reclaim-state s msgid tomb))
              (fn-state-pending s))))

;  KEYSTONE (the stored state stays a state).
(encapsulate ()
(local (defthm conflictsp-of-reclaim
  (equal (fn-memberships-conflictsp ms (fn-rcl-reclaim-articles xs m tomb))
         (fn-memberships-conflictsp ms xs))
  :hints (("Goal" :induct (fn-rcl-reclaim-articles xs m tomb)
                  :in-theory (enable fn-memberships-conflictsp)))))
(local (defthm freshp-of-reclaim
  (equal (fn-articles-freshp (fn-rcl-reclaim-articles xs m tomb))
         (fn-articles-freshp xs))
  :hints (("Goal" :induct (fn-rcl-reclaim-articles xs m tomb)
                  :in-theory (enable fn-articles-freshp)))))
(local (defthm below-of-reclaim
  (equal (fn-articles-below-nextsp (fn-rcl-reclaim-articles xs m tomb) nexts)
         (fn-articles-below-nextsp xs nexts))
  :hints (("Goal" :induct (fn-rcl-reclaim-articles xs m tomb)
                  :in-theory (enable fn-articles-below-nextsp)))))
(local (defthm listp-of-reclaim
  (implies (and (fn-article-listp g xs) (fn-octet-listp tomb))
           (fn-article-listp g (fn-rcl-reclaim-articles xs m tomb)))
  :hints (("Goal" :induct (fn-rcl-reclaim-articles xs m tomb)
                  :in-theory (enable fn-article-listp fn-articlep)))))
(defthm fn-rcl-reclaim-preserves-statep
  (implies (fn-statep s)
           (fn-statep (fn-rcl-reclaim-state s m tomb)))
  :hints (("Goal" :in-theory (enable fn-statep)))))

; Replay correspondence.  The open replays a reclaimed record through the
; unchanged record path; these two say what it reaches.
(encapsulate ()
(local (defthm reclaim-state-fields
  (implies (fn-octet-listp tomb)
           (and (equal (fn-state-articles (fn-rcl-reclaim-state s m tomb))
                       (fn-rcl-reclaim-articles (fn-state-articles s) m tomb))
                (equal (fn-state-fenced (fn-rcl-reclaim-state s m tomb))
                       (fn-state-fenced s))))))
(local (defthm reclaim-state-of-make-state
  (implies (fn-octet-listp tomb)
           (equal (fn-rcl-reclaim-state (fn-make-state g n a x p f) m tomb)
                  (fn-make-state g n (fn-rcl-reclaim-articles a m tomb) x p f)))))
;  KEYSTONE (replay correspondence, every other record).  Acceptance never
; reads a stored payload: staging a submission and then reclaiming M is
; staging it after reclaiming M.
(defthm fn-rcl-prepare-commutes-with-reclaim
  (implies (fn-statep s)
           (equal (fn-accept-prepare (fn-rcl-reclaim-state s m tomb)
                                     generation msgid payload groups stamp)
                  (fn-rcl-reclaim-state
                   (fn-accept-prepare s generation msgid payload groups stamp)
                   m tomb)))
  :hints (("Goal" :cases ((fn-octet-listp tomb))
                  :in-theory (e/d (fn-accept-prepare)
                                  (fn-rcl-reclaim-state fn-rcl-reclaim-articles
                                   fn-statep)))
          ("Subgoal 2" :in-theory (enable fn-rcl-reclaim-state))))
; The reclaimed record's own step (replaying it with the tombstone as its
; payload reaches the reclaimed state) is not proved here: its direct proof
; did not return in 60 s (open, PRF-088).
)

; The guarded step the host's plan applies: a held article is never touched.
(defun fn-rcl-reclaim-if-permitted (s rule now h verdicts msgid tomb)
  (declare (xargs :guard t :verify-guards nil))
  (let ((article (fn-find-article msgid (fn-state-articles s))))
    (if (and article (fn-rcl-reclaimable rule now h verdicts article))
        (fn-rcl-reclaim-state s msgid tomb)
      s)))

(local
 (defthm fn-rcl-msgid-of-find-article
   (implies (fn-find-article m xs)
            (equal (fn-article-msgid (fn-find-article m xs)) m))))

;  KEYSTONE (a held article is never touched).  If any obligation the
; lifetimes table lists names the article, or the rule keeps it, the state
; is unchanged.
(defthm fn-rcl-reclaim-never-touches-a-held-article
  (let ((article (fn-find-article msgid (fn-state-articles s))))
    (implies (or (fn-rcl-some-names-p (fn-rcl-obligations h) msgid
                                      (fn-article-memberships article))
                 (equal rule '(:keep-forever)))
             (equal (fn-rcl-reclaim-if-permitted s rule now h verdicts msgid tomb)
                    s)))
  :hints (("Goal" :in-theory (disable fn-rcl-reclaimable fn-rcl-reclaim-state
                                      fn-rcl-obligations fn-rcl-some-names-p
                                      fn-rcl-tombstonep fn-rcl-rulep
                                      fn-rcl-rule-permits fn-rcl-verdict-heldp)
                  :use ((:instance fn-rcl-reclaimable-is-no-obligation-names-it
                                   (article (fn-find-article
                                             msgid (fn-state-articles s))))))))

; -----------------------------------------------------------------------------
; The tombstone.

;  D13.  The tombstone of PAYLOAD: what `store reclaim' writes in place of
; a reclaimed article's payload (books/reclaim-tombstone for the layout).  It
; keeps the SHA-256 of the octets, and when the payload's own Path line names
; an agent whose recipe gives back a source, the SHA-256 of that source.
(defun fn-rcl-zeros (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons 0 (fn-rcl-zeros (1- n)))))

(defun fn-rcl-tombstone-of (payload msgid)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((agent (fn-pb-path-agent payload msgid))
         (subject (fn-pb-subject payload agent msgid))
         (sourcep (equal (car subject) :source)))
    (append *fn-rcl-magic*
            (cons (if sourcep 1 0)
                  (append (fn-sha256 payload)
                          (append (if sourcep
                                      (fn-sha256 (cdr subject))
                                    (fn-rcl-zeros 32))
                                  (append (fn-rcl-u64-octets (len payload))
                                          (append (fn-rcl-u64-octets (len agent))
                                                  agent))))))))

; A submission against a tombstone: the comparison `fn-pb-same-articlep'
; makes, over the digests the tombstone kept.  The source arm applies when
; the submission's agent is the reclaimed article's own; any other case
; compares the octets' digests.
(defun fn-rcl-same-as-tombstonep (msgid payload tomb)
  (declare (xargs :guard t))
  (let* ((agent (fn-pb-path-agent payload msgid))
         (a (fn-pb-subject payload agent msgid)))
    (if (and (fn-rcl-tomb-sourcep tomb)
             (equal agent (fn-rcl-tomb-agent tomb))
             (equal (car a) :source))
        (equal (fn-sha256 (cdr a)) (fn-rcl-tomb-source-digest tomb))
      (equal (fn-sha256 payload) (fn-rcl-tomb-octets-digest tomb)))))

; The Store's decision for an already held Message-ID, over a store that may
; hold tombstones: `fn-pb-existing-action' (books/poster-bytes) for a live
; payload, the digest comparison for a tombstone.  The host calls this in
; place of `fn-pb-existing-action' at every site that called that.
(defun fn-rcl-same-articlep (msgid payload held-payload)
  (declare (xargs :guard t))
  (if (fn-rcl-tombstonep held-payload)
      (fn-rcl-same-as-tombstonep msgid payload held-payload)
    (fn-pb-same-articlep msgid payload held-payload)))

(defun fn-rcl-existing-action (msgid payload groups s)
  (declare (xargs :guard t))
  (let ((article (fn-find-article
                  msgid (fn-state-articles
                         (fn-node-acceptance (fn-sn-node s))))))
    (if article
        (if (and (fn-rcl-same-articlep (fn-record-string-octets msgid) payload
                                       (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

; -----------------------------------------------------------------------------
; The duplicate-versus-conflict verdict (D25) the host calls,
; `fn-pb-existing-action', read over the article list.

(defun fn-rcl-action-over (msgid payload groups articles)
  (declare (xargs :guard t :verify-guards nil))
  (let ((article (fn-find-article msgid articles)))
    (if article
        (if (and (fn-rcl-same-articlep (fn-record-string-octets msgid) payload
                                       (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

(defthm fn-rcl-existing-action-is-action-over-by-definition
  (equal (fn-rcl-existing-action msgid payload groups s)
         (fn-rcl-action-over msgid payload groups
                             (fn-state-articles
                              (fn-node-acceptance (fn-sn-node s)))))
  :hints (("Goal" :in-theory (enable fn-rcl-existing-action))))

; Before any reclamation the host's new call answers exactly as the old one.
(defthm fn-rcl-existing-action-is-pb-without-a-tombstone
  (implies (not (fn-rcl-tombstonep
                 (fn-article-payload
                  (fn-find-article msgid (fn-state-articles
                                          (fn-node-acceptance (fn-sn-node s)))))))
           (equal (fn-rcl-existing-action msgid payload groups s)
                  (fn-pb-existing-action msgid payload groups s)))
  :hints (("Goal" :in-theory (enable fn-pb-existing-action))))

; Two different octet lists with one SHA-256.
(defun fn-rcl-collisionp (x y)
  (declare (xargs :guard t :verify-guards nil))
  (and (not (equal x y)) (equal (fn-sha256 x) (fn-sha256 y))))

(local (include-book "std/lists/append" :dir :system))

(local
 (defthm fn-rcl-len-sha256
   (equal (len (fn-sha256 x)) 32)
   :hints (("Goal" :use ((:instance fn-sha256-of-octets-shape
                                    (msg (fn-sha256-fix-octets x))))
                   :in-theory (enable fn-sha256)))))

(local
 (defthm fn-rcl-len-u64-aux
   (implies (natp k)
            (equal (len (fn-rcl-u64-octets-aux k n acc)) (+ k (len acc))))))

(local
 (defthm fn-rcl-len-u64
   (equal (len (fn-rcl-u64-octets n)) 8)
   :hints (("Goal" :in-theory (enable fn-rcl-u64-octets)))))

(local
 (defthm fn-rcl-len-zeros
   (equal (len (fn-rcl-zeros n)) (nfix n))))

(local
 (defthm fn-rcl-drop-of-append
   (implies (and (natp n) (<= (len a) n))
            (equal (fn-rcl-drop n (append a b))
                   (fn-rcl-drop (- n (len a)) b)))
   :hints (("Goal" :induct (fn-rcl-drop n a)))))

(local
 (defthm fn-rcl-drop-of-append-short
   (implies (and (natp n) (< n (len a)))
            (equal (fn-rcl-drop n (append a b))
                   (append (fn-rcl-drop n a) b)))
   :hints (("Goal" :induct (fn-rcl-drop n a)))))

(local
 (defthm fn-rcl-take-of-append-exact
   (implies (and (natp n) (equal (len a) n) (true-listp a))
            (equal (fn-rcl-take n (append a b)) a))
   :hints (("Goal" :induct (fn-rcl-take n a)))))

(local
 (defthm fn-rcl-at-leastp-is-len
   (implies (natp n)
            (equal (fn-rcl-at-leastp n x) (<= n (len x))))
   :hints (("Goal" :induct (fn-rcl-at-leastp n x)))))

(local
 (defthm fn-rcl-drop-zero
   (equal (fn-rcl-drop 0 x) x)))

(local
 (defthm fn-rcl-true-listp-sha256
   (true-listp (fn-sha256 x))
   :hints (("Goal" :use ((:instance fn-sha256-of-octets-shape
                                    (msg (fn-sha256-fix-octets x))))
                   :in-theory (enable fn-sha256)))))

(local
 (defthm fn-rcl-true-listp-u64-aux
   (implies (true-listp acc)
            (true-listp (fn-rcl-u64-octets-aux k n acc)))))

(local
 (defthm fn-rcl-true-listp-zeros
   (true-listp (fn-rcl-zeros n))))

(verify-guards fn-rcl-tombstone-of
  :hints (("Goal" :in-theory (disable fn-sha256 fn-pb-subject fn-pb-path-agent))))

; The fields of a tombstone read back what `fn-rcl-tombstone-of' put there.
(defthm fn-rcl-tombstone-of-fields
  (let ((tomb (fn-rcl-tombstone-of payload msgid))
        (agent (fn-pb-path-agent payload msgid)))
    (and (fn-rcl-tombstonep tomb)
         (equal (fn-rcl-tomb-octets-digest tomb) (fn-sha256 payload))
         (equal (fn-rcl-tomb-sourcep tomb)
                (equal (car (fn-pb-subject payload agent msgid)) :source))
         (implies (equal (car (fn-pb-subject payload agent msgid)) :source)
                  (equal (fn-rcl-tomb-source-digest tomb)
                         (fn-sha256 (cdr (fn-pb-subject payload agent msgid)))))
         (equal (fn-rcl-tomb-agent tomb) agent)))
  :hints (("Goal" :in-theory (e/d (fn-rcl-tombstone-of) (fn-sha256 fn-pb-subject
                                                        fn-pb-path-agent)))))

;  KEYSTONE (D25 after reclamation).  Reclaiming article M leaves the
; host's duplicate-versus-conflict verdict unchanged for every Message-ID X,
; every submission P and every group list G -- unless SHA-256 collides on
; the pair the tombstone compares (the submission against the removed
; payload, or their D25 sources), or the submission names a different
; injecting agent under which the removed payload still gives back a source.
; The collision disjuncts are the stated limit: SHA-256's collision
; resistance, about 2^128 work, is the assumption, and it is not proved.
(defthm fn-rcl-existing-action-after-reclaim
  (let* ((held (fn-article-payload (fn-find-article m articles)))
         (mo (fn-record-string-octets m))
         (tomb (fn-rcl-tombstone-of held mo))
         (agent (fn-pb-path-agent p mo))
         (a (fn-pb-subject p agent mo))
         (b (fn-pb-subject held agent mo)))
    (implies (and (fn-find-article m articles)
                  (not (fn-rcl-tombstonep held)))
             (or (equal (fn-rcl-action-over x p g
                                            (fn-rcl-reclaim-articles articles m tomb))
                        (fn-rcl-action-over x p g articles))
                 (fn-rcl-collisionp p held)
                 (fn-rcl-collisionp (cdr a) (cdr b))
                 (and (not (equal agent (fn-pb-path-agent held mo)))
                      (equal (car b) :source)))))
  :hints (("Goal" :cases ((equal x m))
                  :in-theory (e/d (fn-pb-same-articlep)
                                  (fn-rcl-tombstone-of fn-sha256 fn-pb-subject
                                   fn-pb-path-agent fn-rcl-tombstonep
                                   fn-rcl-tomb-sourcep fn-rcl-tomb-agent
                                   fn-rcl-tomb-octets-digest
                                   fn-rcl-tomb-source-digest)))))

; -----------------------------------------------------------------------------
; The host's view: one verdict per stored article, and the counts `status'
; prints.  Work is one pass over the article list with the holders' lists.

(defun fn-rcl-plan (rule now h verdicts articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (cons (cons (fn-article-msgid (car articles))
                  (fn-rcl-verdict rule now h verdicts (car articles)))
            (fn-rcl-plan rule now h verdicts (cdr articles)))
    nil))

; (reclaimable reclaimable-octets reclaimed reclaimed-octets-freed)
(defun fn-rcl-summary (rule now h verdicts articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (let* ((rest (fn-rcl-summary rule now h verdicts (cdr articles)))
             (a (car articles))
             (payload (fn-article-payload a))
             (verdict (fn-rcl-verdict rule now h verdicts a)))
        (cond ((equal verdict :reclaimable)
               (list (+ 1 (nfix (nth 0 rest))) (+ (len payload) (nfix (nth 1 rest)))
                     (nfix (nth 2 rest)) (nfix (nth 3 rest))))
              ((equal verdict :already-reclaimed)
               (list (nfix (nth 0 rest)) (nfix (nth 1 rest))
                     (+ 1 (nfix (nth 2 rest)))
                     (+ (nfix (- (fn-rcl-tomb-length payload) (len payload)))
                        (nfix (nth 3 rest)))))
              (t (list (nfix (nth 0 rest)) (nfix (nth 1 rest))
                       (nfix (nth 2 rest)) (nfix (nth 3 rest))))))
    (list 0 0 0 0)))
