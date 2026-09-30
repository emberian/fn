; store-number-bound.lisp -- RFC 3977 section 6's article-number bound kept
; by admission (lane join-f2-615, 2026-09-28; PKT-615 as the coordinator
; decided it).
;
; RFC 3977 section 6: "Article numbers MUST lie between 1 and 2,147,483,647,
; inclusive."  That is a PROTOCOL bound, not an implementation ceiling (D27):
; a group whose next number would pass it cannot be served at all.  So the
; admission refuses by name an article whose allocation would take any of
; its groups' next number past the bound (books/owner-prepare-served.lisp
; fn-psrv-prepare, word :article-numbers-exhausted), and the served side no
; longer re-counts the whole archive to find out (fn-nntp-projectionp lost
; its article-count conjunct).
;
; The allocation (books/acceptance-alloc.lisp fn-allocate-memberships) gives
; each group its next number and bumps it; the watermark after the article
; is that number plus one.  The watermark is rendered as the low number of an
; emptied group (RFC 3977 section 6.1.1.2), so it must itself be an article
; number: the test is "the number allocated is below 2,147,483,647", which
; keeps every watermark, fn-nntp-nexts-boundedp, within section 6.
;
; KEYSTONE fn-snb-replay-apply-record-keeps-nexts-bounded: a store record
; the admission let through keeps the node's watermarks within the bound;
; so every state the Store reaches by admitted records keeps them
; (fn-snb-replay-keeps-nexts-bounded over a history each of whose records
; fit at its own prefix), and fn-nntp-projectionp of such an archive is its
; fn-statep, its served group names and nothing else
; (books/store-number-projection.lisp).
;
; This book owns the prefix `fn-snb-' (docs/prefixes.md).

(in-package "ACL2")

(include-book "replay")
(include-book "nntp-session")

; The groups of an article, bumped in the allocation's order, each get a
; number strictly below the bound (so the watermark after is at most it).
(defun fn-snb-groups-fitp (groups nexts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (and (natp (fn-next-number (car groups) nexts))
           (< (fn-next-number (car groups) nexts) *fn-nntp-max-article-number*)
           (fn-snb-groups-fitp (cdr groups) (fn-bump-number (car groups) nexts)))
    t))

(verify-guards fn-snb-groups-fitp)

; The article a store record would install: a held row, or the held row a
; signed composite carries; nil for every other event.
(defun fn-snb-record-article (record)
  (declare (xargs :guard t))
  (cond ((fn-held-p record) record)
        ((fn-hstxa-p record) (fn-replay-composite-held record))
        (t nil)))

; THE ADMISSION TEST (RFC 3977 section 6): the record installs no article, or
; its article's groups fit at the node's watermarks.
(defun fn-snb-record-fitp (node record)
  (declare (xargs :guard t :verify-guards nil))
  (let ((article (fn-snb-record-article record)))
    (or (not (fn-held-p article))
        (fn-snb-groups-fitp (fn-record-groups article)
                            (fn-state-nexts (fn-node-acceptance node))))))

(verify-guards fn-snb-record-fitp)

; -----------------------------------------------------------------------------
; The watermarks after an allocation.

(defthm fn-snb-next-number-natp-when-bounded
  (implies (fn-nntp-nexts-boundedp nexts)
           (natp (fn-next-number g nexts)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-next-number fn-nntp-nexts-boundedp))))

(defthm fn-snb-nexts-boundedp-of-bump
  (implies (and (fn-nntp-nexts-boundedp nexts)
                (< (fn-next-number g nexts) *fn-nntp-max-article-number*))
           (fn-nntp-nexts-boundedp (fn-bump-number g nexts)))
  :hints (("Goal" :induct (fn-bump-number g nexts)
           :in-theory (enable fn-bump-number fn-next-number fn-nntp-nexts-boundedp))))

; The acceptance's install (books/acceptance.lisp fn-install-pending) bumps
; each of the article's groups in order: an article that fits keeps every
; watermark within the bound.
(defthm fn-snb-nexts-boundedp-of-advance
  (implies (and (fn-nntp-nexts-boundedp nexts)
                (fn-snb-groups-fitp groups nexts))
           (fn-nntp-nexts-boundedp (fn-advance-nexts groups nexts)))
  :hints (("Goal" :induct (fn-advance-nexts groups nexts)
           :in-theory (enable fn-advance-nexts fn-snb-groups-fitp))))

(defthm fn-snb-initial-nexts-bounded
  (fn-nntp-nexts-boundedp (fn-initial-nexts groups))
  :hints (("Goal" :in-theory (enable fn-initial-nexts fn-nntp-nexts-boundedp))))

; -----------------------------------------------------------------------------
; What each node step does to the watermarks: the prepare and every non-
; article step keep them; a durable completion advances them by the staged
; article's groups.

(defthm fn-snb-advance-txid-nexts
  (equal (fn-state-nexts (fn-node-acceptance (fn-replay-advance-txid node txid)))
         (fn-state-nexts (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (e/d (fn-replay-advance-txid) (fn-node-statep)))))

(defthm fn-snb-advance-txid-stage
  (implies (not (consp (fn-node-stage node)))
           (not (consp (fn-node-stage (fn-replay-advance-txid node txid)))))
  :hints (("Goal" :in-theory (e/d (fn-replay-advance-txid) (fn-node-statep)))))

(defthm fn-snb-accept-prepare-nexts
  (equal (fn-state-nexts (fn-accept-prepare s generation msgid payload groups stamp))
         (fn-state-nexts s))
  :hints (("Goal" :in-theory (e/d (fn-accept-prepare) (fn-statep fn-allocate-memberships)))))

(defthm fn-snb-accept-prepare-pending-groups
  (implies (not (equal (fn-accept-prepare s generation msgid payload groups stamp) s))
           (equal (fn-pending-groups (fn-state-pending (fn-accept-prepare s generation msgid payload groups stamp)))
                  groups))
  :hints (("Goal" :in-theory (e/d (fn-accept-prepare) (fn-statep fn-allocate-memberships)))))

(defthm fn-snb-accept-complete-nexts
  (implies (fn-statep s)
           (equal (fn-state-nexts (fn-accept-complete s txid generation status))
                  (if (and (not (equal (fn-state-fenced s) t))
                           (fn-pending-matchesp (fn-state-pending s) txid generation)
                           (equal status :durable))
                      (fn-advance-nexts (fn-pending-groups (fn-state-pending s)) (fn-state-nexts s))
                    (fn-state-nexts s))))
  :hints (("Goal" :in-theory (e/d (fn-accept-complete fn-install-pending fn-clear-pending)
                                  (fn-statep fn-advance-nexts fn-pending-matchesp)))))

(defthm fn-snb-node-prepare-nexts
  (equal (fn-state-nexts (fn-node-acceptance
                          (fn-node-prepare s generation msgid payload groups id subject evidence charge stamp binding)))
         (fn-state-nexts (fn-node-acceptance s)))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare)
                                  (fn-node-statep fn-accept-prepare fn-retain-admissiblep fn-retain-admit)))))

(defthm fn-snb-node-prepare-pending-groups
  (implies (and (not (consp (fn-node-stage s)))
                (consp (fn-node-stage (fn-node-prepare s generation msgid payload groups id subject
                                                       evidence charge stamp binding))))
           (equal (fn-pending-groups
                   (fn-state-pending (fn-node-acceptance
                                      (fn-node-prepare s generation msgid payload groups id subject
                                                       evidence charge stamp binding))))
                  groups))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare)
                                  (fn-node-statep fn-accept-prepare fn-retain-admissiblep fn-retain-admit)))))

(defthm fn-snb-node-complete-nexts
  (implies (fn-node-pending-matchesp s txid generation)
           (equal (fn-state-nexts (fn-node-acceptance (fn-node-complete s txid generation status)))
                  (if (equal status :durable)
                      (fn-advance-nexts (fn-pending-groups (fn-state-pending (fn-node-acceptance s)))
                                        (fn-state-nexts (fn-node-acceptance s)))
                    (fn-state-nexts (fn-node-acceptance s)))))
  :hints (("Goal" :in-theory (e/d (fn-node-complete fn-node-pending-matchesp fn-node-statep)
                                  (fn-accept-complete fn-advance-nexts fn-pending-matchesp fn-statep)))))

; -----------------------------------------------------------------------------
; KEYSTONE (a Store record the admission let through keeps every watermark
; within RFC 3977 section 6's bound).  books/replay.lisp fn-replay-apply-record
; is the node step of every durable record, live (the Store's completion,
; books/store-node.lisp) and at recovery; the admission's test is
; fn-snb-record-fitp at the node the record is applied to
; (books/owner-prepare-served.lisp fn-psrv-event-numberedp).  Teeth:
; tests/acl2/store-number-bound-tests.lisp.
(defthm fn-snb-replay-apply-record-keeps-nexts-bounded
  (implies (and (fn-nntp-nexts-boundedp (fn-state-nexts (fn-node-acceptance node)))
                (fn-snb-record-fitp node record))
           (fn-nntp-nexts-boundedp
            (fn-state-nexts (fn-node-acceptance (fn-replay-apply-record node record)))))
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-record fn-snb-record-fitp fn-snb-record-article
                                   fn-replay-apply-retention-event fn-replay-complete-retention
                                   fn-replay-node-with-retention fn-replay-apply-identity-neutral
                                   fn-node-pending-matchesp)
                                  (fn-node-prepare fn-node-complete fn-replay-advance-txid
                                   fn-node-statep fn-advance-nexts fn-snb-groups-fitp
                                   fn-retain-admissiblep fn-retain-admit fn-retain-release
                                   fn-retain-matching-releasep fn-held-p fn-hstxa-p
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-cpe-eventp
                                   fn-th-topic-eventp fn-pending-matchesp)))))

; Every record of a history admitted at its own prefix: the fold the
; recovery replays (fn-replay-loop) visits exactly these nodes.
(defun fn-snb-history-fitp (node records)
  (declare (xargs :guard t :verify-guards nil :measure (len records)))
  (if (consp records)
      (and (fn-snb-record-fitp node (car records))
           (let ((next (fn-replay-apply-record node (car records))))
             (or (not (fn-node-statep next))
                 (fn-snb-history-fitp next (cdr records)))))
    t))

(defthm fn-snb-replay-loop-keeps-nexts-bounded
  (implies (and (fn-nntp-nexts-boundedp (fn-state-nexts (fn-node-acceptance node)))
                (fn-snb-history-fitp node records))
           (fn-nntp-nexts-boundedp
            (fn-state-nexts (fn-node-acceptance
                             (fn-replay-result-node (fn-replay-loop node records seq))))))
  :hints (("Goal" :induct (fn-replay-loop node records seq)
           :in-theory (e/d (fn-replay-loop fn-snb-history-fitp)
                           (fn-replay-apply-record fn-node-statep fn-snb-record-fitp)))
          ("Subgoal *1/3" :use ((:instance fn-snb-replay-apply-record-keeps-nexts-bounded
                                           (record (car records)))))))

; KEYSTONE (every state the Store reaches by admitted records keeps its
; watermarks within the bound): the replay of a history each of whose
; records the admission let through at its own prefix.
(defthm fn-snb-replay-keeps-nexts-bounded
  (implies (fn-snb-history-fitp (fn-node-initial-state groups capacity) records)
           (fn-nntp-nexts-boundedp
            (fn-state-nexts (fn-node-acceptance
                             (fn-replay-result-node (fn-replay groups capacity records))))))
  :hints (("Goal" :in-theory (e/d (fn-replay fn-node-initial-state fn-initial-state)
                                  (fn-replay-loop fn-snb-history-fitp fn-node-statep fn-initial-nexts))
           :use ((:instance fn-snb-replay-loop-keeps-nexts-bounded
                            (node (fn-node-initial-state groups capacity)) (seq 0))))))

(in-theory (disable fn-snb-groups-fitp fn-snb-record-fitp fn-snb-history-fitp))
