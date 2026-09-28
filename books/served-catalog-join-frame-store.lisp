;; fn: the catalog invariant across the owner steps that change the store
;; but complete no article (lane sca-join-4, sub-lane F-store, 2026-09-27;
;; PRF-302, step 4 of the catalog join's discharge).
;
; books/served-catalog-join-conns.lisp's fn-scj-invp is the invariant the
; host's catalog carries with the owner.  This book proves that every owner
; transition which changes the Store (or completes a transaction whose record
; loads no catalog row) keeps it with the catalog UNTOUCHED.  One lemma per
; transition, in the pattern of books/owner-offer-indexed.lisp; every one
; reduces to a single keystone:
;
;   fn-scjs-invp-of-store-frame -- an owner O2 over O's view and
;   connections whose Store is a FRAME step of O's Store
;   (fn-scjs-store-framep: the acceptance's articles and the verdicts kept,
;   the history kept or grown by the staged candidate into :completing, and
;   outside :completing every record past the view's version loading no
;   row), once refreshed, keeps fn-scj-invp and the seen fact below.  The
;   refresh itself is books/served-catalog-join-frame.lisp's
;   fn-scj-invp-of-refresh.
;
; The seen fact (fn-scjs-seenp) is the one premise fn-scj-invp does not
; carry: the view's version is within the history it is held to have seen
; (the store's history, less the in-flight last record at :completing) and
; the records past it load no catalog row.  It holds at every refresh at an
; idle phase (the view's version becomes the history's length) and every
; transition here keeps it: the directory's publishing observation appends
; exactly the staged candidate into :completing, whose seen history is the
; old one, and only a finish leaves :completing.  Without it an I/O word that
; returns the Store to :ready (a reservation refusal, a known abort, a
; frontier failure) would refresh the view over records it has not seen.  At
; :completing it gives the host's article finish the rows invariant over the
; history before the in-flight event (fn-scjs-rows-invp-before-in-flight).
;
; Every arm also keeps fn-scjs-versionsp (books/served-catalog-join-
; pinned.lisp fn-scj-conns-versions-atmostp at the view's version): a
; refresh moves the view's version only up, an advance re-pins at it.
;
; Named hypotheses and their sources:
;   fn-scar-view-indexedp  -- books/owner-offer-indexed.lisp carries it
;                             across every owner transition.
;   fn-scjs-historyp       -- natp version, version <= len, a true-list history:
;                             fn-own-relation gives it (fn-scjs-historyp-of-own-relation).
;   fn-nntp-projectionp    -- of the refreshed view's archive: the parent's
;                             named hypothesis (LANEDUMP, "Named hypotheses").
;   for a completion: (not (fn-scj-load-h (fn-sn-completion-record s))), the
;   completing record loads no row -- an ARTICLE completion is the catalog's
;   own T4-then-T2 (step 2) and is excluded; and the history past the view
;   loads no row (in a reachable owner that is the completing record alone).
;   for the staged configuration completion (fn-ocl-complete): the frame
;   fact of fn-cpo-configure-durable's store step stays NAMED (the replay
;   under the grown configuration history keeping the articles and verdicts
;   is not proved here).
;
; Not covered: the model's (:store (:crash ..)) and (:store (:recover)) and
; fn-own-reopen, which are model restart events (the host restarts through
; fn-owner-recover and rebuilds the catalog); recovery may complete the
; in-flight article, so they are not frame steps.
;
; Prefix fn-scjs-.

(in-package "ACL2")

(include-book "served-catalog-join-frame")
(include-book "owner-offer-indexed")
(include-book "served-catalog-join-pinned")

(defthm fn-scjs-invp-of-same-fields
  (implies (and (equal (fn-own-store o2) (fn-own-store o))
                (equal (fn-own-view o2) (fn-own-view o))
                (equal (fn-own-conns o2) (fn-own-conns o)))
           (equal (fn-scj-invp o2 fn-arena fn-cat) (fn-scj-invp o fn-arena fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-scj-invp fn-scj-vvp)
                                  (fn-scj-joinp fn-scj-rows-invp fn-scj-live-okp fn-scj-conns-pinp)))))

;; The history the view is held to have seen: the store's, less the in-flight
;; last record at :completing (the directory's publishing observation
;; appended exactly the staged candidate).
(defun-nx fn-scjs-seen-records (files)
  (if (equal (fn-sf-phase files) :completing)
      (butlast (fn-sf-records files) 1)
    (fn-sf-records files)))

;; THE SEEN FACT, over a store at a version: the version is within that
;; history and the records past it load no catalog row.
(defun-nx fn-scjs-store-seenp (s v)
  (let ((r (fn-scjs-seen-records (fn-sn-files s))))
    (and (<= v (len r))
         (fn-scj-no-rowsp (nthcdr v r)))))

(defun-nx fn-scjs-seenp (o)
  (fn-scjs-store-seenp (fn-own-store o) (fn-own-view-version (fn-own-view o))))

(defun-nx fn-scjs-store-framep (s st v)
  (let ((records (fn-sf-records (fn-sn-files s)))
        (records2 (fn-sf-records (fn-sn-files st))))
    (and (equal (fn-state-articles (fn-node-acceptance (fn-sn-node st)))
                (fn-state-articles (fn-node-acceptance (fn-sn-node s))))
         (equal (fn-sn-verdicts st) (fn-sn-verdicts s))
         (or (equal records2 records)
             (equal records2
                    (append records (list (fn-sf-record-candidate (fn-sn-files s))))))
         (fn-scjs-store-seenp st v))))

(local
 (defthm fn-scjs-take-of-append-le
   (implies (<= n (len xs))
            (equal (fn-own-take n (append xs ys)) (fn-own-take n xs)))
   :hints (("Goal" :induct (fn-own-take n xs) :in-theory (enable fn-own-take)))))

(defthm fn-scjs-no-rowsp-of-nthcdr-len
  (fn-scj-no-rowsp (nthcdr (len xs) xs)))

(local
 (defthm fn-scjs-refresh-version
   (equal (fn-own-view-version (fn-own-view (fn-own-refresh o)))
          (if (fn-own-store-idlep (fn-own-store o))
              (len (fn-sf-records (fn-sn-files (fn-own-store o))))
            (fn-own-view-version (fn-own-view o))))
   :hints (("Goal" :in-theory (e/d (fn-own-refresh)
                                   (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                    fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                    fn-ctl-visible-state-of))))))

(defthm fn-scjs-invp-of-store-frame-unrefreshed
  (let ((v (fn-own-view-version (fn-own-view o))))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (<= v (len (fn-sf-records (fn-sn-files (fn-own-store o)))))
                  (fn-scjs-store-framep (fn-own-store o) (fn-own-store o2) v)
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o)))
             (fn-scj-invp o2 fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-scj-invp fn-scj-vvp fn-scjs-store-framep)
                                  (fn-scj-joinp fn-scj-rows-invp fn-scj-live-okp fn-scj-conns-pinp
                                   fn-scjs-store-seenp)))))

(defthm fn-scjs-seenp-and-framep-give-no-rows
  (let ((v (fn-own-view-version (fn-own-view o))))
    (implies (and (fn-scjs-store-framep (fn-own-store o) (fn-own-store o2) v)
                  (equal (fn-own-view o2) (fn-own-view o)))
             (and (implies (not (equal (fn-sf-phase (fn-sn-files (fn-own-store o2))) :completing))
                           (fn-scj-no-rowsp (nthcdr v (fn-sf-records (fn-sn-files (fn-own-store o2))))))
                  (fn-scjs-seenp o2))))
  :hints (("Goal" :in-theory (enable fn-scjs-store-framep fn-scjs-seenp fn-scjs-store-seenp
                                     fn-scjs-seen-records))))

(defthm fn-scjs-store-seenp-at-length
  (implies (not (equal (fn-sf-phase (fn-sn-files s)) :completing))
           (fn-scjs-store-seenp s (len (fn-sf-records (fn-sn-files s)))))
  :hints (("Goal" :in-theory (enable fn-scjs-store-seenp fn-scjs-seen-records))))

(defthm fn-scjs-view-indexedp-of-same-view
  (implies (equal (fn-own-view o2) (fn-own-view o))
           (equal (fn-scar-view-indexedp o2) (fn-scar-view-indexedp o)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-scar-view-indexedp))))

(defthm fn-scjs-frame-records-facts
  (let ((v (fn-own-view-version (fn-own-view o)))
        (records (fn-sf-records (fn-sn-files (fn-own-store o))))
        (records2 (fn-sf-records (fn-sn-files (fn-own-store o2)))))
    (implies (and (natp v) (<= v (len records)) (true-listp records)
                  (fn-scjs-store-framep (fn-own-store o) (fn-own-store o2) v))
             (and (true-listp records2)
                  (<= v (len records2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scjs-store-framep))))

(defthm fn-scjs-invp-of-store-frame
  (let ((v (fn-own-view-version (fn-own-view o)))
        (records (fn-sf-records (fn-sn-files (fn-own-store o)))))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (fn-scar-view-indexedp o)
                  (natp v)
                  (<= v (len records))
                  (true-listp records)
                  (fn-scjs-store-framep (fn-own-store o) (fn-own-store o2) v)
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (fn-nntp-projectionp (fn-own-view-archive (fn-own-view (fn-own-refresh o2)))))
             (and (fn-scj-invp (fn-own-refresh o2) fn-arena fn-cat)
                  (fn-scjs-seenp (fn-own-refresh o2)))))
  :hints (("Goal" :cases ((fn-own-store-idlep (fn-own-store o2)))
           :in-theory '(fn-scj-refresh-not-idle fn-scjs-refresh-version fn-scjs-no-rowsp-of-nthcdr-len
                        fn-own-refresh-keeps-fields natp (:e fn-snt-idle-phasep) (:e member-equal) (:e equal))
           :use (fn-scjs-invp-of-store-frame-unrefreshed
                 fn-scjs-seenp-and-framep-give-no-rows
                 fn-scjs-view-indexedp-of-same-view
                 fn-scjs-frame-records-facts
                 (:instance fn-scj-invp-of-refresh (o o2))
                 (:instance fn-scjs-seenp (o (fn-own-refresh o2)))
                 (:instance fn-scjs-seenp (o o2))
                 (:instance fn-scjs-store-seenp-at-length (s (fn-own-store o2)))
                 (:instance fn-scjs-store-framep (s (fn-own-store o)) (st (fn-own-store o2))
                            (v (fn-own-view-version (fn-own-view o))))
                 (:instance fn-own-store-idlep (s (fn-own-store o2)))
                 (:instance fn-snt-idle-phasep (phase (fn-sf-phase (fn-sn-files (fn-own-store o2)))))))))

(local
 (defthm fn-scjs-sn-update-fields
   (and (equal (fn-sn-node (fn-sn-update s files node)) node)
        (equal (fn-sn-verdicts (fn-sn-update s files node)) (fn-sn-verdicts s))
        (equal (fn-sn-files (fn-sn-update s files node)) files))
   :hints (("Goal" :in-theory (enable fn-sn-update fn-sn-make-v6 fn-sn-node fn-sn-verdicts fn-sn-files)))))

; A file step of the I/O surface keeps the history, except the directory's
; publishing observation, which appends the staged candidate and enters
; :completing; nothing leaves :completing but the finish.
(defun-nx fn-scjs-files-framep (files files2)
  (or (and (equal (fn-sf-records files2) (fn-sf-records files))
           (iff (equal (fn-sf-phase files2) :completing)
                (equal (fn-sf-phase files) :completing)))
      (and (equal (fn-sf-phase files2) :completing)
           (not (equal (fn-sf-phase files) :completing))
           (equal (fn-sf-records files2)
                  (append (fn-sf-records files)
                          (list (fn-sf-record-candidate files)))))))

(defthm fn-scjs-file-step-framep
  (fn-scjs-files-framep files (fn-sn-file-step files operation result))
  :hints (("Goal" :in-theory (e/d (fn-sn-file-step fn-sf-start-frontier fn-sf-frontier-file-result
                                   fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                                   fn-sf-record-file-result fn-sf-record-link-result
                                   fn-sf-record-dir-result fn-sf-recovery-barrier)
                                  (fn-sf-statep)))))

(defthm fn-scjs-butlast-of-snoc
  (equal (butlast (append r (list c)) 1) (true-list-fix r)))

(defthm fn-scjs-snoc-is-not-self
  (and (not (equal (append x (list c)) x))
       (not (equal x (append x (list c)))))
  :hints (("Goal" :use ((:instance len (x (append x (list c)))))
           :in-theory (disable len))))

(local
 (defthm fn-scjs-no-rowsp-of-list-fix
   (equal (fn-scj-no-rowsp (true-list-fix x)) (fn-scj-no-rowsp x))
   :hints (("Goal" :induct (fn-scj-no-rowsp x)
            :in-theory (e/d (true-list-fix) (fn-scj-load-h))))))

(local
 (defthm fn-scjs-nthcdr-of-list-fix
   (equal (nthcdr v (true-list-fix r)) (true-list-fix (nthcdr v r)))
   :hints (("Goal" :induct (nthcdr v r) :in-theory (enable true-list-fix)))))

(defthm fn-scjs-no-rowsp-nthcdr-of-list-fix
  (equal (fn-scj-no-rowsp (nthcdr v (true-list-fix r)))
         (fn-scj-no-rowsp (nthcdr v r)))
  :hints (("Goal" :in-theory '(fn-scjs-no-rowsp-of-list-fix fn-scjs-nthcdr-of-list-fix))))

; A file step that keeps the history (and whether it is completing) keeps the
; seen history; the one that appends the candidate into :completing keeps it
; too: the seen history is the old one.
(defthm fn-scjs-store-seenp-of-files-framep
  (implies (fn-scjs-files-framep (fn-sn-files s) (fn-sn-files st))
           (equal (fn-scjs-store-seenp st v) (fn-scjs-store-seenp s v)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-scjs-files-framep fn-scjs-store-seenp fn-scjs-seen-records)
                                  (butlast)))))

(defthm fn-scjs-framep-of-files-framep
  (implies (and (fn-scjs-files-framep (fn-sn-files s) (fn-sn-files st))
                (equal (fn-state-articles (fn-node-acceptance (fn-sn-node st)))
                       (fn-state-articles (fn-node-acceptance (fn-sn-node s))))
                (equal (fn-sn-verdicts st) (fn-sn-verdicts s))
                (fn-scjs-store-seenp s v))
           (fn-scjs-store-framep s st v))
  :hints (("Goal" :in-theory '(fn-scjs-files-framep fn-scjs-store-framep)
           :use fn-scjs-store-seenp-of-files-framep)))

(defthm fn-scjs-sn-io-framep
  (implies (fn-scjs-store-seenp s v)
           (fn-scjs-store-framep s (fn-sn-io s operation result) v))
  :hints (("Goal" :in-theory (e/d (fn-sn-io) (fn-scjs-store-framep fn-scjs-files-framep fn-sn-update
                                             fn-sn-file-step fn-sn-statep fn-scj-no-rowsp))
           :use ((:instance fn-scjs-file-step-framep (files (fn-sn-files s)))
                 (:instance fn-scjs-framep-of-files-framep (st (fn-sn-io s operation result)))
                 (:instance fn-scjs-files-framep (files (fn-sn-files s)) (files2 (fn-sn-files s)))))))

(defthm fn-scjs-advance-txid-keeps-articles
  (equal (fn-state-articles (fn-node-acceptance (fn-replay-advance-txid node txid)))
         (fn-state-articles (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-scjs-node-prepare-keeps-articles
  (equal (fn-state-articles
          (fn-node-acceptance
           (fn-node-prepare node generation msgid payload groups
                            obligation-id subject evidence charge stamp)))
         (fn-state-articles (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare fn-accept-prepare)
                                  (fn-retain-admissiblep fn-retain-admit fn-allocate-memberships
                                   fn-selection-validp fn-acceptedp)))))

(defthm fn-scjs-node-complete-aborted-keeps-articles
  (equal (fn-state-articles
          (fn-node-acceptance (fn-node-complete node txid generation :aborted)))
         (fn-state-articles (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-node-complete fn-accept-complete fn-clear-pending))))

(defthm fn-scjs-sn-prepare-node-keeps-articles
  (equal (fn-state-articles (fn-node-acceptance (fn-sn-prepare-node node record)))
         (fn-state-articles (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare-node) (fn-node-prepare fn-replay-advance-txid)))))

(defthm fn-scjs-files-framep-reflexive
  (fn-scjs-files-framep files files)
  :hints (("Goal" :in-theory (enable fn-scjs-files-framep))))

(defthm fn-scjs-sf-prepare-record-framep
  (fn-scjs-files-framep files (fn-sf-prepare-record files record groups capacity))
  :hints (("Goal" :in-theory (e/d (fn-sf-prepare-record fn-scjs-files-framep)
                                  (fn-sf-statep fn-sf-candidatep fn-sf-history-recoverablep)))))

(defthm fn-scjs-sf-refuse-reservation-framep
  (fn-scjs-files-framep files (fn-sf-refuse-reservation files txid))
  :hints (("Goal" :in-theory (e/d (fn-sf-refuse-reservation fn-scjs-files-framep) (fn-sf-statep)))))

(defthm fn-scjs-known-abort-files-framep
  (fn-scjs-files-framep files (fn-sn-known-abort-files files))
  :hints (("Goal" :in-theory (e/d (fn-sn-known-abort-files fn-sn-known-abort-file-start
                                   fn-sf-record-file-result fn-sf-prepublish-abort
                                   fn-sf-abort-completion fn-scjs-files-framep)
                                  (fn-sf-statep)))))

(defthm fn-scjs-seen-store-framep-of-update
  (implies (and (fn-scjs-files-framep (fn-sn-files s) files)
                (equal (fn-state-articles (fn-node-acceptance node))
                       (fn-state-articles (fn-node-acceptance (fn-sn-node s))))
                (fn-scjs-store-seenp s v))
           (fn-scjs-store-framep s (fn-sn-update s files node) v))
  :hints (("Goal" :in-theory '(fn-scjs-sn-update-fields)
           :use ((:instance fn-scjs-framep-of-files-framep (st (fn-sn-update s files node)))))))

(defthm fn-scjs-store-framep-reflexive
  (implies (fn-scjs-store-seenp s v)
           (fn-scjs-store-framep s s v))
  :hints (("Goal" :in-theory (enable fn-scjs-store-framep))))

(defthm fn-scjs-snrt-step-framep
  (implies (and (not (member-equal (car event) '(:finish :crash :recover)))
                (fn-scjs-store-seenp s v))
           (fn-scjs-store-framep s (fn-snrt-step s event) v))
  :hints (("Goal" :in-theory (e/d (fn-snrt-step fn-snt-step fn-sn-prepare fn-sn-prepare-retention
                                   fn-sn-prepare-identity fn-sn-prepare-consumer fn-sn-prepare-topic
                                   fn-sn-refuse-reservation fn-sn-known-abort)
                                  (fn-scjs-store-framep fn-scjs-files-framep fn-scjs-store-seenp fn-sn-update fn-sn-io
                                   fn-sn-statep fn-sf-prepare-record fn-sf-refuse-reservation
                                   fn-sn-known-abort-files fn-sn-prepare-node fn-sn-record-bindsp
                                   fn-sn-refuse-reservation-enabledp fn-sn-known-abort-enabledp
                                   fn-replay-apply-record fn-replay-apply-retention-event
                                   fn-replay-identity-step fn-cpe-projection-step fn-th-prefix-step
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-hstxa-p fn-held-p
                                   fn-cpe-eventp fn-th-topic-eventp fn-th-topic-v1-anchorp
                                   fn-replay-advance-txid fn-node-complete fn-scj-no-rowsp
                                   fn-hc-generation fn-held-context fn-record-stamp fn-th-at
                                   fn-sn-identity-context fn-replay-composite-held)))))

; The three history facts the refresh keystone reads, as one premise.
(defun-nx fn-scjs-historyp (o)
  (let ((v (fn-own-view-version (fn-own-view o)))
        (records (fn-sf-records (fn-sn-files (fn-own-store o)))))
    (and (natp v) (<= v (len records)) (true-listp records))))

(defthm fn-scjs-historyp-of-own-relation
  (implies (fn-own-relation o) (fn-scjs-historyp o))
  :hints (("Goal" :in-theory (e/d (fn-own-relation fn-own-view-okp fn-scjs-historyp)
                                  (fn-own-conns-okp fn-own-ledger-durablep fn-own-facts-okp
                                   fn-midx-correspondencep fn-own-prefix-archive fn-ctl-visible-state
                                   fn-gidx-build fn-ctl-subseq-diff fn-own-ids-below-next-p))
           :use ((:instance fn-sf-state-records-are-true-list (s (fn-sn-files (fn-own-store o))))))))

(defthm fn-scjs-apply-identity-neutral-keeps-articles
  (implies (consp (fn-replay-apply-identity-neutral node record))
           (equal (fn-state-articles
                   (fn-node-acceptance (fn-replay-apply-identity-neutral node record)))
                  (fn-state-articles (fn-node-acceptance node))))
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-identity-neutral) (fn-replay-advance-txid)))))

(defthm fn-scjs-apply-retention-event-keeps-articles
  (implies (consp (fn-replay-apply-retention-event node record))
           (equal (fn-state-articles
                   (fn-node-acceptance (fn-replay-apply-retention-event node record)))
                  (fn-state-articles (fn-node-acceptance node))))
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-retention-event fn-replay-complete-retention
                                   fn-replay-node-with-retention)
                                  (fn-replay-advance-txid fn-retain-admissiblep fn-retain-admit
                                   fn-node-statep)))))

; A record that loads no catalog row is neither an article row nor a signed
; composite (fn-scj-load-h, books/served-catalog-join-entry.lisp).
(defthm fn-scjs-hstxa-shape
  (implies (fn-hstxa-p r)
           (and (consp r) (eq (car r) :hstxa) (fn-held-p (fn-hstxa-held r))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-hstxa-p fn-hstxa-held))))

(defthm fn-scjs-no-row-is-not-held-or-composite
  (implies (not (fn-scj-load-h r))
           (and (not (fn-held-p r)) (not (fn-hstxa-p r))))
  :hints (("Goal" :in-theory '(fn-scj-load-h fn-sca-composite-shapep (:e fn-held-p) (:e fn-hstxa-p) (:e fn-hstxa-held))
           :use (fn-scjs-hstxa-shape
                 (:instance fn-held-p-implies-cat-rowp (x r))
                 (:instance fn-held-p-implies-cat-rowp (x (fn-hstxa-held r)))))))

; The completion of a record that loads no row: the node keeps its articles
; and the verdicts are kept (the kinds are a retention, keyring snapshot,
; standalone verdict, consumer or topic event).
(defthm fn-scjs-no-row-completion-kind
  (let ((r (fn-sn-completion-record s)))
    (implies (and (fn-sn-completion-enabledp s)
                  (not (fn-scj-load-h r)))
             (and (not (fn-held-p r)) (not (fn-hstxa-p r))
                  (or (and (fn-store-retention-event-p r)
                           (consp (fn-replay-apply-retention-event (fn-sn-node s) r)))
                      (and (not (fn-store-retention-event-p r))
                           (or (fn-stxe-p r) (fn-stxk-p r) (fn-cpe-eventp r) (fn-th-topic-eventp r))
                           (consp (fn-replay-apply-record (fn-sn-node s) r)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp fn-sn-completion-core-enabledp
                                   fn-sn-record-bindsp)
                                  (fn-sn-completion-record fn-replay-apply-record
                                   fn-replay-apply-retention-event fn-held-p fn-hstxa-p
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-cpe-eventp
                                   fn-th-topic-eventp fn-sn-statep fn-replay-identity-step
                                   fn-cpe-projection-step fn-th-prefix-step fn-th-at
                                   fn-node-pending-matchesp fn-held-wire fn-sn-pending-record
                                   fn-hc-generation fn-held-context fn-scj-load-h
                                   fn-sn-identity-context))
           :use ((:instance fn-scjs-no-row-is-not-held-or-composite
                            (r (fn-sn-completion-record s)))))))

(defthm fn-scjs-apply-record-neutral-keeps-articles
  (implies (and (not (fn-store-retention-event-p r))
                (or (fn-stxe-p r) (fn-stxk-p r) (fn-cpe-eventp r) (fn-th-topic-eventp r))
                (consp (fn-replay-apply-record node r)))
           (equal (fn-state-articles (fn-node-acceptance (fn-replay-apply-record node r)))
                  (fn-state-articles (fn-node-acceptance node))))
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-record)
                                  (fn-replay-apply-identity-neutral fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-cpe-eventp fn-th-topic-eventp fn-hstxa-p
                                   fn-held-p fn-replay-advance-txid fn-node-prepare fn-node-complete)))))

(local
 (defthm fn-scjs-completion-files-keep-records
   (equal (fn-sf-records (fn-sf-emit-success (fn-sf-core-completion files seq txid) seq2 txid2))
          (fn-sf-records files))
   :hints (("Goal" :in-theory (e/d (fn-sf-emit-success fn-sf-core-completion) (fn-sf-statep))))))

(local
 (defthm fn-scjs-sn-finish-constructors
   (and (equal (fn-sn-node (fn-sn-with-topic s x)) (fn-sn-node s))
        (equal (fn-sn-verdicts (fn-sn-with-topic s x)) (fn-sn-verdicts s))
        (equal (fn-sn-files (fn-sn-with-topic s x)) (fn-sn-files s))
        (equal (fn-sn-node (fn-sn-with-consumer s x)) (fn-sn-node s))
        (equal (fn-sn-verdicts (fn-sn-with-consumer s x)) (fn-sn-verdicts s))
        (equal (fn-sn-files (fn-sn-with-consumer s x)) (fn-sn-files s))
        (equal (fn-sn-node (fn-sn-advance-identity-next s)) (fn-sn-node s))
        (equal (fn-sn-verdicts (fn-sn-advance-identity-next s)) (fn-sn-verdicts s))
        (equal (fn-sn-files (fn-sn-advance-identity-next s)) (fn-sn-files s))
        (equal (fn-sn-node (fn-sn-update-indexed s files node index)) node)
        (equal (fn-sn-verdicts (fn-sn-update-indexed s files node index)) (fn-sn-verdicts s))
        (equal (fn-sn-files (fn-sn-update-indexed s files node index)) files)
        (equal (fn-sn-node (fn-sn-finish-identity s files record node)) node)
        (equal (fn-sn-files (fn-sn-finish-identity s files record node)) files))
   :hints (("Goal" :in-theory '(fn-sn-with-topic fn-sn-with-consumer fn-sn-advance-identity-next
                                 fn-sn-update-indexed fn-sn-finish-identity fn-sn-fields-of-fn-sn-make-v6)))))

; The finish of a completion whose record loads no catalog row keeps the
; node's articles, the verdicts and the history.
(defthm fn-scjs-no-row-finish-keeps-fields
  (implies (and (fn-sn-completion-enabledp s)
                (not (fn-scj-load-h (fn-sn-completion-record s))))
           (and (equal (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-sn-finish s))))
                       (fn-state-articles (fn-node-acceptance (fn-sn-node s))))
                (equal (fn-sn-verdicts (fn-sn-finish s)) (fn-sn-verdicts s))
                (equal (fn-sf-records (fn-sn-files (fn-sn-finish s)))
                       (fn-sf-records (fn-sn-files s)))))
  :hints (("Goal" :in-theory (e/d (fn-sn-finish)
                                  (fn-sn-completion-enabledp fn-sn-completion-record fn-scj-load-h
                                   fn-replay-apply-record fn-replay-apply-retention-event
                                   fn-held-p fn-hstxa-p fn-store-retention-event-p fn-stxe-p fn-stxk-p
                                   fn-cpe-eventp fn-th-topic-eventp fn-sn-with-topic fn-sn-with-consumer
                                   fn-sn-advance-identity-next fn-sn-update-indexed fn-sn-finish-identity
                                   fn-sn-update-accepted fn-sf-emit-success fn-sf-core-completion
                                   fn-cpe-projection-step fn-th-prefix-step fn-stx-index-add
                                   fn-node-complete fn-sn-accepted-delta fn-sn-composite-delta
                                   fn-store-event-sequence fn-store-event-txid fn-cp-nth))
           :use (fn-scjs-no-row-completion-kind
                 (:instance fn-scj-identity-finish-keeps-verdicts
                            (record (fn-sn-completion-record s))
                            (files (fn-sf-emit-success
                                    (fn-sf-core-completion
                                     (fn-sn-files s)
                                     (fn-store-event-sequence (fn-sn-completion-record s))
                                     (fn-store-event-txid (fn-sn-completion-record s)))
                                    (fn-store-event-sequence (fn-sn-completion-record s))
                                    (fn-store-event-txid (fn-sn-completion-record s))))
                            (node (fn-replay-apply-record (fn-sn-node s) (fn-sn-completion-record s))))))))

(defthm fn-scjs-completion-enabled-is-completing
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sf-phase (fn-sn-files s)) :completing))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-sn-completion-enabledp fn-sn-completion-core-enabledp))))

(defthm fn-scjs-len-butlast-le
  (<= (len (butlast x n)) (len x))
  :rule-classes :linear)

(defthm fn-scjs-no-row-finish-framep
  (implies (and (fn-sn-completion-enabledp s)
                (not (fn-scj-load-h (fn-sn-completion-record s)))
                (fn-scj-no-rowsp (nthcdr v (fn-sf-records (fn-sn-files s))))
                (fn-scjs-store-seenp s v))
           (fn-scjs-store-framep s (fn-sn-finish s) v))
  :hints (("Goal" :in-theory '(fn-scjs-store-framep fn-scjs-store-seenp fn-scjs-seen-records
                               fn-scjs-len-butlast-le)
           :use (fn-scjs-no-row-finish-keeps-fields fn-scjs-completion-enabled-is-completing
                 (:instance fn-scjs-len-butlast-le (x (fn-sf-records (fn-sn-files s))) (n 1))))))

(defthm fn-scjs-spc-prepare-framep
  (implies (fn-scjs-store-seenp s v)
           (fn-scjs-store-framep s (fn-spc-prepare s record) v))
  :hints (("Goal" :in-theory (e/d (fn-spc-prepare fn-spc-stage-record fn-scjs-files-framep)
                                  (fn-scjs-store-framep fn-sn-update fn-sn-statep fn-sn-prepare-node
                                   fn-sn-record-bindsp fn-sf-candidatep fn-held-p fn-cpe-projection-step
                                   fn-scj-no-rowsp fn-hc-generation fn-held-context fn-record-stamp)))))

; KEYSTONE (the owner over a store step).  Every owner the host installs by
; replacing the store and refreshing -- fn-ocl-owner-with-store, which is
; fn-own-store-step's body, fn-rcon-ocfg-io's and the configured (:store E)
; event's (fn-psrv-store-step-is-owner-with-store) -- keeps the catalog
; invariant and the seen fact when the store step is a frame step.
(defthm fn-scjs-owner-with-store-keeps-invp
  (let ((o2 (fn-ocl-owner-with-store o st)))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (fn-scar-view-indexedp o)
                  (fn-scjs-historyp o)
                  (fn-scjs-store-framep (fn-own-store o) st (fn-own-view-version (fn-own-view o)))
                  (fn-nntp-projectionp (fn-own-view-archive (fn-own-view o2))))
             (and (fn-scj-invp o2 fn-arena fn-cat)
                  (fn-scjs-seenp o2))))
  :hints (("Goal" :in-theory '(fn-ocl-owner-with-store fn-scjs-historyp fn-own-store-of-fn-own-make
                               fn-own-view-of-fn-own-make fn-own-conns-of-fn-own-make)
           :use ((:instance fn-scjs-invp-of-store-frame
                            (o2 (fn-own-make st (fn-own-view o) (fn-own-conns o)
                                             (fn-own-next-id o) (fn-own-max-conns o)
                                             (fn-own-pending o) (fn-own-ledger-field o)
                                             (fn-own-clock o) (fn-own-facts o)
                                             (fn-own-config o) (fn-own-queue o)
                                             (fn-own-inflight o) (fn-own-feeds o)
                                             (fn-own-node-secret o) (fn-own-refused o))))))))

(local
 (defthm fn-scjs-store-step-is-owner-with-store
   (equal (fn-own-store-step o event)
          (fn-ocl-owner-with-store o (fn-snrt-step (fn-own-store o) event)))
   :hints (("Goal" :in-theory '(fn-own-store-step fn-ocl-owner-with-store)))))

(defthm fn-scjs-seenp-unfolds
  (equal (fn-scjs-seenp o)
         (fn-scjs-store-seenp (fn-own-store o) (fn-own-view-version (fn-own-view o))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-scjs-seenp))))

; The (:store E) arm for every event but the finish, a crash and recovery:
; the prepares, the reservation refusal, the known abort and every I/O word.
(defthm fn-scjs-store-step-keeps-invp
  (implies (and (fn-scj-invp o fn-arena fn-cat)
                (fn-scjs-seenp o)
                (fn-scar-view-indexedp o)
                (fn-scjs-historyp o)
                (not (member-equal (car event) '(:finish :crash :recover)))
                (fn-nntp-projectionp (fn-own-view-archive (fn-own-view (fn-own-store-step o event)))))
           (and (fn-scj-invp (fn-own-store-step o event) fn-arena fn-cat)
                (fn-scjs-seenp (fn-own-store-step o event))))
  :hints (("Goal" :in-theory '(fn-scjs-store-step-is-owner-with-store)
           :use (fn-scjs-seenp-unfolds
                 (:instance fn-scjs-snrt-step-framep (s (fn-own-store o))
                            (v (fn-own-view-version (fn-own-view o))))
                 (:instance fn-scjs-owner-with-store-keeps-invp
                            (st (fn-snrt-step (fn-own-store o) event)))))))

(defthm fn-scjs-complete-is-owner-refresh
  (equal (fn-own-complete o)
         (if (fn-sn-completion-enabledp (fn-own-store o))
             (fn-own-refresh
              (fn-own-make (fn-sn-finish (fn-own-store o)) (fn-own-view o) (fn-own-conns o)
                           (fn-own-next-id o) (fn-own-max-conns o) nil
                           (fn-sl-snoc (fn-own-ledger-field o)
                                       (fn-sf-completion (fn-sn-files (fn-own-store o))))
                           (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                           (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
                           (fn-own-node-secret o) (fn-own-refused o)))
           o))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-own-complete))))

; KEYSTONE (the completion of a record that loads no catalog row).  The
; model's completion, and through the equalities below every completion
; the host installs, keeps the catalog invariant with the catalog
; untouched when the completing record loads no row (a retention, keyring
; snapshot, standalone verdict, consumer or topic event) and the history
; the view has not seen loads none (in a reachable owner that suffix is the
; completing record alone: the view was refreshed at the last idle phase
; and only the directory's publishing observation appended since).
(defthm fn-scjs-complete-keeps-invp
  (let ((s (fn-own-store o)))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scar-view-indexedp o)
                  (fn-scjs-historyp o)
                  (not (fn-scj-load-h (fn-sn-completion-record s)))
                  (fn-scj-no-rowsp (nthcdr (fn-own-view-version (fn-own-view o))
                                           (fn-sf-records (fn-sn-files s))))
                  (fn-nntp-projectionp (fn-own-view-archive (fn-own-view (fn-own-complete o)))))
             (and (fn-scj-invp (fn-own-complete o) fn-arena fn-cat)
                  (fn-scjs-seenp (fn-own-complete o)))))
  :hints (("Goal" :in-theory '(fn-scjs-historyp fn-own-store-of-fn-own-make
                               fn-own-view-of-fn-own-make fn-own-conns-of-fn-own-make)
           :use (fn-scjs-complete-is-owner-refresh
                 fn-scjs-seenp-unfolds
                 (:instance fn-scjs-no-row-finish-framep (s (fn-own-store o))
                            (v (fn-own-view-version (fn-own-view o))))
                 (:instance fn-scjs-invp-of-store-frame
                            (o2 (fn-own-make (fn-sn-finish (fn-own-store o)) (fn-own-view o) (fn-own-conns o)
                                             (fn-own-next-id o) (fn-own-max-conns o) nil
                                             (fn-sl-snoc (fn-own-ledger-field o)
                                                         (fn-sf-completion (fn-sn-files (fn-own-store o))))
                                             (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                                             (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
                                             (fn-own-node-secret o) (fn-own-refused o))))))))

; The configured owner's (:store (:finish)) event is the same store step.
(defthm fn-scjs-store-step-finish-keeps-invp
  (let ((s (fn-own-store o)))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scar-view-indexedp o)
                  (fn-scjs-historyp o)
                  (equal (car event) :finish)
                  (not (fn-scj-load-h (fn-sn-completion-record s)))
                  (fn-scj-no-rowsp (nthcdr (fn-own-view-version (fn-own-view o))
                                           (fn-sf-records (fn-sn-files s))))
                  (fn-nntp-projectionp (fn-own-view-archive (fn-own-view (fn-own-store-step o event)))))
             (and (fn-scj-invp (fn-own-store-step o event) fn-arena fn-cat)
                  (fn-scjs-seenp (fn-own-store-step o event)))))
  :hints (("Goal" :cases ((fn-sn-completion-enabledp (fn-own-store o)))
           :in-theory '(fn-scjs-store-step-is-owner-with-store fn-snrt-step fn-snt-step
                        (:e member-equal) (:e equal))
           :use (fn-scjs-seenp-unfolds
                 (:instance fn-scjs-no-row-finish-framep (s (fn-own-store o))
                            (v (fn-own-view-version (fn-own-view o))))
                 (:instance fn-scjs-store-framep-reflexive (s (fn-own-store o))
                            (v (fn-own-view-version (fn-own-view o))))
                 (:instance fn-sn-finish (s (fn-own-store o)))
                 (:instance fn-scjs-owner-with-store-keeps-invp
                            (st (fn-sn-finish (fn-own-store o))))))))

(defthm fn-scjs-seenp-of-same-fields
  (implies (and (equal (fn-own-store o2) (fn-own-store o))
                (equal (fn-own-view o2) (fn-own-view o)))
           (equal (fn-scjs-seenp o2) (fn-scjs-seenp o)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-scjs-seenp))))

(defthm fn-scjs-begin-keeps-fields
  (and (equal (fn-own-store (fn-own-begin o id)) (fn-own-store o))
       (equal (fn-own-view (fn-own-begin o id)) (fn-own-view o))
       (equal (fn-own-conns (fn-own-begin o id)) (fn-own-conns o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-begin) ()))))

(defthm fn-scjs-begin-keeps-invp
  (and (equal (fn-scj-invp (fn-own-begin o id) fn-arena fn-cat) (fn-scj-invp o fn-arena fn-cat))
       (equal (fn-scjs-seenp (fn-own-begin o id)) (fn-scjs-seenp o)))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-begin-keeps-fields
                 (:instance fn-scjs-invp-of-same-fields (o2 (fn-own-begin o id)))
                 (:instance fn-scjs-seenp-of-same-fields (o2 (fn-own-begin o id)))))))

(defthm fn-scjs-take-submission-keeps-fields
  (and (equal (fn-own-store (fn-own-take-submission o)) (fn-own-store o))
       (equal (fn-own-view (fn-own-take-submission o)) (fn-own-view o))
       (equal (fn-own-conns (fn-own-take-submission o)) (fn-own-conns o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-take-submission) ()))))

(defthm fn-scjs-take-submission-keeps-invp
  (and (equal (fn-scj-invp (fn-own-take-submission o) fn-arena fn-cat) (fn-scj-invp o fn-arena fn-cat))
       (equal (fn-scjs-seenp (fn-own-take-submission o)) (fn-scjs-seenp o)))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-take-submission-keeps-fields
                 (:instance fn-scjs-invp-of-same-fields (o2 (fn-own-take-submission o)))
                 (:instance fn-scjs-seenp-of-same-fields (o2 (fn-own-take-submission o)))))))

(defthm fn-scjs-control-submit-keeps-fields
  (and (equal (fn-own-store (fn-own-control-submit o msgid groups octets)) (fn-own-store o))
       (equal (fn-own-view (fn-own-control-submit o msgid groups octets)) (fn-own-view o))
       (equal (fn-own-conns (fn-own-control-submit o msgid groups octets)) (fn-own-conns o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-control-submit fn-own-enqueue) (fn-own-control-submit-result fn-own-control-decision)))))

(defthm fn-scjs-control-submit-keeps-invp
  (and (equal (fn-scj-invp (fn-own-control-submit o msgid groups octets) fn-arena fn-cat) (fn-scj-invp o fn-arena fn-cat))
       (equal (fn-scjs-seenp (fn-own-control-submit o msgid groups octets)) (fn-scjs-seenp o)))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-control-submit-keeps-fields
                 (:instance fn-scjs-invp-of-same-fields (o2 (fn-own-control-submit o msgid groups octets)))
                 (:instance fn-scjs-seenp-of-same-fields (o2 (fn-own-control-submit o msgid groups octets)))))))

(defthm fn-scjs-operator-submit-keeps-fields
  (and (equal (fn-own-store (fn-own-operator-submit o msgid groups octets stored)) (fn-own-store o))
       (equal (fn-own-view (fn-own-operator-submit o msgid groups octets stored)) (fn-own-view o))
       (equal (fn-own-conns (fn-own-operator-submit o msgid groups octets stored)) (fn-own-conns o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-operator-submit fn-own-enqueue) (fn-own-operator-submit-result fn-own-operator-decision-of)))))

(defthm fn-scjs-operator-submit-keeps-invp
  (and (equal (fn-scj-invp (fn-own-operator-submit o msgid groups octets stored) fn-arena fn-cat) (fn-scj-invp o fn-arena fn-cat))
       (equal (fn-scjs-seenp (fn-own-operator-submit o msgid groups octets stored)) (fn-scjs-seenp o)))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-operator-submit-keeps-fields
                 (:instance fn-scjs-invp-of-same-fields (o2 (fn-own-operator-submit o msgid groups octets stored)))
                 (:instance fn-scjs-seenp-of-same-fields (o2 (fn-own-operator-submit o msgid groups octets stored)))))))

(defthm fn-scjs-bp-transit-submit-keeps-fields
  (and (equal (fn-own-store (fn-own-bp-transit-submit o cfg peer msgid octets id subject)) (fn-own-store o))
       (equal (fn-own-view (fn-own-bp-transit-submit o cfg peer msgid octets id subject)) (fn-own-view o))
       (equal (fn-own-conns (fn-own-bp-transit-submit o cfg peer msgid octets id subject)) (fn-own-conns o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-bp-transit-submit fn-own-enqueue) (fn-own-bp-transit-submit-result fn-peer-make-submission)))))

(defthm fn-scjs-bp-transit-submit-keeps-invp
  (and (equal (fn-scj-invp (fn-own-bp-transit-submit o cfg peer msgid octets id subject) fn-arena fn-cat) (fn-scj-invp o fn-arena fn-cat))
       (equal (fn-scjs-seenp (fn-own-bp-transit-submit o cfg peer msgid octets id subject)) (fn-scjs-seenp o)))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-bp-transit-submit-keeps-fields
                 (:instance fn-scjs-invp-of-same-fields (o2 (fn-own-bp-transit-submit o cfg peer msgid octets id subject)))
                 (:instance fn-scjs-seenp-of-same-fields (o2 (fn-own-bp-transit-submit o cfg peer msgid octets id subject)))))))

(defthm fn-scjs-observe-keeps-fields
  (and (equal (fn-own-store (fn-own-observe o obs)) (fn-own-store o))
       (equal (fn-own-view (fn-own-observe o obs)) (fn-own-view o))
       (equal (fn-own-conns (fn-own-observe o obs)) (fn-own-conns o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-observe) (fn-own-observe-outcome)))))

(defthm fn-scjs-observe-keeps-invp
  (and (equal (fn-scj-invp (fn-own-observe o obs) fn-arena fn-cat) (fn-scj-invp o fn-arena fn-cat))
       (equal (fn-scjs-seenp (fn-own-observe o obs)) (fn-scjs-seenp o)))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-observe-keeps-fields
                 (:instance fn-scjs-invp-of-same-fields (o2 (fn-own-observe o obs)))
                 (:instance fn-scjs-seenp-of-same-fields (o2 (fn-own-observe o obs)))))))

(defthm fn-scjs-declare-group-keeps-fields
  (and (equal (fn-own-store (fn-own-declare-group o name)) (fn-own-store o))
       (equal (fn-own-view (fn-own-declare-group o name)) (fn-own-view o))
       (equal (fn-own-conns (fn-own-declare-group o name)) (fn-own-conns o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-declare-group) (fn-own-replay-facts fn-own-group-fact-make)))))

(defthm fn-scjs-declare-group-keeps-invp
  (and (equal (fn-scj-invp (fn-own-declare-group o name) fn-arena fn-cat) (fn-scj-invp o fn-arena fn-cat))
       (equal (fn-scjs-seenp (fn-own-declare-group o name)) (fn-scjs-seenp o)))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-declare-group-keeps-fields
                 (:instance fn-scjs-invp-of-same-fields (o2 (fn-own-declare-group o name)))
                 (:instance fn-scjs-seenp-of-same-fields (o2 (fn-own-declare-group o name)))))))

(defthm fn-scjs-configure-keeps-fields
  (and (equal (fn-own-store (fn-own-configure o config)) (fn-own-store o))
       (equal (fn-own-view (fn-own-configure o config)) (fn-own-view o))
       (equal (fn-own-conns (fn-own-configure o config)) (fn-own-conns o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-configure) ()))))

(defthm fn-scjs-configure-keeps-invp
  (and (equal (fn-scj-invp (fn-own-configure o config) fn-arena fn-cat) (fn-scj-invp o fn-arena fn-cat))
       (equal (fn-scjs-seenp (fn-own-configure o config)) (fn-scjs-seenp o)))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-configure-keeps-fields
                 (:instance fn-scjs-invp-of-same-fields (o2 (fn-own-configure o config)))
                 (:instance fn-scjs-seenp-of-same-fields (o2 (fn-own-configure o config)))))))

(defthm fn-scjs-control-outcome-keeps-fields
  (and (equal (fn-own-store (fn-own-control-outcome o word)) (fn-own-store o))
       (equal (fn-own-view (fn-own-control-outcome o word)) (fn-own-view o))
       (equal (fn-own-conns (fn-own-control-outcome o word)) (fn-own-conns o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-control-outcome) (fn-own-outcome-completion fn-own-feed-durable fn-own-control-submissionp)))))

(defthm fn-scjs-control-outcome-keeps-invp
  (and (equal (fn-scj-invp (fn-own-control-outcome o word) fn-arena fn-cat) (fn-scj-invp o fn-arena fn-cat))
       (equal (fn-scjs-seenp (fn-own-control-outcome o word)) (fn-scjs-seenp o)))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-control-outcome-keeps-fields
                 (:instance fn-scjs-invp-of-same-fields (o2 (fn-own-control-outcome o word)))
                 (:instance fn-scjs-seenp-of-same-fields (o2 (fn-own-control-outcome o word)))))))

(defthm fn-scjs-bp-transit-outcome-keeps-fields
  (and (equal (fn-own-store (fn-own-bp-transit-outcome o word)) (fn-own-store o))
       (equal (fn-own-view (fn-own-bp-transit-outcome o word)) (fn-own-view o))
       (equal (fn-own-conns (fn-own-bp-transit-outcome o word)) (fn-own-conns o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-bp-transit-outcome fn-own-control-outcome) (fn-own-outcome-completion fn-own-feed-durable fn-own-control-submissionp fn-own-bp-transit-submissionp)))))

(defthm fn-scjs-bp-transit-outcome-keeps-invp
  (and (equal (fn-scj-invp (fn-own-bp-transit-outcome o word) fn-arena fn-cat) (fn-scj-invp o fn-arena fn-cat))
       (equal (fn-scjs-seenp (fn-own-bp-transit-outcome o word)) (fn-scjs-seenp o)))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-bp-transit-outcome-keeps-fields
                 (:instance fn-scjs-invp-of-same-fields (o2 (fn-own-bp-transit-outcome o word)))
                 (:instance fn-scjs-seenp-of-same-fields (o2 (fn-own-bp-transit-outcome o word)))))))

(defthm fn-scjs-conns-pinp-of-replace
  (implies (and (fn-scj-conns-pinp conns fn-arena fn-cat)
                (fn-scj-conn-pinp conn fn-arena fn-cat))
           (fn-scj-conns-pinp (fn-own-replace-conn conn conns) fn-arena fn-cat))
  :hints (("Goal" :induct (fn-own-replace-conn conn conns)
           :in-theory (e/d (fn-own-replace-conn fn-scj-conns-pinp) (fn-scj-conn-pinp)))))

; The connection an advance builds is pinned at the view: its catalog fact
; is the live view's.
(defthm fn-scjs-conn-pinp-of-view-conn
  (implies (fn-scj-live-okp view fn-arena fn-cat)
           (fn-scj-conn-pinp
            (fn-own-conn-make-group-indexed id (fn-own-view-version view) (fn-own-view-frontier view)
                                            wire session (fn-own-view-archive view) config observation
                                            (fn-own-view-verdicts view) (fn-own-view-index view)
                                            (fn-own-view-group-index view) (fn-own-view-control view))
            fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-scj-live-okp fn-scj-conn-pinp fn-scj-conn-pinned-index
                                   fn-scr-live-catalogp fn-scr-fields-catalogp
                                   fn-own-conn-make-group-indexed fn-own-conn-archive
                                   fn-own-conn-version fn-own-conn-index fn-own-conn-group-index
                                   fn-own-conn-control fn-served-pinned-make fn-served-pinned-version
                                   fn-own-view-live-fields)
                                  (fn-scr-catalogp fn-scr-view-of fn-own-view-live
                                   fn-own-view-version fn-own-view-archive fn-own-view-index
                                   fn-own-view-group-index fn-own-view-control fn-own-view-frontier
                                   fn-own-view-verdicts fn-gidx-pin-with-control)))))

(defthm fn-scjs-advance-keeps-invp
  (implies (fn-scj-invp o fn-arena fn-cat)
           (and (fn-scj-invp (fn-own-advance o id) fn-arena fn-cat)
                (equal (fn-scjs-seenp (fn-own-advance o id)) (fn-scjs-seenp o))))
  :hints (("Goal" :in-theory (e/d (fn-own-advance fn-own-advance-result fn-own-set-conns
                                   fn-scj-invp fn-scjs-seenp fn-scj-vvp)
                                  (fn-scj-joinp fn-scj-rows-invp fn-scj-live-okp fn-scj-conns-pinp
                                   fn-scj-conn-pinp fn-own-conn-boundedp fn-own-replace-conn
                                   fn-own-conn-make-group-indexed fn-auth-with-base fn-peer-with-base
                                   fn-post-make-session fn-nntp-set-cursor fn-nntp-open-session
                                   fn-own-find-conn fn-scj-no-rowsp fn-own-view-group-index
                                   fn-own-view-version fn-own-view-frontier fn-own-view-archive
                                   fn-own-view-verdicts fn-own-view-index fn-own-view-control)))))

(defthm fn-scjs-acar-advance-keeps-invp
  (implies (fn-scj-invp o fn-arena fn-cat)
           (and (fn-scj-invp (cdr (fn-acar-own-advance-result o id)) fn-arena fn-cat)
                (equal (fn-scjs-seenp (cdr (fn-acar-own-advance-result o id))) (fn-scjs-seenp o))))
  :hints (("Goal" :in-theory (e/d (fn-acar-own-advance-result fn-own-set-conns
                                   fn-scj-invp fn-scjs-seenp fn-scj-vvp)
                                  (fn-scj-joinp fn-scj-rows-invp fn-scj-live-okp fn-scj-conns-pinp
                                   fn-scj-conn-pinp fn-scar-conn-boundedp fn-own-replace-conn
                                   fn-own-conn-make-group-indexed fn-auth-with-base fn-peer-with-base
                                   fn-post-make-session fn-nntp-set-cursor fn-acar-open-session
                                   fn-own-find-conn fn-scj-no-rowsp fn-own-view-group-index
                                   fn-own-view-version fn-own-view-frontier fn-own-view-archive
                                   fn-own-view-verdicts fn-own-view-index fn-own-view-control)))))

(defthm fn-scjs-outcome-keeps-invp
  (implies (fn-scj-invp o fn-arena fn-cat)
           (and (fn-scj-invp (cdr (fn-own-outcome o id word)) fn-arena fn-cat)
                (equal (fn-scjs-seenp (cdr (fn-own-outcome o id word))) (fn-scjs-seenp o))))
  :hints (("Goal" :in-theory (e/d (fn-own-outcome)
                                  (fn-own-advance fn-scj-invp fn-scjs-seenp fn-own-outcome-completion
                                   fn-own-feed-durable fn-served-post-outcome fn-own-post-rendering
                                   fn-served-result-effects fn-served-make-conn-group-indexed))
           :use ((:instance fn-scjs-invp-of-same-fields
                            (o2 (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                 (fn-own-next-id o) (fn-own-max-conns o)
                                 (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                 (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                 (fn-own-config o) (fn-own-queue o) nil
                                 (if (equal (fn-own-outcome-completion o word) :durable)
                                     (fn-own-feed-durable o (fn-own-inflight o))
                                   (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o))))
                 (:instance fn-scjs-seenp-of-same-fields
                            (o2 (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                 (fn-own-next-id o) (fn-own-max-conns o)
                                 (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                 (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                 (fn-own-config o) (fn-own-queue o) nil
                                 (if (equal (fn-own-outcome-completion o word) :durable)
                                     (fn-own-feed-durable o (fn-own-inflight o))
                                   (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o))))))))

(defthm fn-scjs-transit-outcome-keeps-invp
  (implies (fn-scj-invp o fn-arena fn-cat)
           (and (fn-scj-invp (cdr (fn-own-transit-outcome o id kind reason word)) fn-arena fn-cat)
                (equal (fn-scjs-seenp (cdr (fn-own-transit-outcome o id kind reason word)))
                       (fn-scjs-seenp o))))
  :hints (("Goal" :in-theory (e/d (fn-own-transit-outcome)
                                  (fn-own-advance fn-scj-invp fn-scjs-seenp fn-own-outcome-completion
                                   fn-own-feed-durable fn-served-transit-outcome fn-own-outcome-rendering
                                   fn-served-result-effects fn-served-make-conn-group-indexed
                                   fn-peer-decision fn-own-transit-subp))
           :use ((:instance fn-scjs-invp-of-same-fields
                            (o2 (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                  (fn-own-next-id o) (fn-own-max-conns o)
                                  (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                  (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                  (fn-own-config o) (fn-own-queue o) nil
                                  (if (equal (if (equal kind :want) (fn-own-outcome-completion o word) nil)
                                             :durable)
                                      (fn-own-feed-durable o (fn-own-inflight o))
                                    (fn-own-feeds o)) (fn-own-node-secret o)
                                  (fn-own-transit-refused o (fn-own-find-conn id (fn-own-conns o))
                                                          (fn-own-inflight o) kind reason))))
                 (:instance fn-scjs-seenp-of-same-fields
                            (o2 (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                  (fn-own-next-id o) (fn-own-max-conns o)
                                  (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                  (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                  (fn-own-config o) (fn-own-queue o) nil
                                  (if (equal (if (equal kind :want) (fn-own-outcome-completion o word) nil)
                                             :durable)
                                      (fn-own-feed-durable o (fn-own-inflight o))
                                    (fn-own-feeds o)) (fn-own-node-secret o)
                                  (fn-own-transit-refused o (fn-own-find-conn id (fn-own-conns o))
                                                          (fn-own-inflight o) kind reason))))))))

; host/owner-host.lisp fn-owner-outcome installs the carried outcome.
(defthm fn-scjs-acar-own-outcome-keeps-invp
  (implies (fn-scj-invp o fn-arena fn-cat)
           (and (fn-scj-invp (cdr (fn-acar-own-outcome o id word)) fn-arena fn-cat)
                (equal (fn-scjs-seenp (cdr (fn-acar-own-outcome o id word))) (fn-scjs-seenp o))))
  :hints (("Goal" :in-theory (e/d (fn-acar-own-outcome)
                                  (fn-acar-own-advance-result fn-scj-invp fn-scjs-seenp
                                   fn-own-outcome-completion
                                   fn-own-feed-durable fn-served-post-outcome fn-own-post-rendering
                                   fn-served-result-effects fn-served-make-conn-group-indexed))
           :use ((:instance fn-scjs-invp-of-same-fields
                            (o2 (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                 (fn-own-next-id o) (fn-own-max-conns o)
                                 (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                 (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                 (fn-own-config o) (fn-own-queue o) nil
                                 (if (equal (fn-own-outcome-completion o word) :durable)
                                     (fn-own-feed-durable o (fn-own-inflight o))
                                   (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o))))
                 (:instance fn-scjs-seenp-of-same-fields
                            (o2 (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                 (fn-own-next-id o) (fn-own-max-conns o)
                                 (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                 (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                 (fn-own-config o) (fn-own-queue o) nil
                                 (if (equal (fn-own-outcome-completion o word) :durable)
                                     (fn-own-feed-durable o (fn-own-inflight o))
                                   (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o))))))))

; -----------------------------------------------------------------------------
; The owners host/owner-host.lisp installs.

; fn-owner-finish-submission: the carried finish's owner is the completion's.
(defthm fn-scjs-ccar-own-finish-keeps-invp
  (let ((s (fn-own-store o)))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scar-view-indexedp o)
                  (fn-scjs-historyp o)
                  (not (fn-scj-load-h (fn-sn-completion-record s)))
                  (fn-scj-no-rowsp (nthcdr (fn-own-view-version (fn-own-view o))
                                           (fn-sf-records (fn-sn-files s))))
                  (fn-nntp-projectionp
                   (fn-own-view-archive (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena))))))
             (and (fn-scj-invp (cdr (fn-ccar-own-finish o cfg fn-arena)) fn-arena fn-cat)
                  (fn-scjs-seenp (cdr (fn-ccar-own-finish o cfg fn-arena))))))
  :hints (("Goal" :in-theory '(fn-ccar-own-finish-is-own-finish fn-own-finish cdr-cons)
           :use fn-scjs-complete-keeps-invp)))

; The configured completion (fn-ocfg-step's (:complete)): a staged
; configuration record publishes the configuration and keeps the owner;
; otherwise the owner completes.
(defthm fn-scjs-ocfg-complete-keeps-invp
  (let* ((o (fn-ocfg-owner oc)) (s (fn-own-store o)))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scar-view-indexedp o)
                  (fn-scjs-historyp o)
                  (not (fn-scj-load-h (fn-sn-completion-record s)))
                  (fn-scj-no-rowsp (nthcdr (fn-own-view-version (fn-own-view o))
                                           (fn-sf-records (fn-sn-files s))))
                  (fn-nntp-projectionp
                   (fn-own-view-archive (fn-own-view (fn-ocfg-owner (fn-ocfg-complete oc))))))
             (and (fn-scj-invp (fn-ocfg-owner (fn-ocfg-complete oc)) fn-arena fn-cat)
                  (fn-scjs-seenp (fn-ocfg-owner (fn-ocfg-complete oc))))))
  :hints (("Goal" :in-theory '(fn-ocfg-complete fn-ocfg-owner-of-fn-ocfg-make)
           :use ((:instance fn-scjs-complete-keeps-invp (o (fn-ocfg-owner oc)))))))

; host/owner-host.lisp fn-owner-finish: fn-rix-ocfg-complete over the
; history stobj, which is the configured completion whenever the history
; stobj is the store's (fn-rix-ocfg-complete-is-ccar-ocfg-complete).
(defthm fn-scjs-rix-ocfg-complete-keeps-invp
  (let* ((o (fn-ocfg-owner oc)) (s (fn-own-store o)))
    (implies (and (fn-hist-of-storep fn-hist s)
                  (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scar-view-indexedp o)
                  (fn-scjs-historyp o)
                  (not (fn-scj-load-h (fn-sn-completion-record s)))
                  (fn-scj-no-rowsp (nthcdr (fn-own-view-version (fn-own-view o))
                                           (fn-sf-records (fn-sn-files s))))
                  (fn-nntp-projectionp
                   (fn-own-view-archive (fn-own-view (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist))))))
             (and (fn-scj-invp (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist)) fn-arena fn-cat)
                  (fn-scjs-seenp (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist))))))
  :hints (("Goal" :in-theory '(fn-rix-ocfg-complete-is-ccar-ocfg-complete fn-ccar-ocfg-complete
                               fn-ccar-own-complete-is-own-complete fn-ocfg-complete)
           :use fn-scjs-ocfg-complete-keeps-invp)))

(local
 (defthm fn-scjs-ocfg-store-step-owner
   (equal (fn-ocfg-owner (fn-ocfg-step oc (list :store ev) fn-arena))
          (fn-own-store-step (fn-ocfg-owner oc) ev))
   :hints (("Goal" :in-theory '(fn-ocfg-step fn-ocfg-pass fn-own-step fn-ocfg-owner-of-fn-ocfg-make
                                fn-ocfg-with-owner car-cons cdr-cons (:e equal))))))

; The configured (:store E) event: the host's I/O word (fn-owner-io's
; fn-rcon-ocfg-io, equal to it by fn-rcon-ocfg-io-is-ocfg-step), the
; retention and consumer prepares, the reservation refusal and the known
; abort (books/owner-prepare-outcome.lisp fn-pout-prepare-retention,
; -consumer, fn-pout-refuse-reservation, fn-pout-known-abort install exactly
; this owner).
(defthm fn-scjs-ocfg-store-step-keeps-invp
  (let ((o (fn-ocfg-owner oc)) (o2 (fn-ocfg-owner (fn-ocfg-step oc (list :store ev) fn-arena))))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scar-view-indexedp o)
                  (fn-scjs-historyp o)
                  (not (member-equal (car ev) '(:finish :crash :recover)))
                  (fn-nntp-projectionp (fn-own-view-archive (fn-own-view o2))))
             (and (fn-scj-invp o2 fn-arena fn-cat)
                  (fn-scjs-seenp o2))))
  :hints (("Goal" :in-theory '(fn-scjs-ocfg-store-step-owner)
           :use ((:instance fn-scjs-store-step-keeps-invp (o (fn-ocfg-owner oc)) (event ev))))))

; host/owner-host.lisp fn-owner-prepare: the carried article prepare
; (fn-pcar-sbud-prepare), whose owner is the owner over the store
; correspondence's prepare, or the owner unchanged at the budget.
(defthm fn-scjs-pcar-sbud-prepare-keeps-invp
  (let ((o (fn-ocfg-owner oc)) (o2 (fn-ocfg-owner (fn-pcar-sbud-prepare oc record budget))))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scar-view-indexedp o)
                  (fn-scjs-historyp o)
                  (fn-nntp-projectionp (fn-own-view-archive (fn-own-view o2))))
             (and (fn-scj-invp o2 fn-arena fn-cat)
                  (fn-scjs-seenp o2))))
  :hints (("Goal" :in-theory '(fn-pcar-sbud-prepare-is-sbud-prepare fn-sbud-prepare fn-opc-prepare
                               fn-opc-owner-prepare fn-ocfg-with-owner fn-ocfg-owner-of-fn-ocfg-make)
           :use ((:instance fn-scjs-seenp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-scjs-spc-prepare-framep (s (fn-own-store (fn-ocfg-owner oc)))
                            (v (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-scjs-owner-with-store-keeps-invp
                            (o (fn-ocfg-owner oc))
                            (st (fn-spc-prepare (fn-own-store (fn-ocfg-owner oc)) record)))
                 (:instance fn-ocl-owner-with-store
                            (o (fn-ocfg-owner oc))
                            (st (fn-spc-prepare (fn-own-store (fn-ocfg-owner oc)) record)))))))

; host/owner-host.lisp fn-owner-observe.
(defthm fn-scjs-ocfg-observe-keeps-invp
  (and (equal (fn-scj-invp (fn-ocfg-owner (fn-ocfg-observe oc obs)) fn-arena fn-cat)
              (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat))
       (equal (fn-scjs-seenp (fn-ocfg-owner (fn-ocfg-observe oc obs)))
              (fn-scjs-seenp (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory '(fn-ocfg-observe fn-ocfg-with-owner fn-ocfg-owner-of-fn-ocfg-make
                               fn-scjs-observe-keeps-invp))))

; host/owner-host.lisp fn-owner-reconfigure-complete: the live configuration
; completion.  Unstaged it is the owner's completion (above).  Staged, the
; owner is the owner over fn-cpo-configure-durable's store, and what the
; catalog needs of that store step is the frame fact, which stays NAMED:
; the replay under the grown configuration history (fn-cpr-replay) keeping
; the acceptance's articles and the verdicts is not proved (obstruction).
(defthm fn-scjs-ocl-complete-keeps-invp
  (let* ((o (fn-ocfg-owner oc)) (s (fn-own-store o))
         (v (fn-own-view-version (fn-own-view o))))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scar-view-indexedp o)
                  (fn-scjs-historyp o)
                  (if (fn-ocfg-staged oc)
                      (fn-scjs-store-framep s (fn-cpo-configure-durable s (fn-ocfg-staged oc)) v)
                    (and (not (fn-scj-load-h (fn-sn-completion-record s)))
                         (fn-scj-no-rowsp (nthcdr v (fn-sf-records (fn-sn-files s))))))
                  (fn-nntp-projectionp
                   (fn-own-view-archive (fn-own-view (fn-ocfg-owner (fn-ocl-complete oc))))))
             (and (fn-scj-invp (fn-ocfg-owner (fn-ocl-complete oc)) fn-arena fn-cat)
                  (fn-scjs-seenp (fn-ocfg-owner (fn-ocl-complete oc))))))
  :hints (("Goal" :in-theory '(fn-ocl-complete fn-ocfg-owner-of-fn-ocfg-make)
           :use ((:instance fn-scjs-complete-keeps-invp (o (fn-ocfg-owner oc)))
                 (:instance fn-scjs-owner-with-store-keeps-invp
                            (o (fn-ocfg-owner oc))
                            (st (fn-cpo-configure-durable (fn-own-store (fn-ocfg-owner oc))
                                                          (fn-ocfg-staged oc))))))))

(defthm fn-scjs-spc-stage-record-framep
  (fn-scjs-files-framep files (fn-spc-stage-record files record))
  :hints (("Goal" :in-theory (e/d (fn-spc-stage-record fn-scjs-files-framep)
                                  (fn-sf-statep fn-sf-candidatep)))))

; The carried identity prepare (host/owner-host.lisp fn-owner-prepare-identity
; installs the owner over it: books/owner-prepare-served-ocl.lisp
; fn-psrv-ccar-ocfg-prepare-identity-is-owner-with-store).
(defthm fn-scjs-ccar-sn-prepare-identity-framep
  (implies (fn-scjs-store-seenp s v)
           (fn-scjs-store-framep s (fn-ccar-sn-prepare-identity s event) v))
  :hints (("Goal" :in-theory '(fn-ccar-sn-prepare-identity fn-pcar-stage-record-is-stage-record
                               fn-scjs-store-framep-reflexive)
           :use ((:instance fn-scjs-spc-stage-record-framep (files (fn-sn-files s)) (record event))
                 (:instance fn-scjs-seen-store-framep-of-update
                            (files (fn-spc-stage-record (fn-sn-files s) event))
                            (node (fn-sn-node s)))))))

; The carried configured identity prepare (fn-psrv-prepare-identity's
; served arm; fn-pout-prepare-identity installs it over the interned row,
; fn-pout-store-of-oiis-prepare-identity).
(defthm fn-scjs-ccar-ocfg-prepare-identity-keeps-invp
  (let ((o (fn-ocfg-owner oc)) (o2 (fn-ocfg-owner (fn-ccar-ocfg-prepare-identity oc e))))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scar-view-indexedp o)
                  (fn-scjs-historyp o)
                  (fn-nntp-projectionp (fn-own-view-archive (fn-own-view o2))))
             (and (fn-scj-invp o2 fn-arena fn-cat)
                  (fn-scjs-seenp o2))))
  :hints (("Goal" :in-theory '(fn-ccar-ocfg-prepare-identity fn-ocfg-with-owner
                               fn-ocfg-owner-of-fn-ocfg-make)
           :use ((:instance fn-scjs-seenp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-scjs-ccar-sn-prepare-identity-framep
                            (s (fn-own-store (fn-ocfg-owner oc))) (event e)
                            (v (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-scjs-owner-with-store-keeps-invp
                            (o (fn-ocfg-owner oc))
                            (st (fn-ccar-sn-prepare-identity (fn-own-store (fn-ocfg-owner oc)) e)))
                 (:instance fn-ocl-owner-with-store
                            (o (fn-ocfg-owner oc))
                            (st (fn-ccar-sn-prepare-identity (fn-own-store (fn-ocfg-owner oc)) e)))))))

;; -----------------------------------------------------------------------------
;; The rows before the in-flight event (for the host's article finish): at
;; :completing the invariant and the seen fact give the rows invariant over
;; the history less its last record, and the view's version is within it.

(local
 (defun fn-scjs-take-ind (v k r)
   (if (and (posp v) (consp r))
       (fn-scjs-take-ind (1- v) (1- k) (cdr r))
     (list v k r))))

(local
 (defthm fn-scjs-take-of-take
   (implies (and (<= (nfix v) (nfix k)) (<= (nfix k) (len r)))
            (equal (fn-own-take v (take k r)) (fn-own-take v r)))
   :hints (("Goal" :induct (fn-scjs-take-ind v k r)
            :in-theory (enable fn-own-take)))))

(local
 (defthm fn-scjs-len-of-take
   (equal (len (take n l)) (nfix n))))

(local
 (defthm fn-scjs-own-take-of-short
   (implies (not (posp v)) (equal (fn-own-take v r) nil))
   :hints (("Goal" :in-theory (enable fn-own-take)))))

(local
 (defthm fn-scjs-own-take-of-butlast
   (implies (<= (nfix v) (len (butlast r 1)))
            (equal (fn-own-take v (butlast r 1)) (fn-own-take v r)))
   :hints (("Goal" :cases ((<= (len r) 1))
            :in-theory (e/d (butlast) (take fn-own-take))
            :use ((:instance fn-scjs-take-of-take (k (- (len r) 1))))))))

(defthm fn-scjs-rows-invp-before-in-flight
  (let* ((s (fn-own-store o))
         (records (fn-sf-records (fn-sn-files s)))
         (v (fn-own-view-version (fn-own-view o))))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o)
                  (equal (fn-sf-phase (fn-sn-files s)) :completing))
             (and (<= v (len (butlast records 1)))
                  (fn-scj-rows-invp fn-cat (butlast records 1)))))
  :hints (("Goal" :in-theory (e/d (fn-scj-invp fn-scjs-seenp fn-scjs-store-seenp fn-scjs-seen-records
                                   fn-scjs-historyp)
                                  (fn-scj-joinp fn-scj-rows-invp fn-scj-live-okp fn-scj-conns-pinp
                                   fn-scj-vvp butlast fn-scj-no-rowsp fn-scj-take-append-nthcdr))
           :use ((:instance fn-scj-take-append-nthcdr
                            (n (fn-own-view-version (fn-own-view o)))
                            (xs (butlast (fn-sf-records (fn-sn-files (fn-own-store o))) 1)))
                 (:instance fn-scj-rows-invp-of-no-rows
                            (c fn-cat)
                            (events (fn-own-take (fn-own-view-version (fn-own-view o))
                                                 (butlast (fn-sf-records (fn-sn-files (fn-own-store o))) 1)))
                            (extra (nthcdr (fn-own-view-version (fn-own-view o))
                                           (butlast (fn-sf-records (fn-sn-files (fn-own-store o))) 1))))))))

;; -----------------------------------------------------------------------------
;; The pinned connections' versions (books/served-catalog-join-pinned.lisp
;; fn-scj-conns-versions-atmostp) stay at most the view's version: a refresh
;; moves the view's version only up (to the history's length), the other
;; arms keep the view and the connections, and an advance re-pins at the
;; view's version.

(defun-nx fn-scjs-versionsp (o)
  (fn-scj-conns-versions-atmostp (fn-own-conns o) (fn-own-view-version (fn-own-view o))))

(defthm fn-scjs-versions-of-store-frame
  (let ((v (fn-own-view-version (fn-own-view o)))
        (records (fn-sf-records (fn-sn-files (fn-own-store o)))))
    (implies (and (fn-scjs-versionsp o)
                  (natp v)
                  (<= v (len records))
                  (true-listp records)
                  (fn-scjs-store-framep (fn-own-store o) (fn-own-store o2) v)
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o)))
             (fn-scjs-versionsp (fn-own-refresh o2))))
  :hints (("Goal" :in-theory '(fn-scjs-versionsp fn-scjs-refresh-version fn-own-refresh-keeps-fields
                               nfix natp (:e nfix) (:type-prescription len))
           :use (fn-scjs-frame-records-facts
                 (:instance fn-scj-conns-versions-atmostp-monotone
                            (conns (fn-own-conns o))
                            (m (fn-own-view-version (fn-own-view o)))
                            (n (len (fn-sf-records (fn-sn-files (fn-own-store o2))))))))))




(defthm fn-scjs-owner-with-store-keeps-versions
  (let ((o2 (fn-ocl-owner-with-store o st)))
    (implies (and (fn-scjs-versionsp o)
                  (fn-scjs-historyp o)
                  (fn-scjs-store-framep (fn-own-store o) st (fn-own-view-version (fn-own-view o))))
             (fn-scjs-versionsp o2)))
  :hints (("Goal" :in-theory '(fn-ocl-owner-with-store fn-scjs-historyp fn-own-store-of-fn-own-make
                               fn-own-view-of-fn-own-make fn-own-conns-of-fn-own-make)
           :use ((:instance fn-scjs-versions-of-store-frame
                            (o2 (fn-own-make st (fn-own-view o) (fn-own-conns o)
                                             (fn-own-next-id o) (fn-own-max-conns o)
                                             (fn-own-pending o) (fn-own-ledger-field o)
                                             (fn-own-clock o) (fn-own-facts o)
                                             (fn-own-config o) (fn-own-queue o)
                                             (fn-own-inflight o) (fn-own-feeds o)
                                             (fn-own-node-secret o) (fn-own-refused o))))))))

(defthm fn-scjs-store-step-keeps-versions
  (implies (and (fn-scjs-versionsp o)
                (fn-scjs-seenp o)
                (fn-scjs-historyp o)
                (not (member-equal (car event) '(:finish :crash :recover))))
           (fn-scjs-versionsp (fn-own-store-step o event)))
  :hints (("Goal" :in-theory '(fn-scjs-store-step-is-owner-with-store)
           :use (fn-scjs-seenp-unfolds
                 (:instance fn-scjs-snrt-step-framep (s (fn-own-store o))
                            (v (fn-own-view-version (fn-own-view o))))
                 (:instance fn-scjs-owner-with-store-keeps-versions
                            (st (fn-snrt-step (fn-own-store o) event)))))))

(defthm fn-scjs-complete-keeps-versions
  (let ((s (fn-own-store o)))
    (implies (and (fn-scjs-versionsp o)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o)
                  (not (fn-scj-load-h (fn-sn-completion-record s)))
                  (fn-scj-no-rowsp (nthcdr (fn-own-view-version (fn-own-view o))
                                           (fn-sf-records (fn-sn-files s)))))
             (fn-scjs-versionsp (fn-own-complete o))))
  :hints (("Goal" :in-theory '(fn-scjs-historyp fn-own-store-of-fn-own-make
                               fn-own-view-of-fn-own-make fn-own-conns-of-fn-own-make)
           :use (fn-scjs-complete-is-owner-refresh
                 fn-scjs-seenp-unfolds
                 (:instance fn-scjs-no-row-finish-framep (s (fn-own-store o))
                            (v (fn-own-view-version (fn-own-view o))))
                 (:instance fn-scjs-versions-of-store-frame
                            (o2 (fn-own-make (fn-sn-finish (fn-own-store o)) (fn-own-view o) (fn-own-conns o)
                                             (fn-own-next-id o) (fn-own-max-conns o) nil
                                             (fn-sl-snoc (fn-own-ledger-field o)
                                                         (fn-sf-completion (fn-sn-files (fn-own-store o))))
                                             (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                                             (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
                                             (fn-own-node-secret o) (fn-own-refused o))))))))

(defthm fn-scjs-store-step-finish-keeps-versions
  (let ((s (fn-own-store o)))
    (implies (and (fn-scjs-versionsp o)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o)
                  (equal (car event) :finish)
                  (not (fn-scj-load-h (fn-sn-completion-record s)))
                  (fn-scj-no-rowsp (nthcdr (fn-own-view-version (fn-own-view o))
                                           (fn-sf-records (fn-sn-files s)))))
             (fn-scjs-versionsp (fn-own-store-step o event))))
  :hints (("Goal" :cases ((fn-sn-completion-enabledp (fn-own-store o)))
           :in-theory '(fn-scjs-store-step-is-owner-with-store fn-snrt-step fn-snt-step
                        (:e member-equal) (:e equal))
           :use (fn-scjs-seenp-unfolds
                 (:instance fn-scjs-no-row-finish-framep (s (fn-own-store o))
                            (v (fn-own-view-version (fn-own-view o))))
                 (:instance fn-scjs-store-framep-reflexive (s (fn-own-store o))
                            (v (fn-own-view-version (fn-own-view o))))
                 (:instance fn-sn-finish (s (fn-own-store o)))
                 (:instance fn-scjs-owner-with-store-keeps-versions
                            (st (fn-sn-finish (fn-own-store o))))))))

(defthm fn-scjs-ccar-own-finish-keeps-versions
  (let ((s (fn-own-store o)))
    (implies (and (fn-scjs-versionsp o)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o)
                  (not (fn-scj-load-h (fn-sn-completion-record s)))
                  (fn-scj-no-rowsp (nthcdr (fn-own-view-version (fn-own-view o))
                                           (fn-sf-records (fn-sn-files s)))))
             (fn-scjs-versionsp (cdr (fn-ccar-own-finish o cfg fn-arena)))))
  :hints (("Goal" :in-theory '(fn-ccar-own-finish-is-own-finish fn-own-finish cdr-cons)
           :use fn-scjs-complete-keeps-versions)))

(defthm fn-scjs-ocfg-complete-keeps-versions
  (let* ((o (fn-ocfg-owner oc)) (s (fn-own-store o)))
    (implies (and (fn-scjs-versionsp o)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o)
                  (not (fn-scj-load-h (fn-sn-completion-record s)))
                  (fn-scj-no-rowsp (nthcdr (fn-own-view-version (fn-own-view o))
                                           (fn-sf-records (fn-sn-files s)))))
             (fn-scjs-versionsp (fn-ocfg-owner (fn-ocfg-complete oc)))))
  :hints (("Goal" :in-theory '(fn-ocfg-complete fn-ocfg-owner-of-fn-ocfg-make)
           :use ((:instance fn-scjs-complete-keeps-versions (o (fn-ocfg-owner oc)))))))

(defthm fn-scjs-rix-ocfg-complete-keeps-versions
  (let* ((o (fn-ocfg-owner oc)) (s (fn-own-store o)))
    (implies (and (fn-hist-of-storep fn-hist s)
                  (fn-scjs-versionsp o)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o)
                  (not (fn-scj-load-h (fn-sn-completion-record s)))
                  (fn-scj-no-rowsp (nthcdr (fn-own-view-version (fn-own-view o))
                                           (fn-sf-records (fn-sn-files s)))))
             (fn-scjs-versionsp (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist)))))
  :hints (("Goal" :in-theory '(fn-rix-ocfg-complete-is-ccar-ocfg-complete fn-ccar-ocfg-complete
                               fn-ccar-own-complete-is-own-complete fn-ocfg-complete)
           :use fn-scjs-ocfg-complete-keeps-versions)))

(defthm fn-scjs-ocfg-store-step-keeps-versions
  (let ((o (fn-ocfg-owner oc)) (o2 (fn-ocfg-owner (fn-ocfg-step oc (list :store ev) fn-arena))))
    (implies (and (fn-scjs-versionsp o)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o)
                  (not (member-equal (car ev) '(:finish :crash :recover))))
             (fn-scjs-versionsp o2)))
  :hints (("Goal" :in-theory '(fn-scjs-ocfg-store-step-owner)
           :use ((:instance fn-scjs-store-step-keeps-versions (o (fn-ocfg-owner oc)) (event ev))))))

(defthm fn-scjs-pcar-sbud-prepare-keeps-versions
  (let ((o (fn-ocfg-owner oc)) (o2 (fn-ocfg-owner (fn-pcar-sbud-prepare oc record budget))))
    (implies (and (fn-scjs-versionsp o)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o))
             (fn-scjs-versionsp o2)))
  :hints (("Goal" :in-theory '(fn-pcar-sbud-prepare-is-sbud-prepare fn-sbud-prepare fn-opc-prepare
                               fn-opc-owner-prepare fn-ocfg-with-owner fn-ocfg-owner-of-fn-ocfg-make)
           :use ((:instance fn-scjs-seenp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-scjs-spc-prepare-framep (s (fn-own-store (fn-ocfg-owner oc)))
                            (v (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-scjs-owner-with-store-keeps-versions
                            (o (fn-ocfg-owner oc))
                            (st (fn-spc-prepare (fn-own-store (fn-ocfg-owner oc)) record)))
                 (:instance fn-ocl-owner-with-store
                            (o (fn-ocfg-owner oc))
                            (st (fn-spc-prepare (fn-own-store (fn-ocfg-owner oc)) record)))))))

(defthm fn-scjs-ocl-complete-keeps-versions
  (let* ((o (fn-ocfg-owner oc)) (s (fn-own-store o))
         (v (fn-own-view-version (fn-own-view o))))
    (implies (and (fn-scjs-versionsp o)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o)
                  (if (fn-ocfg-staged oc)
                      (fn-scjs-store-framep s (fn-cpo-configure-durable s (fn-ocfg-staged oc)) v)
                    (and (not (fn-scj-load-h (fn-sn-completion-record s)))
                         (fn-scj-no-rowsp (nthcdr v (fn-sf-records (fn-sn-files s)))))))
             (fn-scjs-versionsp (fn-ocfg-owner (fn-ocl-complete oc)))))
  :hints (("Goal" :in-theory '(fn-ocl-complete fn-ocfg-owner-of-fn-ocfg-make)
           :use ((:instance fn-scjs-complete-keeps-versions (o (fn-ocfg-owner oc)))
                 (:instance fn-scjs-owner-with-store-keeps-versions
                            (o (fn-ocfg-owner oc))
                            (st (fn-cpo-configure-durable (fn-own-store (fn-ocfg-owner oc))
                                                          (fn-ocfg-staged oc))))))))

(defthm fn-scjs-ccar-ocfg-prepare-identity-keeps-versions
  (let ((o (fn-ocfg-owner oc)) (o2 (fn-ocfg-owner (fn-ccar-ocfg-prepare-identity oc e))))
    (implies (and (fn-scjs-versionsp o)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o))
             (fn-scjs-versionsp o2)))
  :hints (("Goal" :in-theory '(fn-ccar-ocfg-prepare-identity fn-ocfg-with-owner
                               fn-ocfg-owner-of-fn-ocfg-make)
           :use ((:instance fn-scjs-seenp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-scjs-ccar-sn-prepare-identity-framep
                            (s (fn-own-store (fn-ocfg-owner oc))) (event e)
                            (v (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-scjs-owner-with-store-keeps-versions
                            (o (fn-ocfg-owner oc))
                            (st (fn-ccar-sn-prepare-identity (fn-own-store (fn-ocfg-owner oc)) e)))
                 (:instance fn-ocl-owner-with-store
                            (o (fn-ocfg-owner oc))
                            (st (fn-ccar-sn-prepare-identity (fn-own-store (fn-ocfg-owner oc)) e)))))))

(defthm fn-scjs-versionsp-of-same-fields
  (implies (and (equal (fn-own-view o2) (fn-own-view o))
                (equal (fn-own-conns o2) (fn-own-conns o)))
           (equal (fn-scjs-versionsp o2) (fn-scjs-versionsp o)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-scjs-versionsp))))


(defthm fn-scjs-begin-keeps-versions
  (equal (fn-scjs-versionsp (fn-own-begin o id)) (fn-scjs-versionsp o))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-begin-keeps-fields
                 (:instance fn-scjs-versionsp-of-same-fields (o2 (fn-own-begin o id)))))))


(defthm fn-scjs-take-submission-keeps-versions
  (equal (fn-scjs-versionsp (fn-own-take-submission o)) (fn-scjs-versionsp o))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-take-submission-keeps-fields
                 (:instance fn-scjs-versionsp-of-same-fields (o2 (fn-own-take-submission o)))))))


(defthm fn-scjs-control-submit-keeps-versions
  (equal (fn-scjs-versionsp (fn-own-control-submit o msgid groups octets)) (fn-scjs-versionsp o))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-control-submit-keeps-fields
                 (:instance fn-scjs-versionsp-of-same-fields (o2 (fn-own-control-submit o msgid groups octets)))))))


(defthm fn-scjs-operator-submit-keeps-versions
  (equal (fn-scjs-versionsp (fn-own-operator-submit o msgid groups octets stored)) (fn-scjs-versionsp o))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-operator-submit-keeps-fields
                 (:instance fn-scjs-versionsp-of-same-fields (o2 (fn-own-operator-submit o msgid groups octets stored)))))))


(defthm fn-scjs-bp-transit-submit-keeps-versions
  (equal (fn-scjs-versionsp (fn-own-bp-transit-submit o cfg peer msgid octets id subject)) (fn-scjs-versionsp o))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-bp-transit-submit-keeps-fields
                 (:instance fn-scjs-versionsp-of-same-fields (o2 (fn-own-bp-transit-submit o cfg peer msgid octets id subject)))))))


(defthm fn-scjs-observe-keeps-versions
  (equal (fn-scjs-versionsp (fn-own-observe o obs)) (fn-scjs-versionsp o))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-observe-keeps-fields
                 (:instance fn-scjs-versionsp-of-same-fields (o2 (fn-own-observe o obs)))))))


(defthm fn-scjs-declare-group-keeps-versions
  (equal (fn-scjs-versionsp (fn-own-declare-group o name)) (fn-scjs-versionsp o))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-declare-group-keeps-fields
                 (:instance fn-scjs-versionsp-of-same-fields (o2 (fn-own-declare-group o name)))))))


(defthm fn-scjs-configure-keeps-versions
  (equal (fn-scjs-versionsp (fn-own-configure o config)) (fn-scjs-versionsp o))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-configure-keeps-fields
                 (:instance fn-scjs-versionsp-of-same-fields (o2 (fn-own-configure o config)))))))


(defthm fn-scjs-control-outcome-keeps-versions
  (equal (fn-scjs-versionsp (fn-own-control-outcome o word)) (fn-scjs-versionsp o))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-control-outcome-keeps-fields
                 (:instance fn-scjs-versionsp-of-same-fields (o2 (fn-own-control-outcome o word)))))))


(defthm fn-scjs-bp-transit-outcome-keeps-versions
  (equal (fn-scjs-versionsp (fn-own-bp-transit-outcome o word)) (fn-scjs-versionsp o))
  :hints (("Goal" :in-theory nil
           :use (fn-scjs-bp-transit-outcome-keeps-fields
                 (:instance fn-scjs-versionsp-of-same-fields (o2 (fn-own-bp-transit-outcome o word)))))))


(defthm fn-scjs-ocfg-observe-keeps-versions
  (equal (fn-scjs-versionsp (fn-ocfg-owner (fn-ocfg-observe oc obs)))
         (fn-scjs-versionsp (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory '(fn-ocfg-observe fn-ocfg-with-owner fn-ocfg-owner-of-fn-ocfg-make
                               fn-scjs-observe-keeps-versions))))

(defthm fn-scjs-versions-of-replace
  (implies (and (fn-scj-conns-versions-atmostp conns n)
                (<= (nfix (fn-own-conn-version conn)) (nfix n)))
           (fn-scj-conns-versions-atmostp (fn-own-replace-conn conn conns) n))
  :hints (("Goal" :induct (fn-own-replace-conn conn conns)
           :in-theory (enable fn-own-replace-conn fn-scj-conns-versions-atmostp))))

(defthm fn-scjs-advance-keeps-versions
  (implies (fn-scjs-versionsp o)
           (fn-scjs-versionsp (fn-own-advance o id)))
  :hints (("Goal" :in-theory (e/d (fn-own-advance fn-own-advance-result fn-own-set-conns fn-scjs-versionsp
                                   fn-own-conn-make-group-indexed fn-own-conn-version)
                                  (fn-scj-conns-versions-atmostp fn-own-conn-boundedp fn-own-replace-conn
                                   fn-auth-with-base fn-peer-with-base
                                   fn-post-make-session fn-nntp-set-cursor fn-nntp-open-session
                                   fn-own-find-conn fn-own-view-group-index
                                   fn-own-view-version fn-own-view-frontier fn-own-view-archive
                                   fn-own-view-verdicts fn-own-view-index fn-own-view-control)))))

(defthm fn-scjs-acar-advance-keeps-versions
  (implies (fn-scjs-versionsp o)
           (fn-scjs-versionsp (cdr (fn-acar-own-advance-result o id))))
  :hints (("Goal" :in-theory (e/d (fn-acar-own-advance-result fn-own-set-conns fn-scjs-versionsp
                                   fn-own-conn-make-group-indexed fn-own-conn-version)
                                  (fn-scj-conns-versions-atmostp fn-scar-conn-boundedp fn-own-replace-conn
                                   fn-auth-with-base fn-peer-with-base
                                   fn-post-make-session fn-nntp-set-cursor fn-acar-open-session
                                   fn-own-find-conn fn-own-view-group-index
                                   fn-own-view-version fn-own-view-frontier fn-own-view-archive
                                   fn-own-view-verdicts fn-own-view-index fn-own-view-control)))))


(defthm fn-scjs-outcome-keeps-versions
  (implies (fn-scjs-versionsp o)
           (fn-scjs-versionsp (cdr (fn-own-outcome o id word))))
  :hints (("Goal" :in-theory (e/d (fn-own-outcome)
                                  (fn-own-advance fn-scjs-versionsp fn-own-outcome-completion
                                   fn-own-feed-durable fn-served-post-outcome fn-own-post-rendering
                                   fn-served-result-effects fn-served-make-conn-group-indexed))
           :use ((:instance fn-scjs-versionsp-of-same-fields
                            (o2 (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                 (fn-own-next-id o) (fn-own-max-conns o)
                                 (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                 (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                 (fn-own-config o) (fn-own-queue o) nil
                                 (if (equal (fn-own-outcome-completion o word) :durable)
                                     (fn-own-feed-durable o (fn-own-inflight o))
                                   (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o))))))))

(defthm fn-scjs-transit-outcome-keeps-versions
  (implies (fn-scjs-versionsp o)
           (fn-scjs-versionsp (cdr (fn-own-transit-outcome o id kind reason word))))
  :hints (("Goal" :in-theory (e/d (fn-own-transit-outcome)
                                  (fn-own-advance fn-scjs-versionsp fn-own-outcome-completion
                                   fn-own-feed-durable fn-served-transit-outcome fn-own-outcome-rendering
                                   fn-served-result-effects fn-served-make-conn-group-indexed
                                   fn-peer-decision fn-own-transit-subp))
           :use ((:instance fn-scjs-versionsp-of-same-fields
                            (o2 (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                  (fn-own-next-id o) (fn-own-max-conns o)
                                  (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                  (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                  (fn-own-config o) (fn-own-queue o) nil
                                  (if (equal (if (equal kind :want) (fn-own-outcome-completion o word) nil)
                                             :durable)
                                      (fn-own-feed-durable o (fn-own-inflight o))
                                    (fn-own-feeds o)) (fn-own-node-secret o)
                                  (fn-own-transit-refused o (fn-own-find-conn id (fn-own-conns o))
                                                          (fn-own-inflight o) kind reason))))))))

(defthm fn-scjs-acar-own-outcome-keeps-versions
  (implies (fn-scjs-versionsp o)
           (fn-scjs-versionsp (cdr (fn-acar-own-outcome o id word))))
  :hints (("Goal" :in-theory (e/d (fn-acar-own-outcome)
                                  (fn-acar-own-advance-result fn-scjs-versionsp
                                   fn-own-outcome-completion
                                   fn-own-feed-durable fn-served-post-outcome fn-own-post-rendering
                                   fn-served-result-effects fn-served-make-conn-group-indexed))
           :use ((:instance fn-scjs-versionsp-of-same-fields
                            (o2 (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                 (fn-own-next-id o) (fn-own-max-conns o)
                                 (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                 (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                 (fn-own-config o) (fn-own-queue o) nil
                                 (if (equal (fn-own-outcome-completion o word) :durable)
                                     (fn-own-feed-durable o (fn-own-inflight o))
                                   (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o))))))))

(in-theory (disable fn-scjs-seenp fn-scjs-store-seenp fn-scjs-seen-records fn-scjs-store-framep
                    fn-scjs-files-framep fn-scjs-historyp fn-scjs-versionsp))
