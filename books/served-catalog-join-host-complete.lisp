; served-catalog-join-host-complete.lisp -- the catalog join carried across
; the host's completions that load no catalog row (lane join-f2, 2026-09-28;
; PRF-302).
;
; host/owner-host.lisp fn-owner-finish (and fn-owner-finish-identity without a
; pending row) installs fn-rix-ocfg-complete's owner: the completion of a
; retention, consumer, topic or keyring event, which the catalog does not see.
; With no pending row, LINK says the completing record loads no catalog row,
; so fn-sjh-okp holds after with none.

(in-package "ACL2")

(include-book "served-catalog-join-host-finish")
(include-book "served-catalog-join-host-post")

(local (in-theory (disable (tau-system))))

(defthm fn-sjh-rix-complete-owner
  (implies (and (fn-hist-of-storep fn-hist (fn-own-store (fn-ocfg-owner oc)))
                (not (fn-ocfg-staged oc)))
           (equal (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist))
                  (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena))))
  :hints (("Goal" :in-theory '(fn-rix-ocfg-complete-is-ccar-ocfg-complete fn-ccar-ocfg-complete
                               fn-ccar-own-complete-is-own-complete fn-ccar-own-finish-is-own-finish
                               fn-own-finish fn-ocfg-owner-of-fn-ocfg-make cdr-cons))))

(defthm fn-sjh-no-rows-of-snoc
  (equal (fn-scj-no-rowsp (append x (list r)))
         (and (fn-scj-no-rowsp x) (not (fn-scj-load-h r))))
  :hints (("Goal" :induct (fn-scj-no-rowsp x) :in-theory (e/d (fn-scj-no-rowsp) (fn-scj-load-h)))))

(defthm fn-sjh-nthcdr-of-snoc
  (implies (<= (nfix v) (len x))
           (equal (nthcdr v (append x (list r))) (append (nthcdr v x) (list r))))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm fn-sjh-butlast-snoc-last
  (implies (and (consp x) (true-listp x))
           (equal (append (butlast x 1) (list (car (last x)))) x))
  :hints (("Goal" :induct (len x))))

; At a completion with no pending row, nothing past the view loads a row.
(defthm fn-sjh-no-row-completion-facts
  (let* ((s (fn-own-store o))
         (records (fn-sf-records (fn-sn-files s))))
    (implies (and (fn-sjh-okp o nil fn-arena fn-cat)
                  (fn-sn-statep s)
                  (fn-ccar-completion-enabledp s))
             (and (not (fn-scj-load-h (fn-sn-completion-record s)))
                  (fn-scj-no-rowsp (nthcdr (fn-own-view-version (fn-own-view o)) records)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sjh-okp fn-sjh-files-okp fn-sjh-files-linkp fn-sjh-inflight fn-sf-record-phasep
                            fn-scjs-seenp fn-scjs-store-seenp fn-scjs-seen-records fn-scjs-historyp)
                           (fn-ccar-completion-enabledp fn-sn-completion-record fn-scj-load-h
                            fn-scj-no-rowsp fn-sn-statep nthcdr butlast last))
           :use ((:instance fn-scj-enabled-is-completing (s (fn-own-store o)))
                 (:instance fn-sjh-completion-record-is-last (s (fn-own-store o)))
                 (:instance fn-ccar-completion-record-is-completion-record (s (fn-own-store o)))
                 (:instance fn-sjh-butlast-snoc-last (x (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-sjh-nthcdr-of-snoc
                            (v (fn-own-view-version (fn-own-view o)))
                            (x (butlast (fn-sf-records (fn-sn-files (fn-own-store o))) 1))
                            (r (car (last (fn-sf-records (fn-sn-files (fn-own-store o)))))))
                 (:instance fn-sjh-no-rows-of-snoc
                            (x (nthcdr (fn-own-view-version (fn-own-view o))
                                       (butlast (fn-sf-records (fn-sn-files (fn-own-store o))) 1)))
                            (r (car (last (fn-sf-records (fn-sn-files (fn-own-store o)))))))))))

; KEYSTONE (a completion the catalog does not see): host/owner-host.lisp
; fn-owner-finish installs fn-rix-ocfg-complete's owner (the history stobj
; synchronized to the store first, no configuration staged); with no pending
; row the completing record loads no catalog row, and fn-sjh-okp holds after.
(defthm fn-sjh-okp-at-owner-finish-no-row
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (o2 (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist))))
    (implies (and (fn-hist-of-storep fn-hist s)
                  (not (fn-ocfg-staged oc))
                  (fn-ocl-relation oc)
                  (fn-sjh-okp o nil fn-arena fn-cat)
                  (fn-ccar-completion-enabledp s)
                  (fn-statep (fn-own-view-archive (fn-own-view o2))))
             (fn-sjh-okp o2 nil fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-okp-when-parts fn-sjh-versionsp-is-versions-okp
                                        fn-ccar-ocl-relation-carries-sn-statep)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)) (pending nil))
                 (:instance fn-sjh-no-row-completion-facts (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-rix-complete-owner (cfg nil))
                 (:instance fn-scjs-rix-ocfg-complete-keeps-invp)
                 (:instance fn-scjs-rix-ocfg-complete-keeps-versions)
                 (:instance fn-sjh-finish-side-facts (o (fn-ocfg-owner oc)) (cfg nil) (c2 fn-cat))
                 (:instance fn-sjh-finish-store-image (o (fn-ocfg-owner oc)) (cfg nil))
                 (:instance fn-sjh-finish-keeps-view-indexed (o (fn-ocfg-owner oc)) (cfg nil))))))

(defthm fn-sjh-prepare-event-staging
  (implies (and (member-equal (car ev) '(:prepare-retention :prepare-consumer :prepare-topic))
                (not (equal (fn-snrt-step s ev) s)))
           (let ((f2 (fn-sn-files (fn-snrt-step s ev))))
             (and (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                  (equal (fn-sf-phase f2) :record-staged)
                  (equal (fn-sf-records f2) (fn-sf-records (fn-sn-files s)))
                  (equal (fn-sf-record-candidate f2) (cadr ev)))))
  :hints (("Goal" :in-theory (e/d (fn-snrt-step fn-sn-prepare-retention fn-sn-prepare-consumer
                                   fn-sn-prepare-topic fn-sf-prepare-record fn-sjh-sn-update-files)
                                  (fn-sf-statep fn-sn-statep fn-sf-candidatep fn-sf-history-recoverablep
                                   fn-sn-update fn-cpe-projection-step fn-replay-apply-retention-event
                                   fn-th-prefix-step fn-store-retention-event-p fn-cpe-eventp
                                   fn-th-topic-eventp)))))

(defthm fn-sjh-other-event-row-facts
  (implies (or (fn-store-retention-event-p e) (fn-cpe-eventp e) (fn-th-topic-eventp e))
           (and (not (fn-scj-load-h e))
                (fn-row-composite-okp e fn-arena)
                (fn-rows-handles-inp (list e) fn-arena)
                (fn-scj-rows-clearp (list e))))
  :hints (("Goal" :in-theory (enable fn-scj-load-h fn-row-composite-okp fn-rows-handles-inp
                                     fn-scj-rows-clearp fn-sca-composite-shapep fn-cat-rowp fn-held-shapep
                                     fn-hstxa-p fn-held-p fn-stxa-p fn-stxa-shapep
                                     fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp))))

(defthm fn-sjh-files-okp-of-staged-no-row
  (implies (and (fn-sjh-files-okp files pending fn-arena fn-cat)
                (equal (fn-sf-phase files) :reserved)
                (equal (fn-sf-phase files2) :record-staged)
                (equal (fn-sf-records files2) (fn-sf-records files))
                (not (fn-scj-load-h (fn-sf-record-candidate files2)))
                (fn-row-composite-okp (fn-sf-record-candidate files2) fn-arena)
                (fn-rows-handles-inp (list (fn-sf-record-candidate files2)) fn-arena)
                (fn-scj-rows-clearp (list (fn-sf-record-candidate files2))))
           (fn-sjh-files-okp files2 nil fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-sjh-files-okp fn-sjh-files-linkp fn-sjh-inflight fn-sf-record-phasep)
                                  (fn-row-composite-okp fn-rows-composites-okp fn-rows-handles-inp
                                   fn-scj-rows-clearp fn-scj-load-h)))))

; KEYSTONE (the retention, consumer and topic prepares): the store stages an
; event that loads no catalog row; fn-sjh-okp with no pending row.
(defthm fn-sjh-okp-of-other-prepare
  (let* ((o (fn-ocfg-owner oc))
         (o2 (fn-ocfg-owner (fn-ocfg-step oc (list :store ev) fn-arena))))
    (implies (and (member-equal (car ev) '(:prepare-retention :prepare-consumer :prepare-topic))
                  (or (fn-store-retention-event-p (cadr ev)) (fn-cpe-eventp (cadr ev))
                      (fn-th-topic-eventp (cadr ev)))
                  (not (equal (fn-snrt-step (fn-own-store o) ev) (fn-own-store o)))
                  (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  (fn-statep (fn-own-view-archive (fn-own-view o2))))
             (fn-sjh-okp o2 nil fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-ocfg-store-step-owner fn-sjh-okp-of-store-step-parts
                                        fn-sjh-store-step-store (:e member-equal) member-equal)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-is-parts (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-prepare-event-staging (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-sjh-other-event-row-facts (e (cadr ev)))
                 (:instance fn-sjh-files-okp-of-staged-no-row
                            (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                            (files2 (fn-sn-files (fn-snrt-step (fn-own-store (fn-ocfg-owner oc)) ev))))
                 (:instance fn-scjs-ocfg-store-step-keeps-invp)
                 (:instance fn-scjs-ocfg-store-step-keeps-versions)
                 (:instance fn-sjh-store-step-historyp (o (fn-ocfg-owner oc)))
                 (:instance fn-oix-ocfg-step-keeps-view-indexed (event (list :store ev)))))))
