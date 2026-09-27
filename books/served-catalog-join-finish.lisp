; served-catalog-join-finish.lisp -- the catalog's rows against the store's
; history, carried across the host's finish (lane sca-join-3, 2026-09-27;
; PRF-302, step 2 of the join's discharge).
;
; The row relation (fn-scj-acc-rowsp) reads a catalog only through its rows
; read as articles (fn-scj-arts-map: Message-ID, handle, groups, numbers,
; stamp; never a withdrawal mark).  The invariant the host's catalog
; carries is fn-scj-rows-invp: its rows as articles are those of the load of
; the store's history (fn-sca-load-held-rows-from over the rows, any index).
; It holds at every open (the catalog IS that load), and the host's finish
; (fn-sca-finish, T4 then T2) keeps it when the pending row is the loaded row
; of the event the store appended (the finish link, fn-scj-finish-keeps-
; rows-invp).  At an idle store in the live relation it gives the row
; relation with the store's acceptance (fn-scj-acc-rowsp-of-rows-invp), hence
; the row equation of fn-scj-joinp-of-article-finish at the host's finish.

(in-package "ACL2")

(include-book "served-catalog-join-entry")

(local (in-theory (disable fn-nntp-article-idp-is-consp fn-scat-article-idp-is-msgid-idp
                           fn-scat-msgid-idp fn-nntp-index-msgid-okp-stringp
                           fn-nntp-index-msgid-okp fn-cp-id-length-bound)))

; -----------------------------------------------------------------------------
; The row relation reads the rows as articles only.

(defun fn-scj-art-number-in (g a)
  (declare (xargs :guard t))
  (let ((pair (fn-cat-assoc g (fn-article-memberships a))))
    (if (consp pair) (cdr pair) nil)))

(defun fn-scj-arts-high (g arts)
  (declare (xargs :guard t))
  (if (consp arts)
      (max (nfix (fn-scj-art-number-in g (car arts)))
           (fn-scj-arts-high g (cdr arts)))
    0))

(defthm fn-scj-group-high-is-arts-high
  (equal (fn-cat-group-high g c) (fn-scj-arts-high g (fn-scj-arts-map c)))
  :hints (("Goal" :in-theory (enable fn-held-number-in fn-scj-row-art))))

(defun fn-scj-arts-keys-inp (arts names)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp arts)
      (and (fn-scj-keys-inp (fn-article-memberships (car arts)) names)
           (fn-scj-arts-keys-inp (cdr arts) names))
    t))

(defthm fn-scj-rows-keys-inp-is-arts-keys-inp
  (equal (fn-scj-rows-keys-inp c names) (fn-scj-arts-keys-inp (fn-scj-arts-map c) names))
  :hints (("Goal" :in-theory (enable fn-scj-row-art))))

(defthm fn-scj-nexts-matchp-by-arts
  (implies (equal (fn-scj-arts-map c) (fn-scj-arts-map d))
           (equal (fn-scj-nexts-matchp names nexts c) (fn-scj-nexts-matchp names nexts d)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-scj-nexts-matchp names nexts c))))

(defthm fn-scj-acc-rowsp-by-arts
  (implies (equal (fn-scj-arts-map c) (fn-scj-arts-map d))
           (equal (fn-scj-acc-rowsp acc c) (fn-scj-acc-rowsp acc d)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-scj-acc-rowsp fn-scj-rows-arts) (fn-scj-nexts-matchp fn-scj-arts-map))
           :use ((:instance fn-scj-nexts-matchp-by-arts (names (fn-state-groups acc)) (nexts (fn-state-nexts acc)))))))

; -----------------------------------------------------------------------------
; The catalog's steps, read as articles.

(defthm fn-scj-assign-numbers-by-arts
  (implies (equal (fn-scj-arts-map c) (fn-scj-arts-map d))
           (equal (fn-cat-assign-numbers gs c) (fn-cat-assign-numbers gs d)))
  :rule-classes nil)

(defthm fn-scj-arts-map-of-commit
  (equal (fn-scj-arts-map (fn-cat-commit h c))
         (append (fn-scj-arts-map c)
                 (list (fn-make-article (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                                        (fn-cat-assign-numbers (fn-record-groups h) c) t
                                        (fn-record-stamp h)))))
  :hints (("Goal" :in-theory (e/d (fn-cat-commit-is-append) (fn-cat-assign fn-scj-row-art)))))

(defthm fn-scj-arts-map-of-load-held-row
  (equal (fn-scj-arts-map (fn-sca-load-held-row r idx c))
         (let ((h (fn-scj-load-h r)))
           (if h
               (append (fn-scj-arts-map c)
                       (list (fn-make-article (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                                              (fn-cat-assign-numbers (fn-record-groups h) c) t
                                              (fn-record-stamp h))))
             (fn-scj-arts-map c))))
  :hints (("Goal" :in-theory (e/d (fn-scj-load-held-row-is)
                                  (fn-sca-load-held-row fn-scj-load-h fn-cat-commit-is-append
                                   fn-midx-lookup fn-cat-assign-numbers)))))

(local (defun-nx fn-scj-load-pair-ind (rows idx c idx2 d)
  (declare (xargs :verify-guards nil))
  (if (consp rows)
      (fn-scj-load-pair-ind (cdr rows) idx (fn-sca-load-held-row (car rows) idx c)
                            idx2 (fn-sca-load-held-row (car rows) idx2 d))
    (list idx c idx2 d))))

(defthm fn-scj-arts-map-of-load-from-by-arts
  (implies (equal (fn-scj-arts-map c) (fn-scj-arts-map d))
           (equal (fn-scj-arts-map (fn-sca-load-held-rows-from rows idx c))
                  (fn-scj-arts-map (fn-sca-load-held-rows-from rows idx2 d))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-scj-load-pair-ind rows idx c idx2 d)
           :in-theory (disable fn-sca-load-held-row fn-scj-load-h fn-cat-assign-numbers
                               fn-scj-load-held-row-is))
          ("Subgoal *1/2" :use ((:instance fn-scj-assign-numbers-by-arts
                                           (gs (fn-record-groups (fn-scj-load-h (car rows)))))))
          ("Subgoal *1/1" :use ((:instance fn-scj-assign-numbers-by-arts
                                           (gs (fn-record-groups (fn-scj-load-h (car rows)))))))))

(defthm fn-scj-arts-map-of-update-nth-withdrawn
  (implies (< (nfix i) (len c))
           (equal (fn-scj-arts-map (update-nth i (fn-held-with-withdrawn (nth i c) w) c))
                  (fn-scj-arts-map c)))
  :hints (("Goal" :in-theory (e/d (update-nth) (fn-scj-row-art)))))

(defthm fn-scj-arts-map-of-mark
  (implies (natp target)
           (equal (fn-scj-arts-map (fn-cat-mark-withdrawn target v by c)) (fn-scj-arts-map c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat-mark-withdrawn) (fn-scj-arts-map fn-scj-arts-map-of-update-nth-withdrawn))
           :cases ((consp c))
           :use ((:instance fn-scj-arts-map-of-update-nth-withdrawn (i target) (w (cons v by)))))))

(defthm fn-scj-arts-map-of-withdraw-targets
  (equal (fn-scj-arts-map (fn-sca-withdraw-targets targets index by c)) (fn-scj-arts-map c))
  :hints (("Goal" :induct (fn-sca-withdraw-targets targets index by c)
           :in-theory (e/d (fn-sca-withdraw-targets) (fn-scj-arts-map fn-cat-view-last-visible)))))

; -----------------------------------------------------------------------------
; THE INVARIANT: the catalog's rows as articles are the load's of the history.

(defun-nx fn-scj-rows-invp (c events)
  (equal (fn-scj-arts-map c) (fn-scj-arts-map (fn-sca-load-held-rows-from events nil nil))))

; It holds of every load (the opens).
(defthm fn-scj-rows-invp-of-load
  (fn-scj-rows-invp (fn-sca-load-held-rows events idx fn-arena fn-cat) events)
  :hints (("Goal" :in-theory (e/d (fn-scj-rows-invp) (fn-sca-load-held-rows-from fn-scj-arts-map))
           :use ((:instance fn-scj-arts-map-of-load-from-by-arts (rows events) (c nil) (d nil) (idx2 nil))))))

(defthm fn-scj-load-from-of-snoc
  (equal (fn-sca-load-held-rows-from (append a (list r)) idx c)
         (fn-sca-load-held-row r idx (fn-sca-load-held-rows-from a idx c)))
  :hints (("Goal" :induct (fn-sca-load-held-rows-from a idx c)
           :in-theory (disable fn-sca-load-held-row fn-scj-load-held-row-is))))

; KEYSTONE (the finish link).  The host's finish (T4 then T2), with the
; token and expected count the host checks, keeps the invariant over the
; history the store appended EVENT to, when the pending row is the row the
; load commits for EVENT (a plain article row, or a signed composite's held
; row).
(defthm fn-scj-finish-keeps-rows-invp
  (implies (and (fn-scj-rows-invp c events0)
                (fn-pc-p pending)
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (len c))
                (equal (fn-scj-load-h event) (fn-pc-held pending)))
           (fn-scj-rows-invp (mv-nth 2 (fn-sca-finish token pending idx targets c))
                             (append events0 (list event))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scj-rows-invp fn-sca-finish fn-sca-complete fn-cat-complete
                            fn-cat-complete-hidden fn-cat-count-is-len)
                           (fn-scj-arts-map fn-sca-withdraw-targets fn-scj-load-h fn-sca-load-held-row
                            fn-sca-load-held-rows-from fn-cat-commit-is-append fn-midx-lookup
                            fn-cat-assign-numbers fn-scj-load-held-row-is))
           :use ((:instance fn-scj-assign-numbers-by-arts
                            (gs (fn-record-groups (fn-pc-held pending)))
                            (d (fn-sca-load-held-rows-from events0 nil nil)))
                 (:instance fn-pc-p-fields (pc pending))))))

; At an idle store in the live relation the invariant gives the row
; relation with the store's acceptance.
(defthm fn-scj-acc-rowsp-of-rows-invp
  (implies (and (fn-cst-relation st)
                (fn-own-store-idlep st)
                (fn-scj-rows-invp c (fn-sf-records (fn-sn-files st))))
           (fn-scj-acc-rowsp (fn-node-acceptance (fn-sn-node st)) c))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cst-relation fn-own-store-idlep fn-cst-recoverablep fn-scj-rows-invp)
                           (fn-scj-acc-rowsp fn-cst-replay-node fn-sca-load-held-rows-from fn-scj-arts-map
                            fn-sn-statep fn-sn-observed-historyp fn-cst-final-configurationp
                            fn-node-statep fn-cst-pending-linkp fn-cst-deferred-linkp fn-cst-completion-linkp))
           :use ((:instance fn-scj-acc-rowsp-of-cst-replay-node
                            (configs (fn-sn-config-history st))
                            (events (fn-sf-records (fn-sn-files st)))
                            (frontier (fn-sf-frontier (fn-sn-files st)))
                            (idx nil))
                 (:instance fn-scj-acc-rowsp-by-arts
                            (acc (fn-node-acceptance (fn-sn-node st)))
                            (d (fn-sca-load-held-rows-from (fn-sf-records (fn-sn-files st)) nil nil)))))))

; -----------------------------------------------------------------------------
; The join at the host's finish.

(defthm fn-scj-arts-map-of-finish
  (implies (and (fn-pc-p pending)
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (len c)))
           (equal (fn-scj-arts-map (mv-nth 2 (fn-sca-finish token pending idx targets c)))
                  (fn-scj-arts-map (fn-cat-commit (fn-pc-held pending) c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sca-finish fn-sca-complete fn-cat-complete fn-cat-complete-hidden
                            fn-cat-count-is-len)
                           (fn-scj-arts-map fn-sca-withdraw-targets fn-cat-commit-is-append fn-midx-lookup
                            fn-cat-assign-numbers))
           :use ((:instance fn-pc-p-fields (pc pending))))))

(defthm fn-scj-rows-seqs-below-of-append
  (equal (fn-scj-rows-seqs-below (append a b) v)
         (and (fn-scj-rows-seqs-below a v) (fn-scj-rows-seqs-below b v))))

(defthm fn-scj-rows-clearp-of-append
  (equal (fn-scj-rows-clearp (append a b))
         (and (fn-scj-rows-clearp a) (fn-scj-rows-clearp b))))

(defthm fn-scj-msgid-not-in-filter
  (implies (not (member-equal m (fn-article-msgids xs)))
           (not (member-equal m (fn-article-msgids (fn-ctl-visible-filter xs ws arts vs)))))
  :hints (("Goal" :induct (fn-ctl-visible-filter xs ws arts vs)
           :in-theory (disable fn-ctl-withdrawn-by-p))))

(defthm fn-scj-no-dup-msgids-of-filter
  (implies (no-duplicatesp-equal (fn-article-msgids xs))
           (no-duplicatesp-equal (fn-article-msgids (fn-ctl-visible-filter xs ws arts vs))))
  :hints (("Goal" :induct (fn-ctl-visible-filter xs ws arts vs)
           :in-theory (disable fn-ctl-withdrawn-by-p))))

(defthm fn-scj-view-refresh-by-store-and-view
  (implies (and (equal (fn-own-store x) (fn-own-store y))
                (equal (fn-own-view x) (fn-own-view y)))
           (equal (fn-own-view (fn-own-refresh x)) (fn-own-view (fn-own-refresh y))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-refresh)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-ctl-visible-state-of fn-own-view-make-visible)))))

; The row side of the finish: the invariant carried, the relation with the
; completed acceptance, and the row equation.
(defthm fn-scj-finish-row-side
  (let* ((acc2 (fn-node-acceptance (fn-sn-node s2)))
         (held (fn-pc-held pending))
         (c2 (mv-nth 2 (fn-sca-finish token pending idx targets fn-cat))))
    (implies (and (fn-scj-rows-invp fn-cat events0)
                  (fn-cst-relation s2)
                  (fn-own-store-idlep s2)
                  (equal (fn-sf-records (fn-sn-files s2)) (append events0 (list event)))
                  (equal (fn-scj-load-h event) held)
                  (fn-pc-p pending)
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) (len fn-cat)))
             (and (fn-scj-rows-invp c2 (append events0 (list event)))
                  (fn-scj-acc-rowsp acc2 c2)
                  (equal (fn-cat-row-article (len fn-cat) fn-arena (fn-cat-commit held fn-cat))
                         (car (fn-state-articles acc2)))
                  (equal (fn-record-msgid held) (fn-article-msgid (car (fn-state-articles acc2)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-cat-row-article-msgid fn-cat-at-is-nth fn-scj-nth-len-of-commit
                                        fn-cat-assign fn-scj-fields-of-with-numbers)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-finish-keeps-rows-invp (c fn-cat))
                 (:instance fn-scj-acc-rowsp-of-rows-invp (st s2)
                            (c (mv-nth 2 (fn-sca-finish token pending idx targets fn-cat))))
                 (:instance fn-scj-arts-map-of-finish (c fn-cat))
                 (:instance fn-scj-acc-rowsp-by-arts
                            (acc (fn-node-acceptance (fn-sn-node s2)))
                            (c (mv-nth 2 (fn-sca-finish token pending idx targets fn-cat)))
                            (d (fn-cat-commit (fn-pc-held pending) fn-cat)))
                 (:instance fn-scj-row-equation-of-acc-rowsp
                            (acc2 (fn-node-acceptance (fn-sn-node s2)))
                            (held (fn-pc-held pending)) (c fn-cat))))))

; The sequence and clearness of the completed row.
(defthm fn-cst-relation-gives-node-statep
  (implies (fn-cst-relation st) (fn-node-statep (fn-sn-node st)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cst-relation fn-sn-statep) (fn-node-statep fn-sf-statep)))))

(defthm fn-scj-last-row-facts
  (implies (and (fn-scj-rows-seqs-below (append a (list e)) v)
                (fn-scj-rows-clearp (append a (list e)))
                (fn-scj-load-h e))
           (and (null (fn-held-withdrawn (fn-scj-load-h e)))
                (< (nfix (fn-record-sequence (fn-scj-load-h e))) (nfix v))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-scj-load-h))))

(defthm fn-scj-finish-held-side
  (implies (and (fn-cst-relation s2)
                (equal (fn-sf-records (fn-sn-files s2)) (append events0 (list event)))
                (fn-rows-composites-okp (append events0 (list event)) fn-arena)
                (fn-scj-rows-clearp (append events0 (list event)))
                (fn-scj-load-h event))
           (and (null (fn-held-withdrawn (fn-scj-load-h event)))
                (< (nfix (fn-record-sequence (fn-scj-load-h event)))
                   (len (fn-sf-records (fn-sn-files s2))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(nfix (:type-prescription len)) (theory 'minimal-theory))
           :use ((:instance fn-scj-rows-seqs-below-at-related-store (st s2))
                 (:instance fn-scj-last-row-facts (a events0) (e event)
                            (v (len (fn-sf-records (fn-sn-files s2)))))))))

; The view side: the completed article against the old visible list.
(defthm fn-scj-finish-view-side
  (let ((arts2 (fn-state-articles (fn-node-acceptance (fn-sn-node s2)))))
    (implies (and (fn-node-statep (fn-sn-node s2))
                  (equal arts2 (cons (car arts2) raw))
                  (equal visible (fn-ctl-visible-articles raw ws vs))
                  (equal visible2 (fn-ctl-visible-articles arts2 ws2 vs2)))
             (and (consp (car arts2))
                  (stringp (fn-article-msgid (car arts2)))
                  (no-duplicatesp-equal (fn-article-msgids (cons (car arts2) visible)))
                  (fn-midx-string-article-listp visible)
                  (fn-midx-string-article-listp visible2))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ctl-visible-articles fn-article-msgids no-duplicatesp-equal
                                        fn-scj-consesp fn-midx-string-article-listp fn-ag-car fn-ag-cdr
                                        car-cons cdr-cons)
                                      (theory 'minimal-theory))
           :use ((:instance fn-own-node-statep-acceptance-articles (node (fn-sn-node s2)))
                 (:instance fn-scj-consesp-of-article-listp
                            (g (fn-state-groups (fn-node-acceptance (fn-sn-node s2))))
                            (xs (fn-state-articles (fn-node-acceptance (fn-sn-node s2)))))
                 (:instance fn-ctl-article-listp-msgids-distinct
                            (configured (fn-state-groups (fn-node-acceptance (fn-sn-node s2))))
                            (xs (fn-state-articles (fn-node-acceptance (fn-sn-node s2)))))
                 (:instance fn-article-listp-gives-midx-string-articles
                            (configured (fn-state-groups (fn-node-acceptance (fn-sn-node s2))))
                            (articles (fn-state-articles (fn-node-acceptance (fn-sn-node s2)))))
                 (:instance fn-scj-msgid-not-in-filter (m (fn-article-msgid (car (fn-state-articles (fn-node-acceptance (fn-sn-node s2))))))
                            (xs raw) (arts raw))
                 (:instance fn-scj-no-dup-msgids-of-filter (xs raw) (arts raw))
                 (:instance fn-scj-string-articles-of-visible-filter (xs raw) (arts raw))
                 (:instance fn-scj-string-articles-of-visible-filter
                            (xs (fn-state-articles (fn-node-acceptance (fn-sn-node s2))))
                            (arts (fn-state-articles (fn-node-acceptance (fn-sn-node s2))))
                            (ws ws2) (vs vs2))))))

(defthm fn-scj-len-of-snoc
  (equal (len (append a (list e))) (+ 1 (len a))))

; KEYSTONE (the join at the host's article finish, the row equation
; discharged).  VIEW is the owner's view before the completion, S2 the store
; after it (idle, in the live relation, its history the old one and EVENT),
; and the refreshed view is fn-own-refresh over S2 and VIEW, which the
; host's finish computes (fn-ccar-own-complete-enabled).  The catalog carries
; the join with VIEW and the rows invariant over the old history; the pending
; row is EVENT's loaded row (the finish link).  Then the catalog after
; fn-sca-finish, over the refreshed view's index and targets as
; host/owner-host.lisp fn-owner-finish-submission passes them, is joined to
; the refreshed view and carries the rows invariant over the new history.
; The completion's acceptance and verdict equations are PRF-202's
; (fn-view-apply-is-refresh); the visible lists are acceptance filters
; (fn-ocl-view-historyp of the owner before and after).
(defthm fn-scj-joinp-of-host-finish
  (let* ((view (fn-own-view o))
         (view2 (fn-own-view (fn-own-refresh (fn-crf-with-store o s2))))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (a (car (fn-state-articles acc2)))
         (events2 (append events0 (list event)))
         (held (fn-pc-held pending))
         (c2 (mv-nth 2 (fn-sca-finish token pending (fn-own-view-index view2)
                                      (fn-sca-targets-of (fn-record-msgid held)
                                                         (fn-own-view-withdrawals view2))
                                      fn-cat))))
    (implies (and (fn-scj-joinp view fn-arena fn-cat)
                  (fn-scar-view-indexedp o)
                  (fn-scj-rows-invp fn-cat events0)
                  (fn-cst-relation s2)
                  (fn-own-store-idlep s2)
                  (equal (fn-sf-records (fn-sn-files s2)) events2)
                  (fn-rows-composites-okp events2 fn-arena)
                  (fn-scj-rows-clearp events2)
                  (equal (fn-scj-load-h event) held)
                  (fn-pc-p pending)
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) (len fn-cat))
                  (equal (fn-state-articles acc2) (cons a (fn-own-view-raw view)))
                  (equal (fn-sn-verdicts s2)
                         (cons (cons (fn-article-msgid a) verdict) (fn-own-view-verdicts view)))
                  (equal (fn-state-articles (fn-own-view-archive view))
                         (fn-ctl-visible-articles (fn-own-view-raw view)
                                                  (fn-own-view-withdrawals view)
                                                  (fn-own-view-verdicts view)))
                  (equal (fn-state-articles (fn-own-view-archive view2))
                         (fn-ctl-visible-articles (fn-state-articles acc2)
                                                  (fn-own-view-withdrawals view2)
                                                  (fn-own-view-verdicts view2)))
                  (<= (nfix (fn-own-view-version view)) (len events0)))
             (and (fn-scj-joinp view2 fn-arena c2)
                  (fn-scj-rows-invp c2 events2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scar-view-indexedp fn-cat-count-is-len nfix fix
                                        fn-scj-len-of-snoc (:type-prescription len)
                                        (:executable-counterpart fn-held-p))
                                      (theory 'minimal-theory))
           :use ((:instance fn-pc-p-fields (pc pending))
                 (:instance fn-scj-finish-row-side
                            (idx (fn-own-view-index (fn-own-view (fn-own-refresh (fn-crf-with-store o s2)))))
                            (targets (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                        (fn-own-view-withdrawals
                                                         (fn-own-view (fn-own-refresh (fn-crf-with-store o s2)))))))
                 (:instance fn-scj-finish-held-side)
                 (:instance fn-cst-relation-gives-node-statep (st s2))
                 (:instance fn-scj-finish-view-side
                            (raw (fn-own-view-raw (fn-own-view o)))
                            (visible (fn-state-articles (fn-own-view-archive (fn-own-view o))))
                            (ws (fn-own-view-withdrawals (fn-own-view o)))
                            (vs (fn-own-view-verdicts (fn-own-view o)))
                            (visible2 (fn-state-articles (fn-own-view-archive
                                                          (fn-own-view (fn-own-refresh (fn-crf-with-store o s2))))))
                            (ws2 (fn-own-view-withdrawals (fn-own-view (fn-own-refresh (fn-crf-with-store o s2)))))
                            (vs2 (fn-own-view-verdicts (fn-own-view (fn-own-refresh (fn-crf-with-store o s2))))))
                 (:instance fn-view-apply-is-refresh
                            (s s2) (a (car (fn-state-articles (fn-node-acceptance (fn-sn-node s2))))))
                 (:instance fn-scj-apply-article-projections
                            (s s2) (a (car (fn-state-articles (fn-node-acceptance (fn-sn-node s2)))))
                            (view (fn-own-view o)))
                 (:instance fn-scj-joinp-of-article-finish
                            (s s2) (a (car (fn-state-articles (fn-node-acceptance (fn-sn-node s2)))))
                            (view (fn-own-view o)))))))

(defthm fn-scj-own-refresh-store
  (equal (fn-own-store (fn-own-refresh x)) (fn-own-store x))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-ctl-visible-state-of fn-own-view-make-visible)))))

; The owner the host's finish installs (fn-ccar-own-finish: fn-apc-own-finish
; under the carried parse and the store's event index,
; fn-apc-own-finish-is-ccar-own-finish) has the view and store the keystone
; above names: the refresh over the finished store and the old view.
(defthm fn-scj-host-finish-view-and-store
  (implies (fn-ccar-completion-enabledp (fn-own-store o))
           (let ((o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
                 (s2 (fn-ccar-sn-finish-enabled (fn-own-store o))))
             (and (equal (fn-own-view o2) (fn-own-view (fn-own-refresh (fn-crf-with-store o s2))))
                  (equal (fn-own-store o2) s2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ccar-own-finish fn-ccar-own-complete-enabled fn-crf-with-store
                                        fn-own-make fn-own-store fn-own-view car-cons cdr-cons)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-view-refresh-by-store-and-view
                            (x (fn-own-make (fn-ccar-sn-finish-enabled (fn-own-store o)) (fn-own-view o)
                                            (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o) nil
                                            (fn-sl-snoc (fn-own-ledger-field o)
                                                        (fn-sf-completion (fn-sn-files (fn-own-store o))))
                                            (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                                            (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
                                            (fn-own-node-secret o) (fn-own-refused o)))
                            (y (fn-crf-with-store o (fn-ccar-sn-finish-enabled (fn-own-store o)))))
                 (:instance fn-scj-own-refresh-store
                            (x (fn-own-make (fn-ccar-sn-finish-enabled (fn-own-store o)) (fn-own-view o)
                                            (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o) nil
                                            (fn-sl-snoc (fn-own-ledger-field o)
                                                        (fn-sf-completion (fn-sn-files (fn-own-store o))))
                                            (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                                            (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
                                            (fn-own-node-secret o) (fn-own-refused o))))))))

; KEYSTONE (step 2 at the host's call).  The same over the owner
; host/owner-host.lisp fn-owner-finish-submission installs
; (fn-ccar-own-finish; fn-apc-own-finish-is-ccar-own-finish) and the
; catalog it computes over that owner's view.
(defthm fn-scj-joinp-at-host-finish
  (let* ((view (fn-own-view o))
         (o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (s2 (fn-own-store o2))
         (view2 (fn-own-view o2))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (a (car (fn-state-articles acc2)))
         (events2 (append events0 (list event)))
         (held (fn-pc-held pending))
         (c2 (mv-nth 2 (fn-sca-finish token pending (fn-own-view-index view2)
                                      (fn-sca-targets-of (fn-record-msgid held)
                                                         (fn-own-view-withdrawals view2))
                                      fn-cat))))
    (implies (and (fn-ccar-completion-enabledp (fn-own-store o))
                  (fn-scj-joinp view fn-arena fn-cat)
                  (fn-scar-view-indexedp o)
                  (fn-scj-rows-invp fn-cat events0)
                  (fn-cst-relation s2)
                  (fn-own-store-idlep s2)
                  (equal (fn-sf-records (fn-sn-files s2)) events2)
                  (fn-rows-composites-okp events2 fn-arena)
                  (fn-scj-rows-clearp events2)
                  (equal (fn-scj-load-h event) held)
                  (fn-pc-p pending)
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) (len fn-cat))
                  (equal (fn-state-articles acc2) (cons a (fn-own-view-raw view)))
                  (equal (fn-sn-verdicts s2)
                         (cons (cons (fn-article-msgid a) verdict) (fn-own-view-verdicts view)))
                  (equal (fn-state-articles (fn-own-view-archive view))
                         (fn-ctl-visible-articles (fn-own-view-raw view)
                                                  (fn-own-view-withdrawals view)
                                                  (fn-own-view-verdicts view)))
                  (equal (fn-state-articles (fn-own-view-archive view2))
                         (fn-ctl-visible-articles (fn-state-articles acc2)
                                                  (fn-own-view-withdrawals view2)
                                                  (fn-own-view-verdicts view2)))
                  (<= (nfix (fn-own-view-version view)) (len events0)))
             (and (fn-scj-joinp view2 fn-arena c2)
                  (fn-scj-rows-invp c2 events2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-scj-host-finish-view-and-store)
                 (:instance fn-scj-joinp-of-host-finish
                            (s2 (fn-ccar-sn-finish-enabled (fn-own-store o))))))))

; Step 2 at the identity finish (an instance; its own teeth OPEN).  host/owner-host.lisp
; fn-owner-finish-identity installs fn-rix-ocfg-complete, which is the
; article finish's owner with no configuration record staged and the
; history stobj synced to the store (fn-scj-identity-finish-owner-is-article-
; finish-owner), then runs the same fn-sca-finish over its view: the join
; and the rows invariant are carried (a signed composite's EVENT loads its
; held row, fn-scj-load-h).
(defthm fn-scj-joinp-at-identity-finish
  (let* ((o (fn-ocfg-owner oc))
         (view (fn-own-view o))
         (o2 (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist)))
         (s2 (fn-own-store o2))
         (view2 (fn-own-view o2))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (a (car (fn-state-articles acc2)))
         (events2 (append events0 (list event)))
         (held (fn-pc-held pending))
         (c2 (mv-nth 2 (fn-sca-finish token pending (fn-own-view-index view2)
                                      (fn-sca-targets-of (fn-record-msgid held)
                                                         (fn-own-view-withdrawals view2))
                                      fn-cat))))
    (implies (and (fn-hist-of-storep fn-hist (fn-own-store o))
                  (not (fn-ocfg-staged oc))
                  (fn-sn-completion-enabledp (fn-own-store o))
                  (fn-scj-joinp view fn-arena fn-cat)
                  (fn-scar-view-indexedp o)
                  (fn-scj-rows-invp fn-cat events0)
                  (fn-cst-relation s2)
                  (fn-own-store-idlep s2)
                  (equal (fn-sf-records (fn-sn-files s2)) events2)
                  (fn-rows-composites-okp events2 fn-arena)
                  (fn-scj-rows-clearp events2)
                  (equal (fn-scj-load-h event) held)
                  (fn-pc-p pending)
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) (len fn-cat))
                  (equal (fn-state-articles acc2) (cons a (fn-own-view-raw view)))
                  (equal (fn-sn-verdicts s2)
                         (cons (cons (fn-article-msgid a) verdict) (fn-own-view-verdicts view)))
                  (equal (fn-state-articles (fn-own-view-archive view))
                         (fn-ctl-visible-articles (fn-own-view-raw view)
                                                  (fn-own-view-withdrawals view)
                                                  (fn-own-view-verdicts view)))
                  (equal (fn-state-articles (fn-own-view-archive view2))
                         (fn-ctl-visible-articles (fn-state-articles acc2)
                                                  (fn-own-view-withdrawals view2)
                                                  (fn-own-view-verdicts view2)))
                  (<= (nfix (fn-own-view-version view)) (len events0)))
             (and (fn-scj-joinp view2 fn-arena c2)
                  (fn-scj-rows-invp c2 events2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ocfg-with-owner fn-ocfg-make fn-ocfg-owner car-cons
                                        fn-ccar-completion-enabledp-is-reference)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-identity-finish-owner-is-article-finish-owner (cfg (fn-ocfg-config oc)))
                 (:instance fn-scj-joinp-at-host-finish (o (fn-ocfg-owner oc)) (cfg (fn-ocfg-config oc)))))))
