; served-catalog-join-host-views.lisp -- the captured reader views carried
; across the host's protocol (lane join-f2-2, 2026-09-29; PRF-302).
;
; While the committer holds a capture (host/owner-host.lisp
; fn-owner-reader-views: nil, (D) or (D N), each a working view the owner
; held), the host's reads and opens run at the captured view (PKT-828).  The
; read and the captured open named its liveness (fn-sjh-views-okp: live over
; the catalog, no newer than the working view).  fn-sjh-viewsp carries it for
; every captured view: at a capture it is the working view, which
; fn-scj-invp keeps live; the catalog's finish keeps an older view live
; (fn-scj-catalogp-of-finish: the committed row's sequence is past it); and
; the working view only ever refreshes forward (the store's history grows,
; fn-sjh-vw-store-step-version, fn-sjh-vw-finish-version-grows).  Every host
; entry keeps it (the KEYSTONES below, one per entry of the join-f2-2 record's
; table); with it the read and the captured open need no named premise
; beyond fn-sjh-okp, fn-sjh-colsp and fn-sjh-viewsp
; (fn-sjh-okp-at-owner-chunk-span-fully-carried,
; fn-sjh-okp-at-owner-open-captured-carried).

(in-package "ACL2")

(include-book "served-catalog-join-host-columns")
(include-book "served-catalog-join-host-identity-finish")

(local (in-theory (disable (tau-system))))


(defun-nx fn-sjh-viewsp (views o fn-cat)
  (if (consp views)
      (and (fn-scj-live-okp (car views) nil fn-cat)
           (<= (nfix (fn-own-view-version (car views)))
               (nfix (fn-own-view-version (fn-own-view o))))
           (fn-sjh-viewsp (cdr views) o fn-cat))
    t))


(defthm fn-sjh-live-okp-arena-free
  (implies (syntaxp (not (equal fn-arena ''nil)))
           (equal (fn-scj-live-okp v fn-arena fn-cat) (fn-scj-live-okp v nil fn-cat)))
  :hints (("Goal" :in-theory (union-theories '(fn-scj-live-okp fn-scr-live-catalogp fn-scr-fields-catalogp
                                               fn-sjh-scr-catalogp-arena-free)
                                             (theory 'minimal-theory)))))

(defthm fn-sjh-viewsp-gives-views-okp
  (implies (fn-sjh-viewsp views o fn-cat)
           (fn-sjh-views-okp views o fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-sjh-viewsp fn-sjh-views-okp) (fn-scj-live-okp)))))

(defthm fn-sjh-viewsp-of-later-view
  (implies (and (fn-sjh-viewsp views o fn-cat)
                (<= (nfix (fn-own-view-version (fn-own-view o)))
                    (nfix (fn-own-view-version (fn-own-view o2)))))
           (fn-sjh-viewsp views o2 fn-cat))
  :hints (("Goal" :induct (fn-sjh-viewsp views o fn-cat)
           :in-theory (e/d (fn-sjh-viewsp) (fn-scj-live-okp)))))

; KEYSTONE (the committer's capture: host/owner-host.lisp
; fn-owner-reader-views-capture, fn-ocv-capture of the working view).
(defthm fn-sjh-viewsp-at-capture
  (implies (and (fn-sjh-viewsp views o fn-cat)
                (fn-scj-invp o fn-arena fn-cat))
           (fn-sjh-viewsp (fn-ocv-capture views event (fn-own-view o)) o fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-ocv-capture fn-sjh-viewsp) (fn-scj-live-okp fn-scj-invp))
           :use ((:instance fn-scj-invp-gives-live-okp)))))


; -----------------------------------------------------------------------------
; The working view refreshes forward; an older view stays live across a finish.


(defthm fn-sjh-vw-framep-records-grow
  (implies (fn-scjs-store-framep s st v)
           (<= (len (fn-sf-records (fn-sn-files s))) (len (fn-sf-records (fn-sn-files st)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-scjs-store-framep))))

(defthm fn-sjh-vw-store-step-version
  (implies (and (fn-scjs-historyp o)
                (fn-scjs-seenp o)
                (not (member-equal (car ev) '(:finish :crash :recover))))
           (<= (nfix (fn-own-view-version (fn-own-view o)))
               (nfix (fn-own-view-version (fn-own-view (fn-own-store-step o ev))))))
  :hints (("Goal" :in-theory (e/d (fn-own-store-step fn-scjs-historyp fn-scjs-seenp)
                                  (fn-snrt-step fn-own-refresh fn-own-store-idlep fn-scjs-store-framep
                                   fn-scjs-store-seenp))
           :use ((:instance fn-scjs-snrt-step-framep (s (fn-own-store o)) (event ev)
                            (v (fn-own-view-version (fn-own-view o))))
                 (:instance fn-sjh-refresh-version
                            (o (fn-own-make (fn-snrt-step (fn-own-store o) ev) (fn-own-view o)
                                            (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
                                            (fn-own-pending o) (fn-own-ledger-field o) (fn-own-clock o)
                                            (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
                                            (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o)
                                            (fn-own-refused o))))))))

(defthm fn-sjh-vw-live-okp-of-finish
  (let ((c2 (mv-nth 2 (fn-sca-finish token pending idx targets fn-cat))))
    (implies (and (fn-scj-live-okp v nil fn-cat)
                  (fn-scj-seqs-sortedp fn-cat)
                  (fn-scj-seqs-below fn-cat (fn-record-sequence (fn-pc-held pending)))
                  (<= (nfix (fn-own-view-version v)) (nfix (fn-record-sequence (fn-pc-held pending)))))
             (fn-scj-live-okp v nil c2)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-live-okp fn-scr-live-catalogp fn-scr-fields-catalogp
                                        fn-own-view-live-fields fn-served-pinned-fields)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-catalogp-of-finish
                            (archive (fn-own-view-archive v))
                            (index (if (fn-own-view-group-index v)
                                       (fn-gidx-pin-with-control (fn-own-view-index v) (fn-own-view-group-index v)
                                                                 (fn-own-view-control v))
                                     (fn-own-view-index v)))
                            (v (fn-own-view-version v))
                            (fn-arena nil))))))

(defthm fn-sjh-vw-viewsp-across-finish
  (let ((c2 (mv-nth 2 (fn-sca-finish token pending idx targets fn-cat))))
    (implies (and (fn-sjh-viewsp views o fn-cat)
                  (fn-scj-seqs-sortedp fn-cat)
                  (fn-scj-seqs-below fn-cat (fn-record-sequence (fn-pc-held pending)))
                  (<= (nfix (fn-own-view-version (fn-own-view o))) (nfix (fn-record-sequence (fn-pc-held pending))))
                  (<= (nfix (fn-own-view-version (fn-own-view o))) (nfix (fn-own-view-version (fn-own-view o2)))))
             (fn-sjh-viewsp views o2 c2)))
  :hints (("Goal" :induct (fn-sjh-viewsp views o fn-cat)
           :in-theory (e/d (fn-sjh-viewsp) (fn-scj-live-okp fn-sca-finish nfix)))
          ("Subgoal *1/2" :use ((:instance fn-sjh-vw-live-okp-of-finish (v (car views)))))))

; The finish's facts the views need: the held row's sequence is the count of
; the history before it, the view is at or below it, the catalog's rows are
; below it, and the finished view is no older.
(defthm fn-sjh-vw-finish-facts
  (let* ((s (fn-own-store o))
         (records (fn-sf-records (fn-sn-files s)))
         (o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (s2 (fn-own-store o2))
         (held (fn-pc-held pending))
         (v (fn-own-view-version (fn-own-view o))))
    (implies (and (fn-ccar-completion-enabledp s)
                  (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o)
                  (consp records)
                  (fn-cst-relation s2)
                  (fn-rows-composites-okp records fn-arena)
                  (equal (fn-scj-load-h (car (last records))) held)
                  (fn-pc-p pending))
             (and (fn-scj-seqs-below fn-cat (fn-record-sequence held))
                  (<= (nfix v) (nfix (fn-record-sequence held)))
                  (<= (nfix v) (nfix (fn-own-view-version (fn-own-view o2)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-invp fn-scj-joinp fn-scjs-seenp fn-scjs-store-seenp fn-scjs-seen-records
                                        fn-scjs-historyp nfix fix (:type-prescription len) natp
                                        fn-scj-true-listp-butlast)
                                      (theory 'minimal-theory))
           :use ((:instance fn-pc-p-fields (pc pending))
                 (:instance fn-scj-held-p-non-nil (h (fn-pc-held pending)))
                 (:instance fn-scj-enabled-is-completing (s (fn-own-store o)))
                 (:instance fn-sjh-finish-store-image)
                 (:instance fn-scj-version-of-host-finish)
                 (:instance fn-scj-records-kept-by-ccar-finish (s (fn-own-store o)))
                 (:instance fn-scj-host-finish-store)
                 (:instance fn-scj-snoc-of-butlast-last (r (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-scj-held-sequence-at-host-finish
                            (s2 (fn-own-store (cdr (fn-ccar-own-finish o cfg fn-arena))))
                            (events0 (butlast (fn-sf-records (fn-sn-files (fn-own-store o))) 1))
                            (event (car (last (fn-sf-records (fn-sn-files (fn-own-store o)))))))
                 (:instance fn-scj-seqs-below-monotone (c fn-cat)
                            (v1 (fn-own-view-version (fn-own-view o)))
                            (v2 (len (butlast (fn-sf-records (fn-sn-files (fn-own-store o))) 1))))))))

(defthm fn-sjh-vw-viewsp-at-finish-by-facts
  (let* ((s (fn-own-store o))
         (records (fn-sf-records (fn-sn-files s)))
         (o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (s2 (fn-own-store o2))
         (held (fn-pc-held pending))
         (c2 (mv-nth 2 (fn-sca-finish token pending idx targets fn-cat))))
    (implies (and (fn-sjh-viewsp views o fn-cat)
                  (fn-ccar-completion-enabledp s)
                  (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o)
                  (consp records)
                  (fn-cst-relation s2)
                  (fn-rows-composites-okp records fn-arena)
                  (equal (fn-scj-load-h (car (last records))) held)
                  (fn-pc-p pending)
                  (fn-scj-seqs-sortedp fn-cat))
             (fn-sjh-viewsp views o2 c2)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '() (theory 'minimal-theory))
           :use ((:instance fn-sjh-vw-finish-facts)
                 (:instance fn-sjh-vw-viewsp-across-finish (o2 (cdr (fn-ccar-own-finish o cfg fn-arena))))))))

; KEYSTONE (the captured views across the host's article finish): as
; fn-sjh-okp-at-host-article-finish.
(defthm fn-sjh-viewsp-at-host-article-finish
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (res (fn-ccar-own-finish o cfg fn-arena))
         (o2 (cdr res))
         (view2 (fn-own-view o2))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending)))
         (fin (fn-sca-finish token pending (fn-own-view-index view2)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view2))
                             fn-cat)))
    (implies (and (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  (equal (car res) :durable)
                  (fn-sjh-viewsp views o fn-cat))
             (fn-sjh-viewsp views o2 (mv-nth 2 fin))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-finish-premisesp) (theory 'minimal-theory))
           :use ((:instance fn-sjh-finish-premises-of-okp
                            )
                 (:instance fn-sjh-vw-viewsp-at-finish-by-facts
                            (o (fn-ocfg-owner oc))
                            (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                                         (fn-pc-expected pending)))
                            (idx (fn-own-view-index (fn-own-view (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
                            (targets (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                        (fn-own-view-withdrawals
                                                         (fn-own-view (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))))))))

(defthm fn-sjh-vw-finish-version-grows
  (implies (and (fn-ccar-completion-enabledp (fn-own-store o))
                (fn-scjs-historyp o))
           (<= (nfix (fn-own-view-version (fn-own-view o)))
               (nfix (fn-own-view-version (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scjs-historyp nfix natp (:type-prescription len))
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-finish-store-image)
                 (:instance fn-scj-version-of-host-finish)))))

; KEYSTONE (the captured views across the host's identity finish, every
; branch of fn-owner-finish-identity; the pending row's branch through the
; article's or the signed composite's premises).
(defthm fn-sjh-viewsp-at-owner-finish-identity
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (completion (fn-sf-completion (fn-sn-files s)))
         (o2 (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist)))
         (view2 (fn-own-view o2))
         (durablep (and (equal (fn-sf-phase (fn-sn-files s)) :completing)
                        (equal (fn-sf-phase (fn-sn-files (fn-own-store o2))) :ready)))
         (fin (fn-sca-finish (cons (nfix (cdr completion)) (fn-pc-expected pending))
                             pending (fn-own-view-index view2)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view2))
                             fn-cat)))
    (implies (and (fn-hist-of-storep fn-hist s)
                  (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  (fn-sjh-viewsp views o fn-cat))
             (if (and durablep pending (consp completion))
                 (fn-sjh-viewsp views o2 (mv-nth 2 fin))
               (fn-sjh-viewsp views o2 fn-cat))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((fn-ocfg-staged oc)
                   (not (fn-ccar-completion-enabledp (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory (union-theories '(fn-sjh-idf-rix-staged-owner fn-sjh-idf-finish-not-enabled
                                        fn-sjh-idf-enabled-completion-consp fn-sjh-finish-premisesp
                                        fn-sjh-idf-premisesp)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-idf-durable-is-enabled)
                 (:instance fn-sjh-rix-complete-owner (cfg nil))
                 (:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-vw-finish-version-grows (o (fn-ocfg-owner oc)) (cfg nil))
                 (:instance fn-sjh-viewsp-of-later-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist))))
                 (:instance fn-sjh-idf-row-kind)
                 (:instance fn-sjh-idf-article-premises-of-okp (cfg nil))
                 (:instance fn-sjh-idf-premises-of-okp (cfg nil))
                 (:instance fn-sjh-vw-viewsp-at-finish-by-facts
                            (o (fn-ocfg-owner oc)) (cfg nil)
                            (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                                         (fn-pc-expected pending)))
                            (idx (fn-own-view-index (fn-own-view (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist)))))
                            (targets (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                        (fn-own-view-withdrawals
                                                         (fn-own-view (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist)))))))))))


; -----------------------------------------------------------------------------
; The served read keeps the view.


(defun-nx fn-sjh-vw-result-viewp (r oc)
  (equal (fn-own-view (fn-ocfg-owner (fn-own-tls-result-owner r))) (fn-own-view (fn-ocfg-owner oc))))

(defthm fn-sjh-vw-owner-closed-view
  (equal (fn-own-view (fn-ocfg-owner (fn-oas-owner-closed oc id))) (fn-own-view (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory '(fn-sjh-rd-owner-closed-owner fn-sjh-rd-set-conns-fields))))

(defthm fn-sjh-vw-unshed-view
  (equal (fn-own-view (fn-ocfg-owner (fn-otm-unshed-ocfg oc id allow))) (fn-own-view (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory '(fn-otm-unshed-ocfg fn-sjh-rd-with-allow-fields fn-sjh-rd-with-refused-fields))))

(defthm fn-sjh-vw-otm-view
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-vw-result-viewp (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat) oc))
  :hints (("Goal" :in-theory (union-theories '(fn-sjh-vw-result-viewp fn-scj-otm-read-span-owner
                                               fn-sjh-vw-unshed-view fn-sjh-rd-shed-view)
                                             (theory 'minimal-theory))
           :use ((:instance fn-sjh-rd-orr-keeps)
                 (:instance fn-sjh-rd-orr-keeps (oc (fn-otm-shed-ocfg oc id)))
                 (:instance fn-scj-invp-of-otm-shed-ocfg)
                 (:instance fn-sjh-rd-views-okp-of-same-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-otm-shed-ocfg oc id))))))))

(defthm fn-sjh-vw-posting-off-view
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-vw-result-viewp (fn-oas-posting-off-read oc views id i end cache s fn-octets fn-arena fn-cat) oc))
  :hints (("Goal" :in-theory (union-theories '(fn-sjh-vw-result-viewp fn-oas-posting-off-read
                                               fn-scj-tls-result-owner-of-make fn-sjh-rd-with-allow-view)
                                             (theory 'minimal-theory))
           :use ((:instance fn-sjh-vw-otm-view (oc (fn-otm-owner-with-allow oc id nil)))
                 (:instance fn-scj-invp-of-otm-owner-with-allow (allow nil))
                 (:instance fn-sjh-rd-views-okp-of-same-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-otm-owner-with-allow oc id nil))))))))

(defthm fn-sjh-vw-close-result-view
  (equal (fn-sjh-vw-result-viewp (fn-oas-close-result r id) oc) (fn-sjh-vw-result-viewp r oc))
  :hints (("Goal" :in-theory '(fn-sjh-vw-result-viewp fn-oas-close-result fn-scj-tls-result-owner-of-make
                               fn-sjh-vw-owner-closed-view))))

(defthm fn-sjh-vw-whole-refusal-view
  (fn-sjh-vw-result-viewp (fn-oas-whole-refusal oc id i end) oc)
  :hints (("Goal" :in-theory '(fn-sjh-vw-result-viewp fn-oas-whole-refusal fn-scj-tls-result-owner-of-make
                               fn-sjh-vw-owner-closed-view))))

(defthm fn-sjh-vw-tiers-view
  (implies (fn-sjh-vw-result-viewp r1 oc)
           (fn-sjh-vw-result-viewp (fn-oas-tiers oc r1 id i end slots) oc))
  :hints (("Goal" :in-theory '(fn-oas-tiers fn-sjh-vw-close-result-view fn-sjh-vw-whole-refusal-view))))


(defthm fn-sjh-vw-oas-view
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-vw-result-viewp (fn-oas-read-span oc views id i end cache s slots fn-octets fn-arena fn-cat) oc))
  :hints (("Goal" :in-theory '(fn-oas-read-span fn-sjh-vw-otm-view fn-sjh-vw-posting-off-view fn-sjh-vw-tiers-view))))

(defthm fn-sjh-vw-shut-read-view
  (fn-sjh-vw-result-viewp (fn-mca-shut-read oc id i end) oc)
  :hints (("Goal" :in-theory '(fn-sjh-vw-result-viewp fn-mca-shut-read fn-scj-tls-result-owner-of-make
                               fn-sjh-vw-owner-closed-view))))

(defthm fn-sjh-vw-refused-read-view
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-vw-result-viewp (fn-mca-refused-read oc views id i end cache s fn-octets fn-arena fn-cat) oc))
  :hints (("Goal" :in-theory '(fn-mca-refused-read fn-sjh-vw-posting-off-view fn-sjh-vw-close-result-view))))

(defthm fn-sjh-vw-mca-view
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-vw-result-viewp (car (fn-mca-read-span credits oc views id i end cache s slots reserve
                                                          fn-octets fn-arena fn-cat))
                                   oc))
  :hints (("Goal" :in-theory '(fn-mca-read-span car-cons fn-sjh-vw-oas-view fn-sjh-vw-refused-read-view
                               fn-sjh-vw-shut-read-view))))

; KEYSTONE (the captured views across the host's served read,
; fn-owner-chunk-span-at): the view and the catalog stay.
(defthm fn-sjh-viewsp-at-owner-chunk-span
  (implies (and (fn-gacc-okp cache) (fn-sjh-colsp pending fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat))
           (fn-sjh-viewsp views
                          (fn-ocfg-owner (fn-own-tls-result-owner
                                          (car (fn-mca-read-span credits oc views id i end cache s slots reserve
                                                                 fn-octets fn-arena fn-cat))))
                          fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-vw-result-viewp fn-sjh-colsp-gives-scol-okp fn-sjh-viewsp-gives-views-okp)
           :use ((:instance fn-sjh-vw-mca-view)
                 (:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-viewsp-of-later-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-own-tls-result-owner
                                                (car (fn-mca-read-span credits oc views id i end cache s slots reserve
                                                                       fn-octets fn-arena fn-cat))))))))))


; -----------------------------------------------------------------------------
; The owner step's events, the store's steps and the host's wrappers.


(defthm fn-sjh-vw-view-of-own-begin
  (equal (fn-own-view (fn-own-begin o id)) (fn-own-view o))
  :hints (("Goal" :in-theory nil :use ((:instance fn-scjs-begin-keeps-fields)))))

(defthm fn-sjh-vw-view-of-own-take
  (equal (fn-own-view (fn-own-take-submission o)) (fn-own-view o))
  :hints (("Goal" :in-theory nil :use ((:instance fn-scjs-take-submission-keeps-fields)))))

(defthm fn-sjh-vw-view-of-own-control-submit
  (equal (fn-own-view (fn-own-control-submit o msgid groups octets)) (fn-own-view o))
  :hints (("Goal" :in-theory nil :use ((:instance fn-scjs-control-submit-keeps-fields)))))

(defthm fn-sjh-vw-view-of-own-operator-submit
  (equal (fn-own-view (fn-own-operator-submit o msgid groups octets stored)) (fn-own-view o))
  :hints (("Goal" :in-theory nil :use ((:instance fn-scjs-operator-submit-keeps-fields)))))

(defthm fn-sjh-vw-view-of-own-bp-transit-submit
  (equal (fn-own-view (fn-own-bp-transit-submit o cfg peer msgid octets id subject)) (fn-own-view o))
  :hints (("Goal" :in-theory nil :use ((:instance fn-scjs-bp-transit-submit-keeps-fields)))))

(defthm fn-sjh-vw-view-of-own-observe
  (equal (fn-own-view (fn-own-observe o obs)) (fn-own-view o))
  :hints (("Goal" :in-theory nil :use ((:instance fn-scjs-observe-keeps-fields)))))

(defthm fn-sjh-vw-view-of-own-declare-group
  (equal (fn-own-view (fn-own-declare-group o name)) (fn-own-view o))
  :hints (("Goal" :in-theory nil :use ((:instance fn-scjs-declare-group-keeps-fields)))))

(defthm fn-sjh-vw-view-of-own-configure
  (equal (fn-own-view (fn-own-configure o config)) (fn-own-view o))
  :hints (("Goal" :in-theory nil :use ((:instance fn-scjs-configure-keeps-fields)))))

(defthm fn-sjh-vw-view-of-own-control-outcome
  (equal (fn-own-view (fn-own-control-outcome o word)) (fn-own-view o))
  :hints (("Goal" :in-theory nil :use ((:instance fn-scjs-control-outcome-keeps-fields)))))

(defthm fn-sjh-vw-view-of-own-bp-transit-outcome
  (equal (fn-own-view (fn-own-bp-transit-outcome o word)) (fn-own-view o))
  :hints (("Goal" :in-theory nil :use ((:instance fn-scjs-bp-transit-outcome-keeps-fields)))))

(defthm fn-sjh-vw-view-of-ocfg-step
  (implies (member-equal (car event)
                         '(:begin :take :control-submit :operator-submit :bp-transit-submit
                           :observe :declare-group :configure :control-outcome :bp-transit-outcome
                           :outcome :transit-outcome :feeds :feed-conn :feed-lost :feed-replay
                           :tick :tick-peer :feed-octets :reconfigure
                           :open :open-peer :advance :close :fault))
           (equal (fn-own-view (fn-ocfg-owner (fn-ocfg-step oc event fn-arena)))
                  (fn-own-view (fn-ocfg-owner oc))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-ocfg-step fn-ocfg-pass fn-own-step fn-sjh-ocfg-owner-of-with-owner
                         fn-sjh-arm-ocfg-reconfigure-owner member-equal (:e member-equal) car-cons cdr-cons
                         fn-sjh-vw-view-of-own-begin fn-sjh-vw-view-of-own-take fn-sjh-vw-view-of-own-control-submit fn-sjh-vw-view-of-own-operator-submit fn-sjh-vw-view-of-own-bp-transit-submit fn-sjh-vw-view-of-own-observe fn-sjh-vw-view-of-own-declare-group fn-sjh-vw-view-of-own-configure fn-sjh-vw-view-of-own-control-outcome fn-sjh-vw-view-of-own-bp-transit-outcome fn-sjh-arm-tick-keeps-store-and-view fn-sjh-arm-tick-peer-keeps-store-and-view fn-sjh-arm-feeds-keeps-store-and-view fn-sjh-arm-feed-connect-keeps-store-and-view fn-sjh-arm-feed-lost-keeps-store-and-view fn-sjh-arm-feed-recover-keeps-store-and-view fn-sjh-arm-feed-reply-keeps-store-and-view fn-sjh-arm-transit-outcome-keeps-store-and-view fn-sjh-arm-outcome-keeps-store-and-view)
                       (theory 'minimal-theory))
           :use ((:instance fn-sjh-ocfg-conn-event-keeps-store-and-view)))))

(defthm fn-sjh-viewsp-of-same-view
  (implies (and (fn-sjh-viewsp views o fn-cat)
                (equal (fn-own-view o2) (fn-own-view o)))
           (fn-sjh-viewsp views o2 fn-cat))
  :hints (("Goal" :use ((:instance fn-sjh-viewsp-of-later-view)))))

; KEYSTONE (the captured views across every fn-owner-step event but the
; store's and the completion; and the connection events).
(defthm fn-sjh-viewsp-of-ocfg-step-view-event
  (implies (and (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
                (member-equal (car event)
                              '(:begin :take :control-submit :operator-submit :bp-transit-submit
                                :observe :declare-group :configure :control-outcome :bp-transit-outcome
                                :outcome :transit-outcome :feeds :feed-conn :feed-lost :feed-replay
                                :tick :tick-peer :feed-octets :reconfigure
                                :open :open-peer :advance :close :fault)))
           (fn-sjh-viewsp views (fn-ocfg-owner (fn-ocfg-step oc event fn-arena)) fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-vw-view-of-ocfg-step fn-sjh-viewsp-of-same-view))))

; KEYSTONE (the store's steps other than its finish: the io steps, the
; retention/consumer/topic prepares, the known abort, the refused
; reservation): the view only ever refreshes forward.
(defthm fn-sjh-viewsp-of-ocfg-store-step
  (implies (and (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (not (member-equal (car ev) '(:finish :crash :recover))))
           (fn-sjh-viewsp views (fn-ocfg-owner (fn-ocfg-step oc (list :store ev) fn-arena)) fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-ocfg-store-step-owner)
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-vw-store-step-version (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-viewsp-of-later-view (o (fn-ocfg-owner oc))
                            (o2 (fn-own-store-step (fn-ocfg-owner oc) ev)))))))

; KEYSTONE (the article POST's prepare, fn-owner-prepare-buffer): staged, the
; store is not idle and the view stays.
(defthm fn-sjh-viewsp-at-owner-prepare-buffer
  (let* ((row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
         (res (fn-pout-prepare-article oc row budget carry)))
    (implies (and (fn-prc-carryp carry)
                  (fn-ocl-relation oc)
                  (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                  (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
                  (equal (mv-nth 0 res) :prepared))
             (fn-sjh-viewsp views (fn-ocfg-owner (mv-nth 1 res)) fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-ocl-facts-for-prepare fn-sjh-viewsp-of-same-view)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-pout-prepared-is-staged
                            (record (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
                 (:instance fn-sjh-pout-prepare-article-next
                            (record (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
                 (:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-sbud-prepare-staged-store
                            (record (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))))))

(defthm fn-sjh-vw-record-staged-not-idle
  (implies (equal (fn-sf-phase (fn-sn-files s)) :record-staged)
           (not (fn-own-store-idlep s)))
  :hints (("Goal" :in-theory (enable fn-own-store-idlep fn-snt-idle-phasep))))

; KEYSTONE (the signed composite's prepare, fn-owner-prepare-identity).
(defthm fn-sjh-viewsp-at-owner-prepare-identity
  (let* ((r (fn-pout-prepare-identity oc w h)))
    (implies (and (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
                  (equal (mv-nth 0 r) :prepared))
             (fn-sjh-viewsp views (fn-ocfg-owner (mv-nth 1 r)) fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-viewsp-of-same-view) (theory 'minimal-theory))
           :use ((:instance fn-sjh-identity-prepared-staging)
                 (:instance fn-sjh-vw-record-staged-not-idle
                            (s (fn-own-store (fn-ocfg-owner (mv-nth 1 (fn-pout-prepare-identity oc w h))))))
                 (:instance fn-sjh-ccar-ocfg-prepare-identity-owner
                            (row (fn-oii-identity-row w (fn-sn-keyring (fn-own-store (fn-ocfg-owner oc)))
                                                      (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner oc)))
                                                      h)))))))

; KEYSTONE (the article finish the host calls, fn-owner-finish-submission:
; fn-apc-own-finish under its carries).
(defthm fn-sjh-viewsp-at-owner-finish-submission
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (res (fn-apc-own-finish o cfg fn-arena fn-hist carry))
         (o2 (cdr res))
         (view2 (fn-own-view o2))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending)))
         (fin (fn-sca-finish token pending (fn-own-view-index view2)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view2))
                             fn-cat)))
    (implies (and (fn-apc-p carry)
                  (fn-hist-of-storep fn-hist s)
                  (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  (equal (car res) :durable)
                  (fn-sjh-viewsp views o fn-cat))
             (fn-sjh-viewsp views o2 (mv-nth 2 fin))))
  :hints (("Goal" :in-theory '(fn-apc-own-finish-is-own-finish fn-ccar-own-finish-is-own-finish)
           :use ((:instance fn-sjh-viewsp-at-host-article-finish)))))

; KEYSTONES (the known abort and the refused reservation: fn-pout-known-abort
; and fn-pout-refuse-reservation are store steps).
(defthm fn-sjh-viewsp-at-owner-known-abort
  (implies (and (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat))
           (fn-sjh-viewsp views (fn-ocfg-owner (mv-nth 1 (fn-pout-known-abort oc fn-arena))) fn-cat))
  :hints (("Goal" :in-theory '(fn-pout-known-abort mv-nth car-cons cdr-cons (:e zp) (:e member-equal) (:e car))
           :use ((:instance fn-sjh-viewsp-of-ocfg-store-step (ev (list :known-abort)))))))

(defthm fn-sjh-viewsp-at-owner-refuse-reservation
  (implies (and (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat))
           (fn-sjh-viewsp views (fn-ocfg-owner (mv-nth 1 (fn-pout-refuse-reservation oc fn-arena))) fn-cat))
  :hints (("Goal" :in-theory '(fn-pout-refuse-reservation mv-nth car-cons cdr-cons (:e zp) (:e member-equal) (:e car))
           :use ((:instance fn-sjh-viewsp-of-ocfg-store-step
                            (ev (list :refuse-reservation
                                      (1- (fn-sf-frontier (fn-sn-files (fn-sbud-oc-store oc)))))))))))

; KEYSTONES (the wrappers that keep the view).
(defthm fn-sjh-viewsp-at-owner-begin
  (implies (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
           (fn-sjh-viewsp views (fn-ocfg-owner (mv-nth 1 (fn-pout-begin oc id fn-arena))) fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-pout-begin) (fn-ocfg-step fn-sjh-viewsp fn-pout-begin-admitsp))
           :use ((:instance fn-sjh-viewsp-of-ocfg-step-view-event (event (list :begin id)))))))

(defthm fn-sjh-viewsp-at-owner-declare-group
  (implies (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
           (fn-sjh-viewsp views (fn-ocfg-owner (mv-nth 1 (fn-pout-declare-group oc name fn-arena))) fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-pout-declare-group) (fn-ocfg-step fn-sjh-viewsp fn-pout-declare-group-admitsp))
           :use ((:instance fn-sjh-viewsp-of-ocfg-step-view-event (event (list :declare-group name)))))))

(defthm fn-sjh-viewsp-at-owner-observe
  (implies (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
           (fn-sjh-viewsp views (fn-ocfg-owner (fn-ocfg-observe oc obs)) fn-cat))
  :hints (("Goal" :in-theory '(fn-ocfg-observe fn-sjh-ocfg-owner-of-with-owner fn-sjh-vw-view-of-own-observe
                               fn-sjh-viewsp-of-same-view))))

(defthm fn-sjh-viewsp-at-owner-node-secret
  (implies (fn-sjh-viewsp views o fn-cat)
           (fn-sjh-viewsp views (fn-own-with-node-secret o ring) fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-with-node-secret) (fn-sjh-viewsp))
           :use ((:instance fn-sjh-viewsp-of-same-view (o2 (fn-own-with-node-secret o ring)))))))

(defthm fn-sjh-viewsp-at-owner-install-profile
  (implies (fn-sjh-viewsp views o fn-cat)
           (fn-sjh-viewsp views (mv-nth 1 (fn-osb-install o profile)) fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-osb-install fn-sjh-vw-view-of-own-configure fn-sjh-viewsp-of-same-view)
                                  (fn-sjh-viewsp fn-own-configure fn-bs-profile-admittedp fn-osb-config)))))

(defthm fn-sjh-viewsp-at-owner-configure
  (implies (fn-sjh-viewsp views o fn-cat)
           (fn-sjh-viewsp views (fn-own-configure o config) fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-vw-view-of-own-configure fn-sjh-viewsp-of-same-view))))

(defthm fn-sjh-viewsp-at-owner-outcome
  (implies (and (fn-icar-carryp icar) (fn-apc-p carry)
                (fn-sjh-viewsp views o fn-cat))
           (fn-sjh-viewsp views (cdr (fn-apc-own-outcome o id word icar carry)) fn-cat))
  :hints (("Goal" :in-theory '(fn-apc-own-outcome-is-acar-own-outcome fn-sjh-arm-acar-outcome-keeps-store-and-view
                               fn-sjh-viewsp-of-same-view))))

(defthm fn-sjh-viewsp-at-owner-transit-outcome
  (implies (fn-sjh-viewsp views o fn-cat)
           (fn-sjh-viewsp views (cdr (fn-own-transit-outcome o id kind reason word)) fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-arm-transit-outcome-keeps-store-and-view fn-sjh-viewsp-of-same-view))))

(defthm fn-sjh-viewsp-at-owner-feed-port
  (implies (fn-sjh-viewsp views o fn-cat)
           (fn-sjh-viewsp views (fn-own-with-feeds o feeds) fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-arm-with-feeds-keeps-store-and-view fn-sjh-viewsp-of-same-view))))

(defthm fn-sjh-viewsp-at-owner-unstage
  (equal (fn-sjh-viewsp views (fn-ocfg-owner (fn-psrv-unstage oc)) fn-cat)
         (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-okp-at-owner-unstage))))

(defthm fn-sjh-viewsp-at-owner-open-peer
  (implies (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
           (fn-sjh-viewsp views (fn-ocfg-owner (cdr (fn-ocfg-open-peer oc peer acfg))) fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-step) (fn-sjh-viewsp fn-ocfg-open-peer fn-ocfg-open fn-ocfg-advance
                                                  fn-ocfg-close fn-ocfg-fault fn-ocfg-read fn-ocfg-read-step
                                                  fn-ocfg-reconfigure fn-ocfg-complete fn-ocfg-pass))
           :use ((:instance fn-sjh-viewsp-of-ocfg-step-view-event (event (list :open-peer peer nil acfg)))))))

(defthm fn-sjh-viewsp-at-owner-open
  (implies (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
           (fn-sjh-viewsp views (fn-ocfg-owner (cdr (fn-ocar-ocfg-open oc acfg))) fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-viewsp-of-same-view)
           :use ((:instance fn-sjh-op-ocar-ocfg-open-facts2 (n 0))))))

(defthm fn-sjh-viewsp-at-owner-open-captured
  (implies (fn-sjh-viewsp views2 (fn-ocfg-owner oc) fn-cat)
           (fn-sjh-viewsp views2
                          (fn-ocfg-owner (fn-ocfg-with-view (cdr (fn-ocar-ocfg-open (fn-ocfg-at-reader-view oc views) acfg))
                                                            (fn-own-view (fn-ocfg-owner oc))))
                          fn-cat))
  :hints (("Goal" :in-theory '(fn-ocfg-with-view-keeps-the-rest fn-sjh-viewsp-of-same-view))))

(defthm fn-sjh-viewsp-at-owner-exposure-open
  (implies (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
           (fn-sjh-viewsp views (fn-ocfg-owner (fn-exp-open-ocfg (fn-ocar-exp-open oc xs lim acfg peer address now)))
                          fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-ocar-exp-open fn-exp-open-ocfg fn-exp-at)
                                  (fn-ocar-ocfg-open fn-ocfg-open-peer fn-sjh-viewsp fn-exp-admit-decision
                                   fn-exp-register fn-exp-pinned-acfg fn-exp-with fn-exp-counters-bump
                                   fn-exp-line fn-sjh-op-ocar-ocfg-open-owner))
           :use ((:instance fn-sjh-viewsp-at-owner-open (acfg (fn-exp-pinned-acfg acfg lim)))
                 (:instance fn-sjh-viewsp-at-owner-open-peer (acfg (fn-exp-pinned-acfg acfg lim)))))))

; KEYSTONE (the wire read steps, fn-ocfg-read-step): the view stays.
(defthm fn-sjh-viewsp-at-owner-read-step
  (implies (and (fn-ocl-relation oc)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat))
           (fn-sjh-viewsp views (fn-ocfg-owner (cdr (fn-ocfg-read-step oc id event fn-arena))) fn-cat))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-versions-okp fn-sjh-rs-ocfg-read-step-owner fn-sjh-viewsp-of-same-view)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-invp-conns (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-invp-gives-live-okp (o (fn-ocfg-owner oc)))
                 (:instance fn-scar-ocl-relation-carries-node-statep)
                 (:instance fn-sjh-rs-read-step-owner-facts (o (fn-ocfg-owner oc)))))))

; KEYSTONE (the live configuration's completion, fn-oclc-publish): the
; carried configure keeps the store's history, so the refreshed view is no
; older.
(defthm fn-sjh-vw-owner-with-store-version
  (implies (and (fn-scjs-historyp o)
                (equal (fn-sn-files st) (fn-sn-files (fn-own-store o))))
           (<= (nfix (fn-own-view-version (fn-own-view o)))
               (nfix (fn-own-view-version (fn-own-view (fn-ocl-owner-with-store o st))))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-owner-with-store fn-scjs-historyp fn-sjh-refresh-version)
                                  (fn-own-refresh fn-own-store-idlep)))))

(defthm fn-sjh-viewsp-at-owner-reconfigure-complete
  (implies (and (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat))
           (fn-sjh-viewsp views (fn-ocfg-owner (mv-nth 1 (fn-oclc-publish oc generation max-octets))) fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-oclc-publish fn-oclc-complete fn-sjh-ocfg-owner-of-with-owner fn-sjh-rc-configure-view
                                   fn-ocfg-owner-of-fn-ocfg-make)
                                  (fn-sjh-viewsp fn-own-configure fn-oag-post-config fn-cfg-record-generation
                                   fn-ocfg-with-owner fn-oclc-configure fn-ocl-owner-with-store fn-sjh-okp))
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-rc-configure-store-fields
                            (s (fn-own-store (fn-ocfg-owner oc))) (config (fn-ocfg-config oc))
                            (record (fn-ocfg-staged oc)))
                 (:instance fn-sjh-vw-owner-with-store-version
                            (o (fn-ocfg-owner oc))
                            (st (mv-nth 0 (fn-oclc-configure (fn-own-store (fn-ocfg-owner oc))
                                                             (fn-ocfg-config oc) (fn-ocfg-staged oc)))))
                 (:instance fn-sjh-viewsp-of-later-view
                            (o (fn-ocfg-owner oc))
                            (o2 (fn-ocl-owner-with-store (fn-ocfg-owner oc)
                                                         (mv-nth 0 (fn-oclc-configure (fn-own-store (fn-ocfg-owner oc))
                                                                                      (fn-ocfg-config oc)
                                                                                      (fn-ocfg-staged oc))))))))))

; The opens start with no capture held (the committer captures only while it
; holds a batch; fn-owner-reader-views is nil at a start).
(defthm fn-sjh-viewsp-at-open
  (fn-sjh-viewsp nil o fn-cat)
  :hints (("Goal" :in-theory (enable fn-sjh-viewsp))))

(defthm fn-sjh-viewsp-of-ocfg-io-run
  (implies (and (fn-sjh-io-eventsp events)
                (fn-sjh-io-run-premisesp oc events fn-arena)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat))
           (fn-sjh-viewsp views (fn-ocfg-owner (fn-ocfg-run oc events fn-arena)) fn-cat))
  :hints (("Goal" :induct (fn-ocfg-run oc events fn-arena)
           :in-theory (union-theories '(fn-ocfg-run fn-sjh-io-eventsp fn-sjh-io-run-premisesp car-cons cdr-cons
                                        (:e member-equal) (:e car))
                                      (theory 'minimal-theory)))
          ("Subgoal *1/1" :use ((:instance fn-sjh-io-eventp-shape (e (car events)))
                                (:instance fn-sjh-okp-of-ocfg-io
                                           (operation (cadr (cadr (car events))))
                                           (result (caddr (cadr (car events)))))
                                (:instance fn-sjh-viewsp-of-ocfg-store-step
                                           (ev (list :io (cadr (cadr (car events))) (caddr (cadr (car events))))))))))


; KEYSTONES (fn-owner-io :log-reserve and :log-order).
(defthm fn-sjh-viewsp-at-owner-log-reserve
  (implies (and (fn-sjh-io-run-premisesp oc *fn-sjh-log-reserve-events* fn-arena)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat))
           (fn-sjh-viewsp views (fn-ocfg-owner (fn-olr-ocfg-reserve oc)) fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-olr-ocfg-reserve-is-the-file-route-by-definition
                                               fn-ocfg-run car-cons cdr-cons (:e fn-sjh-io-eventsp)
                                               (:e consp) (:e car) (:e cdr))
                                             (theory 'minimal-theory))
           :use ((:instance fn-sjh-viewsp-of-ocfg-io-run (events *fn-sjh-log-reserve-events*))))))

(defthm fn-sjh-viewsp-at-owner-log-order
  (implies (and (fn-sjh-io-run-premisesp oc *fn-sjh-log-order-events* fn-arena)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat))
           (fn-sjh-viewsp views (fn-ocfg-owner (fn-olr-ocfg-order oc)) fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-olr-ocfg-order-is-the-file-route-by-definition
                                               fn-ocfg-run car-cons cdr-cons (:e fn-sjh-io-eventsp)
                                               (:e consp) (:e car) (:e cdr))
                                             (theory 'minimal-theory))
           :use ((:instance fn-sjh-viewsp-of-ocfg-io-run (events *fn-sjh-log-order-events*))))))

; The captured open's and the read's named premise, discharged: with the
; views carried, fn-sjh-views-okp holds (fn-sjh-viewsp-gives-views-okp).
(defthm fn-sjh-okp-at-owner-open-captured-carried
  (let ((o2 (fn-ocfg-owner
             (fn-ocfg-with-view (cdr (fn-ocar-ocfg-open (fn-ocfg-at-reader-view oc views) acfg))
                                (fn-own-view (fn-ocfg-owner oc))))))
    (implies (and (consp views)
                  (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                  (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat))
             (fn-sjh-okp o2 pending fn-arena fn-cat)))
  :hints (("Goal" :in-theory '(fn-sjh-viewsp-gives-views-okp)
           :use ((:instance fn-sjh-okp-at-owner-open-captured)))))

(defthm fn-sjh-okp-at-owner-chunk-span-fully-carried
  (implies (and (fn-gacc-okp cache) (fn-sjh-colsp pending fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat))
           (fn-sjh-okp (fn-ocfg-owner
                        (fn-own-tls-result-owner
                         (car (fn-mca-read-span credits oc views id i end cache s slots reserve
                                                fn-octets fn-arena fn-cat))))
                       pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-viewsp-gives-views-okp)
           :use ((:instance fn-sjh-okp-at-owner-chunk-span-carried)))))
