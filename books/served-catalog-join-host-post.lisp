; served-catalog-join-host-post.lisp -- the catalog join carried across the
; host's article POST (lane join-f2, 2026-09-28; PRF-302).
;
; host/native/owner.lisp fnn-owner-attempt, under the service mutex: the
; host's prepare (host/owner-host.lisp fn-owner-prepare-buffer: the store
; stages the row fn-apc-intern-row-at builds at the arena's count, through
; fn-pout-prepare-article), the seal of the buffer holding the record's
; payload (fnn-seal-live-buffer: fn-arena-seal-buffer), and the catalog's
; prepare of that row (fn-owner-cat-prepare-sealed: fn-cat-prepare-sealed,
; which the host installs as its pending row).  From fn-sjh-okp at the
; reserved store, fn-sjh-okp holds after with the new pending row: LINK names
; the staged row, which the seal made a well-formed composite in the arena.

(in-package "ACL2")

(include-book "served-catalog-join-host")
(include-book "owner-prepare-outcome") ; fn-pout-prepare-article: the prepare the host calls

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The arena grows at its end: what a held row reads survives a seal.

(defthm fn-sjh-seal-buffer-is-seal-list
  (equal (fn-arena-seal-buffer fn-octets fn-arena)
         (fn-arena-seal-list (fn-octets-list fn-octets) fn-arena))
  :hints (("Goal" :use ((:instance fn-cat-intern-is-intern-list))
           :in-theory (e/d (fn-cat-intern fn-cat-intern-list fn-held-wire)
                           (fn-cat-intern-is-intern-list)))))

(defthm fn-sjh-nth-of-append-below-len
  (implies (and (natp i) (< i (len a)))
           (equal (nth i (append a b)) (nth i a)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm fn-sjh-row-wire-of-held-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-held-p h) (fn-row-handle-inp h fn-arena))
           (and (equal (fn-row-wire-of h (fn-arena-seal-list xs fn-arena))
                       (fn-row-wire-of h fn-arena))
                (fn-row-handle-inp h (fn-arena-seal-list xs fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-row-wire-of fn-row-bytes fn-row-handle-inp
                                   fn-held-wire-of fn-arena-payload-is-nth
                                   fn-arena-seal-list-is-append fn-arena-count-is-len)
                                  (fn-held-p fn-held-wire)))))

(defthm fn-sjh-rows-survive-seal
  (implies (and (fn-arena-p fn-arena)
                (fn-rows-handles-inp rows fn-arena)
                (fn-rows-composites-okp rows fn-arena))
           (and (fn-rows-composites-okp rows (fn-arena-seal-list xs fn-arena))
                (fn-rows-handles-inp rows (fn-arena-seal-list xs fn-arena))))
  :hints (("Goal" :induct (fn-rows-composites-okp rows fn-arena)
           :in-theory (e/d (fn-rows-composites-okp fn-rows-handles-inp fn-row-composite-okp)
                           (fn-held-p fn-hstxa-p fn-row-wire-of fn-row-handle-inp
                            fn-arena-seal-list-is-append fn-record-p fn-stxa-p fn-replay-composite-record)))
          ("Subgoal *1/2" :cases ((fn-held-p (car rows)) (fn-hstxa-p (car rows)))
           :use ((:instance fn-sjh-row-wire-of-held-survives-seal (h (car rows)))
                 (:instance fn-sjh-row-wire-of-held-survives-seal (h (fn-hstxa-held (car rows))))))))

; -----------------------------------------------------------------------------
; The POST's row: interned at the arena's count, it is a held row whose handle
; is that count; after the seal of its record's payload it materializes to the
; record.

(local
 (defthm fn-sjh-len-of-make-list-ac
   (implies (natp n) (equal (len (make-list-ac n val acc)) (+ n (len acc))))
   :hints (("Goal" :induct (make-list-ac n val acc)))))

(defthm fn-sjh-len-of-make-list
  (implies (natp n) (equal (len (make-list-ac n val nil)) n)))

(defthm fn-sjh-intern-row-held-p
  (implies (and (fn-record-p w) (natp generation) (natp h))
           (fn-held-p (fn-intern-row-at w keyring generation h)))
  :hints (("Goal" :in-theory (union-theories '(fn-arena-count-is-len fn-sjh-len-of-make-list natp nfix)
                                             (theory 'minimal-theory))
           :use ((:instance fn-held-p-of-intern-list (fn-arena (make-list h)))
                 (:instance fn-cat-intern-list-is-row-at-count (fn-arena (make-list h)))))))

(defthm fn-sjh-intern-row-fields
  (let ((row (fn-intern-row-at w keyring generation h)))
    (and (equal (fn-record-payload row) h)
         (equal (fn-record-txid row) (fn-record-txid w))
         (not (fn-held-withdrawn row))))
  :hints (("Goal" :in-theory (enable fn-intern-row-at fn-record-internals fn-held-internals))))

(defthm fn-sjh-record-p-shapep
  (implies (fn-record-p w) (fn-record-shapep w))
  :hints (("Goal" :in-theory (enable fn-record-p))))

(defthm fn-sjh-sealed-row-facts
  (implies (and (fn-record-p w) (natp generation) (fn-arena-p fn-arena))
           (let ((row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
                 (a2 (fn-arena-seal-list (fn-record-payload w) fn-arena)))
             (and (equal (fn-row-wire-of row a2) w)
                  (fn-row-composite-okp row a2)
                  (fn-rows-handles-inp (list row) a2)
                  (fn-scj-rows-clearp (list row))
                  (equal (fn-scj-load-h row) row))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-row-wire-of fn-row-bytes fn-held-wire-of fn-row-composite-okp
                            fn-rows-handles-inp fn-row-handle-inp fn-scj-rows-clearp)
                           (fn-intern-row-at fn-held-p fn-record-p fn-held-wire fn-cat-intern-list
                            fn-arena-seal-list-is-append fn-arena-payload-is-nth fn-arena-count-is-len
                            fn-scj-load-h fn-hstxa-p))
           :use ((:instance fn-cat-intern-list-materializes)
                 (:instance fn-cat-intern-list-is-row-at-count)
                 (:instance fn-sjh-intern-row-held-p (h (fn-arena-count fn-arena)))
                 (:instance fn-sjh-load-h-of-held (r (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
                 (:instance fn-snt-an-article-record-is-no-other-store-event
                            (record (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
                 (:instance fn-arena-seal-count (xs (fn-record-payload w)))))))

; -----------------------------------------------------------------------------
; The store's staging with the seal and the catalog's prepare.

(defthm fn-sjh-stage-record-fields
  (implies (and (equal (fn-sf-phase files) :reserved)
                (equal (fn-sf-phase (fn-spc-stage-record files row)) :record-staged))
           (let ((files2 (fn-spc-stage-record files row)))
             (and (equal (fn-sf-records files2) (fn-sf-records files))
                  (equal (fn-sf-record-candidate files2) row))))
  :hints (("Goal" :in-theory (enable fn-spc-stage-record))))

(defthm fn-sjh-files-okp-of-post-stage
  (let* ((row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
         (files2 (fn-spc-stage-record files row))
         (arena2 (fn-arena-seal-buffer fn-octets fn-arena))
         (pc (fn-cat-prepare-sealed w row plan reservation nil arena2 fn-cat)))
    (implies (and (fn-sjh-files-okp files nil fn-arena fn-cat)
                  (fn-arena-p fn-arena)
                  (fn-record-p w) (natp generation)
                  (equal (fn-octets-list fn-octets) (fn-record-payload w))
                  (equal (fn-sf-phase files) :reserved)
                  (equal (fn-sf-phase files2) :record-staged))
             (and (fn-sjh-files-okp files2 pc arena2 fn-cat)
                  (fn-rows-handles-inp (fn-sf-records files2) arena2)
                  (fn-rows-handles-inp (list row) arena2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sjh-files-okp fn-sjh-files-linkp fn-sjh-inflight fn-sf-record-phasep
                            fn-sjh-seal-buffer-is-seal-list fn-sf-record-pair)
                           (fn-intern-row-at fn-spc-stage-record fn-cat-prepare-sealed fn-pc-p
                            fn-row-composite-okp fn-rows-composites-okp fn-scj-rows-clearp
                            fn-rows-handles-inp fn-scj-load-h fn-record-p fn-held-p
                            fn-arena-seal-list-is-append fn-arena-seal-buffer-is-append
                            fn-store-event-txid))
           :use ((:instance fn-sjh-stage-record-fields
                            (row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
                 (:instance fn-sjh-sealed-row-facts)
                 (:instance fn-sjh-rows-survive-seal (rows (fn-sf-records files)) (xs (fn-record-payload w)))
                 (:instance fn-cat-prepare-sealed-names-the-sealed-handle)
                 (:instance fn-sjh-intern-row-held-p (h (fn-arena-count fn-arena)))
                 (:instance fn-sjh-intern-row-fields (h (fn-arena-count fn-arena)))
                 (:instance fn-cat-intern-list-is-row-at-count)
                 (:instance (:definition fn-store-event-txid)
                            (x (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))))))

; -----------------------------------------------------------------------------
; The catalog invariant reads no arena: the catalog's rows carry their
; handles, not their bytes (fn-cat-row-article).

(defthm fn-sjh-view-below-arena-free
  (equal (fn-cat-view-below i v a1 fn-cat) (fn-cat-view-below i v a2 fn-cat))
  :rule-classes nil
  :hints (("Goal" :induct (fn-cat-view-below i v a1 fn-cat)
           :in-theory (enable fn-cat-view-below fn-cat-row-article))))

(defthm fn-sjh-view-articles-arena-free
  (implies (syntaxp (not (equal fn-arena ''nil)))
           (equal (fn-cat-view-articles v fn-arena fn-cat)
                  (fn-cat-view-articles v nil fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-view-articles)
           :use ((:instance fn-sjh-view-below-arena-free (i (fn-cat-count fn-cat))
                            (a1 fn-arena) (a2 nil))))))

(defthm fn-sjh-scr-catalogp-arena-free
  (implies (syntaxp (not (equal fn-arena ''nil)))
           (equal (fn-scr-catalogp archive index v fn-arena fn-cat)
                  (fn-scr-catalogp archive index v nil fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-scr-catalogp) (fn-cat-view-articles)))))

(defthm fn-sjh-conns-pinp-arena-free
  (implies (syntaxp (not (equal fn-arena ''nil)))
           (equal (fn-scj-conns-pinp conns fn-arena fn-cat)
                  (fn-scj-conns-pinp conns nil fn-cat)))
  :hints (("Goal" :induct (fn-scj-conns-pinp conns fn-arena fn-cat)
           :in-theory (e/d (fn-scj-conns-pinp fn-scj-conn-pinp) (fn-scr-catalogp)))))

(defthm fn-sjh-invp-arena-free
  (implies (syntaxp (not (equal fn-arena ''nil)))
           (equal (fn-scj-invp o fn-arena fn-cat)
                  (fn-scj-invp o nil fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-scj-invp fn-scj-joinp fn-scj-live-okp fn-scr-live-catalogp
                                   fn-scr-fields-catalogp)
                                  (fn-scr-catalogp fn-cat-view-articles fn-scj-conns-pinp
                                   fn-scj-rows-invp fn-scj-vvp fn-own-view-live)))))

(in-theory (disable fn-sjh-view-articles-arena-free fn-sjh-scr-catalogp-arena-free
                    fn-sjh-conns-pinp-arena-free fn-sjh-invp-arena-free))

; -----------------------------------------------------------------------------
; The owner's side of the staging.

(defthm fn-sjh-files-okp-at-reserved-has-no-pending
  (implies (and (fn-sjh-files-okp files pending fn-arena fn-cat)
                (equal (fn-sf-phase files) :reserved))
           (and (not pending)
                (fn-sjh-files-okp files nil fn-arena fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sjh-files-okp fn-sjh-files-linkp fn-sjh-inflight fn-sf-record-phasep))))

(defthm fn-sjh-sbud-prepare-staged-store
  (let ((s (fn-own-store (fn-ocfg-owner oc)))
        (s2 (fn-own-store (fn-ocfg-owner (fn-pcar-sbud-prepare oc record budget)))))
    (implies (fn-pout-stagedp s s2)
             (and (equal s2 (fn-spc-prepare s record))
                  (equal (fn-own-view (fn-ocfg-owner (fn-pcar-sbud-prepare oc record budget)))
                         (fn-own-view (fn-ocfg-owner oc)))
                  (equal (fn-own-conns (fn-ocfg-owner (fn-pcar-sbud-prepare oc record budget)))
                         (fn-own-conns (fn-ocfg-owner oc))))))
  :hints (("Goal" :in-theory (e/d (fn-pcar-sbud-prepare-is-sbud-prepare fn-sbud-prepare fn-opc-prepare
                                   fn-opc-owner-prepare fn-ocfg-with-owner fn-pout-stagedp fn-own-refresh
                                   fn-ocl-owner-with-store
                                   fn-own-store-idlep fn-snt-idle-phasep)
                                  (fn-spc-prepare fn-sbud-admitp fn-pcar-sbud-prepare
                                   fn-ctl-refresh-visible fn-ctl-refresh-withdrawals fn-ctl-refresh-withdrawn
                                   fn-midx-refresh fn-gidx-refresh fn-ctl-visible-state-of)))))

(defthm fn-sjh-sn-update-files
  (equal (fn-sn-files (fn-sn-update s files node)) files)
  :hints (("Goal" :in-theory (enable fn-sn-update fn-sn-make-v6 fn-sn-files))))

(defthm fn-sjh-spc-prepare-staged-files
  (implies (and (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                (equal (fn-sf-phase (fn-sn-files (fn-spc-prepare s record))) :record-staged))
           (equal (fn-sn-files (fn-spc-prepare s record))
                  (fn-spc-stage-record (fn-sn-files s) record)))
  :hints (("Goal" :in-theory (e/d (fn-spc-prepare) (fn-spc-stage-record fn-sn-statep fn-sn-prepare-node
                                                    fn-sn-record-bindsp fn-cpe-projection-step fn-sn-update)))))

(defthm fn-sjh-versionsp-is-versions-okp
  (equal (fn-scjs-versionsp o) (fn-scj-versions-okp o))
  :hints (("Goal" :in-theory '(fn-scjs-versionsp fn-scj-versions-okp))))

(defthm fn-sjh-historyp-of-same-view-and-records
  (implies (and (fn-scjs-historyp o)
                (equal (fn-own-view o2) (fn-own-view o))
                (equal (fn-sf-records (fn-sn-files (fn-own-store o2)))
                       (fn-sf-records (fn-sn-files (fn-own-store o)))))
           (fn-scjs-historyp o2))
  :hints (("Goal" :in-theory (enable fn-scjs-historyp))))

(defthm fn-sjh-indexedp-of-same-view
  (implies (and (fn-scar-view-indexedp o)
                (equal (fn-own-view o2) (fn-own-view o)))
           (fn-scar-view-indexedp o2))
  :hints (("Goal" :in-theory (enable fn-scar-view-indexedp))))

; KEYSTONE (the join carried across the host's article POST).  The host's
; prepare stages the row the arena's count names (over fn-pcar-sbud-prepare,
; the prepare the host's fn-pout-prepare-article equals under the carried
; recognizers: below), seals the record's payload and prepares the catalog's
; pending row: from fn-sjh-okp at the reserved store, fn-sjh-okp with that row.
(defthm fn-sjh-okp-of-post-prepare-sealed
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
         (o2 (fn-ocfg-owner (fn-pcar-sbud-prepare oc row budget)))
         (arena2 (fn-arena-seal-buffer fn-octets fn-arena))
         (pc (fn-cat-prepare-sealed w row plan reservation nil arena2 fn-cat)))
    (implies (and (fn-sjh-okp o pending fn-arena fn-cat)
                  (fn-arena-p fn-arena)
                  (fn-record-p w) (natp generation)
                  (equal (fn-octets-list fn-octets) (fn-record-payload w))
                  (fn-pout-stagedp s (fn-own-store o2))
                  (fn-statep (fn-own-view-archive (fn-own-view o2))))
             (fn-sjh-okp o2 pc arena2 fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-okp fn-sjh-versionsp-is-versions-okp fn-sjh-invp-arena-free
                                        fn-sjh-historyp-of-same-view-and-records
                                        fn-sjh-indexedp-of-same-view)
                                      (theory 'minimal-theory))
           :use ((:instance fn-pout-stagedp (before (fn-own-store (fn-ocfg-owner oc)))
                            (after (fn-own-store (fn-ocfg-owner (fn-pcar-sbud-prepare oc (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)) budget)))))
                 (:instance fn-sjh-sbud-prepare-staged-store
                            (record (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
                 (:instance fn-sjh-spc-prepare-staged-files (s (fn-own-store (fn-ocfg-owner oc)))
                            (record (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
                 (:instance fn-sjh-files-okp-at-reserved-has-no-pending
                            (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                 (:instance fn-sjh-files-okp-of-post-stage (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                 (:instance fn-sjh-stage-record-fields (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                            (row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
                 (:instance fn-scjs-pcar-sbud-prepare-keeps-invp
                            (record (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
                 (:instance fn-scjs-pcar-sbud-prepare-keeps-versions
                            (record (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))))))

; -----------------------------------------------------------------------------
; The host's call: fn-pout-prepare-article's :prepared is the staging, and
; its owner is fn-pcar-sbud-prepare's under the carried recognizers.

(defthm fn-sjh-pout-prepare-article-next
  (implies (and (fn-prc-carryp carry)
                (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner oc)))
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-pout-stagedp (fn-own-store (fn-ocfg-owner oc))
                                 (fn-own-store (fn-ocfg-owner (mv-nth 1 (fn-pout-prepare-article oc record budget carry))))))
           (equal (mv-nth 1 (fn-pout-prepare-article oc record budget carry))
                  (fn-pcar-sbud-prepare oc record budget)))
  :hints (("Goal" :in-theory (e/d (fn-pout-prepare-article fn-psrv-prepare fn-pout-stagedp
                                   fn-prc-sbud-prepare-is-pidx-sbud-prepare
                                   fn-pidx-sbud-prepare-is-pcar-sbud-prepare)
                                  (fn-pcar-sbud-prepare fn-prc-sbud-prepare fn-pidx-sbud-prepare
                                   fn-psrv-event-servedp fn-psrv-refusal-kind fn-ocl-view-visiblep
                                   fn-scar-view-indexedp)))))

(defthm fn-sjh-pout-prepared-is-staged
  (implies (equal (mv-nth 0 (fn-pout-prepare-article oc record budget carry)) :prepared)
           (fn-pout-stagedp (fn-own-store (fn-ocfg-owner oc))
                            (fn-own-store (fn-ocfg-owner (mv-nth 1 (fn-pout-prepare-article oc record budget carry))))))
  :hints (("Goal" :in-theory (e/d (fn-pout-prepare-article fn-psrv-refusal-kind fn-sbud-refusal-kind
                                   fn-sbud-oc-store)
                                  (fn-psrv-prepare fn-pout-stagedp fn-sbud-admitp fn-psrv-event-servedp)))))

(defthm fn-sjh-ocl-facts-for-prepare
  (implies (fn-ocl-relation oc)
           (and (fn-statep (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc))))
                (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner oc)))))
  :hints (("Goal" :in-theory '(fn-acar-view-statep fn-ocl-relation)
           :use ((:instance fn-acar-ocl-relation-carries-view-statep)
                 (:instance fn-ocl-view-historyp-is-visible (o (fn-ocfg-owner oc)))))))

; KEYSTONE (the host's form): host/owner-host.lisp fn-owner-prepare-buffer
; calls fn-pout-prepare-article over the row fn-apc-intern-row-at builds at
; the arena's count (fn-intern-row-at under the parse carry,
; fn-apc-intern-row-at-is-reference) and answers :seal-buffer exactly when
; it answered :prepared; host/native/owner.lisp fnn-owner-attempt then seals
; the buffer holding the record's payload and calls fn-owner-cat-prepare-
; sealed, which installs fn-cat-prepare-sealed's pending row.
(defthm fn-sjh-okp-at-owner-prepare-buffer
  (let* ((o (fn-ocfg-owner oc))
         (row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
         (res (fn-pout-prepare-article oc row budget carry))
         (o2 (fn-ocfg-owner (mv-nth 1 res)))
         (arena2 (fn-arena-seal-buffer fn-octets fn-arena))
         (pc (fn-cat-prepare-sealed w row plan reservation nil arena2 fn-cat)))
    (implies (and (fn-prc-carryp carry)
                  (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  (fn-arena-p fn-arena)
                  (fn-record-p w) (natp generation)
                  (equal (fn-octets-list fn-octets) (fn-record-payload w))
                  (equal (mv-nth 0 res) :prepared))
             (fn-sjh-okp o2 pc arena2 fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-ocl-facts-for-prepare)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-pout-prepared-is-staged
                            (record (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
                 (:instance fn-sjh-pout-prepare-article-next
                            (record (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
                 (:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-sbud-prepare-staged-store
                            (record (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
                 (:instance fn-sjh-okp-of-post-prepare-sealed)))))
