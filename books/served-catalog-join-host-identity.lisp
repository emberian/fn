; served-catalog-join-host-identity.lisp -- the catalog join carried across
; the host's identity events (lane join-f2, 2026-09-28; PRF-302).
;
; host/owner-host.lisp fn-owner-prepare-identity stages the row
; fn-oii-identity-row makes of the event at the arena's count (through
; fn-pout-prepare-identity).  A signed composite (fn-oii-identity-sealsp)
; seals its article's payload and the catalog prepares the composite's held
; row (fn-owner-cat-prepare-sealed); a keyring snapshot or a standalone
; verdict loads no catalog row and leaves no pending row.  From fn-sjh-okp at
; the reserved store, fn-sjh-okp holds after either.

(in-package "ACL2")

(include-book "served-catalog-join-host-post")

(local (in-theory (disable (tau-system))))

(defthm fn-sjh-ccar-sn-prepare-identity-changed
  (implies (not (equal (fn-ccar-sn-prepare-identity s row) s))
           (and (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                (equal (fn-sn-files (fn-ccar-sn-prepare-identity s row))
                       (fn-spc-stage-record (fn-sn-files s) row))
                (equal (fn-sf-phase (fn-sn-files (fn-ccar-sn-prepare-identity s row))) :record-staged)))
  :hints (("Goal" :in-theory '(fn-ccar-sn-prepare-identity fn-sjh-sn-update-files
                               fn-pcar-stage-record-is-stage-record))))

(defthm fn-sjh-ccar-ocfg-prepare-identity-store
  (equal (fn-own-store (fn-ocfg-owner (fn-ccar-ocfg-prepare-identity oc row)))
         (fn-ccar-sn-prepare-identity (fn-own-store (fn-ocfg-owner oc)) row))
  :hints (("Goal" :in-theory (e/d (fn-ccar-ocfg-prepare-identity fn-ocfg-with-owner fn-own-refresh)
                                  (fn-ccar-sn-prepare-identity fn-own-store-idlep
                                   fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-ctl-visible-state-of)))))

(defthm fn-sjh-ccar-ocfg-prepare-identity-owner
  (let ((o2 (fn-ocfg-owner (fn-ccar-ocfg-prepare-identity oc row)))
        (s (fn-own-store (fn-ocfg-owner oc))))
    (implies (not (fn-own-store-idlep (fn-ccar-sn-prepare-identity s row)))
             (and (equal (fn-own-store o2) (fn-ccar-sn-prepare-identity s row))
                  (equal (fn-own-view o2) (fn-own-view (fn-ocfg-owner oc)))
                  (equal (fn-own-conns o2) (fn-own-conns (fn-ocfg-owner oc))))))
  :hints (("Goal" :in-theory (e/d (fn-ccar-ocfg-prepare-identity fn-ocfg-with-owner fn-own-refresh)
                                  (fn-ccar-sn-prepare-identity fn-own-store-idlep
                                   fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-ctl-visible-state-of)))))

(defthm fn-sjh-identity-prepared-next
  (let* ((s (fn-own-store (fn-ocfg-owner oc)))
         (row (fn-oii-identity-row w (fn-sn-keyring s) (fn-sn-keyring-generation s) h)))
    (implies (equal (mv-nth 0 (fn-pout-prepare-identity oc w h)) :prepared)
             (and (equal (mv-nth 1 (fn-pout-prepare-identity oc w h))
                         (fn-ccar-ocfg-prepare-identity oc row))
                  (not (equal (fn-ccar-sn-prepare-identity s row) s)))))
  :hints (("Goal" :do-not-induct t
           :in-theory '(fn-sbud-oc-store fn-oiis-prepare-identity fn-psrv-prepare-identity
                        (:e equal) fn-sjh-ccar-ocfg-prepare-identity-store)
           :use ((:instance fn-pout-prepare-identity-answers-the-store-change)))))

(defthm fn-sjh-identity-prepared-staging
  (let* ((s (fn-own-store (fn-ocfg-owner oc)))
         (row (fn-oii-identity-row w (fn-sn-keyring s) (fn-sn-keyring-generation s) h))
         (r (fn-pout-prepare-identity oc w h))
         (o2 (fn-ocfg-owner (mv-nth 1 r))))
    (implies (equal (mv-nth 0 r) :prepared)
             (and (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                  (equal (mv-nth 1 r) (fn-ccar-ocfg-prepare-identity oc row))
                  (equal (fn-sn-files (fn-own-store o2)) (fn-spc-stage-record (fn-sn-files s) row))
                  (equal (fn-sf-phase (fn-sn-files (fn-own-store o2))) :record-staged)
                  (equal (fn-own-view o2) (fn-own-view (fn-ocfg-owner oc)))
                  (equal (fn-own-conns o2) (fn-own-conns (fn-ocfg-owner oc))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory '(fn-own-store-idlep fn-snt-idle-phasep member-equal (:e equal)
                        fn-sjh-ccar-ocfg-prepare-identity-store)
           :use ((:instance fn-sjh-identity-prepared-next)
                 (:instance fn-sjh-ccar-sn-prepare-identity-changed
                            (s (fn-own-store (fn-ocfg-owner oc)))
                            (row (fn-oii-identity-row w (fn-sn-keyring (fn-own-store (fn-ocfg-owner oc)))
                                                      (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner oc))) h)))
                 (:instance fn-sjh-ccar-ocfg-prepare-identity-owner
                            (row (fn-oii-identity-row w (fn-sn-keyring (fn-own-store (fn-ocfg-owner oc)))
                                                      (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner oc))) h)))))))

; Staging a row into the reserved store, generically: S survives the arena
; (which only grew), and LINK is the staged row's.
(defthm fn-sjh-files-okp-of-stage
  (let ((files2 (fn-spc-stage-record files row)))
    (implies (and (fn-sjh-files-okp files nil fn-arena fn-cat)
                  (equal (fn-sf-phase files) :reserved)
                  (equal (fn-sf-phase files2) :record-staged)
                  (fn-rows-composites-okp (fn-sf-records files) arena2)
                  (fn-rows-handles-inp (fn-sf-records files) arena2)
                  (fn-row-composite-okp row arena2)
                  (fn-rows-handles-inp (list row) arena2)
                  (fn-scj-rows-clearp (list row))
                  (if pending
                      (and (fn-pc-p pending)
                           (equal (fn-scj-load-h row) (fn-pc-held pending))
                           (equal (fn-pc-token pending)
                                  (cons (nfix (cdr (fn-sf-record-pair row))) (fn-pc-expected pending)))
                           (equal (fn-pc-expected pending) (len fn-cat)))
                    (not (fn-scj-load-h row))))
             (fn-sjh-files-okp files2 pending arena2 fn-cat)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sjh-stage-record-fields))
           :in-theory (e/d (fn-sjh-files-okp fn-sjh-files-linkp fn-sjh-inflight fn-sf-record-phasep)
                           (fn-spc-stage-record fn-row-composite-okp fn-rows-composites-okp
                            fn-rows-handles-inp fn-scj-rows-clearp fn-scj-load-h fn-pc-p
                            fn-sf-record-pair)))))

(defthm fn-sjh-composite-record-txid
  (implies (fn-record-p (fn-replay-composite-record w))
           (equal (fn-record-txid (fn-replay-composite-record w)) (fn-stxa-txid w)))
  :hints (("Goal" :in-theory (enable fn-replay-composite-record fn-stxa-bindsp))))

(defthm fn-sjh-hstxa-is-not-held
  (implies (fn-hstxa-p x) (not (fn-held-p x)))
  :hints (("Goal" :use ((:instance fn-snt-an-article-record-is-no-other-store-event (record x)))
           :in-theory (disable fn-hstxa-p fn-held-p))))

(defthm fn-sjh-hstxa-make-facts
  (implies (and (fn-stxa-p w) (fn-held-p held))
           (let ((row (fn-hstxa-make w held)))
             (and (fn-hstxa-p row)
                  (equal (fn-hstxa-stxa row) w)
                  (equal (fn-hstxa-held row) held)
                  (fn-sca-composite-shapep row)
                  (not (fn-cat-rowp row)))))
  :hints (("Goal" :in-theory (e/d (fn-hstxa-p fn-hstxa-make fn-hstxa-stxa fn-hstxa-held
                                   fn-sca-composite-shapep fn-cat-rowp fn-held-shapep)
                                  (fn-held-p fn-stxa-p))
           :use ((:instance fn-held-p-implies-cat-rowp (x held))))))

(defthm fn-sjh-hstxa-event-txid
  (implies (fn-hstxa-p x)
           (equal (fn-store-event-txid x) (fn-stxa-txid (fn-hstxa-stxa x))))
  :hints (("Goal" :in-theory (enable fn-store-event-txid fn-hstxa-p fn-store-retention-event-p
                                     fn-stxe-p fn-stxk-p fn-stxe-shapep fn-stxk-shapep))))

(defthm fn-sjh-composite-row-facts
  (implies (and (fn-stxa-p w)
                (fn-record-p (fn-replay-composite-record w))
                (natp generation) (fn-arena-p fn-arena))
           (let* ((a (fn-replay-composite-record w))
                  (held (fn-intern-row-at a keyring generation (fn-arena-count fn-arena)))
                  (row (fn-hstxa-make w held))
                  (a2 (fn-arena-seal-list (fn-record-payload a) fn-arena)))
             (and (fn-row-composite-okp row a2)
                  (fn-rows-handles-inp (list row) a2)
                  (fn-scj-rows-clearp (list row))
                  (equal (fn-scj-load-h row) held)
                  (equal (nfix (cdr (fn-sf-record-pair row))) (nfix (fn-record-txid a))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-row-composite-okp fn-rows-handles-inp fn-scj-rows-clearp fn-scj-load-h
                         fn-sf-record-pair fn-sjh-hstxa-event-txid fn-sjh-hstxa-is-not-held
                         fn-sjh-hstxa-make-facts fn-sjh-composite-record-txid fn-row-wire-of
                         car-cons cdr-cons (:e fn-scj-rows-clearp) (:e fn-rows-handles-inp)
                         fn-arena-count-is-len natp (:type-prescription len))
                       (theory 'minimal-theory))
           :use ((:instance fn-sjh-sealed-row-facts (w (fn-replay-composite-record w)))
                 (:instance fn-sjh-intern-row-held-p (w (fn-replay-composite-record w))
                            (h (fn-arena-count fn-arena)))
                 (:instance fn-sjh-intern-row-fields (w (fn-replay-composite-record w))
                            (h (fn-arena-count fn-arena)))))))

(defthm fn-sjh-prepare-sealed-facts
  (implies (and (fn-held-p held)
                (natp (fn-record-payload held))
                (equal (fn-record-payload held) (1- (fn-arena-count fn-arena)))
                (natp (fn-record-txid w)))
           (let ((pc (fn-cat-prepare-sealed w held plan reservation nil fn-arena fn-cat)))
             (and (fn-pc-p pc)
                  (equal (fn-pc-held pc) held)
                  (equal (fn-pc-expected pc) (len fn-cat))
                  (equal (fn-pc-token pc) (cons (fn-record-txid w) (fn-pc-expected pc))))))
  :hints (("Goal" :in-theory (e/d (fn-cat-prepare-sealed fn-pc-internals fn-pc-p fn-pc-tokenp fn-pc-anyp
                                   fn-cat-count-is-len)
                                  (fn-held-p)))))

(defthm fn-sjh-stxa-is-not-record
  (implies (fn-stxa-p w) (not (fn-record-p w)))
  :hints (("Goal" :in-theory (enable fn-stxa-p fn-record-p fn-stxa-shapep fn-record-shapep))))

(defthm fn-sjh-identity-row-of-composite
  (implies (and (fn-stxa-p w) (fn-record-p (fn-replay-composite-record w)))
           (equal (fn-oii-identity-row w keyring generation h)
                  (fn-hstxa-make w (fn-intern-row-at (fn-replay-composite-record w) keyring generation h))))
  :hints (("Goal" :in-theory (e/d (fn-oii-identity-row) (fn-intern-row-at fn-hstxa-make fn-record-p
                                                        fn-replay-composite-record fn-stxa-p)))))

(defthm fn-sjh-record-txid-natp
  (implies (fn-record-p w) (natp (fn-record-txid w)))
  :hints (("Goal" :in-theory (enable fn-record-p fn-record-shapep fn-record-uint64p fn-record-internals)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-sjh-pc-p-is-non-nil
  (implies (fn-pc-p pc) pc)
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-pc-p))))

(defthm fn-sjh-files-okp-of-identity-stage
  (let* ((a (fn-replay-composite-record w))
         (held (fn-intern-row-at a keyring generation (fn-arena-count fn-arena)))
         (row (fn-hstxa-make w held))
         (arena2 (fn-arena-seal-list (fn-record-payload a) fn-arena))
         (pc (fn-cat-prepare-sealed a held plan reservation nil arena2 fn-cat)))
    (implies (and (fn-sjh-files-okp files nil fn-arena fn-cat)
                  (fn-arena-p fn-arena)
                  (fn-stxa-p w) (fn-record-p a) (natp generation)
                  (equal (fn-sf-phase files) :reserved)
                  (equal (fn-sf-phase (fn-spc-stage-record files row)) :record-staged))
             (fn-sjh-files-okp (fn-spc-stage-record files row) pc arena2 fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-files-okp fn-sjh-record-txid-natp natp nfix
                                        fn-arena-seal-count fn-sjh-intern-row-fields
                                        fn-sjh-intern-row-held-p (:type-prescription fn-arena-count)
                                        fn-arena-count-is-len (:type-prescription len)
                                        fn-sjh-pc-p-is-non-nil (:executable-counterpart fn-pc-p))
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-files-okp-of-stage
                            (row (fn-hstxa-make w (fn-intern-row-at (fn-replay-composite-record w) keyring generation (fn-arena-count fn-arena))))
                            (arena2 (fn-arena-seal-list (fn-record-payload (fn-replay-composite-record w)) fn-arena))
                            (pending (fn-cat-prepare-sealed (fn-replay-composite-record w)
                                                            (fn-intern-row-at (fn-replay-composite-record w) keyring generation (fn-arena-count fn-arena))
                                                            plan reservation nil
                                                            (fn-arena-seal-list (fn-record-payload (fn-replay-composite-record w)) fn-arena)
                                                            fn-cat)))
                 (:instance fn-sjh-rows-survive-seal (rows (fn-sf-records files))
                            (xs (fn-record-payload (fn-replay-composite-record w))))
                 (:instance fn-sjh-composite-row-facts)
                 (:instance fn-sjh-prepare-sealed-facts
                            (w (fn-replay-composite-record w))
                            (held (fn-intern-row-at (fn-replay-composite-record w) keyring generation (fn-arena-count fn-arena)))
                            (fn-arena (fn-arena-seal-list (fn-record-payload (fn-replay-composite-record w)) fn-arena)))))))

; KEYSTONE (the signed composite's prepare): host/owner-host.lisp
; fn-owner-prepare-identity over fn-pout-prepare-identity at the arena's
; count, the seal of the composite's article payload, and the catalog's
; prepare of the composite's held row: fn-sjh-okp with that pending row.
(defthm fn-sjh-okp-at-owner-prepare-identity-sealed
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (h (fn-arena-count fn-arena))
         (r (fn-pout-prepare-identity oc w h))
         (o2 (fn-ocfg-owner (mv-nth 1 r)))
         (a (fn-replay-composite-record w))
         (held (fn-intern-row-at a (fn-sn-keyring s) (fn-sn-keyring-generation s) h))
         (arena2 (fn-arena-seal-list (fn-record-payload a) fn-arena))
         (pc (fn-cat-prepare-sealed a held plan reservation nil arena2 fn-cat)))
    (implies (and (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  (fn-arena-p fn-arena)
                  (fn-stxa-p w) (fn-record-p a)
                  (natp (fn-sn-keyring-generation s))
                  (equal (mv-nth 0 r) :prepared))
             (fn-sjh-okp o2 pc arena2 fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-okp fn-sjh-versionsp-is-versions-okp fn-sjh-invp-arena-free
                                        fn-sjh-historyp-of-same-view-and-records
                                        fn-sjh-indexedp-of-same-view fn-sjh-identity-row-of-composite
                                        fn-sjh-ocl-facts-for-prepare)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-identity-prepared-staging (h (fn-arena-count fn-arena)))
                 (:instance fn-sjh-files-okp-at-reserved-has-no-pending
                            (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                 (:instance fn-sjh-files-okp-of-identity-stage
                            (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                            (keyring (fn-sn-keyring (fn-own-store (fn-ocfg-owner oc))))
                            (generation (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner oc)))))
                 (:instance fn-sjh-stage-record-fields
                            (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                            (row (fn-hstxa-make w (fn-intern-row-at (fn-replay-composite-record w)
                                                                    (fn-sn-keyring (fn-own-store (fn-ocfg-owner oc)))
                                                                    (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner oc)))
                                                                    (fn-arena-count fn-arena)))))
                 (:instance fn-scjs-ccar-ocfg-prepare-identity-keeps-invp
                            (e (fn-hstxa-make w (fn-intern-row-at (fn-replay-composite-record w)
                                                                  (fn-sn-keyring (fn-own-store (fn-ocfg-owner oc)))
                                                                  (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner oc)))
                                                                  (fn-arena-count fn-arena)))))
                 (:instance fn-scjs-ccar-ocfg-prepare-identity-keeps-versions
                            (e (fn-hstxa-make w (fn-intern-row-at (fn-replay-composite-record w)
                                                                  (fn-sn-keyring (fn-own-store (fn-ocfg-owner oc)))
                                                                  (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner oc)))
                                                                  (fn-arena-count fn-arena)))))))))

(defthm fn-sjh-stxk-row-facts
  (implies (fn-stxk-p w)
           (and (equal (fn-oii-identity-row w keyring generation h) w)
                (fn-row-composite-okp w fn-arena)
                (fn-rows-handles-inp (list w) fn-arena)
                (fn-scj-rows-clearp (list w))
                (not (fn-scj-load-h w))))
  :hints (("Goal" :in-theory (enable fn-oii-identity-row fn-row-composite-okp fn-rows-handles-inp
                                     fn-scj-rows-clearp fn-scj-load-h fn-sca-composite-shapep
                                     fn-stxk-p fn-stxk-shapep fn-record-p fn-record-shapep fn-stxa-p
                                     fn-stxa-shapep fn-held-p fn-held-shapep fn-hstxa-p fn-cat-rowp
                                     fn-wire-event-p fn-stxk-sequence fn-record-uint32p))))

; KEYSTONE (a keyring snapshot's prepare): it loads no catalog row, the host
; keeps no pending row: fn-sjh-okp with none.
(defthm fn-sjh-okp-at-owner-prepare-identity-unsealed
  (let* ((o (fn-ocfg-owner oc))
         (h (fn-arena-count fn-arena))
         (r (fn-pout-prepare-identity oc w h))
         (o2 (fn-ocfg-owner (mv-nth 1 r))))
    (implies (and (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  (fn-stxk-p w)
                  (equal (mv-nth 0 r) :prepared))
             (fn-sjh-okp o2 nil fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-okp fn-sjh-versionsp-is-versions-okp
                                        fn-sjh-historyp-of-same-view-and-records
                                        fn-sjh-indexedp-of-same-view fn-sjh-ocl-facts-for-prepare)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-identity-prepared-staging (h (fn-arena-count fn-arena)))
                 (:instance fn-sjh-stxk-row-facts
                            (keyring (fn-sn-keyring (fn-own-store (fn-ocfg-owner oc))))
                            (generation (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner oc))))
                            (h (fn-arena-count fn-arena)))
                 (:instance fn-sjh-files-okp-at-reserved-has-no-pending
                            (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                 (:instance fn-sjh-files-okp-of-stage
                            (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                            (row w) (arena2 fn-arena) (pending nil))
                 (:instance fn-sjh-stage-record-fields
                            (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) (row w))
                 (:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-scjs-ccar-ocfg-prepare-identity-keeps-invp (e w))
                 (:instance fn-scjs-ccar-ocfg-prepare-identity-keeps-versions (e w))))))
