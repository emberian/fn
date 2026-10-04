; fn: the served POST keeps the stored-bytes condition (records-flip,
; flip-L1-3, 2026-09-27).
;
; books/store-budget-stored.lisp proves that the history budget's octets are
; the stored octets under `fn-sbud-rows-extents-okp' (every held row's facts
; octets are its handle's extent in the arena), and that the open's intern
; establishes it.  This book carries it forward: the relation is kept IN the
; store, over the retained rows and the staged candidate
; (`fn-sbud-store-extents-okp'), and every transition of the served POST keeps
; it, so the budget never has to re-read the arena to know what it counts.
;
;   the stage   host/owner-host.lisp `fn-owner-prepare' calls
;               `fn-pcar-sbud-prepare' (current view P9) over the row
;               `fn-intern-row-at' makes at the arena's count, and seals the
;               record's payload exactly when the store changed.  The host's
;               call is `fn-sbud-prepare' with no hypothesis
;               (books/owner-prepare-carried.lisp
;               `fn-pcar-sbud-prepare-is-sbud-prepare'), so the keystone is
;               stated over the reference
;               (`fn-sbud-prepare-keeps-the-stored-octets'); this book does not
;               include the carried book, which the flip's host wiring is
;               still restating.  The standalone store's entry is
;               `fn-store-prepare-interned'
;               (`fn-store-prepare-interned-keeps-the-stored-octets').
;   the publish `fn-sn-io' (host `fn-owner-io' / `fn-store-sn-io'): the
;               directory barrier appends the candidate to the history
;               (`fn-sn-io-keeps-the-stored-octets').
;   the finish  `fn-sn-finish' (`fn-sn-finish-keeps-the-stored-octets').
;
; Neither the publish nor the finish touches the arena.  A reopen clears the
; arena and re-interns the journal, which re-establishes the relation from
; nothing (`fn-intern-events-extents-okp').  The relation is proof-level: no
; host line evaluates it.
(in-package "ACL2")
(include-book "store-budget-stored")
(include-book "store-node-traces")
(include-book "owner-store-budget")

; The arena is read through its interface (a seal keeps every sealed handle),
; the list view opened only in the one-row lemma below.
(local (in-theory (disable fn-arena-payload-is-nth fn-arena-count-is-len
                           fn-arena-seal-list-is-append fn-arena-p-is-payload-listp
                           fn-arena-get-is-nth fn-arena-payload-len-is-len-nth)))

; -----------------------------------------------------------------------------
; The relation carried in the store.

(defun fn-sbud-files-extents-okp (files fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (fn-sbud-rows-extents-okp (fn-sf-records files) fn-arena)
       (fn-sbud-rows-extents-okp (list (fn-sf-record-candidate files)) fn-arena)))

(defun fn-sbud-store-extents-okp (s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-sbud-files-extents-okp (fn-sn-files s) fn-arena))

; Under it the budget's committed octets are the stored octets
; (fn-sbud-bytes-used-is-the-stored-octets: its hypothesis is the first
; conjunct).

(local (defthm fn-sbsp-rows-extents-okp-of-append
  (equal (fn-sbud-rows-extents-okp (append a b) fn-arena)
         (and (fn-sbud-rows-extents-okp a fn-arena)
              (fn-sbud-rows-extents-okp b fn-arena)))
  :hints (("Goal" :in-theory (disable fn-sbud-row-extent-okp)))))

(local (defthm fn-sbsp-rows-extents-okp-of-nil-list
  (fn-sbud-rows-extents-okp (list nil) fn-arena)))

(local (in-theory (disable fn-sbud-rows-extents-okp)))

; -----------------------------------------------------------------------------
; The publish: every file-kernel step keeps the relation (the history grows
; only by the candidate, at the directory barrier).

(local (defthm fn-sbsp-file-step-keeps
  (implies (fn-sbud-files-extents-okp files fn-arena)
           (fn-sbud-files-extents-okp (fn-sn-file-step files operation result) fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-sn-file-step fn-sf-start-frontier
                                   fn-sf-frontier-file-result fn-sf-frontier-replace-result
                                   fn-sf-frontier-dir-result fn-sf-record-file-result
                                   fn-sf-record-link-result fn-sf-record-dir-result
                                   fn-sf-recovery-barrier)
                                  (fn-sf-statep))))))

(local (defthm fn-sbsp-files-of-io
  (equal (fn-sn-files (fn-sn-io s operation result))
         (fn-sn-file-step (fn-sn-files s) operation result))
  :hints (("Goal" :in-theory '(fn-sn-io fn-sn-files-of-fn-sn-update)))))

(defthm fn-sn-io-keeps-the-stored-octets
  (implies (fn-sbud-store-extents-okp s fn-arena)
           (fn-sbud-store-extents-okp (fn-sn-io s operation result) fn-arena))
  :hints (("Goal" :in-theory (disable fn-sn-io fn-sn-file-step fn-sbud-files-extents-okp))))

; -----------------------------------------------------------------------------
; The finish: the history is kept (fn-snt-finish-keeps-records) and the
; candidate is the one before or none.

(local (defthm fn-sbsp-files-of-with-topic
  (equal (fn-sn-files (fn-sn-with-topic s topic)) (fn-sn-files s))
  :hints (("Goal" :in-theory '(fn-sn-with-topic fn-sn-files-of-fn-sn-make-v6)))))
(local (defthm fn-sbsp-files-of-with-consumer
  (equal (fn-sn-files (fn-sn-with-consumer s consumer)) (fn-sn-files s))
  :hints (("Goal" :in-theory '(fn-sn-with-consumer fn-sn-files-of-fn-sn-make-v6)))))
(local (defthm fn-sbsp-files-of-advance-identity-next
  (equal (fn-sn-files (fn-sn-advance-identity-next s)) (fn-sn-files s))
  :hints (("Goal" :in-theory '(fn-sn-advance-identity-next fn-sn-files-of-fn-sn-make-v6)))))
(local (defthm fn-sbsp-files-of-update-indexed
  (equal (fn-sn-files (fn-sn-update-indexed s files node index)) files)
  :hints (("Goal" :in-theory '(fn-sn-update-indexed fn-sn-files-of-fn-sn-make-v6)))))
(local (defthm fn-sbsp-files-of-update-accepted
  (equal (fn-sn-files (fn-sn-update-accepted s files node index msgid verdict)) files)
  :hints (("Goal" :in-theory '(fn-sn-update-accepted fn-sn-files-of-fn-sn-make-v6)))))
(local (defthm fn-sbsp-files-of-finish-identity
  (equal (fn-sn-files (fn-sn-finish-identity s files record node)) files)
  :hints (("Goal" :in-theory '(fn-sn-finish-identity fn-sn-files-of-fn-sn-make-v6)))))

(local (defthm fn-sbsp-candidate-of-completion
  (implies (fn-sbud-rows-extents-okp (list (fn-sf-record-candidate files)) fn-arena)
           (fn-sbud-rows-extents-okp
            (list (fn-sf-record-candidate
                   (fn-sf-emit-success (fn-sf-core-completion files sequence txid)
                                       sequence2 txid2)))
            fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-sf-emit-success fn-sf-core-completion)
                                  (fn-sf-statep))))))

(local (defthm fn-sbsp-finish-candidate
  (implies (fn-sbud-rows-extents-okp (list (fn-sf-record-candidate (fn-sn-files s))) fn-arena)
           (fn-sbud-rows-extents-okp
            (list (fn-sf-record-candidate (fn-sn-files (fn-sn-finish s))))
            fn-arena))
  :hints (("Goal" :in-theory '(fn-sn-finish fn-sbsp-files-of-with-topic
                               fn-sbsp-files-of-with-consumer
                               fn-sbsp-files-of-advance-identity-next
                               fn-sbsp-files-of-update-indexed
                               fn-sbsp-files-of-update-accepted
                               fn-sbsp-files-of-finish-identity
                               fn-sbsp-candidate-of-completion)))))

(defthm fn-sn-finish-keeps-the-stored-octets
  (implies (fn-sbud-store-extents-okp s fn-arena)
           (fn-sbud-store-extents-okp (fn-sn-finish s) fn-arena))
  :hints (("Goal" :use (fn-snt-finish-keeps-records fn-sbsp-finish-candidate)
           :in-theory '(fn-sbud-store-extents-okp fn-sbud-files-extents-okp))))

; -----------------------------------------------------------------------------
; The stage.  The staged row is the one the intern makes at the arena's
; count; the seal that follows puts the record's bytes under it.

; (Any W: the facts' octets and the sealed extent are both the length of
; W's payload position, so no wire-record hypothesis is needed.)
(local (defthm fn-sbsp-nth-of-append-at-len
  (equal (nth (len a) (append a (list x))) x)))
(local (defthm fn-sbsp-row-at-count-extent
  (implies (fn-arena-p fn-arena)
           (fn-sbud-rows-extents-okp
            (list (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
            (fn-arena-seal-list (fn-record-payload w) fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-sbud-rows-extents-okp fn-sbud-row-extent-okp
                                   fn-row-handle-inp fn-intern-row-at fn-held-facts-of
                                   fn-arena-count-is-len fn-arena-payload-len-is-len-nth
                                   fn-arena-seal-list-is-append)
                                  (fn-held-p fn-held-context-of fn-hf-split-index
                                   fn-hf-body-lines-of fn-arena-payload-is-nth
                                   fn-arena-get-is-nth fn-arena-p-is-payload-listp))))))

(defthm fn-store-prepare-interned-keeps-the-stored-octets
  (implies (and (fn-arena-p fn-arena) (fn-sbud-store-extents-okp s fn-arena))
           (fn-sbud-store-extents-okp (mv-nth 0 (fn-store-prepare-interned s w fn-arena))
                                      (mv-nth 1 (fn-store-prepare-interned s w fn-arena))))
  :hints (("Goal" :use ((:instance fn-sn-prepare-installs-bound-candidate
                         (record (fn-intern-row-at w (fn-sn-keyring s)
                                                   (fn-sn-keyring-generation s)
                                                   (fn-arena-count fn-arena))))
                        (:instance fn-snt-prepare-keeps-records
                         (record (fn-intern-row-at w (fn-sn-keyring s)
                                                   (fn-sn-keyring-generation s)
                                                   (fn-arena-count fn-arena)))))
           :in-theory (e/d (fn-store-prepare-interned fn-sbud-store-extents-okp
                            fn-sbud-files-extents-okp)
                           (fn-sn-prepare fn-intern-row-at fn-record-p fn-arena-seal-list
                            fn-sn-prepare-installs-bound-candidate
                            fn-snt-prepare-keeps-records)))))

; The owner's prepare stages the same way.
(local (defthm fn-sbsp-spc-prepare-stages
  (implies (not (equal (fn-spc-prepare s row) s))
           (and (equal (fn-sf-records (fn-sn-files (fn-spc-prepare s row)))
                       (fn-sf-records (fn-sn-files s)))
                (equal (fn-sf-record-candidate (fn-sn-files (fn-spc-prepare s row)))
                       row)))
  :hints (("Goal" :in-theory (e/d (fn-spc-prepare fn-spc-stage-record)
                                  (fn-sn-statep fn-sn-record-bindsp fn-sn-prepare-node
                                   fn-sf-candidatep fn-cpe-projection-step))))))

(local (defthm fn-sbsp-own-store-of-refresh
  (equal (fn-own-store (fn-own-refresh o)) (fn-own-store o))
  :hints (("Goal" :in-theory (enable fn-own-refresh)))))

(local (defthm fn-sbsp-store-of-sbud-prepare
  (equal (fn-sbud-oc-store (fn-sbud-prepare oc row budget))
         (if (fn-sbud-admitp budget (fn-sbud-used (fn-sbud-oc-store oc)))
             (fn-spc-prepare (fn-sbud-oc-store oc) row)
           (fn-sbud-oc-store oc)))
  :hints (("Goal" :in-theory (e/d (fn-sbud-prepare fn-opc-prepare
                                   fn-opc-owner-prepare fn-sbud-oc-store
                                   fn-ocfg-with-owner)
                                  (fn-own-refresh fn-spc-prepare fn-sbud-admitp
                                   fn-sbud-used))))))

; KEYSTONE (the served POST keeps the stored-bytes condition).  The host line:
; host/owner-host.lisp `fn-owner-prepare' calls `fn-pcar-sbud-prepare', which
; is this `fn-sbud-prepare' (`fn-pcar-sbud-prepare-is-sbud-prepare', no
; hypothesis), on the row `fn-intern-row-at' makes of the POST's wire record
; at the arena's count (under the Store's keyring and generation: any KEYRING
; and GENERATION here), and seals the record's payload when the Store
; changed.  From a store that holds the relation over the live arena, the
; store after holds it over the arena after.
(defthm fn-sbud-prepare-keeps-the-stored-octets
  (implies (and (fn-arena-p fn-arena)
                (fn-sbud-store-extents-okp (fn-sbud-oc-store oc) fn-arena))
           (let* ((row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
                  (next (fn-sbud-prepare oc row budget))
                  (after (if (equal (fn-sbud-oc-store next) (fn-sbud-oc-store oc))
                             fn-arena
                           (fn-arena-seal-list (fn-record-payload w) fn-arena))))
             (fn-sbud-store-extents-okp (fn-sbud-oc-store next) after)))
  :hints (("Goal" :use ((:instance fn-sbsp-spc-prepare-stages
                         (s (fn-sbud-oc-store oc))
                         (row (fn-intern-row-at w keyring generation
                                                (fn-arena-count fn-arena)))))
           :in-theory (e/d (fn-sbud-store-extents-okp fn-sbud-files-extents-okp)
                           (fn-sbud-prepare fn-intern-row-at fn-record-p
                            fn-arena-seal-list fn-sbud-oc-store fn-spc-prepare
                            fn-sbud-admitp fn-sbud-used
                            fn-sbsp-spc-prepare-stages)))))

(in-theory (disable fn-sbud-store-extents-okp fn-sbud-files-extents-okp))
