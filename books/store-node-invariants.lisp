; Correspondence for actual live node/file completion, without a trusted reply.
(in-package "ACL2")
(include-book "store-node-invariants-base")

; Split 2026-09-27 (the 10 s budget): everything before the carried index and
; the prefix recoverability section is in books/store-node-invariants-base;
; this book carries the index and exports the vocabulary.  The local theory
; below is the base book's at the point this section began.

; The codecs cluster withdraws the record and codec definitions at export
; (2026-09-19); the proofs here open fn-record-p and the record accessors.
(local (in-theory (enable fn-record-record-vocabulary fn-record-shape-vocabulary)))

; The core definitions these correspondence proofs open (the core exports
; keystones only, docs/proof-style.md s2); local, named once.
(local (deftheory fn-snx-core-definitions
         (union-theories (union-theories '(fn-articlep fn-pendingp fn-statep fn-initial-state fn-install-pending
            fn-clear-pending fn-accept-prepare fn-accept-complete fn-accept-recover
            fn-pending-matchesp
            fn-retain-obligationp fn-retain-releasep fn-retain-statep
            fn-retain-initial-state fn-retain-admissiblep fn-retain-admit
            fn-retain-release
            fn-node-stagep fn-node-bindingp fn-node-statep fn-node-initial-state
            fn-node-pending-matchesp fn-node-prepare fn-node-complete fn-node-recover
            fn-replay-okp fn-replay-advance-okp fn-replay-advance-txid) (theory 'fn-acceptance-invariants-vocabulary)) (theory 'fn-node-invariants-vocabulary))))

; The composed definitions and the kernel steps these proofs open are
; enabled locally (docs/proof-style.md s2); the records stay opaque.
(local (in-theory (e/d (fn-sn-statep fn-sn-initial fn-sn-pending-record
                        fn-sn-record-bindsp fn-sn-prepare-node fn-sn-prepare
                        fn-sn-completion-record fn-sn-completion-enabledp
                        fn-sn-finish fn-sn-file-step fn-sn-io fn-sn-crash
                        fn-sn-recover fn-sn-fence-node fn-sn-resolve-node
                        fn-sf-initial-state fn-sf-history-recoverablep
                        fn-sf-replay-node fn-sf-refuse-reservation
                        fn-sf-prepublish-abort fn-sf-abort-completion
                        fn-sf-lose-success fn-sf-recover fn-sf-crash-imagep
                        fn-replay-apply-record fn-replay-okp fn-replay-faultp
                        fn-replay-advance-okp fn-node-pending-matchesp
                        fn-store-files-invariants-vocabulary)
                       (fn-node-statep fn-sf-statep fn-record-p
                        fn-node-prepare fn-node-complete fn-node-recover
                        fn-replay-advance-txid fn-replay fn-replay-loop
                        fn-retain-statep fn-node-initial-state fn-sf-prepare-record
                        fn-sf-start-frontier fn-sf-frontier-file-result
                        fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                        fn-sf-record-file-result fn-sf-record-link-result
                        fn-sf-record-dir-result fn-sf-recovery-barrier
                        fn-sf-core-completion fn-sf-emit-success
                        fn-sf-crash
                        ;; Backchained on every true-listp and stringp goal and
                        ;; never useful here (0.2 M useless frames each).
                        fn-cp-idp-true-listp
                        fn-prov-structured-is-not-a-string
                        fn-sn-verdict-listp member-equal))))


(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable fn-node-statep fn-sf-statep fn-record-p
                           fn-node-prepare fn-node-complete fn-node-recover
                           fn-replay-advance-txid fn-replay fn-replay-loop
                           fn-sf-replay-node fn-sn-prepare-node
                           fn-retain-statep fn-node-initial-state)))

(local (in-theory (disable  fn-state-next-txid
                             )))

(local (in-theory (enable fn-sn-indexedp fn-sn-set-keyring fn-sn-accepted-delta
                          fn-sn-statement-lookup fn-sn-equivocatorp)))

; Also local in the base book (its use here is in the non-row lemmas below).
(local
 (defthm fn-sn-an-article-record-is-no-other-store-event
   (implies (fn-held-p record)
            (and (not (fn-store-retention-event-p record))
                 (not (fn-stxe-p record))
                 (not (fn-stxk-p record))
                 (not (fn-hstxa-p record))
                 (not (fn-th-topic-eventp record))
                 (not (fn-cpe-eventp record))))
   :hints (("Goal"
            :in-theory (e/d ((:d fn-held-p) (:d fn-held-shapep)
                             (:d fn-record-uint64p)
                             (:d fn-store-retention-event-p)
                             (:d fn-stxe-p) (:d fn-stxe-shapep)
                             (:d fn-stxk-p) (:d fn-stxk-shapep)
                             (:d fn-hstxa-p)
                             (:d fn-cpe-eventp)
                             (:d fn-th-topic-eventp)
                             (:d fn-th-local-admin-eventp))
                            ((:d fn-stxe-bounded-octetsp)
                             (:d fn-record-uint32p) (:d fn-record-msgidp)
                             (:d fn-record-payloadp)
                             (:d fn-record-groups-validp)
                             (:d fn-record-metadata-bytes-p)
                             (:d fn-record-stampp)
                             (:d fn-hf-p) (:d fn-hc-p)
                             (:d fn-held-numbersp) (:d fn-held-withdrawnp)))))))

; -----------------------------------------------------------------------------
; THE CARRIED INDEX (records-flip, 2026-09-27).  fn-sn-indexedp
; (books/store-node.lisp): the index is the fold of the rows' context deltas
; over fn-sn-indexed-rows -- the history less the row the directory barrier
; appended and the finish has not yet indexed (:completing), and no row after
; a crash (:replaying, :fault) -- and in :completing the completion pair names
; the last row.  Every transition below keeps it; recovery and the keyring
; installation recompute it over the rows.  No byte is read anywhere: a
; row's delta is its context's, decided at the intern.

(local (in-theory (enable fn-sn-indexed-rows)))

(local (defthm fn-sni-records-true-listp
  (implies (fn-sf-statep files) (true-listp (fn-sf-records files)))
  :hints (("Goal" :in-theory (enable fn-sf-statep)))))

(local (defthm fn-sni-car-last-of-append-one
  (implies (true-listp xs)
           (equal (car (last (append xs (list x)))) x))))

(local (defthm fn-sni-consp-append-one
  (consp (append xs (list x)))))

; The files after each transition: which rows are indexed, and the completion
; conjunct.  Exported: the books that add transitions (store-node-resolution,
; store-sweep) reach the invariant through these.
(defthm fn-sn-indexed-rows-of-initial-state
  (equal (fn-sn-indexed-rows-of (fn-sf-initial-state)) nil)
  :hints (("Goal" :in-theory (enable fn-sf-initial-state fn-sn-indexed-rows-of))))

(defthm fn-sn-completion-is-last-of-initial-state
  (fn-sn-completion-is-last-p (fn-sf-initial-state))
  :hints (("Goal" :in-theory (enable fn-sf-initial-state fn-sn-completion-is-last-p))))

(defthm fn-sn-indexed-rows-of-prepare-record
  (implies (fn-sf-statep files)
           (equal (fn-sn-indexed-rows-of (fn-sf-prepare-record files record groups capacity))
                  (fn-sn-indexed-rows-of files)))
  :hints (("Goal" :in-theory (e/d (fn-sf-prepare-record fn-sn-indexed-rows-of)
                                  (fn-sf-statep fn-sf-candidatep fn-sf-history-recoverablep)))))

(defthm fn-sn-completion-is-last-of-prepare-record
  (implies (and (fn-sf-statep files) (fn-sn-completion-is-last-p files))
           (fn-sn-completion-is-last-p (fn-sf-prepare-record files record groups capacity)))
  :hints (("Goal" :in-theory (e/d (fn-sf-prepare-record fn-sn-completion-is-last-p)
                                  (fn-sf-statep fn-sf-candidatep fn-sf-history-recoverablep)))))

(defthm fn-sn-indexed-rows-of-file-step
  (implies (fn-sf-statep files)
           (equal (fn-sn-indexed-rows-of (fn-sn-file-step files operation result))
                  (fn-sn-indexed-rows-of files)))
  :hints (("Goal" :in-theory (e/d (fn-sn-file-step fn-sn-indexed-rows-of
                                   fn-sf-start-frontier fn-sf-frontier-file-result
                                   fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                                   fn-sf-record-file-result fn-sf-record-link-result
                                   fn-sf-record-dir-result fn-sf-recovery-barrier)
                                  (fn-sf-statep)))))

(defthm fn-sn-completion-is-last-of-file-step
  (implies (and (fn-sf-statep files) (fn-sn-completion-is-last-p files))
           (fn-sn-completion-is-last-p (fn-sn-file-step files operation result)))
  :hints (("Goal" :in-theory (e/d (fn-sn-file-step fn-sn-completion-is-last-p
                                   fn-sf-start-frontier fn-sf-frontier-file-result
                                   fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                                   fn-sf-record-file-result fn-sf-record-link-result
                                   fn-sf-record-dir-result fn-sf-recovery-barrier)
                                  (fn-sf-statep)))))

(defthm fn-sn-indexed-rows-of-completion
  (implies (and (fn-sf-statep files) (equal (fn-sf-phase files) :completing)
                (equal (cons sequence txid) (fn-sf-completion files)))
           (let ((after (fn-sf-emit-success (fn-sf-core-completion files sequence txid)
                                            sequence txid)))
             (and (equal (fn-sf-phase after) :ready)
                  (equal (fn-sf-records after) (fn-sf-records files))
                  (equal (fn-sn-indexed-rows-of after) (fn-sf-records files))
                  (fn-sn-completion-is-last-p after))))
  :hints (("Goal" :in-theory (e/d (fn-sf-core-completion fn-sf-emit-success
                                   fn-sn-indexed-rows-of fn-sn-completion-is-last-p)
                                  (fn-sf-statep))
           :use ((:instance fn-sf-core-completion-preserves-state (s files))))))

(defthm fn-sn-indexed-rows-of-crash
  (implies (and (fn-sf-statep files) (fn-sf-crash-choicep frontier-choice record-choice))
           (and (equal (fn-sn-indexed-rows-of (fn-sf-crash files frontier-choice record-choice)) nil)
                (fn-sn-completion-is-last-p (fn-sf-crash files frontier-choice record-choice))))
  :hints (("Goal" :in-theory (e/d (fn-sf-crash fn-sn-indexed-rows-of fn-sn-completion-is-last-p)
                                  (fn-sf-statep fn-sf-frontier-new-visiblep
                                   fn-sf-record-present-visiblep)))))

(defthm fn-sn-indexed-rows-of-recover
  (implies (and (fn-sf-statep files) (equal (fn-sf-phase files) :replaying))
           (let ((after (fn-sf-recover files groups capacity)))
             (and (equal (fn-sf-records after) (fn-sf-records files))
                  (equal (fn-sn-indexed-rows-of after)
                         (if (equal (fn-sf-phase after) :fault) nil (fn-sf-records files)))
                  (fn-sn-completion-is-last-p after))))
  :hints (("Goal" :in-theory (e/d (fn-sf-recover fn-sn-indexed-rows-of fn-sn-completion-is-last-p)
                                  (fn-sf-statep fn-sf-history-recoverablep)))))

; A history's rows carry strictly increasing sequences, so the pair of its last
; row finds that row and no earlier one.
(local (defthm fn-sni-last-sequence-at-least
  (implies (and (fn-sf-record-listp records sequence lower frontier) (consp records))
           (and (natp (fn-store-event-sequence (car (last records))))
                (<= sequence (fn-store-event-sequence (car (last records))))))
  :hints (("Goal" :induct (fn-sf-record-listp records sequence lower frontier)
           :in-theory (enable fn-sf-record-listp)))))

; The same fact as a linear rule, so the induction step below sees that the
; last row's sequence is above the first's.
(local (defthm fn-sni-last-sequence-at-least-linear
  (implies (and (fn-sf-record-listp records sequence lower frontier) (consp records))
           (<= sequence (fn-store-event-sequence (car (last records)))))
  :rule-classes :linear
  :hints (("Goal" :use fn-sni-last-sequence-at-least))))

(local (defthm fn-sni-cdr-last-sequence-above
  (implies (and (fn-sf-record-listp records sequence lower frontier)
                (consp records) (consp (cdr records)))
           (< (fn-store-event-sequence (car records))
              (fn-store-event-sequence (car (last records)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :expand ((fn-sf-record-listp records sequence lower frontier))
           :use ((:instance fn-sni-last-sequence-at-least
                            (records (cdr records)) (sequence (1+ sequence))
                            (lower (1+ (fn-store-event-txid (car records))))))
           :in-theory (disable fn-sni-last-sequence-at-least)))))

(local (defthm fn-sni-find-record-of-last-pair
  (implies (and (fn-sf-record-listp records sequence lower frontier) (consp records))
           (equal (fn-sn-find-record (fn-sf-record-pair (car (last records))) records)
                  (car (last records))))
  :hints (("Goal" :induct (fn-sf-record-listp records sequence lower frontier)
           :in-theory (e/d (fn-sf-record-listp fn-sn-find-record fn-sf-record-pair)
                           (fn-store-event-p fn-sni-last-sequence-at-least))))))

(local (defthm fn-sni-completion-record-is-last
  (implies (and (fn-sn-statep s)
                (fn-sn-completion-is-last-p (fn-sn-files s))
                (equal (fn-sf-phase (fn-sn-files s)) :completing))
           (equal (fn-sn-completion-record s)
                  (car (last (fn-sf-records (fn-sn-files s))))))
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-record fn-sn-completion-is-last-p
                                   fn-sn-statep fn-sf-statep)
                                  (fn-sf-phase-shapep fn-sf-success-listp fn-node-statep
                                   fn-sn-find-record fn-sf-record-pair))
           :use ((:instance fn-sni-find-record-of-last-pair
                            (records (fn-sf-records (fn-sn-files s)))
                            (sequence 0) (lower 0)
                            (frontier (fn-sf-frontier (fn-sn-files s)))))))))

(local (defthm fn-sni-rows-split-at-last
  (implies (and (true-listp records) (consp records))
           (equal (append (fn-sn-all-but-last records) (list (car (last records))))
                  records))
  :hints (("Goal" :in-theory (enable fn-sn-all-but-last)))))

(local (defthm fn-sni-index-of-rows-at-last
  (implies (and (true-listp records) (consp records))
           (equal (fn-sn-index-of-rows records)
                  (fn-stx-index-add (fn-sn-index-of-rows (fn-sn-all-but-last records))
                                    (fn-sn-row-delta (car (last records))))))
  :hints (("Goal" :use ((:instance fn-sn-index-of-rows-of-append-one
                                   (rows (fn-sn-all-but-last records))
                                   (row (car (last records)))))
           :in-theory (disable fn-sn-index-of-rows-of-append-one)))))

; The enabled completion is in :completing.
(local (defthm fn-sni-enabled-is-completing
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sf-phase (fn-sn-files s)) :completing))
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp fn-sn-completion-core-enabledp)
                                  (fn-sn-statep fn-sn-completion-record
                                   fn-replay-apply-record fn-replay-apply-retention-event
                                   fn-replay-identity-step fn-sn-identity-context
                                   fn-sn-record-bindsp fn-cpe-projection-step fn-th-prefix-step
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp))))))

; The files every enabled finish leaves: the completion published and the
; success emitted on the exact pair.
; The files each constructor fn-sn-finish's arms end in leaves.
(local (defthm fn-sni-files-of-finish-constructors
  (and (equal (fn-sn-files (fn-sn-update-accepted s f n i m v)) f)
       (equal (fn-sn-files (fn-sn-update-indexed s f n i)) f)
       (equal (fn-sn-files (fn-sn-advance-identity-next s)) (fn-sn-files s))
       (equal (fn-sn-files (fn-sn-with-consumer s c)) (fn-sn-files s))
       (equal (fn-sn-files (fn-sn-with-topic s tp)) (fn-sn-files s))
       (equal (fn-sn-files (fn-sn-finish-identity s f r n)) f))
  :hints (("Goal" :in-theory (e/d (fn-sn-update-accepted fn-sn-update-indexed
                                   fn-sn-advance-identity-next fn-sn-with-consumer
                                   fn-sn-with-topic fn-sn-finish-identity fn-sn-make-v6
                                   fn-sn-files)
                                  (fn-replay-identity-step fn-sn-identity-context
                                   fn-stx-index-add fn-sn-composite-delta
                                   fn-replay-verdict-pairs))))))

; The files every enabled finish leaves: the completion published and the
; success emitted on the exact pair.  Every arm is closed but its files.
(local (defthmd fn-sni-finish-files
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sn-files (fn-sn-finish s))
                  (fn-sf-emit-success
                   (fn-sf-core-completion (fn-sn-files s)
                                          (fn-store-event-sequence (fn-sn-completion-record s))
                                          (fn-store-event-txid (fn-sn-completion-record s)))
                   (fn-store-event-sequence (fn-sn-completion-record s))
                   (fn-store-event-txid (fn-sn-completion-record s)))))
  :hints (("Goal" :in-theory (union-theories '(fn-sn-finish fn-sni-files-of-finish-constructors)
                                             (theory 'minimal-theory))))))

; The completion pair is the completion record's.
(local (defthm fn-sni-find-record-pair
  (implies (fn-sn-find-record pair records)
           (equal (fn-sf-record-pair (fn-sn-find-record pair records)) pair))
  :hints (("Goal" :in-theory (enable fn-sn-find-record)))))

(local (defthm fn-sni-completion-pair
  (implies (fn-sn-completion-enabledp s)
           (equal (cons (fn-store-event-sequence (fn-sn-completion-record s))
                        (fn-store-event-txid (fn-sn-completion-record s)))
                  (fn-sf-completion (fn-sn-files s))))
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp fn-sn-completion-core-enabledp
                                   fn-sn-completion-record)
                                  (fn-sn-statep fn-replay-apply-record
                                   fn-replay-apply-retention-event fn-replay-identity-step
                                   fn-sn-identity-context fn-sn-record-bindsp
                                   fn-cpe-projection-step fn-th-prefix-step
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp fn-sn-find-record))
           :use ((:instance fn-sni-find-record-pair
                            (pair (fn-sf-completion (fn-sn-files s)))
                            (records (fn-sf-records (fn-sn-files s)))))
           :expand ((fn-sf-record-pair (fn-sn-find-record (fn-sf-completion (fn-sn-files s))
                                                          (fn-sf-records (fn-sn-files s)))))))))

; Every reachable state is indexed: the base case.
(defthm fn-sn-initial-is-indexed
  (implies (and (fn-string-listp groups) (fn-no-duplicatesp groups)
                (natp capacity))
           (fn-sn-indexedp (fn-sn-initial groups capacity)))
  :hints (("Goal" :in-theory (e/d (fn-sn-initial fn-sn-make-v2 fn-sn-files fn-sn-index)
                                  (fn-node-initial-state fn-sf-initial-state
                                   fn-sn-index-of-rows fn-sn-indexed-rows-of))
           :use ((:instance fn-sn-initial-is-state)))))

(defthm fn-sn-prepare-preserves-indexedp
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-prepare s record)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare fn-sn-update fn-sn-make-v6 fn-sn-files fn-sn-index
                                   fn-sn-statep)
                                  (fn-sn-prepare-node fn-node-statep fn-sf-statep
                                   fn-sn-verdict-listp fn-sn-keyring-snapshot-listp
                                   fn-sn-index-of-rows fn-sn-indexed-rows-of
                                   fn-sf-prepare-record fn-sn-record-bindsp
                                   fn-cpe-projection-step))
           :use ((:instance fn-sn-prepare-preserves-state)))))

(defthm fn-sn-io-preserves-indexedp
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-io s operation result)))
  :hints (("Goal" :in-theory (e/d (fn-sn-io fn-sn-update fn-sn-make-v6 fn-sn-files fn-sn-index
                                   fn-sn-statep)
                                  (fn-sn-file-step fn-node-statep fn-sf-statep
                                   fn-sn-verdict-listp fn-sn-keyring-snapshot-listp
                                   fn-sn-index-of-rows fn-sn-indexed-rows-of))
           :use ((:instance fn-sn-io-preserves-state)))))

; THE ONE THAT DOES WORK.  The store grows here, by the one article
; fn-install-pending conses, and the index grows by the delta of exactly that
; article -- at most one cons, never a walk.  The subject is fn-sn-finish,
; which host/store-node-host.lisp line 402 (fn-store-sn-finish) calls.
; The two arms of `fn-sn-finish' that are NOT an acceptance publish no
; article, so the index the state carries is still the index of its store.
; `fn-replay-advance-txid' rebuilds the acceptance record around the same
; article list; `fn-replay-node-with-retention' replaces the retention half
; and keeps the acceptance record whole; and the identity-neutral step is two
; advances.  Each is stated over `fn-stx-store', which this proof holds
; closed, so the equation reaches the invariant without opening the store.
(local
 (defthm fn-sn-store-of-node-with-retention
   (equal (fn-stx-store (fn-replay-node-with-retention node retention))
          (fn-stx-store node))
   :hints (("Goal" :in-theory (enable fn-stx-store
                                      fn-replay-node-with-retention)))))

(local
 (defthm fn-sn-store-of-advance-txid
   (equal (fn-stx-store (fn-replay-advance-txid node recorded-txid))
          (fn-stx-store node))
   :hints (("Goal" :in-theory (enable fn-stx-store fn-replay-advance-txid)))))

(local
 (defthm fn-sn-store-of-complete-retention
   (equal (fn-stx-store (fn-replay-complete-retention node retention event))
          (fn-stx-store node))
   :hints (("Goal" :in-theory (e/d (fn-replay-complete-retention)
                                   (fn-stx-store fn-replay-advance-txid
                                    fn-replay-node-with-retention))))))

(local
 (defthm fn-sn-store-of-retention-event
   (implies (fn-replay-apply-retention-event node event)
            (equal (fn-stx-store (fn-replay-apply-retention-event node event))
                   (fn-stx-store node)))
   :hints (("Goal" :in-theory (e/d (fn-replay-apply-retention-event)
                                   (fn-stx-store fn-replay-advance-txid
                                    fn-replay-complete-retention
                                    fn-record-shape-vocabulary
                                    fn-store-retention-event-p
                                    fn-retain-admissiblep fn-retain-admit
                                    fn-retain-release))))))

(local
 (defthm fn-sn-store-of-identity-neutral
   (implies (fn-replay-apply-identity-neutral node event)
            (equal (fn-stx-store (fn-replay-apply-identity-neutral node event))
                   (fn-stx-store node)))
   :hints (("Goal" :in-theory (e/d (fn-replay-apply-identity-neutral)
                                   (fn-stx-store fn-replay-advance-txid
                                    fn-record-shape-vocabulary))))))

; And the composite identity arm whose event binds nothing: its delta is the
; delta of no octets, which is empty, and adding an empty delta is the
; identity on the index.
(local
 (defthm fn-sn-no-delta-from-no-octets
   (equal (fn-stx-delta nil keyring) nil)
   :hints (("Goal" :in-theory (enable fn-stx-delta)))))

(local
 (defthm fn-sn-index-add-of-an-empty-delta
   (equal (fn-stx-index-add index nil) index)
   :hints (("Goal" :in-theory (enable fn-stx-index-add)))))

; The composite acceptance arm replays a decoded article.  Its prepared
; article must be exactly the head added to the Store and exactly the source
; of the carried index delta; the following local facts state those two
; equations without opening the record codec in the final arm dispatch.
(local
 (defthm fn-sn-cbor-octets-are-octets
   (implies (fn-cbor-octet-listp xs) (fn-octet-listp xs))
   :hints (("Goal" :induct (fn-cbor-octet-listp xs)
            :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp
                               fn-octet-listp fn-octetp)))))

; A composite row is no other retained kind: its head is :hstxa where a held
; record's, a verdict's and a snapshot's are naturals and a retention's is
; :retention.
(local
 (defthm fn-sn-composite-kind-disjoint
   (implies (fn-hstxa-p record)
            (and (not (fn-store-retention-event-p record))
                 (not (fn-stxe-p record))
                 (not (fn-stxk-p record))
                 (not (fn-held-p record))
                 (not (fn-cpe-eventp record))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-stxe-p fn-stxe-shapep fn-record-uint32p
                             fn-stxk-p fn-stxk-shapep
                             fn-store-retention-event-p fn-cpe-eventp)
                            (fn-stxe-bounded-octetsp fn-record-msgidp
                             fn-record-metadata-bytes-p))))))

(local
 (defthm fn-sn-composite-idle-has-no-pending
   (implies (and (fn-node-statep node) (null (fn-node-stage node)))
            (null (fn-state-pending (fn-node-acceptance node))))
   :hints (("Goal" :in-theory (enable fn-node-statep)))))

(local
 (defthm fn-sn-composite-stage-of-advance
   (equal (fn-node-stage (fn-replay-advance-txid node txid))
          (fn-node-stage node))
   :hints (("Goal" :in-theory (enable fn-replay-advance-txid)))))

(local
 (defthm fn-sn-composite-is-not-topic-event
   (implies (fn-hstxa-p event)
            (not (fn-th-topic-eventp event)))
   :hints (("Goal" :in-theory
            (e/d (fn-th-topic-eventp fn-th-local-admin-eventp)
                 (fn-stxe-bounded-octetsp fn-th-auth-ref-p
                  fn-th-source-id-p fn-th-parents-p))))))

(local
 (defthm fn-sn-composite-replay-article-typed
   (implies (and (fn-hstxa-p event)
                 (consp (fn-replay-apply-record node event)))
            (fn-held-p (fn-replay-composite-held event)))
   :hints (("Goal" :in-theory (e/d (fn-replay-apply-record)
                                   (fn-stxa-p fn-stxe-p fn-stxk-p
                                    fn-th-topic-eventp
                                    fn-store-retention-event-p
                                    fn-replay-advance-txid fn-node-prepare
                                    fn-node-complete fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))

(local
 (defthm fn-sn-composite-replay-installs-decoded-payload
   (implies (and (fn-node-statep node)
                 (null (fn-node-stage node))
                 (fn-hstxa-p event)
                 (consp (fn-replay-apply-record node event)))
            (equal (fn-article-payload
                    (car (fn-stx-store (fn-replay-apply-record node event))))
                   (fn-record-payload (fn-replay-composite-held event))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-replay-apply-record fn-node-complete
                             fn-accept-complete fn-install-pending
                             fn-article-from-pending fn-node-prepare
                             fn-accept-prepare fn-stx-store fn-node-statep
                             fn-node-pending-matchesp fn-pending-matchesp)
                            (fn-statep fn-record-shape-vocabulary
                             fn-record-record-vocabulary fn-stxa-p fn-stxe-p
                             fn-stxk-p fn-store-retention-event-p
                             fn-replay-composite-record
                             fn-replay-advance-txid))))))

(local
 (defthm fn-sn-composite-replay-installs-one-article
   (implies (and (fn-node-statep node)
                 (null (fn-node-stage node))
                 (fn-hstxa-p event)
                 (consp (fn-replay-apply-record node event)))
            (and (consp (fn-stx-store (fn-replay-apply-record node event)))
                 (equal (cdr (fn-stx-store (fn-replay-apply-record node event)))
                        (fn-stx-store node))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-replay-apply-record fn-node-complete
                             fn-accept-complete fn-install-pending
                             fn-article-from-pending fn-node-prepare
                             fn-accept-prepare fn-stx-store fn-node-statep
                             fn-node-pending-matchesp fn-pending-matchesp)
                            (fn-statep fn-record-shape-vocabulary
                             fn-record-record-vocabulary fn-stxa-p fn-stxe-p
                             fn-stxk-p fn-store-retention-event-p
                             fn-replay-composite-record
                             fn-replay-advance-txid))))))

(local
 (defthm fn-sn-composite-delta-of-typed-article
   (implies (and (fn-prin-keyringp keyring) (fn-hstxa-p event))
            (equal (fn-sn-composite-delta event keyring)
                   (fn-hc-delta (fn-held-context (fn-hstxa-held event)))))
   :hints (("Goal" :in-theory (enable fn-sn-composite-delta)))))

(local
 (defthmd fn-sn-finish-composite-arm-fields
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-hstxa-p (fn-sn-completion-record s)))
            (and (equal (fn-sn-index (fn-sn-finish s))
                        (fn-stx-index-add
                         (fn-sn-index s)
                         (fn-sn-composite-delta (fn-sn-completion-record s)
                                                (fn-sn-keyring s))))
                 (equal (fn-sn-node (fn-sn-finish s))
                        (fn-replay-apply-record
                         (fn-sn-node s) (fn-sn-completion-record s)))
                 (equal (fn-sn-keyring (fn-sn-finish s))
                        (fn-sn-keyring s))))
   :hints (("Goal" :in-theory (e/d (fn-sn-finish fn-sn-finish-identity)
                                   (fn-sn-completion-enabledp fn-sn-statep
                                    fn-sn-completion-record
                                    fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                                    fn-replay-apply-record fn-replay-identity-step
                                    fn-sn-identity-context fn-sf-core-completion
                                    fn-sf-emit-success fn-sn-composite-delta
                                    fn-sn-make-v6
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))
;; fn-sn-finish-preserves-indexedp, one arm at a time.  The theorem below
;; dispatches on the finish arm; with `fn-sn-finish', `fn-sn-completion-
;; enabledp' and `fn-sn-record-bindsp' open it split 5249 ways at Goal'' on
;; the record codec, the replay steps and the store-transaction recognizers
;; (118.8 s, 50.8 million steps, 13 734 subgoals on the 2026-09-23 seam run,
;; planning/evidence/store-cluster-cost-2026-09-23.md).  What it needs from
;; each arm is three fields of the result, stated here once per arm with the
;; replay steps and the recognizers closed; the theorem is then a `:cases' on
;; the arm; the disabled branch is `fn-sn-finish-disabled-is-no-op' above.
;; They are enabled only in that theorem's hint.
(local
 (defthmd fn-sn-finish-retention-arm-keeps-the-store-and-index
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-store-retention-event-p (fn-sn-completion-record s)))
            (and (equal (fn-sn-index (fn-sn-finish s)) (fn-sn-index s))
                 (equal (fn-sn-keyring (fn-sn-finish s)) (fn-sn-keyring s))
                 (equal (fn-stx-store (fn-sn-node (fn-sn-finish s)))
                        (fn-stx-store (fn-sn-node s)))))
   :hints (("Goal" :in-theory (e/d (fn-sn-finish fn-sn-completion-enabledp)
                                   (fn-sn-statep fn-stx-store
                                    fn-replay-apply-retention-event
                                    fn-replay-apply-record
                                    fn-replay-identity-step fn-sn-identity-context
                                    fn-sf-core-completion fn-sf-emit-success
                                    fn-sn-completion-record fn-sn-record-bindsp
                                    fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                                    fn-node-complete fn-sn-accepted-delta
                                    fn-sn-make-v6
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))
(local
 (defthmd fn-sn-finish-identity-arm-keeps-the-store-and-index
   (implies (and (fn-sn-completion-enabledp s)
                 (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                 (or (fn-stxe-p (fn-sn-completion-record s))
                     (fn-stxk-p (fn-sn-completion-record s)))
                 (not (fn-hstxa-p (fn-sn-completion-record s))))
            (and (equal (fn-sn-index (fn-sn-finish s)) (fn-sn-index s))
                 (equal (fn-stx-store (fn-sn-node (fn-sn-finish s)))
                        (fn-stx-store (fn-sn-node s)))))
   :hints (("Goal" :in-theory (e/d (fn-sn-finish fn-sn-completion-enabledp)
                                   (fn-sn-statep fn-stx-store
                                    fn-replay-apply-retention-event
                                    fn-replay-apply-identity-neutral
                                    fn-replay-composite-record
                                    fn-replay-identity-step fn-sn-identity-context
                                    fn-sf-core-completion fn-sf-emit-success
                                    fn-sn-completion-record fn-sn-record-bindsp
                                    fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                                    fn-node-complete fn-sn-accepted-delta
                                    fn-sn-make-v6
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))

; Consumer records are a distinct five-field Store kind.  Their node replay
; only advances txid; the carried consumer projection changes separately.
(local
 (defthm fn-snx-cpe-no-other-event
   (implies (fn-cpe-eventp event)
            (and (not (fn-store-retention-event-p event))
                 (not (fn-stxe-p event))
                 (not (fn-stxk-p event))
                 (not (fn-stxa-p event))
                 (not (fn-held-p event))
                 (not (fn-hstxa-p event))))
   :hints (("Goal" :in-theory (enable fn-cpe-eventp
                                      fn-store-retention-event-p
                                      fn-stxe-shapep fn-stxk-shapep
                                      fn-stxa-shapep)))))
(local
 (defthm fn-snx-identity-neutral-keeps-articles
   (implies (consp (fn-replay-apply-identity-neutral node event))
            (equal (fn-state-articles
                    (fn-node-acceptance
                     (fn-replay-apply-identity-neutral node event)))
                   (fn-state-articles (fn-node-acceptance node))))
   :hints (("Goal" :in-theory (enable fn-replay-apply-identity-neutral)))))
(local
 (defthm fn-snx-consumer-completion-node-idle-by-definition
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-cpe-eventp (fn-sn-completion-record s)))
            (null (fn-node-stage (fn-sn-node s))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-completion-enabledp fn-replay-apply-record)
                 (fn-cpe-eventp fn-store-retention-event-p
                  fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                  fn-sn-statep fn-sn-record-bindsp
                  fn-node-pending-matchesp fn-pending-matchesp
                  fn-replay-apply-identity-neutral))))))
(local
 (defthm fn-snx-consumer-completion-replay-non-nil-by-definition
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-cpe-eventp (fn-sn-completion-record s)))
            (consp (fn-replay-apply-identity-neutral
                    (fn-sn-node s) (fn-sn-completion-record s))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-completion-enabledp fn-replay-apply-record)
                 (fn-cpe-eventp fn-store-retention-event-p
                  fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                  fn-sn-statep fn-sn-record-bindsp
                  fn-node-pending-matchesp fn-pending-matchesp
                  fn-replay-apply-identity-neutral))))))
(local
 (defthmd fn-sn-finish-consumer-arm-keeps-the-store-and-index
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-cpe-eventp (fn-sn-completion-record s)))
            (and (equal (fn-sn-index (fn-sn-finish s)) (fn-sn-index s))
                 (equal (fn-sn-keyring (fn-sn-finish s)) (fn-sn-keyring s))
                 (equal (fn-stx-store (fn-sn-node (fn-sn-finish s)))
                        (fn-stx-store (fn-sn-node s)))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-finish fn-stx-store fn-replay-apply-record)
                 (fn-sn-completion-enabledp fn-sn-completion-record
                  fn-cpe-eventp
                  fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                  fn-replay-apply-identity-neutral
                  fn-replay-apply-retention-event fn-sf-core-completion
                  fn-sf-emit-success fn-record-shape-vocabulary
                  fn-sn-make-v6))
            :use (fn-snx-consumer-completion-node-idle-by-definition
                  fn-snx-consumer-completion-replay-non-nil-by-definition)))))
(local
 (defthm fn-snx-topic-not-consumer-tag
   (implies (fn-th-topic-eventp event)
            (not (equal (car event) :consumer)))
   :hints (("Goal" :use (fn-th-topic-event-has-topic-tag)
            :in-theory (enable member-equal)))))
(local
 (defthm fn-snx-topic-not-retention-tag
   (implies (fn-th-topic-eventp event)
            (not (equal (car event) :retention)))
   :hints (("Goal" :use (fn-th-topic-event-has-topic-tag)
            :in-theory (enable member-equal)))))
(local
 (defthm fn-snx-topic-no-other-event
   (implies (fn-th-topic-eventp event)
            (and (not (fn-store-retention-event-p event))
                 (not (fn-stxe-p event))
                 (not (fn-stxk-p event))
                 (not (fn-stxa-p event))
                 (not (fn-cpe-eventp event))
                 (not (fn-held-p event))
                 (not (fn-hstxa-p event))))
   :hints (("Goal" :in-theory
            (e/d (fn-store-retention-event-p fn-cpe-eventp)
                 (fn-th-topic-eventp fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                  fn-stxe-shapep fn-stxk-shapep fn-stxa-shapep))
            :use (fn-th-topic-event-is-not-stxe
                  fn-th-topic-event-is-not-stxk
                  fn-th-topic-event-is-not-stxa)))))
(local
 (defthm fn-snx-topic-completion-node-idle-by-definition
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-th-topic-eventp (fn-sn-completion-record s)))
            (null (fn-node-stage (fn-sn-node s))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-completion-enabledp fn-replay-apply-record)
                 (fn-th-topic-eventp fn-cpe-eventp
                  fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                  fn-replay-apply-identity-neutral))))))
(local
 (defthm fn-snx-topic-completion-replay-non-nil-by-definition
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-th-topic-eventp (fn-sn-completion-record s)))
            (consp (fn-replay-apply-identity-neutral
                    (fn-sn-node s) (fn-sn-completion-record s))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-completion-enabledp fn-replay-apply-record)
                 (fn-th-topic-eventp fn-cpe-eventp
                  fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                  fn-replay-apply-identity-neutral))))))
(local
 (defthmd fn-sn-finish-topic-arm-keeps-the-store-and-index
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-th-topic-eventp (fn-sn-completion-record s)))
            (and (equal (fn-sn-index (fn-sn-finish s)) (fn-sn-index s))
                 (equal (fn-sn-keyring (fn-sn-finish s)) (fn-sn-keyring s))
                 (equal (fn-stx-store (fn-sn-node (fn-sn-finish s)))
                        (fn-stx-store (fn-sn-node s)))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-finish fn-stx-store fn-replay-apply-record)
                 (fn-sn-completion-enabledp fn-sn-completion-record
                  fn-th-topic-eventp fn-cpe-eventp
                  fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                  fn-replay-apply-identity-neutral
                  fn-replay-apply-retention-event fn-sf-core-completion
                  fn-sf-emit-success fn-record-shape-vocabulary
                  fn-sn-make-v6))
            :use (fn-snx-topic-completion-node-idle-by-definition
                  fn-snx-topic-completion-replay-non-nil-by-definition)))))

; Topic installation, anchor and report admission are real durable Store
; completions.  They advance the exact Store pair and the carried topic
; projection while leaving article acceptance and its index unchanged.
(defthm fn-sn-finish-topic-completion
  (implies (and (fn-sn-completion-enabledp s)
                (fn-th-topic-eventp (fn-sn-completion-record s)))
           (and (equal (fn-sf-successes (fn-sn-files (fn-sn-finish s)))
                       (append (fn-sf-successes (fn-sn-files s))
                               (list (cons
                                      (fn-store-event-sequence
                                       (fn-sn-completion-record s))
                                      (fn-store-event-txid
                                       (fn-sn-completion-record s))))))
                (equal (fn-sn-topic (fn-sn-finish s))
                       (fn-th-prefix-step (fn-sn-topic s)
                                          (fn-sn-completion-record s)))
                (equal (fn-sn-index (fn-sn-finish s)) (fn-sn-index s))
                (equal (fn-stx-store (fn-sn-node (fn-sn-finish s)))
                       (fn-stx-store (fn-sn-node s)))))
  :hints (("Goal" :use (fn-sn-finish-acknowledges-exact-pair
                         fn-sn-finish-topic-arm-keeps-the-store-and-index)
           :in-theory (e/d (fn-sn-finish fn-sn-completion-enabledp)
                           (fn-th-topic-eventp fn-sn-completion-record
                            fn-replay-apply-record fn-sn-finish-acknowledges-exact-pair
                            fn-sn-finish-topic-arm-keeps-the-store-and-index
                            fn-sf-core-completion fn-sf-emit-success
                            fn-record-shape-vocabulary fn-sn-make-v6)))))
(local
 (defthmd fn-sn-finish-acceptance-arm-fields
   (implies (and (fn-sn-completion-enabledp s)
                 (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                 (not (fn-stxe-p (fn-sn-completion-record s)))
                 (not (fn-stxk-p (fn-sn-completion-record s)))
                 (not (fn-hstxa-p (fn-sn-completion-record s)))
                 (not (fn-cpe-eventp (fn-sn-completion-record s)))
                 (not (fn-th-topic-eventp (fn-sn-completion-record s))))
            (and (equal (fn-sn-index (fn-sn-finish s))
                        (fn-stx-index-add (fn-sn-index s)
                                          (fn-sn-accepted-delta s)))
                 (equal (fn-sn-keyring (fn-sn-finish s)) (fn-sn-keyring s))
                 (equal (fn-sn-node (fn-sn-finish s))
                        (fn-node-complete
                         (fn-sn-node s)
                         (fn-record-txid (fn-sn-completion-record s))
                         (fn-record-generation (fn-sn-completion-record s))
                         :durable))
                 (fn-node-pending-matchesp
                  (fn-sn-node s)
                  (fn-record-txid (fn-sn-completion-record s))
                  (fn-record-generation (fn-sn-completion-record s)))))
   :hints (("Goal" :in-theory (e/d (fn-sn-finish fn-sn-completion-enabledp
                                    fn-sn-record-bindsp)
                                   (fn-sn-statep fn-stx-store
                                    fn-replay-apply-retention-event
                                    fn-replay-apply-record
                                    fn-replay-identity-step fn-sn-identity-context
                                    fn-sf-core-completion fn-sf-emit-success
                                    fn-sn-completion-record
                                    fn-node-pending-matchesp fn-sn-pending-record
                                    fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                                    fn-th-topic-eventp
                                    fn-node-complete fn-sn-accepted-delta
                                    fn-stx-index-add
                                    fn-sn-make-v6
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))

; The other kinds are neither an article row nor a composite row, so their
; row delta is nothing (fn-sn-row-delta), and a completion of one keeps the
; index.
(local (defthm fn-sni-retention-is-not-a-row
  (implies (fn-store-retention-event-p x)
           (and (not (fn-held-p x)) (not (fn-hstxa-p x))))
  :hints (("Goal" :in-theory (e/d (fn-store-retention-event-p) ())))))
(local (defthm fn-sni-stxe-is-not-a-row
  (implies (fn-stxe-p x) (and (not (fn-held-p x)) (not (fn-hstxa-p x))))
  :hints (("Goal" :use ((:instance fn-sn-an-article-record-is-no-other-store-event (record x))
                        (:instance fn-sn-composite-kind-disjoint (record x)))
           :in-theory (disable fn-sn-an-article-record-is-no-other-store-event
                               fn-sn-composite-kind-disjoint)))))
(local (defthm fn-sni-stxk-is-not-a-row
  (implies (fn-stxk-p x) (and (not (fn-held-p x)) (not (fn-hstxa-p x))))
  :hints (("Goal" :use ((:instance fn-sn-an-article-record-is-no-other-store-event (record x))
                        (:instance fn-sn-composite-kind-disjoint (record x)))
           :in-theory (disable fn-sn-an-article-record-is-no-other-store-event
                               fn-sn-composite-kind-disjoint)))))

; The completion record of an enabled finish is a row of the history, so a
; retained event; the one kind it is decides its delta.
(local (defthm fn-sni-find-record-is-a-value
  (implies (and (fn-sf-record-valuesp records) (fn-sn-find-record pair records))
           (fn-store-event-p (fn-sn-find-record pair records)))
  :hints (("Goal" :in-theory (enable fn-sn-find-record fn-sf-record-valuesp)))))
(local (defthm fn-sni-record-listp-values
  (implies (fn-sf-record-listp records sequence lower frontier)
           (fn-sf-record-valuesp records))
  :hints (("Goal" :in-theory (enable fn-sf-record-listp fn-sf-record-valuesp)))))
(local (defthm fn-sni-completion-record-is-store-event
  (implies (and (fn-sn-statep s) (fn-sn-completion-enabledp s))
           (fn-store-event-p (fn-sn-completion-record s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp fn-sn-completion-core-enabledp
                                   fn-sn-completion-record fn-sn-statep fn-sf-statep)
                                  (fn-sf-phase-shapep fn-sf-success-listp fn-node-statep
                                   fn-sn-find-record fn-replay-apply-record
                                   fn-replay-apply-retention-event fn-replay-identity-step
                                   fn-sn-identity-context fn-sn-record-bindsp
                                   fn-cpe-projection-step fn-th-prefix-step
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp fn-held-p
                                   fn-sf-record-listp fn-sf-record-valuesp))
           :use ((:instance fn-sni-find-record-is-a-value
                            (pair (fn-sf-completion (fn-sn-files s)))
                            (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-sni-record-listp-values
                            (records (fn-sf-records (fn-sn-files s)))
                            (sequence 0) (lower 0) (frontier (fn-sf-frontier (fn-sn-files s)))))))))

; THE ONE THAT DOES WORK.  The history grew at the directory barrier; the
; finish indexes exactly that last row: its context's delta on the article
; arm, its interned article's on the composite arm, nothing on the others.
; The subject is fn-sn-finish, which host/store-node-host.lisp
; (fn-store-sn-finish) calls.
(defthm fn-sn-finish-preserves-indexedp
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-finish s)))
  :hints (("Goal"
           :cases ((not (fn-sn-completion-enabledp s))
                   (and (fn-sn-completion-enabledp s)
                        (fn-store-retention-event-p (fn-sn-completion-record s)))
                   (and (fn-sn-completion-enabledp s)
                        (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                        (or (fn-stxe-p (fn-sn-completion-record s))
                            (fn-stxk-p (fn-sn-completion-record s)))
                        (not (fn-hstxa-p (fn-sn-completion-record s))))
                   (and (fn-sn-completion-enabledp s)
                        (fn-hstxa-p (fn-sn-completion-record s)))
                   (and (fn-sn-completion-enabledp s)
                        (fn-cpe-eventp (fn-sn-completion-record s)))
                   (and (fn-sn-completion-enabledp s)
                        (fn-th-topic-eventp (fn-sn-completion-record s)))
                   (and (fn-sn-completion-enabledp s)
                        (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                        (not (fn-stxe-p (fn-sn-completion-record s)))
                        (not (fn-stxk-p (fn-sn-completion-record s)))
                        (not (fn-hstxa-p (fn-sn-completion-record s)))
                        (not (fn-cpe-eventp (fn-sn-completion-record s)))
                        (not (fn-th-topic-eventp (fn-sn-completion-record s)))))
           :in-theory (e/d (fn-sn-finish-retention-arm-keeps-the-store-and-index
                            fn-sn-finish-identity-arm-keeps-the-store-and-index
                            fn-sn-finish-composite-arm-fields
                            fn-sn-finish-consumer-arm-keeps-the-store-and-index
                            fn-sn-finish-topic-arm-keeps-the-store-and-index
                            fn-sn-finish-acceptance-arm-fields
                            fn-sni-finish-files fn-sn-row-delta fn-store-event-p
                            fn-sn-accepted-delta fn-sn-indexed-rows-of
                            fn-sn-completion-is-last-p)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-sn-completion-record fn-sn-record-bindsp
                            fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p fn-cpe-eventp
                            fn-th-topic-eventp fn-held-p
                            fn-replay-apply-record fn-replay-identity-step
                            fn-sn-identity-context
                            fn-sf-core-completion fn-sf-emit-success
                            fn-node-statep fn-node-complete fn-sf-statep
                            fn-stx-index-of-store fn-stx-store fn-stx-index-add
                            fn-node-pending-matchesp
                            fn-record-shape-vocabulary fn-record-record-vocabulary
                            fn-sn-index-of-rows fn-sn-all-but-last
                            fn-sn-verdict-listp fn-sn-keyring-snapshot-listp))
           :use ((:instance fn-sn-finish-preserves-state)
                 (:instance fn-sn-finish-disabled-is-no-op)
                 (:instance fn-sni-completion-record-is-last)
                 (:instance fn-sni-completion-record-is-store-event)
                 (:instance fn-sni-completion-pair)
                 (:instance fn-sni-enabled-is-completing)
                 (:instance fn-sni-index-of-rows-at-last
                            (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-sn-indexed-rows-of-completion (files (fn-sn-files s))
                            (sequence (fn-store-event-sequence (fn-sn-completion-record s)))
                            (txid (fn-store-event-txid (fn-sn-completion-record s))))))))

; -by-recomputation: a crash resets the node to the empty store and the index
; to the empty one; the rows are not indexed again until recovery.
; The files and the index each constructor the crash and the recovery end in
; leaves; with these the two proofs below never open the 14-slot state.
(local (defthm fn-sni-files-index-of-constructors
  (and (equal (fn-sn-files (fn-sn-update-indexed s f n i)) f)
       (equal (fn-sn-index (fn-sn-update-indexed s f n i)) i)
       (equal (fn-sn-files (fn-sn-update-replayed s f n i c)) f)
       (equal (fn-sn-index (fn-sn-update-replayed s f n i c)) i)
       (equal (fn-sn-files (fn-sn-update s f n)) f)
       (equal (fn-sn-index (fn-sn-update s f n)) (fn-sn-index s))
       (equal (fn-sn-files (fn-sn-with-topic s tp)) (fn-sn-files s))
       (equal (fn-sn-index (fn-sn-with-topic s tp)) (fn-sn-index s))
       (equal (fn-sn-files (fn-sn-with-consumer s c)) (fn-sn-files s))
       (equal (fn-sn-index (fn-sn-with-consumer s c)) (fn-sn-index s))
       (equal (fn-sn-files (fn-sn-with-event-index s e)) (fn-sn-files s))
       (equal (fn-sn-index (fn-sn-with-event-index s e)) (fn-sn-index s)))
  :hints (("Goal" :in-theory (enable fn-sn-update-indexed fn-sn-update-replayed fn-sn-update
                                     fn-sn-with-topic fn-sn-with-consumer fn-sn-with-event-index
                                     fn-sn-make-v6 fn-sn-files fn-sn-index)))))

(local (defthm fn-sni-statep-files
  (implies (fn-sn-statep s) (fn-sf-statep (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep))))))

(defthm fn-sn-crash-preserves-indexedp-by-recomputation
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-crash s frontier-choice record-choice)))
  :hints (("Goal" :use ((:instance fn-sn-crash-preserves-state)
                        (:instance fn-sn-indexed-rows-of-crash (files (fn-sn-files s))))
           :in-theory (union-theories '(fn-sn-indexedp fn-sn-crash fn-sn-indexed-rows
                                        fn-sni-files-index-of-constructors fn-sni-statep-files
                                        fn-sn-index-of-rows-of-nil)
                                      (theory 'minimal-theory)))))

; The :fault arm of the recovery: its files hold no indexed row and no
; completion, and the store's index at :replaying was the empty fold.
(local (defthm fn-sni-fault-files-facts
  (and (equal (fn-sn-indexed-rows-of (fn-sf-make :fault fr nil rs nil nil su 0)) nil)
       (fn-sn-completion-is-last-p (fn-sf-make :fault fr nil rs nil nil su 0)))
  :hints (("Goal" :in-theory (enable fn-sn-indexed-rows-of fn-sn-completion-is-last-p)))))

(local (defthm fn-sni-replaying-has-no-indexed-rows
  (implies (equal (fn-sf-phase files) :replaying)
           (equal (fn-sn-indexed-rows-of files) nil))
  :hints (("Goal" :in-theory (enable fn-sn-indexed-rows-of)))))

; -by-recomputation: recovery's node comes from a replay, not from a step of
; this machine, so its index is recomputed: the fold of every row's context.
(defthm fn-sn-recover-preserves-indexedp-by-recomputation
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-recover s)))
  :hints (("Goal" :use ((:instance fn-sn-recover-preserves-state)
                        (:instance fn-sn-indexed-rows-of-recover (files (fn-sn-files s))
                                   (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s)))
                        (:instance fn-sni-replaying-has-no-indexed-rows (files (fn-sn-files s))))
           :in-theory (union-theories '(fn-sn-indexedp fn-sn-recover fn-sn-indexed-rows
                                        fn-sni-files-index-of-constructors fn-sni-statep-files
                                        fn-sni-fault-files-facts fn-sn-index-of-rows-of-nil
                                        eq)
                                      (theory 'minimal-theory)))))

; The keyring installation rebuilds the history with new contexts
; (fn-sn-recontext-rows): every row keeps its kind and its coordinates, so
; the history's shape facts, and the successes that name its pairs, hold of
; the rebuilt one.
(local (defthm fn-sni-recontexted-row-fields
  (implies (and (fn-held-p h) (fn-hc-p ctx))
           (and (fn-store-event-p (fn-held-with-context h ctx))
                (equal (fn-store-event-sequence (fn-held-with-context h ctx))
                       (fn-store-event-sequence h))
                (equal (fn-store-event-txid (fn-held-with-context h ctx))
                       (fn-store-event-txid h))
                (equal (fn-store-event-generation (fn-held-with-context h ctx))
                       (fn-store-event-generation h))))
  :hints (("Goal" :in-theory (e/d (fn-store-event-p fn-store-event-sequence
                                   fn-store-event-txid fn-store-event-generation)
                                  (fn-held-p fn-held-with-context))))))

(local (defthm fn-sni-recontexted-composite-fields
  (implies (and (fn-hstxa-p x) (fn-hc-p ctx))
           (let ((r (fn-hstxa-make (fn-hstxa-stxa x)
                                   (fn-held-with-context (fn-hstxa-held x) ctx))))
             (and (fn-store-event-p r)
                  (equal (fn-store-event-sequence r) (fn-store-event-sequence x))
                  (equal (fn-store-event-txid r) (fn-store-event-txid x))
                  (equal (fn-store-event-generation r) (fn-store-event-generation x)))))
  :hints (("Goal" :in-theory (e/d (fn-store-event-p fn-store-event-sequence
                                   fn-store-event-txid fn-store-event-generation)
                                  (fn-held-p fn-hstxa-p fn-held-with-context))))))

; The induction the two walks share: the rows and the contexts as the
; recontext consumes them, the sequence and the lower txid bound as the
; history recognizer advances them.
(local (defun fn-sni-recontext-induct (rows contexts generation sequence lower frontier)
  (declare (xargs :measure (len rows)))
  (cond ((atom rows) (list contexts generation sequence lower frontier))
        ((or (fn-held-p (car rows)) (fn-hstxa-p (car rows)))
         (fn-sni-recontext-induct (cdr rows) (cdr contexts) generation
                                  (1+ sequence) (1+ (fn-store-event-txid (car rows)))
                                  frontier))
        (t (fn-sni-recontext-induct (cdr rows) contexts generation
                                    (1+ sequence) (1+ (fn-store-event-txid (car rows)))
                                    frontier)))))

(local (defthm fn-sni-recontext-keeps-record-listp
  (implies (and (fn-sf-record-listp rows sequence lower frontier)
                (not (equal (fn-sn-recontext-rows rows contexts generation) :mismatch)))
           (fn-sf-record-listp (fn-sn-recontext-rows rows contexts generation)
                               sequence lower frontier))
  :hints (("Goal" :induct (fn-sni-recontext-induct rows contexts generation sequence lower frontier)
           :in-theory (e/d (fn-sn-recontext-rows fn-sf-record-listp)
                           (fn-held-p fn-hstxa-p fn-hc-p fn-held-with-context
                            fn-store-event-p fn-store-event-sequence
                            fn-store-event-txid fn-store-event-generation))))))

(local (defthm fn-sni-recontext-keeps-pairs
  (implies (not (equal (fn-sn-recontext-rows rows contexts generation) :mismatch))
           (iff (fn-sf-record-has-pairp pair (fn-sn-recontext-rows rows contexts generation))
                (fn-sf-record-has-pairp pair rows)))
  :hints (("Goal" :induct (fn-sn-recontext-rows rows contexts generation)
           :in-theory (e/d (fn-sn-recontext-rows fn-sf-record-has-pairp fn-sf-record-pair)
                           (fn-held-p fn-hstxa-p fn-hc-p fn-held-with-context
                            fn-store-event-p fn-store-event-sequence
                            fn-store-event-txid fn-store-event-generation))))))

(local (defthm fn-sni-recontext-keeps-success-listp
  (implies (not (equal (fn-sn-recontext-rows rows contexts generation) :mismatch))
           (iff (fn-sf-success-listp successes (fn-sn-recontext-rows rows contexts generation))
                (fn-sf-success-listp successes rows)))
  :hints (("Goal" :induct (fn-sf-success-listp successes rows)
           :in-theory (e/d (fn-sf-success-listp) (fn-sf-record-has-pairp fn-sn-recontext-rows))))))

(defthm fn-sn-set-keyring-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-set-keyring s keyring contexts)))
  :hints (("Goal" :in-theory (e/d (fn-sn-set-keyring fn-sn-statep fn-sf-statep fn-sf-phase-shapep)
                                  (fn-node-statep fn-sn-recontext-rows fn-cei-build
                                   fn-sf-record-listp fn-sf-success-listp
                                   fn-sn-verdict-listp fn-sn-keyring-snapshot-listp
                                   fn-sn-index-of-rows fn-sf-frontier-phasep
                                   fn-sf-record-phasep fn-sf-completion-phasep)))))

; -by-recomputation: the keyring installation recontexts every row and folds
; them again, at :ready, which is correct and is not a served path.
(defthm fn-sn-set-keyring-preserves-indexedp-by-recomputation
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-set-keyring s keyring contexts)))
  :hints (("Goal" :in-theory (e/d (fn-sn-set-keyring fn-sn-make-v6 fn-sn-files fn-sn-index
                                   fn-sn-indexed-rows-of fn-sn-completion-is-last-p)
                                  (fn-sf-statep fn-node-statep fn-sn-statep
                                   fn-sn-index-of-rows fn-sn-recontext-rows fn-cei-build))
           :use ((:instance fn-sn-set-keyring-preserves-state)))))

; The served queries' agreement with the lace of the rows' BYTES is stated
; where the bytes are: books/store-intern.lisp (fn-store-statement-lookup-is-
; the-lace-lookup, over the arena, under the context invariant every intern
; establishes).  Here the index is the fold of the rows' contexts and no more.

; -----------------------------------------------------------------------------
; Export theory.  Withdrawn under a name: the replay-composition and
; frontier-advance lemmas (proof vocabulary for the trace books) and the
; committed-record recognizer.  Enabled on include: the preservation
; keystones, the cannot-acknowledge family, the completion-gate keystone
; and the resolution correspondences.
(deftheory fn-store-node-invariants-vocabulary
  '(fn-sn-file-recovery-retains-history fn-sn-replay-loop-append
    fn-sn-replay-singleton-is-live-completion
    fn-sn-extended-history-equals-live-completion
    fn-snt-node-reconstruct fn-snt-acceptance-reconstruct
    fn-snt-valid-node-is-consp fn-snt-advanced-node-is-consp
    fn-snt-advance-is-idle fn-snt-advance-at-current-is-identity
    fn-snt-advance-twice fn-snt-history-recoverable-monotone
    fn-snt-replayed-node-idle-and-frontier fn-snt-advance-replayed-node
    fn-snt-successful-replay-sequence fn-snt-successful-replay-history-length
    fn-snt-prepared-abort-is-frontier-advance
    fn-snt-prepared-durable-is-idle-at-successor
    fn-snt-apply-event-from-idle-is-idle-and-monotone
    fn-snt-apply-event-from-idle-is-at-the-successor))
(in-theory (disable fn-store-node-invariants-vocabulary fn-sn-committed-recordp))
