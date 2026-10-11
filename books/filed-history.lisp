; O1 packet 4, P4-R (transport), the Store layer, DRAFT (C13, 2026-10-10).
; The history invariant over the Store's files: every committed record and
; the staged candidate are filed within their own payloads (through the
; arena that holds their handles).  Records change only at the record
; directory's :ok (the candidate appended) and at a crash (the candidate
; appended or not); the candidate only at a prepare.  So the invariant
; holds after every Store transition, given that what a prepare stages is
; filed (that premise is the per-arm packet: P2-2, P2-3, P4-1, P4-3, P4-6a,
; P4-6b, and P4-2's duplicate answer for the operator's reinjection).
; Recovery replays the records it finds (fn-sf-recover keeps them), so it
; carries the invariant of the history it replays (Codex F10); nothing is
; re-established.  The arena is fixed here; its interning (handles never
; rebound) is P4-R6, stated separately.

(in-package "ACL2")

(include-book "filed-catalog")
(include-book "store-intern")
(include-book "store-reclaim-pack")      ; fn-rclp-tombstoned
(include-book "history-fold-refinement") ; fn-rows-composites-okp

; Rows in an arena: their articles filed or reclaimed, each what the intern
; makes of a row (a composite row's held article is its composite's
; article), every handle in the arena.
(defun fn-o1-rows-invp (rows fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (and (fn-o1-records-filed-or-reclaimedp (fn-cat-history-articles rows fn-arena))
       (fn-rows-composites-okp rows fn-arena)
       (fn-rows-handles-inp rows fn-arena)))

; The Store's files: the records and the staged candidate.
(defun fn-o1-files-invp (files fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (and (fn-o1-rows-invp (fn-sf-records files) fn-arena)
       (fn-o1-rows-invp (list (fn-sf-record-candidate files)) fn-arena)))

(local
 (defthm o1h-history-articles-of-append
   (equal (fn-cat-history-articles (append a b) fn-arena)
          (append (fn-cat-history-articles a fn-arena) (fn-cat-history-articles b fn-arena)))))

(local
 (defthm o1h-fr-append
   (equal (fn-o1-records-filed-or-reclaimedp (append a b))
          (and (fn-o1-records-filed-or-reclaimedp a) (fn-o1-records-filed-or-reclaimedp b)))
   :hints (("Goal" :induct (fn-o1-records-filed-or-reclaimedp a)
            :in-theory (disable fn-o1-filed-within-sourcep)))))

(local
 (defthm o1h-comp-append
   (equal (fn-rows-composites-okp (append a b) fn-arena)
          (and (fn-rows-composites-okp a fn-arena) (fn-rows-composites-okp b fn-arena)))
   :hints (("Goal" :induct (fn-rows-composites-okp a fn-arena)))))

(local
 (defthm o1h-handles-append
   (equal (fn-rows-handles-inp (append a b) fn-arena)
          (and (fn-rows-handles-inp a fn-arena) (fn-rows-handles-inp b fn-arena)))
   :hints (("Goal" :induct (fn-rows-handles-inp a fn-arena)))))

; Rows are invariant exactly when their parts are (the lifecycle books split
; a row list by this).
(defthm fn-o1-rows-invp-append
  (equal (fn-o1-rows-invp (append a b) fn-arena)
         (and (fn-o1-rows-invp a fn-arena) (fn-o1-rows-invp b fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-o1-rows-invp)
                                  (fn-o1-records-filed-or-reclaimedp fn-rows-composites-okp
                                   fn-rows-handles-inp)))))

(local
 (defthm o1h-invp-nil
   (fn-o1-rows-invp nil fn-arena)
   :hints (("Goal" :in-theory (enable fn-o1-rows-invp)))))

(local
 (defthm o1h-invp-list-nil
   (fn-o1-rows-invp (list nil) fn-arena)
   :hints (("Goal" :in-theory (enable fn-o1-rows-invp fn-cat-history-article fn-row-wire-of fn-hstxa-p
                                      fn-held-p fn-row-composite-okp fn-stxa-p)))))

; The events the four non-article prepares stage are no row: not a record,
; a held row, a composite or a composite row.
(local
 (defthm o1h-event-not-row
   (implies (or (fn-store-retention-event-p e) (fn-cpe-eventp e) (fn-th-topic-eventp e))
            (and (not (fn-held-p e)) (not (fn-hstxa-p e)) (not (fn-stxa-p e)) (not (fn-record-p e))))
   :hints (("Goal" :use ((:instance fn-held-is-no-wire-event (x e))
                         (:instance fn-hstxa-is-no-wire-event (x e))
                         (:instance fn-stxa-is-no-other-wire-event (x e))
                         (:instance fn-record-is-no-other-wire-event (x e)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm o1h-event-invp
   (implies (or (fn-store-retention-event-p e) (fn-cpe-eventp e) (fn-th-topic-eventp e))
            (fn-o1-rows-invp (list e) fn-arena))
   :hints (("Goal" :use o1h-event-not-row
            :in-theory (e/d (fn-o1-rows-invp fn-cat-history-article fn-row-wire-of fn-row-composite-okp
                             fn-rows-composites-okp fn-rows-handles-inp fn-o1-records-filed-or-reclaimedp)
                            (o1h-event-not-row fn-held-p fn-hstxa-p fn-stxa-p fn-record-p
                             fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp))))))

(local
 (defthm o1h-start-frontier-shape
   (and (or (equal (fn-sf-records (fn-sf-start-frontier s)) (fn-sf-records s))
            (equal (fn-sf-records (fn-sf-start-frontier s)) (append (fn-sf-records s) (list (fn-sf-record-candidate s)))))
        (or (equal (fn-sf-record-candidate (fn-sf-start-frontier s)) (fn-sf-record-candidate s))
            (equal (fn-sf-record-candidate (fn-sf-start-frontier s)) nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-sf-start-frontier)))))

(local
 (defthm o1h-frontier-file-result-shape
   (and (or (equal (fn-sf-records (fn-sf-frontier-file-result s result)) (fn-sf-records s))
            (equal (fn-sf-records (fn-sf-frontier-file-result s result)) (append (fn-sf-records s) (list (fn-sf-record-candidate s)))))
        (or (equal (fn-sf-record-candidate (fn-sf-frontier-file-result s result)) (fn-sf-record-candidate s))
            (equal (fn-sf-record-candidate (fn-sf-frontier-file-result s result)) nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-sf-frontier-file-result)))))

(local
 (defthm o1h-frontier-replace-result-shape
   (and (or (equal (fn-sf-records (fn-sf-frontier-replace-result s result)) (fn-sf-records s))
            (equal (fn-sf-records (fn-sf-frontier-replace-result s result)) (append (fn-sf-records s) (list (fn-sf-record-candidate s)))))
        (or (equal (fn-sf-record-candidate (fn-sf-frontier-replace-result s result)) (fn-sf-record-candidate s))
            (equal (fn-sf-record-candidate (fn-sf-frontier-replace-result s result)) nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-sf-frontier-replace-result)))))

(local
 (defthm o1h-frontier-dir-result-shape
   (and (or (equal (fn-sf-records (fn-sf-frontier-dir-result s result)) (fn-sf-records s))
            (equal (fn-sf-records (fn-sf-frontier-dir-result s result)) (append (fn-sf-records s) (list (fn-sf-record-candidate s)))))
        (or (equal (fn-sf-record-candidate (fn-sf-frontier-dir-result s result)) (fn-sf-record-candidate s))
            (equal (fn-sf-record-candidate (fn-sf-frontier-dir-result s result)) nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-sf-frontier-dir-result)))))

(local
 (defthm o1h-record-file-result-shape
   (and (or (equal (fn-sf-records (fn-sf-record-file-result s result)) (fn-sf-records s))
            (equal (fn-sf-records (fn-sf-record-file-result s result)) (append (fn-sf-records s) (list (fn-sf-record-candidate s)))))
        (or (equal (fn-sf-record-candidate (fn-sf-record-file-result s result)) (fn-sf-record-candidate s))
            (equal (fn-sf-record-candidate (fn-sf-record-file-result s result)) nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-sf-record-file-result)))))

(local
 (defthm o1h-record-link-result-shape
   (and (or (equal (fn-sf-records (fn-sf-record-link-result s result)) (fn-sf-records s))
            (equal (fn-sf-records (fn-sf-record-link-result s result)) (append (fn-sf-records s) (list (fn-sf-record-candidate s)))))
        (or (equal (fn-sf-record-candidate (fn-sf-record-link-result s result)) (fn-sf-record-candidate s))
            (equal (fn-sf-record-candidate (fn-sf-record-link-result s result)) nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-sf-record-link-result)))))

(local
 (defthm o1h-record-dir-result-shape
   (and (or (equal (fn-sf-records (fn-sf-record-dir-result s result)) (fn-sf-records s))
            (equal (fn-sf-records (fn-sf-record-dir-result s result)) (append (fn-sf-records s) (list (fn-sf-record-candidate s)))))
        (or (equal (fn-sf-record-candidate (fn-sf-record-dir-result s result)) (fn-sf-record-candidate s))
            (equal (fn-sf-record-candidate (fn-sf-record-dir-result s result)) nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-sf-record-dir-result)))))

(local
 (defthm o1h-recovery-barrier-shape
   (and (or (equal (fn-sf-records (fn-sf-recovery-barrier s result)) (fn-sf-records s))
            (equal (fn-sf-records (fn-sf-recovery-barrier s result)) (append (fn-sf-records s) (list (fn-sf-record-candidate s)))))
        (or (equal (fn-sf-record-candidate (fn-sf-recovery-barrier s result)) (fn-sf-record-candidate s))
            (equal (fn-sf-record-candidate (fn-sf-recovery-barrier s result)) nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-sf-recovery-barrier)))))

(local
 (defthm o1h-core-completion-shape
   (and (or (equal (fn-sf-records (fn-sf-core-completion s sequence txid)) (fn-sf-records s))
            (equal (fn-sf-records (fn-sf-core-completion s sequence txid)) (append (fn-sf-records s) (list (fn-sf-record-candidate s)))))
        (or (equal (fn-sf-record-candidate (fn-sf-core-completion s sequence txid)) (fn-sf-record-candidate s))
            (equal (fn-sf-record-candidate (fn-sf-core-completion s sequence txid)) nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-sf-core-completion)))))

(local
 (defthm o1h-emit-success-shape
   (and (or (equal (fn-sf-records (fn-sf-emit-success s sequence txid)) (fn-sf-records s))
            (equal (fn-sf-records (fn-sf-emit-success s sequence txid)) (append (fn-sf-records s) (list (fn-sf-record-candidate s)))))
        (or (equal (fn-sf-record-candidate (fn-sf-emit-success s sequence txid)) (fn-sf-record-candidate s))
            (equal (fn-sf-record-candidate (fn-sf-emit-success s sequence txid)) nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-sf-emit-success)))))

(local
 (defun o1h-shape (f2 f1)
   (declare (xargs :verify-guards nil))
   (and (or (equal (fn-sf-records f2) (fn-sf-records f1))
            (equal (fn-sf-records f2) (append (fn-sf-records f1) (list (fn-sf-record-candidate f1)))))
        (or (equal (fn-sf-record-candidate f2) (fn-sf-record-candidate f1))
            (equal (fn-sf-record-candidate f2) nil)))))

(local
 (defthm o1h-shape-keeps-inv
   (implies (and (fn-o1-files-invp f1 fn-arena) (o1h-shape f2 f1))
            (fn-o1-files-invp f2 fn-arena))
   :hints (("Goal" :in-theory (e/d (o1h-shape fn-o1-files-invp)
                                   (fn-o1-rows-invp))))
   :rule-classes nil))

(local
 (defthm o1h-prepare-record-shape
   (and (equal (fn-sf-records (fn-sf-prepare-record s record groups capacity)) (fn-sf-records s))
        (or (equal (fn-sf-record-candidate (fn-sf-prepare-record s record groups capacity))
                   (fn-sf-record-candidate s))
            (equal (fn-sf-record-candidate (fn-sf-prepare-record s record groups capacity)) record)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-sf-prepare-record)))))

(local
 (defthm o1h-recover-shape
   (o1h-shape (fn-sf-recover s groups capacity) s)
   :hints (("Goal" :in-theory (enable fn-sf-recover o1h-shape)))))

(local
 (defthm o1h-crash-shape
   (o1h-shape (fn-sf-crash s fc rc) s)
   :hints (("Goal" :in-theory (enable fn-sf-crash o1h-shape)))))

(local
 (defthm o1h-shape-refl (o1h-shape s s) :hints (("Goal" :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-shape-of-start-frontier
   (o1h-shape (fn-sf-start-frontier s) s)
   :hints (("Goal" :use o1h-start-frontier-shape :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-shape-of-frontier-file-result
   (o1h-shape (fn-sf-frontier-file-result s result) s)
   :hints (("Goal" :use o1h-frontier-file-result-shape :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-shape-of-frontier-replace-result
   (o1h-shape (fn-sf-frontier-replace-result s result) s)
   :hints (("Goal" :use o1h-frontier-replace-result-shape :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-shape-of-frontier-dir-result
   (o1h-shape (fn-sf-frontier-dir-result s result) s)
   :hints (("Goal" :use o1h-frontier-dir-result-shape :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-shape-of-record-file-result
   (o1h-shape (fn-sf-record-file-result s result) s)
   :hints (("Goal" :use o1h-record-file-result-shape :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-shape-of-record-link-result
   (o1h-shape (fn-sf-record-link-result s result) s)
   :hints (("Goal" :use o1h-record-link-result-shape :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-shape-of-record-dir-result
   (o1h-shape (fn-sf-record-dir-result s result) s)
   :hints (("Goal" :use o1h-record-dir-result-shape :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-shape-of-recovery-barrier
   (o1h-shape (fn-sf-recovery-barrier s result) s)
   :hints (("Goal" :use o1h-recovery-barrier-shape :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-shape-of-core-completion
   (o1h-shape (fn-sf-core-completion s sequence txid) s)
   :hints (("Goal" :use o1h-core-completion-shape :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-shape-of-emit-success
   (o1h-shape (fn-sf-emit-success s sequence txid) s)
   :hints (("Goal" :use o1h-emit-success-shape :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-file-step-shape
   (o1h-shape (fn-sn-file-step files operation result) files)
   :hints (("Goal" :in-theory (enable fn-sn-file-step)))))

(local
 (defthm o1h-sn-io-shape
   (o1h-shape (fn-sn-files (fn-sn-io s operation result)) (fn-sn-files s))
   :hints (("Goal" :in-theory (enable fn-sn-io)))))

(local
 (defthm o1h-sn-crash-shape
   (o1h-shape (fn-sn-files (fn-sn-crash s fc rc)) (fn-sn-files s))
   :hints (("Goal" :in-theory (enable fn-sn-crash)))))

(local
 (defthm o1h-finish-files-shape
   (o1h-shape (fn-sf-emit-success (fn-sf-core-completion f a b) c d) f)
   :hints (("Goal" :use ((:instance o1h-core-completion-shape (s f) (sequence a) (txid b))
                         (:instance o1h-emit-success-shape (s (fn-sf-core-completion f a b)) (sequence c) (txid d))
                         (:instance fn-sf-records-of-core-completion (s f) (sequence a) (txid b))
                         (:instance fn-sf-records-of-emit-success (s (fn-sf-core-completion f a b)) (sequence c) (txid d)))
            :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-files-of-constructors
   (and (equal (fn-sn-files (fn-sn-update-accepted s f n i m v)) f)
        (equal (fn-sn-files (fn-sn-update-indexed s f n i)) f)
        (equal (fn-sn-files (fn-sn-update s f n)) f)
        (equal (fn-sn-files (fn-sn-update-replayed s f n i c)) f)
        (equal (fn-sn-files (fn-sn-with-event-index s x)) (fn-sn-files s))
        (equal (fn-sn-files (fn-sn-advance-identity-next s)) (fn-sn-files s))
        (equal (fn-sn-files (fn-sn-with-consumer s c)) (fn-sn-files s))
        (equal (fn-sn-files (fn-sn-with-topic s tp)) (fn-sn-files s))
        (equal (fn-sn-files (fn-sn-finish-identity s f r n)) f))
   :hints (("Goal" :in-theory (e/d (fn-sn-update-accepted fn-sn-update-indexed fn-sn-update fn-sn-update-replayed
                                    fn-sn-with-event-index
                                    fn-sn-advance-identity-next fn-sn-with-consumer
                                    fn-sn-with-topic fn-sn-finish-identity fn-sn-make-v6
                                    fn-sn-files)
                                   (fn-replay-identity-step fn-sn-identity-context
                                    fn-stx-index-add fn-sn-composite-delta
                                    fn-replay-verdict-pairs))))))

(local
 (defthm o1h-sn-finish-files
   (equal (fn-sn-files (fn-sn-finish s))
          (if (fn-sn-completion-enabledp s)
              (fn-sf-emit-success
               (fn-sf-core-completion (fn-sn-files s)
                                      (fn-store-event-sequence (fn-sn-completion-record s))
                                      (fn-store-event-txid (fn-sn-completion-record s)))
               (fn-store-event-sequence (fn-sn-completion-record s))
               (fn-store-event-txid (fn-sn-completion-record s)))
            (fn-sn-files s)))
   :hints (("Goal" :in-theory (union-theories '(fn-sn-finish o1h-files-of-constructors)
                                              (theory 'minimal-theory))))))

(local
 (defthm o1h-sn-finish-shape
   (o1h-shape (fn-sn-files (fn-sn-finish s)) (fn-sn-files s))
   :hints (("Goal" :in-theory (disable o1h-shape fn-sn-finish)))))

(local
 (defthm o1h-make-fault-shape
   (implies (o1h-shape files f)
            (o1h-shape (fn-sf-make ph fr nil (fn-sf-records files) nil nil succ 0) f))
   :hints (("Goal" :in-theory (enable o1h-shape)))))

(local
 (defthm o1h-sn-recover-shape
   (o1h-shape (fn-sn-files (fn-sn-recover s)) (fn-sn-files s))
   :hints (("Goal" :in-theory (union-theories '(fn-sn-recover o1h-files-of-constructors o1h-shape-refl
                                                o1h-recover-shape o1h-make-fault-shape)
                                              (theory 'minimal-theory))))))

; Staging a row whose article is filed or reclaimed, or staging nothing, keeps
; the history (the files-level step every prepare, and the intern-then-stage
; of books/filed-lifecycle, is).
(defthm fn-o1-staging-keeps-the-history
  (implies (and (fn-o1-files-invp f1 fn-arena)
                (or (equal f2 f1)
                    (and (fn-o1-rows-invp (list record) fn-arena)
                         (equal f2 (fn-sf-prepare-record f1 record groups capacity)))))
           (fn-o1-files-invp f2 fn-arena))
  :rule-classes nil
  :hints (("Goal" :use ((:instance o1h-prepare-record-shape (s f1)))
           :in-theory (e/d (fn-o1-files-invp) (fn-o1-rows-invp fn-sf-prepare-record)))))

(local
 (defthm o1h-sn-prepare-files
   (let ((f (fn-sn-files (fn-sn-prepare s record))))
     (or (equal f (fn-sn-files s))
         (equal f (fn-sf-prepare-record (fn-sn-files s) record (fn-sn-groups s) (fn-sn-capacity s)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-sn-prepare o1h-files-of-constructors)
                                              (theory 'minimal-theory))))))

(local
 (defthm o1h-sn-prepare-retention-files
   (let ((f (fn-sn-files (fn-sn-prepare-retention s event))))
     (or (equal f (fn-sn-files s))
         (and (fn-store-retention-event-p event)
              (equal f (fn-sf-prepare-record (fn-sn-files s) event (fn-sn-groups s) (fn-sn-capacity s))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-sn-prepare-retention o1h-files-of-constructors)
                                              (theory 'minimal-theory))))))

(local
 (defthm o1h-sn-prepare-identity-files
   (let ((f (fn-sn-files (fn-sn-prepare-identity s event))))
     (or (equal f (fn-sn-files s))
         (equal f (fn-sf-prepare-record (fn-sn-files s) event (fn-sn-groups s) (fn-sn-capacity s)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-sn-prepare-identity o1h-files-of-constructors)
                                              (theory 'minimal-theory))))))

(local
 (defthm o1h-sn-prepare-consumer-files
   (let ((f (fn-sn-files (fn-sn-prepare-consumer s event))))
     (or (equal f (fn-sn-files s))
         (and (fn-cpe-eventp event)
              (equal f (fn-sf-prepare-record (fn-sn-files s) event (fn-sn-groups s) (fn-sn-capacity s))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-sn-prepare-consumer o1h-files-of-constructors)
                                              (theory 'minimal-theory))))))

(local
 (defthm o1h-sn-prepare-topic-files
   (let ((f (fn-sn-files (fn-sn-prepare-topic s event))))
     (or (equal f (fn-sn-files s))
         (and (fn-th-topic-eventp event)
              (equal f (fn-sf-prepare-record (fn-sn-files s) event (fn-sn-groups s) (fn-sn-capacity s))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-sn-prepare-topic o1h-files-of-constructors)
                                              (theory 'minimal-theory))))))

(local
 (in-theory (disable fn-arena-payload-is-nth fn-arena-count-is-len
                     fn-arena-seal-list-is-append fn-arena-p-is-payload-listp
                     fn-arena-get-is-nth fn-arena-payload-len-is-len-nth)))

(local
 (defthm o1h-row-bytes-survives-seal
   (implies (and (fn-arena-p fn-arena) (fn-row-handle-inp h fn-arena))
            (equal (fn-row-bytes h (fn-arena-seal-list xs fn-arena))
                   (fn-row-bytes h fn-arena)))
   :hints (("Goal" :in-theory (enable fn-row-bytes fn-row-handle-inp)))))

(local
 (defthm o1h-row-wire-of-survives-seal
   (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp (list row) fn-arena))
            (equal (fn-row-wire-of row (fn-arena-seal-list xs fn-arena))
                   (fn-row-wire-of row fn-arena)))
   :hints (("Goal" :in-theory (enable fn-row-wire-of fn-rows-handles-inp fn-held-wire-of
                                      fn-row-handle-inp fn-row-bytes)))))

(local
 (defthm o1h-history-article-survives-seal
   (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp (list row) fn-arena))
            (equal (fn-cat-history-article row (fn-arena-seal-list xs fn-arena))
                   (fn-cat-history-article row fn-arena)))
   :hints (("Goal" :in-theory (enable fn-cat-history-article)
            :use ((:instance o1h-row-wire-of-survives-seal (row (fn-hstxa-held row)))
                  (:instance o1h-row-wire-of-survives-seal))))))

(local
 (defthm o1h-history-articles-survive-seal
   (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
            (equal (fn-cat-history-articles rows (fn-arena-seal-list xs fn-arena))
                   (fn-cat-history-articles rows fn-arena)))
   :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
            :in-theory (e/d (fn-rows-handles-inp fn-cat-history-articles)
                            (o1h-history-article-survives-seal)))
           ("Subgoal *1/3" :use ((:instance o1h-history-article-survives-seal (row (car rows)))))
           ("Subgoal *1/2" :use ((:instance o1h-history-article-survives-seal (row (car rows)))))
           ("Subgoal *1/1" :use ((:instance o1h-history-article-survives-seal (row (car rows))))))))

;; sealing more payloads keeps what a row with its handle in the arena reads
(local
 (defthm o1h-handles-survive-seal
   (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
            (fn-rows-handles-inp rows (fn-arena-seal-list xs fn-arena)))
   :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
            :in-theory (enable fn-rows-handles-inp fn-row-handle-inp)))))

(local
 (defthm o1h-row-composite-okp-survives-seal
   (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp (list row) fn-arena))
            (equal (fn-row-composite-okp row (fn-arena-seal-list xs fn-arena))
                   (fn-row-composite-okp row fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-row-composite-okp fn-rows-handles-inp) (fn-row-wire-of))
            :use ((:instance o1h-row-wire-of-survives-seal (row row))
                  (:instance o1h-row-wire-of-survives-seal (row (fn-hstxa-held row))))))))

(local
 (defthm o1h-handles-car-cdr
   (implies (fn-rows-handles-inp rows fn-arena)
            (and (fn-rows-handles-inp (list (car rows)) fn-arena)
                 (fn-rows-handles-inp (cdr rows) fn-arena)))
   :hints (("Goal" :expand ((fn-rows-handles-inp rows fn-arena)
                            (fn-rows-handles-inp (list (car rows)) fn-arena)
                            (fn-rows-handles-inp nil fn-arena))))))

(local
 (defun o1h-ind (rows) (if (atom rows) nil (o1h-ind (cdr rows)))))

(local
 (defthm o1h-composites-survive-seal
   (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
            (equal (fn-rows-composites-okp rows (fn-arena-seal-list xs fn-arena))
                   (fn-rows-composites-okp rows fn-arena)))
   :hints (("Goal" :induct (o1h-ind rows)
            :in-theory (disable fn-row-composite-okp fn-rows-handles-inp fn-arena-seal-list))
           ("Subgoal *1/2" :use ((:instance o1h-row-composite-okp-survives-seal (row (car rows)))
                                 o1h-handles-car-cdr)
            :expand ((fn-rows-composites-okp rows (fn-arena-seal-list xs fn-arena))
                     (fn-rows-composites-okp rows fn-arena))))))

; Sealing more payloads into the arena keeps rows that were invariant in it.
(defthm fn-o1-rows-invp-seal
  (implies (and (fn-arena-p fn-arena) (fn-o1-rows-invp rows fn-arena))
           (fn-o1-rows-invp rows (fn-arena-seal-list xs fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-o1-rows-invp) (fn-arena-seal-list))
           :use (o1h-history-articles-survive-seal o1h-composites-survive-seal o1h-handles-survive-seal))))

; KR1 io: every file step (frontier, record file, link, directory, the
; recovery barrier) keeps the history.
(defthm fn-o1-io-keeps-the-history
  (implies (fn-o1-files-invp (fn-sn-files s) fn-arena)
           (fn-o1-files-invp (fn-sn-files (fn-sn-io s operation result)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use ((:instance o1h-shape-keeps-inv (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-io s operation result)))))
           :in-theory (disable fn-sn-io fn-o1-files-invp o1h-shape))))

; KR2 finish (the completion; fn-sf-core-completion keeps the records).
(defthm fn-o1-finish-keeps-the-history
  (implies (fn-o1-files-invp (fn-sn-files s) fn-arena)
           (fn-o1-files-invp (fn-sn-files (fn-sn-finish s)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use ((:instance o1h-shape-keeps-inv (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-finish s)))))
           :in-theory (disable fn-sn-finish fn-o1-files-invp o1h-shape))))

; KR3 crash, every choice.
(defthm fn-o1-crash-keeps-the-history
  (implies (fn-o1-files-invp (fn-sn-files s) fn-arena)
           (fn-o1-files-invp (fn-sn-files (fn-sn-crash s frontier-choice record-choice)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use ((:instance o1h-shape-keeps-inv (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-crash s frontier-choice record-choice)))))
           :in-theory (disable fn-sn-crash fn-o1-files-invp o1h-shape))))

; KR4 recovery.
(defthm fn-o1-recover-keeps-the-history
  (implies (fn-o1-files-invp (fn-sn-files s) fn-arena)
           (fn-o1-files-invp (fn-sn-files (fn-sn-recover s)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use ((:instance o1h-shape-keeps-inv (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-recover s)))))
           :in-theory (disable fn-sn-recover fn-o1-files-invp o1h-shape))))

; KR5 prepare, each of the five: what is staged is what was prepared.  The
; article and identity entries stage a row the caller supplies, so that row
; is a premise; a retention, consumer or topic event is no row at all
; (o1h-event-invp), so those need none.
(defthm fn-o1-prepare-keeps-the-history
  (implies (and (fn-o1-files-invp (fn-sn-files s) fn-arena)
                (fn-o1-rows-invp (list record) fn-arena))
           (fn-o1-files-invp (fn-sn-files (fn-sn-prepare s record)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use (o1h-sn-prepare-files
                        (:instance fn-o1-staging-keeps-the-history (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-prepare s record)))
                                   (record record) (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s)))))))

(defthm fn-o1-prepare-retention-keeps-the-history
  (implies (fn-o1-files-invp (fn-sn-files s) fn-arena)
           (fn-o1-files-invp (fn-sn-files (fn-sn-prepare-retention s event)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use (o1h-sn-prepare-retention-files
                        (:instance o1h-event-invp (e event))
                        (:instance fn-o1-staging-keeps-the-history (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-prepare-retention s event)))
                                   (record event) (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (disable o1h-event-invp))))

(defthm fn-o1-prepare-identity-keeps-the-history
  (implies (and (fn-o1-files-invp (fn-sn-files s) fn-arena)
                (fn-o1-rows-invp (list event) fn-arena))
           (fn-o1-files-invp (fn-sn-files (fn-sn-prepare-identity s event)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use (o1h-sn-prepare-identity-files
                        (:instance fn-o1-staging-keeps-the-history (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-prepare-identity s event)))
                                   (record event) (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s)))))))

(defthm fn-o1-prepare-consumer-keeps-the-history
  (implies (fn-o1-files-invp (fn-sn-files s) fn-arena)
           (fn-o1-files-invp (fn-sn-files (fn-sn-prepare-consumer s event)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use (o1h-sn-prepare-consumer-files
                        (:instance o1h-event-invp (e event))
                        (:instance fn-o1-staging-keeps-the-history (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-prepare-consumer s event)))
                                   (record event) (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (disable o1h-event-invp))))

(defthm fn-o1-prepare-topic-keeps-the-history
  (implies (fn-o1-files-invp (fn-sn-files s) fn-arena)
           (fn-o1-files-invp (fn-sn-files (fn-sn-prepare-topic s event)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use (o1h-sn-prepare-topic-files
                        (:instance o1h-event-invp (e event))
                        (:instance fn-o1-staging-keeps-the-history (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-prepare-topic s event)))
                                   (record event) (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (disable o1h-event-invp))))

; KR6 the start: the initial Store's files hold no record and no candidate.
(defthm fn-o1-initial-history
  (fn-o1-files-invp (fn-sn-files (fn-sn-initial groups capacity)) fn-arena)
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-o1-files-invp fn-sn-initial fn-sn-make-v2 fn-sn-files fn-sf-initial-state)
                                  ()))))

; KR7 interning: sealing more payloads into the arena keeps what every row
; with handles in the arena reads, so it keeps the history.
(defthm fn-o1-seal-keeps-the-history
  (implies (and (fn-arena-p fn-arena)
                (fn-o1-files-invp files fn-arena))
           (fn-o1-files-invp files (fn-arena-seal-list xs fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-o1-files-invp) (fn-arena-seal-list fn-o1-rows-invp))
           :use ((:instance fn-o1-rows-invp-seal (rows (fn-sf-records files)))
                 (:instance fn-o1-rows-invp-seal (rows (list (fn-sf-record-candidate files))))))))

; K0 reclaim's rewrite: a tombstoned record is reclaimed, whatever its groups.
(defthm fn-o1-tombstoned-record-is-reclaimed
  (fn-o1-records-filed-or-reclaimedp (list (fn-rclp-tombstoned r)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rclp-tombstoned fn-rcl-tombstonep fn-rcl-tombstone-of fn-o1-records-filed-or-reclaimedp)
                                  (fn-asj-subject fn-asj-preimage fn-asj-project fn-blake3 fn-pb-subject fn-pb-path-agent)))))
