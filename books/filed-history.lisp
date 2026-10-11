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

(defun fn-o1-files-filedp (files fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (and (fn-o1-records-filedp (fn-cat-history-articles (fn-sf-records files) fn-arena))
       (fn-o1-records-filedp (fn-cat-history-articles
                              (list (fn-sf-record-candidate files)) fn-arena))))

(local
 (defthm o1h-history-articles-of-append
   (equal (fn-cat-history-articles (append a b) fn-arena)
          (append (fn-cat-history-articles a fn-arena) (fn-cat-history-articles b fn-arena)))))

(local
 (defthm o1h-records-filedp-of-append
   (equal (fn-o1-records-filedp (append a b))
          (and (fn-o1-records-filedp a) (fn-o1-records-filedp b)))
   :hints (("Goal" :induct (fn-o1-records-filedp a)
            :in-theory (disable fn-o1-filed-within-sourcep)))))

(local
 (defthm o1h-history-articles-of-nil-list
   (fn-o1-records-filedp (fn-cat-history-articles (list nil) fn-arena))
   :hints (("Goal" :in-theory (enable fn-cat-history-article fn-row-wire-of fn-hstxa-p fn-held-p)))))

(local
 (defthm o1h-history-articles-of-nil
   (fn-o1-records-filedp (fn-cat-history-articles nil fn-arena))))

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
 (defthm o1h-shape-keeps-filed
   (implies (and (fn-o1-files-filedp f1 fn-arena) (o1h-shape f2 f1))
            (fn-o1-files-filedp f2 fn-arena))
   :hints (("Goal" :in-theory (e/d (o1h-shape fn-o1-files-filedp) (fn-o1-records-filedp fn-cat-history-articles))))
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

(local
 (defthm o1h-prepared-keeps-filed
   (implies (and (fn-o1-files-filedp f1 fn-arena)
                 (fn-o1-records-filedp (fn-cat-history-articles (list record) fn-arena))
                 (or (equal f2 f1)
                     (equal f2 (fn-sf-prepare-record f1 record groups capacity))))
            (fn-o1-files-filedp f2 fn-arena))
   :hints (("Goal" :use ((:instance o1h-prepare-record-shape (s f1)))
            :in-theory (e/d (fn-o1-files-filedp) (fn-o1-records-filedp fn-cat-history-articles fn-sf-prepare-record))))))

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
         (equal f (fn-sf-prepare-record (fn-sn-files s) event (fn-sn-groups s) (fn-sn-capacity s)))))
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
         (equal f (fn-sf-prepare-record (fn-sn-files s) event (fn-sn-groups s) (fn-sn-capacity s)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-sn-prepare-consumer o1h-files-of-constructors)
                                              (theory 'minimal-theory))))))

(local
 (defthm o1h-sn-prepare-topic-files
   (let ((f (fn-sn-files (fn-sn-prepare-topic s event))))
     (or (equal f (fn-sn-files s))
         (equal f (fn-sf-prepare-record (fn-sn-files s) event (fn-sn-groups s) (fn-sn-capacity s)))))
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

; P4-R1 io: every file step (frontier, record file, link, directory, the
; recovery barrier) keeps the files filed.
(defthm fn-o1-io-keeps-the-files-filed
  (implies (fn-o1-files-filedp (fn-sn-files s) fn-arena)
           (fn-o1-files-filedp (fn-sn-files (fn-sn-io s operation result)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use ((:instance o1h-shape-keeps-filed (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-io s operation result)))))
           :in-theory (disable fn-sn-io fn-o1-files-filedp o1h-shape))))

; P4-R2 finish (the completion; fn-sf-core-completion keeps the records).
(defthm fn-o1-finish-keeps-the-files-filed
  (implies (fn-o1-files-filedp (fn-sn-files s) fn-arena)
           (fn-o1-files-filedp (fn-sn-files (fn-sn-finish s)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use ((:instance o1h-shape-keeps-filed (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-finish s)))))
           :in-theory (disable fn-sn-finish fn-o1-files-filedp o1h-shape))))

; P4-R3 crash, every choice.
(defthm fn-o1-crash-keeps-the-files-filed
  (implies (fn-o1-files-filedp (fn-sn-files s) fn-arena)
           (fn-o1-files-filedp (fn-sn-files (fn-sn-crash s frontier-choice record-choice)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use ((:instance o1h-shape-keeps-filed (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-crash s frontier-choice record-choice)))))
           :in-theory (disable fn-sn-crash fn-o1-files-filedp o1h-shape))))

; P4-R4 recovery.
(defthm fn-o1-recover-keeps-the-files-filed
  (implies (fn-o1-files-filedp (fn-sn-files s) fn-arena)
           (fn-o1-files-filedp (fn-sn-files (fn-sn-recover s)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use ((:instance o1h-shape-keeps-filed (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-recover s)))))
           :in-theory (disable fn-sn-recover fn-o1-files-filedp o1h-shape))))

; P4-R5 prepare, each of the five: what is staged is what was prepared.
(defthm fn-o1-prepare-keeps-the-files-filed
  (implies (and (fn-o1-files-filedp (fn-sn-files s) fn-arena)
                (fn-o1-records-filedp (fn-cat-history-articles (list record) fn-arena)))
           (fn-o1-files-filedp (fn-sn-files (fn-sn-prepare s record)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use (o1h-sn-prepare-files
                        (:instance o1h-prepared-keeps-filed (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-prepare s record)))
                                   (record record) (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (disable o1h-prepared-keeps-filed))))

(defthm fn-o1-prepare-retention-keeps-the-files-filed
  (implies (and (fn-o1-files-filedp (fn-sn-files s) fn-arena)
                (fn-o1-records-filedp (fn-cat-history-articles (list event) fn-arena)))
           (fn-o1-files-filedp (fn-sn-files (fn-sn-prepare-retention s event)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use (o1h-sn-prepare-retention-files
                        (:instance o1h-prepared-keeps-filed (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-prepare-retention s event)))
                                   (record event) (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (disable o1h-prepared-keeps-filed))))

(defthm fn-o1-prepare-identity-keeps-the-files-filed
  (implies (and (fn-o1-files-filedp (fn-sn-files s) fn-arena)
                (fn-o1-records-filedp (fn-cat-history-articles (list event) fn-arena)))
           (fn-o1-files-filedp (fn-sn-files (fn-sn-prepare-identity s event)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use (o1h-sn-prepare-identity-files
                        (:instance o1h-prepared-keeps-filed (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-prepare-identity s event)))
                                   (record event) (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (disable o1h-prepared-keeps-filed))))

(defthm fn-o1-prepare-consumer-keeps-the-files-filed
  (implies (and (fn-o1-files-filedp (fn-sn-files s) fn-arena)
                (fn-o1-records-filedp (fn-cat-history-articles (list event) fn-arena)))
           (fn-o1-files-filedp (fn-sn-files (fn-sn-prepare-consumer s event)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use (o1h-sn-prepare-consumer-files
                        (:instance o1h-prepared-keeps-filed (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-prepare-consumer s event)))
                                   (record event) (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (disable o1h-prepared-keeps-filed))))

(defthm fn-o1-prepare-topic-keeps-the-files-filed
  (implies (and (fn-o1-files-filedp (fn-sn-files s) fn-arena)
                (fn-o1-records-filedp (fn-cat-history-articles (list event) fn-arena)))
           (fn-o1-files-filedp (fn-sn-files (fn-sn-prepare-topic s event)) fn-arena))
  :rule-classes nil
  :hints (("Goal" :use (o1h-sn-prepare-topic-files
                        (:instance o1h-prepared-keeps-filed (f1 (fn-sn-files s))
                                   (f2 (fn-sn-files (fn-sn-prepare-topic s event)))
                                   (record event) (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (disable o1h-prepared-keeps-filed))))

; P4-R0 the start: the initial Store's files are filed.
(defthm fn-o1-initial-files-are-filed
  (fn-o1-files-filedp (fn-sn-files (fn-sn-initial groups capacity)) fn-arena)
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-o1-files-filedp fn-sn-initial fn-sn-make-v2 fn-sn-files fn-sf-initial-state)
                                  ()))))

; P4-R6 interning: sealing more payloads into the arena keeps what every row
; with handles in the arena reads, so it keeps the files filed.
(defthm fn-o1-seal-keeps-the-files-filed
  (implies (and (fn-arena-p fn-arena)
                (fn-rows-handles-inp (fn-sf-records files) fn-arena)
                (fn-rows-handles-inp (list (fn-sf-record-candidate files)) fn-arena)
                (fn-o1-files-filedp files fn-arena))
           (fn-o1-files-filedp files (fn-arena-seal-list xs fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-o1-files-filedp) (fn-arena-seal-list fn-o1-records-filedp))
           :use ((:instance o1h-history-articles-survive-seal (rows (fn-sf-records files)))
                 (:instance o1h-history-articles-survive-seal (rows (list (fn-sf-record-candidate files))))))))
