; fn: the one resumable checkpoint pipeline: the schema-3 tables
; (books/store-checkpoint-tables.lisp) written in bounded batches through
; the publication buffer, decided before anything is allocated (lane
; checkpoint-pipeline, 2026-09-26; D33; design section 2.2).
;
; Before this book the owner's automatic publication and the verb each
; encoded the WHOLE frozen checkpoint into the publication buffer before the
; first write (`fn-sccb-plan': 315 MB resident at N = 40,000), after a walk
; of every payload octet for the estimate (`fn-ockb-file-len', 54 s at
; N = 40,000 and linear in the payload).  This book replaces both with one
; pipeline the owner's thread and the verb run alike:
;
;   capture (under the mutex, host/owner-host.lisp fn-owner-sco-capture: the
;     base, the configuration history, the record list by pointer, S, the
;     budget, the free space)
;   -> `fn-ockp-estimate' (off the mutex): the file's length from the tables'
;      rows without encoding them: a walk over the METADATA (a payload leaf
;      costs its length, never a copy; a referenced payload costs its
;      reference), equal to the length of the file the pipeline writes
;      (`fn-ockp-estimate-is-len-file-octets')
;   -> `fn-ockp-decide': the deferral by name BEFORE any allocation, against
;      the profile's checkpoint budget (`fn-ock-capture-budget', the reader's
;      file bound, STO-024) and the space (the free octets the host observed
;      by statvfs less the maintenance reserve `fn-smr-reserve-octets')
;   -> `fn-ockp-batch' (the resumable step): the next B rows of the current
;      table encoded into the buffer after the residue the last step left,
;      the full SEG-octet chunks framed and chained, the residue (under SEG
;      octets) kept for the next step; at a table's end its last chunk; then
;      the next table.  The buffer holds at most one batch's rows and one
;      segment's residue, never the file.  Each frame is admitted by the
;      reader's own rule (`fn-sccr-admit-segment') before it is handed to
;      the host: a file the open would refuse is never completed.
;
; The host (host/native/owner.lisp `fnn-owner-publish-captured';
; host/native/io.lisp `fnn-command-state-checkpoint') loops on
; `fn-ockp-batch' and writes each step's frames through `fnn-write-staged-at'
; between the `created' and `written' cuts of `fn-bs-scp-program' (its
; :write-all is the loop of writes), then renames and fences as before.
; `fn-ockp-run' is that loop in the logic, its result the file's octets.
;
; KEYSTONE `fn-ockp-run-writes-the-file' (PRF-199 with the tables book's
; `fn-sct-decode-file-of-file-is-the-capture'): the octets the batched
; pipeline writes, at ANY batch size and any segment size, are
; `fn-sct-file-octets' of the tables' programs, whose reader gives the
; tables and the capture.  PRF-200 `fn-ockp-decide-defers-by-the-estimate':
; the pipeline defers exactly when the file it would write exceeds the
; budget or the space, naming the file's length and the bound, else it
; answers the plan.

(in-package "ACL2")
(include-book "store-checkpoint-tables")
(include-book "store-checkpoint-buffer")
(include-book "store-checkpoint-reader")
(include-book "store-maintenance-reserve")
(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-ockp-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-ockp-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; -----------------------------------------------------------------------------
; The publication buffer: the second abstract stobj congruent to
; `fn-octets' (owner-checkpoint-stream, moved here; the stream book goes).

(defabsstobj fn-octets-pub
  :foundation fn-octets$c
  :recognizer (fn-octets-pub-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-octets-pub :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-octets-pub-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-octets-pub-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-octets-pub-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-octets-pub-append-octet :logic fn-octets$a-append-octet
                                        :exec fn-octets$c-append-octet :protect t)
            (fn-octets-pub-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-octets-pub-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                   :protect t)
            (fn-octets-pub-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-octets-pub-from-list :logic fn-octets$a-from-list
                                     :exec fn-octets$c-from-list :protect t)
            (fn-octets-pub-append-list :logic fn-octets$a-append-list
                                       :exec fn-oct-write-list :protect t))
  :congruent-to fn-octets)

; -----------------------------------------------------------------------------
; The budget (STO-024, kept): the file bound the open refuses a checkpoint
; past, and the blocked rule of a recorded deferral, now for both reasons.

(defun fn-ock-capture-budget (profile)
  (declare (xargs :guard t))
  (fn-sccr-file-read-bound (fn-bs-profile-max-history-octets profile)
                           (fn-bs-profile-max-record-octets profile)))

(defthm fn-ock-capture-budget-natp
  (natp (fn-ock-capture-budget profile))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-sccr-file-read-bound fn-scc-segment-max-octets)
                                  (fn-bs-profile-max-history-octets
                                   fn-bs-profile-max-record-octets)))))

; The space the staged file may take: the free octets the host observed
; less the maintenance reserve (nil when the host could not observe).
(defun fn-ockp-space (free)
  (declare (xargs :guard t))
  (if (natp free) (nfix (- free (fn-smr-reserve-octets))) nil))

; A recorded deferral (:deferred REASON ESTIMATE BOUND) blocks the next
; attempt while the bound it named (the budget for :exceeds-budget, the
; space for :exceeds-space) is still below its estimate.
(defun fn-ock-publication-blockedp (deferred budget space)
  (declare (xargs :guard t))
  (and (consp deferred) (eq (car deferred) :deferred)
       (consp (cdr deferred)) (consp (cddr deferred))
       (natp (caddr deferred))
       (if (eq (cadr deferred) :exceeds-space)
           (or (not (natp space)) (< space (caddr deferred)))
         (< (nfix budget) (caddr deferred)))))

; -----------------------------------------------------------------------------
; The estimate: the length of a row's program, of a table's run, of the
; file, by a walk that allocates nothing (a payload leaf costs its length,
; a reference its few octets), equal to the length of what is written.

(defun fn-ockp-len-acc (x cand mtrie n table k acc)
  (declare (xargs :guard (and (natp k) (natp acc)) :measure (acl2-count x)
                  :verify-guards nil))
  (cond ((and cand (fn-sct-refp x cand n table))
         (+ acc 1 (len (fn-scc-nat-octets cand)) (nfix k)))
        ((fn-scc-octets-valuep x)
         (+ acc 1 (len (fn-scc-nat-octets (len x))) (len x) (nfix k)))
        ((consp x)
         (let ((c (let ((c2 (fn-sct-candidate x mtrie n table))) (if c2 c2 cand))))
           (fn-ockp-len-acc (cdr x) c mtrie n table (+ 1 (nfix k))
                            (fn-ockp-len-acc (car x) c mtrie n table 0 acc))))
        ((fn-scc-atomp x) (+ acc (len (fn-scc-atom-octets x)) (nfix k)))
        (t (+ acc (nfix k)))))

(defthm fn-ockp-len-acc-natp
  (implies (natp acc) (natp (fn-ockp-len-acc x cand mtrie n table k acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-ockp-len-acc x cand mtrie n table k acc)
           :in-theory (disable fn-sct-refp fn-sct-candidate fn-scc-octets-valuep
                               fn-scc-atomp fn-scc-atom-octets fn-scc-nat-octets))))

(verify-guards fn-ockp-len-acc
  :hints (("Goal" :in-theory (enable fn-sct-refp))))

(local
 (defthm fn-ockp-len-repeat
   (equal (len (fn-scc-repeat n v)) (nfix n))
   :hints (("Goal" :in-theory (enable fn-scc-repeat)))))

(local
 (defthm fn-ockp-len-program-of-octets
   (implies (fn-scc-octets-valuep x)
            (equal (len (fn-scc-program x))
                   (+ 1 (len (fn-scc-nat-octets (len x))) (len x))))
   :hints (("Goal" :expand ((fn-scc-program x))
            :in-theory (disable fn-scc-nat-octets)))))

(defthm fn-ockp-len-acc-is-len-program
  (implies (fn-scc-treep x)
           (equal (fn-ockp-len-acc x cand mtrie n table k acc)
                  (+ (fix acc) (nfix k) (len (fn-sct-program x cand mtrie n table)))))
  :hints (("Goal" :induct (fn-ockp-len-acc x cand mtrie n table k acc)
           :in-theory (e/d (fn-sct-program)
                           (fn-scc-atom-octets fn-scc-nat-octets fn-sct-refp fn-scc-atomp
                            fn-sct-candidate fn-scc-octets-valuep fn-scc-program)))))

(defun fn-ockp-rows-len (rows i selfp mtrie n table acc)
  (declare (xargs :guard (and (natp i) (natp acc))))
  (if (consp rows)
      (fn-ockp-rows-len (cdr rows) (+ 1 i) selfp mtrie n table
                        (fn-ockp-len-acc (car rows) (if selfp i nil) mtrie n table 0 acc))
    acc))

(defthm fn-ockp-rows-len-is-len-rows-program
  (implies (and (natp acc) (fn-sct-rows-treep rows))
           (equal (fn-ockp-rows-len rows i selfp mtrie n table acc)
                  (+ acc (len (fn-sct-rows-program rows i selfp mtrie n table)))))
  :hints (("Goal" :induct (fn-ockp-rows-len rows i selfp mtrie n table acc)
           :in-theory (e/d (fn-sct-rows-program fn-sct-rows-treep)
                           (fn-sct-program fn-ockp-len-acc)))))

(defthm fn-ockp-rows-len-natp
  (implies (natp acc) (natp (fn-ockp-rows-len rows i selfp mtrie n table acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-ockp-rows-len rows i selfp mtrie n table acc)
           :in-theory (e/d (fn-ockp-rows-len) (fn-ockp-len-acc)))))

(in-theory (disable fn-ockp-len-acc fn-ockp-rows-len))

; One header and one trailer per segment.
(defconst *fn-ockp-frame-octets*
  (+ *fn-scc-segment-header-octets* *fn-frame-trailer-octets*))

; A run's length: its program and its frames.
(defun fn-ockp-run-len (l seg)
  (declare (xargs :guard (and (natp l) (natp seg))))
  (+ l (* (fn-sccb-chunk-count l seg) *fn-ockp-frame-octets*)))

; The frames' lengths, from the codec's shape (owner-checkpoint-stream's
; local lemmas, moved).
(local
 (defthm fn-ockp-octet-listp-append
   (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
            (fn-scc-octet-listp (append a b)))))

(local
 (defthm fn-ockp-header-shape
   (and (fn-scc-octet-listp (fn-scc-header index count length sequence))
        (equal (len (fn-scc-header index count length sequence))
               *fn-scc-segment-header-octets*))
   :hints (("Goal" :in-theory (enable fn-scc-header)))))

(local
 (defthm fn-ockp-seal-is-digest
   (implies (and (fn-scc-octet-listp prev) (fn-scc-octet-listp header)
                 (fn-scc-octet-listp chunk))
            (and (fn-scc-octet-listp (fn-scc-seal prev header chunk))
                 (equal (len (fn-scc-seal prev header chunk)) *fn-frame-trailer-octets*)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-frame-trailer-is-a-digest
                             (octets (append prev header chunk))))
            :in-theory (e/d (fn-scc-seal fn-frame-digestp)
                            (fn-frame-trailer-is-a-digest))))))

(defun fn-ockp-sum-len (chunks)
  (declare (xargs :guard t))
  (if (consp chunks) (+ (len (car chunks)) (fn-ockp-sum-len (cdr chunks))) 0))

(defun fn-ockp-octet-list-listp (chunks)
  (declare (xargs :guard t))
  (if (consp chunks)
      (and (fn-scc-octet-listp (car chunks)) (fn-ockp-octet-list-listp (cdr chunks)))
    t))

(local
 (defthm fn-ockp-len-true-list-fix
   (equal (len (true-list-fix x)) (len x))))

(local
 (defthm fn-ockp-concat-of-frames-len
   (implies (and (fn-scc-octet-listp prev) (fn-ockp-octet-list-listp chunks))
            (equal (len (fn-scc-concat (fn-scc-frames chunks index count sequence prev)))
                   (+ (fn-ockp-sum-len chunks)
                      (* *fn-ockp-frame-octets* (len chunks)))))
   :hints (("Goal" :induct (fn-scc-frames chunks index count sequence prev)
            :in-theory (e/d () (fn-scc-header fn-scc-seal))))))

(local
 (defthm fn-ockp-long-enoughp-is-len
   (implies (natp n)
            (equal (fn-scc-long-enoughp n xs) (<= n (len xs))))))

(local
 (defthm fn-ockp-octet-listp-take
   (implies (and (fn-scc-octet-listp p) (natp k) (<= k (len p)))
            (fn-scc-octet-listp (take k p)))))

(local
 (defthm fn-ockp-octet-listp-nthcdr
   (implies (fn-scc-octet-listp p)
            (fn-scc-octet-listp (nthcdr k p)))))

(local
 (defthm fn-ockp-len-take
   (equal (len (take k x)) (nfix k))))

(local
 (defthm fn-ockp-len-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (len (nthcdr n xs)) (- (len xs) n)))))

(local
 (defthm fn-ockp-chunks-octet-lists
   (implies (fn-scc-octet-listp p)
            (fn-ockp-octet-list-listp (fn-scc-chunks p seg)))
   :hints (("Goal" :induct (fn-scc-chunks p seg)))))

(local
 (defthm fn-ockp-sum-len-of-chunks
   (implies (true-listp p)
            (equal (fn-ockp-sum-len (fn-scc-chunks p seg)) (len p)))
   :hints (("Goal" :induct (fn-scc-chunks p seg)))))

(local
 (defthm fn-ockp-genesis-octets
   (fn-scc-octet-listp *fn-scc-genesis*)))

; A run's octets have the run's length.
(defthm fn-ockp-run-len-is-len-run
  (implies (fn-scc-octet-listp prog)
           (equal (len (fn-scc-concat (fn-sct-run-segments prog seg s)))
                  (fn-ockp-run-len (len prog) seg)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccb-chunk-count-is-len-chunks (p prog))
                 (:instance fn-ockp-concat-of-frames-len
                            (chunks (fn-scc-chunks prog seg)) (index 0)
                            (count (len (fn-scc-chunks prog seg))) (sequence s)
                            (prev *fn-scc-genesis*)))
           :in-theory (e/d (fn-sct-run-segments)
                           (fn-scc-frames fn-scc-chunks fn-scc-concat fn-sccb-chunk-count
                            fn-sccb-chunk-count-is-len-chunks fn-ockp-concat-of-frames-len)))))

; The file's length from the tables' rows: the four runs.
(defun fn-ockp-estimate (tables index seg)
  (declare (xargs :guard (and (fn-sct-tables-treep tables) (natp seg))
                  :guard-hints (("Goal" :in-theory (enable fn-sct-tables-treep)))))
  (let ((n (len (fn-sct-tables-e tables))))
    (+ (fn-ockp-run-len (fn-ockp-rows-len (list (fn-sct-tables-f tables)) 0 nil nil n nil 0) seg)
       (fn-ockp-run-len (fn-ockp-rows-len (fn-sct-tables-p tables) 0 nil nil n nil 0) seg)
       (fn-ockp-run-len (fn-ockp-rows-len (fn-sct-tables-e tables) 0 t nil n index 0) seg)
       (fn-ockp-run-len (fn-ockp-rows-len (fn-sct-tables-r tables) 0 nil
                                          (fn-cei-msgid-trie index) n index 0)
                        seg))))

(defthm fn-ockp-estimate-natp
  (natp (fn-ockp-estimate tables index seg))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable fn-sccb-chunk-count fn-cei-msgid-trie
                                      fn-sct-tables-f fn-sct-tables-p fn-sct-tables-e
                                      fn-sct-tables-r))))

(local
 (defthm fn-ockp-concat-append
   (equal (fn-scc-concat (append a b))
          (append (fn-scc-concat a) (fn-scc-concat b)))))

; Encodability: every row's octets octets (`fn-sccb-treep', the buffer
; codec's honest recognizer: a leaf whose length needs 256 digits is
; refused, never written as a non-octet).
(defun fn-ockp-rows-encodablep (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (fn-sccb-treep (car rows)) (fn-ockp-rows-encodablep (cdr rows)))
    (null rows)))

(defun fn-ockp-tables-encodablep (tables)
  (declare (xargs :guard t))
  (and (true-listp tables) (equal (len tables) 4)
       (fn-sccb-treep (fn-sct-tables-f tables))
       (fn-ockp-rows-encodablep (fn-sct-tables-p tables))
       (fn-ockp-rows-encodablep (fn-sct-tables-e tables))
       (fn-ockp-rows-encodablep (fn-sct-tables-r tables))))

(defthm fn-ockp-rows-encodablep-treep
  (implies (fn-ockp-rows-encodablep rows) (fn-sct-rows-treep rows))
  :hints (("Goal" :in-theory (enable fn-sct-rows-treep))))

(defthm fn-ockp-tables-encodablep-treep
  (implies (fn-ockp-tables-encodablep tables) (fn-sct-tables-treep tables))
  :hints (("Goal" :in-theory (enable fn-sct-tables-treep))))

(local
 (defthm fn-ockp-nat-octets-octets-when-encodable
   (implies (fn-scc-nat-encodablep n)
            (fn-scc-octet-listp (fn-scc-nat-octets n)))
   :hints (("Goal" :in-theory (enable fn-scc-nat-octets fn-scc-nat-encodablep)))))

(local
 (defthm fn-ockp-program-leaf-octets
   (implies (and (fn-scc-octets-valuep x)
                 (fn-scc-octet-listp (fn-scc-nat-octets (len x))))
            (fn-scc-octet-listp (fn-scc-program x)))
   :hints (("Goal" :use ((:instance fn-sccb-treep-encodes-octets))
            :expand ((fn-sccb-treep x))
            :in-theory (disable fn-sccb-treep-encodes-octets fn-scc-program
                                fn-scc-nat-octets fn-scc-octets-valuep fn-scc-octet-listp)))))

(defthm fn-ockp-program-octets
  (implies (fn-sccb-treep x)
           (fn-scc-octet-listp (fn-sct-program x cand mtrie n table)))
  :hints (("Goal" :induct (fn-sct-program x cand mtrie n table)
           :in-theory (e/d (fn-sct-program fn-sct-refp fn-sccb-treep)
                           (fn-scc-atom-octets fn-scc-nat-octets fn-sct-candidate
                            fn-scc-octets-valuep fn-scc-program fn-scc-treep
                            fn-scc-atomp fn-sccb-treep-is-treep
                            fn-sccb-treep-encodes-octets)))))

(defthm fn-ockp-rows-program-octets
  (implies (fn-ockp-rows-encodablep rows)
           (fn-scc-octet-listp (fn-sct-rows-program rows i selfp mtrie n table)))
  :hints (("Goal" :induct (fn-sct-rows-program rows i selfp mtrie n table)
           :in-theory (e/d (fn-sct-rows-program) (fn-sct-program)))))

; The estimate is the length of the file the pipeline writes for the
; tables, for every table set the codec encodes.
(defthm fn-ockp-estimate-is-len-file-octets
  (implies (fn-ockp-tables-encodablep tables)
           (equal (len (fn-sct-file-octets (fn-sct-table-programs tables index) seg s))
                  (fn-ockp-estimate tables index seg)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sct-file-octets fn-sct-file-segments fn-sct-table-programs
                            fn-sct-tables-treep)
                           (fn-sct-run-segments fn-ockp-run-len fn-scc-concat
                            fn-sct-rows-program fn-sccb-chunk-count)))))

(in-theory (disable fn-ockp-run-len fn-ockp-estimate))

; -----------------------------------------------------------------------------
; The decision, before any allocation.  (:deferred :exceeds-budget ESTIMATE
; BUDGET), (:deferred :exceeds-space ESTIMATE SPACE), or (:plan ESTIMATE).

(defun fn-ockp-decide (estimate budget free)
  (declare (xargs :guard (and (natp estimate) (natp budget))))
  (let ((space (fn-ockp-space free)))
    (cond ((< budget estimate) (list :deferred :exceeds-budget estimate budget))
          ((or (not (natp space)) (< space estimate))
           (list :deferred :exceeds-space estimate (nfix space)))
          (t (list :plan estimate)))))

; PRF-200.  The decision defers exactly when the estimate exceeds the
; budget or the space, naming the estimate and the bound it exceeds, and
; otherwise answers the plan; and the deferral it records blocks a later
; attempt exactly while that bound is below the estimate.
(defthm fn-ockp-decide-defers-by-the-estimate
  (implies (and (natp estimate) (natp budget))
           (let ((verdict (fn-ockp-decide estimate budget free)))
             (and (iff (equal (car verdict) :deferred)
                       (or (< budget estimate)
                           (not (natp (fn-ockp-space free)))
                           (< (fn-ockp-space free) estimate)))
                  (implies (< budget estimate)
                           (equal verdict (list :deferred :exceeds-budget estimate budget)))
                  (implies (and (not (< budget estimate))
                                (natp (fn-ockp-space free))
                                (< (fn-ockp-space free) estimate))
                           (equal verdict
                                  (list :deferred :exceeds-space estimate (fn-ockp-space free))))
                  (implies (not (equal (car verdict) :deferred))
                           (equal verdict (list :plan estimate)))
                  (implies (< budget estimate)
                           (iff (fn-ock-publication-blockedp verdict later-budget later-space)
                                (< (nfix later-budget) estimate)))
                  (implies (and (not (< budget estimate))
                                (natp (fn-ockp-space free))
                                (< (fn-ockp-space free) estimate))
                           (iff (fn-ock-publication-blockedp verdict later-budget later-space)
                                (or (not (natp later-space)) (< later-space estimate))))))))

(in-theory (disable fn-ockp-decide fn-ock-publication-blockedp fn-ockp-space))

; -----------------------------------------------------------------------------
; The writer: a row's program written forward into the buffer (the tables
; codec's `fn-sct-program' as `fn-sccb-renc' writes `fn-scc-program').

(defun fn-sct-renc (x cand mtrie n table k fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-sccb-treep x) (natp k))
                  :measure (acl2-count x)
                  :verify-guards nil))
  (cond ((and cand (fn-sct-refp x cand n table))
         (let* ((fn-octets (fn-octets-append-octet *fn-sct-op-ref* fn-octets))
                (fn-octets (fn-sccb-append-list (fn-scc-nat-octets cand) fn-octets)))
           (fn-sccb-cons-ops k fn-octets)))
        ((fn-scc-octets-valuep x)
         (let* ((fn-octets (fn-octets-append-octet *fn-scc-op-octets* fn-octets))
                (fn-octets (fn-sccb-append-list (fn-scc-nat-octets (len x)) fn-octets))
                (fn-octets (fn-sccb-append-list x fn-octets)))
           (fn-sccb-cons-ops k fn-octets)))
        ((consp x)
         (let* ((c (let ((c2 (fn-sct-candidate x mtrie n table))) (if c2 c2 cand)))
                (fn-octets (fn-sct-renc (car x) c mtrie n table 0 fn-octets)))
           (fn-sct-renc (cdr x) c mtrie n table (+ 1 (nfix k)) fn-octets)))
        (t
         (let ((fn-octets (fn-sccb-append-list (fn-scc-atom-octets x) fn-octets)))
           (fn-sccb-cons-ops k fn-octets)))))

(local
 (defthm fn-ockp-atom-octets-true-listp
   (true-listp (fn-scc-atom-octets x))
   :hints (("Goal" :in-theory (enable fn-scc-atom-octets fn-scc-nat-octets
                                      fn-scc-string-octets)))))

(local
 (defthm fn-ockp-snoc-is-append
   (equal (fn-oct-snoc xs o) (append xs (list o)))
   :hints (("Goal" :in-theory (enable fn-oct-snoc)))))

(local
 (defthm fn-ockp-true-listp-append
   (implies (true-listp b) (true-listp (append a b)))))

(local
 (defthm fn-ockp-program-true-listp
   (true-listp (fn-sct-program x cand mtrie n table))))

(local
 (defthm fn-ockp-repeat-true-listp
   (true-listp (fn-scc-repeat n v))
   :hints (("Goal" :in-theory (enable fn-scc-repeat)))))

(defthm fn-sct-renc-is-program
  (implies (true-listp fn-octets)
           (equal (fn-sct-renc x cand mtrie n table k fn-octets)
                  (append fn-octets (fn-sct-program x cand mtrie n table)
                          (fn-scc-repeat (nfix k) *fn-scc-op-cons*))))
  :hints (("Goal" :induct (fn-sct-renc x cand mtrie n table k fn-octets)
           :in-theory (e/d (fn-sct-program fn-scc-repeat fn-sccb-append-list-is-append
                            fn-sccb-cons-ops-is-append-repeat)
                           (fn-scc-atom-octets fn-scc-nat-octets fn-scc-le-digits
                            fn-scc-string-octets fn-scc-atomp fn-scc-treep
                            fn-scc-octet-listp fn-sct-refp fn-sct-candidate
                            fn-scc-program)))
          ("Subgoal *1/2" :in-theory (e/d (fn-sct-program fn-scc-program fn-scc-repeat
                                           fn-sccb-append-list-is-append
                                           fn-sccb-cons-ops-is-append-repeat)
                                          (fn-scc-atom-octets fn-scc-nat-octets fn-scc-le-digits
                                           fn-scc-string-octets fn-scc-atomp fn-scc-treep
                                           fn-scc-octet-listp fn-sct-refp fn-sct-candidate)))))

(verify-guards fn-sct-renc
  :hints (("Goal" :expand ((fn-sccb-treep x))
           :in-theory (e/d (fn-sct-refp fn-sccb-scc-octetp-is-cbor-octetp)
                           (fn-scc-atom-octets fn-scc-nat-octets fn-sct-candidate
                            fn-scc-treep fn-sccb-treep fn-scc-octets-valuep fn-sct-renc
                            fn-sccb-treep-is-treep)))))

; The rows of a batch: at most B rows from REST, row i with candidate i
; when SELFP.  (mv REST' I' fn-octets)
(defun fn-ockp-encode-batch (rest i b selfp mtrie n table fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-ockp-rows-encodablep rest) (natp i) (natp b))))
  (if (or (zp b) (not (consp rest)))
      (mv rest i fn-octets)
    (let ((fn-octets (fn-sct-renc (car rest) (if selfp i nil) mtrie n table 0 fn-octets)))
      (fn-ockp-encode-batch (cdr rest) (+ 1 i) (1- b) selfp mtrie n table fn-octets))))

; The first B rows, and the rest, as lists.
(defun fn-ockp-take (b rows)
  (declare (xargs :guard (natp b)))
  (if (or (zp b) (not (consp rows))) nil (cons (car rows) (fn-ockp-take (1- b) (cdr rows)))))

(defun fn-ockp-drop (b rows)
  (declare (xargs :guard (natp b)))
  (if (or (zp b) (not (consp rows))) rows (fn-ockp-drop (1- b) (cdr rows))))

(defthm fn-ockp-encode-batch-is-rows-program
  (implies (and (true-listp fn-octets) (natp i))
           (equal (fn-ockp-encode-batch rest i b selfp mtrie n table fn-octets)
                  (mv (fn-ockp-drop b rest) (+ (nfix i) (len (fn-ockp-take b rest)))
                      (append fn-octets
                              (fn-sct-rows-program (fn-ockp-take b rest) i selfp mtrie n table)))))
  :hints (("Goal" :induct (fn-ockp-encode-batch rest i b selfp mtrie n table fn-octets)
           :in-theory (e/d (fn-sct-rows-program fn-scc-repeat)
                           (fn-sct-program fn-sct-renc)))))

(in-theory (disable fn-sct-renc fn-ockp-encode-batch))

; -----------------------------------------------------------------------------
; The cut: the buffer's full SEG-octet chunks from A, framed and chained;
; what is left (under SEG octets, or all of it when the run ends) is the
; residue.  (mv FRAMES A' PREV' INDEX')

(defun fn-ockp-cut-frames (a index count s prev seg acc fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp a) (<= a (fn-octets-len fn-octets))
                              (natp index) (natp count) (natp s) (natp seg)
                              (true-listp acc))
                  :measure (nfix (- (fn-octets-len fn-octets) (nfix a)))))
  (let ((len (fn-octets-len fn-octets)))
    (if (or (zp seg) (not (natp a)) (> a len) (<= (- len a) seg))
        (mv (revappend acc nil) a prev index)
      (let* ((b (+ a seg))
             (chunk (fn-sccb-slice-acc a b nil fn-octets))
             (header (fn-scc-header index count seg s))
             (trailer (fn-scc-seal prev header chunk)))
        (fn-ockp-cut-frames b (+ 1 index) count s trailer seg
                            (cons (list header a b trailer) acc) fn-octets)))))

; The run's last chunk: the residue [A, fill) as one frame.
(defun fn-ockp-last-frame (a index count s prev fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp a) (<= a (fn-octets-len fn-octets))
                              (natp index) (natp count) (natp s))))
  (let* ((b (fn-octets-len fn-octets))
         (chunk (fn-sccb-slice-acc a b nil fn-octets))
         (header (fn-scc-header index count (- b a) s))
         (trailer (fn-scc-seal prev header chunk)))
    (list (list header a b trailer))))

; The list level of the same cut: the full chunks of P and the residue.
(defun fn-ockp-cut (p seg)
  (declare (xargs :guard (and (true-listp p) (natp seg)) :measure (len p)))
  (if (or (zp seg) (not (fn-scc-long-enoughp (+ 1 seg) p)))
      (mv nil p)
    (mv-let (chunks residue)
      (fn-ockp-cut (nthcdr seg p) seg)
      (mv (cons (take seg p) chunks) residue))))

; L1: the codec's chunks of P ++ Q are the full chunks the cut of P emits,
; then the chunks of the residue with Q behind it.
(local
 (defthm fn-ockp-take-of-append
   (implies (and (natp k) (<= k (len a)))
            (equal (take k (append a b)) (take k a)))))

(local
 (defthm fn-ockp-nthcdr-of-append
   (implies (and (natp k) (<= k (len a)))
            (equal (nthcdr k (append a b)) (append (nthcdr k a) b)))))

(defthm fn-ockp-chunks-of-append-cut
  (implies (true-listp p)
           (equal (fn-scc-chunks (append p q) seg)
                  (append (mv-nth 0 (fn-ockp-cut p seg))
                          (fn-scc-chunks (append (mv-nth 1 (fn-ockp-cut p seg)) q) seg))))
  :hints (("Goal" :induct (fn-ockp-cut p seg)
           :expand ((fn-scc-chunks (append p q) seg)))))

(defthm fn-ockp-cut-residue-short
  (implies (and (true-listp p) (natp seg))
           (<= (len (mv-nth 1 (fn-ockp-cut p seg))) (max seg (len p))))
  :rule-classes nil)

; The chain's end: the trailer the frames of CHUNKS leave for the next.
(defun fn-ockp-chain-end (chunks index count s prev)
  (declare (xargs :guard (and (true-list-listp chunks) (natp index) (natp count) (natp s))
                  :verify-guards nil))
  (if (consp chunks)
      (fn-ockp-chain-end (cdr chunks) (+ 1 index) count s
                         (fn-scc-seal prev (fn-scc-header index count (len (car chunks)) s)
                                      (car chunks)))
    prev))

(defthm fn-ockp-frames-of-append
  (implies (natp index)
           (equal (fn-scc-frames (append c1 c2) index count s prev)
                  (append (fn-scc-frames c1 index count s prev)
                          (fn-scc-frames c2 (+ index (len c1)) count s
                                         (fn-ockp-chain-end c1 index count s prev)))))
  :hints (("Goal" :induct (fn-scc-frames c1 index count s prev)
           :in-theory (disable fn-scc-header fn-scc-seal))))

(in-theory (disable fn-ockp-cut-frames fn-ockp-last-frame fn-ockp-cut fn-ockp-chain-end))

; -----------------------------------------------------------------------------
; The admission of the frames just produced, by the reader's rule.
; (:ok TOTAL') or (:refused REASON).

(defun fn-ockp-admit-frames (frames total segment-bound file-bound)
  (declare (xargs :guard (and (true-list-listp frames) (natp total))))
  (if (consp frames)
      (let ((a (fn-sccr-admit-segment (nth 0 (car frames)) total segment-bound file-bound)))
        (if (and (consp a) (eq (car a) :ok) (natp (nth 1 a)))
            (fn-ockp-admit-frames (cdr frames) (+ total (nth 1 a)) segment-bound file-bound)
          (list :refused (if (consp a) (cadr a) :header))))
    (list :ok total)))

; -----------------------------------------------------------------------------
; The step.  TABLES: the four row lists (F P E R); K: the table being
; written (0..3); REST: its rows not yet encoded; I: the next row's index;
; INDEX, PREV: the run's next segment index and chain trailer; W: where the
; residue begins in the buffer; B: rows per step; COUNTS: each run's
; segment count (from the estimate); N = S; MTRIE, TABLE: the capture's
; Message-ID trie and event index; TOTAL: the file octets admitted so far.
; Answers (mv VERDICT FRAMES K' REST' I' INDEX' PREV' W' TOTAL' fn-octets):
; VERDICT :ok, or (:refused REASON) when a frame the reader would refuse
; was produced (the host then abandons the staged file).  The frames
; reference the buffer as left; the host writes them before the next step,
; which moves the residue to the front first.

(defun fn-ockp-table-rows (tables k)
  (declare (xargs :guard t))
  (cond ((eql k 0) (list (fn-sct-tables-f tables)))
        ((eql k 1) (fn-sct-tables-p tables))
        ((eql k 2) (fn-sct-tables-e tables))
        ((eql k 3) (fn-sct-tables-r tables))
        (t nil)))

(defun fn-ockp-count (counts k)
  (declare (xargs :guard t))
  (nfix (fn-sco-at (nfix k) counts)))

(defun fn-ockp-batch (tables k rest i index prev w b seg s counts n mtrie table
                             total segment-bound file-bound fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-ockp-rows-encodablep rest) (natp k) (natp i) (natp index)
                              (natp w) (<= w (fn-octets-len fn-octets))
                              (natp b) (natp seg) (natp s) (natp total)
                              (true-listp prev))
                  :verify-guards nil))
  (let* ((residue (fn-sccb-slice-acc w (fn-octets-len fn-octets) nil fn-octets))
         (fn-octets (fn-octets-clear fn-octets))
         (fn-octets (fn-octets-append-list residue fn-octets)))
    (mv-let (rest2 i2 fn-octets)
      (fn-ockp-encode-batch rest i b (eql k 2) (if (eql k 3) mtrie nil) n table fn-octets)
      (mv-let (frames a prev2 index2)
        (fn-ockp-cut-frames 0 index (fn-ockp-count counts k) s prev seg nil fn-octets)
        (if (consp rest2)
            (let ((admitted (fn-ockp-admit-frames frames total segment-bound file-bound)))
              (if (eq (car admitted) :ok)
                  (mv :ok frames k rest2 i2 index2 prev2 a (nth 1 admitted) fn-octets)
                (mv admitted nil k rest2 i2 index2 prev2 a total fn-octets)))
          (let* ((last (fn-ockp-last-frame a index2 (fn-ockp-count counts k) s prev2 fn-octets))
                 (frames (append frames last))
                 (admitted (fn-ockp-admit-frames frames total segment-bound file-bound)))
            (if (eq (car admitted) :ok)
                (mv :ok frames (+ 1 k) (fn-ockp-table-rows tables (+ 1 k)) 0 0
                    *fn-scc-genesis* (fn-octets-len fn-octets) (nth 1 admitted) fn-octets)
              (mv admitted nil k nil i2 index2 prev2 a total fn-octets))))))))

; The pipeline's start: the F table's one row, from the genesis, an empty
; buffer.  The counts: each run's segment count from its rows' length.
(defun fn-ockp-counts (tables index seg)
  (declare (xargs :guard (and (fn-sct-tables-treep tables) (natp seg))
                  :guard-hints (("Goal" :in-theory (enable fn-sct-tables-treep)))))
  (let ((n (len (fn-sct-tables-e tables))))
    (list (fn-sccb-chunk-count
           (fn-ockp-rows-len (list (fn-sct-tables-f tables)) 0 nil nil n nil 0) seg)
          (fn-sccb-chunk-count
           (fn-ockp-rows-len (fn-sct-tables-p tables) 0 nil nil n nil 0) seg)
          (fn-sccb-chunk-count
           (fn-ockp-rows-len (fn-sct-tables-e tables) 0 t nil n index 0) seg)
          (fn-sccb-chunk-count
           (fn-ockp-rows-len (fn-sct-tables-r tables) 0 nil (fn-cei-msgid-trie index) n index 0)
           seg))))

(defthm fn-ockp-counts-are-chunk-counts
  (implies (fn-sct-tables-treep tables)
           (let ((progs (fn-sct-table-programs tables index)))
             (equal (fn-ockp-counts tables index seg)
                    (list (len (fn-scc-chunks (nth 0 progs) seg))
                          (len (fn-scc-chunks (nth 1 progs) seg))
                          (len (fn-scc-chunks (nth 2 progs) seg))
                          (len (fn-scc-chunks (nth 3 progs) seg))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sct-table-programs fn-sct-tables-treep)
                           (fn-sccb-chunk-count fn-scc-chunks fn-sct-rows-program)))))

(in-theory (disable fn-ockp-admit-frames fn-ockp-batch fn-ockp-counts fn-ockp-table-rows
                    fn-ockp-count))

; -----------------------------------------------------------------------------
; What the host calls.  `fn-ockp-setup' (off the mutex, before anything is
; allocated): the tables of NEXT, the estimate, the decision, and what the
; steps need.  `fn-ockp-step': one batch over a state list.  The host loops
; on the step until K reaches 4, writing each step's frames.

; (list VERDICT TABLES COUNTS MTRIE INDEX N ESTIMATE): VERDICT :unencodable
; (the codec refuses a row), (:deferred REASON ESTIMATE BOUND) or
; (:plan ESTIMATE).
(defun fn-ockp-setup (next frontier revision seg budget free)
  (declare (xargs :guard (and (natp seg) (natp budget))
                  :guard-hints (("Goal" :in-theory (disable fn-ockp-estimate fn-ockp-counts
                                                            fn-ockp-decide)))))
  (let ((tables (fn-sct-tables-of-capture next frontier revision)))
    (if (not (fn-ockp-tables-encodablep tables))
        (list :unencodable nil nil nil nil 0 0)
      (let* ((index (fn-sco-event-index next))
             (estimate (fn-ockp-estimate tables index seg)))
        (list (fn-ockp-decide estimate budget free)
              tables (fn-ockp-counts tables index seg) (fn-cei-msgid-trie index) index
              (len (fn-sct-tables-e tables)) estimate)))))

; The state between steps: (K REST I INDEX PREV W TOTAL); the first, before
; any step, over the F table's one row.
(defun fn-ockp-initial-state (tables)
  (declare (xargs :guard t))
  (list 0 (fn-ockp-table-rows tables 0) 0 0 *fn-scc-genesis* 0 0))

(defun fn-ockp-statep (pst fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (and (true-listp pst) (equal (len pst) 7)
       (natp (nth 0 pst)) (fn-ockp-rows-encodablep (nth 1 pst))
       (natp (nth 2 pst)) (natp (nth 3 pst)) (true-listp (nth 4 pst))
       (natp (nth 5 pst)) (<= (nth 5 pst) (fn-octets-len fn-octets))
       (natp (nth 6 pst))))

(defun fn-ockp-donep (pst)
  (declare (xargs :guard t))
  (not (< (nfix (fn-sco-at 0 pst)) 4)))

; (mv VERDICT FRAMES STATE' fn-octets)
(defun fn-ockp-step (setup pst b seg s segment-bound file-bound fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-ockp-statep pst fn-octets) (natp b) (natp seg) (natp s))
                  :verify-guards nil))
  (let ((tables (fn-sco-at 1 setup)) (counts (fn-sco-at 2 setup))
        (mtrie (fn-sco-at 3 setup)) (table (fn-sco-at 4 setup)) (n (nfix (fn-sco-at 5 setup))))
    (mv-let (verdict frames k rest i index prev w total fn-octets)
      (fn-ockp-batch tables (nth 0 pst) (nth 1 pst) (nth 2 pst) (nth 3 pst)
                     (nth 4 pst) (nth 5 pst) b seg s counts n mtrie table
                     (nth 6 pst) segment-bound file-bound fn-octets)
      (mv verdict frames (list k rest i index prev w total) fn-octets))))

; The loop in the logic: the octets of every step's frames, in order, until
; the four tables are written; FUEL bounds it (the host stops at K = 4).
; (mv VERDICT OCTETS fn-octets)
(defun fn-ockp-run (setup pst b seg s segment-bound file-bound fuel fn-octets)
  (declare (xargs :stobjs fn-octets :measure (nfix fuel) :verify-guards nil))
  (if (or (zp fuel) (fn-ockp-donep pst))
      (mv :ok nil fn-octets)
    (mv-let (verdict frames pst2 fn-octets)
      (fn-ockp-step setup pst b seg s segment-bound file-bound fn-octets)
      (if (not (eq verdict :ok))
          (mv verdict nil fn-octets)
        (let ((octets (fn-sccb-plan-octets frames fn-octets)))
          (mv-let (verdict2 more fn-octets)
            (fn-ockp-run setup pst2 b seg s segment-bound file-bound (1- fuel) fn-octets)
            (mv verdict2 (append octets more) fn-octets)))))))

(in-theory (disable fn-ockp-setup fn-ockp-initial-state fn-ockp-statep fn-ockp-donep
                    fn-ockp-step fn-ockp-run))
