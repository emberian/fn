; fn: the reclaim pass over the generation-pinned history in chunks, with no
; whole rewritten-row list (lane reclaim, 2026-10-04; storage-served reader's
; note §reclaim; FN-SWARMPLAN wave 3 row 2).
;
; Before this book the live pass (host/native/owner.lisp
; fnn-owner-reclaim-pass) walked the pinned history root in chunks but
; collected every rewritten row into one host list, then handed that list
; whole to the checkpoint capture, the tombstone prediction, the rebuild
; (fn-owner-orcp-rebuild) and the catalog load (fn-owner-orcp-load-catalog):
; one extra copy of the history alive beside the old Store, the checkpoint
; capture and the rebuilt Store.
;
; The pass now walks the pinned root more than once and feeds each chunk to
; folds whose carried state is the only thing that grows:
;
;   pass 1  the decision's fold (fn-orc-fold), no rewrite;
;   pass 2  the rewrite, canonicalized into the checkpoint's capture
;           (fn-rcw-canon-step: fn-scka-canon-rows from the carried handle);
;   pass 3  the rewrite, predicted into held rows (fn-rcw-predict-step:
;           fn-orcs-predict from the carried handle), extended into the
;           rebuilt capture.
;
; A capture is extended by a chunk through the accumulator fn-rcw-acc: the
; capture's five folds as they are, its records REVERSED with their count
; carried, so a chunk costs the chunk (fn-sco-extend appends the whole
; record list each call).  fn-rcw-acc-finish builds the capture once.
;
; KEYSTONES (each over ANY chunking of the history the host reads):
;   fn-rcw-acc-steps-is-capture: the accumulator stepped over the chunks
;     finishes to the capture of their concatenation (fn-sco-capture);
;   fn-rcw-canon-steps-is-canon: the canonical rows chunk by chunk, each from
;     the handle the previous chunk left, are the canonical rows of the
;     concatenation (fn-scka-canon-rows from 0), :bad exactly when it is;
;   fn-rcw-predict-steps-is-predict: the predicted rows and seal payloads
;     chunk by chunk are fn-orcs-predict's over the concatenation;
;   fn-rcw-rebuild-of-chunks-is-the-full-open: the rebuilt owner from the
;     chunked capture is the owner the full open of the rewritten history
;     installs (fn-orcp-rebuild-is-the-full-open's statement, over the
;     chunked form the host calls);
;   fn-rcw-load-catalog-chunks-is-load: the catalog loaded chunk by chunk
;     after the keyed clear is fn-sca-load-held-rows-keyed over the
;     concatenation.
(in-package "ACL2")
(include-book "store-checkpoint-open")
(include-book "replay-identity-index")
(include-book "store-checkpoint-arena")
(include-book "catalog-availability-owner-load")
(include-book "owner-reclaim")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; 1. The capture accumulator.

; (REV N CPR IDENTITY CONSUMER TOPIC INDEX): REV the records newest first, N
; their count.
(defun fn-rcw-acc-make (rev n cpr identity consumer topic index)
  (declare (xargs :guard t))
  (list rev n cpr identity consumer topic index))

(defun fn-rcw-acc-rev (acc) (declare (xargs :guard t)) (fn-sco-at 0 acc))
(defun fn-rcw-acc-n (acc) (declare (xargs :guard t)) (fn-sco-at 1 acc))

; The accumulator of the capture of no records.
(defun fn-rcw-acc-init (configs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((c (fn-sco-capture configs nil)))
    (fn-rcw-acc-make nil 0 (fn-sco-cpr c) (fn-sco-identity c) (fn-sco-consumer c)
                     (fn-sco-topic c) (fn-sco-event-index c))))

; One chunk: every fold resumed over it exactly as fn-sco-extend resumes it
; (the host's resumption fn-rii-sco-cpr-resume for the configuration fold).
(defun fn-rcw-acc-step (acc configs chunk)
  (declare (xargs :guard t :verify-guards nil))
  (let ((chunk (true-list-fix chunk))
        (rev (fn-rcw-acc-rev acc))
        (n (nfix (fn-rcw-acc-n acc))))
    (fn-rcw-acc-make (revappend chunk (true-list-fix rev))
                     (+ n (len chunk))
                     (fn-rii-sco-cpr-resume (fn-sco-at 2 acc) configs chunk)
                     (fn-replay-identity-loop chunk (fn-sco-at 3 acc))
                     (fn-sco-consumer-resume (fn-sco-at 4 acc) chunk n)
                     (fn-th-prefix-loop (fn-sco-at 5 acc) chunk)
                     (fn-cei-build-aux chunk n (fn-sco-at 6 acc)))))

(defun fn-rcw-acc-finish (acc)
  (declare (xargs :guard t))
  (fn-sco-make (revappend (true-list-fix (fn-rcw-acc-rev acc)) nil)
               (fn-sco-at 2 acc) (fn-sco-at 3 acc) (fn-sco-at 4 acc)
               (fn-sco-at 5 acc) (fn-sco-at 6 acc)))

; The accumulator's invariant: N is the count of REV.
(defun fn-rcw-accp (acc)
  (declare (xargs :guard t))
  (and (true-listp (fn-rcw-acc-rev acc))
       (equal (fn-rcw-acc-n acc) (len (fn-rcw-acc-rev acc)))))

; The chunks, in order (the host's walk; the logical form of its calls).
(defun fn-rcw-acc-steps (acc configs chunks)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp chunks)
      (fn-rcw-acc-steps (fn-rcw-acc-step acc configs (car chunks)) configs (cdr chunks))
    acc))

(defun fn-rcw-concat (chunks)
  (declare (xargs :guard t))
  (if (consp chunks)
      (append (true-list-fix (car chunks)) (fn-rcw-concat (cdr chunks)))
    nil))

(local
 (defthm fn-rcw-revappend-revappend
   (implies (true-listp b)
            (equal (revappend (revappend a b) nil)
                   (append (revappend b nil) (true-list-fix a))))))

(local
 (defthm fn-rcw-len-revappend
   (equal (len (revappend a b)) (+ (len a) (len b)))))

(local
 (defthm fn-rcw-true-listp-revappend
   (implies (true-listp b) (true-listp (revappend a b)))))

(local
 (defthm fn-rcw-append-nil
   (equal (append y nil) (true-list-fix y))))

(local
 (defthm fn-rcw-true-list-fix-append
   (equal (true-list-fix (append a b)) (append a (true-list-fix b)))))

(defthm fn-rcw-accp-of-step
  (implies (fn-rcw-accp acc)
           (fn-rcw-accp (fn-rcw-acc-step acc configs chunk)))
  :hints (("Goal" :in-theory (enable fn-sco-at))))

(defthm fn-rcw-accp-of-init
  (fn-rcw-accp (fn-rcw-acc-init configs))
  :hints (("Goal" :in-theory (enable fn-sco-at))))

; One step finishes to the checkpoint extension of the finished accumulator.
(defthm fn-rcw-finish-of-step
  (implies (fn-rcw-accp acc)
           (equal (fn-rcw-acc-finish (fn-rcw-acc-step acc configs chunk))
                  (fn-sco-extend (fn-rcw-acc-finish acc) configs (true-list-fix chunk))))
  :hints (("Goal" :in-theory (e/d (fn-sco-extend fn-sco-records fn-sco-cpr
                                   fn-sco-identity fn-sco-consumer fn-sco-topic
                                   fn-sco-event-index fn-sco-at fn-sco-make
                                   fn-rii-sco-cpr-resume-is-sco-cpr-resume)
                                  (fn-rii-sco-cpr-resume fn-sco-cpr-resume
                                   fn-replay-identity-loop fn-sco-consumer-resume
                                   fn-th-prefix-loop fn-cei-build-aux)))))

(defthm fn-rcw-finish-of-init
  (equal (fn-rcw-acc-finish (fn-rcw-acc-init configs))
         (fn-sco-capture configs nil))
  :hints (("Goal" :in-theory (e/d (fn-sco-capture fn-sco-make fn-sco-at fn-sco-cpr
                                   fn-sco-identity fn-sco-consumer fn-sco-topic
                                   fn-sco-event-index)
                                  (fn-sco-cpr-prefix fn-replay-identity-loop
                                   fn-cpe-projection-replay fn-th-prefix-loop
                                   fn-cei-build-aux)))))

(local
 (defun fn-rcw-steps-ind (acc configs chunks prefix)
   (declare (xargs :verify-guards nil))
   (if (consp chunks)
       (fn-rcw-steps-ind (fn-rcw-acc-step acc configs (car chunks)) configs (cdr chunks)
                         (append prefix (true-list-fix (car chunks))))
     (list acc prefix))))

(local
 (defthm fn-rcw-append-true-list-fix-left
   (equal (append (true-list-fix a) b) (append a b))))

(local
 (defthm fn-rcw-steps-from-a-capture
   (implies (and (fn-rcw-accp acc)
                 (equal (fn-rcw-acc-finish acc) (fn-sco-capture configs prefix)))
            (equal (fn-rcw-acc-finish (fn-rcw-acc-steps acc configs chunks))
                   (fn-sco-capture configs (append prefix (fn-rcw-concat chunks)))))
   :hints (("Goal" :induct (fn-rcw-steps-ind acc configs chunks prefix)
            :in-theory (disable fn-rcw-acc-step fn-rcw-acc-finish fn-rcw-accp
                                fn-sco-capture fn-sco-extend))
           ("Subgoal *1/1" :use ((:instance fn-sco-extend-of-capture
                                            (suffix (true-list-fix (car chunks))))
                                 (:instance fn-rcw-finish-of-step
                                            (chunk (car chunks))))
            :in-theory (e/d (fn-rcw-concat)
                            (fn-rcw-acc-step fn-rcw-acc-finish fn-rcw-accp
                             fn-sco-capture fn-sco-extend)))
           ("Subgoal *1/2" :in-theory (enable fn-rcw-concat)))))

; KEYSTONE.  The accumulator stepped over the host's chunks, from the empty
; capture, finishes to the capture of the whole rewritten history.
(defthm fn-rcw-acc-steps-is-capture
  (equal (fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init configs) configs chunks))
         (fn-sco-capture configs (fn-rcw-concat chunks)))
  :hints (("Goal" :use ((:instance fn-rcw-steps-from-a-capture
                                   (acc (fn-rcw-acc-init configs)) (prefix nil)))
           :in-theory (disable fn-rcw-acc-init fn-rcw-acc-finish fn-rcw-acc-steps
                               fn-sco-capture fn-rcw-accp))))

; -----------------------------------------------------------------------------
; 2. Pass 2: the checkpoint's capture, chunk by chunk.
;
; The checkpoint a reclaim stages is the capture of the rewritten rows'
; canonical rows, handles from 0 (host/owner-host.lisp fn-owner-sco-next with
; no base: fn-sco-capture over fn-scka-canon-rows).  A chunk's canonical rows
; start at the handle the previous chunks' sealed payloads left.

; The sealed payloads a chunk's canonical rows take (the count of
; fn-scka-canon-payloads, without building them).
(defun fn-rcw-seal-count (rows fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom rows)
      0
    (+ (if (fn-scka-sealsp (fn-row-wire-of (car rows) fn-arena)) 1 0)
       (fn-rcw-seal-count (cdr rows) fn-arena))))

(defthm fn-rcw-seal-count-is-len-of-canon-payloads
  (equal (fn-rcw-seal-count rows fn-arena)
         (len (fn-scka-canon-payloads rows fn-arena)))
  :hints (("Goal" :in-theory (disable fn-scka-sealsp fn-row-wire-of fn-scka-payload-of))))

(local
 (defthm fn-rcw-seal-count-of-append
   (equal (fn-rcw-seal-count (append a b) fn-arena)
          (+ (fn-rcw-seal-count a fn-arena) (fn-rcw-seal-count b fn-arena)))
   :hints (("Goal" :in-theory (disable fn-scka-sealsp fn-row-wire-of
                                       fn-rcw-seal-count-is-len-of-canon-payloads)))))

(local
 (defthm fn-rcw-append-is-not-bad
   (implies (not (equal y :bad))
            (not (equal (append x y) :bad)))))

(local (in-theory (disable fn-scka-canon-rows-is-intern-at-of-alpha)))

(local
 (defthm fn-rcw-canon-rows-of-append
   (implies
    (natp h)
    (equal (fn-scka-canon-rows (append a b) fn-arena h)
          (let ((ra (fn-scka-canon-rows a fn-arena h)))
            (if (eq ra :bad)
                :bad
              (let ((rb (fn-scka-canon-rows b fn-arena (+ h (fn-rcw-seal-count a fn-arena)))))
                (if (eq rb :bad) :bad (append ra rb)))))))
   :hints (("Goal" :induct (fn-scka-canon-rows a fn-arena h)
            :in-theory (disable fn-scka-intern-one fn-scka-sealsp fn-row-wire-of
                                fn-scka-canon-rows-is-intern-at-of-alpha
                                fn-rcw-seal-count-is-len-of-canon-payloads)))))

; The host's call per chunk of pass 2: ACC extended by the chunk's canonical
; rows from H, and the next H; :bad when a row has no canonical row.
(defun fn-rcw-canon-acc-step (acc configs chunk h fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((canon (fn-scka-canon-rows chunk fn-arena (nfix h))))
    (if (eq canon :bad)
        :bad
      (list (fn-rcw-acc-step acc configs canon)
            (+ (nfix h) (fn-rcw-seal-count chunk fn-arena))))))

(local
 (defthm fn-rcw-canon-acc-step-parts
   (and (equal (equal (fn-rcw-canon-acc-step acc configs chunk h fn-arena) :bad)
               (equal (fn-scka-canon-rows chunk fn-arena (nfix h)) :bad))
        (equal (car (fn-rcw-canon-acc-step acc configs chunk h fn-arena))
               (if (equal (fn-scka-canon-rows chunk fn-arena (nfix h)) :bad)
                   nil
                 (fn-rcw-acc-step acc configs (fn-scka-canon-rows chunk fn-arena (nfix h)))))
        (equal (cadr (fn-rcw-canon-acc-step acc configs chunk h fn-arena))
               (if (equal (fn-scka-canon-rows chunk fn-arena (nfix h)) :bad)
                   nil
                 (+ (nfix h) (fn-rcw-seal-count chunk fn-arena)))))
   :hints (("Goal" :in-theory (union-theories '(fn-rcw-canon-acc-step car-cons cdr-cons eq)
                                              (theory 'minimal-theory))))))

(local (in-theory (disable fn-rcw-canon-acc-step fn-rcw-acc-step)))

(defun fn-rcw-canon-acc-steps (acc configs chunks h fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil :measure (len chunks)))
  (if (consp chunks)
      (let ((r (fn-rcw-canon-acc-step acc configs (car chunks) h fn-arena)))
        (if (eq r :bad)
            :bad
          (fn-rcw-canon-acc-steps (car r) configs (cdr chunks) (cadr r) fn-arena)))
    (list acc h)))

(local
 (defthm fn-rcw-canon-rows-true-listp
   (implies (not (equal (fn-scka-canon-rows rows fn-arena h) :bad))
            (true-listp (fn-scka-canon-rows rows fn-arena h)))
   :hints (("Goal" :in-theory (disable fn-scka-intern-one fn-scka-sealsp fn-row-wire-of)))))

(local
 (defthm fn-rcw-canon-rows-of-true-list-fix
   (equal (fn-scka-canon-rows (true-list-fix rows) fn-arena h)
          (fn-scka-canon-rows rows fn-arena h))
   :hints (("Goal" :in-theory (disable fn-scka-intern-one fn-scka-sealsp fn-row-wire-of)))))

(local
 (defthm fn-rcw-seal-count-of-true-list-fix
   (equal (fn-rcw-seal-count (true-list-fix rows) fn-arena)
          (fn-rcw-seal-count rows fn-arena))
   :hints (("Goal" :in-theory (disable fn-scka-sealsp fn-row-wire-of
                                       fn-rcw-seal-count-is-len-of-canon-payloads)))))

(local
 (defun fn-rcw-canon-ind (acc configs chunks h prefix fn-arena)
   (declare (xargs :stobjs fn-arena :verify-guards nil :measure (len chunks)))
   (if (consp chunks)
       (let ((r (fn-rcw-canon-acc-step acc configs (car chunks) h fn-arena)))
         (if (eq r :bad)
             (list prefix)
           (fn-rcw-canon-ind (car r) configs (cdr chunks) (cadr r)
                             (append prefix (true-list-fix (car chunks))) fn-arena)))
     (list acc h prefix))))

(local
 (defthm fn-rcw-canon-steps-from
   (implies (and (fn-rcw-accp acc) (natp h)
                 (not (eq (fn-scka-canon-rows prefix fn-arena 0) :bad))
                 (equal h (fn-rcw-seal-count prefix fn-arena))
                 (equal (fn-rcw-acc-finish acc)
                        (fn-sco-capture configs (fn-scka-canon-rows prefix fn-arena 0))))
            (let ((r (fn-rcw-canon-acc-steps acc configs chunks h fn-arena))
                  (all (fn-scka-canon-rows (append prefix (fn-rcw-concat chunks)) fn-arena 0)))
              (and (equal (eq r :bad) (eq all :bad))
                   (implies (not (eq r :bad))
                            (equal (fn-rcw-acc-finish (car r))
                                   (fn-sco-capture configs all))))))
   :hints (("Goal" :induct (fn-rcw-canon-ind acc configs chunks h prefix fn-arena)
            :in-theory (disable fn-rcw-acc-step fn-rcw-acc-finish fn-rcw-accp
                                fn-sco-capture fn-sco-extend fn-scka-canon-rows
                                fn-rcw-seal-count-is-len-of-canon-payloads))
           ("Subgoal *1/2" :use ((:instance fn-sco-extend-of-capture
                                            (prefix (fn-scka-canon-rows prefix fn-arena 0))
                                            (suffix (fn-scka-canon-rows (car chunks) fn-arena h)))
                                 (:instance fn-rcw-finish-of-step
                                            (chunk (fn-scka-canon-rows (car chunks) fn-arena h)))
                                 (:instance fn-rcw-canon-rows-of-append
                                            (a prefix) (b (true-list-fix (car chunks))) (h 0)))
            :in-theory (e/d (fn-rcw-concat)
                            (fn-rcw-acc-step fn-rcw-acc-finish fn-rcw-accp
                             fn-sco-capture fn-sco-extend fn-scka-canon-rows
                             fn-rcw-seal-count-is-len-of-canon-payloads))))))

(local
 (defthm fn-rcw-canon-rows-of-atom
   (implies (atom rows) (equal (fn-scka-canon-rows rows fn-arena h) nil))))

(local
 (defthm fn-rcw-seal-count-of-atom
   (implies (atom rows) (equal (fn-rcw-seal-count rows fn-arena) 0))))

; KEYSTONE.  Pass 2 over the host's chunks, from the empty capture and handle
; 0, is :bad exactly when the whole history's canonical rows are, and
; otherwise finishes to the capture fn-owner-sco-next stages: the capture of
; the canonical rows of the whole rewritten history.
(defthm fn-rcw-canon-acc-steps-is-the-checkpoint-capture
  (let ((r (fn-rcw-canon-acc-steps (fn-rcw-acc-init configs) configs chunks 0 fn-arena))
        (all (fn-scka-canon-rows (fn-rcw-concat chunks) fn-arena 0)))
    (and (equal (eq r :bad) (eq all :bad))
         (implies (not (eq r :bad))
                  (equal (fn-rcw-acc-finish (car r)) (fn-sco-capture configs all)))))
  :hints (("Goal" :use ((:instance fn-rcw-canon-steps-from
                                   (acc (fn-rcw-acc-init configs)) (h 0) (prefix nil)))
           :in-theory (disable fn-rcw-acc-init fn-rcw-acc-finish fn-rcw-canon-acc-steps
                               fn-sco-capture fn-rcw-accp fn-scka-canon-rows))))

; -----------------------------------------------------------------------------
; 3. The fresh catalog, chunk by chunk.
;
; The host clears the fresh catalog with the keyed clear and then loads the
; rebuilt capture's records a chunk per call (the records are the capture's
; own list: nothing is copied).  Availability comes from each held row's
; decided facts, which the prediction set from the rewritten record's own
; payload (books/owner-reclaim-seal.lisp fn-orcs-held-of), so a reclaimed
; row is unavailable with no read of the arena's tombstone bit
; (books/catalog-availability.lisp fn-cat-row-availablep).

(defun fn-rcw-load-chunks (chunks view-index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if (consp chunks)
      (let ((fn-cat (fn-sca-load-held-available-from (car chunks) view-index fn-arena fn-cat)))
        (fn-rcw-load-chunks (cdr chunks) view-index fn-arena fn-cat))
    fn-cat))

(defthm fn-rcw-load-available-of-append
  (equal (fn-sca-load-held-available-from (append a b) view-index fn-arena fn-cat)
         (fn-sca-load-held-available-from
          b view-index fn-arena
          (fn-sca-load-held-available-from a view-index fn-arena fn-cat)))
  :hints (("Goal" :in-theory (disable fn-sca-load-held-available-row))))

(local
 (defthm fn-rcw-load-available-of-true-list-fix
   (equal (fn-sca-load-held-available-from (true-list-fix rows) view-index fn-arena fn-cat)
          (fn-sca-load-held-available-from rows view-index fn-arena fn-cat))
   :hints (("Goal" :in-theory (disable fn-sca-load-held-available-row)))))

(local
 (defthm fn-rcw-load-available-of-atom
   (implies (atom rows)
            (equal (fn-sca-load-held-available-from rows view-index fn-arena fn-cat)
                   fn-cat))))

(defthm fn-rcw-load-chunks-is-available-from
  (equal (fn-rcw-load-chunks chunks view-index fn-arena fn-cat)
         (fn-sca-load-held-available-from (fn-rcw-concat chunks) view-index fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-rcw-concat) (fn-sca-load-held-available-from)))))

; KEYSTONE.  Loading the chunks in order after the clear is the open's load
; of their concatenation (fn-sca-load-held-rows: the clear, then every row).
(defthm fn-rcw-load-chunks-is-load
  (equal (fn-rcw-load-chunks chunks view-index fn-arena (fn-cat-clear fn-cat))
         (fn-sca-load-held-rows (fn-rcw-concat chunks) view-index fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-sca-load-held-rows)
                                  (fn-sca-load-held-available-from fn-cat-clear
                                   fn-rcw-load-chunks)))))
