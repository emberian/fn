; fn: the reclaim pass over the generation-pinned history in chunks, with no
; whole rewritten-row list (lane reclaim, 2026-10-04; storage-served reader's
; note, section reclaim; FN-SWARMPLAN wave 3 row 2).
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
(include-book "store-finalize-incremental")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; 1. The capture accumulator.

; (REV N CPR IDENTITY CONSUMER TOPIC INDEX IX): REV the records newest first,
; N their count; IX the id tries of CPR's paused node (fn-sfi-carry's value),
; NIL where CPR has no configured pause.
(defun fn-rcw-acc-make (rev n cpr identity consumer topic index ix)
  (declare (xargs :guard t))
  (list rev n cpr identity consumer topic index ix))

(defun fn-rcw-acc-rev (acc) (declare (xargs :guard t)) (fn-sco-at 0 acc))
(defun fn-rcw-acc-n (acc) (declare (xargs :guard t)) (fn-sco-at 1 acc))
(defun fn-rcw-acc-ix (acc) (declare (xargs :guard t)) (fn-sco-at 7 acc))

; The tries a fold result carries: fn-sfi-carry's value on any capture whose
; fold is R.
(defun fn-rcw-carry-of (r)
  (declare (xargs :guard t))
  (if (and (fn-sco-pausedp r) (fn-cnode-statep (fn-sco-at 1 r)))
      (fn-rii-ix-of (fn-cnode-node (fn-sco-at 1 r)))
    nil))

;; The carried invariant (R1): the tries IX, when held, are the tries of CPR's
;; paused node (fn-sfi-cpr-carriedp: the node configured, IX under
;; fn-rii-okp with it).  fn-rii-okp is a defun-sk, so this is a guard and a
;; hypothesis, never a runtime test; fn-rcw-accp stays executable.
(defun fn-rcw-acc-carriedp (acc)
  (declare (xargs :guard t))
  (implies (fn-rcw-acc-ix acc)
           (fn-sfi-cpr-carriedp (fn-sco-at 2 acc) (fn-rcw-acc-ix acc))))

; The accumulator of the capture of no records.
(defun fn-rcw-acc-init (configs)
  (declare (xargs :guard t))
  (let ((c (fn-sco-capture configs nil)))
    (fn-rcw-acc-make nil 0 (fn-sco-cpr c) (fn-sco-identity c) (fn-sco-consumer c)
                     (fn-sco-topic c) (fn-sco-event-index c)
                     (fn-sfi-carry c))))

; The configuration fold's resumption: through the carried tries when the
; accumulator holds them (fn-sfi-cpr-resume-carried: no trie rebuild), else
; the host's resumption fn-rii-sco-cpr-resume.  (CPR . IX').
(defun fn-rcw-cpr-step (cpr configs chunk ix)
  (declare (xargs :guard (implies ix (fn-sfi-cpr-carriedp cpr ix))))
  (if ix
      (let ((r (fn-sfi-cpr-resume-carried cpr configs chunk ix)))
        (cons (car r) (if (fn-sco-pausedp (car r)) (cdr r) nil)))
    (let ((r (fn-rii-sco-cpr-resume cpr configs chunk)))
      (cons r (fn-rcw-carry-of r)))))

; One chunk: every fold resumed over it exactly as fn-sco-extend resumes it.
(defun fn-rcw-acc-step (acc configs chunk)
  (declare (xargs :guard (fn-rcw-acc-carriedp acc)))
  (let ((chunk (true-list-fix chunk))
        (rev (fn-rcw-acc-rev acc))
        (n (nfix (fn-rcw-acc-n acc)))
        (cs (fn-rcw-cpr-step (fn-sco-at 2 acc) configs (true-list-fix chunk)
                             (fn-rcw-acc-ix acc))))
    (fn-rcw-acc-make (revappend chunk (true-list-fix rev))
                     (+ n (len chunk))
                     (car cs)
                     (fn-replay-identity-loop chunk (fn-sco-at 3 acc))
                     (fn-sco-consumer-resume (fn-sco-at 4 acc) chunk n)
                     (fn-th-prefix-loop (fn-sco-at 5 acc) chunk)
                     (fn-cei-build-aux chunk n (fn-sco-at 6 acc))
                     (cdr cs))))

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

; -----------------------------------------------------------------------------
; The carried invariant (R1) at init and over every step, and the step's
; fold as the checkpoint's resume (R2).  The cpr slot is unchanged in value:
; the carry only skips the trie rebuild.

(defthm fn-rcw-carry-of-is-carried
  (implies (fn-rcw-carry-of r)
           (fn-sfi-cpr-carriedp r (fn-rcw-carry-of r)))
  :hints (("Goal" :in-theory (e/d (fn-rcw-carry-of fn-sfi-cpr-carriedp)
                                  (fn-cnode-statep fn-rii-ix-of fn-sco-at fn-rii-okp)))))

(defthm fn-rcw-carried-ix-is-non-nil
  (implies (fn-sfi-cpr-carriedp r ix) ix)
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-sfi-cpr-carriedp fn-rii-okp) (fn-cnode-statep fn-rii-known-okp)))))

(defthm fn-rcw-cpr-step-car-is-resume
  (implies (implies ix (fn-sfi-cpr-carriedp cpr ix))
           (equal (car (fn-rcw-cpr-step cpr configs chunk ix))
                  (fn-sco-cpr-resume cpr configs chunk)))
  :hints (("Goal" :in-theory (e/d (fn-rcw-cpr-step)
                                  (fn-sfi-cpr-carriedp fn-sfi-cpr-resume-carried
                                   fn-rii-sco-cpr-resume fn-rcw-carry-of fn-sco-cpr-resume))
           :use ((:instance fn-sfi-cpr-resume-carried-is-sco-cpr-resume
                            (r cpr) (events chunk))
                 (:instance fn-rii-sco-cpr-resume-is-sco-cpr-resume
                            (r cpr) (events chunk))))))

(defthm fn-rcw-cpr-step-carried
  (implies (and (implies ix (fn-sfi-cpr-carriedp cpr ix))
                (cdr (fn-rcw-cpr-step cpr configs chunk ix)))
           (fn-sfi-cpr-carriedp (car (fn-rcw-cpr-step cpr configs chunk ix))
                                (cdr (fn-rcw-cpr-step cpr configs chunk ix))))
  :hints (("Goal" :in-theory (e/d (fn-rcw-cpr-step)
                                  (fn-sfi-cpr-carriedp fn-sfi-cpr-resume-carried
                                   fn-rii-sco-cpr-resume fn-rcw-carry-of fn-sco-cpr-resume))
           :use ((:instance fn-sfi-cpr-resume-carried-keeps-carried
                            (r cpr) (events chunk))
                 (:instance fn-rcw-carry-of-is-carried
                            (r (fn-rii-sco-cpr-resume cpr configs chunk)))))))

(defthm fn-rcw-cpr-step-keeps-a-configured-pause
  (implies (and (implies ix (fn-sfi-cpr-carriedp cpr ix))
                (fn-sco-pausedp (car (fn-rcw-cpr-step cpr configs chunk ix)))
                (fn-cnode-statep (fn-sco-at 1 (car (fn-rcw-cpr-step cpr configs chunk ix)))))
           (cdr (fn-rcw-cpr-step cpr configs chunk ix)))
  :hints (("Goal" :in-theory (e/d (fn-rcw-cpr-step fn-rcw-carry-of)
                                  (fn-sfi-cpr-carriedp fn-sfi-cpr-resume-carried
                                   fn-rii-sco-cpr-resume fn-sco-cpr-resume))
           :use ((:instance fn-sfi-cpr-resume-carried-keeps-carried
                            (r cpr) (events chunk))
                 (:instance fn-rcw-carried-ix-is-non-nil
                            (r (car (fn-sfi-cpr-resume-carried cpr configs chunk ix)))
                            (ix (cdr (fn-sfi-cpr-resume-carried cpr configs chunk ix))))))))

(defthm fn-rcw-cpr-step-keeps-the-tries
  (implies (and ix (fn-sfi-cpr-carriedp cpr ix)
                (fn-sco-pausedp (car (fn-rcw-cpr-step cpr configs chunk ix))))
           (cdr (fn-rcw-cpr-step cpr configs chunk ix)))
  :hints (("Goal" :in-theory (e/d (fn-rcw-cpr-step)
                                  (fn-sfi-cpr-carriedp fn-sfi-cpr-resume-carried))
           :use ((:instance fn-sfi-cpr-resume-carried-keeps-carried
                            (r cpr) (events chunk))
                 (:instance fn-rcw-carried-ix-is-non-nil
                            (r (car (fn-sfi-cpr-resume-carried cpr configs chunk ix)))
                            (ix (cdr (fn-sfi-cpr-resume-carried cpr configs chunk ix))))))))

(defthm fn-rcw-acc-carriedp-of-init
  (fn-rcw-acc-carriedp (fn-rcw-acc-init configs))
  :hints (("Goal" :use ((:instance fn-sfi-carry-is-carried
                                   (c (fn-sco-capture configs nil))))
           :in-theory (e/d (fn-rcw-acc-carriedp fn-rcw-acc-init fn-rcw-acc-make fn-rcw-acc-ix
                            fn-sco-at fn-sco-cpr)
                           (fn-sfi-carry fn-sfi-carry-is-carried fn-sco-capture
                            fn-sfi-cpr-carriedp)))))

(defthm fn-rcw-acc-carriedp-of-step
  (implies (fn-rcw-acc-carriedp acc)
           (fn-rcw-acc-carriedp (fn-rcw-acc-step acc configs chunk)))
  :hints (("Goal" :in-theory (e/d (fn-rcw-acc-carriedp fn-rcw-acc-step fn-rcw-acc-make
                                   fn-rcw-acc-ix fn-sco-at)
                                  (fn-rcw-cpr-step fn-sfi-cpr-carriedp))
           :use ((:instance fn-rcw-cpr-step-carried
                            (cpr (nth 2 acc)) (chunk (true-list-fix chunk)) (ix (nth 7 acc)))))))

(defthm fn-rcw-acc-step-cpr-is-resume
  (implies (fn-rcw-acc-carriedp acc)
           (equal (fn-sco-at 2 (fn-rcw-acc-step acc configs chunk))
                  (fn-sco-cpr-resume (fn-sco-at 2 acc) configs (true-list-fix chunk))))
  :hints (("Goal" :in-theory (e/d (fn-rcw-acc-carriedp fn-rcw-acc-step fn-rcw-acc-make
                                   fn-rcw-acc-ix fn-sco-at)
                                  (fn-rcw-cpr-step fn-sfi-cpr-carriedp fn-sco-cpr-resume))
           :use ((:instance fn-rcw-cpr-step-car-is-resume
                            (cpr (nth 2 acc)) (chunk (true-list-fix chunk)) (ix (nth 7 acc)))))))

(defthm fn-rcw-acc-step-carries-a-configured-pause
  (implies (and (fn-rcw-acc-carriedp acc)
                (fn-sco-pausedp (fn-sco-at 2 (fn-rcw-acc-step acc configs chunk)))
                (fn-cnode-statep (fn-sco-at 1 (fn-sco-at 2 (fn-rcw-acc-step acc configs chunk)))))
           (fn-rcw-acc-ix (fn-rcw-acc-step acc configs chunk)))
  :hints (("Goal" :in-theory (e/d (fn-rcw-acc-carriedp fn-rcw-acc-step fn-rcw-acc-make
                                   fn-rcw-acc-ix fn-sco-at)
                                  (fn-rcw-cpr-step fn-sfi-cpr-carriedp))
           :use ((:instance fn-rcw-cpr-step-keeps-a-configured-pause
                            (cpr (nth 2 acc)) (chunk (true-list-fix chunk)) (ix (nth 7 acc)))))))

(defthm fn-rcw-acc-step-keeps-the-tries
  (implies (and (fn-rcw-acc-carriedp acc) (fn-rcw-acc-ix acc)
                (fn-sco-pausedp (fn-sco-at 2 (fn-rcw-acc-step acc configs chunk))))
           (fn-rcw-acc-ix (fn-rcw-acc-step acc configs chunk)))
  :hints (("Goal" :in-theory (e/d (fn-rcw-acc-carriedp fn-rcw-acc-step fn-rcw-acc-make
                                   fn-rcw-acc-ix fn-sco-at)
                                  (fn-rcw-cpr-step fn-sfi-cpr-carriedp))
           :use ((:instance fn-rcw-cpr-step-keeps-the-tries
                            (cpr (nth 2 acc)) (chunk (true-list-fix chunk)) (ix (nth 7 acc)))))))

(defthm fn-rcw-accp-of-step
  (implies (fn-rcw-accp acc)
           (fn-rcw-accp (fn-rcw-acc-step acc configs chunk)))
  :hints (("Goal" :in-theory (enable fn-sco-at))))

(defthm fn-rcw-accp-of-init
  (fn-rcw-accp (fn-rcw-acc-init configs))
  :hints (("Goal" :in-theory (enable fn-sco-at))))

; One step finishes to the checkpoint extension of the finished accumulator.
(defthm fn-rcw-finish-of-step
  (implies (and (fn-rcw-accp acc) (fn-rcw-acc-carriedp acc))
           (equal (fn-rcw-acc-finish (fn-rcw-acc-step acc configs chunk))
                  (fn-sco-extend (fn-rcw-acc-finish acc) configs (true-list-fix chunk))))
  :hints (("Goal" :in-theory (e/d (fn-sco-extend fn-sco-records fn-sco-cpr
                                   fn-sco-identity fn-sco-consumer fn-sco-topic
                                   fn-sco-event-index fn-sco-at fn-sco-make)
                                  (fn-rcw-cpr-step fn-sfi-cpr-carriedp
                                   fn-rii-sco-cpr-resume fn-sco-cpr-resume
                                   fn-replay-identity-loop fn-sco-consumer-resume
                                   fn-th-prefix-loop fn-cei-build-aux))
           :use ((:instance fn-rcw-cpr-step-car-is-resume
                            (cpr (nth 2 acc)) (chunk (true-list-fix chunk))
                            (ix (nth 7 acc)))))))

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
   (implies (and (fn-rcw-accp acc) (fn-rcw-acc-carriedp acc)
                 (equal (fn-rcw-acc-finish acc) (fn-sco-capture configs prefix)))
            (equal (fn-rcw-acc-finish (fn-rcw-acc-steps acc configs chunks))
                   (fn-sco-capture configs (append prefix (fn-rcw-concat chunks)))))
   :hints (("Goal" :induct (fn-rcw-steps-ind acc configs chunks prefix)
            :in-theory (disable fn-rcw-acc-step fn-rcw-acc-finish fn-rcw-accp
                                fn-rcw-acc-carriedp fn-sco-capture fn-sco-extend))
           ("Subgoal *1/1" :use ((:instance fn-sco-extend-of-capture
                                            (suffix (true-list-fix (car chunks))))
                                 (:instance fn-rcw-finish-of-step
                                            (chunk (car chunks))))
            :in-theory (e/d (fn-rcw-concat)
                            (fn-rcw-acc-step fn-rcw-acc-finish fn-rcw-accp
                             fn-rcw-acc-carriedp fn-sco-capture fn-sco-extend)))
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
  (declare (xargs :stobjs fn-arena))
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

(local (in-theory (disable fn-scka-canon-rows-is-intern-at-of-alpha fn-scka-intern-at-bad-iff)))

;; The canonical rows of a concatenation, chunk by chunk: the second chunk's rows
;; are interned from the seed of the identity the first chunk's rows leave
;; (fn-replay-identity-loop over them), which is the identity the accumulator
;; carries after the first chunk.
(local
 (defthm fn-rcw-rows-wire-of-append
   (equal (fn-rows-wire-of (append a b) fn-arena)
          (append (fn-rows-wire-of a fn-arena) (fn-rows-wire-of b fn-arena)))))

(local
 (defthm fn-rcw-rows-wire-of-true-listp
   (true-listp (fn-rows-wire-of rows fn-arena))))

(local
 (defthm fn-rcw-rows-wire-of-true-list-fix
   (equal (fn-rows-wire-of (true-list-fix rows) fn-arena) (fn-rows-wire-of rows fn-arena))))

(local
 (defthm fn-rcw-seal-count-is-len-payloads-of-alpha
   (equal (fn-rcw-seal-count rows fn-arena)
          (len (fn-scka-payloads (fn-rows-wire-of rows fn-arena))))
   :hints (("Goal" :use (fn-rcw-seal-count-is-len-of-canon-payloads
                         fn-scka-canon-payloads-is-payloads-of-alpha)
            :in-theory (disable fn-rcw-seal-count-is-len-of-canon-payloads
                                fn-scka-canon-payloads-is-payloads-of-alpha
                                fn-scka-canon-payloads)))))

(local
 (defthm fn-rcw-append-is-bad
   (equal (equal (append x r) :bad) (and (atom x) (equal r :bad)))))

(local
 (defthm fn-rcw-canon-rows-of-append
   (implies
    (natp h)
    (equal (fn-scka-canon-rows (append a b) fn-arena h id)
           (let ((ra (fn-scka-canon-rows a fn-arena h id)))
             (if (eq ra :bad)
                 :bad
               (let ((rb (fn-scka-canon-rows b fn-arena (+ h (fn-rcw-seal-count a fn-arena))
                                             (fn-replay-identity-loop ra id))))
                 (if (eq rb :bad) :bad (append ra rb)))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-scka-canon-rows-is-intern-at-of-alpha)
                            (fn-scka-canon-rows fn-scka-intern-at fn-scka-intern-at-of-append
                             fn-scka-intern-at-bad-iff fn-rows-wire-of fn-scka-payloads
                             fn-replay-identity-loop fn-rcw-seal-count-is-len-of-canon-payloads))
            :use ((:instance fn-scka-intern-at-of-append
                             (ws (fn-rows-wire-of a fn-arena)) (vs (fn-rows-wire-of b fn-arena)))
                  (:instance fn-scka-intern-at-of-append-bad
                             (ws (fn-rows-wire-of a fn-arena)) (vs (fn-rows-wire-of b fn-arena))))))))

; The host's call per chunk of pass 2: ACC extended by the chunk's canonical
; rows from H, interned from the seed of the identity ACC carries, and the next
; H; :bad when a row has no canonical row.
(defun fn-rcw-canon-acc-step (acc configs chunk h fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-rcw-acc-carriedp acc)))
  (let ((canon (fn-scka-canon-rows chunk fn-arena (nfix h) (fn-sco-at 3 acc))))
    (if (eq canon :bad)
        :bad
      (list (fn-rcw-acc-step acc configs canon)
            (+ (nfix h) (fn-rcw-seal-count chunk fn-arena))))))

(local
 (defthm fn-rcw-canon-acc-step-parts
   (and (equal (equal (fn-rcw-canon-acc-step acc configs chunk h fn-arena) :bad)
               (equal (fn-scka-canon-rows chunk fn-arena (nfix h) (fn-sco-at 3 acc)) :bad))
        (equal (car (fn-rcw-canon-acc-step acc configs chunk h fn-arena))
               (if (equal (fn-scka-canon-rows chunk fn-arena (nfix h) (fn-sco-at 3 acc)) :bad)
                   nil
                 (fn-rcw-acc-step acc configs
                                  (fn-scka-canon-rows chunk fn-arena (nfix h) (fn-sco-at 3 acc)))))
        (equal (cadr (fn-rcw-canon-acc-step acc configs chunk h fn-arena))
               (if (equal (fn-scka-canon-rows chunk fn-arena (nfix h) (fn-sco-at 3 acc)) :bad)
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
   (implies (not (equal (fn-scka-canon-rows rows fn-arena h id) :bad))
            (true-listp (fn-scka-canon-rows rows fn-arena h id)))
   :hints (("Goal" :use ((:instance fn-scka-intern-at-true-listp (ws (fn-rows-wire-of rows fn-arena))))
            :in-theory (e/d (fn-scka-canon-rows-is-intern-at-of-alpha)
                            (fn-scka-intern-at-true-listp fn-scka-canon-rows fn-scka-intern-at
                             fn-rows-wire-of))))))

(local
 (defthm fn-rcw-canon-rows-of-true-list-fix
   (equal (fn-scka-canon-rows (true-list-fix rows) fn-arena h id)
          (fn-scka-canon-rows rows fn-arena h id))
   :hints (("Goal" :in-theory (e/d (fn-scka-canon-rows-is-intern-at-of-alpha)
                                   (fn-scka-canon-rows fn-scka-intern-at fn-rows-wire-of))))))

(local
 (defthm fn-rcw-seal-count-of-true-list-fix
   (equal (fn-rcw-seal-count (true-list-fix rows) fn-arena)
          (fn-rcw-seal-count rows fn-arena))
   :hints (("Goal" :in-theory (disable fn-scka-sealsp fn-row-wire-of
                                       fn-rcw-seal-count-is-len-of-canon-payloads
                                       fn-rcw-seal-count-is-len-payloads-of-alpha)))))

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
 (defthm fn-rcw-identity-of-finish
   (equal (fn-sco-identity (fn-rcw-acc-finish acc)) (fn-sco-at 3 acc))
   :hints (("Goal" :in-theory (enable fn-rcw-acc-finish fn-sco-identity fn-sco-make fn-sco-at)))))

(local
 (defthm fn-rcw-identity-of-acc-at-a-capture
   (implies (and (true-listp rows)
                 (equal (fn-rcw-acc-finish acc) (fn-sco-capture configs rows)))
            (equal (fn-sco-at 3 acc)
                   (fn-replay-identity-loop rows (fn-stxk-initial-context 0))))
   :hints (("Goal" :use ((:instance fn-rcw-identity-of-finish)
                         (:instance fn-scka-identity-of-capture (records rows)))
            :in-theory (disable fn-rcw-identity-of-finish
                                fn-rcw-acc-finish fn-sco-capture fn-sco-identity fn-sco-at)))))

(local
 (defthm fn-rcw-canon-steps-from
   (implies (and (fn-rcw-accp acc) (fn-rcw-acc-carriedp acc) (natp h)
                 (not (eq (fn-scka-canon-rows prefix fn-arena 0 (fn-stxk-initial-context 0)) :bad))
                 (equal h (fn-rcw-seal-count prefix fn-arena))
                 (equal (fn-rcw-acc-finish acc)
                        (fn-sco-capture configs
                                        (fn-scka-canon-rows prefix fn-arena 0
                                                            (fn-stxk-initial-context 0)))))
            (let ((r (fn-rcw-canon-acc-steps acc configs chunks h fn-arena))
                  (all (fn-scka-canon-rows (append prefix (fn-rcw-concat chunks)) fn-arena 0
                                           (fn-stxk-initial-context 0))))
              (and (equal (eq r :bad) (eq all :bad))
                   (implies (not (eq r :bad))
                            (equal (fn-rcw-acc-finish (car r))
                                   (fn-sco-capture configs all))))))
   :hints (("Goal" :induct (fn-rcw-canon-ind acc configs chunks h prefix fn-arena)
            :in-theory (disable fn-rcw-acc-step fn-rcw-acc-finish fn-rcw-accp fn-rcw-acc-carriedp
                                fn-sco-capture fn-sco-extend fn-scka-canon-rows
                                fn-rcw-seal-count-is-len-of-canon-payloads
                                fn-rcw-seal-count-is-len-payloads-of-alpha))
           ("Subgoal *1/1" :use ((:instance fn-rcw-canon-rows-of-append
                                            (a prefix) (b (true-list-fix (car chunks))) (h 0)
                                            (id (fn-stxk-initial-context 0)))
                                 (:instance fn-rcw-identity-of-acc-at-a-capture
                                            (rows (fn-scka-canon-rows prefix fn-arena 0
                                                                      (fn-stxk-initial-context 0))))
                                 (:instance fn-rcw-canon-rows-true-listp
                                            (rows prefix) (h 0) (id (fn-stxk-initial-context 0))))
            :in-theory (e/d (fn-rcw-concat)
                            (fn-rcw-acc-step fn-rcw-acc-finish fn-rcw-accp fn-rcw-acc-carriedp
                             fn-sco-capture fn-sco-extend fn-scka-canon-rows
                             fn-rcw-seal-count-is-len-of-canon-payloads
                             fn-rcw-seal-count-is-len-payloads-of-alpha)))
           ("Subgoal *1/2" :use ((:instance fn-sco-extend-of-capture
                                            (prefix (fn-scka-canon-rows prefix fn-arena 0
                                                                        (fn-stxk-initial-context 0)))
                                            (suffix (fn-scka-canon-rows
                                                     (car chunks) fn-arena h
                                                     (fn-sco-at 3 acc))))
                                 (:instance fn-rcw-finish-of-step
                                            (chunk (fn-scka-canon-rows (car chunks) fn-arena h
                                                                       (fn-sco-at 3 acc))))
                                 (:instance fn-rcw-canon-rows-of-append
                                            (a prefix) (b (true-list-fix (car chunks))) (h 0)
                                            (id (fn-stxk-initial-context 0)))
                                 (:instance fn-rcw-identity-of-acc-at-a-capture
                                            (rows (fn-scka-canon-rows prefix fn-arena 0
                                                                      (fn-stxk-initial-context 0))))
                                 (:instance fn-rcw-canon-rows-true-listp
                                            (rows prefix) (h 0) (id (fn-stxk-initial-context 0))))
            :in-theory (e/d (fn-rcw-concat)
                            (fn-rcw-acc-step fn-rcw-acc-finish fn-rcw-accp fn-rcw-acc-carriedp
                             fn-sco-capture fn-sco-extend fn-scka-canon-rows
                             fn-rcw-seal-count-is-len-of-canon-payloads
                             fn-rcw-seal-count-is-len-payloads-of-alpha))))))

(local
 (defthm fn-rcw-canon-rows-of-atom
   (implies (atom rows) (equal (fn-scka-canon-rows rows fn-arena h id) nil))
   :hints (("Goal" :in-theory (e/d (fn-scka-canon-rows fn-scka-canon-fold) nil)))))

(local
 (defthm fn-rcw-seal-count-of-atom
   (implies (atom rows) (equal (fn-rcw-seal-count rows fn-arena) 0))))

; KEYSTONE.  Pass 2 over the host's chunks, from the empty capture and handle
; 0, is :bad exactly when the whole history's canonical rows are, and
; otherwise finishes to the capture fn-owner-sco-next stages: the capture of
; the canonical rows of the whole rewritten history.
(defthm fn-rcw-canon-acc-steps-is-the-checkpoint-capture
  (let ((r (fn-rcw-canon-acc-steps (fn-rcw-acc-init configs) configs chunks 0 fn-arena))
        (all (fn-scka-canon-rows (fn-rcw-concat chunks) fn-arena 0 (fn-stxk-initial-context 0))))
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
; payload (books/owner-reclaim-seal.lisp fn-intern-row-at), so a reclaimed
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

; -----------------------------------------------------------------------------
; 4. The accumulator as a stobj.
;
; fn-rii-okp is a defun-sk, so the carried invariant cannot be tested at
; runtime, and a per-call accumulator VALUE cannot carry it into a
; guard-checked host call.  The accumulator lives in a stobj instead:
; fn-rcwacc-carriedp is the steps' guard (verified, never evaluated), and
; the entries below preserve it (fn-rcwacc-carriedp-of-init, -of-canon-step,
; and -of-predict-step in books/reclaim-chunked-seal.lisp).  Each entry is
; the value function on the stobj's field (R4), so the keystones above, over
; the value fold from fn-rcw-acc-init, are the host's.

(defstobj fn-rcwacc
  (fn-rcwacc-acc :type t :initially nil))

(defun fn-rcwacc-carriedp (fn-rcwacc)
  (declare (xargs :stobjs fn-rcwacc))
  (fn-rcw-acc-carriedp (fn-rcwacc-acc fn-rcwacc)))

(defun fn-rcwacc-init (configs fn-rcwacc)
  (declare (xargs :stobjs fn-rcwacc))
  (update-fn-rcwacc-acc (fn-rcw-acc-init configs) fn-rcwacc))

(defun fn-rcwacc-finish (fn-rcwacc)
  (declare (xargs :stobjs fn-rcwacc))
  (fn-rcw-acc-finish (fn-rcwacc-acc fn-rcwacc)))

(defthm fn-rcwacc-carriedp-of-init
  (fn-rcwacc-carriedp (fn-rcwacc-init configs fn-rcwacc))
  :hints (("Goal" :in-theory (e/d (fn-rcwacc-carriedp fn-rcwacc-init)
                                  (fn-rcw-acc-init fn-rcw-acc-carriedp)))))

(local
 (defthm fn-rcw-canon-acc-step-shape
   (implies (not (equal (fn-rcw-canon-acc-step acc configs chunk h fn-arena) :bad))
            (and (true-listp (fn-rcw-canon-acc-step acc configs chunk h fn-arena))
                 (consp (fn-rcw-canon-acc-step acc configs chunk h fn-arena))
                 (true-listp (cdr (fn-rcw-canon-acc-step acc configs chunk h fn-arena)))))
   :hints (("Goal" :in-theory (enable fn-rcw-canon-acc-step)))))

; Pass 2's entry: ACC extended by the chunk's canonical rows from H; the next
; handle, or :bad (the stobj untouched) when a row has no canonical row.
(defun fn-rcwacc-canon-step (configs chunk h fn-arena fn-rcwacc)
  (declare (xargs :stobjs (fn-arena fn-rcwacc)
                  :guard (fn-rcwacc-carriedp fn-rcwacc)))
  (let ((r (fn-rcw-canon-acc-step (fn-rcwacc-acc fn-rcwacc) configs chunk h fn-arena)))
    (if (eq r :bad)
        (mv :bad fn-rcwacc)
      (let ((fn-rcwacc (update-fn-rcwacc-acc (car r) fn-rcwacc)))
        (mv (cadr r) fn-rcwacc)))))

(defthm fn-rcwacc-carriedp-of-canon-step
  (implies (fn-rcwacc-carriedp fn-rcwacc)
           (fn-rcwacc-carriedp
            (mv-nth 1 (fn-rcwacc-canon-step configs chunk h fn-arena fn-rcwacc))))
  :hints (("Goal" :in-theory (e/d (fn-rcwacc-carriedp fn-rcwacc-canon-step fn-rcw-canon-acc-step)
                                  (fn-rcw-acc-carriedp fn-rcw-acc-step))
           :use ((:instance fn-rcw-acc-carriedp-of-step
                            (acc (fn-rcwacc-acc fn-rcwacc))
                            (chunk (fn-scka-canon-rows chunk fn-arena (nfix h)
                                                       (fn-sco-at 3 (fn-rcwacc-acc fn-rcwacc)))))))))

(defun fn-rcwacc-canon-steps (configs chunks h fn-arena fn-rcwacc)
  (declare (xargs :stobjs (fn-arena fn-rcwacc) :verify-guards nil :measure (len chunks)))
  (if (consp chunks)
      (mv-let (r fn-rcwacc)
        (fn-rcwacc-canon-step configs (car chunks) h fn-arena fn-rcwacc)
        (if (eq r :bad)
            (mv :bad fn-rcwacc)
          (fn-rcwacc-canon-steps configs (cdr chunks) r fn-arena fn-rcwacc)))
    (mv h fn-rcwacc)))

(local
 (defthm fn-rcw-canon-acc-step-h-is-not-bad
   (not (equal (cadr (fn-rcw-canon-acc-step acc configs chunk h fn-arena)) :bad))
   :hints (("Goal" :in-theory (enable fn-rcw-canon-acc-step)))))

(defthm fn-rcwacc-canon-step-is-the-value-step
  (let ((r (fn-rcw-canon-acc-step (fn-rcwacc-acc fn-rcwacc) configs chunk h fn-arena))
        (e (fn-rcwacc-canon-step configs chunk h fn-arena fn-rcwacc)))
    (and (equal (mv-nth 0 e) (if (equal r :bad) :bad (cadr r)))
         (equal (fn-rcwacc-acc (mv-nth 1 e))
                (if (equal r :bad) (fn-rcwacc-acc fn-rcwacc) (car r)))))
  :hints (("Goal" :in-theory (enable fn-rcwacc-canon-step))))

(defthm fn-rcwacc-canon-steps-is-the-value-fold-from
  (implies
   (not (equal h :bad))
   (let ((v (fn-rcw-canon-acc-steps (fn-rcwacc-acc fn-rcwacc) configs chunks h fn-arena))
         (e (fn-rcwacc-canon-steps configs chunks h fn-arena fn-rcwacc)))
     (and (equal (equal (mv-nth 0 e) :bad) (equal v :bad))
          (implies (not (equal v :bad))
                   (and (equal (mv-nth 0 e) (cadr v))
                        (equal (fn-rcwacc-acc (mv-nth 1 e)) (car v)))))))
  :hints (("Goal" :induct (fn-rcwacc-canon-steps configs chunks h fn-arena fn-rcwacc)
           :in-theory (disable fn-rcwacc-canon-step fn-rcwacc-acc update-fn-rcwacc-acc
                               fn-rcw-canon-acc-step fn-rcw-canon-acc-step-parts
                               fn-scka-canon-rows fn-rcw-seal-count))))

; R4.  From the fresh stobj, the entries over the host's chunks are the value
; fold from fn-rcw-acc-init.
(defthm fn-rcwacc-canon-steps-is-the-value-fold
  (let ((v (fn-rcw-canon-acc-steps (fn-rcw-acc-init configs) configs chunks 0 fn-arena))
        (e (fn-rcwacc-canon-steps configs chunks 0 fn-arena (fn-rcwacc-init configs fn-rcwacc))))
    (and (equal (equal (mv-nth 0 e) :bad) (equal v :bad))
         (implies (not (equal v :bad))
                  (and (equal (mv-nth 0 e) (cadr v))
                       (equal (fn-rcwacc-acc (mv-nth 1 e)) (car v))))))
  :hints (("Goal" :use ((:instance fn-rcwacc-canon-steps-is-the-value-fold-from
                                   (h 0) (fn-rcwacc (fn-rcwacc-init configs fn-rcwacc))))
           :in-theory (disable fn-rcwacc-canon-steps-is-the-value-fold-from
                               fn-rcwacc-canon-steps fn-rcw-canon-acc-steps fn-rcw-acc-init))))

; The keystone, on the stobj: the entries over the chunks finish to the
; checkpoint's capture.
(defthm fn-rcwacc-canon-steps-is-the-checkpoint-capture
  (let ((e (fn-rcwacc-canon-steps configs chunks 0 fn-arena (fn-rcwacc-init configs fn-rcwacc)))
        (all (fn-scka-canon-rows (fn-rcw-concat chunks) fn-arena 0 (fn-stxk-initial-context 0))))
    (and (equal (eq (mv-nth 0 e) :bad) (eq all :bad))
         (implies (not (eq all :bad))
                  (equal (fn-rcwacc-finish (mv-nth 1 e)) (fn-sco-capture configs all)))))
  :hints (("Goal" :use (fn-rcwacc-canon-steps-is-the-value-fold
                        fn-rcw-canon-acc-steps-is-the-checkpoint-capture)
           :in-theory (e/d (fn-rcwacc-finish)
                           (fn-rcwacc-canon-steps-is-the-value-fold
                            fn-rcw-canon-acc-steps-is-the-checkpoint-capture
                            fn-rcwacc-canon-steps fn-rcw-canon-acc-steps fn-rcw-acc-init
                            fn-rcw-acc-finish fn-scka-canon-rows fn-sco-capture
                            fn-rcwacc-acc update-fn-rcwacc-acc fn-rcwacc-init)))))
