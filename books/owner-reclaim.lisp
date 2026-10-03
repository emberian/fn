; fn: content reclamation on a RUNNING owner (lane online-reclaim, Q16,
; 2026-09-29; the design is planning/evidence/operations-2026-09-28.md 3b).
;
; Offline, `store reclaim' streams the history's records as octets, folds
; them (books/store-reclaim-stream.lisp fn-rcls-step), rewrites each
; (books/store-reclaim-pack.lisp fn-rclp-event), replays the rewritten
; history and checkpoints it (books/store-log-reclaim.lisp,
; books/reclaim-instant.lisp).  A running owner holds its history as ROWS
; (held rows whose payloads are handles into the live arena), captured by
; pointer under the owner mutex like its automatic publication
; (host/owner-host.lisp fn-owner-sco-capture).  This book decides the online
; pass over those rows:
;
;   fn-orc-rewrite-row / -rows   a row the offline rewrite changes becomes
;       the tombstoned record (a plain record: its payload octets, which the
;       checkpoint writer takes as a source, books/store-checkpoint-arena-
;       writer.lisp fn-scka-src-of); every other row is kept, by pointer.
;   fn-orc-fold                  the offline fold over the rows' octets.
;
;   KEYSTONE fn-orc-rewrite-rows-is-the-offline-rewrite: the octets of the
;       rewritten rows are exactly fn-rclp-events of the rows' octets (the
;       history the offline verb streams: the covered prefix encoded from the
;       checkpoint's rows, the log's records as the canonical encoding of the
;       rows they intern to, fn-record-accepted-input-is-canonical), so every
;       theorem about the offline rewrite (a held article is never touched, a
;       reclaimed one stays reclaimed, a rerun rewrites nothing) is a theorem
;       about what the online pass checkpoints.
;   KEYSTONE fn-orc-decision-names-the-rewritten-articles: the online decision
;       (the recorded instant's, fn-rci-decide-stream over fn-orc-fold, which
;       is the offline fold over the rows' octets) reclaims only when recorded,
;       admitted and not a dry run, and names exactly the rewritten articles.
;   fn-orc-rewrite-rows-of-append, fn-orc-fold-of-append: the pass walks the
;       captured rows in chunks, and the chunks' rewrites and folds compose to
;       the whole history's.
;
; The request's answer is fn-orc-request-word.  The pass that installs (the
; rewritten capture's checkpoint, the live swap, the drop) is lane
; online-reclaim's NEXT; until it lands a running owner answers the dry run
; (host/native/owner.lisp fnn-owner-reclaim-dry-run).
(in-package "ACL2")
(include-book "expiry-instant")
(include-book "store-intern")

; -----------------------------------------------------------------------------
; 1. The rows' octets and the row rewrite.

;; The host's chunk (host/owner-host.lisp fn-owner-orc-chunk -> fn-orc-chunk)
;; runs the row rewrite in raw Lisp only when every function under it is
;; guard-verified; the encoders' and the reclaim pack's are verified here, as
;; books/store-budget.lisp verifies the store-events encoders it runs.
(verify-guards fn-store-retention-event-encode)
(verify-guards fn-store-event-encode)
(verify-guards fn-rclp-tombstoned)
(verify-guards fn-rclp-ctx-reclaimable)
(verify-guards fn-rclp-rewrites-p)

; A row's octets: the canonical encoding of the wire event the row stands for
; (alpha, books/store-intern.lisp fn-row-wire-of).
(defun fn-orc-row-octets (row fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-store-event-encode (fn-row-wire-of row fn-arena)))

(defun fn-orc-rows-octets (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp rows)
      (cons (fn-orc-row-octets (car rows) fn-arena)
            (fn-orc-rows-octets (cdr rows) fn-arena))
    nil))

; A guard dependency of the actual rewrite: expose the decision's payload
; profile conjunct without expanding the row's wire encoding or its bytes.
(local
 (defthm fn-orc-rewrite-payload-profile-by-definition
   (implies (fn-rclp-rewrites-p octets ctx)
            (fn-rcl-payload-profilep
             (fn-record-payload
              (fn-record-result-record (fn-record-decode-exact octets)))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (union-theories '(fn-rclp-rewrites-p)
                                       (theory 'minimal-theory))))))

(defun fn-orc-rewrite-row (row ctx fn-arena)
  (declare
   (xargs :stobjs fn-arena :guard t
          :guard-hints
          (("Goal"
            :use ((:instance fn-orc-rewrite-payload-profile-by-definition
                             (octets (fn-orc-row-octets row fn-arena))))
            :in-theory (theory 'minimal-theory)))))
  (let ((o (fn-orc-row-octets row fn-arena)))
    (if (fn-rclp-rewrites-p o ctx)
        (fn-rclp-tombstoned (fn-record-result-record (fn-record-decode-exact o)))
      row)))

; Executes by a loop (depth_check: a chunk's rows), equal by
; fn-orc-rewrite-rows-loop-is-rev-onto.
(defun fn-orc-rewrite-rows-loop (rows ctx acc fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp rows)
      (fn-orc-rewrite-rows-loop (cdr rows) ctx
                                (cons (fn-orc-rewrite-row (car rows) ctx fn-arena) acc)
                                fn-arena)
    (fn-ag-rev-onto acc nil)))

(defun fn-orc-rewrite-rows (rows ctx fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (mbe :logic (if (consp rows)
                  (cons (fn-orc-rewrite-row (car rows) ctx fn-arena)
                        (fn-orc-rewrite-rows (cdr rows) ctx fn-arena))
                nil)
       :exec (fn-orc-rewrite-rows-loop rows ctx nil fn-arena)))

(defthm fn-orc-rewrite-rows-loop-is-rev-onto
  (equal (fn-orc-rewrite-rows-loop rows ctx acc fn-arena)
         (fn-ag-rev-onto acc (fn-orc-rewrite-rows rows ctx fn-arena)))
  :hints (("Goal" :induct (fn-orc-rewrite-rows-loop rows ctx acc fn-arena)
                  :in-theory (disable fn-orc-rewrite-row))))

(verify-guards fn-orc-rewrite-rows
  :hints (("Goal" :in-theory (disable fn-orc-rewrite-row))))

; The offline fold (count, rewritten Message-IDs newest first, freed octets)
; over the rows' octets.
(defun fn-orc-fold (rows ctx acc fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp rows)
      (fn-orc-fold (cdr rows) ctx
                   (fn-rcls-step acc (fn-orc-row-octets (car rows) fn-arena) ctx)
                   fn-arena)
    acc))

; One chunk of the pass (what the host calls, off the owner mutex, a bounded
; number of rows per call): the chunk's rewrite and the fold advanced over it.
(defun fn-orc-chunk (rows ctx acc fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (list (fn-orc-rewrite-rows rows ctx fn-arena)
        (fn-orc-fold rows ctx acc fn-arena)))

; -----------------------------------------------------------------------------
; 2. The keystones.

(local
 (defthm fn-orc-record-is-not-held
   (implies (fn-record-p x) (not (fn-held-p x)))
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-shapep fn-held-p fn-held-shapep
                                      fn-record-payloadp)))))

(local
 (defthm fn-orc-record-is-not-hstxa
   (implies (fn-record-p x) (not (fn-hstxa-p x)))
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-shapep fn-hstxa-p)))))

; A plain record stands for itself.
(local
 (defthm fn-orc-wire-of-a-record
   (implies (fn-record-p x)
            (equal (fn-row-wire-of x fn-arena) x))
   :hints (("Goal" :in-theory (enable fn-row-wire-of)))))

;; The one fact of fn-rclp-rewrites-p the row lemma needs.
(local
 (defthm fn-orc-rewrites-p-tombstoned-is-a-record
   (implies (fn-rclp-rewrites-p o ctx)
            (fn-record-p (fn-rclp-tombstoned (fn-record-result-record (fn-record-decode-exact o)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-rclp-rewrites-p) (theory 'minimal-theory))))))

; Per row: the rewritten row's octets are the offline rewrite of its octets.
(defthm fn-orc-rewrite-row-is-the-offline-event
  (equal (fn-orc-row-octets (fn-orc-rewrite-row row ctx fn-arena) fn-arena)
         (fn-rclp-event (fn-orc-row-octets row fn-arena) ctx))
  :hints (("Goal" :in-theory (union-theories '(fn-orc-rewrite-row fn-rclp-event fn-orc-row-octets)
                                             (theory 'minimal-theory))
           :use ((:instance fn-orc-rewrites-p-tombstoned-is-a-record
                            (o (fn-orc-row-octets row fn-arena)))
                 (:instance fn-store-event-article-encoding-is-legacy-record-encoding
                            (record (fn-rclp-tombstoned
                                     (fn-record-result-record
                                      (fn-record-decode-exact
                                       (fn-orc-row-octets row fn-arena))))))
                 (:instance fn-orc-wire-of-a-record
                            (x (fn-rclp-tombstoned
                                (fn-record-result-record
                                 (fn-record-decode-exact
                                  (fn-orc-row-octets row fn-arena))))))))))

; KEYSTONE.  The subject is fn-orc-chunk's first element, called by
; host/native/owner.lisp fnn-owner-reclaim-rewrite (through
; host/owner-host.lisp fn-owner-orc-chunk).
(defthm fn-orc-rewrite-rows-is-the-offline-rewrite
  (equal (fn-orc-rows-octets (fn-orc-rewrite-rows rows ctx fn-arena) fn-arena)
         (fn-rclp-events (fn-orc-rows-octets rows fn-arena) ctx))
  :hints (("Goal" :induct (fn-orc-rewrite-rows rows ctx fn-arena)
                  :in-theory (e/d (fn-orc-rewrite-rows fn-orc-rows-octets fn-rclp-events)
                                  (fn-orc-rewrite-row fn-orc-row-octets fn-rclp-event)))))

(defthm fn-orc-fold-is-the-offline-fold
  (equal (fn-orc-fold rows ctx acc fn-arena)
         (fn-rcls-fold (fn-orc-rows-octets rows fn-arena) ctx acc))
  :hints (("Goal" :induct (fn-orc-fold rows ctx acc fn-arena)
                  :in-theory (e/d (fn-orc-fold fn-orc-rows-octets fn-rcls-fold)
                                  (fn-rcls-step fn-orc-row-octets)))))

(defthm fn-orc-true-listp-rows-octets
  (true-listp (fn-orc-rows-octets rows fn-arena)))

; KEYSTONE.  When the online decision (the recorded instant's, over the fold
; of the captured rows under the context CTX) reclaims, it was recorded, not a
; dry run, under an admitted profile, and the Message-IDs and freed octets it
; reports are the offline rewrite's over the rows' octets (the rows whose
; rewrite fn-orc-rewrite-rows-is-the-offline-rewrite changes).  With
; fn-orc-fold-is-the-offline-fold it is the decision `store reclaim
; --recorded' takes offline over the same history and context.  The subject
; is host/owner-host.lisp fn-owner-orc-decide, called by
; host/native/owner.lisp fnn-owner-reclaim-pass.
(defthm fn-orc-decision-names-the-rewritten-articles
  (let ((d (fn-rci-decide-stream profile v s (fn-orc-fold rows ctx (fn-rcls-init) fn-arena)
                                 dry fn-arena))
        (h (fn-orc-rows-octets rows fn-arena)))
    (implies (equal (car d) :reclaim)
             (and (fn-rci-recordedp v)
                  (not dry)
                  (fn-bs-profile-admittedp profile)
                  (consp (fn-rclp-rewritten-msgids h ctx))
                  (equal (nth 1 d) (fn-rclp-rewritten-msgids h ctx))
                  (equal (nth 2 d) (fn-rclp-freed h ctx)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rci-decide-stream fn-lgr-decide-stream
                                               fn-orc-fold-is-the-offline-fold
                                               fn-orc-true-listp-rows-octets
                                               car-cons cdr-cons nth-0-cons nth-add1
                                               (:executable-counterpart car)
                                               (:executable-counterpart equal)
                                               (:executable-counterpart zp)
                                               (:executable-counterpart binary-+))
                                             (theory 'minimal-theory))
                  :use ((:instance fn-rcls-fold-of-init
                                   (records (fn-orc-rows-octets rows fn-arena)))))))

; -----------------------------------------------------------------------------
; 3. Chunks.

(defthm fn-orc-rewrite-rows-of-append
  (equal (fn-orc-rewrite-rows (append a b) ctx fn-arena)
         (append (fn-orc-rewrite-rows a ctx fn-arena)
                 (fn-orc-rewrite-rows b ctx fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-orc-rewrite-rows) (fn-orc-rewrite-row)))))

(defthm fn-orc-fold-of-append
  (equal (fn-orc-fold (append a b) ctx acc fn-arena)
         (fn-orc-fold b ctx (fn-orc-fold a ctx acc fn-arena) fn-arena))
  :hints (("Goal" :induct (fn-orc-fold a ctx acc fn-arena)
                  :in-theory (union-theories '(fn-orc-fold binary-append car-cons cdr-cons)
                                             (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; 4. The operator's request.

; The answer to `store reclaim' on a running owner.  PASS the phase of a
; reclaim pass in flight (nil when none); INFLIGHT the count an automatic
; publication in flight captured (a natural) or nil; BLOCKEDP a deferral of
; the publication by the budget or the space (PKT-492); RECORDEDP whether
; the configuration carries a recorded instant.
;   :in-flight   a pass runs; this request is that pass (no second).
;   :queued      a publication runs; the pass starts when it ends.
;   :blocked     a deferral stands; refused by name (status says which).
;   :no-recorded-instant  nothing to decide at (`--recorded' without one).
;   :requested   the pass starts now.
(defun fn-orc-request-word (pass inflight blockedp recordedp)
  (declare (xargs :guard t))
  (cond (pass :in-flight)
        ((natp inflight) :queued)
        (blockedp :blocked)
        ((not recordedp) :no-recorded-instant)
        (t :requested)))

(defun fn-orc-request-status (word)
  (declare (xargs :guard t))
  (if (member-eq word '(:blocked :no-recorded-instant)) :refused :accepted))

(defthm fn-orc-one-pass-in-flight-by-definition
  (implies pass
           (equal (fn-orc-request-word pass inflight blockedp recordedp) :in-flight)))

(defthm fn-orc-never-past-a-deferral
  (implies (and (not pass) (not (natp inflight)) blockedp)
           (equal (fn-orc-request-status (fn-orc-request-word pass inflight blockedp recordedp))
                  :refused)))

; The capture's own admission (sweep S038).  The request above is answered in
; one owner quantum and the capture taken in a later one (host/native/owner.lisp
; fnn-owner-reclaim-pass, fnn-owner-reclaim-dry-run), so a second reclaim, or
; an automatic publication, can take the slot between them.  The capture
; therefore decides again, over the slot as it is in its own quantum: PASS
; the reclaim pass in flight (its mode, nil when none), INFLIGHT the count a
; publication in flight captured (a reclaim that writes is one: it holds
; INFLIGHT at its count).  A dry run writes nothing and leaves INFLIGHT alone.
;   :in-flight  a pass already holds the slot; this capture takes nothing.
;   :queued     a publication holds it; a writing pass takes nothing (the
;               host answers DEFERRED-QUEUED, a refusal by name).
;   :capture    the slot is free: PASS becomes MODE, and INFLIGHT the
;               captured COUNT for a writing pass.
; The result is (WORD PASS' INFLIGHT'), which host/owner-host.lisp
; fn-owner-orc-capture installs; it writes nothing else.
(defun fn-orc-capture-word (pass inflight dryp)
  (declare (xargs :guard t))
  (cond (pass :in-flight)
        ((and (not dryp) (natp inflight)) :queued)
        (t :capture)))

(defun fn-orc-capture-slot (mode count pass inflight)
  (declare (xargs :guard t))
  (let* ((dryp (eq mode :dry-run))
         (word (fn-orc-capture-word pass inflight dryp)))
    (if (eq word :capture)
        (list word mode (if dryp inflight count))
      (list word pass inflight))))

; KEYSTONE (no hypotheses beyond the ones each conjunct names): a capture
; that is refused leaves the slot exactly as it found it; one that is taken
; found no pass in flight and, when it writes, no publication; and while a
; taken capture holds the slot (MODE is a keyword, as every caller passes),
; every other capture, of any mode, is refused.  So at most one reclaim
; pass, and never a writing pass beside a publication, is in flight across
; the request's and the capture's separate quanta.
(defthm fn-orc-capture-takes-only-a-free-slot
  (let ((r (fn-orc-capture-slot mode count pass inflight)))
    (and (implies (not (equal (car r) :capture))
                  (equal (cdr r) (list pass inflight)))
         (implies (equal (car r) :capture)
                  (and (not pass)
                       (or (equal mode :dry-run) (not (natp inflight)))
                       (equal (cadr r) mode)))
         (implies (and (keywordp mode) (equal (car r) :capture))
                  (not (equal (car (fn-orc-capture-slot mode2 count2
                                                        (cadr r) (caddr r)))
                              :capture)))))
  :rule-classes nil)

; The release, by its holder (sweep S038).  HOLDER is (:reclaim MODE) -- the
; pass ending, host/owner-host.lisp fn-owner-orc-finish -- or
; (:publication COUNT) -- the publication done, fn-owner-sco-publication-done,
; COUNT the count it captured.  A release clears only what its holder holds:
; the reclaim pass whose MODE is in flight frees PASS (and INFLIGHT, which a
; writing pass held); a publication frees INFLIGHT only while it holds it at
; its COUNT and no writing pass does.  Anything else changes nothing.  The
; result is (PASS' INFLIGHT').
(defun fn-orc-release-slot (holder pass inflight)
  (declare (xargs :guard t))
  (let ((kind (and (consp holder) (car holder)))
        (who (and (consp holder) (consp (cdr holder)) (cadr holder))))
    (cond ((and (eq kind :reclaim) pass (equal pass who))
           (list nil (if (eq pass :dry-run) inflight nil)))
          ((and (eq kind :publication)
                (or (not pass) (eq pass :dry-run))
                (natp inflight) (equal inflight who))
           (list pass nil))
          (t (list pass inflight)))))

; KEYSTONE.  A release by anything but the slot's holder changes nothing,
; and, composed with the capture: while a writing reclaim pass holds the
; slot, a publication's release (at any count) leaves it held, and the
; pass's own release frees it; a publication's release never frees a pass.
(defthm fn-orc-release-by-a-non-holder-changes-nothing
  (and (implies (and (equal (car holder) :reclaim)
                     (not (and pass (equal pass (cadr holder)))))
                (equal (fn-orc-release-slot holder pass inflight)
                       (list pass inflight)))
       (implies (and (equal (car holder) :publication)
                     (or (and pass (not (equal pass :dry-run)))
                         (not (equal inflight (cadr holder)))))
                (equal (fn-orc-release-slot holder pass inflight)
                       (list pass inflight)))
       (implies (equal (car holder) :publication)
                (equal (car (fn-orc-release-slot holder pass inflight)) pass))
       (implies (and (keywordp mode) (not (equal mode :dry-run))
                     (equal (car (fn-orc-capture-slot mode count pass inflight))
                            :capture))
                (let ((r (fn-orc-capture-slot mode count pass inflight)))
                  (and (equal (fn-orc-release-slot (list :publication any)
                                                   (cadr r) (caddr r))
                              (cdr r))
                       (equal (fn-orc-release-slot (list :reclaim mode)
                                                   (cadr r) (caddr r))
                              (list nil nil))))))
  :rule-classes nil)
