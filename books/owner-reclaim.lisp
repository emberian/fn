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
;   fn-orc-rewrite-rows-of-append: the rewrite of a history extended by a
;       suffix is the rewrite of the prefix followed by the suffix's; the pass
;       rewrites the captured prefix in chunks and the records committed after
;       the capture are kept as they are (fn-orc-suffix-keptp decides that
;       they need no rewrite, so the swapped history is the offline rewrite
;       of the whole current history).
;
; The request (fn-orc-request-word) and the swap's validity
; (fn-orc-swap-validp) are the owner's answers; the pass's cuts and what a
; process death at each leaves durable are fn-orc-cut-outcome.
(in-package "ACL2")
(include-book "expiry-instant")
(include-book "store-intern")

; -----------------------------------------------------------------------------
; 1. The rows' octets and the row rewrite.

; A row's octets: the canonical encoding of the wire event the row stands for
; (alpha, books/store-intern.lisp fn-row-wire-of).
(defun fn-orc-row-octets (row fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (fn-store-event-encode (fn-row-wire-of row fn-arena)))

(defun fn-orc-rows-octets (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp rows)
      (cons (fn-orc-row-octets (car rows) fn-arena)
            (fn-orc-rows-octets (cdr rows) fn-arena))
    nil))

(defun fn-orc-rewrite-row (row ctx fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((o (fn-orc-row-octets row fn-arena)))
    (if (fn-rclp-rewrites-p o ctx)
        (fn-rclp-tombstoned (fn-record-result-record (fn-record-decode-exact o)))
      row)))

(defun fn-orc-rewrite-rows (rows ctx fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp rows)
      (cons (fn-orc-rewrite-row (car rows) ctx fn-arena)
            (fn-orc-rewrite-rows (cdr rows) ctx fn-arena))
    nil))

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
; 3. The captured prefix and the suffix.

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

; Whether no record of SUFFIX is rewritten under CTX (the records committed
; after the capture: new articles the capture's context does not release).
(defun fn-orc-suffix-keptp (suffix ctx fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp suffix)
      (and (not (fn-rclp-rewrites-p (fn-orc-row-octets (car suffix) fn-arena) ctx))
           (fn-orc-suffix-keptp (cdr suffix) ctx fn-arena))
    t))

(defthm fn-orc-rewrite-rows-of-a-kept-suffix
  (implies (and (fn-orc-suffix-keptp suffix ctx fn-arena) (true-listp suffix))
           (equal (fn-orc-rewrite-rows suffix ctx fn-arena) suffix))
  :hints (("Goal" :induct (fn-orc-suffix-keptp suffix ctx fn-arena)
                  :in-theory (union-theories '(fn-orc-rewrite-rows fn-orc-rewrite-row
                                               fn-orc-suffix-keptp true-listp car-cons cdr-cons
                                               cons-car-cdr)
                                             (theory 'minimal-theory)))))

; The swapped history (the captured prefix's rewrite, then the suffix as it
; is) is the rewrite of the whole current history when the suffix is kept.
(defthm fn-orc-swapped-history-is-the-rewrite-of-the-history
  (implies (and (fn-orc-suffix-keptp suffix ctx fn-arena) (true-listp suffix))
           (equal (append (fn-orc-rewrite-rows prefix ctx fn-arena) suffix)
                  (fn-orc-rewrite-rows (append prefix suffix) ctx fn-arena)))
  :hints (("Goal" :in-theory (union-theories '(fn-orc-rewrite-rows-of-append
                                               fn-orc-rewrite-rows-of-a-kept-suffix)
                                             (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; 4. The operator's request, and the swap.

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

(defthm fn-orc-one-pass-in-flight
  (implies pass
           (equal (fn-orc-request-word pass inflight blockedp recordedp) :in-flight)))

(defthm fn-orc-never-past-a-deferral
  (implies (and (not pass) (not (natp inflight)) blockedp)
           (equal (fn-orc-request-status (fn-orc-request-word pass inflight blockedp recordedp))
                  :refused)))

; The swap (under the owner mutex): valid when the reclaim context of the
; articles the pass rewrote cannot have changed since the capture -- the
; holders and the verdicts the capture's context read are the store's now,
; and the articles the capture read are a tail of the articles now (the
; acceptance only adds articles in front) -- and the suffix is kept.  An
; invalid swap installs nothing: the pass is abandoned and says so.
(defun fn-orc-article-tailp (cap now)
  (declare (xargs :guard t))
  (cond ((equal cap now) t)
        ((consp now) (fn-orc-article-tailp cap (cdr now)))
        (t nil)))

(defun fn-orc-swap-validp (s-cap s-now suffix ctx fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (and (equal (fn-rcl-store-holders s-now) (fn-rcl-store-holders s-cap))
       (equal (fn-sn-verdicts s-now) (fn-sn-verdicts s-cap))
       (fn-orc-article-tailp (fn-state-articles (fn-node-acceptance (fn-sn-node s-cap)))
                             (fn-state-articles (fn-node-acceptance (fn-sn-node s-now))))
       (fn-orc-suffix-keptp suffix ctx fn-arena)))

; -----------------------------------------------------------------------------
; 5. The pass's cuts (model crash points).
;
; Each cut is a point a process death can fall at; the outcome is what the
; next open reads.  Before the install's rename the old publication stands
; (the recorded instant is a configuration record, committed by the live
; reconfiguration before the capture; the staged file is staging's, swept by
; the open); from the rename on the new one does (the byte program's
; fn-bs-scp-program-crash-is-old-or-new: the file is the old or the new one,
; never torn, and the new checkpoint's F row names the segment the capture
; rotated to, so the open replays exactly the suffix after it).  The drop of
; the covered segments comes after the root's fence (T8).
(defconst *fn-orc-cuts*
  '(:instant-recorded :captured :rewritten :staged :staged-durable
    :installed :installed-durable :swapped :dropped))

(defun fn-orc-cut-outcome (cut)
  (declare (xargs :guard t))
  (if (member-eq cut '(:instant-recorded :captured :rewritten :staged :staged-durable))
      :old
    (if (member-eq cut *fn-orc-cuts*) :new :unknown)))

(defthm fn-orc-every-cut-is-old-or-new
  (implies (member-equal cut *fn-orc-cuts*)
           (member-equal (fn-orc-cut-outcome cut) '(:old :new))))

(defthm fn-orc-new-exactly-from-the-install
  (implies (member-equal cut *fn-orc-cuts*)
           (iff (equal (fn-orc-cut-outcome cut) :new)
                (member-equal cut '(:installed :installed-durable :swapped :dropped)))))
