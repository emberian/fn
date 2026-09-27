; fn: the history folds over RETAINED rows are the folds over their WIRE
; forms (records-flip wave, lane flip-L3, 2026-09-27).
;
; After the records flip the Store history `fn-sf-records' holds retained
; rows (books/held-record.lisp): a plain article is a HELD row (its payload a
; handle into the arena), an accepted statement is the composite ROW
; `fn-hstxa-p' (the wire composite beside its article interned).  ALPHA, the
; wire event a row stands for, is `fn-row-wire-of' (books/store-intern.lisp):
; a held row with its bytes read through the arena, a composite row's wire
; composite, every other event itself.  The folds below read the history;
; before the flip they read wire events, so the specification of each is the
; same fold over the rows' wire forms.  One theorem per fold states that
; refinement for the function the host calls:
;
;   keys redecide   fn-ks-find-statement (host/owner-host.lisp
;                   fn-owner-key-statement-redecide-plan/-event reach it
;                   through fn-ks-redecide)            fn-ks-find-statement-over-alpha
;   carried usage   fn-pcb-usage (the admission's usage over the history,
;                   books/peer-carriage.lisp)          fn-pcb-usage-over-alpha
;   pre-C1 refusal  fn-sopc-free-p / the refusal's predicate
;                   (host/store-node-host.lisp fn-store-sn-open-extended
;                   through fn-sopc-classified-open)   fn-sopc-free-p-over-alpha
;   BP receipts     fn-bpr-article-records (books/bp-receipt.lisp
;                   fn-bpr-store-record-acceptedp)     fn-bpr-article-records-over-alpha
;   cancel txid     fn-ctl-event-msgid (books/control-visible.lisp
;                   fn-ctl-record-txid, the withdrawing article's
;                   acceptance txid)                    fn-ctl-event-msgid-over-alpha
;   consumer poll   fn-col-poll-article (books/consumer-poll-index.lisp
;                   fn-col-poll-scan, which host/owner-host.lisp
;                   fn-owner-consumer-local-poll reaches) fn-col-poll-article-over-alpha
;
; The article folds need what the intern establishes: a composite row's
; interned article stands for the article record its composite carries
; (`fn-row-composite-okp'; fn-intern-event-composite-okp).
(in-package "ACL2")
(include-book "store-intern")
(include-book "history-wire")
(include-book "key-statements")
(include-book "peer-carriage")
(include-book "bp-receipt")
(include-book "consumer-owner-local-progress")
(include-book "store-open-pre-c1")
(include-book "control-visible")

; The recognizers stay closed: the lemmas below dispatch on the row's kind.
(local (in-theory (disable fn-stxa-p fn-held-p fn-hstxa-p fn-record-p)))

; -----------------------------------------------------------------------------
; 1. Alpha of one row, by kind.

(defthm fn-hfr-wire-of-a-composite-row
  (implies (fn-hstxa-p row)
           (equal (fn-row-wire-of row fn-arena) (fn-hstxa-stxa row)))
  :hints (("Goal" :in-theory (enable fn-row-wire-of))))

(defthm fn-hfr-wire-of-a-held-row
  (implies (fn-held-p row)
           (equal (fn-row-wire-of row fn-arena)
                  (fn-held-wire row (fn-row-bytes row fn-arena))))
  :hints (("Goal" :in-theory (enable fn-row-wire-of))))

(defthm fn-hfr-wire-of-another-event
  (implies (and (not (fn-held-p row)) (not (fn-hstxa-p row)))
           (equal (fn-row-wire-of row fn-arena) row))
  :hints (("Goal" :in-theory (enable fn-row-wire-of))))

; The wire form of a held row is eleven wide: never a composite (ten wide)
; nor a composite row (three wide), and never a held row (fifteen wide).
(defthm fn-hfr-held-wire-is-no-composite
  (and (not (fn-stxa-p (fn-held-wire h payload)))
       (not (fn-hstxa-p (fn-held-wire h payload)))
       (not (fn-held-p (fn-held-wire h payload))))
  :hints (("Goal" :in-theory (enable fn-held-wire fn-record-make fn-stxa-p
                                     fn-stxa-shapep fn-hstxa-p fn-held-p
                                     fn-held-shapep))))

; -----------------------------------------------------------------------------
; 2. The composite a history event carries, gated as every reader gates it.

(defun fn-hfr-stxa-of (e)
  (declare (xargs :guard t))
  (let ((c (fn-hw-composite e)))
    (if (fn-stxa-p c) c nil)))

(defthm fn-hfr-stxa-of-alpha
  (equal (fn-hfr-stxa-of (fn-row-wire-of row fn-arena))
         (fn-hfr-stxa-of row))
  :hints (("Goal" :cases ((fn-hstxa-p row) (fn-held-p row))
           :in-theory (e/d (fn-hw-composite) (fn-row-wire-of fn-held-wire))
           :use ((:instance fn-held-is-no-wire-event (x row))
                 (:instance fn-hstxa-is-not-held (x row))))))

; Each reader reads only that composite.
(defthm fn-ks-evidence-reads-the-composite
  (equal (fn-ks-evidence e) (fn-ks-evidence (fn-hfr-stxa-of e)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ks-evidence fn-hw-composite))))

(defthm fn-ks-source-reads-the-composite
  (equal (fn-ks-source e) (fn-ks-source (fn-hfr-stxa-of e)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ks-source fn-hw-composite))))

(defthm fn-pcb-event-carriage-reads-the-composite
  (equal (fn-pcb-event-carriage e) (fn-pcb-event-carriage (fn-hfr-stxa-of e)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pcb-event-carriage fn-hw-composite))))

(defthm fn-sopc-pre-c1-control-record-p-reads-the-composite
  (equal (fn-sopc-pre-c1-control-record-p e)
         (fn-sopc-pre-c1-control-record-p (fn-hfr-stxa-of e)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sopc-pre-c1-control-record-p fn-hfr-stxa-of
                                   fn-sopc-hw-composite-idempotent)
                                  (fn-sopc-pre-c1-composite-p fn-hw-composite))
           :use ((:instance fn-sopc-pre-c1-composite-needs-a-composite
                            (x (fn-hw-composite e)))
                 (:instance fn-sopc-pre-c1-composite-needs-a-composite
                            (x (fn-hw-composite nil)))))))

; So each reader gives the same answer on a row and on its wire form.
(defthm fn-ks-evidence-over-alpha
  (equal (fn-ks-evidence (fn-row-wire-of row fn-arena)) (fn-ks-evidence row))
  :hints (("Goal" :in-theory (disable fn-row-wire-of fn-hfr-stxa-of fn-ks-evidence)
           :use ((:instance fn-ks-evidence-reads-the-composite (e row))
                 (:instance fn-ks-evidence-reads-the-composite
                            (e (fn-row-wire-of row fn-arena)))))))

(defthm fn-ks-source-over-alpha
  (equal (fn-ks-source (fn-row-wire-of row fn-arena)) (fn-ks-source row))
  :hints (("Goal" :in-theory (disable fn-row-wire-of fn-hfr-stxa-of fn-ks-source)
           :use ((:instance fn-ks-source-reads-the-composite (e row))
                 (:instance fn-ks-source-reads-the-composite
                            (e (fn-row-wire-of row fn-arena)))))))

(defthm fn-pcb-event-carriage-over-alpha
  (equal (fn-pcb-event-carriage (fn-row-wire-of row fn-arena))
         (fn-pcb-event-carriage row))
  :hints (("Goal" :in-theory (disable fn-row-wire-of fn-hfr-stxa-of fn-pcb-event-carriage)
           :use ((:instance fn-pcb-event-carriage-reads-the-composite (e row))
                 (:instance fn-pcb-event-carriage-reads-the-composite
                            (e (fn-row-wire-of row fn-arena)))))))

(defthm fn-sopc-pre-c1-control-record-p-over-alpha
  (equal (fn-sopc-pre-c1-control-record-p (fn-row-wire-of row fn-arena))
         (fn-sopc-pre-c1-control-record-p row))
  :hints (("Goal" :in-theory (disable fn-row-wire-of fn-hfr-stxa-of
                                      fn-sopc-pre-c1-control-record-p)
           :use ((:instance fn-sopc-pre-c1-control-record-p-reads-the-composite (e row))
                 (:instance fn-sopc-pre-c1-control-record-p-reads-the-composite
                            (e (fn-row-wire-of row fn-arena)))))))

(defthm fn-row-wire-of-nil
  (equal (fn-row-wire-of nil fn-arena) nil)
  :hints (("Goal" :in-theory (enable fn-row-wire-of fn-held-p fn-hstxa-p))))

(defthm fn-hfr-wire-of-a-value-is-a-value
  (implies row (fn-row-wire-of row fn-arena))
  :hints (("Goal" :cases ((fn-hstxa-p row) (fn-held-p row))
           :in-theory (e/d (fn-held-wire fn-record-make) (fn-row-wire-of))
           :use ((:instance fn-hstxa-p-fields (x row))))))

; -----------------------------------------------------------------------------
; 3. The scalar folds.  KEYSTONES: each fold over the rows is the fold over
; their wire forms (no hypothesis).

(defthm fn-ks-find-statement-over-alpha
  (equal (fn-ks-find-statement msgid (fn-rows-wire-of rows fn-arena))
         (fn-row-wire-of (fn-ks-find-statement msgid rows) fn-arena))
  :hints (("Goal" :induct (len rows)
           :in-theory (e/d (fn-ks-find-statement fn-rows-wire-of fn-ks-pending
                            fn-ks-msgid)
                           (fn-row-wire-of fn-ks-evidence fn-ks-source
                            fn-ks-statement)))))

(defthm fn-pcb-usage-over-alpha
  (equal (fn-pcb-usage (fn-rows-wire-of rows fn-arena) evidence)
         (fn-pcb-usage rows evidence))
  :hints (("Goal" :induct (len rows)
           :in-theory (e/d (fn-pcb-usage fn-rows-wire-of)
                           (fn-row-wire-of fn-pcb-event-carriage)))))

(defthm fn-sopc-free-p-over-alpha
  (equal (fn-sopc-free-p (fn-rows-wire-of rows fn-arena))
         (fn-sopc-free-p rows))
  :hints (("Goal" :induct (len rows)
           :in-theory (e/d (fn-sopc-free-p fn-rows-wire-of)
                           (fn-row-wire-of fn-sopc-pre-c1-control-record-p)))))

; -----------------------------------------------------------------------------
; 4. What the intern establishes for a row: a held row stands for a wire
; record (its handle names bytes in the arena), a composite row's interned
; article stands for the article record its wire composite carries, and no
; other row is a bare wire composite (the intern never retains one).

(defun fn-row-composite-okp (row fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (cond ((fn-hstxa-p row)
         (and (fn-record-p (fn-replay-composite-record (fn-hstxa-stxa row)))
              (equal (fn-row-wire-of (fn-hstxa-held row) fn-arena)
                     (fn-replay-composite-record (fn-hstxa-stxa row)))))
        ((fn-held-p row) (fn-record-p (fn-row-wire-of row fn-arena)))
        (t (not (fn-stxa-p row)))))

(defun fn-rows-composites-okp (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom rows)
      t
    (and (fn-row-composite-okp (car rows) fn-arena)
         (fn-rows-composites-okp (cdr rows) fn-arena))))

(defthm fn-intern-event-composite-okp
  (implies (and (fn-arena-p fn-arena) (natp generation)
                (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena))
                            :bad)))
           (fn-row-composite-okp
            (mv-nth 0 (fn-intern-event w keyring generation fn-arena))
            (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :cases ((fn-record-p w) (fn-stxa-p w))
           :in-theory (e/d (fn-intern-event fn-row-composite-okp)
                           (fn-cat-intern-list fn-row-wire-of fn-wire-event-p
                            fn-replay-composite-record fn-held-p-of-intern-list
                            fn-intern-event-materializes
                            fn-cat-intern-list-is-row-at-count fn-intern-row-at))
           :use ((:instance fn-intern-event-materializes
                            (w (fn-replay-composite-record w)))
                 (:instance fn-intern-event-materializes)
                 (:instance fn-held-p-of-intern-list)
                 (:instance fn-held-p-of-intern-list (w (fn-replay-composite-record w)))
                 (:instance fn-hstxa-is-not-held
                            (x (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena))))))))

; -----------------------------------------------------------------------------
; 5. The article folds.  KEYSTONES: alpha of the fold over the rows is the
; fold over their wire forms, for rows the intern made.

(defthm fn-bpr-event-article-over-alpha
  (implies (fn-row-composite-okp row fn-arena)
           (equal (fn-bpr-event-article (fn-row-wire-of row fn-arena))
                  (fn-row-wire-of (fn-bpr-event-article row) fn-arena)))
  :hints (("Goal" :cases ((fn-hstxa-p row) (fn-held-p row) (fn-stxa-p row))
           :in-theory (e/d (fn-bpr-event-article)
                           (fn-row-wire-of fn-held-wire fn-replay-composite-record)))))

(defthm fn-bpr-article-records-over-alpha
  (implies (fn-rows-composites-okp rows fn-arena)
           (equal (fn-bpr-article-records (fn-rows-wire-of rows fn-arena))
                  (fn-rows-wire-of (fn-bpr-article-records rows) fn-arena)))
  :hints (("Goal" :induct (len rows)
           :in-theory (e/d (fn-bpr-article-records fn-rows-wire-of)
                           (fn-row-wire-of fn-bpr-event-article
                            fn-row-composite-okp)))))

(defthm fn-col-poll-article-over-alpha
  (implies (fn-row-composite-okp row fn-arena)
           (equal (fn-col-poll-article (fn-row-wire-of row fn-arena))
                  (fn-row-wire-of (fn-col-poll-article row) fn-arena)))
  :hints (("Goal" :cases ((fn-hstxa-p row) (fn-held-p row) (fn-stxa-p row))
           :in-theory (e/d (fn-col-poll-article)
                           (fn-row-wire-of fn-held-wire fn-replay-composite-record)))))

(defthm fn-hfr-held-wire-msgid
  (equal (fn-record-msgid (fn-held-wire h payload)) (fn-record-msgid h))
  :hints (("Goal" :in-theory (enable fn-held-wire))))

(defthm fn-ctl-event-msgid-over-alpha
  (implies (fn-row-composite-okp row fn-arena)
           (equal (fn-ctl-event-msgid (fn-row-wire-of row fn-arena))
                  (fn-ctl-event-msgid row)))
  :hints (("Goal" :cases ((fn-hstxa-p row) (fn-held-p row))
           :in-theory (e/d (fn-ctl-event-msgid fn-row-composite-okp)
                           (fn-row-wire-of fn-held-wire fn-replay-composite-record
                            fn-row-bytes))
           :use ((:instance fn-hfr-held-wire-msgid
                            (h (fn-hstxa-held row))
                            (payload (fn-row-bytes (fn-hstxa-held row) fn-arena)))
                 (:instance fn-hfr-wire-of-a-held-row (row (fn-hstxa-held row)))))))

; -----------------------------------------------------------------------------
; 6. The consumer poll's report over the arena.

; THE HOST-CALLED POLL over a flipped history: the page's report is the exact
; encoding of the selected row's WIRE form, its bytes read through the arena
; (`fn-row-wire-of').  Host: host/owner-host.lisp fn-owner-consumer-local-poll
; with the live arena (flip-L3 REQUEST to the host lane: today it calls
; fn-col-poll-report, which refuses a held row :report).
(defun fn-col-poll-report-over (o consumer fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((decision (fn-col-poll o consumer)))
    (if (and (eq (car decision) :poll) (caddr decision))
        (let ((report (fn-col-poll-report-octets
                       (fn-row-wire-of (caddr decision) fn-arena))))
          (cond ((fn-ncl-poll-event-bytesp report)
                 (list :poll (cadr decision) report))
                ((and (consp report) (fn-cbor-octet-listp report))
                 (list :refused :oversize))
                (t (list :refused :report))))
      decision)))

(verify-guards fn-col-poll-report-over)

; KEYSTONE (the poll's report over the flipped history).  Unless the selected
; event is a held article row, the page the host serves over the arena is
; the page `fn-col-poll-report' computes, whatever the arena holds: a
; retained composite row reports the wire composite it carries, exactly as
; the wire composite reported before the flip.
(defthm fn-hfr-report-octets-of-alpha-unless-held
  (implies (not (fn-held-p e))
           (equal (fn-col-poll-report-octets (fn-row-wire-of e fn-arena))
                  (fn-col-poll-report-octets e)))
  :hints (("Goal" :cases ((fn-hstxa-p e))
           :in-theory (e/d (fn-col-poll-report-octets)
                           (fn-row-wire-of fn-stxa-encode fn-rcon-record-encode-impl
                            fn-rcon-record-encode-impl-is-record-encode-impl))
           :use ((:instance fn-hstxa-p-fields (x e))
                 (:instance fn-hstxa-is-no-wire-event (x (fn-hstxa-stxa e)))))))

(defthm fn-col-poll-report-over-is-the-report-unless-a-held-row
  (implies (not (fn-held-p (caddr (fn-col-poll o consumer))))
           (equal (fn-col-poll-report-over o consumer fn-arena)
                  (fn-col-poll-report o consumer)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-col-poll-report-over fn-col-poll-report
                                fn-hfr-report-octets-of-alpha-unless-held)
                              (theory 'minimal-theory)))))

; A held article row's report encodes its wire form: the row's positions
; with the payload its handle names in the arena.
(defthm fn-col-poll-report-over-of-a-held-row-unfolds
  (implies (fn-held-p (caddr (fn-col-poll o consumer)))
           (equal (fn-col-poll-report-over o consumer fn-arena)
                  (let* ((decision (fn-col-poll o consumer))
                         (h (caddr decision))
                         (report (fn-col-poll-report-octets
                                  (fn-held-wire h (fn-row-bytes h fn-arena)))))
                    (if (eq (car decision) :poll)
                        (cond ((fn-ncl-poll-event-bytesp report)
                               (list :poll (cadr decision) report))
                              ((and (consp report) (fn-cbor-octet-listp report))
                               (list :refused :oversize))
                              (t (list :refused :report)))
                      decision))))
  :hints (("Goal" :in-theory (e/d (fn-col-poll-report-over fn-row-wire-of)
                                  (fn-col-poll fn-col-poll-report-octets
                                   fn-ncl-poll-event-bytesp fn-held-wire
                                   fn-row-bytes)))))

; KEYSTONE (PKT-254 over the arena; the twin of
; fn-col-poll-report-fits-or-refuses-by-name, books/consumer-owner-local-
; progress.lisp, for the function the host calls after the flip): a refusal
; or empty page exactly as fn-col-poll answered; a page whose report is the
; exact encoding of the selected row's WIRE form when the kind-6 reply can
; carry it; the named refusal :oversize above the ceiling.
(defthm fn-col-poll-report-over-fits-or-refuses-by-name
  (let ((r (fn-col-poll-report-over o consumer fn-arena))
        (d (fn-col-poll o consumer)))
    (and (implies (not (equal (car d) :poll)) (equal r d))
         (implies (and (equal (car d) :poll) (not (caddr d))) (equal r d))
         (implies (and (equal (car d) :poll) (caddr d)
                       (fn-ncl-poll-event-bytesp
                        (fn-col-poll-report-octets
                         (fn-row-wire-of (caddr d) fn-arena))))
                  (equal r (list :poll (cadr d)
                                 (fn-col-poll-report-octets
                                  (fn-row-wire-of (caddr d) fn-arena)))))
         (implies (and (equal (car d) :poll) (caddr d)
                       (consp (fn-col-poll-report-octets
                               (fn-row-wire-of (caddr d) fn-arena)))
                       (fn-cbor-octet-listp (fn-col-poll-report-octets
                                             (fn-row-wire-of (caddr d) fn-arena)))
                       (< *fn-stxa-max-octets*
                          (len (fn-col-poll-report-octets
                                (fn-row-wire-of (caddr d) fn-arena)))))
                  (equal r '(:refused :oversize)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-col-poll-report-over fn-ncl-poll-event-bytesp
                                (:executable-counterpart fn-cbor-octet-listp))
                              (theory 'minimal-theory)))))

; KEYSTONE (PKT-467 over the arena; the twin of
; fn-col-poll-report-of-an-admitted-payload-fits, books/consumer-owner-local-
; progress.lisp): a page
; whose selected row's wire encoding is a payload the publication gate admits
; is served as that page, never :oversize.
(defthm fn-col-poll-report-over-of-an-admitted-payload-fits
  (let* ((d (fn-col-poll o consumer))
         (octets (fn-col-poll-report-octets (fn-row-wire-of (caddr d) fn-arena))))
    (implies (and (equal (car d) :poll)
                  (caddr d)
                  (consp octets)
                  (fn-cbor-octet-listp octets)
                  (fn-bs-publication-admissiblep profile committed-count
                                                 (len octets)))
             (equal (fn-col-poll-report-over o consumer fn-arena)
                    (list :poll (cadr d) octets))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-col-poll-report-over-fits-or-refuses-by-name)
                        (:instance fn-bs-profile-valid-record-fits-a-poll-reply
                                   (values profile)
                                   (octets (len (fn-col-poll-report-octets
                                                 (fn-row-wire-of
                                                  (caddr (fn-col-poll o consumer))
                                                  fn-arena))))))
           :in-theory (union-theories '(fn-ncl-poll-event-bytesp)
                                      (theory 'minimal-theory)))))
