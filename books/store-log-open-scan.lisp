; fn: the charged totals of the log past a checkpoint, read before the open
; (Builder L, landing 2, 2026-10-10; prefix `fn-lgo-').
;
; A read-only command sizes its heap from the store's charged totals
; (books/heap-command.lisp fn-mo-observed-totals HDR SUFFIX) before it opens
; the store: HDR from the checkpoint's header run (Builder A,
; books/charged-totals-header.lisp), SUFFIX from this scan of the log's
; records past the header's S.  The scan streams the log one entry at a
; time (books/store-log-stream.lisp fn-lgw-step), expands each record
; (fn-lzr-expand), decodes it (fn-srs-decode) and adds its charged totals
; to a nine-field accumulator; no record is kept past its step.
;
; What the scan can know.  Eight of a row's nine fields are functions of
; the record's wire event: RECORDS, ARENA, HCHARGE, MEMBERSHIPS, EVENTS, LOG,
; CHARGE, RESIDENCY.  HISTORY (fn-ct-row-history, the padded SCC length of
; the interned ROW) also reads the row's arena handle and its statement
; context, which the open decides from the checkpoint's arena and the
; statement epoch at S; neither is in the log past S (seam L-M-A
; 2026-10-10, build/log-runs/l2/SEAM-history-field.md, M's ruling (b)).  The
; scan charges HISTORY at ALLOW + 3 x the row's octets, Builder M's per-row
; HISTORY clause of K-BOUND (books/admission-memory.lisp fn-adm-row-within-p,
; ALLOW = fn-adm-row-allowance PROFILE, memory landing 4b), and is exact in
; the other eight.  So the scan's totals bound the opened store's from above
; (fn-mm-tot-le), and M's fn-mo-read-holds-every-store-within-its-totals
; makes the read decision sound at them.
;
; KEYSTONES
;   L2-1 fn-lgo-run-is-the-fold          the stream's fold over one segment
;                                        is the fold over the recovered
;                                        kernel's committed records
;   L2-2 fn-lgo-chain-is-the-fold        over the open's segments, the fold
;                                        over fn-lgs-chain-records
;   L2-3 fn-lgo-fold-is-the-wire-fold    a fold that does not refuse is the
;                                        header's total plus the wire fold of
;                                        the decoded expansions past the skip
;   L2-4 fn-lgo-wire-fold-covers-the-replay
;                                        the wire fold agrees with the charged
;                                        fold of the rows the suffix replay
;                                        interns (fn-ssr-intern-step) in eight
;                                        fields and bounds its HISTORY, every
;                                        row within the HISTORY clause
;   L2-5 fn-lgo-observed-covers-the-opened-store
;                                        from a valid (K . TOT) cache, the
;                                        scan's total bounds the charged fold
;                                        of every row the open recovers

(in-package "ACL2")
(include-book "store-log-segments")
(include-book "store-log-stream")
(include-book "statement-recover-stream")
(include-book "history-totals-carried")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; 1. One record's charged totals, from its wire event.

; The held row the intern builds from wire record A (books/catalog-record.lisp
; fn-cat-intern-list) at handle 0, under the empty keyring and generation 0.
; The handle and the context are the two fields the scan cannot know; no
; total but HISTORY reads them.
(defun fn-lgo-held-of (a)
  (declare (xargs :guard t :verify-guards nil))
  (let ((bytes (fn-record-payload a)))
    (fn-held-make (fn-record-sequence a) (fn-record-txid a)
                  (fn-record-generation a) (fn-record-msgid a) 0
                  (fn-record-groups a) (fn-record-obligation-id a)
                  (fn-record-content-subject a) (fn-record-release-evidence a)
                  (fn-record-charge a) (fn-record-stamp a)
                  (fn-held-facts-of bytes)
                  (fn-held-context-of bytes nil 0)
                  nil nil)))

; The row the intern builds from wire event W, up to handle and context
; (books/store-intern.lisp fn-intern-event); :bad where the intern refuses.
(defun fn-lgo-wire-row (w)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-record-p w) (fn-lgo-held-of w))
        ((fn-stxa-p w)
         (let ((a (fn-replay-composite-record w)))
           (if (fn-record-p a) (fn-hstxa-make w (fn-lgo-held-of a)) :bad)))
        ((fn-wire-event-p w) w)
        (t :bad)))

; The row's charged totals with HISTORY at the clause's ceiling.
(defun fn-lgo-wire-tot (w allow)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((row (fn-lgo-wire-row w))
         (tot (fn-ct-row-tot row :resident)))
    (fn-mm-make-tot 1 (fn-mm-tot-arena tot) (fn-mm-tot-hcharge tot)
                    (fn-mm-tot-memberships tot) (fn-mm-tot-events tot)
                    (fn-mm-tot-log tot)
                    (+ (nfix allow) (* 3 (fn-sbud-row-octets row)))
                    (fn-mm-tot-charge tot) :resident)))

(defun fn-lgo-wire-fold (ws allow)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ws)
      (fn-mm-tot-plus (fn-lgo-wire-tot (car ws) allow)
                      (fn-lgo-wire-fold (cdr ws) allow))
    (fn-ct-zero-tot :resident)))

; One log record Z (as the stream hands it on: a frame of the store's
; dictionaries DICTS, or the record itself), expanded and decoded as the
; open decodes it, then charged; :bad where either refuses.
(defun fn-lgo-record-tot (z dicts allow)
  (declare (xargs :guard t :verify-guards nil))
  (let ((x (fn-lzr-expand dicts z)))
    (if (and (consp x) (eq (car x) :ok))
        (let ((ws (fn-srs-decode (list (cadr x)))))
          (if (consp ws) (fn-lgo-wire-tot (car ws) allow) :bad))
      :bad)))

; -----------------------------------------------------------------------------
; 2. The fold: the first SKIP records pass uncharged (the checkpoint covers
; them), every later one is added to ACC; :bad absorbs.  Answers
; (mv SKIP' ACC').

(defun fn-lgo-add (acc z dicts allow)
  (declare (xargs :guard t :verify-guards nil))
  (if (eq acc :bad)
      :bad
    (let ((r (fn-lgo-record-tot z dicts allow)))
      (if (eq r :bad) :bad (fn-mm-tot-plus acc r)))))

(defun fn-lgo-fold (zs skip acc dicts allow)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom zs) (mv (nfix skip) acc))
        ((posp skip) (fn-lgo-fold (cdr zs) (1- skip) acc dicts allow))
        (t (fn-lgo-fold (cdr zs) 0 (fn-lgo-add acc (car zs) dicts allow) dicts allow))))

; The expansions of the records ZS, or :bad.
(defun fn-lgo-expansions (zs dicts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp zs)
      (let ((x (fn-lzr-expand dicts (car zs)))
            (rest (fn-lgo-expansions (cdr zs) dicts)))
        (if (and (consp x) (eq (car x) :ok) (not (eq rest :bad)))
            (cons (cadr x) rest)
          :bad))
    nil))

; -----------------------------------------------------------------------------
; 3. The stream: fn-lgw-run's loop with each step's records folded at once.
; Answers (mv SKIP' ACC' ST').

(defun fn-lgo-run (c st unit max skip acc dicts allow)
  (declare (xargs :measure (nfix (- (len c) (fn-lgw-pos st)))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-lgw-step fn-lgw-window)))))
  (mv-let (took records st2) (fn-lgw-step (fn-lgw-window c st) st unit max (len c))
    (mv-let (skip2 acc2) (if took (fn-lgo-fold records skip acc dicts allow) (mv skip acc))
      (if (and took (not (fn-lgw-stop st2)) (< (fn-lgw-pos st2) (len c)))
          (fn-lgo-run c st2 unit max skip2 acc2 dicts allow)
        (mv skip2 acc2 st2)))))

; The open's segments CS (their durable octets, index order), each streamed
; from the genesis the one before ends on (books/store-log-stream.lisp
; fn-lgw-open-chain-records).  Answers (mv SKIP' ACC').
(defun fn-lgo-chain (cs genesis unit max skip acc dicts allow)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp cs)
      (mv-let (skip2 acc2 st) (fn-lgo-run (car cs) (fn-lgw-start genesis 1) unit max skip acc dicts allow)
        (fn-lgo-chain (cdr cs) (fn-lgc-last (fn-lgw-kernel st)) unit max skip2 acc2 dicts allow))
    (mv (nfix skip) acc)))

; Every row within the HISTORY clause (K-BOUND's, books/admission-memory.lisp
; fn-adm-row-within-p, at ALLOW = fn-adm-row-allowance PROFILE).
(defun fn-lgo-rows-history-within (rows allow)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (and (<= (nfix (fn-ct-row-history (car rows)))
               (+ (nfix allow) (* 3 (fn-sbud-row-octets (car rows)))))
           (fn-lgo-rows-history-within (cdr rows) allow))
    t))

; Two totals equal in every field but HISTORY.
(defun fn-lgo-agree-but-history (a b)
  (declare (xargs :guard t))
  (and (equal (fn-mm-tot-records a) (fn-mm-tot-records b))
       (equal (fn-mm-tot-arena a) (fn-mm-tot-arena b))
       (equal (fn-mm-tot-hcharge a) (fn-mm-tot-hcharge b))
       (equal (fn-mm-tot-memberships a) (fn-mm-tot-memberships b))
       (equal (fn-mm-tot-events a) (fn-mm-tot-events b))
       (equal (fn-mm-tot-log a) (fn-mm-tot-log b))
       (equal (fn-mm-tot-charge a) (fn-mm-tot-charge b))
       (equal (fn-mm-tot-paged-p a) (fn-mm-tot-paged-p b))))
