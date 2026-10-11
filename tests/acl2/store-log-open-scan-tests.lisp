; Teeth for books/store-log-open-scan (Builder L, landing 2a): the log
; suffix's charged totals before the open, L2-1 to L2-5, and the read-only
; probe's scan of it (landing 2a-host), L2H-1 to L2H-3.
;
; The fixture is a keyring history: an enrollment (a keyring snapshot), an
; article, a key rotation, an article; encoded, logged as one batch entry of
; the first two and one entry each of the last two, in one 16 KiB segment
; (and split over two segments for the chain).  The checkpoint covers the
; first record: its cache is (1 . the charged fold of the first row).
; ALLOW 200 puts every row within the HISTORY clause (row HISTORY
; 2064/168/2064/176 against octets 2052/3/2052/3); at ALLOW 0 the two article
; rows are not within (their exact HISTORY 344 against the wire fold's 18).
;
; The codecs are attachments: assert-event evaluates with them, so the
; fixture is computed by zero-argument functions and defconst-eval.
(in-package "ACL2")
(include-book "../../books/store-log-open-scan")
(include-book "../../books/codec-attach")
(include-book "../../books/crypto-attach")
(include-book "../../books/statement-attach")
(include-book "../../books/defkeystone")
(include-book "teeth-ground-lemma")

(defconst *lgot-principal* (make-list 32 :initial-element 7))
(defconst *lgot-keys1* (list (cons :ed25519 (make-list 32 :initial-element 11))
                             (cons :ml-dsa-65 (make-list 1952 :initial-element 13))))
(defconst *lgot-keys2* (list (cons :ed25519 (make-list 32 :initial-element 12))
                             (cons :ml-dsa-65 (make-list 1952 :initial-element 14))))
(defun lgot-enroll ()
  (declare (xargs :verify-guards nil))
  (fn-hl-enroll-event 0 0 0 1 *lgot-principal* *lgot-keys1* nil))
(defun lgot-rotate ()
  (declare (xargs :verify-guards nil))
  (fn-hl-enroll-event 2 2 2 2 *lgot-principal* *lgot-keys2* (list (lgot-enroll))))
(defun lgot-ws-fn ()
  (declare (xargs :verify-guards nil))
  (list (lgot-enroll)
        (fn-record-make 1 1 1 "<before@example>" '(65 13 10) '("example") "o1" "s1" "e1" 1 841000000)
        (lgot-rotate)
        (fn-record-make 3 3 3 "<after@example>" '(66 13 10) '("example" "other") "o2" "s2" "e2" 1
                        841000001)))
(defun lgot-enc (ws)
  (declare (xargs :verify-guards nil))
  (if (consp ws) (cons (fn-store-event-encode (car ws)) (lgot-enc (cdr ws))) nil))
(defun lgot-pad (log n)
  (declare (xargs :verify-guards nil))
  (append log (fn-bs-zeros (- n (len log)))))

(defconst-eval *lgot-ws* (lgot-ws-fn))
(defconst-eval *lgot-zs* (lgot-enc *lgot-ws*))
(defconst-eval *lgot-t1*
  (fn-lg-last-trailer (list (nth 0 *lgot-zs*) (nth 1 *lgot-zs*)) *fn-lg-genesis*))
(defconst-eval *lgot-t2* (fn-lg-last-trailer (list (nth 2 *lgot-zs*)) *lgot-t1*))
; The first segment: the batch of the first two records.
(defconst-eval *lgot-seg1*
  (lgot-pad (fn-lg-log (list (nth 0 *lgot-zs*) (nth 1 *lgot-zs*)) *fn-lg-genesis* 4) 16384))
; The second: the last two, one entry each, chained from the first's trailer.
(defconst-eval *lgot-seg2*
  (lgot-pad (append (fn-lg-log (list (nth 2 *lgot-zs*)) *lgot-t1* 4)
                    (fn-lg-log (list (nth 3 *lgot-zs*)) *lgot-t2* 4))
            16384))
; The whole log in one segment.
(defconst-eval *lgot-seg*
  (lgot-pad (append (fn-lg-log (list (nth 0 *lgot-zs*) (nth 1 *lgot-zs*)) *fn-lg-genesis* 4)
                    (fn-lg-log (list (nth 2 *lgot-zs*)) *lgot-t1* 4)
                    (fn-lg-log (list (nth 3 *lgot-zs*)) *lgot-t2* 4))
            16384))
(defconst-eval *lgot-seed* (fn-ssr-seed (fn-stxk-initial-context 0)))

; The rows the open interns from the whole log (the replay worker, :resident).
(defun lgot-replay-rows (ws)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (acc fn-arena)
      (fn-ssr-intern-step *lgot-seed* ws nil nil :resident nil fn-arena)
      (if (eq acc :bad) :bad (fn-ssr-rows acc)))))
(defconst-eval *lgot-rows* (lgot-replay-rows *lgot-ws*))
(defconst-eval *lgot-cache* (cons 1 (fn-ct-charged (take 1 *lgot-rows*) :resident)))

(assert-event
 (and (equal (fn-lgk-committed (fn-lgt-recover *lgot-seg* *fn-lg-genesis* 4 16384 1)) *lgot-zs*)
      (equal (fn-lgs-chain-records (list *lgot-seg1* *lgot-seg2*) *fn-lg-genesis* 4 16384) *lgot-zs*)
      (equal (fn-srs-decode (fn-lgo-expansions *lgot-zs* nil)) *lgot-ws*)
      (equal (len *lgot-rows*) 4))
 :msg "the fixture: the log recovers the four records, the two-segment chain too, they decode to the history, and the replay interns four rows")
; -----------------------------------------------------------------------------
; L2-1: one segment's stream folds the recovered kernel's committed records.
(defteeth fn-lgo-run-is-the-fold
  :claim (let* ((run (fn-lgo-run c (fn-lgw-start genesis floor) unit max skip acc dicts allow))
                (ks (fn-lgt-recover c genesis unit max floor))
                (fold (fn-lgo-fold (fn-lgk-committed ks) skip acc dicts allow)))
           (()
            (and (equal (mv-nth 0 run) (mv-nth 0 fold))
                 (equal (mv-nth 1 run) (mv-nth 1 fold))
                 (equal (fn-lgw-kernel (mv-nth 2 run)) (fn-lgc-of ks)))))
  :subject fn-lgo-run
  :witness ((c *lgot-seg*) (genesis *fn-lg-genesis*) (floor 1) (unit 4) (max 16384) (skip 1)
            (acc (cdr *lgot-cache*)) (dicts nil) (allow 200))
  :breaks ()
  :mutations ((charges-the-covered-records
               (:conclusion
                (let ((fold0 (fn-lgo-fold (fn-lgk-committed ks) 0 acc dicts allow)))
                  (and (equal (mv-nth 0 run) (mv-nth 0 fold0))
                       (equal (mv-nth 1 run) (mv-nth 1 fold0))
                       (equal (fn-lgw-kernel (mv-nth 2 run)) (fn-lgc-of ks)))))
               ((c *lgot-seg*) (genesis *fn-lg-genesis*) (floor 1) (unit 4) (max 16384) (skip 1)
                (acc (cdr *lgot-cache*)) (dicts nil) (allow 200))
               :fault "the scan's fold drops the skip and charges the records the checkpoint already covers")))

; -----------------------------------------------------------------------------
; L2-2: over the open's segments, the fold over the chain's records.
(defteeth fn-lgo-chain-is-the-fold
  :claim (()
          (equal (fn-lgo-chain cs genesis unit max skip acc dicts allow)
                 (fn-lgo-fold (fn-lgs-chain-records cs genesis unit max) skip acc dicts allow)))
  :subject fn-lgo-chain
  :witness ((cs (list *lgot-seg1* *lgot-seg2*)) (genesis *fn-lg-genesis*) (unit 4) (max 16384)
            (skip 1) (acc (cdr *lgot-cache*)) (dicts nil) (allow 200))
  :breaks ()
  :mutations ((genesis-not-carried
               (:conclusion
                (equal (fn-lgo-chain cs genesis unit max skip acc dicts allow)
                       (fn-lgo-fold (append (car (fn-lg-scan (car cs) genesis unit max))
                                            (car (fn-lg-scan (cadr cs) genesis unit max)))
                                    skip acc dicts allow)))
               ((cs (list *lgot-seg1* *lgot-seg2*)) (genesis *fn-lg-genesis*) (unit 4) (max 16384)
                (skip 1) (acc (cdr *lgot-cache*)) (dicts nil) (allow 200))
               :fault "each segment scanned from the log's genesis instead of the trailer the one before ends on")))

; -----------------------------------------------------------------------------
; L2-3: a fold that does not refuse is ACC plus the wire fold past the skip.
(defteeth fn-lgo-fold-is-the-wire-fold
  :claim (let ((acc2 (mv-nth 1 (fn-lgo-fold zs skip acc dicts allow)))
               (xs (fn-lgo-expansions (nthcdr skip zs) dicts)))
           (((tot (fn-mm-tot-p acc))
             (ok (not (eq acc2 :bad))))
            (and (not (eq xs :bad))
                 (not (eq (fn-srs-decode xs) :bad))
                 (equal acc2 (fn-mm-tot-plus acc (fn-lgo-wire-fold (fn-srs-decode xs) allow))))))
  :subject fn-lgo-fold
  :witness ((zs *lgot-zs*) (skip 1) (acc (cdr *lgot-cache*)) (dicts nil) (allow 200))
  :breaks ((tot ((acc '(1 2 3)) (skip 4)))
           (ok ((zs (cons '(1 2 3 4 5) *lgot-zs*)) (skip 0))))
  :mutations ((wire-fold-from-the-start
               (:conclusion
                (let ((xs0 (fn-lgo-expansions zs dicts)))
                  (and (not (eq xs0 :bad))
                       (not (eq (fn-srs-decode xs0) :bad))
                       (equal acc2 (fn-mm-tot-plus acc (fn-lgo-wire-fold (fn-srs-decode xs0) allow))))))
               ((zs *lgot-zs*) (skip 1) (acc (cdr *lgot-cache*)) (dicts nil) (allow 200))
               :fault "the wire fold counted from the log's first record, not past the checkpoint's")))

; -----------------------------------------------------------------------------
; The stobj claims (L2-4, L2-5).  Each conjunct sits in the claim's LET*,
; whose binding interns over the arena; its native checker runs the same
; replay single-threaded and answers the conjunct, and defteeth proves the
; two equal before it runs any witness.

; The arena the open's earlier rows left: the payloads PRE sealed in order.
(defun lgot-presealed (pre fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom pre)
      fn-arena
    (let ((fn-arena (fn-arena-seal-list (car pre) fn-arena)))
      (lgot-presealed (cdr pre) fn-arena))))

; The statement epoch the replay of the first N history events leaves, with
; no rows: the suffix replay's ACC at K = N.
(defun lgot-epoch (n)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (acc fn-arena)
      (fn-ssr-intern-step *lgot-seed* (take n *lgot-ws*) nil nil :resident nil fn-arena)
      (if (eq acc :bad) :bad (fn-ssr-state nil (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) (fn-ssr-at 3 acc))))))
(defun lgot-rows-from (acc ws pre)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (acc1 fn-arena)
      (let ((fn-arena (lgot-presealed pre fn-arena)))
        (fn-ssr-intern-step acc ws nil nil :resident nil fn-arena))
      (fn-ssr-rows acc1))))
(defconst *lgot-pre3* (list (fn-record-payload (nth 1 *lgot-ws*))))
(defconst-eval *lgot-acc1* (lgot-epoch 1))
(defconst-eval *lgot-acc3* (lgot-epoch 3))
(defconst-eval *lgot-cache3* (cons 3 (fn-ct-charged (take 3 *lgot-rows*) :resident)))
; An epoch whose generation is not a natural (outside fn-ssr-statep, the
; replay's guard), whose identity context expects no sequence: the intern
; then builds an article row that is not a held row, and the replay keeps it.
(defun lgot-not-a-state (acc)
  (declare (xargs :verify-guards nil))
  (let ((c (fn-ssr-at 3 acc)))
    (fn-ssr-state nil (fn-ssr-at 1 acc) 'x
                  (fn-stxk-context :ok nil (fn-stxk-context-snapshots c) (fn-stxk-context-verdicts c)
                                   (fn-stxk-context-current-generation c) nil))))
(defconst-eval *lgot-seed-x* (lgot-not-a-state *lgot-seed*))
; An epoch that already holds a row.
(defconst-eval *lgot-seed-held*
  (fn-ssr-state (list (car *lgot-rows*)) (fn-ssr-at 1 *lgot-seed*) (fn-ssr-at 2 *lgot-seed*)
                (fn-ssr-at 3 *lgot-seed*)))

(assert-event
 (and (equal (lgot-rows-from *lgot-acc1* (nthcdr 1 *lgot-ws*) nil) (nthcdr 1 *lgot-rows*))
      (equal (lgot-rows-from *lgot-acc3* (nthcdr 3 *lgot-ws*) *lgot-pre3*) (nthcdr 3 *lgot-rows*)))
 :msg "the suffix replay from the epoch at K interns the rows past K")

(defun lgot4-check (i acc ws dicts allow fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (acc1 fn-arena) (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)
    (let ((rows (fn-ssr-rows acc1)))
      (mv (case i
        (0 (fn-ssr-statep acc))
        (1 (null (fn-ssr-at 0 acc)))
        (2 (not (eq acc1 :bad)))
        (3 (fn-lgo-rows-history-within rows allow))
        (4 (and (fn-lgo-agree-but-history (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow)) (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow))))
        (otherwise (equal (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow))))
          fn-arena))))

(defun lgot5-check (i cache rows zs j keyring generation identity dicts allow fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((k (car cache))
        (suffix (mv-nth 1 (mv-list 2 (fn-lgo-fold zs j (fn-ct-zero-tot :resident) dicts allow)))))
    (mv-let (acc1 fn-arena)
      (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity)
                          (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts))
                          nil nil :resident nil fn-arena)
      (mv (case i
        (0 (fn-ct-totals-cache-validp cache rows :resident))
        (1 (equal (nthcdr k rows) (fn-ssr-rows acc1)))
        (2 (fn-lgo-rows-history-within (nthcdr k rows) allow))
        (3 (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) suffix)))
        (otherwise (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) (mv-nth 1 (mv-list 2 (fn-lgo-fold (nthcdr j zs) j (fn-ct-zero-tot :resident) dicts allow)))))))
          fn-arena))))

; L2-4: the rows the suffix replay interns agree with the wire fold in eight
; fields and are bounded by it, every row within the HISTORY clause.
(defteeth fn-lgo-wire-fold-covers-the-replay
  :claim (let* ((acc1 (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)))
                (rows (fn-ssr-rows acc1)))
           (((st (fn-ssr-statep acc))
             (fresh (null (fn-ssr-at 0 acc)))
             (ok (not (eq acc1 :bad)))
             (within (fn-lgo-rows-history-within rows allow)))
            (and (fn-lgo-agree-but-history (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow))
                 (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow)))))
  :subject fn-ssr-intern-step
  :witness ((acc *lgot-seed*) (ws *lgot-ws*) (dicts nil) (allow 200) (pre nil))
  :stobjs ((fn-arena (lgot-presealed pre fn-arena)))
  :stobj-checks
  (
   ((let* ((acc1 (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))) (rows (fn-ssr-rows acc1))) (declare (ignorable acc1 rows)) (fn-ssr-statep acc))
    (lgot4-check 0 acc ws dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot4-check) (theory 'minimal-theory)))))
   ((let* ((acc1 (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))) (rows (fn-ssr-rows acc1))) (declare (ignorable acc1 rows)) (null (fn-ssr-at 0 acc)))
    (lgot4-check 1 acc ws dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot4-check) (theory 'minimal-theory)))))
   ((let* ((acc1 (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))) (rows (fn-ssr-rows acc1))) (declare (ignorable acc1 rows)) (not (eq acc1 :bad)))
    (lgot4-check 2 acc ws dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot4-check) (theory 'minimal-theory)))))
   ((let* ((acc1 (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))) (rows (fn-ssr-rows acc1))) (declare (ignorable acc1 rows)) (fn-lgo-rows-history-within rows allow))
    (lgot4-check 3 acc ws dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot4-check) (theory 'minimal-theory)))))
   ((let* ((acc1 (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))) (rows (fn-ssr-rows acc1))) (declare (ignorable acc1 rows)) (and (fn-lgo-agree-but-history (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow)) (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow))))
    (lgot4-check 4 acc ws dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot4-check) (theory 'minimal-theory)))))
   ((let* ((acc1 (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))) (rows (fn-ssr-rows acc1))) (declare (ignorable acc1 rows)) (equal (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow)))
    (lgot4-check 5 acc ws dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot4-check) (theory 'minimal-theory))))))
  :breaks ((st ((acc *lgot-seed-x*) (ws (list (nth 1 *lgot-ws*))) (allow 1000000)) :logical "a replay state's generation is a natural (fn-ssr-statep, the replay's guard)")
           (fresh ((acc *lgot-seed-held*)))
           (ok ((ws (list :not-an-event))))
           (within ((acc *lgot-acc1*) (ws (list (nth 1 *lgot-ws*))) (allow 0))))
  :mutations ((history-claimed-exact
               (:conclusion (equal (fn-ct-charged rows :resident) (fn-lgo-wire-fold ws allow)))
               ((acc *lgot-seed*) (ws *lgot-ws*) (dicts nil) (allow 200))
               :fault "the scan's totals claimed equal to the opened store's in all nine fields, HISTORY included, which reads the handle and the statement context the log past S does not carry (seam L-M-A)")))

; L2-5: from a valid cache, the scan's total bounds the opened store's
; charged fold; the suffix replay starts from the epoch at K with no rows.
(defteeth fn-lgo-observed-covers-the-opened-store
  :claim (let* ((k (car cache))
                (suffix (mv-nth 1 (fn-lgo-fold zs j (fn-ct-zero-tot :resident) dicts allow)))
                (acc1 (mv-nth 0 (fn-ssr-intern-step
                                 (fn-ssr-state nil keyring (nfix generation) identity)
                                 (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts))
                                 nil nil :resident nil fn-arena))))
           (((valid (fn-ct-totals-cache-validp cache rows :resident))
             (tail (equal (nthcdr k rows) (fn-ssr-rows acc1)))
             (within (fn-lgo-rows-history-within (nthcdr k rows) allow)))
            (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) suffix))))
  :subject fn-lgo-fold
  :witness ((cache *lgot-cache*) (rows *lgot-rows*) (zs *lgot-zs*) (j 1) (keyring (fn-ssr-at 1 *lgot-acc1*)) (generation (fn-ssr-at 2 *lgot-acc1*)) (identity (fn-ssr-at 3 *lgot-acc1*))
            (dicts nil) (allow 200) (pre nil))
  :stobjs ((fn-arena (lgot-presealed pre fn-arena)))
  :stobj-checks
  (
   ((let* ((k (car cache)) (suffix (mv-nth 1 (fn-lgo-fold zs j (fn-ct-zero-tot :resident) dicts allow))) (acc1 (mv-nth 0 (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity) (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)) nil nil :resident nil fn-arena)))) (declare (ignorable k suffix acc1)) (fn-ct-totals-cache-validp cache rows :resident))
    (lgot5-check 0 cache rows zs j keyring generation identity dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot5-check mv-list) (theory 'minimal-theory)))))
   ((let* ((k (car cache)) (suffix (mv-nth 1 (fn-lgo-fold zs j (fn-ct-zero-tot :resident) dicts allow))) (acc1 (mv-nth 0 (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity) (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)) nil nil :resident nil fn-arena)))) (declare (ignorable k suffix acc1)) (equal (nthcdr k rows) (fn-ssr-rows acc1)))
    (lgot5-check 1 cache rows zs j keyring generation identity dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot5-check mv-list) (theory 'minimal-theory)))))
   ((let* ((k (car cache)) (suffix (mv-nth 1 (fn-lgo-fold zs j (fn-ct-zero-tot :resident) dicts allow))) (acc1 (mv-nth 0 (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity) (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)) nil nil :resident nil fn-arena)))) (declare (ignorable k suffix acc1)) (fn-lgo-rows-history-within (nthcdr k rows) allow))
    (lgot5-check 2 cache rows zs j keyring generation identity dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot5-check mv-list) (theory 'minimal-theory)))))
   ((let* ((k (car cache)) (suffix (mv-nth 1 (fn-lgo-fold zs j (fn-ct-zero-tot :resident) dicts allow))) (acc1 (mv-nth 0 (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity) (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)) nil nil :resident nil fn-arena)))) (declare (ignorable k suffix acc1)) (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) suffix)))
    (lgot5-check 3 cache rows zs j keyring generation identity dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot5-check mv-list) (theory 'minimal-theory)))))
   ((let* ((k (car cache)) (suffix (mv-nth 1 (fn-lgo-fold zs j (fn-ct-zero-tot :resident) dicts allow))) (acc1 (mv-nth 0 (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity) (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)) nil nil :resident nil fn-arena)))) (declare (ignorable k suffix acc1)) (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) (mv-nth 1 (fn-lgo-fold (nthcdr j zs) j (fn-ct-zero-tot :resident) dicts allow)))))
    (lgot5-check 4 cache rows zs j keyring generation identity dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot5-check mv-list) (theory 'minimal-theory))))))
  :breaks ((valid ((cache (cons 1 (fn-ct-zero-tot :resident)))))
           (tail ((rows (append *lgot-rows* (list (car *lgot-rows*))))))
           (within ((cache *lgot-cache3*) (j 3) (keyring (fn-ssr-at 1 *lgot-acc3*)) (generation (fn-ssr-at 2 *lgot-acc3*)) (identity (fn-ssr-at 3 *lgot-acc3*)) (allow 0) (pre *lgot-pre3*))))
  :mutations ((prefix-skipped-twice
               (:conclusion
                (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) (mv-nth 1 (fn-lgo-fold (nthcdr j zs) j (fn-ct-zero-tot :resident) dicts allow)))))
               ((cache *lgot-cache*) (rows *lgot-rows*) (zs *lgot-zs*) (j 1) (keyring (fn-ssr-at 1 *lgot-acc1*)) (generation (fn-ssr-at 2 *lgot-acc1*)) (identity (fn-ssr-at 3 *lgot-acc1*))
                (dicts nil) (allow 200) (pre nil))
               :fault "the host trims the log to the suffix and the scan skips the checkpoint's records again (Codex l-l2a F2)")))

; -----------------------------------------------------------------------------
; Landing 2a-host: the probe's scan before the open (L2H-1 to L2H-3).

; L2H-1: from skip 0 the fold bounds the fold from any skip.
(defteeth fn-lgo-fold-from-no-skip-bounds-any-skip
  :claim (((le (fn-mm-tot-le a b))
           (tot (not (equal a :bad)))
           (ok (not (equal (mv-nth 1 (fn-lgo-fold zs 0 b dicts allow)) :bad))))
          (and (not (equal (mv-nth 1 (fn-lgo-fold zs j a dicts allow)) :bad))
               (fn-mm-tot-le (mv-nth 1 (fn-lgo-fold zs j a dicts allow))
                             (mv-nth 1 (fn-lgo-fold zs 0 b dicts allow)))))
  :subject fn-lgo-fold
  :witness ((zs *lgot-zs*) (j 1) (a (fn-ct-zero-tot :resident)) (b (fn-ct-zero-tot :resident))
            (dicts nil) (allow 200))
  :breaks ((le ((a (fn-mm-make-tot 1000 0 0 0 0 0 0 0 :resident))))
           (tot ((a :bad)))
           (ok ((zs (cons '(1 2 3 4 5) *lgot-zs*)))))
  :mutations ((skip-blind
               (:conclusion
                (equal (mv-nth 1 (fn-lgo-fold zs j a dicts allow))
                       (mv-nth 1 (fn-lgo-fold zs 0 b dicts allow))))
               ((zs *lgot-zs*) (j 1) (a (fn-ct-zero-tot :resident)) (b (fn-ct-zero-tot :resident))
                (dicts nil) (allow 200))
               :fault "the skip claimed not to matter: the covered records charged as if past S")))

; L2H-3: the plan scans every present segment; skip S only from the genesis.
(defteeth fn-lgo-scan-plan-scans-every-present-segment
  :claim (let ((p (fn-lgo-scan-plan names s)))
           (((planned p))
            (and (subsetp-equal (fn-lgs-indices names) (third p))
                 (equal (third p) (fn-lgs-range (second p) (fn-lgs-max-index (fn-lgs-indices names) 0)))
                 (iff (equal (car p) :genesis) (member-equal 1 (fn-lgs-indices names)))
                 (equal (fourth p) (if (equal (car p) :genesis) (nfix s) 0))
                 (equal (fifth p) (fn-ct-zero-tot :resident)))))
  :subject fn-lgo-scan-plan
  :witness ((names (list "000000.log" "000002.log" "000003.log")) (s 3))
  :breaks ((planned ((names (list "000000.log" "000001.log" "000003.log")))))
  :mutations ((skip-s-past-a-drop
               (:conclusion
                (and (subsetp-equal (fn-lgs-indices names) (third p))
                     (equal (fourth p) (nfix s))))
               ((names (list "000000.log" "000002.log" "000003.log")) (s 3))
               :fault "the probe skips S records from the lowest present segment after the drop took the covered ones: the suffix's records go uncharged")))

(assert-event
 (and (equal (fn-lgo-scan-plan (list "000000.log" "000001.log" "000002.log") 3) (list :genesis 1 '(1 2) 3 (fn-ct-zero-tot :resident)))
      (equal (fn-lgo-scan-plan (list "000000.log" "000002.log" "000003.log") 3) (list :head 2 '(2 3) 0 (fn-ct-zero-tot :resident))))
 :msg "the plan: from the genesis with skip S when segment 1 is present, from segment 2's head with skip 0 when the drop took it")

; L2H-2: the open's records are PRE (the dropped segment's, the first two)
; then REST (the host's scan); the checkpoint at K = 3 covers one record of
; REST, which the host's skip-0 suffix over-counts: a bound, not equal.
(defun lgot6-check (i cache rows pre rest j keyring generation identity dicts allow fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((k (car cache))
        (host (mv-nth 1 (mv-list 2 (fn-lgo-fold rest 0 (fn-ct-zero-tot :resident) dicts allow)))))
    (mv-let (acc1 fn-arena)
      (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity)
                          (fn-srs-decode (fn-lgo-expansions (nthcdr j (append pre rest)) dicts))
                          nil nil :resident nil fn-arena)
      (mv (case i
        (0 (<= (len pre) (nfix j)))
        (1 (not (equal host :bad)))
        (2 (fn-ct-totals-cache-validp cache rows :resident))
        (3 (equal (nthcdr k rows) (fn-ssr-rows acc1)))
        (4 (fn-lgo-rows-history-within (nthcdr k rows) allow))
        (5 (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) host)))
        (otherwise (equal (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) host))))
          fn-arena))))
;
(defteeth fn-lgo-host-suffix-covers-the-opened-store
  :claim (let* ((k (car cache))
                (zs (append pre rest))
                (host (mv-nth 1 (fn-lgo-fold rest 0 (fn-ct-zero-tot :resident) dicts allow)))
                (acc1 (mv-nth 0 (fn-ssr-intern-step
                                 (fn-ssr-state nil keyring (nfix generation) identity)
                                 (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts))
                                 nil nil :resident nil fn-arena))))
           (((dropped (<= (len pre) (nfix j)))
             (seen (not (equal host :bad)))
             (valid (fn-ct-totals-cache-validp cache rows :resident))
             (tail (equal (nthcdr k rows) (fn-ssr-rows acc1)))
             (within (fn-lgo-rows-history-within (nthcdr k rows) allow)))
            (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) host))))
  :subject fn-lgo-fold
  :witness ((cache *lgot-cache3*) (rows *lgot-rows*) (pre (take 2 *lgot-zs*)) (rest (nthcdr 2 *lgot-zs*)) (j 3) (keyring (fn-ssr-at 1 *lgot-acc3*)) (generation (fn-ssr-at 2 *lgot-acc3*)) (identity (fn-ssr-at 3 *lgot-acc3*)) (dicts nil) (allow 200) (sealed *lgot-pre3*))
  :stobjs ((fn-arena (lgot-presealed sealed fn-arena)))
  :stobj-checks
  (
   ((let* ((k (car cache)) (zs (append pre rest)) (host (mv-nth 1 (fn-lgo-fold rest 0 (fn-ct-zero-tot :resident) dicts allow))) (acc1 (mv-nth 0 (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity) (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)) nil nil :resident nil fn-arena)))) (declare (ignorable k zs host acc1)) (<= (len pre) (nfix j)))
    (lgot6-check 0 cache rows pre rest j keyring generation identity dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot6-check mv-list) (theory 'minimal-theory)))))
   ((let* ((k (car cache)) (zs (append pre rest)) (host (mv-nth 1 (fn-lgo-fold rest 0 (fn-ct-zero-tot :resident) dicts allow))) (acc1 (mv-nth 0 (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity) (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)) nil nil :resident nil fn-arena)))) (declare (ignorable k zs host acc1)) (not (equal host :bad)))
    (lgot6-check 1 cache rows pre rest j keyring generation identity dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot6-check mv-list) (theory 'minimal-theory)))))
   ((let* ((k (car cache)) (zs (append pre rest)) (host (mv-nth 1 (fn-lgo-fold rest 0 (fn-ct-zero-tot :resident) dicts allow))) (acc1 (mv-nth 0 (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity) (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)) nil nil :resident nil fn-arena)))) (declare (ignorable k zs host acc1)) (fn-ct-totals-cache-validp cache rows :resident))
    (lgot6-check 2 cache rows pre rest j keyring generation identity dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot6-check mv-list) (theory 'minimal-theory)))))
   ((let* ((k (car cache)) (zs (append pre rest)) (host (mv-nth 1 (fn-lgo-fold rest 0 (fn-ct-zero-tot :resident) dicts allow))) (acc1 (mv-nth 0 (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity) (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)) nil nil :resident nil fn-arena)))) (declare (ignorable k zs host acc1)) (equal (nthcdr k rows) (fn-ssr-rows acc1)))
    (lgot6-check 3 cache rows pre rest j keyring generation identity dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot6-check mv-list) (theory 'minimal-theory)))))
   ((let* ((k (car cache)) (zs (append pre rest)) (host (mv-nth 1 (fn-lgo-fold rest 0 (fn-ct-zero-tot :resident) dicts allow))) (acc1 (mv-nth 0 (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity) (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)) nil nil :resident nil fn-arena)))) (declare (ignorable k zs host acc1)) (fn-lgo-rows-history-within (nthcdr k rows) allow))
    (lgot6-check 4 cache rows pre rest j keyring generation identity dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot6-check mv-list) (theory 'minimal-theory)))))
   ((let* ((k (car cache)) (zs (append pre rest)) (host (mv-nth 1 (fn-lgo-fold rest 0 (fn-ct-zero-tot :resident) dicts allow))) (acc1 (mv-nth 0 (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity) (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)) nil nil :resident nil fn-arena)))) (declare (ignorable k zs host acc1)) (fn-mm-tot-le (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) host)))
    (lgot6-check 5 cache rows pre rest j keyring generation identity dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot6-check mv-list) (theory 'minimal-theory)))))
   ((let* ((k (car cache)) (zs (append pre rest)) (host (mv-nth 1 (fn-lgo-fold rest 0 (fn-ct-zero-tot :resident) dicts allow))) (acc1 (mv-nth 0 (fn-ssr-intern-step (fn-ssr-state nil keyring (nfix generation) identity) (fn-srs-decode (fn-lgo-expansions (nthcdr j zs) dicts)) nil nil :resident nil fn-arena)))) (declare (ignorable k zs host acc1)) (equal (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) host)))
    (lgot6-check 6 cache rows pre rest j keyring generation identity dicts allow fn-arena)
    :hints (("Goal" :in-theory (union-theories '(lgot6-check mv-list) (theory 'minimal-theory))))))
  :breaks ((dropped ((pre *lgot-zs*) (rest nil)))
           (seen ((pre (take 1 *lgot-zs*)) (rest (cons '(1 2 3 4 5) (nthcdr 1 *lgot-zs*))) (j 4)))
           (valid ((cache (cons 3 (fn-ct-zero-tot :resident)))))
           (tail ((pre (take 3 *lgot-zs*)) (rest (nthcdr 3 *lgot-zs*)) (rows (append *lgot-rows* (list (nth 3 *lgot-rows*))))))
           (within ((pre (take 3 *lgot-zs*)) (rest (nthcdr 3 *lgot-zs*)) (allow 0))))
  :mutations ((the-bound-claimed-exact
               (:conclusion (equal (fn-ct-charged rows :resident) (fn-mm-tot-plus (cdr cache) host)))
               ((cache *lgot-cache3*) (rows *lgot-rows*) (pre (take 2 *lgot-zs*)) (rest (nthcdr 2 *lgot-zs*)) (j 3) (keyring (fn-ssr-at 1 *lgot-acc3*)) (generation (fn-ssr-at 2 *lgot-acc3*)) (identity (fn-ssr-at 3 *lgot-acc3*)) (dicts nil) (allow 200) (sealed *lgot-pre3*))
               :fault "the probe's suffix claimed equal to the open's after a drop: the covered records an interrupted drop leaves are over-counted, so it is a bound")))

(defteeth-check (fn-lgo-run-is-the-fold fn-lgo-chain-is-the-fold fn-lgo-fold-is-the-wire-fold
                 fn-lgo-wire-fold-covers-the-replay fn-lgo-observed-covers-the-opened-store
                 fn-lgo-fold-from-no-skip-bounds-any-skip fn-lgo-scan-plan-scans-every-present-segment
                 fn-lgo-host-suffix-covers-the-opened-store))
