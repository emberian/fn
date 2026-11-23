;; One bounded rolling SOURCE span into the upload's storage page.  The
;; upload machine calls fn2-upload-stream-stage-events after its core exists.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "upload")
(fn2-book-layer :d)

 ;; Actual byte-array touches: one read for stored B3 plus read/write for
;; the copy; at most four delimiter reads and 32 final digest writes.
(defconst *fn2-upload-stream-stage-overhead* (+ 4 *fn2-upload-digest-octets*))
(defconst *fn2-upload-stream-stage-quantum*
 (min *fn2-upload-hash-bytes*
      (floor (nfix (- *fn2-upload-run-bytes* *fn2-upload-stream-stage-overhead*)) 3)))
(defconst *fn2-upload-stream-stage-work*
 (+ (* 3 *fn2-upload-stream-stage-quantum*) *fn2-upload-stream-stage-overhead*))
(assert-event (equal *fn2-upload-stream-stage-quantum* 1353))
(assert-event (and (posp *fn2-upload-stream-stage-quantum*)
                   (<= *fn2-upload-stream-stage-work* *fn2-upload-run-bytes*)))

(defcost fn2-upload-stream-stage :answers (:ok :idle :fault)
  :faults (:fault)
  :bytes *fn2-upload-stream-stage-work*
  :tables (fn2-core-machines fn2-core-machine-tables fn2-upload-table
           fn2-core-pool fn2-core-b3 fn2-core-digests)
  :own-writes (stored-hashed stream-stage-used stream-stored-finalized)
  :doc "Hash and stage one available stored-stream span, or finalize its digest at EOF.")

(defmacro fn2-upload-stream-stage-events ()
 '(progn
;; No work can be borrowed from a future C1 window.  C0's actual filled
;; delimiter is the fixed header boundary; C1 holds only the resident tail
;; of STREAM-END.  Thus SOURCE-CURSOR must be in C0 or the current C1 range.
(defun fn2-upload-stream-stage (id gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (and (eq (fn2-upload-snapshot-read-code id fn2-core) :ok)
                     (equal (fn2-machine-generation id fn2-core) gen)
                     (equal (fn2-upload-row-lease id fn2-core) *fn2-upload-lease-held*)
                     (equal (fn2-upload-row-word id fn2-core) 0)))
        (mv :fault 0 fn2-core))
       (ls (fn2-upload-row-lslot id fn2-core))
       (lg (fn2-upload-row-lgen id fn2-core))
       (c0 (fn2-upload-row-c0-slot id fn2-core))
       (g0 (fn2-upload-row-c0-gen id fn2-core))
       (c1 (fn2-upload-row-c1-slot id fn2-core))
       (g1 (fn2-upload-row-c1-gen id fn2-core))
       (ilen (fn2-upload-row-ilen id fn2-core))
       (cursor (fn2-upload-row-stored-hashed id fn2-core))
       (used (fn2-upload-row-stream-stage-used id fn2-core))
       (stream-end (fn2-upload-row-stream-end id fn2-core))
       (eof (equal (fn2-upload-row-stream-eof id fn2-core) 1))
       ((mv geometry header-ready header-fill body-fill)
        (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (ok ready h b)
          (b* ((h (fn2-gram-fill c0 fn2-pool))
               (b (fn2-gram-fill c1 fn2-pool))
               ((mv tail-code ready)
                (fn2-feed-header-complete-p c0 g0 *fn2-upload-kind* id gen fn2-pool))
               (ok (and (eq tail-code :ok)
                        (eq (fn2-pool-workspace-code c0 g0 *fn2-upload-kind* id gen fn2-pool) :ok)
                        (eq (fn2-pool-workspace-code c1 g1 *fn2-upload-kind* id gen fn2-pool) :ok)
                        (eq (fn2-pool-workspace-code ls lg *fn2-upload-kind* id gen fn2-pool) :ok))))
            (mv ok ready h b))
          (mv ok ready h b)))
       ((unless (and geometry header-ready
                     (<= header-fill *fn2-upload-header-octets*)
                     (<= body-fill *fn2-upload-body-window-bytes*)
                     (<= ilen *fn2-upload-page-stored-source*)
                     (<= used *fn2-commit-unit-bytes*)
                     (<= (+ header-fill body-fill) stream-end)
                     (<= cursor (+ ilen stream-end))))
        (mv :fault 0 fn2-core))
       (body-base (- stream-end body-fill))
       (total (+ ilen stream-end))
       (source-cursor (nfix (- cursor ilen)))
       (hrow (fn2-upload-stored-hasher id fn2-core))
       ;; EOF may arrive after the hasher caught up with all currently
       ;; available octets.  Finalize without consuming or staging a span.
       ((when (and eof (equal cursor total)))
        (b* ((digest-ready
              (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (ok)
                (fn2-pool-range-in ls *fn2-upload-page-stored-source*
                                   *fn2-upload-digest-octets* fn2-pool)
                ok))
             ((unless digest-ready) (mv :fault 0 fn2-core))
             ((mv code fn2-core) (fn2-upload-hash-end hrow fn2-core))
             ((unless (eq code :ok)) (mv :fault 0 fn2-core))
             ((mv code fn2-core)
              (fn2-upload-digest-store hrow ls lg *fn2-upload-page-stored-source* id gen fn2-core)))
          (let ((fn2-core (if (eq code :ok)
                              (fn2-machine-write-stream-stored-finalized id 1 fn2-core) fn2-core)))
            (mv (if (eq code :ok) :ok :fault) 0 fn2-core))))
       ((when (equal used *fn2-commit-unit-bytes*)) (mv :idle 0 fn2-core))
       (prefix (< cursor ilen))
       (header (and (not prefix) (< source-cursor header-fill)))
       (body (and (not prefix) (not header)
                  (<= body-base source-cursor) (< source-cursor stream-end)))
       ((unless (or prefix header body))
        (mv (if (equal source-cursor stream-end) :idle :fault) 0 fn2-core))
       (src (cond (prefix ls) (header c0) (t c1)))
       (src-gen (cond (prefix lg) (header g0) (t g1)))
       (off (cond (prefix cursor) (header source-cursor)
                  (t (- source-cursor body-base))))
       (available (cond (prefix (- ilen cursor))
                        (header (- header-fill source-cursor))
                        (t (- stream-end source-cursor))))
       (length (min *fn2-upload-stream-stage-quantum* (min (- *fn2-commit-unit-bytes* used) available)))
       (stage-off (+ *fn2-upload-page-stage* used))
       ((unless (posp length)) (mv :idle 0 fn2-core))
       ;; All handles, ownership, filled source octets and destination range
       ;; are checked before the B3 context advances.  The page stage was
       ;; zero-filled by the controller, so the destination is in fill.
       (preflight
        (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (ok)
          (and (eq (fn2-pool-workspace-code src src-gen *fn2-upload-kind* id gen fn2-pool) :ok)
               (eq (fn2-pool-workspace-code ls lg *fn2-upload-kind* id gen fn2-pool) :ok)
               (fn2-pool-range-in src off length fn2-pool)
               (fn2-pool-range-in ls stage-off length fn2-pool)
               (fn2-pool-range-in ls *fn2-upload-page-stored-source* *fn2-upload-digest-octets* fn2-pool))
          ok))
       ((unless preflight) (mv :fault 0 fn2-core))
       (last (and eof (equal (+ cursor length) total)))
       ((mv hcode fn2-core)
        (fn2-upload-stored-hash hrow src src-gen off cursor length last ls lg
                                *fn2-upload-kind* id gen fn2-core))
       ((unless (eq hcode :ok)) (mv :fault 0 fn2-core))
       ((mv ccode fn2-core)
        (fn2-core-copy-range src src-gen off ls lg stage-off length
                             *fn2-upload-kind* id gen fn2-core))
       ((unless (eq ccode :ok)) (mv :fault 0 fn2-core))
       (fn2-core (if last (fn2-machine-write-stream-stored-finalized id 1 fn2-core) fn2-core))
       (fn2-core (fn2-machine-write-stored-hashed id (+ cursor length) fn2-core))
       (fn2-core (fn2-machine-write-stream-stage-used id (+ used length) fn2-core)))
    (mv :ok length fn2-core)))
(fn2-core-preserves fn2-upload-stream-stage (id gen fn2-core) :position 2 :rows nil)
(in-theory (disable fn2-upload-stream-stage))))
