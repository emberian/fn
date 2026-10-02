; fn test fixture, never certified and never in an image: a state checkpoint
; re-written with one group's article-number watermark past
; *fn-nntp-max-article-number*, re-sealed by fn's own codec.
;
; No store verb sets a watermark and replay only increments one, so the
; damaged store the open must refuse (books/owner-number-bound.lisp
; fn-onb-open-okp, :article-numbers-damaged) is built here: the file a
; writer published is split into its segments, the arena run is kept as
; written, the four tables (books/store-checkpoint-tables.lisp) are decoded
; with the reader's list-level `fn-sct-decode-file', the node's nexts are
; replaced, and the tables are re-encoded with `fn-sct-table-programs' and
; `fn-sct-file-octets' (the writer's codec, chained from the genesis and
; sealed with the BLAKE3 books/crypto-attach.lisp attaches).  The result is
; decoded again and compared with the damaged tables before it is written.
;
; Driven by tools/fixtures/damaged_checkpoint.py, which first includes
; books/store-checkpoint-tables, books/history-image-snapshot and
; books/crypto-attach.

(set-guard-checking :none)
(program)

(defun fx-read-octets (channel acc state)
  (declare (xargs :stobjs state))
  (mv-let (b state) (read-byte$ channel state)
    (if (null b)
        (mv (reverse acc) state)
      (fx-read-octets channel (cons b acc) state))))

(defun fx-write-octets (xs channel state)
  (declare (xargs :stobjs state))
  (if (endp xs)
      state
    (let ((state (write-byte$ (car xs) channel state)))
      (fx-write-octets (cdr xs) channel state))))

; The file's segments by their headers' extents, or :bad.
(defun fx-split (xs acc)
  (if (endp xs)
      (reverse acc)
    (let ((e (and (<= *fn-scc-segment-header-octets* (len xs))
                  (fn-scc-segment-extent (take *fn-scc-segment-header-octets* xs)))))
      (if (or (not (posp e)) (< (len xs) e))
          :bad
        (fx-split (nthcdr e xs) (cons (take e xs) acc))))))

(defun fx-max-chunk (segs acc)
  (if (endp segs)
      acc
    (fx-max-chunk (cdr segs) (max acc (nth 2 (fn-scc-parse-header (car segs)))))))

(defun fx-subst (new old x)
  (cond ((equal x old) new)
        ((atom x) x)
        (t (cons (fx-subst new old (car x)) (fx-subst new old (cdr x))))))

(defun fx-node-nexts (tables)
  (fn-state-nexts
   (fn-node-acceptance
    (fn-cnode-node (fn-sco-at 1 (fn-sco-at 0 (fn-sct-tables-r tables)))))))

; The tables with the first group's watermark set to V, or a refusal.
(defun fx-damage-tables (tables v)
  (let* ((r (fn-sct-tables-r tables))
         (cpr (fn-sco-at 0 r))
         (old (fx-node-nexts tables)))
    (cond ((not (fn-sco-pausedp cpr)) (list :refused :not-paused))
          ((not (and (consp old) (consp (car old)))) (list :refused :no-group))
          (t (let* ((new (cons (cons (caar old) v) (cdr old)))
                    (r2 (list (fx-subst new old cpr) (fn-sco-at 1 r) (fn-sco-at 2 r)
                              (fn-sco-at 3 r)))
                    (tables2 (list (fn-sct-tables-f tables) (fn-sct-tables-p tables)
                                   (fn-sct-tables-e tables) r2)))
               (if (equal (fx-node-nexts tables2) new)
                   (list :ok tables2 (caar old) (cdar old))
                 (list :refused :nexts-not-replaced)))))))

(defun fx-damage-segments (xs v)
  (let ((segs (fx-split xs nil)))
    (if (or (eq segs :bad) (not (consp segs)))
        (list :refused :segments)
      (let* ((h (fn-scc-parse-header (car segs)))
             (arena-count (and h (nth 1 h))))
        (if (not (and (posp arena-count)
                      (equal (take 4 (nthcdr *fn-scc-segment-header-octets* (car segs)))
                             '(102 110 65 49))))
            (list :refused :no-arena-run)
          (let* ((rest (nthcdr arena-count segs))
                 (dec (fn-sct-decode-file rest)))
            (if (not (eq (car dec) :ok))
                (list :refused :decode dec)
              (let ((d (fx-damage-tables (cadr dec) v)))
                (if (not (eq (car d) :ok))
                    d
                  (let* ((tables2 (nth 1 d))
                         (s (fn-sco-at 1 (fn-sct-tables-f tables2)))
                         (index (fn-sco-event-index (fn-sct-capture-of-tables tables2)))
                         (octets (fn-sct-file-octets (fn-sct-table-programs tables2 index)
                                                     (fx-max-chunk rest 1) s))
                         (again (fx-split octets nil)))
                    (if (not (and (not (eq again :bad))
                                  (equal (fn-sct-decode-file again) (list :ok tables2))))
                        (list :refused :round-trip)
                      (list :ok (append (fn-scc-concat (take arena-count segs)) octets)
                            (nth 2 d) (nth 3 d)))))))))))))

; A file that carries a history image region (books/history-image-snapshot.lisp)
; starts with it; the region is kept as written and the framed segments
; after it (fn-his-region-octets) are what is split, as the open skips it
; (fn-his-image-header-np, fn-his-skip-octets).
(defun fx-image-region (xs)
  (let ((np (and (<= *fn-his-header-octets* (len xs))
                 (fn-his-image-header-np (take *fn-his-header-octets* xs)))))
    (if (and (natp np) (<= (fn-his-region-octets np) (len xs)))
        (take (fn-his-region-octets np) xs)
      nil)))

(defun fx-damage-octets (xs v)
  (let ((region (fx-image-region xs)))
    (let ((d (fx-damage-segments (nthcdr (len region) xs) v)))
      (if (eq (car d) :ok)
          (list :ok (append region (nth 1 d)) (nth 2 d) (nth 3 d))
        d))))

(defun fx-damage-file (in out v state)
  (declare (xargs :stobjs state))
  (mv-let (ch state) (open-input-channel in :byte state)
    (if (not ch)
        (mv (list :refused :open-input) state)
      (mv-let (xs state) (fx-read-octets ch nil state)
        (let* ((state (close-input-channel ch state))
               (d (fx-damage-octets xs v)))
          (if (not (eq (car d) :ok))
              (mv d state)
            (mv-let (och state) (open-output-channel out :byte state)
              (if (not och)
                  (mv (list :refused :open-output) state)
                (let* ((state (fx-write-octets (nth 1 d) och state))
                       (state (close-output-channel och state)))
                  (mv (list :ok (nth 2 d) (nth 3 d)) state))))))))))
