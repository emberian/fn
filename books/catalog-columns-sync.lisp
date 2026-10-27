;; Route A2: keeping the LB columns in step with fn-cat.  fn-lbc-sync
;; catches the columns up to the catalog from outside, so no proved
;; signature that takes fn-cat changes: the withdrawals since the columns'
;; last horizon (fn-cat-withdrawn-at per version) are applied to the rows
;; the columns already hold, then the rows past the columns' count are
;; committed, then the horizon is recorded.  A catalog that is smaller than
;; the columns, or replaced (reclaim, clear), is a fn-lbc-reset first.  The
;; horizon lives in the summary dense map under the group key :HORIZON.
;; Locators are 0 here: the arena extent supplies them when a read arm needs
;; a payload range (DESIGN D-6).
(in-package "ACL2")
(include-book "catalog")
(include-book "catalog-columns-load")

(defun fn-lbc-horizon (fn-lbc)
  (declare (xargs :stobjs fn-lbc :mode :program))
  (fn-lbc-summary-word :horizon 1 fn-lbc))

(defun fn-lbc-reset (fn-lbc)
  (declare (xargs :stobjs fn-lbc :mode :program))
  (let* ((fn-lbc (fn-lbc-clear-columns fn-lbc))
         (fn-lbc (fn-lbc-slots-ensure fn-lbc)))
    (fn-lbc-summary-put :horizon (list 0) 1 fn-lbc)))

(defun fn-cat-clear-and-columns (fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-cat fn-lbc) :mode :program))
  (let* ((fn-cat (fn-cat-clear fn-cat))
         (fn-lbc (fn-lbc-reset fn-lbc)))
    (mv fn-cat fn-lbc)))

(defun fn-cat-clear-keyed-and-columns (key fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-cat fn-lbc) :mode :program))
  (let* ((fn-cat (fn-cat-clear-keyed key fn-cat))
         (fn-lbc (fn-lbc-reset fn-lbc)))
    (mv fn-cat fn-lbc)))

(defun fn-lbc-sync-withdrawn (seqs m fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-cat fn-lbc) :mode :program))
  (if (atom seqs) fn-lbc
    (let* ((seq (car seqs))
           (fn-lbc (if (< seq m)
                       (let ((pair (fn-held-withdrawn (fn-cat-at seq fn-cat))))
                         (fn-lbc-withdraw-row seq (car pair) (cdr pair) fn-lbc))
                     fn-lbc)))
      (fn-lbc-sync-withdrawn (cdr seqs) m fn-cat fn-lbc))))

(defun fn-lbc-sync-versions (w hz m fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-cat fn-lbc) :mode :program))
  (if (>= w hz) fn-lbc
    (let ((fn-lbc (fn-lbc-sync-withdrawn (fn-cat-withdrawn-at w fn-cat) m fn-cat fn-lbc)))
      (fn-lbc-sync-versions (+ w 1) hz m fn-cat fn-lbc))))

(defun fn-lbc-sync-commits (i n fn-arena fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-arena fn-cat fn-lbc) :mode :program))
  (if (>= i n) fn-lbc
    (let* ((row (fn-cat-at i fn-cat))
           (payload (fn-nntp-payload-bytes (fn-record-payload row) fn-arena))
           (fn-lbc (fn-lbc-commit-row row payload 0 0 nil fn-lbc)))
      (fn-lbc-sync-commits (+ i 1) n fn-arena fn-cat fn-lbc))))

; A withdrawal's version is the catalog's count when it happens, so a
; withdrawal after the last sync can share the last synced version (horizon
; is 1 + the greatest version): the scan restarts one version back.  The
; columns' withdraw is a no-op on an already withdrawn row, so the rescan of
; that version costs only its own bucket.
(defun fn-lbc-sync-from (horizon)
  (declare (xargs :mode :program))
  (if (zp horizon) 0 (- horizon 1)))

(defun fn-lbc-sync (fn-arena fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-arena fn-cat fn-lbc) :mode :program))
  (let* ((fn-lbc (if (< (fn-cat-count fn-cat) (fn-lbc-count fn-lbc)) (fn-lbc-reset fn-lbc) fn-lbc))
         (m (fn-lbc-count fn-lbc))
         (hz (fn-cat-horizon fn-cat))
         (fn-lbc (fn-lbc-sync-versions (fn-lbc-sync-from (fn-lbc-horizon fn-lbc)) hz m fn-cat fn-lbc))
         (fn-lbc (fn-lbc-sync-commits m (fn-cat-count fn-cat) fn-arena fn-cat fn-lbc)))
    (fn-lbc-summary-put :horizon (list hz) 1 fn-lbc)))
