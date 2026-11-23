; Layer C1c unit: books/sealer-counts.lisp on real installed-run tables.
; Each table is built in a local fn2-run-installed by the real transitions
; (fn2-run-install, fn2-run-retire, fn2-run-retired-next); every count,
; selection and version below is read by the scans of sealer.lisp and
; runs.lisp and compared with the maintained summary, the laws' predicted
; values and hand-computed constants. Teeth (marked #tooth) drop one
; semantic hypothesis of a theorem against a well-shaped table and show its
; conclusion fails there.
; Run: python3 tools/certify_books.py --incremental tests/sealer-counts-unit --jobs 1
(in-package "ACL2")
(include-book "../books/sealer-counts")

; A transition: (:install r sid run), (:retire r) or (:release r)
; (fn2-run-retired-next, which frees a row once its single unit is
; released: every installed row here names units 0..0).
(defun fn2-sct-apply (op fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :verify-guards nil))
 (case (car op)
  (:install
   (b* (((mv code fn2-run-installed)
         (fn2-run-install (nth 1 op) (nth 2 op) (nth 3 op) 0 0 0 0 0 1 0 0 0 fn2-run-installed))
        ((unless (eq code :ok)) (mv code fn2-run-installed))
        ((mv code fn2-run-installed) (fn2-run-install-units (nth 1 op) 0 0 fn2-run-installed)))
    (mv code fn2-run-installed)))
  (:retire (fn2-run-retire (nth 1 op) fn2-run-installed))
  (otherwise (fn2-run-retired-next (nth 1 op) fn2-run-installed))))
(defun fn2-sct-apply-all (ops fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :verify-guards nil))
 (if (atom ops) (mv t fn2-run-installed)
  (mv-let (code fn2-run-installed) (fn2-sct-apply (car ops) fn2-run-installed)
   (if (eq code :ok) (fn2-sct-apply-all (cdr ops) fn2-run-installed) (mv (list :refused (car ops) code) fn2-run-installed)))))

; The selection over COUNTS as a list (best best-n).
(defun fn2-sct-pick (counts)
 (declare (xargs :verify-guards nil))
 (mv-let (best best-n) (fn2-seal-most-counts counts 0 0 0) (list best best-n)))
; The scans' view of a table: live runs and versions of schemas 0..N-1.
(defun fn2-sct-live (sid n fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :verify-guards nil :measure (nfix (- (nfix n) (nfix sid)))))
 (if (< (nfix sid) (nfix n))
     (cons (fn2-seal-live-runs (fn2-run-installed-rows fn2-run-installed) 0 (nfix sid) fn2-run-installed)
           (fn2-sct-live (+ 1 (nfix sid)) n fn2-run-installed))
   nil))
(defun fn2-sct-versions (sid n fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :verify-guards nil :measure (nfix (- (nfix n) (nfix sid)))))
 (if (< (nfix sid) (nfix n))
     (cons (fn2-run-version (nfix sid) (fn2-run-installed-rows fn2-run-installed) fn2-run-installed)
           (fn2-sct-versions (+ 1 (nfix sid)) n fn2-run-installed))
   nil))
(defconst *fn2-sct-schemas* 20)
(defun fn2-sct-view (max-sid fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :verify-guards nil))
 (let ((rows (fn2-run-installed-rows fn2-run-installed)))
  (list :most (mv-let (best best-n) (fn2-seal-most-runs rows 0 0 0 fn2-run-installed) (list best best-n))
        :fast (mv-let (best best-n) (fn2-seal-most-runs-fast max-sid fn2-run-installed) (list best best-n))
        :within (fn2-seal-live-within-p rows 0 (+ 1 max-sid) fn2-run-installed)
        :free (fn2-seal-free-rows rows 0 fn2-run-installed)
        :live (fn2-sct-live 0 *fn2-sct-schemas* fn2-run-installed)
        :versions (fn2-sct-versions 0 *fn2-sct-schemas* fn2-run-installed))))
(defun fn2-sct-run (rows ops max-sid)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-run-installed
  (mv-let (answer fn2-run-installed)
   (b* ((fn2-run-installed (fn2-run-installed-init rows fn2-run-installed))
        ((mv code fn2-run-installed) (fn2-sct-apply-all ops fn2-run-installed)))
    (mv (if (eq code t) (fn2-sct-view max-sid fn2-run-installed) code) fn2-run-installed))
   answer)))
(defmacro fn2-sct-get (key rows ops &optional (max-sid '19))
 `(cadr (assoc-keyword ,key (fn2-sct-run ,rows ,ops ,max-sid))))

; The maintained summary: counts per schema 0..19, the free count, the
; versions; each transition updates them by the laws alone, from the
; transition's arguments and the written row's old contents. The one rescan
; is a retirement of the row holding its schema's version
; (fn2-run-version-of-retire covers every other retirement).
(defun fn2-sct-maintain (ops counts free versions fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :verify-guards nil))
 (if (atom ops) (mv (list counts free versions) fn2-run-installed)
  (b* ((op (car ops)) (r (nth 1 op))
       (old-schema (fn2-run-installed-schema r fn2-run-installed))
       (old-run (fn2-run-installed-run r fn2-run-installed))
       (old-ulast (fn2-run-installed-ulast r fn2-run-installed))
       (old-ufirst (fn2-run-installed-ufirst r fn2-run-installed))
       ((mv code fn2-run-installed) (fn2-sct-apply op fn2-run-installed))
       ((unless (eq code :ok)) (mv (list :refused op code) fn2-run-installed)))
   (case (car op)
    (:install
     (fn2-sct-maintain (cdr ops) (fn2-seal-counts-bump counts 0 (nth 2 op) 1) (- free 1)
                       (if (< (nfix (nth (nth 2 op) versions)) (nth 3 op)) (update-nth (nth 2 op) (nth 3 op) versions) versions)
                       fn2-run-installed))
    (:retire
     (fn2-sct-maintain (cdr ops) (fn2-seal-counts-bump counts 0 old-schema -1) free
                       (if (< old-run (nfix (nth old-schema versions))) versions
                         (update-nth old-schema (fn2-run-version old-schema (fn2-run-installed-rows fn2-run-installed) fn2-run-installed)
                                     versions))
                       fn2-run-installed))
    (otherwise
     (fn2-sct-maintain (cdr ops) counts (if (< (nfix old-ulast) (+ 1 (nfix old-ufirst))) (+ 1 free) free)
                       versions fn2-run-installed))))))
(defun fn2-sct-maintained (rows ops)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-run-installed
  (mv-let (answer fn2-run-installed)
   (b* ((fn2-run-installed (fn2-run-installed-init rows fn2-run-installed)))
    (fn2-sct-maintain ops (fn2-seal-zero-counts *fn2-sct-schemas*) rows (fn2-seal-zero-counts *fn2-sct-schemas*)
                      fn2-run-installed))
   answer)))
; The maintained counts select as the scan does; the maintained free count
; and versions are the scans'.
(defun fn2-sct-agrees-p (rows ops)
 (declare (xargs :verify-guards nil))
 (let ((view (fn2-sct-run rows ops 19)) (kept (fn2-sct-maintained rows ops)))
  (and (equal (car kept) (cadr (assoc-keyword :live view)))
       (equal (cadr kept) (cadr (assoc-keyword :free view)))
       (equal (caddr kept) (cadr (assoc-keyword :versions view)))
       (equal (fn2-sct-pick (car kept)) (cadr (assoc-keyword :most view)))
       (equal (cadr (assoc-keyword :fast view)) (cadr (assoc-keyword :most view))))))

; ---------------------------------------------------------------------------
; The empty table: no live run anywhere, every row free, (mv 0 0).
(assert-event (equal (fn2-sct-get :most 8 nil) '(0 0)))
(assert-event (equal (fn2-sct-get :fast 8 nil) '(0 0)))
(assert-event (equal (fn2-sct-get :free 8 nil) 8))
(assert-event (equal (fn2-sct-get :versions 8 nil) (fn2-seal-zero-counts 20)))
(assert-event (equal (fn2-sct-pick (fn2-seal-zero-counts 20)) '(0 0)))
(assert-event (equal (fn2-sct-pick nil) '(0 0)))
(assert-event (fn2-sct-agrees-p 8 nil))
(assert-event (equal (fn2-sct-get :most 0 nil) '(0 0)))
(assert-event (equal (fn2-sct-get :fast 0 nil) '(0 0)))

; Ties: schemas 5 and 3 hold two live runs each, 5's rows first in row
; order and 7 holding one. The smaller schema wins, whichever the scan
; meets first.
(defconst *fn2-sct-tie*
 '((:install 0 5 1) (:install 1 3 2) (:install 2 5 3) (:install 3 3 4) (:install 4 7 5)))
(assert-event (equal (fn2-sct-get :most 8 *fn2-sct-tie*) '(3 2)))
(assert-event (equal (fn2-sct-get :fast 8 *fn2-sct-tie*) '(3 2)))
(assert-event (equal (fn2-sct-pick '(0 0 0 2 0 2 0 1)) '(3 2)))
(assert-event (equal (fn2-sct-pick '(0 0 0 2 0 3 0 1)) '(5 3)))
(assert-event (fn2-sct-agrees-p 8 *fn2-sct-tie*))
; A schema with live runs at row 7, the last row, is counted.
(assert-event (equal (fn2-sct-get :most 8 '((:install 7 19 1) (:install 0 2 2))) '(2 1)))
(assert-event (equal (fn2-sct-get :fast 8 '((:install 7 19 1) (:install 0 2 2) (:install 6 19 3))) '(19 2)))

; Install, retire and release deltas. Each prefix of the trace is checked:
; the maintained counts, free count and versions follow the laws, and the
; counts select as the scan.
(defconst *fn2-sct-trace*
 '((:install 0 3 1) (:install 1 3 2) (:install 2 4 3) (:install 3 4 4) (:install 4 4 5)
   (:retire 2) (:retire 3) (:release 2) (:install 2 3 6) (:release 3) (:retire 0) (:release 0)))
(defun fn2-sct-prefixes-agree-p (rows ops n)
 (declare (xargs :verify-guards nil))
 (or (zp n) (and (fn2-sct-agrees-p rows (take n ops)) (fn2-sct-prefixes-agree-p rows ops (- n 1)))))
(assert-event (fn2-sct-prefixes-agree-p 6 *fn2-sct-trace* (len *fn2-sct-trace*)))
(defconst *fn2-sct-drop* '((:install 0 4 7) (:install 1 4 3) (:install 2 6 8) (:retire 0) (:retire 1) (:release 0)))
(assert-event (fn2-sct-prefixes-agree-p 4 *fn2-sct-drop* (len *fn2-sct-drop*)))
(assert-event (equal (fn2-sct-get :live 6 (take 5 *fn2-sct-trace*)) '(0 0 0 2 3 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))
(assert-event (equal (fn2-sct-get :most 6 (take 5 *fn2-sct-trace*)) '(4 3)))
(assert-event (equal (fn2-sct-get :free 6 (take 5 *fn2-sct-trace*)) 1))
; Two retirements: schema 4 down to one live run, 3 now leads; no row freed.
(assert-event (equal (fn2-sct-get :most 6 (take 7 *fn2-sct-trace*)) '(3 2)))
(assert-event (equal (fn2-sct-get :free 6 (take 7 *fn2-sct-trace*)) 1))
; Releasing row 2 frees it; installing schema 3 there takes it again.
(assert-event (equal (fn2-sct-get :free 6 (take 8 *fn2-sct-trace*)) 2))
(assert-event (equal (fn2-sct-get :free 6 (take 9 *fn2-sct-trace*)) 1))
(assert-event (equal (fn2-sct-get :live 6 (take 9 *fn2-sct-trace*)) '(0 0 0 3 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))
(assert-event (equal (fn2-sct-get :most 6 *fn2-sct-trace*) '(3 2)))
(assert-event (equal (fn2-sct-get :free 6 *fn2-sct-trace*) 3))
; A transition on a row in the wrong state is refused: row 1 is live.
(assert-event (equal (fn2-sct-run 6 '((:install 1 3 2) (:install 1 4 9)) 19) '(:refused (:install 1 4 9) :state)))
(assert-event (equal (fn2-sct-run 6 '((:install 1 3 2) (:release 1)) 19) '(:refused (:release 1) :state)))

; fn2-run-version: the greatest live run of a schema, after an installation
; with a greater run the installed run; after retiring a run below the
; version, unchanged; retiring the greatest run drops it to the next.
(assert-event (equal (nth 3 (fn2-sct-get :versions 6 (take 2 *fn2-sct-trace*))) 2))
(assert-event (equal (nth 3 (fn2-sct-get :versions 6 (take 9 *fn2-sct-trace*))) 6))
(assert-event (equal (nth 4 (fn2-sct-get :versions 6 (take 5 *fn2-sct-trace*))) 5))
(assert-event (equal (nth 4 (fn2-sct-get :versions 6 (take 7 *fn2-sct-trace*))) 5))
(assert-event (equal (nth 4 (fn2-sct-get :versions 6 '((:install 0 4 7) (:install 1 4 3) (:retire 0)))) 3))
(assert-event (equal (nth 3 (fn2-sct-get :versions 6 *fn2-sct-trace*)) 6))

; Beyond MAX-SID: a live schema 9 with the most runs, MAX-SID 4. The
; histogram refuses and the fast selection falls back to the scan.
(defconst *fn2-sct-wide* '((:install 0 1 1) (:install 1 1 2) (:install 2 9 3) (:install 3 9 4) (:install 4 9 5)))
(assert-event (equal (fn2-sct-get :most 8 *fn2-sct-wide* 4) '(9 3)))
(assert-event (equal (fn2-sct-get :fast 8 *fn2-sct-wide* 4) '(9 3)))
(assert-event (not (fn2-sct-get :within 8 *fn2-sct-wide* 4)))
(assert-event (fn2-sct-get :within 8 *fn2-sct-wide* 9))

; ---------------------------------------------------------------------------
; #tooth fn2-seal-most-counts-is-most-runs without fn2-seal-live-within-p:
; counts that match schemas 0..4 exactly on the wide table select schema 1,
; the scan schema 9.
(assert-event (let ((live (fn2-sct-get :live 8 *fn2-sct-wide* 4)))
               (and (equal (take 5 live) '(0 2 0 0 0))
                    (equal (fn2-sct-pick (take 5 live)) '(1 2))
                    (not (equal (fn2-sct-pick (take 5 live)) (fn2-sct-get :most 8 *fn2-sct-wide* 4))))))
; #tooth fn2-seal-most-counts-is-most-runs without fn2-seal-counts-match-p:
; counts kept from before the last installation (stale by one) select
; schema 3, the scan schema 4.
(assert-event (let ((stale (fn2-sct-get :live 6 (take 4 *fn2-sct-trace*))))
               (and (equal (fn2-sct-pick stale) '(3 2))
                    (equal (fn2-sct-get :most 6 (take 5 *fn2-sct-trace*)) '(4 3)))))
; #tooth fn2-run-version-of-install without its comparison: installing a
; run below the schema's version leaves the version where it was.
(assert-event (equal (nth 3 (fn2-sct-get :versions 6 '((:install 0 3 5) (:install 1 3 2)))) 5))
; #tooth fn2-run-version-of-retire without its condition: retiring the
; row that holds the schema's greatest run moves the version.
(assert-event (let ((before (fn2-sct-get :versions 6 '((:install 0 3 5) (:install 1 3 2))))
                    (after (fn2-sct-get :versions 6 '((:install 0 3 5) (:install 1 3 2) (:retire 0)))))
               (and (equal (nth 3 before) 5) (equal (nth 3 after) 2))))
