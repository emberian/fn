; Reachable, nonempty checkpoint fixtures for MOVE crash/reopen controls.
; The wire article and owner admission use the existing catalog fixture's
; supported group/profile; no arena or catalog local stobj is introduced.
(in-package "ACL2")
(include-book "lc-cleaning-model-tests")

(defun lcm-owner-held (seq)
 (declare (xargs :guard t :verify-guards nil))
 (fn-held-with-numbers (ec-call (fn-intern-row-at
  (fn-record-make (nfix seq) (nfix seq) (nfix seq)
     (if (equal seq 0) "<one@example>" "<two@example>")
     '(77 101 115 115 97 103 101 45 73 68 58 32 60 120 62 13 10 13 10 72 105 13 10)
     '("fn.letters")
     (if (equal seq 0) "own-pin:<one@example>" "own-pin:<two@example>")
     (if (equal seq 0) "own-content:<one@example>" "own-content:<two@example>")
     (if (equal seq 0) "own-release:<one@example>" "own-release:<two@example>") 2 841000000)
  nil 0 (nfix seq))) (list (cons "fn.letters" (+ 1 (nfix seq))))))
(verify-guards lcm-owner-held)

(defconst *lcm-owner-payload*
 '(77 101 115 115 97 103 101 45 73 68 58 32 60 120 62 13 10 13 10 72 105 13 10))
(defun lcm-owner-rows (count)
 (declare (xargs :guard t))
 (if (equal count 2) (list (lcm-owner-held 0) (lcm-owner-held 1))
  (list (lcm-owner-held 0))))
; These two readers describe only this freshly rebuilt one-group fixture's
; write-once map cells. They are not a general native map extraction.
(defun lcm-owner-number-cells (n fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :measure (nfix n)))
 (if (zp (nfix n)) nil
  (cons (cons (cons "fn.letters" (nfix n))
              (ec-call (fn-lbc-number-get "fn.letters" (nfix n) fn-lbc)))
        (lcm-owner-number-cells (1- (nfix n)) fn-lbc))))
(defun lcm-owner-summary-cells (field fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :measure (nfix field)))
 (if (zp (nfix field)) nil
  (cons (cons (cons (list :summary "fn.letters") (nfix field))
              (ec-call (fn-lbc-summary-word "fn.letters" (nfix field) fn-lbc)))
        (lcm-owner-summary-cells (1- (nfix field)) fn-lbc))))
(defun lcm-owner-snapshot (rows segs fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (let* ((fn-lbc (ec-call (fn-lbc-open-rebuild rows segs fn-lbc)))
        (value (lcm-fixture-value fn-lbc))
        (maps (list (lcm-owner-number-cells (fn-lbc-count fn-lbc) fn-lbc)
                    (lcm-owner-summary-cells 4 fn-lbc) nil))
        (value (ec-call (update-nth *fn-lbc-number-store* maps value)))
        (value (ec-call (update-nth *fn-lbc-summary-groups*
                                   (fn-lbc-summary-groups fn-lbc) value))))
  (mv value fn-lbc)))
(defun lcm-owner-snapshot-fixture (rows segs)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (value fn-lbc) (lcm-owner-snapshot rows segs fn-lbc) value)))
(verify-guards lcm-owner-snapshot-fixture)
(defun lcm-owner-input (count)
 (declare (xargs :guard t))
 (let* ((rows (lcm-owner-rows count))
        (old (ec-call (fn-lb-log-model-append (lcm-owner-held 0) *lcm-owner-payload* 1 nil)))
        (old (if (equal count 2)
              (ec-call (fn-lb-log-model-append (lcm-owner-held 1) *lcm-owner-payload* 1 old)) old))
        (segs (fn-lc-join old '((2 nil nil))))
        (value (lcm-owner-snapshot-fixture rows segs))
        (control (ec-call (fn-lc-control-of (list (list *fn-cfg-default-record*) rows))))
        (header (fn-lc-snapshot-header-value value
                  (list :lc-header (list 1 (len (fn-lc-at 1 (fn-lc-head old)))
                                   (len rows) 8 *fn-lg-genesis*) 3 nil nil nil) control))
        (disk (ec-call (fn-lc-proof-image-disk
                       (fn-lc-pages (ec-call (fn-lc-columns-value value)) header)))))
  (list disk segs header rows value)))
(assert-event
 (let* ((rows (lcm-owner-rows 2)) (configs (list *fn-cfg-default-record*))
        (control (fn-lc-control-of (list configs rows))))
  (and (fn-sn-observed-historyp 8 rows)
       (not (equal (fn-ock-recover-full configs 8 rows 4) :fault))
       (equal (fn-lc-owner-from-seed (fn-lc-owner-seed control rows) configs 8 nil 4)
              (fn-ock-recover-full configs 8 rows 4)))))
