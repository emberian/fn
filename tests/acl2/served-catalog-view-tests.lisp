; served-catalog-view-tests.lisp -- witnesses and teeth for
; books/served-catalog-view.lisp and the catalog's withdrawals-by-version
; export (books/catalog.lisp fn-cat-withdrawn-at; lane scale-latency,
; PKT-870, PRF-363).
;
; The fixture is served-catalog-tests' four-row catalog: three articles
; (fn.test 1, 2, 3; the second also fn.other 1), the second withdrawn at
; version 3, then a fourth article (fn.test 4).  Views are counts.  Every
; witness is ground and proved by evaluation; a must-fail form is a
; hypothesis-removal witness, preceded by the affirmative check of the
; omitted hypothesis' failure and of the conclusion's.
(in-package "ACL2")
(include-book "../../books/served-catalog")
(include-book "../../books/served-available-commands")
(include-book "must-fail-checked")

(defconst *scvt-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *scvt-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10)))
(defconst *scvt-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))
(defconst *scvt-p3* (append (fn-record-string-octets "Subject: d") '(13 10 13 10 68 13 10)))
(defconst *scvt-w0* (fn-record-make 0 1 1 "<a@x>" *scvt-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *scvt-w1* (fn-record-make 1 2 2 "<b@x>" *scvt-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *scvt-w2* (fn-record-make 2 3 3 "<c@x>" *scvt-p2* '("fn.test") "o" "s" "e" 1 5))
(defconst *scvt-w3* (fn-record-make 3 4 4 "<d@x>" *scvt-p3* '("fn.test") "o" "s" "e" 1 5))

(defun scvt-held (w handle numbers withdrawn)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers withdrawn))

(defconst *scvt-c3*
  (fn-cat$a-commit (scvt-held *scvt-w2* 2 nil nil)
                   (fn-cat$a-commit (scvt-held *scvt-w1* 1 nil nil)
                                    (fn-cat$a-commit (scvt-held *scvt-w0* 0 nil nil) nil))))
(defconst *scvt-cw* (fn-cat$a-withdraw 1 3 *scvt-c3*))
(defconst *scvt-c4* (fn-cat$a-commit (scvt-held *scvt-w3* 3 nil nil) *scvt-cw*))

;; The export: row 1 withdrawn at version 3 (the count when it was withdrawn).
(defthm scvt-withdrawn-at
  (and (fn-cat-p *scvt-c4*)
       (equal (fn-cat-count *scvt-c4*) 4)
       (equal (fn-cat-horizon *scvt-c4*) 4)
       (equal (fn-cat-withdrawn-at 3 *scvt-c4*) '(1))
       (equal (fn-cat-withdrawn-at 2 *scvt-c4*) nil)
       (equal (fn-cat-withdrawn-at 4 *scvt-c4*) nil))
  :rule-classes nil)

;; REACHABLE WITNESS (the view branch, KEYSTONES fn-scv-count-is-count-p,
;; fn-scv-first-is-first-p, fn-scv-last-is-last-p, antecedent and
;; conclusion): a reader at view 2 of the four-row catalog -- below the
;; count (rows 2 and 3 appended after it) and below the horizon (row 1
;; withdrawn at 3, still visible at 2).  X names fn.test 3 and 4 (the
;; appended rows) and 2 (the withdrawn row); the table says 1, 3, 4 live;
;; the view serves 1 and 2.
(defthm scvt-view-2
  (and (fn-cat-p *scvt-c4*)
       (not (fn-scat-top-viewp 2 *scvt-c4*))
       (equal (fn-cat-group-high "fn.test" *scvt-c4*) 4)
       (equal (fn-scv-x "fn.test" 2 *scvt-c4*) '(3 4 2))
       (equal (fn-cat-group-live-count "fn.test" *scvt-c4*) 3)
       (equal (fn-scv-summary "fn.test" 2 *scvt-c4*) '(2 1 2))
       (equal (car (fn-scv-summary "fn.test" 2 *scvt-c4*))
              (fn-scv-count-p "fn.test" 1 4 2 *scvt-c4*))
       (equal (cadr (fn-scv-summary "fn.test" 2 *scvt-c4*))
              (fn-scv-first-p "fn.test" 1 4 2 *scvt-c4*))
       (equal (caddr (fn-scv-summary "fn.test" 2 *scvt-c4*))
              (fn-scv-last-p "fn.test" 4 2 *scvt-c4*))
       ;; the served GROUP's answer, and the pass's
       (equal (fn-scat-group-summary nil "fn.test" 2 *scvt-c4*) '(2 1 2))
       (equal (fn-scat-group-summary nil "fn.test" 2 *scvt-c4*)
              (fn-scat-group-summary-pass nil "fn.test" 2 *scvt-c4*))
       (equal (fn-scat-group-low "fn.test" 2 *scvt-c4*) 1)
       (equal (fn-scat-group-low "fn.test" 2 *scvt-c4*)
              (fn-scat-group-low-pass "fn.test" 2 *scvt-c4*)))
  :rule-classes nil)

;; At view 3 (the withdrawal's own version: row 1 still visible; row 3
;; appended after): 1, 2, 3.  fn.other: its only row withdrawn at 3, still
;; served at 3; the table says empty.
(defthm scvt-view-3
  (and (not (fn-scat-top-viewp 3 *scvt-c4*))
       (equal (fn-scv-summary "fn.test" 3 *scvt-c4*) '(3 1 3))
       (equal (fn-scat-group-summary nil "fn.test" 3 *scvt-c4*)
              (fn-scat-group-summary-pass nil "fn.test" 3 *scvt-c4*))
       (equal (fn-cat-group-live-count "fn.other" *scvt-c4*) 0)
       (equal (fn-scv-summary "fn.other" 3 *scvt-c4*) '(1 1 1))
       (equal (fn-scat-group-summary nil "fn.other" 3 *scvt-c4*)
              (fn-scat-group-summary-pass nil "fn.other" 3 *scvt-c4*)))
  :rule-classes nil)

;; A view below every row: empty, and the pass's watermark branch.
(defthm scvt-view-0
  (and (equal (fn-scv-summary "fn.test" 0 *scvt-c4*) '(0 0 0))
       (equal (fn-scat-group-summary nil "fn.test" 0 *scvt-c4*)
              (fn-scat-group-summary-pass nil "fn.test" 0 *scvt-c4*)))
  :rule-classes nil)

;;; Teeth.

;; The keystones without fn-cat-p (a corrupted-state witness): one row whose
;; payload is not a handle (so the rows are not the catalog's) and which
;; says it was withdrawn at version 10.  Off the recognizer the horizon
;; export answers count + 1 = 2, so X has no version-10 bucket; the row,
;; visible at view 1, is counted by the pass but not by the summary.
(defconst *scvt-bad*
  (list (scvt-held *scvt-w0* "not-a-handle" '(("fn.test" . 1)) '(10 . 0))))

(defthm scvt-teeth-recognizer
  (and (not (fn-cat-p *scvt-bad*))
       (equal (fn-cat-horizon *scvt-bad*) 2)
       (equal (fn-scv-count-p "fn.test" 1 (fn-cat-group-high "fn.test" *scvt-bad*) 1 *scvt-bad*) 1)
       (not (equal (car (fn-scv-summary "fn.test" 1 *scvt-bad*))
                   (fn-scv-count-p "fn.test" 1 (fn-cat-group-high "fn.test" *scvt-bad*)
                                   1 *scvt-bad*))))
  :rule-classes nil
  ;; off the recognizer the exports' guards fail, so evaluation leaves HIDEs:
  ;; open them and read the exports by their logical sides
  :hints (("Goal" :expand ((:free (x) (hide x)))
           :in-theory (enable fn-scv-keptp fn-scv-liveq fn-scv-x))))

(must-fail-checked
 (defthm scvt-teeth-count-without-recognizer
   (equal (car (fn-scv-summary group v fn-cat))
          (fn-scv-count-p group 1 (fn-cat-group-high group fn-cat) v fn-cat))
   :rule-classes nil))

; W2c: old-view corrections include both post-view appends and a post-view
; withdrawal. The full result is nondegenerate, not merely three equal zeros.
(defun scvt-w2-live-min (group xs lo top fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil))
  (if (consp xs)
      (fn-scv-min* (if (and (fn-scv-in-rangep (car xs) lo top)
                            (fn-scv-liveq group (car xs) fn-cat)) (car xs) 0)
                    (scvt-w2-live-min group (cdr xs) lo top fn-cat))
    0))

(defun scvt-w2-load (fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil))
  (let* ((fn-cat (fn-cat-clear fn-cat))
         (fn-cat (fn-cat-commit (scvt-held *scvt-w0* 0 nil nil) fn-cat))
         (fn-cat (fn-cat-commit (scvt-held *scvt-w1* 1 nil nil) fn-cat))
         (fn-cat (fn-cat-commit (scvt-held *scvt-w2* 2 nil nil) fn-cat))
         (fn-cat (fn-cat-withdraw 1 3 fn-cat)))
    (fn-cat-commit (scvt-held *scvt-w3* 3 nil nil) fn-cat)))

(defun scvt-w2-xfold-check (fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil))
  (let ((xs (fn-scv-x "fn.test" 2 fn-cat)))
    (and (fn-cat-p fn-cat) (consp xs)
         (equal xs '(3 4 2))
         (equal (fn-scv-xfold "fn.test" xs 1 4 2 fn-cat) '(-1 2 2))
         (equal (fn-scv-xfold "fn.test" xs 1 4 2 fn-cat)
                (list (fn-scv-xdiff "fn.test" xs 1 4 2 fn-cat)
                      (fn-scv-xmin "fn.test" xs 1 4 2 fn-cat)
                      (fn-scv-xmax "fn.test" xs 1 4 2 fn-cat)))
         (fn-scv-keptp "fn.test" 2 2 fn-cat)
         (not (fn-scv-liveq "fn.test" 2 fn-cat))
         ; Mutant: compute minimum from liveq rather than keptp.
         (equal (scvt-w2-live-min "fn.test" xs 1 4 fn-cat) 3)
         (not (equal (cadr (fn-scv-xfold "fn.test" xs 1 4 2 fn-cat))
                     (scvt-w2-live-min "fn.test" xs 1 4 fn-cat)))
         ; Mutant: fail to exclude number 4 from the correction range.
         (equal (fn-scv-xfold "fn.test" '(4 2) 1 2 2 fn-cat) '(1 2 2))
         (equal (fn-scv-xfold "fn.test" '(4 2) 1 2 2 fn-cat)
                (list (fn-scv-xdiff "fn.test" '(4 2) 1 2 2 fn-cat)
                      (fn-scv-xmin "fn.test" '(4 2) 1 2 2 fn-cat)
                      (fn-scv-xmax "fn.test" '(4 2) 1 2 2 fn-cat)))
         (not (equal (fn-scv-xfold "fn.test" '(4 2) 1 2 2 fn-cat)
                     (fn-scv-xfold "fn.test" '(4 2) 1 4 2 fn-cat))))))

(with-guard-checking-event
 :none
 (assert-event
  (let ((fn-cat (scvt-w2-load fn-cat)))
    (mv (scvt-w2-xfold-check fn-cat) fn-cat))
  :stobjs-out '(nil fn-cat)))

(defconst *scvt-w2-archive*
  (fn-make-state '("fn.test" "fn.empty")
                  '(("fn.test" . 5) ("fn.empty" . 7)) nil 0 nil nil))

; W2b's two equations, including the count-zero distinction: the reply's
; low is the watermark 7 but the cursor's view low is 0, hence NIL current.
(defun scvt-w2-summary-check (fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil))
  (let* ((s (fn-scv-summary "fn.test" 2 fn-cat))
         (empty (fn-scv-summary "fn.empty" 4 fn-cat))
         (session (fn-nntp-make-session t nil nil t))
         (group (fn-av-nntp-group-result-cat session *scvt-w2-archive*
                                             "fn.empty" 4 fn-cat)))
    (and (fn-cat-p fn-cat)
         (equal s '(2 1 2))
         (equal (fn-scat-available-summary *scvt-w2-archive* "fn.test" 2 fn-cat)
                (fn-scat-available-summary-of *scvt-w2-archive* "fn.test" s))
         (equal (fn-scat-available-low "fn.test" 2 fn-cat) (cadr s))
         (equal empty '(0 0 0))
         (equal (fn-scat-available-summary *scvt-w2-archive* "fn.empty" 4 fn-cat)
                (fn-scat-available-summary-of *scvt-w2-archive* "fn.empty" empty))
         (equal (fn-scat-available-low "fn.empty" 4 fn-cat) (cadr empty))
         (equal (fn-scat-available-summary-of *scvt-w2-archive* "fn.empty" empty)
                '(0 7 6))
         (not (equal (cadr empty)
                     (cadr (fn-scat-available-summary-of *scvt-w2-archive* "fn.empty" empty))))
         (null (fn-nntp-session-current (fn-nntp-result-session group)))
         (equal group
                (fn-nntp-make-result
                 (fn-nntp-set-cursor session "fn.empty" nil)
                 (list (fn-nntp-reply-effect
                        (fn-nntp-crlf
                         (fn-av-scat-group-initial *scvt-w2-archive* "fn.empty" 4 fn-cat)))))))))

(with-guard-checking-event
 :none
 (assert-event
  (let ((fn-cat (scvt-w2-load fn-cat)))
    (mv (scvt-w2-summary-check fn-cat) fn-cat))
  :stobjs-out '(nil fn-cat)))
