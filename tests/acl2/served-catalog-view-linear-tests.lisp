; served-catalog-view-linear-tests.lisp -- witnesses and teeth for the
; linear correction of books/served-catalog-view.lisp (lane list-hold, LH-B):
; X is built without a pass over itself, a scan step tests membership in X
; in constant time, the walks at the group's ends step only past numbers of
; X, and the summary's work is a constant plus nine per unit of change since
; the view (fn-scv-summary-work-bounded).
;
; The fixture is a three-row catalog (fn.test 1, 2, 3) followed by N appended
; rows.  A reader holding view 3 sees three rows however many are appended;
; the correction walks the N appended rows once.  Every witness is ground and
; proved by evaluation.
(in-package "ACL2")
(include-book "../../books/served-catalog")

(defconst *scvl-payload* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))

(defun scvl-record (i)
  (fn-record-make i (+ 1 i) (+ 1 i) "<a@x>" *scvl-payload* '("fn.test") "o" "s" "e" 1 5))

(defun scvl-held (i handle numbers withdrawn)
  (let ((w (scvl-record i)))
    (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                  (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                  (fn-record-content-subject w) (fn-record-release-evidence w)
                  (fn-record-charge w) (fn-record-stamp w)
                  (fn-held-facts-of (fn-record-payload w))
                  (fn-held-context-of (fn-record-payload w) nil 0) numbers withdrawn)))

; Rows I .. I+N-1 committed onto C.
(defun scvl-append (i n c)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      c
    (scvl-append (+ 1 i) (- n 1) (fn-cat$a-commit (scvl-held i i nil nil) c))))

(defconst *scvl-base* (scvl-append 0 3 nil))
(defconst *scvl-c25* (scvl-append 3 25 *scvl-base*))
(defconst *scvl-c50* (scvl-append 3 50 *scvl-base*))

;; The summary at view 3 is the number-wise answer (three rows, however many
;; are appended), and X is the 50 appended numbers, each once.
(defthm scvl-summary-unchanged
  (and (fn-cat-p *scvl-c50*)
       (equal (fn-cat-count *scvl-c50*) 53)
       (equal (fn-scv-summary "fn.test" 3 *scvl-c50*) '(3 1 3))
       (equal (car (fn-scv-summary "fn.test" 3 *scvl-c50*))
              (fn-scv-count-p "fn.test" 1 53 3 *scvl-c50*))
       (equal (cadr (fn-scv-summary "fn.test" 3 *scvl-c50*))
              (fn-scv-first-p "fn.test" 1 53 3 *scvl-c50*))
       (equal (caddr (fn-scv-summary "fn.test" 3 *scvl-c50*))
              (fn-scv-last-p "fn.test" 53 3 *scvl-c50*))
       (equal (len (fn-scv-x "fn.test" 3 *scvl-c50*)) 50)
       (no-duplicatesp-equal (fn-scv-x "fn.test" 3 *scvl-c50*)))
  :rule-classes nil)

;; The work is linear in the appends: N = 25 and N = 50, the exact figures,
;; and the bound of fn-scv-summary-work-linear instantiated.  The difference
;; is 25 x (1 + 6 + 1): a row walked, six passes over its number, and a scan
;; step down through it.
(defthm scvl-work-linear
  (and (equal (fn-scv-change-since 3 *scvl-c25*) 25)
       (equal (fn-scv-change-since 3 *scvl-c50*) 50)
       (equal (fn-scv-summary-work "fn.test" 3 *scvl-c25*) 203)
       (equal (fn-scv-summary-work "fn.test" 3 *scvl-c50*) 403)
       (<= (fn-scv-summary-work "fn.test" 3 *scvl-c50*)
           (+ 1 (* 7 (fn-scv-change-since 3 *scvl-c50*))
              (fn-scv-scan-steps "fn.test" 3 *scvl-c50*))))
  :rule-classes nil)

;; A withdrawal below the view enters X once: row 1 withdrawn at version 3,
;; then 50 rows appended.  A reader at view 2 has X = the 51 appended-or-
;; later numbers (3 .. 53) and the withdrawn number 2, each once.
(defconst *scvl-cw* (scvl-append 3 50 (fn-cat$a-withdraw 1 3 *scvl-base*)))

(defthm scvl-withdrawn-once
  (and (fn-cat-p *scvl-cw*)
       (equal (len (fn-scv-x "fn.test" 2 *scvl-cw*)) 52)
       (no-duplicatesp-equal (fn-scv-x "fn.test" 2 *scvl-cw*))
       (member-equal 2 (fn-scv-x "fn.test" 2 *scvl-cw*))
       (fn-scv-in-xp "fn.test" 2 2 *scvl-cw*)
       (not (fn-scv-in-xp "fn.test" 1 2 *scvl-cw*))
       (equal (car (fn-scv-summary "fn.test" 2 *scvl-cw*))
              (fn-scv-count-p "fn.test" 1 53 2 *scvl-cw*))
       (equal (cadr (fn-scv-summary "fn.test" 2 *scvl-cw*))
              (fn-scv-first-p "fn.test" 1 53 2 *scvl-cw*))
       (equal (caddr (fn-scv-summary "fn.test" 2 *scvl-cw*))
              (fn-scv-last-p "fn.test" 53 2 *scvl-cw*))
       (<= (fn-scv-summary-work "fn.test" 2 *scvl-cw*)
           (+ 1 (* 7 (fn-scv-change-since 2 *scvl-cw*))
              (fn-scv-scan-steps "fn.test" 2 *scvl-cw*))))
  :rule-classes nil)

;; TOOTH: a number held by two rows (the recognizer allows it; the commit
;; path never makes it) is one element of X through the row the table names,
;; and the membership test agrees with the list: row 1's copy of fn.test 1
;; is not X's, row 0 (below the view, live) is not in X, and the summary is
;; the number-wise answer.
(defconst *scvl-dup*
  (list (scvl-held 0 0 '(("fn.test" . 1)) nil)
        (scvl-held 1 1 '(("fn.test" . 1)) nil)))

(defthm scvl-duplicate-number
  (and (fn-cat-p *scvl-dup*)
       (equal (fn-cat-group-number "fn.test" 1 *scvl-dup*) 0)
       (equal (fn-scv-x "fn.test" 1 *scvl-dup*) nil)
       (not (fn-scv-in-xp "fn.test" 1 1 *scvl-dup*))
       (equal (fn-scv-summary "fn.test" 1 *scvl-dup*)
              (list (fn-scv-count-p "fn.test" 1 1 1 *scvl-dup*)
                    (fn-scv-first-p "fn.test" 1 1 1 *scvl-dup*)
                    (fn-scv-last-p "fn.test" 1 1 *scvl-dup*))))
  :rule-classes nil)

;; RED-2's TOOTH, the dead run (lane spans-dead-runs): fn.test 1 live, 2 .. 51
;; cancelled at version 51, a fn.other row, then fn.test 52 posted at row 52;
;; the reader's view is 52 (the posting-load case: the
;; reader's view one batch behind, the table's high in X).  The number-wise
;; scan down from the high crosses the whole cancelled run (scvl-scan-down-
;; steps, the old count, kept here as the red); the summary's walk takes two
;; steps, 52 (in X) then its live neighbour 1, and the answer is the
;; number-wise one.
(defun scvl-withdraw-range (i n c)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      c
    (scvl-withdraw-range (+ 1 i) (- n 1) (fn-cat$a-withdraw i (len c) c))))

; A row of another group: the count moves past the cancels' version without
; a fn.test number, so the view 52 sees the cancels and not the post after it.
(defun scvl-held-other (i)
  (let ((w (scvl-record i)))
    (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                  (fn-record-msgid w) i '("fn.other") (fn-record-obligation-id w)
                  (fn-record-content-subject w) (fn-record-release-evidence w)
                  (fn-record-charge w) (fn-record-stamp w)
                  (fn-held-facts-of (fn-record-payload w))
                  (fn-held-context-of (fn-record-payload w) nil 0) nil nil)))

(defconst *scvl-dead*
  (scvl-append 52 1 (fn-cat$a-commit (scvl-held-other 51)
                                     (scvl-withdraw-range 1 50 (scvl-append 0 51 nil)))))

(defun scvl-scan-down-steps (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp k) (natp v))))
  (if (posp k)
      (if (and (not (fn-scv-in-xp group k v fn-cat)) (fn-scv-liveq group k fn-cat))
          1
        (+ 1 (scvl-scan-down-steps group (- k 1) v fn-cat)))
    0))

(defthm scvl-dead-run
  (and (fn-cat-p *scvl-dead*)
       (equal (fn-cat-count *scvl-dead*) 53)
       (equal (fn-cat-group-live-high "fn.test" *scvl-dead*) 52)
       (equal (fn-cat-group-live-low "fn.test" *scvl-dead*) 1)
       (equal (fn-cat-live-prev "fn.test" 52 *scvl-dead*) 1)
       (equal (fn-cat-live-next "fn.test" 1 *scvl-dead*) 52)
       (equal (fn-cat-live-prev "fn.test" 30 *scvl-dead*) 0)
       (equal (fn-scv-x "fn.test" 52 *scvl-dead*) '(52))
       (>= (scvl-scan-down-steps "fn.test" 52 52 *scvl-dead*) 51)
       (equal (fn-scv-scan-steps "fn.test" 52 *scvl-dead*) 3)
       (equal (fn-scv-summary "fn.test" 52 *scvl-dead*) '(1 1 1))
       (equal (fn-scv-summary "fn.test" 52 *scvl-dead*)
              (list (fn-scv-count-p "fn.test" 1 52 52 *scvl-dead*)
                    (fn-scv-first-p "fn.test" 1 52 52 *scvl-dead*)
                    (fn-scv-last-p "fn.test" 52 52 *scvl-dead*)))
       (<= (fn-scv-summary-work "fn.test" 52 *scvl-dead*)
           (+ 3 (* 9 (fn-scv-change-since 52 *scvl-dead*)))))
  :rule-classes nil)
