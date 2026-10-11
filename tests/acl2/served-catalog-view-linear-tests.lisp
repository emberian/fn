; served-catalog-view-linear-tests.lisp -- witnesses and teeth for the
; linear correction of books/served-catalog-view.lisp (lane list-hold, LH-B):
; X is built without a pass over itself, a scan step tests membership in X
; in constant time, and the summary's work is a constant plus seven per unit
; of change since the view plus the scan steps.
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
