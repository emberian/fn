; Teeth for books/owner-refresh-indexed.lisp: the owner's refresh over the
; Store's event index.
;
; KEYSTONE fn-own-refresh-ix-is-own-refresh: under (H1) fn-sn-statep of the
; owner's Store and (H2) fn-ceis-indexedp of it, fn-own-refresh-ix is
; fn-own-refresh.  The witness is the refresh the completion of a real
; cancel runs (tests/acl2/owner-cancel-refresh-tests.lisp scenario 1: T with
; a Cancel-Lock, then C cancelling it with the matching Cancel-Key, over the
; owner transitions the host drives): the owner just before C's :complete,
; with the finished Store under its old view, as fn-own-complete refreshes
; it.  One must-fail per hypothesis.
(in-package "ACL2")
(include-book "owner-cancel-refresh-tests")
(include-book "../../books/owner-refresh-indexed")

; The owner O with Store S and every other field its own.
(defun ori-with-store (o s)
  (fn-own-make s (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
               (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o)
               (fn-own-refused o)))

(defun ori-butlast (xs)
  (if (and (consp xs) (consp (cdr xs))) (cons (car xs) (ori-butlast (cdr xs))) nil))

; The owner after T, then C's events up to (not including) its :complete.
(defconst *ori-pre*
  (fn-own-run (fn-own-step *ocr-t-first* '(:begin 1))
              (ori-butlast (own-post-events *ocr-rc1*))))
(defconst *ori-s* (fn-sn-finish (fn-own-store *ori-pre*)))
(defconst *ori-mid* (ori-with-store *ori-pre* *ori-s*))

; Positive witness: both hypotheses hold; the twin is the reference; the
; refresh sees C's acceptance and withdraws T (the committed view of
; *ocr-after*, which is fn-own-complete of *ori-pre*).
(assert-event
 (and (fn-sn-statep *ori-s*)
      (fn-ceis-indexedp *ori-s*)
      (equal (fn-own-view (fn-own-refresh-ix *ori-mid*))
             (fn-own-view (fn-own-refresh *ori-mid*)))
      (equal (fn-own-refresh-ix *ori-mid*) (fn-own-refresh *ori-mid*))
      (equal (fn-own-view (fn-own-refresh-ix *ori-mid*)) (fn-own-view *ocr-after*))
      (equal (fn-own-complete *ori-pre*) *ocr-after*)
      (equal (len (fn-own-view-withdrawals (fn-own-view (fn-own-refresh-ix *ori-mid*)))) 1)
      (equal (ocr-archive (fn-own-refresh-ix *ori-mid*)) (list "<lc@example>"))
      ; the view's count is the index's
      (equal (fn-cei-count (fn-sn-event-index *ori-s*))
             (len (fn-sf-records (fn-sn-files *ori-s*))))))

; Teeth, H2 (the index is the history's): the finished Store with an index
; of another history, where C's Message-ID names a row at sequence 1 whose
; bytes carry no Control header.  H1 holds (the recognizer does not read the
; derived index); the twin decides no record; the reference withdraws T.
(defconst *ori-rc-plain*
  (ocr-row 1 "<lc@example>"
           (ocr-octets (list "From: friend <friend@example.invalid>" "Newsgroups: fn.letters"
                             "Subject: not a cancel" "Message-ID: <lc@example>"))))
(defconst *ori-bad-s*
  (fn-sn-with-event-index *ori-s* (fn-cei-build (list *ocr-rt0* *ori-rc-plain*))))
(assert-event
 (and (fn-sn-statep *ori-bad-s*)
      (not (fn-ceis-indexedp *ori-bad-s*))
      (equal (len (fn-own-view-withdrawals
                   (fn-own-view (fn-own-refresh-ix (ori-with-store *ori-pre* *ori-bad-s*)))))
             0)))
(must-fail
 (assert-event
  (equal (fn-own-refresh-ix (ori-with-store *ori-pre* *ori-bad-s*))
         (fn-own-refresh (ori-with-store *ori-pre* *ori-bad-s*)))))

; Teeth, H1 (a Store's history is Store events): the finished Store whose
; history's first event is a row-shaped value carrying C's Message-ID that
; is no held row (no handle), with the index of that history.  H2 holds;
; the walk answers the value (no facts: no record), the index C's row.
(defconst *ori-fake*
  (list 0 0 0 "<lc@example>" :no-handle '("fn.letters") "a" "s" "e" 2 :legacy
        nil nil nil nil))
(defun ori-with-records (s records)
  (let ((f (fn-sn-files s)))
    (fn-sn-with-event-index
     (fn-sn-update s (fn-sf-make (fn-sf-phase f) (fn-sf-frontier f)
                                 (fn-sf-frontier-candidate f) records
                                 (fn-sf-record-candidate f) (fn-sf-completion f)
                                 (fn-sf-successes f) (fn-sf-barriers f))
                   (fn-sn-node s))
     (fn-cei-build records))))
(defconst *ori-fake-s*
  (ori-with-records *ori-s* (list *ori-fake* (cadr (fn-sf-records (fn-sn-files *ori-s*))))))
(assert-event
 (and (fn-ceis-indexedp *ori-fake-s*)
      (not (fn-sn-statep *ori-fake-s*))
      (equal (len (fn-own-view-withdrawals
                   (fn-own-view (fn-own-refresh-ix (ori-with-store *ori-pre* *ori-fake-s*)))))
             1)))
(must-fail
 (assert-event
  (equal (fn-own-refresh-ix (ori-with-store *ori-pre* *ori-fake-s*))
         (fn-own-refresh (ori-with-store *ori-pre* *ori-fake-s*)))))

; -----------------------------------------------------------------------------
; PRF-277: the ledger is a snoc-list and the host's completion appends it in
; O(1).  KEYSTONES fn-rix-own-complete-enabled-ledger-field (the field after
; the completion is fn-sl-snoc of the old field and the completion pair) and
; fn-rix-own-complete-enabled-ledger (the ledger it represents is the old
; ledger with the pair appended), both for every owner (no hypothesis, so no
; must-fail); fn-own-ledger-count-is-len (the O(1) count the take, the
; outcome and host fn-owner-finish read is the length), for every owner.

(defconst *ori-pair* (fn-sf-completion (fn-sn-files (fn-own-store *ori-pre*))))
(defconst *ori-done* (fn-rix-own-complete-enabled *ori-pre*))

; Reachable positive witness: the live owner after T's commit (C's
; completion pending) holds its one-pair ledger as a snoc form; C's
; completion snocs one pair onto it, the new field's reverse is the old
; one's under one cons (nothing copied), the ledger is the append, the
; count is the length, and the owner is the reference completion's.
(assert-event
 (and (fn-ccar-completion-enabledp (fn-own-store *ori-pre*))
      (fn-sl-snoc-formp (fn-own-ledger-field *ori-pre*))
      (equal (fn-own-ledger-count *ori-pre*) 1)
      (equal (fn-own-ledger-field *ori-done*)
             (fn-sl-snoc (fn-own-ledger-field *ori-pre*) *ori-pair*))
      (equal (cddr (fn-own-ledger-field *ori-done*))
             (cons *ori-pair* (cddr (fn-own-ledger-field *ori-pre*))))
      (equal (fn-own-ledger *ori-done*)
             (append (fn-own-ledger *ori-pre*) (list *ori-pair*)))
      (equal (fn-own-ledger-count *ori-done*) 2)
      (equal (fn-own-ledger-count *ori-done*) (len (fn-own-ledger *ori-done*)))
      (equal (fn-own-ledger *ori-done*) (fn-own-ledger *ocr-after*))))

; A plain-list field (a literal a test builds, nil at the start) represents
; itself; the first snoc puts it in snoc form once.
(assert-event
 (let ((o (fn-own-make (fn-own-store *ori-pre*) (fn-own-view *ori-pre*) nil 0 1 nil
                       (list (cons 0 7)) nil nil nil nil nil nil nil nil)))
   (and (equal (fn-own-ledger o) (list (cons 0 7)))
        (equal (fn-own-ledger-count o) 1)
        (equal (fn-sl-snoc (fn-own-ledger-field o) (cons 1 8))
               (list* :snoc 2 (cons 1 8) (list (cons 0 7))))
        (equal (fn-own-ledger (fn-own-make nil nil nil 0 1 nil
                                           (fn-sl-snoc (fn-own-ledger-field o) (cons 1 8))
                                           nil nil nil nil nil nil nil nil))
               (list (cons 0 7) (cons 1 8))))))

; Corrupted state (labelled): a snoc form whose count exceeds its reverse
; represents the list padded with nil (as TAKE pads); the count is still its
; length, so the O(1) count and the model never disagree on any value.
(assert-event
 (let ((o (fn-own-make nil nil nil 0 1 nil (list* :snoc 3 (list (cons 0 7)))
                       nil nil nil nil nil nil nil nil)))
   (and (equal (fn-own-ledger o) (list nil nil (cons 0 7)))
        (equal (fn-own-ledger-count o) 3)
        (equal (fn-own-ledger-count o) (len (fn-own-ledger o))))))
