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
(include-book "must-fail-checked")
(include-book "owner-cancel-refresh-tests")
(include-book "../../books/owner-refresh-indexed")

; lane history-columns-3: the readers take the history stobj fn-hist.
(defun fn-own-refresh-ix-h (o)
  ; fn-own-refresh-ix over a history stobj loaded with the history it reads (R holds by construction).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix (fn-sf-records (fn-sn-files (fn-own-store o)))) 0 fn-hist)))
        (mv (fn-own-refresh-ix o fn-hist) fn-hist))
      ans)))
(defun fn-rix-ocfg-complete-h (oc)
  ; fn-rix-ocfg-complete over a history stobj loaded with the history it reads (R holds by construction).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))) 0 fn-hist)))
        (mv (fn-rix-ocfg-complete oc fn-hist) fn-hist))
      ans)))
(defun fn-rix-own-complete-enabled-h (o)
  ; fn-rix-own-complete-enabled over a history stobj loaded with the history it reads (R holds by construction).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix (fn-sf-records (fn-sn-files (fn-own-store o)))) 0 fn-hist)))
        (mv (fn-rix-own-complete-enabled o fn-hist) fn-hist))
      ans)))
(defun fn-rix-own-finish-h (o cfg fn-arena)
  ; fn-rix-own-finish over a history stobj loaded with the history it reads (R holds by construction).
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix (fn-sf-records (fn-sn-files (fn-own-store o)))) 0 fn-hist)))
        (mv (fn-rix-own-finish o cfg fn-arena fn-hist) fn-hist))
      ans)))

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
(defun ori-run (o events fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-own-run (fn-own-step o '(:begin 1) fn-arena) events fn-arena))
(bpr-lift ori-run 2)
(defconst *ori-pre*
  (in-arena-ori-run *sr-arena* *ocr-t-first*
                    (ori-butlast (own-post-events *ocr-rc1*))))
(defconst *ori-s* (fn-sn-finish (fn-own-store *ori-pre*)))
(defconst *ori-mid* (ori-with-store *ori-pre* *ori-s*))

; Positive witness: both hypotheses hold; the twin is the reference; the
; refresh sees C's acceptance and withdraws T (the committed view of
; *ocr-after*, which is fn-own-complete of *ori-pre*).


; Teeth, H2 (the index is the history's): the finished Store with an index
; of another history, where C's Message-ID names a row at sequence 1 whose
; bytes carry no Control header.  H1 holds (the recognizer does not read the
; derived index); the twin decides no record; the reference withdraws T.
(defconst *ori-rc-plain*
  (ocr-row 1 "<lc@example>"
           (ocr-octets (list "From: friend <friend@example.invalid>" "Newsgroups: fn.letters"
                             "Subject: not a cancel" "Message-ID: <lc@example>"))))




; Teeth, H1 (a Store's history is Store events): the finished Store whose
; history's first event is a row-shaped value carrying C's Message-ID that
; is no held row (no handle), with the index of that history.  H2 holds;
; the walk answers the value (no facts: no record), the index C's row.
(defconst *ori-fake*
  (list 0 0 0 "<lc@example>" :no-handle '("fn.letters") "a" "s" "e" 2 0
        nil nil nil nil))





; -----------------------------------------------------------------------------
; PRF-283: the ledger is a snoc-list and the host's completion appends it in
; O(1).  KEYSTONES fn-rix-own-complete-enabled-ledger-field (the field after
; the completion is fn-sl-snoc of the old field and the completion pair) and
; fn-rix-own-complete-enabled-ledger (the ledger it represents is the old
; ledger with the pair appended), both for every owner (no hypothesis, so no
; must-fail); fn-own-ledger-count-is-len (the O(1) count the take, the
; outcome and host fn-owner-finish read is the length), for every owner.

(defconst *ori-pair* (fn-sf-completion (fn-sn-files (fn-own-store *ori-pre*))))
(defconst *ori-done* (fn-rix-own-complete-enabled-h *ori-pre*))

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

; -----------------------------------------------------------------------------
; keystone-audit 2026-09-27: the host-line twins fn-rix-ocfg-complete and
; fn-rix-own-finish had no witness.  Reachable positive: the live owner
; before C's completion (its Store indexed), unstaged.  Teeth (CORRUPTED,
; labelled): the same Store with the index of another history
; (*ori-rc-plain*), fn-sn-statep and completion-enabled, not indexed; the
; twin and the carried completion then differ.

(defconst *ori-oc* (fn-ocfg-make *ori-pre* nil nil nil))




; fn-rix-own-finish-is-ccar-own-finish over a fresh arena (the word is
; :fault on both sides: no row stands for the completion; the owner
; component is the completion's).
(defun ori-finish-pair (o)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (mv (list (fn-rix-own-finish-h o nil fn-arena) (fn-ccar-own-finish o nil fn-arena))
          fn-arena)
      r)))
(assert-event
 (let ((p (ori-finish-pair *ori-pre*)))
   (and (equal (nth 0 p) (nth 1 p))
        (equal (cdr (nth 0 p)) *ori-done*))))


; fn-own-refresh-ix-keeps-ledger-field (no hypothesis): the refresh of the
; live owner holding a one-pair ledger leaves that field, and its view moves.
(assert-event
 (and (equal (fn-own-ledger-count *ori-pre*) 1)
      (equal (fn-own-ledger-field (fn-own-refresh-ix-h *ori-pre*))
             (fn-own-ledger-field *ori-pre*))))
