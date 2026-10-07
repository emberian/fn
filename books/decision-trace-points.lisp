; fn: the projections the first traced entries need beyond the library of
; books/decision-trace.lisp (lane obs-decision-trace).
;
; A traced entry names two functions of the list of values it returned: D,
; the decision part, and FN, the record kept (books/definterface.lisp :trace).
; Most entries use the library's selectors.  Here is the one whose record
; carries more than its word: `fn-otm-disk-step' returns (WORD S' JOURNAL-LINE
; LOG-LINE), the decision journal's entry for the event is built from S', and
; the row carries the journal's sequence number (JSEQ) so a reader joins the
; trace to the journal.  The row holds ACL2's JSEQ of S'; it does not hold the
; journal line, which is the journal's alone.
;
; Prefix `fn-dtrace-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "decision-trace")
(include-book "owner-time-journal")

; The decision: the word, as an atom (the words are keywords).
(defun fn-dtrace-disk-step-word (vals)
  (declare (xargs :guard t))
  (fn-dtrace-atom-clip (fn-dtrace-v0car vals)))

; The record: (WORD JSEQ), JSEQ the journal sequence of the state the event
; produced (the entry's journal line is of that state).
(defun fn-dtrace-disk-step-record (vals)
  (declare (xargs :guard t))
  (let ((r (fn-dtrace-v0 vals)))
    (list (fn-dtrace-disk-step-word vals)
          (fn-dtrace-atom-clip
           (if (and (consp r) (consp (cdr r))) (fn-otm-jseq (cadr r)) 0)))))

(defthm fn-dtrace-disk-step-record-is-a-record
  (fn-dtrace-recordp (fn-dtrace-disk-step-record vals)))
