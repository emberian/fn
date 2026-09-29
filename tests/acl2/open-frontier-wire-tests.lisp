; Teeth for books/open-frontier-wire (row S1 item 4, PRF-976): the host's
; events fold (fn-ofw-wire-next, called by host/native/io.lisp
; fnn-recover-suffix-intern and fnn-recover-log, host/store-open-host.lisp,
; host/store-write-host.lisp) is the replay's frontier fold over the rows the
; intern makes.  KEYSTONE fn-ofw-wire-next-is-the-rows-next: a reachable
; witness asserting its whole antecedent and conclusion over the intern the
; owner's recovery runs (keyring nil, generation 0, a fresh arena); per
; hypothesis a witness keeping the other, failing the omitted one and
; failing the conclusion, then a must-fail of the weakened theorem.
(in-package "ACL2")
(include-book "../../books/open-frontier-wire")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defun ofwt-record (sequence txid msgid)
  (fn-record-make sequence txid txid msgid
                  (list 77 101 115 115 97 103 101 45 73 68 58 32 60 120 62 13 10 13 10
                        72 105 13 10)
                  '("fn.letters")
                  (concatenate 'string "own-pin:" msgid)
                  (concatenate 'string "own-content:" msgid)
                  (concatenate 'string "own-release:" msgid)
                  2 841000000))

(defun ofwt-rows (ws generation)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena)
      (fn-intern-events ws nil generation fn-arena)
      rows)))

; Two articles at txids 4 and 9 (a gap: a refused transaction), then a
; value that is not a wire event.
(defconst *ofwt-ws* (list (ofwt-record 0 4 "<a@example>") (ofwt-record 1 9 "<b@example>")))
(defconst *ofwt-rows* (ofwt-rows *ofwt-ws* 0))

; Reachable witness: the whole antecedent (generation a natural, the intern
; not :bad) and the conclusion, at ACC 0 and at a checkpoint floor above.
(assert-event (and (natp 0)
                   (not (equal *ofwt-rows* :bad))
                   (equal (len *ofwt-rows*) 2)
                   (equal (fn-ofw-wire-next *ofwt-ws* 0) 10)
                   (equal (fn-ofw-wire-next *ofwt-ws* 0) (fn-ofr-events-next *ofwt-rows* 0))
                   (equal (fn-ofw-wire-next *ofwt-ws* 12) 12)
                   (equal (fn-ofw-wire-next *ofwt-ws* 12) (fn-ofr-events-next *ofwt-rows* 12))))
; The chunked fold is the whole fold (fn-ofw-wire-next-of-append).
(assert-event (equal (fn-ofw-wire-next (cdr *ofwt-ws*)
                                       (fn-ofw-wire-next (list (car *ofwt-ws*)) 0))
                     (fn-ofw-wire-next *ofwt-ws* 0)))

; Hypothesis (the intern succeeds): generation 0 kept; a history with a value
; the codec does not produce interns to :bad, and the replay's fold over
; :bad is the floor while the wire fold still read the article's txid.
(defconst *ofwt-bad-ws* (list (ofwt-record 0 4 "<a@example>") 7))
(assert-event (and (natp 0)
                   (equal (ofwt-rows *ofwt-bad-ws* 0) :bad)
                   (not (equal (fn-ofw-wire-next *ofwt-bad-ws* 0)
                               (fn-ofr-events-next (ofwt-rows *ofwt-bad-ws* 0) 0)))))
(must-fail-checked
 (defthm ofwt-without-the-intern
   (implies (natp generation)
            (equal (fn-ofw-wire-next ws acc)
                   (fn-ofr-events-next (mv-nth 0 (fn-intern-events ws keyring generation
                                                                   fn-arena))
                                       acc)))
   :rule-classes nil))

; Hypothesis (generation a natural): the intern kept; at a generation that is
; not a natural the rows are not held rows, and the replay's fold reads no
; txid from them (the intern's guard asks for a natural, so the witness runs
; the logic definitions).
(with-guard-checking-event
 :none
 (assert-event (let ((rows (ofwt-rows *ofwt-ws* -1)))
                 (and (not (natp -1))
                      (not (equal rows :bad))
                      (equal (len rows) 2)
                      (not (fn-held-p (car rows)))
                      (not (equal (fn-ofw-wire-next *ofwt-ws* 0)
                                  (fn-ofr-events-next rows 0)))))))
(must-fail-checked
 (defthm ofwt-without-a-natural-generation
   (implies (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad))
            (equal (fn-ofw-wire-next ws acc)
                   (fn-ofr-events-next (mv-nth 0 (fn-intern-events ws keyring generation
                                                                   fn-arena))
                                       acc)))
   :rule-classes nil))
