; Teeth for books/history-fold-refinement.lisp and the history folds it
; covers (records-flip wave, lane flip-L3): ground wire histories interned
; into retained rows on a local arena, each fold over the rows against the
; fold over their wire forms, a positive witness that each fold now SEES the
; retained composite (the behaviour the flip had silently dropped), and the
; hypothesis of the article folds removed.
(in-package "ACL2")
(include-book "../../books/history-fold-refinement")
(include-book "key-statements-tests")
(include-book "peer-carriage-tests")
(include-book "store-open-pre-c1-tests")
(include-book "../../books/records-concrete")
(include-book "std/testing/must-fail" :dir :system)

; The rows the intern makes of a wire history WS on a fresh arena, and the
; folds over them and over their wire forms.
(defun hfr-folds (ws msgid evidence fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events ws nil 0 fn-arena)
    (let ((wires (fn-rows-wire-of rows fn-arena)))
      (mv (list :rows rows
                :wires wires
                :okp (fn-rows-composites-okp rows fn-arena)
                :found (fn-ks-find-statement msgid rows)
                :found-alpha (fn-row-wire-of (fn-ks-find-statement msgid rows) fn-arena)
                :found-wire (fn-ks-find-statement msgid wires)
                :usage (fn-pcb-usage rows evidence)
                :usage-wire (fn-pcb-usage wires evidence)
                :free (fn-sopc-free-p rows)
                :free-wire (fn-sopc-free-p wires)
                :articles-alpha (fn-rows-wire-of (fn-bpr-article-records rows) fn-arena)
                :articles-wire (fn-bpr-article-records wires)
                :poll-alpha (fn-row-wire-of (fn-col-poll-article (car rows)) fn-arena)
                :poll-wire (fn-col-poll-article (car wires)))
          fn-arena))))

(defun hfr-run (ws msgid evidence)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (hfr-folds ws msgid evidence fn-arena)
      r)))

(defmacro hfr (key r) `(cadr (member-eq ,key ,r)))

; -----------------------------------------------------------------------------
; keys redecide: the statement's composite, retained as a row, is found, and
; its wire form is the statement the wire history holds
; (fn-ks-find-statement-over-alpha, reached).
(make-event `(defconst *hfr-ks* ',(hfr-run (list *kst-event*) *kst-msgid* "none")))
(assert-event (equal (hfr :wires *hfr-ks*) (list *kst-event*)))
(assert-event (fn-hstxa-p (car (hfr :rows *hfr-ks*))))
(assert-event (equal (hfr :found *hfr-ks*) (car (hfr :rows *hfr-ks*))))
(assert-event (fn-hstxa-p (hfr :found *hfr-ks*)))
(assert-event (equal (hfr :found-alpha *hfr-ks*) *kst-event*))
(assert-event (equal (hfr :found-wire *hfr-ks*) (hfr :found-alpha *hfr-ks*)))
(assert-event (equal (fn-ks-txid (hfr :found *hfr-ks*)) (fn-ks-txid *kst-event*)))
(assert-event (natp (fn-ks-txid (hfr :found *hfr-ks*))))

; carried usage: the carried composite, retained as a row, is charged
; (fn-pcb-usage-over-alpha, reached with a nonzero usage).
(make-event `(defconst *hfr-pcb* ',(hfr-run *pcb-records* "none" *pcb-evidence*)))
(assert-event (fn-hstxa-p (cadr (hfr :rows *hfr-pcb*))))
(assert-event (equal (hfr :usage *hfr-pcb*) (cons *pcb-charge* 1)))
(assert-event (equal (hfr :usage-wire *hfr-pcb*) (hfr :usage *hfr-pcb*)))

; BP receipts and the consumer poll: the signed article is among the rows'
; article records, and alpha of the fold is the fold over the wire history
; (fn-bpr-article-records-over-alpha, fn-col-poll-article-over-alpha:
; the antecedent holds).
(assert-event (hfr :okp *hfr-pcb*))
(assert-event (fn-held-p (fn-bpr-event-article (cadr (hfr :rows *hfr-pcb*)))))
(assert-event (fn-record-p (cadr (hfr :articles-wire *hfr-pcb*))))
(assert-event (equal (hfr :articles-alpha *hfr-pcb*) (hfr :articles-wire *hfr-pcb*)))
(assert-event (fn-held-p (fn-col-poll-article (cadr (hfr :rows *hfr-pcb*)))))
(assert-event (fn-record-p (hfr :poll-wire *hfr-pcb*)))
(assert-event (equal (hfr :poll-alpha *hfr-pcb*) (hfr :poll-wire *hfr-pcb*)))

; The pre-C1 refusal: the pre-C1 control composite, retained as a row, is
; named (fn-sopc-free-p-over-alpha, reached with a history that is NOT free).
(make-event
 `(defconst *hfr-sopc*
    ',(hfr-run (list (sopc-rec *sopc-txn1*) (sopc-rec *sopc-txn2*)) "none" "none")))
(assert-event (fn-hstxa-p (cadr (hfr :rows *hfr-sopc*))))
(assert-event (fn-sopc-pre-c1-control-record-p (cadr (hfr :rows *hfr-sopc*))))
(assert-event (not (fn-sopc-pre-c1-control-record-p (car (hfr :rows *hfr-sopc*)))))
(assert-event (not (hfr :free *hfr-sopc*)))
(assert-event (equal (hfr :free-wire *hfr-sopc*) (hfr :free *hfr-sopc*)))

; The topic projection: a retained composite row records the wire composite
; it carries, so a later topic event finds its authorship; the concrete twin
; the host calls is the same step (fn-rcon-th-prefix-step-is-th-prefix-step,
; reached on the row); a bare wire composite is no retained event and
; faults the prefix.
(make-event
 `(defconst *hfr-tha-row*
    ',(fn-hstxa-make *tha-event*
                     (fn-held-plain (fn-replay-composite-record *tha-event*) 0))))
(assert-event (fn-hstxa-p *hfr-tha-row*))
(defconst *hfr-th-before*
  (fn-th-prefix-state :ok (fn-stxa-sequence *tha-event*) (list *tha-snapshot*)
                      nil nil nil nil))
(make-event `(defconst *hfr-th-after* ',(fn-th-prefix-step *hfr-th-before* *hfr-tha-row*)))
(assert-event (equal (fn-th-at 0 *hfr-th-after*) :ok))
(assert-event (equal (fn-th-at 3 *hfr-th-after*) (list *tha-event*)))
(assert-event (equal (fn-rcon-th-prefix-step *hfr-th-before* *hfr-tha-row*)
                     *hfr-th-after*))
(assert-event (equal (fn-th-at 0 (fn-th-prefix-step *hfr-th-before* *tha-event*))
                     :fault))

; -----------------------------------------------------------------------------
; Hypothesis removal (fn-row-composite-okp): a composite row whose held row
; is not the article its composite carries (the key statement's article row
; in the carried composite's place) breaks the article folds' refinement.
(defun hfr-forged (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events (append *pcb-records* (list *kst-event*)) nil 0 fn-arena)
    (let* ((plain (fn-hstxa-held (caddr rows)))
           (forged (fn-hstxa-make (fn-hstxa-stxa (cadr rows)) plain))
           (rows2 (list forged)))
      (mv (list (fn-hstxa-p forged)
                (fn-rows-composites-okp rows2 fn-arena)
                (fn-rows-wire-of (fn-bpr-article-records rows2) fn-arena)
                (fn-bpr-article-records (fn-rows-wire-of rows2 fn-arena)))
          fn-arena))))
(defun hfr-forged-run ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena) (hfr-forged fn-arena) r)))
(make-event `(defconst *hfr-forged* ',(hfr-forged-run)))
(assert-event (car *hfr-forged*))
(assert-event (not (cadr *hfr-forged*)))
(must-fail
 (assert-event (equal (caddr *hfr-forged*) (cadddr *hfr-forged*))))
