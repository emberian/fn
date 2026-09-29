; store-finalize-published-tests.lisp -- teeth for PRF-992 (lane
; incremental-finalize-3): the composed boundary of the Store open from a
; checkpoint, per literal theorem.  A reachable positive witness of the
; complete antecedent and conclusion of fn-sfp-published-capture-finalizes-ok,
; fn-sfp-published-next-is-the-bound and the keystone
; fn-sfp-open-from-publication-is-the-twin (and that the open is :ok, so the
; witness is not vacuous); the hypothesis-removal witness of the keystone's
; one hypothesis (a history that does not open :ok: the retained facts
; affirmed, the hypothesis failing, the conclusion failing); and the trust
; row's teeth: the assumption's constraint at a ground publication, and a
; must-fail on a non-publication that verifies nothing.
;
; The history is the twin book's test history (tests/acl2/
; replay-identity-index-tests.lisp, as store-finalize-incremental-tests uses
; it): an undertaking, its release, an article at transaction 7; the
; publication frontier is 8; a second article at transaction 8 follows the
; publication and the open is at frontier 9.

(in-package "ACL2")

(include-book "must-fail-checked")
(include-book "../../books/assumptions-publication")

(defconst *sfp-t-stamp* *fn-cfg-default-stamp*)
(defconst *sfp-t-undertake*
  (fn-store-retention-event-make :undertake 0 0 0
                                 "forward-sfp" "subject" "evidence" 10))
(defconst *sfp-t-release*
  (fn-store-retention-event-make :release 1 1 1
                                 "forward-sfp" "subject" "evidence" 0))
(defconst *sfp-t-decrease*
  (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *sfp-t-stamp*))
(defconst *sfp-t-increase*
  (fn-cfg-record-make 2 7 3 (list (fn-cfg-set-capacity 20)) *sfp-t-stamp*))
(defun sfp-t-article (sequence txid generation msgid obligation)
  (fn-held-plain (fn-record-make sequence txid generation msgid '(65) '("fn.test")
                                 obligation "subject" "evidence" 2 841000000)
                 sequence))
(defconst *sfp-t-article* (sfp-t-article 2 7 7 "<sfp@example.invalid>" "archive-sfp"))
(defconst *sfp-t-article-2*
  (sfp-t-article 3 8 8 "<sfp-2@example.invalid>" "archive-sfp-2"))

(defconst *sfp-t-configs*
  (list *fn-cfg-default-record* *sfp-t-decrease* *sfp-t-increase*))
(defconst *sfp-t-records* (list *sfp-t-undertake* *sfp-t-release* *sfp-t-article*))
(defconst *sfp-t-frontier* 8)
(defconst *sfp-t-f* 9)
(defconst *sfp-t-q* (list *sfp-t-article-2*))
; The owner's first publication: no base (the capture of the empty prefix).
(defconst *sfp-t-base* (fn-sco-capture *sfp-t-configs* nil))

; The publication, its tables, and what the open loads from them.
(defconst *sfp-t-published*
  (fn-ock-next-checkpoint *sfp-t-base* *sfp-t-configs* *sfp-t-records*))
(defconst *sfp-t-tables*
  (fn-sct-tables-of-capture *sfp-t-published* *sfp-t-frontier* "rev-sfp" nil))
(defconst *sfp-t-c* (fn-sct-capture-of-tables *sfp-t-tables*))
(defconst *sfp-t-next* (fn-sct-tables-next *sfp-t-tables*))

; -----------------------------------------------------------------------------
; POSITIVE WITNESS, per literal theorem.  The antecedent (the history opens
; :ok at the publication frontier); the conclusions: the published capture
; finalizes :ok there, NEXT is the bound (8, one past the article's
; transaction), and the open from the loaded tables with that NEXT is the
; twin's -- and :ok, over the suffix at frontier 9.
(assert-event
 (and (equal (fn-sn-open-kind (fn-cpo-open-observed *sfp-t-configs* *sfp-t-frontier*
                                                    *sfp-t-records*))
             :ok)
      ; fn-sfp-published-capture-finalizes-ok
      (equal (fn-sn-open-kind (fn-sco-finalize *sfp-t-published* *sfp-t-configs*
                                               *sfp-t-frontier*))
             :ok)
      ; fn-sfp-published-next-is-the-bound
      (equal *sfp-t-next* (fn-sf-next-lower *sfp-t-records* 0))
      (equal *sfp-t-next* 8)
      ; the F row: schema, S, frontier, revision, log, NEXT
      (fn-sct-f-rowp (fn-sct-tables-f *sfp-t-tables*))
      (equal (cadr (fn-sct-tables-f *sfp-t-tables*)) 3)
      ; fn-sfp-open-from-publication-is-the-twin, and the open is :ok
      (equal (fn-sfi-extend-open *sfp-t-c* *sfp-t-configs* *sfp-t-q* *sfp-t-f* *sfp-t-next*)
             (fn-rii-sco-extend-open *sfp-t-c* *sfp-t-configs* *sfp-t-q* *sfp-t-f*))
      (equal (fn-sn-open-kind
              (cadr (cadr (fn-sfi-extend-open *sfp-t-c* *sfp-t-configs* *sfp-t-q*
                                              *sfp-t-f* *sfp-t-next*))))
             :ok)))

; The empty suffix at the publication frontier: the open from the tables is
; the twin's and :ok (the restart right after a publication).
(assert-event
 (and (equal (fn-sfi-extend-open *sfp-t-c* *sfp-t-configs* nil *sfp-t-frontier* *sfp-t-next*)
             (fn-rii-sco-extend-open *sfp-t-c* *sfp-t-configs* nil *sfp-t-frontier*))
      (equal (fn-sn-open-kind
              (cadr (cadr (fn-sfi-extend-open *sfp-t-c* *sfp-t-configs* nil
                                              *sfp-t-frontier* *sfp-t-next*))))
             :ok)))

; -----------------------------------------------------------------------------
; HYPOTHESIS REMOVAL (the keystone's one hypothesis).  A history whose article
; carries generation 8 on transaction 7 does not open :ok at any frontier
; (only the history recognizer compares the two).  Published anyway (the
; capture is built, the tables written, NEXT = 8 as of the sound history),
; the open from its tables proceeds where the twin's whole-history walk
; refuses: the conclusion fails.
(defconst *sfp-t-bad-records*
  (list *sfp-t-undertake* *sfp-t-release*
        (sfp-t-article 2 7 8 "<sfp@example.invalid>" "archive-sfp")))
(defconst *sfp-t-bad-published*
  (fn-ock-next-checkpoint *sfp-t-base* *sfp-t-configs* *sfp-t-bad-records*))
(defconst *sfp-t-bad-tables*
  (fn-sct-tables-of-capture *sfp-t-bad-published* *sfp-t-frontier* "rev-sfp" nil))
(defconst *sfp-t-bad-c* (fn-sct-capture-of-tables *sfp-t-bad-tables*))
(defconst *sfp-t-bad-next* (fn-sct-tables-next *sfp-t-bad-tables*))
(assert-event
 (and ; the hypothesis fails
      (not (equal (fn-sn-open-kind (fn-cpo-open-observed *sfp-t-configs* *sfp-t-frontier*
                                                         *sfp-t-bad-records*))
                  :ok))
      ; the tables are a publication's all the same, NEXT as of a sound history
      (equal *sfp-t-bad-next* 8)
      (fn-sct-f-rowp (fn-sct-tables-f *sfp-t-bad-tables*))
      ; the conclusion fails: the twin refuses the history, the open from the
      ; tables opens (the fault is in the prefix it does not walk)
      (equal (cadr (cadr (fn-rii-sco-extend-open *sfp-t-bad-c* *sfp-t-configs*
                                                 *sfp-t-q* *sfp-t-f*)))
             (fn-sn-open-error :history))
      (equal (fn-sn-open-kind
              (cadr (cadr (fn-sfi-extend-open *sfp-t-bad-c* *sfp-t-configs* *sfp-t-q*
                                              *sfp-t-f* *sfp-t-bad-next*))))
             :ok)
      (not (equal (fn-sfi-extend-open *sfp-t-bad-c* *sfp-t-configs* *sfp-t-q*
                                      *sfp-t-f* *sfp-t-bad-next*)
                  (fn-rii-sco-extend-open *sfp-t-bad-c* *sfp-t-configs*
                                          *sfp-t-q* *sfp-t-f*)))))
(must-fail-checked
 (defthm sfp-t-without-the-open-ok
   (equal (fn-sfi-extend-open *sfp-t-bad-c* *sfp-t-configs* *sfp-t-q*
                              *sfp-t-f* *sfp-t-bad-next*)
          (fn-rii-sco-extend-open *sfp-t-bad-c* *sfp-t-configs* *sfp-t-q* *sfp-t-f*))))

; -----------------------------------------------------------------------------
; THE TRUST ROW's teeth (assumptions-tests' discipline).  The constraint of
; fn-assume-checkpoint-publication-is-a-publication at a ground candidate: a
; publication of the sound history meets it; the bad history's tables do not
; (the second conjunct is false there), so a candidate that admitted them
; would violate the constraint -- the assumption is restrictive, not prose.
(assert-event
 (let ((p (list *sfp-t-base* *sfp-t-records* *sfp-t-frontier* "rev-sfp" nil)))
   (and (equal *sfp-t-tables*
               (fn-sct-tables-of-capture
                (fn-ock-next-checkpoint (nth 0 p) *sfp-t-configs* (nth 1 p))
                (nth 2 p) (nth 3 p) (nth 4 p)))
        (equal (fn-sn-open-kind (fn-cpo-open-observed *sfp-t-configs* (nth 2 p) (nth 1 p)))
               :ok))))
(assert-event
 (let ((p (list *sfp-t-base* *sfp-t-bad-records* *sfp-t-frontier* "rev-sfp" nil)))
   (and (equal *sfp-t-bad-tables*
               (fn-sct-tables-of-capture
                (fn-ock-next-checkpoint (nth 0 p) *sfp-t-configs* (nth 1 p))
                (nth 2 p) (nth 3 p) (nth 4 p)))
        (not (equal (fn-sn-open-kind (fn-cpo-open-observed *sfp-t-configs* (nth 2 p) (nth 1 p)))
                    :ok)))))
