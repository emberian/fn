; store-finalize-incremental-tests.lisp -- teeth for PRF-946 (lane
; incremental-finalize): the keystone fn-sfi-extend-open-is-rii-extend-open
; and its corollary fn-sfi-extend-open-finalizes-the-extension, per literal
; theorem: a reachable positive witness asserting the complete antecedent and
; the conclusion (and that the open is :ok, so the witness is not vacuous);
; the empty suffix; four refusals decided from the suffix alone, alike on
; both sides; one hypothesis-removal witness per hypothesis (the retained
; hypothesis affirmed, the omitted one failing, the conclusion failing); and
; a corrupted carried bound, labelled as such.
;
; The history is the twin book's test history (tests/acl2/
; replay-identity-index-tests.lisp): an undertaking, its release, an article
; at transaction 7, and a second article at transaction 8 after the capture;
; the base finalizes :ok at frontier 8, the extension at 9.

(in-package "ACL2")

(include-book "must-fail-checked")
(include-book "../../books/store-finalize-incremental")

(defconst *sfi-t-stamp* *fn-cfg-default-stamp*)
(defconst *sfi-t-undertake*
  (fn-store-retention-event-make :undertake 0 0 0
                                 "forward-sfi" "subject" "evidence" 10))
(defconst *sfi-t-release*
  (fn-store-retention-event-make :release 1 1 1
                                 "forward-sfi" "subject" "evidence" 0))
(defconst *sfi-t-decrease*
  (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *sfi-t-stamp*))
(defconst *sfi-t-increase*
  (fn-cfg-record-make 2 7 3 (list (fn-cfg-set-capacity 20)) *sfi-t-stamp*))
(defun sfi-t-article (sequence txid msgid obligation)
  (fn-held-plain (fn-record-make sequence txid txid msgid '(65) '("fn.test")
                                 obligation "subject" "evidence" 2 841000000)
                 sequence))
(defconst *sfi-t-article* (sfi-t-article 2 7 "<sfi@example.invalid>" "archive-sfi"))
(defconst *sfi-t-article-2*
  (sfi-t-article 3 8 "<sfi-2@example.invalid>" "archive-sfi-2"))

(defconst *sfi-t-configs*
  (list *fn-cfg-default-record* *sfi-t-decrease* *sfi-t-increase*))
(defconst *sfi-t-prefix* (list *sfi-t-undertake* *sfi-t-release* *sfi-t-article*))
(defconst *sfi-t-base* (fn-sco-capture *sfi-t-configs* *sfi-t-prefix*))
(defconst *sfi-t-f0* 8)
(defconst *sfi-t-f1* 9)
(defconst *sfi-t-q* (list *sfi-t-article-2*))
(defconst *sfi-t-next* (fn-sf-next-lower (fn-sco-records *sfi-t-base*) 0))

; The carried verdict is reachable: the base finalizes :ok at f0; the bound
; it leaves is 8 (one past the article's transaction).
(assert-event
 (and (equal (fn-sn-open-kind (fn-sco-finalize *sfi-t-base* *sfi-t-configs* *sfi-t-f0*))
             :ok)
      (equal *sfi-t-next* 8)))

; -----------------------------------------------------------------------------
; KEYSTONE positive witness: both hypotheses, the conclusion, the open :ok,
; and the corollary's shape (the second component is the finalize of the
; extension).

(defconst *sfi-t-mine*
  (fn-sfi-extend-open *sfi-t-base* *sfi-t-configs* *sfi-t-q* *sfi-t-f1* *sfi-t-next*))
(defconst *sfi-t-twin*
  (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* *sfi-t-q* *sfi-t-f1*))

(assert-event
 (and (equal (fn-sn-open-kind (fn-sco-finalize *sfi-t-base* *sfi-t-configs* *sfi-t-f0*))
             :ok)
      (equal *sfi-t-next* (fn-sf-next-lower (fn-sco-records *sfi-t-base*) 0))
      (equal *sfi-t-mine* *sfi-t-twin*)
      (equal (fn-sn-open-kind (cadr (cadr *sfi-t-mine*))) :ok)
      (not (fn-sopc-open-refusal (fn-sco-extend *sfi-t-base* *sfi-t-configs* *sfi-t-q*)))
      (equal (cadr (cadr *sfi-t-mine*))
             (fn-sco-finalize (fn-sco-extend *sfi-t-base* *sfi-t-configs* *sfi-t-q*)
                              *sfi-t-configs* *sfi-t-f1*))))

; The empty suffix (the swap's empty delta; the open with no record after the
; checkpoint): equal, and :ok.
(assert-event
 (let ((mine (fn-sfi-extend-open *sfi-t-base* *sfi-t-configs* nil *sfi-t-f0* *sfi-t-next*)))
   (and (equal mine (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* nil *sfi-t-f0*))
        (equal (fn-sn-open-kind (cadr (cadr mine))) :ok))))

; -----------------------------------------------------------------------------
; Refusals decided from the suffix alone, alike on both sides.

; A suffix record at the frontier (frontier 8, transaction 8).
(assert-event
 (let ((mine (fn-sfi-extend-open *sfi-t-base* *sfi-t-configs* *sfi-t-q* 8 *sfi-t-next*)))
   (and (equal mine (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* *sfi-t-q* 8))
        (equal (cadr (cadr mine)) (fn-sn-open-error :history)))))

; A suffix record out of sequence (5 where 3 is due).
(defconst *sfi-t-wrong-seq*
  (list (sfi-t-article 5 8 "<sfi-2@example.invalid>" "archive-sfi-2")))
(assert-event
 (let ((mine (fn-sfi-extend-open *sfi-t-base* *sfi-t-configs* *sfi-t-wrong-seq*
                                 *sfi-t-f1* *sfi-t-next*)))
   (and (equal mine (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* *sfi-t-wrong-seq*
                                            *sfi-t-f1*))
        (equal (cadr (cadr mine)) (fn-sn-open-error :history)))))

; A suffix record whose transaction repeats the prefix's last (7, below the
; bound 8).
(defconst *sfi-t-dup-txid*
  (list (sfi-t-article 3 7 "<sfi-2@example.invalid>" "archive-sfi-2")))
(assert-event
 (let ((mine (fn-sfi-extend-open *sfi-t-base* *sfi-t-configs* *sfi-t-dup-txid*
                                 *sfi-t-f1* *sfi-t-next*)))
   (and (equal mine (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* *sfi-t-dup-txid*
                                            *sfi-t-f1*))
        (equal (cadr (cadr mine)) (fn-sn-open-error :history)))))

; A frontier below the prefix's bound (7 < 8): the twin walks the prefix to
; find the article at 7; the carried compare decides the same.
(assert-event
 (let ((mine (fn-sfi-extend-open *sfi-t-base* *sfi-t-configs* nil 7 *sfi-t-next*)))
   (and (equal mine (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* nil 7))
        (equal (cadr (cadr mine)) (fn-sn-open-error :history)))))

; -----------------------------------------------------------------------------
; Hypothesis removal, per literal theorem (two hypotheses).

; (1) The carried verdict omitted.  A base whose second record is out of
; sequence never finalizes :ok at any frontier; with NEXT exactly as the
; theorem says and a suffix that continues the base's count and bound, the
; carried open proceeds where the twin's whole-history walk refuses.
(defconst *sfi-t-bad-base*
  (fn-sco-capture *sfi-t-configs* (list *sfi-t-undertake* *sfi-t-article*)))
(defconst *sfi-t-bad-next* (fn-sf-next-lower (fn-sco-records *sfi-t-bad-base*) 0))
(defconst *sfi-t-bad-q*
  (list (sfi-t-article 2 8 "<sfi-2@example.invalid>" "archive-sfi-2")))
(assert-event
 (and ; the omitted hypothesis fails
      (not (equal (fn-sn-open-kind (fn-sco-finalize *sfi-t-bad-base* *sfi-t-configs* *sfi-t-f0*))
                  :ok))
      ; the retained hypothesis holds
      (equal *sfi-t-bad-next* (fn-sf-next-lower (fn-sco-records *sfi-t-bad-base*) 0))
      ; the conclusion fails: the twin refuses the history, the carried open
      ; does not see the base's fault
      (equal (cadr (cadr (fn-rii-sco-extend-open *sfi-t-bad-base* *sfi-t-configs*
                                                 *sfi-t-bad-q* *sfi-t-f1*)))
             (fn-sn-open-error :history))
      (not (equal (fn-sfi-extend-open *sfi-t-bad-base* *sfi-t-configs* *sfi-t-bad-q*
                                      *sfi-t-f1* *sfi-t-bad-next*)
                  (fn-rii-sco-extend-open *sfi-t-bad-base* *sfi-t-configs*
                                          *sfi-t-bad-q* *sfi-t-f1*)))))
(must-fail-checked
 (defthm sfi-t-without-the-carried-verdict
   (equal (fn-sfi-extend-open *sfi-t-bad-base* *sfi-t-configs* *sfi-t-bad-q*
                              *sfi-t-f1* *sfi-t-bad-next*)
          (fn-rii-sco-extend-open *sfi-t-bad-base* *sfi-t-configs*
                                  *sfi-t-bad-q* *sfi-t-f1*))))

; (2) The bound omitted (NEXT = 0 where the prefix left 8).  With the
; repeated transaction 7 in the suffix, the carried walk admits what the
; whole-history walk refuses.
(assert-event
 (and ; the retained hypothesis holds
      (equal (fn-sn-open-kind (fn-sco-finalize *sfi-t-base* *sfi-t-configs* *sfi-t-f0*))
             :ok)
      ; the omitted hypothesis fails
      (not (equal 0 (fn-sf-next-lower (fn-sco-records *sfi-t-base*) 0)))
      ; the conclusion fails
      (equal (cadr (cadr (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs*
                                                 *sfi-t-dup-txid* *sfi-t-f1*)))
             (fn-sn-open-error :history))
      (not (equal (fn-sfi-extend-open *sfi-t-base* *sfi-t-configs* *sfi-t-dup-txid*
                                      *sfi-t-f1* 0)
                  (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs*
                                          *sfi-t-dup-txid* *sfi-t-f1*)))))
(must-fail-checked
 (defthm sfi-t-without-the-bound
   (equal (fn-sfi-extend-open *sfi-t-base* *sfi-t-configs* *sfi-t-dup-txid* *sfi-t-f1* 0)
          (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* *sfi-t-dup-txid*
                                  *sfi-t-f1*))))

; -----------------------------------------------------------------------------
; CORRUPTED CARRIED BOUND (a mutation witness, not a hypothesis removal): a
; bound above the frontier refuses an extension the twin opens.  The carried
; open never admits more than the twin; it may refuse more under a lie.
(assert-event
 (let ((mine (fn-sfi-extend-open *sfi-t-base* *sfi-t-configs* nil *sfi-t-f0* 100)))
   (and (equal (cadr (cadr mine)) (fn-sn-open-error :history))
        (equal (fn-sn-open-kind
                (cadr (cadr (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* nil
                                                    *sfi-t-f0*))))
               :ok))))
