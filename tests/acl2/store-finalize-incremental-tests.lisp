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

; (1) The carried verdict omitted.  A base whose article carries generation 8
; on transaction 7 never finalizes :ok at any frontier (only the history
; recognizer compares the two; every fold accepts it and stays paused); with
; NEXT exactly as the theorem says and the same suffix, the carried open
; proceeds where the twin's whole-history walk refuses.
(defconst *sfi-t-bad-base*
  (fn-sco-capture *sfi-t-configs*
                  (list *sfi-t-undertake* *sfi-t-release*
                        (fn-held-plain (fn-record-make 2 7 8 "<sfi@example.invalid>"
                                                       '(65) '("fn.test") "archive-sfi"
                                                       "subject" "evidence" 2 841000000)
                                       2))))
(defconst *sfi-t-bad-next* (fn-sf-next-lower (fn-sco-records *sfi-t-bad-base*) 0))
(defconst *sfi-t-bad-q* *sfi-t-q*)
(assert-event
 (and ; the omitted hypothesis fails
      (not (equal (fn-sn-open-kind (fn-sco-finalize *sfi-t-bad-base* *sfi-t-configs* *sfi-t-f0*))
                  :ok))
      ; the retained hypothesis holds
      (equal *sfi-t-bad-next* (fn-sf-next-lower (fn-sco-records *sfi-t-bad-base*) 0))
      ; the conclusion fails: the twin refuses the history, the carried open
      ; opens (the base's fault is in the prefix it does not walk)
      (fn-sco-pausedp (fn-sco-cpr *sfi-t-bad-base*))
      (equal (cadr (cadr (fn-rii-sco-extend-open *sfi-t-bad-base* *sfi-t-configs*
                                                 *sfi-t-bad-q* *sfi-t-f1*)))
             (fn-sn-open-error :history))
      (equal (fn-sn-open-kind
              (cadr (cadr (fn-sfi-extend-open *sfi-t-bad-base* *sfi-t-configs* *sfi-t-bad-q*
                                              *sfi-t-f1* *sfi-t-bad-next*))))
             :ok)
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

; (2) The bound omitted (NEXT = 0 where the prefix left 8).  A suffix record
; below the bound is refused by the folds themselves (the node's next
; transaction is the bound), so the bound is observable only where nothing
; else looks: the frontier compare.  At frontier 7 with no suffix, the twin
; walks the prefix and refuses the history; the carried open with NEXT = 0
; passes the compare and reaches the node's frontier check instead.
(assert-event
 (and ; the retained hypothesis holds
      (equal (fn-sn-open-kind (fn-sco-finalize *sfi-t-base* *sfi-t-configs* *sfi-t-f0*))
             :ok)
      ; the omitted hypothesis fails
      (not (equal 0 (fn-sf-next-lower (fn-sco-records *sfi-t-base*) 0)))
      ; the conclusion fails: different refusals
      (equal (cadr (cadr (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* nil 7)))
             (fn-sn-open-error :history))
      (equal (cadr (cadr (fn-sfi-extend-open *sfi-t-base* *sfi-t-configs* nil 7 0)))
             (fn-sn-open-error :frontier))
      (not (equal (fn-sfi-extend-open *sfi-t-base* *sfi-t-configs* nil 7 0)
                  (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* nil 7)))))
(must-fail-checked
 (defthm sfi-t-without-the-bound
   (equal (fn-sfi-extend-open *sfi-t-base* *sfi-t-configs* nil 7 0)
          (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* nil 7))))

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

; -----------------------------------------------------------------------------
; PRF-968: the carried resume (lane incremental-finalize-2).  The entries'
; guard is the carried invariant, which is not executable (fn-rii-known-okp
; is a defun-sk): the evaluator cannot check it, and with guard checking off
; it runs the :logic side of every mbe, where the tries are not consulted.
; So every witness runs the entries in raw Lisp through a :program wrapper,
; which is what the :program host and the served image execute.

(defun sfi-t-raw-resume (r configs events ix)
  (declare (xargs :mode :program))
  (fn-sfi-cpr-resume-carried r configs events ix))
(defun sfi-t-raw-extend (c ix configs suffix frontier count next)
  (declare (xargs :mode :program))
  (fn-sfi-extend-open-carried c ix configs suffix frontier count next))
(defun sfi-t-raw-steps (r configs events ix)
  (declare (xargs :mode :program))
  (fn-sfi-cpr-resume-carried-steps r configs events ix))

(defconst *sfi-t-count* (len (fn-sco-records *sfi-t-base*)))
(defconst *sfi-t-ix* (fn-sfi-carry *sfi-t-base*))
(defconst *sfi-t-article-3*
  (sfi-t-article 4 9 "<sfi-3@example.invalid>" "archive-sfi-3"))
(defconst *sfi-t-f2* 10)

; KEYSTONE positive witness (fn-sfi-extend-open-carried-is-rii-extend-open):
; the complete antecedent -- the pair carried (fn-sfi-carry-is-carried: the
; base's pause is configured, the carry non-nil), the carried verdict, the
; count and the bound -- and the conclusion; the open :ok; the corollary's
; shape (fn-sfi-extend-open-carried-finalizes-the-extension).
(assert-event
 (let ((round-1 (sfi-t-raw-extend *sfi-t-base* *sfi-t-ix* *sfi-t-configs* *sfi-t-q*
                                  *sfi-t-f1* *sfi-t-count* *sfi-t-next*)))
 (and (consp *sfi-t-ix*)
      (fn-sco-pausedp (fn-sco-cpr *sfi-t-base*))
      (fn-cnode-statep (fn-sco-at 1 (fn-sco-cpr *sfi-t-base*)))
      (equal (fn-sn-open-kind (fn-sco-finalize *sfi-t-base* *sfi-t-configs* *sfi-t-f0*))
             :ok)
      (equal *sfi-t-count* (len (fn-sco-records *sfi-t-base*)))
      (equal *sfi-t-next* (fn-sf-next-lower (fn-sco-records *sfi-t-base*) 0))
      (equal (len round-1) 3)
      (equal (list (car round-1) (caddr round-1))
             (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* *sfi-t-q* *sfi-t-f1*))
      (equal (car round-1) (fn-sco-extend *sfi-t-base* *sfi-t-configs* *sfi-t-q*))
      (equal (fn-sn-open-kind (cadr (caddr round-1))) :ok)
      (equal (cadr (caddr round-1))
             (fn-sco-finalize (fn-sco-extend *sfi-t-base* *sfi-t-configs* *sfi-t-q*)
                              *sfi-t-configs* *sfi-t-f1*)))))

; The next round's facts, each O(|Q|) (fn-sfi-extend-open-carried-keeps-
; carried, -count-and-bound; the carried Message-ID trie is the rebuilt one,
; fn-sfi-carried-msgid-trie-is-the-rebuilt-trie), then round 2 from the
; carried pair with no node pass: the twin's result again, :ok.
(assert-event
 (let* ((round-1 (sfi-t-raw-extend *sfi-t-base* *sfi-t-ix* *sfi-t-configs* *sfi-t-q*
                                   *sfi-t-f1* *sfi-t-count* *sfi-t-next*))
        (e1 (car round-1)) (ix1 (cadr round-1))
        (count1 (+ *sfi-t-count* (len *sfi-t-q*)))
        (next1 (fn-sf-next-lower *sfi-t-q* *sfi-t-next*))
        (round-2 (sfi-t-raw-extend e1 ix1 *sfi-t-configs* (list *sfi-t-article-3*)
                                   *sfi-t-f2* count1 next1)))
   (and (fn-sco-pausedp (fn-sco-cpr e1))
        (fn-cnode-statep (fn-sco-at 1 (fn-sco-cpr e1)))
        (equal (car ix1) (car (fn-rii-ix-of (fn-cnode-node (fn-sco-at 1 (fn-sco-cpr e1))))))
        (equal count1 (len (fn-sco-records e1)))
        (equal next1 (fn-sf-next-lower (fn-sco-records e1) 0))
        (equal next1 9)
        (equal (list (car round-2) (caddr round-2))
               (fn-rii-sco-extend-open e1 *sfi-t-configs* (list *sfi-t-article-3*)
                                       *sfi-t-f2*))
        (equal (fn-sn-open-kind (cadr (caddr round-2))) :ok)
        (equal (fn-sf-next-lower (list *sfi-t-article-3*) next1) 10))))

; HYPOTHESIS REMOVAL (1): the carried invariant, on the SERVED PATH.  The
; empty node's tries stand in for the base's.  Retained: a configured pause.
; Omitted: the wrong Message-ID trie is not the rebuilt one, so fn-rii-okp
; fails (fn-sfi-carried-msgid-trie-is-the-rebuilt-trie).  Conclusion: the
; served path (:exec, raw) with the wrong trie ADMITS a duplicate
; Message-ID (a pause) that the checkpoint's resume refuses; the carried
; trie refuses alike.  In the logic this instance coincides: the twin's
; inner mbe :logic sides answer from the node, so a ground defthm of the
; weakened equality is PROVED (the first certify run proved it in 13 steps)
; and none refutes it.  The invariant is therefore the guard's hypothesis
; -- what makes the :exec path the :logic path -- carried into the keystone
; from the twin's own fn-rii-sco-cpr-prefix-is-sco-cpr-prefix; whether the
; logical equality holds without it is that book's question, and the
; hypothesis is not removed here (a weakened theorem is proved first).
(defconst *sfi-t-q-dup*
  (list (sfi-t-article 3 8 "<sfi@example.invalid>" "archive-sfi-dup")))
(defconst *sfi-t-ix-wrong*
  (fn-rii-ix-of (fn-cnode-node (fn-cnode-initial (fn-cfg-initial)))))
(assert-event
 (let* ((r0 (fn-sco-cpr *sfi-t-base*))
        (node (fn-cnode-node (fn-sco-at 1 r0))))
   (and (fn-sco-pausedp r0)
        (fn-cnode-statep (fn-sco-at 1 r0))
        (not (equal (car *sfi-t-ix-wrong*) (car (fn-rii-ix-of node))))
        (equal (car *sfi-t-ix*) (car (fn-rii-ix-of node)))
        (equal (fn-replay-result-kind
                (car (sfi-t-raw-resume r0 *sfi-t-configs* *sfi-t-q-dup* *sfi-t-ix-wrong*)))
               :paused)
        (equal (fn-replay-result-kind (fn-sco-cpr-resume r0 *sfi-t-configs* *sfi-t-q-dup*))
               :fault)
        (equal (fn-replay-result-kind
                (car (sfi-t-raw-resume r0 *sfi-t-configs* *sfi-t-q-dup* *sfi-t-ix*)))
               :fault))))
; HYPOTHESIS REMOVAL (2): the carried verdict.  The bad base carries (its
; pause is configured) and its verdict is not :ok; the carried open says :ok
; under the lie and differs from the twin.
(defconst *sfi-t-bad-ix* (fn-sfi-carry *sfi-t-bad-base*))
(assert-event
 (let ((bad-round (sfi-t-raw-extend *sfi-t-bad-base* *sfi-t-bad-ix* *sfi-t-configs*
                                    *sfi-t-bad-q* *sfi-t-f1*
                                    (len (fn-sco-records *sfi-t-bad-base*))
                                    *sfi-t-bad-next*)))
 (and (consp *sfi-t-bad-ix*)
      (not (equal (fn-sn-open-kind
                   (fn-sco-finalize *sfi-t-bad-base* *sfi-t-configs* *sfi-t-f0*))
                  :ok))
      (equal (fn-sn-open-kind (cadr (caddr bad-round))) :ok)
      (not (equal (list (car bad-round) (caddr bad-round))
                  (fn-rii-sco-extend-open *sfi-t-bad-base* *sfi-t-configs* *sfi-t-bad-q*
                                          *sfi-t-f1*))))))
(must-fail-checked
 (defthm sfi-t-without-the-carried-verdict
   (equal (list (car (fn-sfi-extend-open-carried *sfi-t-bad-base* *sfi-t-bad-ix* *sfi-t-configs*
                                                 *sfi-t-bad-q* *sfi-t-f1*
                                                 (len (fn-sco-records *sfi-t-bad-base*))
                                                 *sfi-t-bad-next*))
                (caddr (fn-sfi-extend-open-carried *sfi-t-bad-base* *sfi-t-bad-ix* *sfi-t-configs*
                                                   *sfi-t-bad-q* *sfi-t-f1*
                                                   (len (fn-sco-records *sfi-t-bad-base*))
                                                   *sfi-t-bad-next*)))
          (fn-rii-sco-extend-open *sfi-t-bad-base* *sfi-t-configs* *sfi-t-bad-q* *sfi-t-f1*))))

; HYPOTHESIS REMOVAL (3) and (4): the bound and the count.  The bound
; omitted (NEXT = 0 where the prefix left 8): at frontier 7 with no suffix
; the twin refuses the history, the carried open reaches the node's frontier
; check.  The count omitted (0 where the prefix has 3): the consumer fold
; resumes at the wrong position and the extension differs.  The other
; hypotheses hold in both.
(assert-event
 (and (equal (fn-sf-next-lower (fn-sco-records *sfi-t-base*) 0) 8)
      (equal (cadr (caddr (sfi-t-raw-extend *sfi-t-base* *sfi-t-ix* *sfi-t-configs* nil 7
                                            *sfi-t-count* 0)))
             (fn-sn-open-error :frontier))
      (equal (cadr (cadr (fn-rii-sco-extend-open *sfi-t-base* *sfi-t-configs* nil 7)))
             (fn-sn-open-error :history))
      (equal *sfi-t-count* 3)
      (not (equal (car (sfi-t-raw-extend *sfi-t-base* *sfi-t-ix* *sfi-t-configs* *sfi-t-q*
                                         *sfi-t-f1* 0 *sfi-t-next*))
                  (fn-sco-extend *sfi-t-base* *sfi-t-configs* *sfi-t-q*)))))

; THE BOUND (fn-sfi-cpr-resume-carried-steps-bounded): one suffix record,
; one step; the count is the counters' advance, under |configs| + |Q|.
(assert-event
 (let* ((r0 (fn-sco-cpr *sfi-t-base*))
        (r1 (car (sfi-t-raw-resume r0 *sfi-t-configs* *sfi-t-q* *sfi-t-ix*)))
        (steps (sfi-t-raw-steps r0 *sfi-t-configs* *sfi-t-q* *sfi-t-ix*)))
   (and (equal steps 1)
        (equal steps (+ (- (fn-sco-at 2 r1) (fn-sco-at 2 r0))
                        (- (fn-sco-at 3 r1) (fn-sco-at 3 r0))))
        (<= steps (+ (len *sfi-t-configs*) (len *sfi-t-q*))))))

; THE EXECUTED PATH: the callee closure over the :exec side of every mbe.
; The carried resume reaches neither fn-cnode-statep (the paused-node check)
; nor fn-rii-ix-of (the trie rebuild); the twin's resume reaches both; the
; trie step fn-rii-ix-next is what runs; no rebuild anywhere in the entry;
; the paused branch's drain and finalize name no node check -- only the
; fault branch, fn-rii-sco-store-open, does.
(mutual-recursion
 (defun sfi-t-exec-fnnames (term)
   (declare (xargs :mode :program))
   (cond ((or (atom term) (fquotep term)) nil)
         ((flambdap (ffn-symb term))
          (append (sfi-t-exec-fnnames (lambda-body (ffn-symb term)))
                  (sfi-t-exec-fnnames-lst (fargs term))))
         ((and (eq (ffn-symb term) 'return-last)
               (quotep (fargn term 1))
               (eq (unquote (fargn term 1)) 'mbe1-raw))
          (sfi-t-exec-fnnames (fargn term 2)))
         (t (cons (ffn-symb term) (sfi-t-exec-fnnames-lst (fargs term))))))
 (defun sfi-t-exec-fnnames-lst (terms)
   (declare (xargs :mode :program))
   (if (endp terms) nil
     (append (sfi-t-exec-fnnames (car terms)) (sfi-t-exec-fnnames-lst (cdr terms))))))
(defun sfi-t-exec-closure (fns seen wrld)
  (declare (xargs :mode :program))
  (cond ((endp fns) seen)
        ((member-eq (car fns) seen) (sfi-t-exec-closure (cdr fns) seen wrld))
        (t (let ((body (getpropc (car fns) 'unnormalized-body nil wrld)))
             (sfi-t-exec-closure (append (sfi-t-exec-fnnames body) (cdr fns))
                                 (cons (car fns) seen) wrld)))))
(assert-event
 (let ((mine (sfi-t-exec-closure '(fn-sfi-cpr-resume-carried) nil (w state)))
       (twin (sfi-t-exec-closure '(fn-rii-sco-cpr-resume) nil (w state)))
       (entry (sfi-t-exec-closure '(fn-sfi-extend-open-carried) nil (w state)))
       (drain (sfi-t-exec-closure '(fn-rii-sco-cpr-finish-configured fn-sfi-finalize-carried)
                                  nil (w state)))
       (fault (sfi-t-exec-closure '(fn-rii-sco-store-open) nil (w state))))
   (and (not (member-eq 'fn-cnode-statep mine))
        (not (member-eq 'fn-rii-ix-of mine))
        (member-eq 'fn-rii-ix-next mine)
        (member-eq 'fn-cnode-statep twin)
        (member-eq 'fn-rii-ix-of twin)
        (not (member-eq 'fn-rii-ix-of entry))
        (not (member-eq 'fn-cnode-statep drain))
        (member-eq 'fn-cnode-statep fault))))
