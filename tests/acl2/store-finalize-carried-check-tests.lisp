; store-finalize-carried-check-tests.lisp -- teeth for PRF-1005 (lane
; incremental-finalize-3): fn-sfk-carried-check, the carried pair's
; invariant made decidable, per literal theorem, and item (3) of the lane's
; brief: the wrong trie the logic cannot see is named at the boundary.
;
; The history is the twin book's test history as store-finalize-incremental-
; tests uses it: an undertaking, its release, an article at transaction 7;
; the base finalizes :ok at 8; a second article at 8 after the capture.

(in-package "ACL2")

(include-book "../../books/store-finalize-carried-check")

(defconst *sfk-t-stamp* *fn-cfg-default-stamp*)
(defconst *sfk-t-undertake*
  (fn-store-retention-event-make :undertake 0 0 0
                                 "forward-sfk" "subject" "evidence" 10))
(defconst *sfk-t-release*
  (fn-store-retention-event-make :release 1 1 1
                                 "forward-sfk" "subject" "evidence" 0))
(defconst *sfk-t-decrease*
  (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *sfk-t-stamp*))
(defconst *sfk-t-increase*
  (fn-cfg-record-make 2 7 3 (list (fn-cfg-set-capacity 20)) *sfk-t-stamp*))
(defun sfk-t-article (sequence txid msgid obligation)
  (fn-held-plain (fn-record-make sequence txid txid msgid '(65) '("fn.test")
                                 obligation "subject" "evidence" 2 841000000)
                 sequence))
(defconst *sfk-t-article* (sfk-t-article 2 7 "<sfk@example.invalid>" "archive-sfk"))
(defconst *sfk-t-article-2*
  (sfk-t-article 3 8 "<sfk-2@example.invalid>" "archive-sfk-2"))
(defconst *sfk-t-configs*
  (list *fn-cfg-default-record* *sfk-t-decrease* *sfk-t-increase*))
(defconst *sfk-t-prefix* (list *sfk-t-undertake* *sfk-t-release* *sfk-t-article*))
(defconst *sfk-t-base* (fn-sco-capture *sfk-t-configs* *sfk-t-prefix*))
(defconst *sfk-t-q* (list *sfk-t-article-2*))
(defconst *sfk-t-f1* 9)
(defconst *sfk-t-count* (len (fn-sco-records *sfk-t-base*)))
(defconst *sfk-t-next* (fn-sf-next-lower (fn-sco-records *sfk-t-base*) 0))
(defconst *sfk-t-r0* (fn-sco-cpr *sfk-t-base*))
(defconst *sfk-t-ix* (fn-sfi-carry *sfk-t-base*))

; The carried entries run raw through :program wrappers (what the host and
; the served image execute; the evaluator cannot run their guard).
(defun sfk-t-raw-resume (r configs events ix)
  (declare (xargs :mode :program))
  (fn-sfi-cpr-resume-carried r configs events ix))
(defun sfk-t-raw-extend (c ix configs suffix frontier count next)
  (declare (xargs :mode :program))
  (fn-sfi-extend-open-carried c ix configs suffix frontier count next))

; -----------------------------------------------------------------------------
; :ok -- the open's own pair (fn-sfk-carry-checks-ok's witness), and the
; pair a carried round answers, checked against the round's own pause.
(assert-event
 (and *sfk-t-ix*
      (equal (fn-sfk-carried-check *sfk-t-r0* *sfk-t-ix*) :ok)))

(assert-event
 (let* ((round-1 (sfk-t-raw-extend *sfk-t-base* *sfk-t-ix* *sfk-t-configs* *sfk-t-q*
                                   *sfk-t-f1* *sfk-t-count* *sfk-t-next*))
        (e1 (car round-1))
        (ix1 (cadr round-1)))
   (and (equal (fn-sn-open-kind (cadr (caddr round-1))) :ok)
        (equal (fn-sfk-carried-check (fn-sco-cpr e1) ix1) :ok))))

; -----------------------------------------------------------------------------
; :wrong-msgid-trie -- the empty node's tries standing in for the base's
; (store-finalize-incremental-tests' served-path witness).  Item (3): in the
; logic the wrong trie is invisible (the twin's inner mbe :logic sides
; answer from the node), on the served path (raw) it ADMITS a duplicate
; Message-ID that the right pair refuses; the check names it.
(defconst *sfk-t-q-dup*
  (list (sfk-t-article 3 8 "<sfk@example.invalid>" "archive-sfk-dup")))
(defconst *sfk-t-ix-wrong*
  (fn-rii-ix-of (fn-cnode-node (fn-cnode-initial (fn-cfg-initial)))))
(assert-event
 (and (equal (fn-sfk-carried-check *sfk-t-r0* *sfk-t-ix-wrong*) :wrong-msgid-trie)
      ; the served path with the wrong pair admits the duplicate (a pause) ...
      (equal (fn-replay-result-kind
              (car (sfk-t-raw-resume *sfk-t-r0* *sfk-t-configs* *sfk-t-q-dup* *sfk-t-ix-wrong*)))
             :paused)
      ; ... where the right pair refuses it
      (not (equal (fn-replay-result-kind
                   (car (sfk-t-raw-resume *sfk-t-r0* *sfk-t-configs* *sfk-t-q-dup* *sfk-t-ix*)))
                  :paused))))

; -----------------------------------------------------------------------------
; The shape answers, each by its own conjunct.
(assert-event
 (and (equal (fn-sfk-carried-check *sfk-t-r0* nil) :not-a-pair)
      (equal (fn-sfk-carried-check *sfk-t-r0* 7) :not-a-pair)
      (equal (fn-sfk-carried-check nil *sfk-t-ix*) :not-paused)
      (equal (fn-sfk-carried-check (fn-sco-cpr (fn-sco-capture *sfk-t-configs* nil))
                                   *sfk-t-ix*)
             (fn-sfk-carried-check (fn-sco-cpr (fn-sco-capture *sfk-t-configs* nil))
                                   *sfk-t-ix*))))

; :uncertain-id-trie is reachable: the right Message-ID trie with a foreign
; id trie.  The check decides nothing there, and says so.
(assert-event
 (equal (fn-sfk-carried-check *sfk-t-r0* (cons (car *sfk-t-ix*) (cdr *sfk-t-ix-wrong*)))
        :uncertain-id-trie))
