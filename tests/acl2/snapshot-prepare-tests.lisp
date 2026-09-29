(in-package "ACL2")
(include-book "../../books/snapshot-prepare")
(defconst *osp-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                       "forward-cpo" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                       "forward-cpo" "subject" "evidence" 0)))
(defconst *osp-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1))
                            *fn-cfg-default-stamp*)))
(defun osp-test-tick (cursor)
  (declare (xargs :guard t :verify-guards nil))
  (fn-osp-cpr-tick (nth 0 cursor) (nth 1 cursor) (nth 2 cursor)
                   (nth 3 cursor) (nth 4 cursor)))
(defconst *osp-t1* (osp-test-tick (fn-osp-cpr-begin *osp-configs* *osp-events*)))
(defconst *osp-t2* (osp-test-tick (cdr *osp-t1*)))
(defconst *osp-t3* (osp-test-tick (cdr *osp-t2*)))
(defconst *osp-t4* (osp-test-tick (cdr *osp-t3*)))
; Literal complete nonempty positive refinement witness, including refusal
; and paused-value equality (this theorem has no hypotheses).
(assert-event
 (equal (fn-osp-cpr-after *osp-t1*)
        (fn-sco-cpr-prefix (fn-cnode-initial (fn-cfg-initial))
                           *osp-configs* *osp-events* 0 0)))
; Literal full antecedent and every conclusion of one-input progress.
(assert-event
 (and (equal (car *osp-t1*) :continue) (consp *osp-events*)
      (or (and (consp *osp-configs*)
               (equal (nth 2 *osp-t1*) (cdr *osp-configs*))
               (equal (nth 3 *osp-t1*) *osp-events*))
          (and (equal (nth 2 *osp-t1*) *osp-configs*)
               (equal (nth 3 *osp-t1*) (cdr *osp-events*))))
      (equal (+ (len (nth 2 *osp-t1*)) (len (nth 3 *osp-t1*)))
             (- (+ (len *osp-configs*) (len *osp-events*)) 1))))
(assert-event
 (and (equal (car *osp-t2*) :continue)
      (fn-cnode-statep (nth 1 *osp-t2*))))
; Later configuration remains unconsumed when the final event is consumed;
; finishing this paused state drains it elsewhere, exactly as the format.
(assert-event
 (and (equal (car *osp-t4*) :done)
      (equal (nth 1 *osp-t4*)
             (fn-sco-cpr-prefix (fn-cnode-initial (fn-cfg-initial))
                                *osp-configs* *osp-events* 0 0))
      (equal (nth 2 (nth 1 *osp-t4*)) 1)
      (equal (nth 3 (nth 1 *osp-t4*)) 2)))
 ; Hypothesis-removal for progress: a completed cursor fails continuation
; and the full conclusion, since its remaining event list is empty.
(assert-event
 (and (not (equal (car *osp-t4*) :continue))
      (not (and (consp (nth 3 *osp-t3*))
                (or (and (consp (nth 2 *osp-t3*))
                         (equal (nth 2 *osp-t4*) (cdr (nth 2 *osp-t3*)))
                         (equal (nth 3 *osp-t4*) (nth 3 *osp-t3*)))
                    (and (equal (nth 2 *osp-t4*) (nth 2 *osp-t3*))
                         (equal (nth 3 *osp-t4*) (cdr (nth 3 *osp-t3*)))))
                (equal (+ (len (nth 2 *osp-t4*)) (len (nth 3 *osp-t4*)))
                       (- (+ (len (nth 2 *osp-t3*)) (len (nth 3 *osp-t3*))) 1))))))

(defconst *osp-f0* (fn-osp-fold-begin *osp-events*))
(defconst *osp-f1* (nth 1 (fn-osp-fold-tick *osp-f0*)))
(defconst *osp-f2* (nth 1 (fn-osp-fold-tick *osp-f1*)))
; Full antecedent and conclusion of four-summary refinement.
(assert-event
 (and (fn-sco-store-eventsp (fn-sco-at 0 *osp-f0*))
      (implies (equal (fn-sco-at 0 (fn-sco-at 2 *osp-f0*)) :ok)
               (equal (fn-sco-at 2 *osp-f0*)
                      (list :ok (fn-sco-at 1 (fn-sco-at 2 *osp-f0*)))))
      (equal (fn-osp-fold-value *osp-f0*)
             (let ((tick (fn-osp-fold-tick *osp-f0*)))
               (if (equal (car tick) :continue)
                   (fn-osp-fold-value (nth 1 tick)) (nth 1 tick))))))
(assert-event
 (let ((tick (fn-osp-fold-tick *osp-f0*)))
   (and (equal (car tick) :continue)
        (consp (fn-sco-at 0 *osp-f0*))
        (equal (fn-sco-at 0 (nth 1 tick)) (cdr (fn-sco-at 0 *osp-f0*)))
        (equal (fn-sco-at 5 (nth 1 tick)) (+ 1 (fn-sco-at 5 *osp-f0*)))
        (natp (fn-sco-at 5 *osp-f0*)) (natp (fn-sco-at 5 (nth 1 tick))))))
(assert-event
 (let ((captured (fn-sco-capture *osp-configs* *osp-events*)))
   (and (equal (car (fn-osp-fold-tick *osp-f2*)) :done)
        (equal (nth 1 (fn-osp-fold-tick *osp-f2*))
               (list (fn-sco-identity captured) (fn-sco-consumer captured)
                     (fn-sco-topic captured) (fn-sco-event-index captured))))))
; Hypothesis-removal, malformed captured record: keep normalized consumer,
; fail the event-list hypothesis, and fail retained full-fold equality.
(defconst *osp-bad-record* (fn-osp-fold-begin '(bad)))
(assert-event
 (and (not (fn-sco-store-eventsp (fn-sco-at 0 *osp-bad-record*)))
      (implies (equal (fn-sco-at 0 (fn-sco-at 2 *osp-bad-record*)) :ok)
               (equal (fn-sco-at 2 *osp-bad-record*)
                      (list :ok (fn-sco-at 1 (fn-sco-at 2 *osp-bad-record*)))))
      (not (equal (fn-osp-fold-value *osp-bad-record*)
                  (fn-osp-fold-value (nth 1 (fn-osp-fold-tick *osp-bad-record*)))))))
; Corrupted private cursor, separately labelled: keep the event-list
; hypothesis, fail normalized-consumer hypothesis and full-fold equality.
(defconst *osp-bad-consumer* (update-nth 2 '(:ok nil junk) (fn-osp-fold-begin nil)))
(assert-event
 (and (fn-sco-store-eventsp (fn-sco-at 0 *osp-bad-consumer*))
      (equal (fn-sco-at 0 (fn-sco-at 2 *osp-bad-consumer*)) :ok)
      (not (equal (fn-sco-at 2 *osp-bad-consumer*)
                  (list :ok (fn-sco-at 1 (fn-sco-at 2 *osp-bad-consumer*)))))
      (not (equal (fn-osp-fold-value *osp-bad-consumer*)
                  (nth 1 (fn-osp-fold-tick *osp-bad-consumer*))))))

; Reachable article rows are interned into an arena containing an orphan;
; canonical handles must differ from the source handles while alpha stays.
(defconst *osp-canon-wire*
  (list (fn-record-make 0 0 0 "<snapshot-one@example>" '(1 2 3)
                        '("fn.test") "p" "c" "r" 1 841000000)
        (fn-record-make 1 1 0 "<snapshot-two@example>" '(65 66)
                        '("fn.test") "p" "c" "r" 1 841000001)))
(defun osp-canon-test-run (cursor fuel fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) :fuel-exhausted
    (let ((tick (fn-osp-canon-tick cursor fn-arena)))
      (if (equal (car tick) :continue)
          (osp-canon-test-run (nth 1 tick) (- fuel 1) fn-arena)
        tick))))
(defun osp-canon-positive-tooth ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (let ((fn-arena (fn-arena-seal-list '(99 99) fn-arena)))
        (mv-let (rows fn-arena)
          (fn-intern-events *osp-canon-wire* nil 0 fn-arena)
          (let* ((cursor (fn-osp-canon-begin rows))
                 (tick (fn-osp-canon-tick cursor fn-arena))
                 (next (nth 1 tick))
                 (all (osp-canon-test-run cursor 8 fn-arena)))
            (mv
             (and (equal (fn-record-payload (car rows)) 1)
                  ; Literal complete refinement antecedent/conclusion.
                  (member-equal (fn-sco-at 0 cursor) '(:canon :reverse))
                  (true-listp (fn-sco-at 1 cursor))
                  (true-listp (fn-sco-at 3 cursor))
                  (equal (fn-osp-canon-value cursor fn-arena)
                         (if (equal (car tick) :continue)
                             (fn-osp-canon-value next fn-arena) (nth 1 tick)))
                  ; Row progress: the entire positive row branch.
                  (equal (car tick) :continue)
                  (equal (fn-sco-at 0 cursor) :canon)
                  (consp (fn-sco-at 1 cursor))
                  (equal (fn-sco-at 0 next) :canon)
                  (equal (fn-sco-at 1 next) (cdr (fn-sco-at 1 cursor)))
                  ; Complete executable-cursor preservation witness.
                  (natp (fn-sco-at 2 cursor))
                  (true-listp (fn-sco-at 4 cursor))
                  (natp (fn-sco-at 2 next))
                  (true-listp (fn-sco-at 1 next))
                  (true-listp (fn-sco-at 3 next))
                  (true-listp (fn-sco-at 4 next))
                  ; All ticks, including cell-wise reverse, equal old writer.
                  (equal (car all) :done)
                  (equal (nth 1 all) (fn-scka-canon-rows rows fn-arena 0))
                  (equal (fn-record-payload (car (nth 1 all))) 0)
                  (equal (fn-rows-wire-of (nth 1 all) fn-arena)
                         (fn-rows-wire-of (fn-scka-canon-rows rows fn-arena 0) fn-arena)))
             fn-arena))))
      out)))
(assert-event (osp-canon-positive-tooth))
; Corrupted private cursor: remaining-list hypothesis removed.  All other
; refinement hypotheses are affirmed, and the exact conclusion fails.
(assert-event
 (let* ((cursor '(:canon 7 0 nil nil))
        (tick (fn-osp-canon-tick cursor fn-arena)))
   (and (member-equal (fn-sco-at 0 cursor) '(:canon :reverse))
        (true-listp (fn-sco-at 3 cursor))
        (not (true-listp (fn-sco-at 1 cursor)))
        (not (equal (fn-osp-canon-value cursor fn-arena)
                    (if (equal (car tick) :continue)
                        (fn-osp-canon-value (nth 1 tick) fn-arena) (nth 1 tick)))))))
; Corrupted phase: remaining-list hypothesis retained, phase fails and the
; exact refinement conclusion fails; no externally reachable-state claim.
(assert-event
 (let* ((cursor '(:bad nil 0 nil nil))
        (tick (fn-osp-canon-tick cursor fn-arena)))
   (and (true-listp (fn-sco-at 1 cursor))
        (true-listp (fn-sco-at 3 cursor))
        (not (member-equal (fn-sco-at 0 cursor) '(:canon :reverse)))
        (not (equal (fn-osp-canon-value cursor fn-arena)
                    (if (equal (car tick) :continue)
                        (fn-osp-canon-value (nth 1 tick) fn-arena) (nth 1 tick)))))))

; Completed actual configured/summary values assemble the original tuple;
; this literal boundary witness has nonempty retained obligations/history.
(assert-event
 (let* ((configured (nth 1 *osp-t4*))
        (summaries (nth 1 (fn-osp-fold-tick *osp-f2*))))
   (and (true-listp *osp-events*)
        (equal configured
               (fn-sco-cpr-prefix (fn-cnode-initial (fn-cfg-initial))
                                  *osp-configs* *osp-events* 0 0))
        (equal summaries (fn-osp-fold-value (fn-osp-fold-begin *osp-events*)))
        (equal (fn-osp-assemble *osp-events* configured summaries)
               (fn-sco-capture *osp-configs* *osp-events*)))))
