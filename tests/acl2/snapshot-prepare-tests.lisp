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
