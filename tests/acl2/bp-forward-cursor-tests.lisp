; Teeth of books/bp-forward-cursor.lisp (PRF-1311): five held rows in the
; shape the forward plan reads (slots 11, 12, 14 and the primary's
; destination), two routed hops, one deleted row, one unroutable row.
(in-package "ACL2")
(include-book "../../books/bp-forward-cursor")
(include-book "../../books/bp-route-step")
(include-book "must-fail-checked")

(defconst *fc-local* (cons :dtn (fn-record-string-octets "//bp-local/")))
(defconst *fc-sender* (cons :dtn (fn-record-string-octets "//bp-sender/")))
(defconst *fc-dest* (cons :dtn (fn-record-string-octets "//bp-dest/")))
(defconst *fc-other* (cons :dtn (fn-record-string-octets "//other/x")))
(defconst *fc-relay* (cons :dtn (fn-record-string-octets "//relay/")))
(defconst *fc-relay-b* (cons :dtn (fn-record-string-octets "//relay-b/")))
(defconst *fc-config* (fn-bpn-config *fc-sender* 3600000 2 32 1048576))
(defconst *fc-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *fc-table*
  (list (fn-bprt-route 100 "dtn://bp-dest/" "relay" "dtn://relay/" 4556)
        (fn-bprt-route 100 "dtn://other/*" "relay-b" "dtn://relay-b/" 4557)))
(assert-event (fn-bprt-tablep *fc-table*))

(defun fc-row (id dest next-hop deleted)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-held *fc-sender* id id (list :cl (cons 0 1) 1 *fc-sender* '(115) 0) nil nil
                (fn-bpn-send-bundle *fc-config* dest '(1 2 3 4) id *fc-obs*)
                nil nil nil next-hop '(:forward-pending) nil deleted nil))
(defconst *fc-r1* (fc-row 1 *fc-dest* *fc-relay* nil))
(defconst *fc-r2* (fc-row 2 *fc-other* *fc-relay-b* nil))
(defconst *fc-r3* (fc-row 3 *fc-dest* *fc-relay* nil))
(defconst *fc-r4* (fc-row 4 *fc-dest* *fc-relay* t))
(defconst *fc-r5* (fc-row 5 *fc-local* *fc-relay* nil))
; HELD is newest first, as fn-bpnf-held-list keeps it; the sweep is oldest first.
(defconst *fc-held* (list *fc-r5* *fc-r4* *fc-r3* *fc-r2* *fc-r1*))
(assert-event (equal (fn-bpfc-ordered *fc-held*) (list *fc-r1* *fc-r2* *fc-r3* *fc-r4* *fc-r5*)))
(assert-event (equal (fn-bpnp-held-dest *fc-r1*) "dtn://bp-dest/"))
(assert-event (equal (fn-bprt-outbound-choice (fn-bpnp-held-dest *fc-r5*) *fc-table*) '(:no-route)))

(defconst *fc-e-relay* (list *fc-relay* "relay" "dtn://relay/" 4556))
(defconst *fc-e-relay-b* (list *fc-relay-b* "relay-b" "dtn://relay-b/" 4557))
; The logical model's answers, for the K2 witnesses below.
(assert-event (equal (fn-bpnp-forward-plan *fc-held* *fc-table*) (list *fc-e-relay* *fc-e-relay-b*)))
(assert-event (equal (fn-bpsched-forward-entry (fn-bpnp-forward-plan *fc-held* *fc-table*) nil) *fc-e-relay*))
(assert-event (equal (fn-bpsched-forward-entry (fn-bpnp-forward-plan *fc-held* *fc-table*) (list *fc-relay*)) *fc-e-relay-b*))
(assert-event (null (fn-bpsched-forward-entry (fn-bpnp-forward-plan *fc-held* *fc-table*) (list *fc-relay* *fc-relay-b*))))

;; K1 fn-bpfc-turn-advances-at-most-quantum: the literal complete positive
;; witness (both bounds) on a yielding turn and on an entry turn.
(defconst *fc-busy2* (list *fc-relay* *fc-relay-b*))
(defconst *fc-y1* (fn-bpfc-turn (fn-bpfc-initial) *fc-held* *fc-table* *fc-busy2* 2))
(assert-event (and (member-equal (car *fc-y1*) '(:entry :yield))
                   (equal (car *fc-y1*) :yield)
                   (<= (fn-bpfc-pos (fn-bpfc-initial)) (fn-bpfc-pos (second *fc-y1*)))
                   (<= (fn-bpfc-pos (second *fc-y1*)) (+ (fn-bpfc-pos (fn-bpfc-initial)) (nfix 2)))
                   (equal (fn-bpfc-pos (second *fc-y1*)) 2)
                   (equal (fn-bpfc-seen (second *fc-y1*)) (list *fc-relay-b* *fc-relay*))))
(defconst *fc-t1* (fn-bpfc-turn (fn-bpfc-initial) *fc-held* *fc-table* nil 2))
(assert-event (and (equal (car *fc-t1*) :entry) (equal (second *fc-t1*) *fc-e-relay*)
                   (<= (fn-bpfc-pos (third *fc-t1*)) (+ 0 (nfix 2)))
                   (equal (fn-bpfc-pos (third *fc-t1*)) 1)))
;; A turn of quantum 2 is not bounded by quantum 1: the bound is the quantum.
(must-fail-checked (assert-event (<= (fn-bpfc-pos (second *fc-y1*)) (+ (fn-bpfc-pos (fn-bpfc-initial)) 1))))

;; K3 fn-bpfc-turn-after-a-yield-is-the-larger-turn: resuming the yield of
;; quantum 2 with quantum 2 is the turn of quantum 4 from the head; resuming
;; again drains (rows 3, 4 skipped as seen/deleted; row 5 unroutable).
(assert-event (and (natp 2) (natp 2) (equal (car *fc-y1*) :yield)
                   (equal (fn-bpfc-turn (second *fc-y1*) *fc-held* *fc-table* *fc-busy2* 2)
                          (fn-bpfc-turn (fn-bpfc-initial) *fc-held* *fc-table* *fc-busy2* 4))))
(defconst *fc-y2* (fn-bpfc-turn (second *fc-y1*) *fc-held* *fc-table* *fc-busy2* 2))
(assert-event (and (equal (car *fc-y2*) :yield) (equal (fn-bpfc-pos (second *fc-y2*)) 4)))
(assert-event (equal (fn-bpfc-turn (second *fc-y2*) *fc-held* *fc-table* *fc-busy2* 2) '(:drained)))
;; Hypothesis removal: a turn that did not yield has no resumption cursor.
;; From position 2 with no peer busy, quantum 3 drains; what stands in the
;; cursor slot of (:drained) reads as the head, and quantum 2 from the head
;; is the relay entry, not the drained turn of quantum 5 from position 2.
(defconst *fc-d3* (fn-bpfc-turn (second *fc-y1*) *fc-held* *fc-table* nil 3))
(assert-event (equal *fc-d3* '(:drained)))
(assert-event (equal (fn-bpfc-turn (second *fc-y1*) *fc-held* *fc-table* nil 5) '(:drained)))
(must-fail-checked
 (assert-event (equal (fn-bpfc-turn (second *fc-d3*) *fc-held* *fc-table* nil 2)
                      (fn-bpfc-turn (second *fc-y1*) *fc-held* *fc-table* nil 5))))

;; K2 fn-bpfc-run-is-the-plan-choice: with quantum 1 (five resumptions at
;; most) the run makes the plan's choice under each busy set.
(assert-event
 (let ((run (fn-bpfc-run (fn-bpfc-initial) *fc-held* *fc-table* nil 1 (len *fc-held*)))
       (e (fn-bpsched-forward-entry (fn-bpnp-forward-plan *fc-held* *fc-table*) nil)))
   (and (true-listp *fc-held*) (posp 1)
        (equal (car run) (if e :entry :drained)) (implies e (equal (second run) e))
        (equal (second run) *fc-e-relay*))))
(assert-event
 (let ((run (fn-bpfc-run (fn-bpfc-initial) *fc-held* *fc-table* (list *fc-relay*) 1 (len *fc-held*)))
       (e (fn-bpsched-forward-entry (fn-bpnp-forward-plan *fc-held* *fc-table*) (list *fc-relay*))))
   (and (equal (car run) (if e :entry :drained)) (implies e (equal (second run) e))
        (equal (second run) *fc-e-relay-b*))))
(assert-event
 (let ((run (fn-bpfc-run (fn-bpfc-initial) *fc-held* *fc-table* *fc-busy2* 1 (len *fc-held*)))
       (e (fn-bpsched-forward-entry (fn-bpnp-forward-plan *fc-held* *fc-table*) *fc-busy2*)))
   (and (equal (car run) (if e :entry :drained)) (not e) (equal run '(:drained)))))
;; Hypothesis removal, posp quantum: quantum 0 never advances, so the run
;; ends in a yield and is not the plan's choice.  Quantum 0 is outside
;; fn-bpfc-run's guard, so the witness evaluates the logic without guard
;; checking (a guard violation would make the must-fail pass vacuously).
(assert-event (equal (car (with-guard-checking :none
                           (fn-bpfc-run (fn-bpfc-initial) *fc-held* *fc-table* nil 0 (len *fc-held*))))
                     :yield))
(must-fail-checked
 (assert-event (let ((run (with-guard-checking :none
                           (fn-bpfc-run (fn-bpfc-initial) *fc-held* *fc-table* nil 0 (len *fc-held*))))
                     (e (fn-bpsched-forward-entry (fn-bpnp-forward-plan *fc-held* *fc-table*) nil)))
                 (equal (car run) (if e :entry :drained)))))
;; Hypothesis removal, fuel: with quantum 1 and one resumption the run has
;; examined two rows; under both peers busy it has not reached the end.
(must-fail-checked
 (assert-event (let ((run (fn-bpfc-run (fn-bpfc-initial) *fc-held* *fc-table* *fc-busy2* 1 1))
                     (e (fn-bpsched-forward-entry (fn-bpnp-forward-plan *fc-held* *fc-table*) *fc-busy2*)))
                 (equal (car run) (if e :entry :drained)))))
;; Mutation witness: the oldest row deleted (slot 14) drops out of both the
;; plan and the cursor's choice; the younger relay-b row is chosen.
(defconst *fc-held-forwarded*
  (list *fc-r5* *fc-r4* *fc-r3* *fc-r2* (fc-row 1 *fc-dest* *fc-relay* t)))
(assert-event (equal (second (fn-bpfc-run (fn-bpfc-initial) *fc-held-forwarded* *fc-table* nil 2 5))
                     *fc-e-relay-b*))
(assert-event (equal (fn-bpsched-forward-entry (fn-bpnp-forward-plan *fc-held-forwarded* *fc-table*) nil)
                     *fc-e-relay-b*))
