; fn: RTC-U64 boundary witnesses and coordinator-ruled retirement teeth.
(in-package "ACL2")
(include-book "../../books/runtime-contract-u64")

; No attached stobj computations appear in compiled constants.
(with-guard-checking-event
 nil
 (assert-event
  (let ((slots '((0 :live nil) (18446744073709551615 :free nil) (0 :free nil))))
    (and (fn-rtc-slotp (fn-rtc-get 1 slots))
         (equal (fn-rtc-s-status (fn-rtc-get 1 slots)) :free)
         (equal (+ 1 (fn-rtc-s-inc (fn-rtc-get 1 slots)))
                18446744073709551616)
         (not (fn-rtc-slot-selectablep (fn-rtc-get 1 slots)))
         (equal (fn-rtc-free-slot 0 slots) 2)
         (fn-rtc-inc-roomp (fn-rtc-get 2 slots))
         (equal (+ 1 (fn-rtc-s-inc (fn-rtc-get 2 slots))) 1)))))

; The old selector's lowest free record is retired; no selectable record remains.
(with-guard-checking-event
 nil
 (assert-event
  (let ((s '((2 0 0 0 0 0 0 0 0)
              ((0 :live nil) (18446744073709551615 :free nil))
              nil nil (nil nil) 1)))
    (mv-let (s2 acts2) (fn-rtc-rearm s)
      (declare (ignore acts2))
      (and (equal (fn-rtc-s-status (fn-rtc-slot 1 s)) :free)
           (posp 1)
           (not (fn-rtc-inc-roomp (fn-rtc-slot 1 s)))
           (not (fn-rtc-free-slot 0 (fn-rtc-slots s)))
           (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s2))))))))

; Counterexample to books/runtime-contract-invariant.lisp:970.
; Both old and replacement records are u64-typed free slots.
(defthm fn-a24-free-slot-of-set-free-counterexample
  (let ((i 0) (k 1)
        (slots '((0 :live nil) (0 :free nil)))
        (slot '(18446744073709551615 :free nil)))
    (and (natp i)
         (natp k)
         (fn-rtc-free-slot i slots)
         (equal (fn-rtc-s-status slot) :free)
         (fn-rtc-slotp slot)
         (not (fn-rtc-free-slot i (fn-rtc-set k slot slots)))))
  :rule-classes nil)


(defthm fn-a24-m-max-state-positive
  (<= 1 (fn-rtc-m-max-state))
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-m-init-is-bounded
           :in-theory (disable fn-rtc-m-init-is-bounded))))
(defthm fn-a24-t13-counterexample
  (let* ((s '((2 0 0 0 0 0 0 0 0)
              ((0 :live nil) (18446744073709551615 :draining 7))
              nil ((:timer 1 18446744073709551615 0 nil)) (nil nil) 1))
         (j 1)
         (u '(:timer 1 18446744073709551615 0 nil))
         (e '(:timer 1 18446744073709551615 0 (:done 0)))
         (s2 (mv-nth 0 (fn-rtc-step s e 1))))
    (and (fn-rtc-invp s)
         (equal (fn-rtc-s-status (fn-rtc-slot j s)) :draining)
         (member-equal u (fn-rtc-uses s))
         (equal (fn-rtc-get 1 u) j)
         (fn-rtc-ends-use-p e u)
         (not (fn-rtc-uses-of-slot-p
               j (fn-rtc-s-inc (fn-rtc-slot j s))
               (fn-rtc-remove-use (fn-rtc-key u) (fn-rtc-uses s))))
         (equal (fn-rtc-s-status (fn-rtc-slot j s2)) :free)
         (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s2)))
         (iff (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s2))
              (fn-rtc-free-slot 0 (fn-rtc-slots s2)))
         (implies (fn-rtc-inc-roomp (fn-rtc-slot j s2))
                  (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-invp fn-rtc-step fn-rtc-step* fn-rtc-acts-on-p
                   fn-rtc-end-use fn-rtc-end-lease fn-rtc-retire-drained
                   fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant
                   fn-rtc-make fn-rtc-config fn-rtc-slots fn-rtc-uses
                   fn-rtc-mstates fn-rtc-next-op fn-rtc-with-uses fn-rtc-with-slot
                   fn-rtc-slot fn-rtc-s-inc fn-rtc-s-status fn-rtc-get
                   fn-rtc-kind-out-p fn-rtc-uses-of-slot-p fn-rtc-remove-use
                   fn-rtc-find-use fn-rtc-key fn-rtc-e-kind fn-rtc-e-id
                   fn-rtc-e-inc fn-rtc-e-op fn-rtc-e-outcome
                   fn-rtc-completionp fn-rtc-outcomep fn-rtc-usep fn-rtc-use-okp
                   fn-rtc-uses-okp fn-rtc-ends-use-p fn-rtc-op-used-p
                   fn-rtc-current-p fn-rtc-live-p fn-rtc-free-slot fn-rtc-slot-selectablep fn-rtc-inc-roomp
                   fn-rtc-configp fn-rtc-nslots fn-rtc-nbufs fn-rtc-nstatic
                   fn-rtc-qfixed fn-rtc-npool fn-rtc-capf fn-rtc-capl
                   fn-rtc-nhome fn-rtc-pool-buf-p fn-rtc-free-pool-buf
                   fn-rtc-oldest-wait fn-rtc-slots-okp fn-rtc-slotp
                   fn-rtc-statics-okp fn-rtc-pool-okp fn-rtc-draining-okp
                   fn-rtc-mstates-okp fn-rtc-size fn-rtc-u64p
                   fn-rtc-u-hd fn-rtc-handlep fn-rtc-hand-delivers-p)
            ((:executable-counterpart fn-rtc-mstates-okp)
             (:executable-counterpart fn-rtc-invp))))))

; Original-claim tooth: the raw constructor's old NATP-only implication is false.
; INC=2^64 is not the valid retired-record case INC=2^64-1.
(defthm fn-a24-free-slotp-u64-counterexample
  (and (natp 18446744073709551616)
       (not (fn-rtc-slotp (list 18446744073709551616 :free nil))))
  :rule-classes nil)

; Whole antecedent and conclusion of the approved bounded constructor.
(defthm fn-a24-free-slotp-witness
  (and (fn-rtc-u64p 0) (fn-rtc-slotp '(0 :free nil)))
  :rule-classes nil)

; Removing INVP permits an already invalid incarnation to persist through an
; unmatched completion. The preservation claim needs its real state premise.
(defthm fn-a24-invariant-bound-hypothesis-tooth
  (let* ((s '((2 0 0 0 0 0 0 0 0)
              ((0 :live nil) (18446744073709551616 :free nil))
              nil nil (nil nil) 1))
         (e '(:timer 1 0 99 (:done 0)))
         (s2 (mv-nth 0 (fn-rtc-step* s e 1))))
    (and (not (fn-rtc-invp s))
         (equal s2 s)
         (not (fn-rtc-u64p (fn-rtc-s-inc (fn-rtc-slot 1 s2))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-step*-state-is-step-state fn-rtc-step-state
                 fn-rtc-acts-on-p fn-rtc-end-use fn-rtc-retire-drained
                 fn-rtc-end-lease fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant
                 fn-rtc-invp fn-rtc-core-invp)
                ((:executable-counterpart fn-rtc-invp)
                 (:executable-counterpart fn-rtc-core-invp)
                 (:executable-counterpart fn-rtc-step*))))))

(defthm fn-a24-fresh-unbuffered-use-u64-tooth-nil
  (let* ((s '((2 0 0 0 0 0 0 0 0) ((0 :live nil) (18446744073709551616 :live 7)) nil nil (nil nil) 0))
         (kind :timer) (id 1) (inc 18446744073709551616))
    (and (member-eq kind '(:fsync :close :accept :timer :extend))
         (natp id) (natp inc) (< id (fn-rtc-nslots (fn-rtc-config s)))
         (fn-rtc-current-p id inc s)
         (iff (eq kind :accept) (equal id 0))
         (implies (eq kind :close) (eq (fn-rtc-s-status (fn-rtc-slot id s)) :closing))
         (not (fn-rtc-use-okp (list kind id inc (fn-rtc-next-op s) nil)
                (fn-rtc-issue (list kind id inc (fn-rtc-next-op s) nil) s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rtc-issue))))
(defthm fn-a24-fresh-wait-use-u64-tooth
  (let* ((s '((2 0 0 0 0 0 0 0 0) ((0 :live nil) (18446744073709551616 :live 7)) nil nil (nil nil) 0))
         (id 1) (inc 18446744073709551616))
    (and (natp id) (not (equal id 0)) (natp inc)
         (< id (fn-rtc-nslots (fn-rtc-config s))) (fn-rtc-current-p id inc s)
         (not (fn-rtc-use-okp (list :wait id inc (fn-rtc-next-op s) nil)
                (fn-rtc-issue (list :wait id inc (fn-rtc-next-op s) nil) s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rtc-issue))))
(defthm fn-a24-activate-slot-u64-tooth
  (let* ((s '((2 0 0 0 0 0 0 0 0) ((0 :live nil) (0 :free nil)) nil nil (nil nil) 0))
         (id 1) (inc 18446744073709551616) (r 7))
    (and (fn-rtc-core-invp s) (posp id) (natp inc) (natp r) (< r (expt 2 64))
         (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free)
         (not (fn-rtc-core-invp (fn-rtc-with-slot id (list inc :live r) s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rtc-core-invp fn-rtc-with-slot)
     ((:executable-counterpart fn-rtc-core-invp) (:executable-counterpart fn-rtc-mstates-okp))))))

(defthm fn-a24-hand-target-u64-counterexample
  (let* ((s '((3 1 1 1 0 1 1 0 0)
              ((0 :live nil) (1 :live 0) (0 :free nil))
              ((0 (:workspace 1 1) nil)) nil (nil nil nil) 0))
         (id 1) (inc 1) (hd '(0 0 0 0)) (extra '(2 18446744073709551616))
         (s2 (fn-rtc-hand-submit-state hd extra id inc s)))
    (and (fn-rtc-core-invp s)
         (fn-rtc-instance-active-p id inc s)
         (fn-rtc-live-p id inc s)
         (fn-rtc-submit-okp :hand hd id inc s)
         (fn-rtc-hand-target-okp extra id s)
         (fn-rtc-u64p inc)
         (not (fn-rtc-u64p (fn-rtc-get 1 extra)))
         (not (fn-rtc-extrap extra))
         (not (fn-rtc-ownerp (fn-rtc-b-owner (fn-rtc-buffer 0 s2))))
         (not (fn-rtc-core-invp s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rtc-core-invp fn-rtc-hand-submit-state fn-rtc-issue)
    ((:executable-counterpart fn-rtc-core-invp) (:executable-counterpart fn-rtc-mstates-okp))))))

(defthm fn-a24-fresh-opened-use-u64-tooth
  (let* ((s '((2 0 0 1 0 0 0 0 0)
              ((0 :live nil) (18446744073709551616 :live 7))
              nil nil (nil nil) 0))
         (id 1) (inc 18446744073709551616))
    (and (natp id) (natp inc) (<= 1 id)
         (<= id (fn-rtc-nstatic (fn-rtc-config s)))
         (< id (fn-rtc-nslots (fn-rtc-config s)))
         (fn-rtc-current-p id inc s)
         (not (fn-rtc-use-okp (list :opened id inc (fn-rtc-next-op s) nil)
                (fn-rtc-issue (list :opened id inc (fn-rtc-next-op s) nil) s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rtc-issue))))

; Each positive witness asserts the helper's entire bounded antecedent and result.
(defthm fn-a27-fresh-unbuffered-use-u64-witness
  (let* ((s '((2 0 0 0 0 0 0 0 0) ((0 :live nil) (1 :live 7)) nil nil (nil nil) 0))
         (kind :timer) (id 1) (inc 1))
    (and (member-eq kind '(:fsync :close :accept :timer :extend))
         (natp id) (fn-rtc-u64p inc) (< id (fn-rtc-nslots (fn-rtc-config s)))
         (fn-rtc-current-p id inc s)
         (iff (eq kind :accept) (equal id 0))
         (implies (eq kind :close) (eq (fn-rtc-s-status (fn-rtc-slot id s)) :closing))
         (fn-rtc-use-okp (list kind id inc (fn-rtc-next-op s) nil)
           (fn-rtc-issue (list kind id inc (fn-rtc-next-op s) nil) s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rtc-issue))))
(defthm fn-a27-fresh-wait-use-u64-witness
  (let* ((s '((2 0 0 0 0 0 0 0 0) ((0 :live nil) (1 :live 7)) nil nil (nil nil) 0))
         (id 1) (inc 1))
    (and (natp id) (not (equal id 0)) (fn-rtc-u64p inc)
         (< id (fn-rtc-nslots (fn-rtc-config s))) (fn-rtc-current-p id inc s)
         (fn-rtc-use-okp (list :wait id inc (fn-rtc-next-op s) nil)
           (fn-rtc-issue (list :wait id inc (fn-rtc-next-op s) nil) s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rtc-issue))))
(defthm fn-a27-activate-slot-u64-witness
  (let* ((s '((2 0 0 0 0 0 0 0 0) ((0 :live nil) (0 :free nil)) nil nil (nil nil) 0))
         (id 1) (inc 1) (r 7))
    (and (fn-rtc-core-invp s) (posp id) (fn-rtc-u64p inc) (natp r) (< r (expt 2 64))
         (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free)
         (fn-rtc-core-invp (fn-rtc-with-slot id (list inc :live r) s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rtc-core-invp fn-rtc-with-slot)
     ((:executable-counterpart fn-rtc-core-invp) (:executable-counterpart fn-rtc-mstates-okp))))))
(defthm fn-a27-hand-submit-u64-witness
  (let* ((s '((3 1 1 1 0 1 1 0 0)
              ((0 :live nil) (1 :live 0) (0 :free nil))
              ((0 (:workspace 1 1) nil)) nil (nil nil nil) 0))
         (id 1) (inc 1) (hd '(0 0 0 0)) (extra '(2 1)))
    (and (fn-rtc-core-invp s)
         (fn-rtc-instance-active-p id inc s)
         (fn-rtc-live-p id inc s)
         (fn-rtc-submit-okp :hand hd id inc s)
         (fn-rtc-hand-target-okp extra id s)
         (fn-rtc-kind-extrap :hand extra)
         (fn-rtc-core-invp (fn-rtc-hand-submit-state hd extra id inc s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rtc-core-invp fn-rtc-hand-submit-state fn-rtc-issue)
    ((:executable-counterpart fn-rtc-core-invp) (:executable-counterpart fn-rtc-mstates-okp))))))
(defthm fn-a27-fresh-opened-use-u64-witness
  (let* ((s '((2 0 0 1 0 0 0 0 0) ((0 :live nil) (1 :live 7)) nil nil (nil nil) 0))
         (id 1) (inc 1))
    (and (natp id) (fn-rtc-u64p inc) (<= 1 id)
         (<= id (fn-rtc-nstatic (fn-rtc-config s)))
         (< id (fn-rtc-nslots (fn-rtc-config s))) (fn-rtc-current-p id inc s)
         (fn-rtc-use-okp (list :opened id inc (fn-rtc-next-op s) nil)
           (fn-rtc-issue (list :opened id inc (fn-rtc-next-op s) nil) s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rtc-issue))))
(defthm fn-a27-free-slotp-u64-max-witness
  (and (fn-rtc-u64p 18446744073709551615)
       (fn-rtc-slotp '(18446744073709551615 :free nil)))
  :rule-classes nil)
(defthm fn-a27-set-free-selectable-arm-witness
  (let ((i 0) (k 1) (slots '((0 :live nil) (0 :free nil))) (slot '(1 :free nil)))
    (and (natp i) (natp k) (fn-rtc-free-slot i slots)
         (equal (fn-rtc-s-status slot) :free)
         (or (fn-rtc-slot-selectablep slot)
             (not (fn-rtc-slot-selectablep (fn-rtc-get k slots))))
         (fn-rtc-slot-selectablep slot)
         (fn-rtc-slot-selectablep (fn-rtc-get k slots))
         (fn-rtc-free-slot i (fn-rtc-set k slot slots))))
  :rule-classes nil)
(defthm fn-a27-set-free-old-not-selectable-arm-witness
  (let ((i 0) (k 1)
        (slots '((0 :live nil) (18446744073709551615 :free nil) (0 :free nil)))
        (slot '(18446744073709551615 :free nil)))
    (and (natp i) (natp k) (fn-rtc-free-slot i slots)
         (equal (fn-rtc-s-status slot) :free)
         (or (fn-rtc-slot-selectablep slot)
             (not (fn-rtc-slot-selectablep (fn-rtc-get k slots))))
         (not (fn-rtc-slot-selectablep slot))
         (not (fn-rtc-slot-selectablep (fn-rtc-get k slots)))
         (fn-rtc-free-slot i (fn-rtc-set k slot slots))))
  :rule-classes nil)
