; Proof-side count of issued operation incarnations. Acknowledge does not
; erase an issue: submitted/done remain issued, and recycling trades the
; issued bit for the next generation. No served function scans this measure.
(in-package "ACL2")
(include-book "ops-heads")

(defun fn2-op-issued-weight (gen phase)
  (declare (xargs :guard t))
  (+ (nfix gen)
     (if (member-equal phase (list *fn2-op-phase-free* *fn2-op-phase-reserved*)) 0 1)))

(defun fn2-ops-issued-count (n fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix n)))
  (if (zp n) 0
    (+ (fn2-op-issued-weight (fn2-ops-gen (- n 1) fn2-ops)
                            (fn2-ops-phase (- n 1) fn2-ops))
       (fn2-ops-issued-count (- n 1) fn2-ops))))

(defthm fn2-ops-issued-count-natural
  (natp (fn2-ops-issued-count n fn2-ops))
  :rule-classes :type-prescription)

(defthm fn2-op-enqueue-issued-weight
  (implies (natp i)
    (equal
      (fn2-op-issued-weight
        (fn2-ops-gen i (mv-nth 1 (fn2-op-enqueue slot gen fn2-ops)))
        (fn2-ops-phase i (mv-nth 1 (fn2-op-enqueue slot gen fn2-ops))))
      (+ (fn2-op-issued-weight (fn2-ops-gen i fn2-ops) (fn2-ops-phase i fn2-ops))
         (if (and (equal i slot) (eq (car (fn2-op-enqueue slot gen fn2-ops)) :ok)) 1 0))))
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn2-env-op-enqueue-heads (o fn2-ops) (s i))
          (:instance fn2-env-op-enqueue-ok-facts (o fn2-ops)))
    :in-theory (e/d (fn2-op-enqueue fn2-op-issued-weight fn2-op-phase-code fn2-op-handle-code fn2-op-slotp)
                    (fn2-ops-gen fn2-ops-phase fn2-ops-out-slot-length fn2-ops-out-gen-length
                     fn2-ops-out-tail fn2-ops-queued fn2-ops-reserved-credits fn2-ring-next unsigned-byte-p)))))

(defthm fn2-op-enqueue-issued-count
  (equal (fn2-ops-issued-count n (mv-nth 1 (fn2-op-enqueue slot gen fn2-ops)))
         (+ (fn2-ops-issued-count n fn2-ops)
            (if (and (natp slot) (< slot (nfix n))
                     (eq (car (fn2-op-enqueue slot gen fn2-ops)) :ok)) 1 0)))
  :hints (("Goal" :induct (fn2-ops-issued-count n fn2-ops)
    :in-theory (e/d (fn2-ops-issued-count) (fn2-op-enqueue fn2-op-issued-weight fn2-ops-gen fn2-ops-phase)))))

(defthm fn2-op-reserve-issued-weight
 (implies (natp i)
  (equal
   (fn2-op-issued-weight
    (fn2-ops-gen i (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may-release fn2-ops)))
    (fn2-ops-phase i (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may-release fn2-ops))))
   (fn2-op-issued-weight (fn2-ops-gen i fn2-ops) (fn2-ops-phase i fn2-ops))))
 :hints (("Goal" :do-not-induct t
   :use ((:instance fn2-env-op-reserve-heads (o fn2-ops) (s i))
         (:instance fn2-env-op-reserve-ok-facts (o fn2-ops)))
   :in-theory (e/d (fn2-op-reserve fn2-ops-clear-row fn2-op-issued-weight fn2-op-slotp)
     (fn2-op-cleanup-reserve fn2-op-cleanup-kindp fn2-ops-gen fn2-ops-phase
      fn2-ops-queued fn2-ops-reserved-credits fn2-ops-out-slot-length fn2-ops-free-count
      unsigned-byte-p fn2-ops-next-free)))))
(defthm fn2-op-reserve-issued-count
 (equal (fn2-ops-issued-count n (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may-release fn2-ops)))
        (fn2-ops-issued-count n fn2-ops))
 :hints (("Goal" :induct (fn2-ops-issued-count n fn2-ops)
   :in-theory (e/d (fn2-ops-issued-count) (fn2-op-reserve fn2-op-issued-weight fn2-ops-gen fn2-ops-phase)))))

(defthm fn2-op-unreserve-issued-weight
 (implies (and (natp i) (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
  (equal
   (fn2-op-issued-weight (fn2-ops-gen i (mv-nth 1 (fn2-op-unreserve slot gen fn2-ops)))
                         (fn2-ops-phase i (mv-nth 1 (fn2-op-unreserve slot gen fn2-ops))))
   (fn2-op-issued-weight (fn2-ops-gen i fn2-ops) (fn2-ops-phase i fn2-ops))))
 :hints (("Goal" :do-not-induct t
   :use (:instance fn2-env-op-unreserve-heads (o fn2-ops) (s i))
   :in-theory (e/d (fn2-op-unreserve fn2-ops-clear-row fn2-op-issued-weight fn2-ops-phase fn2-op-slotp
                    fn2-op-phase-code fn2-op-handle-code)
     (fn2-opsp fn2-ops-wfp fn2-ops-rows fn2-ops-gen fn2-ops-queued fn2-ops-reserved-credits
      fn2-ops-out-slot-length fn2-ops-free-count unsigned-byte-p fn2-ops-next-free)))))
(defthm fn2-op-unreserve-issued-count
 (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
 (equal (fn2-ops-issued-count n (mv-nth 1 (fn2-op-unreserve slot gen fn2-ops)))
        (fn2-ops-issued-count n fn2-ops)))
 :hints (("Goal" :induct (fn2-ops-issued-count n fn2-ops)
   :in-theory (e/d (fn2-ops-issued-count) (fn2-op-unreserve fn2-op-issued-weight fn2-ops-gen fn2-ops-phase)))))

(defun fn2-issued-setter-count-events (names world)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (let* ((fn (car names)) (args (getpropc fn 'formals nil world))
         (call (cons fn args)))
   (cons `(defthm ,(fn2-columns-sym fn "-ISSUED-COUNT")
     (equal (fn2-ops-issued-count n (mv-nth 1 ,call)) (fn2-ops-issued-count n fn2-ops))
     :hints (("Goal" :induct (fn2-ops-issued-count n fn2-ops)
       :in-theory (e/d (fn2-ops-issued-count) (,fn fn2-op-issued-weight fn2-ops-gen fn2-ops-phase)))))
    (fn2-issued-setter-count-events (cdr names) world)))))
(make-event (value (cons 'progn (fn2-issued-setter-count-events
 '(fn2-op-set-range fn2-op-set-capability fn2-op-set-storage fn2-op-set-cancel-target) (w state)))))

(defthm fn2-op-enqueue-ok-slot-bounds
 (implies (eq (car (fn2-op-enqueue slot gen fn2-ops)) :ok)
          (and (natp slot) (< slot (fn2-ops-rows fn2-ops))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-op-enqueue fn2-op-phase-code fn2-op-handle-code fn2-op-slotp)
   (fn2-ops-rows fn2-ops-phase fn2-ops-gen fn2-ops-out-tail fn2-ops-queued fn2-ops-reserved-credits
    fn2-ops-out-slot-length fn2-ops-out-gen-length fn2-ring-next)))))
(defthm fn2-op-enqueue-issued-total
 (implies (fn2-opsp fn2-ops)
  (equal
   (fn2-ops-issued-count (fn2-ops-rows (mv-nth 1 (fn2-op-enqueue slot gen fn2-ops)))
                         (mv-nth 1 (fn2-op-enqueue slot gen fn2-ops)))
   (+ (fn2-ops-issued-count (fn2-ops-rows fn2-ops) fn2-ops)
      (if (eq (car (fn2-op-enqueue slot gen fn2-ops)) :ok) 1 0))))
 :hints (("Goal" :use (fn2-op-enqueue-ok-slot-bounds
                       (:instance fn2-env-op-enqueue-heads (o fn2-ops) (s 0)))
  :in-theory (disable fn2-op-enqueue fn2-ops-issued-count fn2-op-issued-weight fn2-opsp fn2-ops-rows))))

(defun fn2-issued-total-frame-events (entries world)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (let* ((fn (caar entries)) (pos (cadar entries)) (heads (caddar entries))
         (call (cons fn (getpropc fn 'formals nil world))) (out `(mv-nth ,pos ,call)))
   (cons `(defthm ,(fn2-columns-sym fn "-ISSUED-TOTAL")
     (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
      (equal (fn2-ops-issued-count (fn2-ops-rows ,out) ,out)
             (fn2-ops-issued-count (fn2-ops-rows fn2-ops) fn2-ops)))
     :hints (("Goal" :use (:instance ,heads (o fn2-ops) (s 0))
       :in-theory (disable ,fn fn2-ops-issued-count fn2-op-issued-weight fn2-opsp fn2-ops-wfp fn2-ops-rows))))
    (fn2-issued-total-frame-events (cdr entries) world)))))
(make-event (value (cons 'progn (fn2-issued-total-frame-events
 '((fn2-op-reserve 3 fn2-env-op-reserve-heads)
   (fn2-op-unreserve 1 fn2-env-op-unreserve-heads)
   (fn2-op-set-range 1 fn2-env-op-set-range-heads)
   (fn2-op-set-capability 1 fn2-env-op-set-capability-heads)
   (fn2-op-set-storage 1 fn2-env-op-set-storage-heads)
   (fn2-op-set-cancel-target 1 fn2-env-op-set-cancel-target-heads)) (w state)))))

(in-theory (disable fn2-ops-issued-count fn2-op-issued-weight))
