; THE OP HEADS (each op slot's validity, generation and phase) and the
; relation every issue keeps on them, FN2-ENV-OPS-ADVANCED: each op keeps its
; head or advances it. Over the ops child alone, below the dispatch, whose run
; stubs keep it (books/dispatch-heads.lisp) and whose attachments' chains
; reach these primitives' lemmas; commit-durable-children builds the :take
; and harvest cases on them.
(in-package "ACL2")
(include-book "arm-children")
;; An op's head advanced from O to O2: same validity, and either the same
;; generation with a phase that stays out of free/reserved if it was out, or
;; a newer generation. Every incarnation that began and was issued stays so.
(defun fn2-env-head-advanced (o o2)
  (declare (xargs :verify-guards nil))
  (and (equal (nth 0 o2) (nth 0 o))
       (or (and (equal (nth 1 o2) (nth 1 o))
                (implies (not (member-equal (nth 2 o) (list *fn2-op-phase-free* *fn2-op-phase-reserved*)))
                         (not (member-equal (nth 2 o2) (list *fn2-op-phase-free* *fn2-op-phase-reserved*)))))
           (and (natp (nth 1 o)) (natp (nth 1 o2)) (< (nth 1 o) (nth 1 o2))))))
(defthm fn2-env-head-advanced-refl (fn2-env-head-advanced o o))
(in-theory (disable fn2-env-head-advanced))
;; FN2-ENV-OPS-ADVANCED: every op of the table keeps its head or advances
;; it (FN2-ENV-HEAD-ADVANCED). The op primitives an issue chains (reserve,
;; the reserved op's setters, enqueue, unreserve) keep the rows and
;; generations and move one op out of free or reserved at most (their -HEADS
;; lemmas), so every issue advances the heads.
(defun fn2-env-ops-head (s fn2-ops)
  ; (VALID GEN PHASE) of op slot S
  (declare (xargs :stobjs fn2-ops :verify-guards nil))
  (if (and (natp s) (< s (fn2-ops-rows fn2-ops)))
      (list t (fn2-ops-gen s fn2-ops) (fn2-ops-phase s fn2-ops))
    (list nil)))
(defun-sk fn2-env-ops-advanced (a b)
  (forall s (fn2-env-head-advanced (fn2-env-ops-head s a) (fn2-env-ops-head s b))))
(defthm fn2-env-head-advanced-trans
  (implies (and (fn2-env-head-advanced x y) (fn2-env-head-advanced y z)) (fn2-env-head-advanced x z))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-head-advanced))))
(defthm fn2-env-ops-advanced-refl (fn2-env-ops-advanced a a)
  :hints (("Goal" :in-theory '(fn2-env-ops-advanced fn2-env-head-advanced-refl))))
(defthm fn2-env-ops-advanced-trans
  (implies (and (fn2-env-ops-advanced a b) (fn2-env-ops-advanced b c)) (fn2-env-ops-advanced a c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-ops-advanced)
           :use ((:instance fn2-env-ops-advanced-necc (a a) (b b) (s (fn2-env-ops-advanced-witness a c)))
                 (:instance fn2-env-ops-advanced-necc (a b) (b c) (s (fn2-env-ops-advanced-witness a c)))
                 (:instance fn2-env-head-advanced-trans (x (fn2-env-ops-head (fn2-env-ops-advanced-witness a c) a))
                            (y (fn2-env-ops-head (fn2-env-ops-advanced-witness a c) b))
                            (z (fn2-env-ops-head (fn2-env-ops-advanced-witness a c) c)))))))
(in-theory (disable fn2-env-ops-head))
(defthm fn2-env-ops-advanced-step
  ; B advances A at S when the rows stay, and S keeps its generation and
  ; keeps its phase unless it is X, moved out of free or reserved
  (implies (and (equal (fn2-ops-rows b) (fn2-ops-rows a))
                (implies (and (natp s) (< s (fn2-ops-rows a)))
                         (and (equal (fn2-ops-gen s b) (fn2-ops-gen s a))
                              (or (equal (fn2-ops-phase s b) (fn2-ops-phase s a))
                                  (and (equal s x)
                                       (member-equal (fn2-ops-phase s a) (list *fn2-op-phase-free* *fn2-op-phase-reserved*)))))))
           (fn2-env-head-advanced (fn2-env-ops-head s a) (fn2-env-ops-head s b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-ops-head fn2-env-head-advanced) (fn2-ops-gen fn2-ops-phase fn2-ops-rows)))))
(defthm fn2-env-op-reserve-heads
  ; reservation keeps every generation and the rows, and moves the free
  ; head's phase alone, and only from free
  (let ((b (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may-release o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (equal (fn2-ops-gen s b) (fn2-ops-gen s o)))
         (implies (and (natp s) (not (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))
                  (and (equal s (fn2-ops-free-head o)) (equal (fn2-ops-phase s o) *fn2-op-phase-free*)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-reserve fn2-ops-clear-row fn2-op-slotp)
                           (fn2-op-cleanup-reserve fn2-op-cleanup-kindp fn2-ops-queued fn2-ops-reserved-credits
                            fn2-ops-out-slot-length fn2-ops-free-count unsigned-byte-p fn2-ops-next-free)))))
(defthm fn2-env-op-unreserve-heads
  (let ((b (mv-nth 1 (fn2-op-unreserve slot gen o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (equal (fn2-ops-gen s b) (fn2-ops-gen s o)))
         (implies (and (natp s) (not (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))
                  (and (equal s slot) (equal (fn2-ops-phase s o) *fn2-op-phase-reserved*)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-unreserve fn2-ops-clear-row fn2-op-slotp fn2-op-phase-code fn2-op-handle-code)
                           (fn2-ops-queued fn2-ops-reserved-credits fn2-ops-out-slot-length fn2-ops-free-count
                            unsigned-byte-p fn2-ops-next-free fn2-ops-out-tail fn2-ops-out-gen-length fn2-ring-next)))))
(defthm fn2-env-op-enqueue-heads
  (let ((b (mv-nth 1 (fn2-op-enqueue slot gen o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (equal (fn2-ops-gen s b) (fn2-ops-gen s o)))
         (implies (and (natp s) (not (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))
                  (and (equal s slot) (equal (fn2-ops-phase s o) *fn2-op-phase-reserved*)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-enqueue fn2-ops-clear-row fn2-op-slotp fn2-op-phase-code fn2-op-handle-code)
                           (fn2-ops-queued fn2-ops-reserved-credits fn2-ops-out-slot-length fn2-ops-free-count
                            unsigned-byte-p fn2-ops-next-free fn2-ops-out-tail fn2-ops-out-gen-length fn2-ring-next)))))
(defthm fn2-env-op-set-range-heads
  ; a reserved op's field setter keeps every head
  (let ((b (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (and (equal (fn2-ops-gen s b) (fn2-ops-gen s o)) (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-set-range fn2-op-slotp fn2-op-phase-code fn2-op-handle-code) (unsigned-byte-p)))))
(defthm fn2-env-op-set-capability-heads
  ; a reserved op's field setter keeps every head
  (let ((b (mv-nth 1 (fn2-op-set-capability slot gen index nonce o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (and (equal (fn2-ops-gen s b) (fn2-ops-gen s o)) (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-set-capability fn2-op-slotp fn2-op-phase-code fn2-op-handle-code) (unsigned-byte-p)))))
(defthm fn2-env-op-set-storage-heads
  ; a reserved op's field setter keeps every head
  (let ((b (mv-nth 1 (fn2-op-set-storage slot gen offset fua o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (and (equal (fn2-ops-gen s b) (fn2-ops-gen s o)) (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-set-storage fn2-op-slotp fn2-op-phase-code fn2-op-handle-code) (unsigned-byte-p)))))
(defthm fn2-env-op-set-cancel-target-heads
  ; a reserved op's field setter keeps every head
  (let ((b (mv-nth 1 (fn2-op-set-cancel-target slot gen tslot tgen o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (and (equal (fn2-ops-gen s b) (fn2-ops-gen s o)) (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-set-cancel-target fn2-op-slotp fn2-op-phase-code fn2-op-handle-code) (unsigned-byte-p)))))
(defthm fn2-env-op-reserve-ok-facts
  ; a reservation takes the free head, free at its generation, and leaves it reserved there
  (let ((r (fn2-op-reserve kind okind oslot ogen principal may-release o)))
    (implies (equal (mv-nth 0 r) :ok)
             (and (equal (mv-nth 1 r) (fn2-ops-free-head o)) (natp (mv-nth 1 r)) (< (mv-nth 1 r) (fn2-ops-rows o))
                  (equal (mv-nth 2 r) (fn2-ops-gen (mv-nth 1 r) o))
                  (equal (fn2-ops-phase (mv-nth 1 r) o) *fn2-op-phase-free*)
                  (equal (fn2-ops-gen (mv-nth 1 r) (mv-nth 3 r)) (mv-nth 2 r))
                  (equal (fn2-ops-phase (mv-nth 1 r) (mv-nth 3 r)) *fn2-op-phase-reserved*))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-reserve fn2-ops-clear-row fn2-op-slotp)
                           (fn2-op-cleanup-reserve fn2-op-cleanup-kindp fn2-ops-queued fn2-ops-reserved-credits
                            fn2-ops-out-slot-length fn2-ops-free-count unsigned-byte-p fn2-ops-next-free)))))
(defthm fn2-env-op-enqueue-ok-facts
  ; an accepted enqueue leaves the op queued at its generation
  (implies (and (natp slot) (equal (mv-nth 0 (fn2-op-enqueue slot gen o)) :ok))
           (and (equal (fn2-ops-gen slot (mv-nth 1 (fn2-op-enqueue slot gen o))) (fn2-ops-gen slot o))
                (equal (fn2-ops-phase slot (mv-nth 1 (fn2-op-enqueue slot gen o))) *fn2-op-phase-queued*)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-enqueue fn2-op-slotp fn2-op-phase-code fn2-op-handle-code)
                           (fn2-ops-queued fn2-ops-reserved-credits fn2-ops-out-slot-length unsigned-byte-p
                            fn2-ops-out-tail fn2-ops-out-gen-length fn2-ring-next)))))
(in-theory (disable fn2-env-op-reserve-ok-facts fn2-env-op-enqueue-ok-facts))
(defmacro fn2-env-ops-advanced-by-heads (name call heads x)
  ; NAME: CALL's ops result advances every op head (its HEADS lemma: the
  ; rows and generations stay, and only X moves, out of free or reserved)
  (let ((w `(fn2-env-ops-advanced-witness o ,call)))
    `(defthm ,name
       (implies (fn2-env-ops-advanced a o) (fn2-env-ops-advanced a ,call))
       :hints (("Goal" :in-theory '((:e member-equal) member-equal car-cons cdr-cons)
                :use ((:instance fn2-env-ops-advanced-trans (a a) (b o) (c ,call))
                      (:instance fn2-env-ops-advanced (a o) (b ,call))
                      (:instance ,heads (s ,w))
                      (:instance fn2-env-ops-advanced-step (a o) (b ,call) (s ,w) (x ,x))))))))
(fn2-env-ops-advanced-by-heads fn2-op-reserve-heads-advanced
  (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may-release o)) fn2-env-op-reserve-heads (fn2-ops-free-head o))
(fn2-env-ops-advanced-by-heads fn2-op-unreserve-heads-advanced (mv-nth 1 (fn2-op-unreserve slot gen o)) fn2-env-op-unreserve-heads slot)
(fn2-env-ops-advanced-by-heads fn2-op-enqueue-heads-advanced (mv-nth 1 (fn2-op-enqueue slot gen o)) fn2-env-op-enqueue-heads slot)
(fn2-env-ops-advanced-by-heads fn2-op-set-range-heads-advanced
  (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len o)) fn2-env-op-set-range-heads slot)
(fn2-env-ops-advanced-by-heads fn2-op-set-capability-heads-advanced
  (mv-nth 1 (fn2-op-set-capability slot gen index nonce o)) fn2-env-op-set-capability-heads slot)
(fn2-env-ops-advanced-by-heads fn2-op-set-storage-heads-advanced
  (mv-nth 1 (fn2-op-set-storage slot gen offset fua o)) fn2-env-op-set-storage-heads slot)
(fn2-env-ops-advanced-by-heads fn2-op-set-cancel-target-heads-advanced
  (mv-nth 1 (fn2-op-set-cancel-target slot gen tslot tgen o)) fn2-env-op-set-cancel-target-heads slot)
(defthm fn2-env-issue-children-advanced
  ; an issue advances every op head: it moves one free op through reserved
  ; to queued at its generation, or leaves it reserved or free
  (fn2-env-ops-advanced ops (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release
                                                          target-slot target-gen okind oslot ogen principal pool ops control)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-issue-children)
                           (fn2-env-ops-advanced fn2-op-reserve fn2-op-unreserve fn2-op-enqueue fn2-op-set-range
                            fn2-op-set-capability fn2-op-set-storage fn2-op-set-cancel-target
                            fn2-core-lease fn2-control-record-stop fn2-core-outbox-ready unsigned-byte-p)))))
;; The issue under the walk's name (core-walk.lisp: <fn>-HEADS-ADVANCED, from
;; a start the heads advanced from), so the dispatch's walk stops there.
(defthm fn2-issue-children-heads-advanced
  (implies (fn2-env-ops-advanced a ops)
           (fn2-env-ops-advanced a (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release
                                                                 target-slot target-gen okind oslot ogen principal pool ops control))))
  :hints (("Goal" :in-theory '(fn2-env-issue-children-advanced)
           :use ((:instance fn2-env-ops-advanced-trans
                            (b ops) (c (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release
                                                                     target-slot target-gen okind oslot ogen principal pool ops control))))))))
