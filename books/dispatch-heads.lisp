; THE RUN STUBS' HEADS. FN2-DFR-HEADS-ADVANCE A B: every incarnation of an op
; slot that has begun and been issued in A (FN2-ENV-INCARNATION-OK) still
; has in B: the relation the run stubs are to keep (books/dispatch-fresh.lisp
; derives FRESHNESS and LENT-OK from it). Below the dispatch, which states it.
(in-package "ACL2")
(include-book "assembly-core")

(defun fn2-env-op (s fn2-core)
  ; (VALID GEN PHASE KIND OKIND OSLOT OGEN RSLOT RGEN ROFF RLEN OFFSET FUA C0P C0H C0E C0O C0C MAYREL C1P)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (r)
    (if (and (natp s) (< s (fn2-ops-rows fn2-ops)))
        (list t (fn2-ops-gen s fn2-ops) (fn2-ops-phase s fn2-ops) (fn2-ops-kind s fn2-ops)
              (fn2-ops-owner-kind s fn2-ops) (fn2-ops-owner-slot s fn2-ops) (fn2-ops-owner-gen s fn2-ops)
              (fn2-ops-range-slot s fn2-ops) (fn2-ops-range-gen s fn2-ops)
              (fn2-ops-range-off s fn2-ops) (fn2-ops-range-len s fn2-ops)
              (fn2-ops-storage-offset s fn2-ops) (fn2-ops-fua s fn2-ops)
              (fn2-ops-c0-posted s fn2-ops) (fn2-ops-c0-harvested s fn2-ops) (fn2-ops-c0-event s fn2-ops)
              (fn2-ops-c0-outcome s fn2-ops) (fn2-ops-c0-count s fn2-ops)
              (fn2-ops-may-release s fn2-ops) (fn2-ops-c1-posted s fn2-ops))
      (list nil))
    r))
(defun fn2-env-incarnation-ok (s g fn2-core)
  ; (S G) names an incarnation of op slot S that has begun and been issued
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((op (fn2-env-op s fn2-core)))
    (and (nth 0 op) (natp g) (<= g (nfix (nth 1 op)))
         (implies (equal g (nth 1 op))
                  (not (member-equal (nth 2 op) (list *fn2-op-phase-free* *fn2-op-phase-reserved*)))))))
(in-theory (disable fn2-env-incarnation-ok))

(defun-sk fn2-dfr-heads-advance (a b)
  (forall (s g) (implies (fn2-env-incarnation-ok s g a) (fn2-env-incarnation-ok s g b))))
(in-theory (disable fn2-dfr-heads-advance))
(defthm fn2-dfr-heads-advance-trans
  (implies (and (fn2-dfr-heads-advance a b) (fn2-dfr-heads-advance b c)) (fn2-dfr-heads-advance a c))
  :hints (("Goal" :in-theory '(fn2-dfr-heads-advance)
           :use ((:instance fn2-dfr-heads-advance-necc (s (mv-nth 0 (fn2-dfr-heads-advance-witness a c)))
                            (g (mv-nth 1 (fn2-dfr-heads-advance-witness a c))))
                 (:instance fn2-dfr-heads-advance-necc (a b) (b c) (s (mv-nth 0 (fn2-dfr-heads-advance-witness a c)))
                            (g (mv-nth 1 (fn2-dfr-heads-advance-witness a c))))))))
(defthm fn2-dfr-incarnation-ok-of-advance
  (implies (and (fn2-env-incarnation-ok s g a) (fn2-dfr-heads-advance a b)) (fn2-env-incarnation-ok s g b))
  :hints (("Goal" :in-theory nil :use ((:instance fn2-dfr-heads-advance-necc)))))

