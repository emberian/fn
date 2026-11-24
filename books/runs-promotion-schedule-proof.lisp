; A sealed child with an open parent is promoted even while finishing.
; Higher open or idle writers leave this child to the scheduler.
(in-package "ACL2")
(include-book "runs-builder-promoted-row-proof")

(defun-nx fn2-run-higher-writers-available-p (top parent writers)
  (declare (xargs :measure (nfix (1+ top))))
  (if (or (not (natp top)) (not (natp parent)) (< top parent)) t
    (and (member-equal (fn2-run-writers-phase top writers)
                       (list *fn2-run-writer-phase-open* *fn2-run-writer-phase-idle*))
         (fn2-run-higher-writers-available-p (1- top) parent writers))))

(local
 (defthm fn2-run-sealed-child-prevents-finish-close
   (implies (and (natp level) (natp top) (< level top)
                 (equal (fn2-run-writers-phase level writers) *fn2-run-writer-phase-sealed*))
            (not (fn2-run-below-idle top 0 writers)))
   :hints (("Goal" :induct (fn2-run-below-idle top 0 writers)
            :in-theory (e/d (fn2-run-below-idle) (fn2-run-writers-phase))))))

(local
 (defthm fn2-run-available-writer-phase
   (implies (and (natp parent) (natp top) (<= parent top) (fn2-run-higher-writers-available-p top parent writers))
            (member-equal (fn2-run-writers-phase top writers) (list *fn2-run-writer-phase-open* *fn2-run-writer-phase-idle*)))
   :hints (("Goal" :expand ((fn2-run-higher-writers-available-p top parent writers))
            :in-theory (disable fn2-run-writers-phase fn2-run-higher-writers-available-p)))))

(local
 (defthm fn2-run-available-writer-tail
   (implies (and (natp parent) (natp top) (<= parent top) (fn2-run-higher-writers-available-p top parent writers))
            (fn2-run-higher-writers-available-p (1- top) parent writers))
   :hints (("Goal" :expand ((fn2-run-higher-writers-available-p top parent writers))
            :in-theory (disable fn2-run-writers-phase fn2-run-higher-writers-available-p)))))

(local
 (defun fn2-run-walk-higher-writers (top level)
   (declare (xargs :measure (nfix top)))
   (if (or (zp top) (not (natp level)) (<= top level)) level
     (fn2-run-walk-higher-writers (1- top) level))))

(defthmd fn2-run-scan-selects-sealed-child
  (implies (and (natp top) (natp level) (<= level top)
                (< (1+ level) (fn2-run-builds-height 0 builds)) (equal (fn2-run-builds-wbase 0 builds) 0)
                (equal (fn2-run-writers-phase level writers) *fn2-run-writer-phase-sealed*)
                (equal (fn2-run-writers-phase (1+ level) writers) *fn2-run-writer-phase-open*)
                (fn2-run-higher-writers-available-p top (1+ level) writers))
           (equal (fn2-run-scan top 0 finishing builds writers) (list :promote level)))
  :hints (("Goal" :induct (fn2-run-walk-higher-writers top level)
           :expand ((fn2-run-scan top 0 finishing builds writers) (fn2-run-scan level 0 finishing builds writers)
                    (fn2-run-scan 0 0 finishing builds writers))
           :in-theory (disable fn2-run-scan fn2-run-below-idle fn2-run-writers-phase fn2-run-writers-ordinal
                               fn2-run-builds-wbase fn2-run-builds-height fn2-run-higher-writers-available-p))
          ("Subgoal *1/2" :use ((:instance fn2-run-available-writer-phase (parent (1+ level)))
                                 (:instance fn2-run-available-writer-phase (top (1- top)) (parent (1+ level)))
                                 (:instance fn2-run-available-writer-tail (parent (1+ level)))))))

(defthmd fn2-run-work-schedules-parent-promotion
  (let* ((height (fn2-run-builds-height 0 builds)) (crow (fn2-run-builds-crow 0 builds))
         (work (fn2-run-build-work 0 4096 builds writers restarts f pool fc ctx b3 ds)))
    (implies (and (fn2-run-overview-promotion-ready-p level builds writers) (posp height) (<= height *fn2-run-max-levels*)
                  (fn2-run-higher-writers-available-p (1- height) (1+ level) writers)
                  (fn2-run-writerp level writers restarts f) (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx)))
             (equal work (list :promote level builds writers restarts f pool fc ctx b3 ds))))
  :hints (("Goal" :use ((:instance fn2-run-scan-selects-sealed-child (top (1- (fn2-run-builds-height 0 builds)))
                          (finishing (equal (fn2-run-builds-phase 0 builds) *fn2-run-build-phase-finishing*))))
           :in-theory (e/d (fn2-run-build-work fn2-run-overview-promotion-ready-p)
                       (fn2-run-scan fn2-run-below-idle fn2-run-close-step fn2-run-head fn2-run-seal-step fn2-run-close fn2-run-seal-context
                        fn2-run-builds-hbase fn2-run-builds-wbase fn2-run-builds-height fn2-run-builds-phase fn2-run-builds-crow
                        fn2-run-builds-schema fn2-run-builds-fields fn2-run-builds-okind fn2-run-builds-oslot fn2-run-builds-ogen
                        fn2-run-writers-phase fn2-run-writers-rows fn2-run-writerp fn2-fc-rows fn2-fc-context-rows
                        fn2-run-higher-writers-available-p)))))
