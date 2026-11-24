; The builder spends exactly the checker calls used on a scheduled page,
; records the physical address once, and continues with the unused fuel.
(in-package "ACL2")
(include-book "runs-builder-seal-workspace-proof")

(defmacro fn2-run-writer-page-drive (fuel w writers fc ctx b3 f pool ds)
  `(fn2-format-drive ,fuel 0 :page t (fn2-run-writers-slot ,w ,writers) (fn2-run-writers-gen ,w ,writers)
     0 65536 (fn2-run-writers-fields ,w ,writers) (fn2-run-writers-okind ,w ,writers)
     (fn2-run-writers-oslot ,w ,writers) (fn2-run-writers-ogen ,w ,writers) 4096 ,fc ,ctx ,b3 ,f ,pool ,ds))

(defun-nx fn2-run-page-check-calls (fuel w writers fc ctx b3 f pool ds)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel) 0
    (let ((step (fn2-run-writer-page-check w writers fc ctx b3 f pool ds)))
      (if (eq (car step) :more)
          (1+ (fn2-run-page-check-calls (1- fuel) w writers (mv-nth 1 step) ctx (mv-nth 2 step)
                                        (mv-nth 3 step) pool (mv-nth 5 step)))
        1))))

(defthmd fn2-run-page-check-calls-fit-fuel
  (let ((calls (fn2-run-page-check-calls fuel w writers fc ctx b3 f pool ds)))
    (and (<= calls (nfix fuel)) (implies (posp fuel) (posp calls))))
  :hints (("Goal" :induct (fn2-run-page-check-calls fuel w writers fc ctx b3 f pool ds)
           :in-theory (e/d (fn2-run-page-check-calls nfix) (fn2-format-run)))))

(defmacro fn2-run-sealing-loop (fuel pages builds writers f fc b3 ds)
  `(fn2-run-run-loop ,fuel layout entries src sg off unit ,pages ,builds curs paths cache
                     ,writers restarts ,f pool ,fc ctx ,b3 ,ds))

(defmacro fn2-run-sealed-address (w writers)
  `(list l (fn2-run-writers-unit ,w ,writers) (fn2-run-writers-counter ,w ,writers)
           (fn2-run-writers-slot ,w ,writers) (fn2-run-writers-gen ,w ,writers)))

(defmacro fn2-run-sealed-builds (builds)
  `(let ((count (1+ (fn2-run-builds-pages 0 ,builds))))
     (if (unsigned-byte-p 60 count) (fn2-run-builds-set-pages 0 count ,builds) ,builds)))

(local
 (defmacro fn2-run-seal-driver-theory (&rest more)
   `(union-theories (theory 'minimal-theory)
       '(posp natp zp not eq eql member-equal mv-nth car-cons cdr-cons (:e mv-nth) (:e equal)
         (:e car) (:e cdr) (:e consp) (:e zp) (:e binary-+) (:e unary--) (:e member-equal) ,@more))))

(defthmd fn2-run-scheduled-loop-takes-page-check
  (let ((step (fn2-run-writer-page-check w writers fc ctx b3 f pool ds)))
    (implies (and (posp fuel) (equal w (+ l (fn2-run-builds-wbase 0 builds)))
                  (equal hrow (+ l (fn2-run-builds-hbase 0 builds))) (equal (fn2-run-builds-crow 0 builds) 0)
                  (fn2-run-build-sealing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-seal-workspace-p w hrow writers fc ctx b3 f pool ds)
                  (member-eq (car step) '(:ok :more)))
             (equal (fn2-run-sealing-loop fuel pages builds writers f fc b3 ds)
                    (let ((done (eq (car step) :ok)))
                      (fn2-run-sealing-loop (1- fuel) (if done (cons (fn2-run-sealed-address w writers) pages) pages)
                         (if done (fn2-run-sealed-builds builds) builds)
                         (if done (fn2-run-writers-set-phase w *fn2-run-writer-phase-sealed* writers) writers)
                         (mv-nth 3 step) (mv-nth 1 step) (mv-nth 2 step) (mv-nth 5 step))))))
  :hints (("Goal" :do-not '(preprocess)
           :expand ((fn2-run-sealing-loop fuel pages builds writers f fc b3 ds))
           :use (fn2-run-writer-follows-format-check fn2-run-adapter-seal-state)
           :in-theory (fn2-run-seal-driver-theory))))

(local
 (defthmd fn2-run-writer-drive-takes-page-check
   (let* ((step (fn2-run-writer-page-check w writers fc ctx b3 f pool ds))
          (drive (fn2-run-writer-page-drive fuel w writers fc ctx b3 f pool ds)))
     (implies (and (posp fuel) (equal (mv-nth 4 step) pool))
              (equal drive (if (eq (car step) :more)
                               (fn2-run-writer-page-drive (1- fuel) w writers (mv-nth 1 step) ctx (mv-nth 2 step)
                                                        (mv-nth 3 step) pool (mv-nth 5 step))
                             (list (car step) (mv-nth 1 step) (mv-nth 2 step) (mv-nth 3 step) pool (mv-nth 5 step))))))
   :hints (("Goal" :expand ((fn2-run-writer-page-drive fuel w writers fc ctx b3 f pool ds))
            :in-theory (fn2-run-seal-driver-theory (:t fn2-format-run))))))

(local
 (defthm fn2-run-check-call-fuel-arithmetic
   (implies (and (natp calls) (natp extra))
            (and (posp (+ (+ 1 calls) extra))
                 (equal (+ -1 (+ (+ 1 calls) extra)) (+ calls extra))
                 (posp (+ 1 extra)) (equal (+ -1 (+ 1 extra)) extra)))
   :rule-classes nil))

(defthmd fn2-run-builder-continues-after-page-check
  (let* ((drive (fn2-run-writer-page-drive fuel w writers fc ctx b3 f pool ds))
         (calls (fn2-run-page-check-calls fuel w writers fc ctx b3 f pool ds)))
    (implies (and (natp extra) (equal w (+ l (fn2-run-builds-wbase 0 builds)))
                  (equal hrow (+ l (fn2-run-builds-hbase 0 builds))) (equal (fn2-run-builds-crow 0 builds) 0)
                  (fn2-run-build-sealing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-seal-workspace-p w hrow writers fc ctx b3 f pool ds) (equal (car drive) :ok))
             (equal (fn2-run-sealing-loop (+ calls extra) pages builds writers f fc b3 ds)
                    (fn2-run-sealing-loop extra (cons (fn2-run-sealed-address w writers) pages) (fn2-run-sealed-builds builds)
                        (fn2-run-writers-set-phase w *fn2-run-writer-phase-sealed* writers)
                        (mv-nth 3 drive) (mv-nth 1 drive) (mv-nth 2 drive) (mv-nth 5 drive)))))
  :hints (("Goal" :induct (fn2-run-page-check-calls fuel w writers fc ctx b3 f pool ds)
           :do-not '(preprocess) :in-theory (fn2-run-seal-driver-theory (:induction fn2-run-page-check-calls)))
          ("Subgoal *1/1" :expand ((fn2-run-writer-page-drive fuel w writers fc ctx b3 f pool ds)))
          ("Subgoal *1/3" :use (fn2-run-writer-drive-takes-page-check fn2-run-writer-follows-format-check
                       (:instance fn2-run-check-call-fuel-arithmetic (calls 0))
                       (:instance fn2-run-scheduled-loop-takes-page-check (fuel (+ 1 extra))))
           :expand ((fn2-run-page-check-calls fuel w writers fc ctx b3 f pool ds)))
          ("Subgoal *1/2" :use (fn2-run-writer-drive-takes-page-check fn2-run-writer-follows-format-check
                       fn2-run-page-check-keeps-seal-workspace fn2-run-page-check-keeps-seal-scheduled
                       (:instance fn2-run-check-call-fuel-arithmetic
                         (calls (let ((step (fn2-run-writer-page-check w writers fc ctx b3 f pool ds)))
                                  (fn2-run-page-check-calls (1- fuel) w writers (mv-nth 1 step) ctx (mv-nth 2 step)
                                                           (mv-nth 3 step) pool (mv-nth 5 step)))))
                       (:instance fn2-run-scheduled-loop-takes-page-check
                         (fuel (+ (fn2-run-page-check-calls fuel w writers fc ctx b3 f pool ds) extra))))
           :expand ((fn2-run-page-check-calls fuel w writers fc ctx b3 f pool ds))
           :in-theory (fn2-run-seal-driver-theory (:t fn2-run-page-check-calls)))))
