; Source enumeration assigns successive cursor slots to live descriptors,
; visiting the highest installed input index first.
(in-package "ACL2")
(include-book "range-installed-pages-proof")

(defun-nx fn2-range-adapter-source-space-p (g r)
  (and (natp g) (< g (fn2-ranges-rows r))
       (equal (fn2-ranges-sbase g r) 0) (equal (fn2-ranges-cbase g r) 0)
       (equal (fn2-ranges-rbase g r) *fn2-rga-heads*)
       (equal (fn2-ranges-smax g r) *fn2-rga-smax*)))

(defun-nx fn2-range-source-cursor-record (j rs)
  (list (fn2-range-sources-kind j rs) (fn2-range-sources-src j rs) (fn2-range-sources-run j rs)
        (fn2-range-sources-okind j rs) (fn2-range-sources-oslot j rs) (fn2-range-sources-ogen j rs)
        (fn2-range-sources-state j rs) (fn2-range-sources-cursor j rs) (fn2-range-sources-rb j rs)
        (fn2-range-sources-pos j rs) (fn2-range-sources-count j rs)))

(defun fn2-range-fresh-cursor-record (i kind ref run)
  (declare (xargs :guard (natp i)))
  (list kind ref run 9 0 1 *fn2-range-state-seek* i
        (+ *fn2-rga-heads* (* i *fn2-run-reader-fields*)) 0 0))

(defthmd fn2-range-add-assigns-cursor
  (let* ((add (fn2-range-add-source g i kind ref run 9 0 1 r rs))
         (after (mv-nth 1 add)))
    (implies (and (fn2-range-adapter-source-space-p g r)
                  (equal (fn2-range-sources-rows rs) *fn2-rga-smax*)
                  (natp i) (< i *fn2-rga-smax*) (natp j)
                  (or (equal kind *fn2-range-kind-run*) (equal kind *fn2-range-kind-overlay*))
                  (unsigned-byte-p 32 ref) (unsigned-byte-p 60 run))
             (and (equal (car add) :ok)
                  (equal (fn2-range-sources-rows after) *fn2-rga-smax*)
                  (equal (fn2-range-source-cursor-record j after)
                         (if (equal j i) (fn2-range-fresh-cursor-record i kind ref run)
                           (fn2-range-source-cursor-record j rs))))))
  :hints (("Goal" :in-theory (e/d (fn2-range-add-source fn2-range-source-cursor-record
                   fn2-range-adapter-source-space-p fn2-range-fresh-cursor-record fn2-range-sources-rows
                   fn2-range-sources-kind fn2-range-sources-src fn2-range-sources-run
                   fn2-range-sources-okind fn2-range-sources-oslot fn2-range-sources-ogen
                   fn2-range-sources-state fn2-range-sources-pos fn2-range-sources-count
                   fn2-range-sources-cursor fn2-range-sources-rb nth-update-nth)
                 (fn2-ranges-rows fn2-ranges-sbase fn2-ranges-cbase fn2-ranges-rbase fn2-ranges-smax
                  nth update-nth)))))

(defun-nx fn2-range-input-descriptors-p (n sid inputs inst)
  (if (zp n) t
    (let* ((j (1- n)) (rows (nth j inputs)))
      (and (equal (fn2-run-installed-source j inst)
                  (if (consp rows)
                      (list *fn2-run-installed-state-live* sid (1+ j) (len rows) 9 0 1)
                    (list *fn2-run-installed-state-free* 0 0 0 0 0 0)))
           (fn2-range-input-descriptors-p j sid inputs inst)))))

(defun fn2-range-nonempty-run-indices (n inputs)
  (declare (xargs :guard (and (natp n) (true-listp inputs))))
  (if (zp n) nil
    (let* ((j (1- n)) (rest (fn2-range-nonempty-run-indices j inputs)))
      (if (consp (nth j inputs)) (cons j rest) rest))))

(local
 (defthm fn2-range-input-descriptor-at-last-index
   (let* ((j (1- n)) (rows (nth j inputs)) (live (consp rows)))
     (implies (and (posp n) (fn2-range-input-descriptors-p n sid inputs inst))
              (and (equal (fn2-run-installed-state j inst)
                          (if live *fn2-run-installed-state-live* *fn2-run-installed-state-free*))
                   (implies live
                            (and (equal (fn2-run-installed-schema j inst) sid)
                                 (equal (fn2-run-installed-run j inst) n)
                                 (equal (fn2-run-installed-okind j inst) 9)
                                 (equal (fn2-run-installed-oslot j inst) 0)
                                 (equal (fn2-run-installed-ogen j inst) 1))))))
   :hints (("Goal" :expand ((fn2-range-input-descriptors-p n sid inputs inst))
            :in-theory (e/d (fn2-run-installed-source)
                      (fn2-run-installed-state fn2-run-installed-schema fn2-run-installed-run
                       fn2-run-installed-entries fn2-run-installed-okind fn2-run-installed-oslot
                       fn2-run-installed-ogen nth len))))))

(local
 (defun-nx fn2-range-enumerate-inputs-induct (n i g sid inputs r rs)
   (declare (ignorable sid))
   (if (zp n) rs
     (let ((j (1- n)))
       (if (consp (nth j inputs))
           (fn2-range-enumerate-inputs-induct j (1+ i) g sid inputs r
             (mv-nth 1 (fn2-range-add-source g i *fn2-range-kind-run* j n 9 0 1 r rs)))
         (fn2-range-enumerate-inputs-induct j i g sid inputs r rs))))))

(local
 (defthm fn2-range-descriptor-prefix
   (implies (and (posp n) (fn2-range-input-descriptors-p n sid inputs inst))
            (fn2-range-input-descriptors-p (1- n) sid inputs inst))
   :hints (("Goal" :expand ((fn2-range-input-descriptors-p n sid inputs inst))
            :in-theory (disable fn2-run-installed-source nth)))))

(defthmd fn2-range-enumerates-input-runs
  (let* ((refs (fn2-range-nonempty-run-indices n inputs))
         (add (fn2-range-add-runs n i g sid 0 r rs inst)) (after (mv-nth 2 add))
         (ref (nth (- j i) refs)))
    (implies (and (natp n) (<= n 16) (natp i) (natp j)
                  (<= (+ i (len refs)) *fn2-rga-smax*)
                  (fn2-range-input-descriptors-p n sid inputs inst)
                  (fn2-range-adapter-source-space-p g r) (equal (fn2-range-sources-rows rs) *fn2-rga-smax*))
             (and (equal (car add) :ok) (equal (mv-nth 1 add) (+ i (len refs)))
                  (equal (fn2-range-source-cursor-record j after)
                         (if (and (<= i j) (< j (+ i (len refs))))
                             (fn2-range-fresh-cursor-record j *fn2-range-kind-run* ref (1+ ref))
                           (fn2-range-source-cursor-record j rs))))))
  :hints (("Goal" :induct (fn2-range-enumerate-inputs-induct n i g sid inputs r rs)
           :do-not '(preprocess)
           :expand ((fn2-range-add-runs n i g sid 0 r rs inst)
                    (fn2-range-nonempty-run-indices n inputs))
           :in-theory (e/d (fn2-range-add-assigns-cursor)
                     (fn2-range-input-descriptors-p fn2-range-adapter-source-space-p fn2-range-source-cursor-record fn2-range-fresh-cursor-record
                      fn2-range-add-source fn2-range-sources-rows fn2-run-installed-source
                      fn2-run-installed-state fn2-run-installed-schema fn2-run-installed-run
                      fn2-run-installed-okind fn2-run-installed-oslot fn2-run-installed-ogen)))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use (fn2-range-input-descriptor-at-last-index fn2-range-descriptor-prefix
                       (:instance fn2-range-add-assigns-cursor (ref (1- n)) (run n) (kind *fn2-range-kind-run*)))))))
