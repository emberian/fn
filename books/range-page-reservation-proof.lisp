; Reserving a new run page uses one free slot. Opening its writer keeps
; the remaining slots available, at every level of the overview tree.
(in-package "ACL2")
(include-book "range-workspace-reservations-proof")
(include-book "runs-builder-open-page-proof")

(local
 (defthm fn2-range-opening-writer-keeps-free-slots
   (implies (fn2-range-pool-available-p n p)
            (fn2-range-pool-available-p n
              (mv-nth 2 (fn2-run-open w slot gen sid version level run ordinal kind unit epoch counter history incarnation
                                      pk ps pg base limit writers p))))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-run-open fn2-range-reset-retains-reservations fn2-range-zero-retains-reservations)
                            (fn2-range-pool-available-p fn2-run-zero fn2-pool-reset fn2-run-writers-phase unsigned-byte-p
                             fn2-pool-rows fn2-pool-slot-cap))))))

(defthmd fn2-range-opening-page-keeps-free-slots
  (implies (fn2-range-pool-available-p n p)
           (fn2-range-pool-available-p n (mv-nth 3 (fn2-run-build-page 0 level slot gen unit 2 unit b w p))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-run-build-page fn2-run-build-page-kind fn2-range-opening-writer-keeps-free-slots
                          mv-nth car-cons cdr-cons (:e equal) (:e mv-nth) (:e zp) (:e binary-+))))))

(defun-nx fn2-range-ready-page-level-p (level b w)
  (and (fn2-run-buildsp b) (fn2-run-builds-wfp b) (< 0 (fn2-run-builds-rows b))
       (fn2-run-writersp w) (fn2-run-writers-wfp w) (< level (fn2-run-writers-rows w))
       (natp level) (< level *fn2-run-max-levels*) (< level (fn2-run-builds-height 0 b))
       (equal (fn2-run-builds-wbase 0 b) 0) (equal (fn2-run-writers-phase level w) *fn2-run-writer-phase-idle*)
       (equal (fn2-run-builds-schema 0 b) 3) (equal (fn2-run-builds-fields 0 b) 0)
       (equal (fn2-run-builds-limit 0 b) 2048) (equal (fn2-run-builds-okind 0 b) 9)
       (equal (fn2-run-builds-oslot 0 b) 0) (equal (fn2-run-builds-ogen 0 b) 1)))

(defmacro fn2-range-with-reserved-page (body)
  `(let* ((reserve (fn2-pool-reserve 0 9 0 1 p)) (slot (mv-nth 1 reserve)) (gen (mv-nth 2 reserve))
          (page (fn2-run-build-page 0 level slot gen unit 2 unit b w (mv-nth 3 reserve)))
          (opened (mv-nth 2 page)) (pool (mv-nth 3 page)))
     (declare (ignorable reserve slot gen page opened pool))
     ,body))

(defthmd fn2-range-reserving-opens-overview-page
  (fn2-range-with-reserved-page
   (implies (and (fn2-range-ready-page-level-p level b w) (posp n) (<= n 327)
                 (fn2-range-pool-available-p n p) (unsigned-byte-p 60 unit))
            (and (equal (car reserve) :ok) (equal slot (- 327 n)) (equal gen 1)
                 (equal (car page) :ok) (equal (mv-nth 1 page) b)
                 (fn2-run-empty-open-writer-p level 3 level slot gen 9 0 1 opened)
                 (equal (fn2-run-writers-fields level opened) (* level *fn2-run-writer-fields*))
                 (equal (fn2-run-writers-limit level opened) 2048)
                 (equal (fn2-pool-base slot pool) (* (- 327 n) 65536))
                 (equal (fn2-layout-range-code slot gen *fn2-run-entries-base* *fn2-run-page-size* t 9 0 1 pool) :ok)
                 (fn2-range-pool-available-p (1- n) pool))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-range-reservation-provides-workspace (pk 9) (ps 0) (pg 1))
                 (:instance fn2-range-reserve-preserves-remaining-capacity (pk 9) (ps 0) (pg 1))
                 (:instance fn2-range-opening-page-keeps-free-slots (n (1- n))
                            (slot (- 327 n)) (gen 1) (p (mv-nth 3 (fn2-pool-reserve 0 9 0 1 p))))
                 (:instance fn2-run-build-opens-empty-overview-page
                            (builds b) (writers w) (slot (- 327 n)) (gen 1)
                            (pool (mv-nth 3 (fn2-pool-reserve 0 9 0 1 p)))))
           :in-theory (e/d (fn2-range-ready-page-level-p)
             (fn2-range-pool-available-p fn2-pool-reserve fn2-run-build-page fn2-layout-range-code
              fn2-pool-slot-cap fn2-pool-base fn2-run-empty-open-writer-p fn2-run-open-overview-contents-p
              fn2-run-buildsp fn2-run-builds-wfp fn2-run-builds-rows fn2-run-builds-height fn2-run-builds-wbase
              fn2-run-builds-schema fn2-run-builds-fields fn2-run-builds-limit fn2-run-builds-okind
              fn2-run-builds-oslot fn2-run-builds-ogen fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows
              fn2-run-writers-phase fn2-run-writers-fields fn2-run-writers-limit fn2-run-writers-entries
              fn2-run-writers-restarts fn2-run-writers-cursor)))))
