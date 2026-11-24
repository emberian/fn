; A full-budget writer call on a filled page either leaves hashing with a
; status or advances the live checker cursor by the entire aligned span.
(in-package "ACL2")
(include-book "runs-page-hash-span-proof")
(include-book "runs-page-seal")
(include-book "runs-header-overwrite-proof")

(defmacro fn2-run-hash-used (row b3)
  `(+ (* 64 (fn2-b3-blocks ,row ,b3)) (fn2-b3-pos ,row ,b3)))

(defun-nx fn2-run-hashing-filled-page-p (row slot gen pk ps pg fc b3 pool)
  (let ((pos (fn2-fc-pos row fc)) (pad (fn2-fc-pad row fc)))
    (and (natp row) (natp pos) (< pos *fn2-run-page-size*) (natp pad) (<= pad 2048)
         (equal (fn2-fc-phase row fc) *fn2-fc-phase-hash*) (equal (fn2-fc-pad-end row fc) *fn2-run-page-size*)
         (natp (fn2-run-hash-used row b3)) (fn2-run-filled-page-p slot gen pk ps pg pool))))

(local
 (defthm fn2-run-filled-page-physical-bounds
   (implies (fn2-run-filled-page-p slot gen pk ps pg pool)
            (and (natp slot) (< slot (fn2-pool-rows pool)) (natp (fn2-pool-slot-base slot pool))
                 (<= (+ (fn2-pool-slot-base slot pool) 65536) (fn2-pool-data-length pool))))
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-pool-workspace-code fn2-pool-handle-code
                                fn2-pool-capacity-bytes fn2-pool-slot-base)
                      (fn2-pool-slot-fill fn2-pool-slot-cap fn2-pool-data-length fn2-pool-base fn2-pool-rows
                       fn2-pool-gen fn2-pool-state fn2-pool-ownerp fn2-pool-query-ref-count))))))

(local
 (defthm fn2-run-hashing-page-selects-span
   (let ((code (car (fn2-run-full-page-span))))
     (implies (fn2-run-hashing-filled-page-p row slot gen pk ps pg fc b3 pool)
              (and (not (equal code :byte)) (not (equal code :more)) (not (equal code :ok)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-readable-hash-span-returns-a-result fn2-run-filled-page-physical-bounds
                  (:instance fn2-run-page-hash-span-size (pos (fn2-fc-pos row fc)) (pad (fn2-fc-pad row fc))
                             (used (fn2-run-hash-used row b3)))
                  (:instance fn2-run-filled-page-allows-subrange (start (fn2-fc-pos row fc)) (writep nil)
                             (end (+ (fn2-fc-pos row fc) (fn2-fc-span-size 4096 (fn2-fc-pos row fc)
                                                       (fn2-fc-pad row fc) 65536 (fn2-run-hash-used row b3))))))
            :in-theory (e/d (fn2-run-hashing-filled-page-p)
                        (fn2-fc-page-span fn2-fc-span-size fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-phase fn2-b3-pos
                         fn2-b3-blocks fn2-pool-base fn2-pool-rows fn2-pool-data-length fn2-pool-slot-base fn2-layout-range-code))))))

(local
 (defthm fn2-run-page-checker-carries-hash-span
   (let* ((span (fn2-run-full-page-span)) (code (car span))
          (run (fn2-format-run :page t row slot gen 0 65536 base pk ps pg 4096 fc ctx b3 f pool ds)))
     (implies (and (equal (fn2-fc-phase row fc) *fn2-fc-phase-hash*)
                   (not (equal code :byte)) (not (equal code :more)) (not (equal code :ok)))
              (and (equal (car run) (if (equal code :yield) :more code))
                   (implies (equal code :yield) (equal (mv-nth 1 run) (mv-nth 2 span))))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess) :cases ((equal (car (fn2-run-full-page-span)) :yield))
            :expand ((fn2-fc-run-bytes 4096 row :page t slot gen 0 65536 base pk ps pg fc ctx b3 f pool ds))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-format-run fn2-fc-step fn2-fc-advance eq eql mv-nth car-cons cdr-cons
                           (:e member-equal) (:e binary-+) (:e equal) (:e <) (:e posp) (:e zp) (:e mv-nth)))))))

(local
 (defthm fn2-run-hash-pos-update
   (let ((after (fn2-fc-set-pos row next fc)))
     (implies (natp row) (and (equal (fn2-fc-pos row after) next) (equal (fn2-fc-pad row after) (fn2-fc-pad row fc))
                              (equal (fn2-fc-phase row after) (fn2-fc-phase row fc)))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-pos fn2-fc-pad fn2-fc-phase fn2-fc-set-pos update-fn2-fc-pos$ai nth-update-nth)
                                  (nth update-nth))))))

(defthmd fn2-run-page-checker-decreases-hash-count
  (let* ((pos (fn2-fc-pos row fc)) (pad (fn2-fc-pad row fc)) (left (fn2-run-page-hash-spans-left pos pad))
         (run (fn2-format-run :page t row slot gen 0 65536 base pk ps pg 4096 fc ctx b3 f pool ds))
         (code (car run)) (after (mv-nth 1 run)))
    (implies (fn2-run-hashing-filled-page-p row slot gen pk ps pg fc b3 pool)
             (and (posp left) (<= left 66) (not (equal code :ok))
                  (implies (equal code :more)
                    (and (equal (fn2-fc-phase row after) *fn2-fc-phase-hash*)
                         (equal (fn2-fc-pad row after) pad)
                         (< pos (fn2-fc-pos row after)) (<= (fn2-fc-pos row after) 65536)
                         (< (fn2-run-page-hash-spans-left (fn2-fc-pos row after) pad) left))))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-hashing-page-selects-span fn2-run-page-checker-carries-hash-span
                 fn2-run-page-hash-yield-advances-to-span-end
                 (:instance fn2-run-full-budget-hash-span-decreases-count (pos (fn2-fc-pos row fc)) (pad (fn2-fc-pad row fc))
                            (used (fn2-run-hash-used row b3)))
                 (:instance fn2-run-page-hash-span-size (pos (fn2-fc-pos row fc)) (pad (fn2-fc-pad row fc))
                            (used (fn2-run-hash-used row b3))))
           :cases ((equal (car (fn2-run-full-page-span)) :yield))
           :in-theory (e/d (fn2-run-hashing-filled-page-p)
                       (fn2-fc-page-span fn2-format-run fn2-run-page-hash-spans-left fn2-fc-span-size fn2-fc-pos fn2-fc-pad
                        fn2-fc-phase fn2-fc-pad-end fn2-fc-set-pos fn2-b3-pos fn2-b3-blocks fn2-layout-range-code fn2-pool-base)))))

(defthmd fn2-run-sealing-writer-decreases-hash-count
  (let* ((seal (fn2-run-seal-step w row hrow 4096 writers fc ctx b3 f pool ds))
         (pad (fn2-fc-pad row fc)) (left (fn2-run-page-hash-spans-left (fn2-fc-pos row fc) pad))
         (after (mv-nth 2 seal)))
    (implies (fn2-run-hashing-filled-page-p row (fn2-run-writers-slot w writers) (fn2-run-writers-gen w writers)
                       (fn2-run-writers-okind w writers) (fn2-run-writers-oslot w writers) (fn2-run-writers-ogen w writers) fc b3 pool)
             (and (posp left) (<= left 66) (not (equal (car seal) :ok))
                  (implies (equal (car seal) :more)
                     (and (equal (fn2-fc-phase row after) *fn2-fc-phase-hash*) (equal (fn2-fc-pad row after) pad)
                          (< (fn2-fc-pos row fc) (fn2-fc-pos row after)) (<= (fn2-fc-pos row after) 65536)
                          (< (fn2-run-page-hash-spans-left (fn2-fc-pos row after) pad) left))))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-page-checker-decreases-hash-count (slot (fn2-run-writers-slot w writers))
                          (gen (fn2-run-writers-gen w writers)) (base (fn2-run-writers-fields w writers))
                          (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers))
                          (pg (fn2-run-writers-ogen w writers))))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-run-seal-step eq eql mv-nth car-cons cdr-cons (:e mv-nth) (:e <) (:e zp) (:e binary-+) (:e equal))))))
