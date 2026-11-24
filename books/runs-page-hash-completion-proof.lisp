; After the page header and domain prefix, the format driver completes
; the remaining page hash within one call per span and one final call.
(in-package "ACL2")
(include-book "runs-filled-page-hash-proof")
(include-book "runs-finished-page-seal-proof")

(defmacro fn2-run-check-page-hash ()
  '(fn2-format-run :page t 0 slot gen 0 65536 base pk ps pg 4096 fc ctx b3 f pool ds))

(local
 (defthmd fn2-run-page-checker-returns-hash-span
   (let ((s (fn2-fc-page-span 4096 0 slot gen 0 65536 base pk ps pg fc ctx b3 f pool ds)))
     (implies (and (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*) (equal (car s) :yield))
              (equal (fn2-run-check-page-hash)
                     (list :more (mv-nth 2 s) (mv-nth 3 s) f pool (mv-nth 4 s)))))
   :hints (("Goal" :expand ((fn2-fc-run-bytes 4096 0 :page t slot gen 0 65536 base pk ps pg fc ctx b3 f pool ds))
            :in-theory (union-theories (theory 'minimal-theory)
                  '(fn2-format-run fn2-fc-step fn2-fc-advance eq eql mv-nth car-cons cdr-cons (:e member-equal)
                    (:e posp) (:e zp) (:e binary-+) (:e unary--) (:e equal) (:e <) (:e natp) (:e mv-nth)))))))

(local
 (defthm fn2-run-page-checker-moves-hash-offset
   (let ((after (fn2-fc-set-pos 0 next fc)))
     (and (equal (fn2-fc-phase 0 after) (fn2-fc-phase 0 fc))
          (equal (fn2-fc-pad 0 after) (fn2-fc-pad 0 fc)) (equal (fn2-fc-pad-end 0 after) (fn2-fc-pad-end 0 fc))
          (equal (fn2-fc-pos 0 after) next) (equal (fn2-fc-rows after) (fn2-fc-rows fc))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-phase fn2-fc-pad fn2-fc-pad-end fn2-fc-pos fn2-fc-rows
                                     fn2-fc-set-pos update-fn2-fc-pos$ai nth-update-nth) (nth update-nth))))))

(local
 (defthm fn2-run-input-has-hash-work
   (implies (fn2-run-hash-page-input-p slot gen pk ps pg fc b3 pool)
            (fn2-run-hashing-filled-page-p 0 slot gen pk ps pg fc b3 pool))
   :hints (("Goal" :in-theory (e/d (fn2-run-hashing-filled-page-p fn2-run-hash-page-input-p fn2-ribbon-hash-cursor-p)
                      (fn2-fc-phase fn2-fc-pad fn2-fc-pad-end fn2-fc-pos fn2-b3-blocks fn2-b3-pos
                       fn2-layout-range-code fn2-pool-base fn2-ribbon-zero-region-p))))))

(local
 (defthmd fn2-run-hash-checker-accepts-range
   (let* ((check (fn2-run-check-page-hash))
          (s (fn2-fc-page-span 4096 0 slot gen 0 65536 base pk ps pg fc ctx b3 f pool ds))
          (n (fn2-run-hash-page-span-length)) (pos (fn2-fc-pos 0 fc)))
     (implies (fn2-run-hash-page-input-p slot gen pk ps pg fc b3 pool)
              (and (equal (car check) :more) (equal (mv-nth 3 check) f) (equal (mv-nth 4 check) pool)
                   (equal (mv-nth 1 check) (fn2-fc-set-pos 0 (+ pos n) fc))
                   (equal (mv-nth 2 check) (mv-nth 3 s))
                   (fn2-ribbon-hash-cursor-p (+ 20 pos n) (mv-nth 2 check)))))
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-hash-page-accepts-next-span fn2-run-page-checker-returns-hash-span)
            :in-theory (union-theories (theory 'minimal-theory)
                   '(fn2-run-hash-page-input-p mv-nth car-cons cdr-cons (:e zp) (:e mv-nth) (:e binary-+) (:e equal)))))))

(defthmd fn2-run-valid-hash-step-continues
  (let* ((step (fn2-run-check-page-hash)) (after (mv-nth 1 step)) (new-b3 (mv-nth 2 step))
         (left (fn2-run-page-hash-spans-left (fn2-fc-pos 0 fc) (fn2-fc-pad 0 fc))))
    (implies (fn2-run-hash-page-input-p slot gen pk ps pg fc b3 pool)
             (and (equal (car step) :more) (equal (mv-nth 3 step) f) (equal (mv-nth 4 step) pool)
                  (equal (fn2-fc-phase 0 after) *fn2-fc-phase-hash*)
                  (equal (fn2-fc-rows after) (fn2-fc-rows fc))
                  (equal (fn2-fc-pos 0 after) (+ (fn2-fc-pos 0 fc) (fn2-run-hash-page-span-length)))
                  (<= (fn2-fc-pos 0 after) 65536)
                  (posp left) (<= left 66)
                  (< (fn2-run-page-hash-spans-left (fn2-fc-pos 0 after) (fn2-fc-pad 0 after)) left)
                  (or (equal (fn2-fc-pos 0 after) 65536)
                      (fn2-run-hash-page-input-p slot gen pk ps pg after new-b3 pool)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-hash-checker-accepts-range fn2-run-input-has-hash-work
                 (:instance fn2-run-page-checker-decreases-hash-count (row 0)))
           :in-theory (e/d (fn2-run-hash-page-input-p)
                      (fn2-run-hashing-filled-page-p fn2-ribbon-hash-cursor-p fn2-fc-page-span fn2-b3-update fn2-format-run fn2-fc-span-size fn2-run-page-hash-spans-left
                       fn2-fc-phase fn2-fc-pad fn2-fc-pad-end fn2-fc-pos fn2-fc-rows fn2-fc-set-pos
                       fn2-b3-counter fn2-b3-blocks fn2-b3-pos fn2-b3-depth fn2-b3-flags fn2-b3-verify-phase fn2-b3-origin
                       fn2-pool-base fn2-layout-range-code fn2-ribbon-zero-region-p)))))

(defun-nx fn2-run-hash-page-or-end-p (slot gen pk ps pg fc b3 pool)
  (or (and (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*) (equal (fn2-fc-pos 0 fc) 65536))
      (fn2-run-hash-page-input-p slot gen pk ps pg fc b3 pool)))

(local
 (defthm fn2-run-page-drive-first-result
   (equal (mv-nth 0 x) (car x)) :hints (("Goal" :in-theory (enable mv-nth)))))

(local
 (defthm fn2-run-hash-finish-has-no-negative-cost
   (not (< (fn2-run-page-hash-spans-left 65536 pad) 0))
   :hints (("Goal" :in-theory (enable fn2-run-page-hash-spans-left)))))

(local
 (defthmd fn2-run-hash-ready-page-choice
   (let ((step (fn2-run-check-page-hash)))
     (implies (fn2-run-hash-page-or-end-p slot gen pk ps pg fc b3 pool)
              (and (equal (mv-nth 3 step) f) (equal (mv-nth 4 step) pool)
                   (not (< (fn2-run-page-hash-spans-left (fn2-fc-pos 0 fc) (fn2-fc-pad 0 fc)) 0))
                   (if (equal (fn2-fc-pos 0 fc) 65536) (equal (car step) :ok)
                     (and (equal (car step) :more)
                          (fn2-run-hash-page-or-end-p slot gen pk ps pg (mv-nth 1 step) (mv-nth 2 step) pool)
                          (< (fn2-run-page-hash-spans-left (fn2-fc-pos 0 (mv-nth 1 step)) (fn2-fc-pad 0 (mv-nth 1 step)))
                             (fn2-run-page-hash-spans-left (fn2-fc-pos 0 fc) (fn2-fc-pad 0 fc))))))))
   :hints (("Goal" :do-not '(preprocess) :cases ((equal (fn2-fc-pos 0 fc) 65536))
            :use (fn2-run-valid-hash-step-continues (:instance fn2-run-finished-checker-stores-page-digest (row 0)))
            :in-theory (union-theories (theory 'minimal-theory)
                '(fn2-run-hash-page-or-end-p fn2-run-hash-page-input-p fn2-run-hash-finish-has-no-negative-cost (:e natp) posp mv-nth car-cons cdr-cons
                  (:e mv-nth) (:e zp) (:e equal) (:e binary-+) (:e <)))))))

(defthmd fn2-run-format-driver-finishes-page-hash
  (let ((result (fn2-format-drive fuel 0 :page t slot gen 0 65536 base pk ps pg 4096 fc ctx b3 f pool ds)))
    (implies (and (natp fuel) (fn2-run-hash-page-or-end-p slot gen pk ps pg fc b3 pool)
                  (< (fn2-run-page-hash-spans-left (fn2-fc-pos 0 fc) (fn2-fc-pad 0 fc)) fuel))
             (and (equal (car result) :ok) (equal (mv-nth 3 result) f) (equal (mv-nth 4 result) pool))))
  :hints (("Goal" :induct (fn2-format-drive fuel 0 :page t slot gen 0 65536 base pk ps pg 4096 fc ctx b3 f pool ds)
           :expand ((fn2-format-drive fuel 0 :page t slot gen 0 65536 base pk ps pg 4096 fc ctx b3 f pool ds))
           :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
                    '((:i fn2-format-drive) (:t fn2-run-page-hash-spans-left) (:t fn2-format-run) (:t fn2-format-drive) fn2-run-page-drive-first-result natp posp zp eq eql not mv-nth car-cons cdr-cons
                      (:e mv-nth) (:e zp) (:e equal) (:e binary-+) (:e unary--) (:e <))))
          ("Subgoal *1/1" :use fn2-run-hash-ready-page-choice)
          ("Subgoal *1/2" :use fn2-run-hash-ready-page-choice)
          ("Subgoal *1/3" :use fn2-run-hash-ready-page-choice)))
