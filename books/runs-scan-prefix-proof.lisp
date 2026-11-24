; A successful scan can continue at the end of a field prefix with the
; remaining byte budget and the field table produced by that prefix.
(in-package "ACL2")
(include-book "runs-page-scan-proof")
(local (include-book "runs-page-window-proof"))

(local
 (defthm fn2-run-scan-prefix-cons
   (implies (consp prefix)
            (and (consp (append prefix x))
                 (equal (car (append prefix x)) (car prefix))
                 (equal (cdr (append prefix x)) (append (cdr prefix) x))
                 (equal (len (cdr prefix)) (1- (len prefix)))))
   :hints (("Goal" :expand ((len prefix) (append prefix x))))))

(defthmd fn2-run-scan-through-field-prefix
  (let* ((first (fn2-layout-scan prefix fuel i pos v hi size ref phase next slot gen end pk ps pg f pool))
         (at (mv-nth 8 first))
         (whole (fn2-layout-scan (append prefix suffix) fuel i pos v hi size ref phase next slot gen end pk ps pg f pool))
         (tail (fn2-layout-scan suffix (- fuel (- at next)) (+ i (len prefix)) 0 0 0 0 0 0
                                at slot gen end pk ps pg (mv-nth 9 first) pool)))
    (implies (and (natp fuel) (natp i) (natp next)
                  (or (consp prefix) (and (equal pos 0) (equal v 0) (equal hi 0)
                                          (equal size 0) (equal ref 0) (equal phase 0)))
                  (equal (car first) :ok) (equal (car tail) :ok))
             (and (equal (car whole) :ok) (equal (mv-nth 8 whole) (mv-nth 8 tail))
                  (equal (mv-nth 9 whole) (mv-nth 9 tail)))))
  :hints (("Goal" :induct (fn2-layout-scan prefix fuel i pos v hi size ref phase next slot gen end pk ps pg f pool)
           :do-not '(preprocess generalize fertilize eliminate-destructors)
           :expand ((fn2-layout-scan prefix fuel i pos v hi size ref phase next slot gen end pk ps pg f pool)
                    (fn2-layout-scan (append prefix suffix) fuel i pos v hi size ref phase next slot gen end pk ps pg f pool)
                    (:free (fld rest)
                     (fn2-layout-scan (cons fld rest) fuel i pos v hi size ref phase next slot gen end pk ps pg f pool)))
           :in-theory (e/d ((:induction fn2-layout-scan))
                       ((:definition fn2-layout-scan) fn2-layout-byte fn2-layout-store fn2-pool-read
                        fn2-fields-rows fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen
                        fn2-fields-ref-off fn2-fields-ref-len fn2-fields-status mod nfix unsigned-byte-p)))))
