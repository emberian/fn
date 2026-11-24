; The value written to the selected field equals the scalar in the admitted row.
(in-package "ACL2")
(include-book "runs-page-id-step-proof")
(include-book "runs-page-scan-proof")

(local
 (defthm fn2-run-scan-field-of-store
 (implies (and (natp i) (natp target))
  (equal (fn2-fields-value target (fn2-layout-store i v slot gen off size status f))
         (if (and (equal i target) (< i (fn2-fields-rows f))
                  (unsigned-byte-p 60 v) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                  (unsigned-byte-p 32 off) (unsigned-byte-p 32 size) (unsigned-byte-p 8 status))
             v (fn2-fields-value target f))))
 :hints (("Goal" :in-theory (e/d (fn2-layout-store fn2-fields-value fn2-fields-set-value
                        update-fn2-fields-value$ai nth-update-nth) (fn2-fields-rows unsigned-byte-p nth update-nth))))))

(defthm fn2-run-scan-keeps-earlier-id
 (implies (and (natp target) (natp i) (< target i))
  (equal (fn2-fields-value target (mv-nth 9 (fn2-layout-scan layout fuel i pos v hi size ref phase next slot gen end pk ps pg f pool)))
         (fn2-fields-value target f)))
 :hints (("Goal" :induct (fn2-layout-scan layout fuel i pos v hi size ref phase next slot gen end pk ps pg f pool)
          :expand ((fn2-layout-scan layout fuel i pos v hi size ref phase next slot gen end pk ps pg f pool))
          :in-theory (e/d ((:induction fn2-layout-scan))
                          (fn2-layout-store fn2-layout-byte fn2-pool-read fn2-fields-rows fn2-fields-value
                           fn2-fields-ref-slot fn2-fields-ref-off fn2-fields-ref-len fn2-fields-status fn2-fields-ref-gen
                           mod nfix unsigned-byte-p)))))

(local
 (defthm fn2-run-scan-returns-admitted-scalar
 (let* ((xs (fn2-run-page-window next bound slot gen pk ps pg pool))
        (j (- target i)) (picked (fn2-run-parser-scalar layout j xs pos v hi size phase))
        (parse (fn2-run-parser-span layout xs pos v hi size phase))
        (scan (fn2-layout-scan layout fuel i pos v hi size ref phase next slot gen end pk ps pg f pool)))
   (implies (and (natp next) (natp bound) (<= next bound) (<= bound end)
                 (natp fuel) (<= (- bound next) fuel)
                 (natp i) (<= (+ i (len layout)) (fn2-fields-rows f))
                 (natp pos) (natp v) (natp hi) (natp size) (natp phase)
                 (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                 (eq (fn2-layout-range-code slot gen next bound nil pk ps pg pool) :ok)
                 (eq (car parse) :ok) (eq (car scan) :ok)
                 (equal phase 0) (natp target) (<= i target)
                 (fn2-run-scalar-prefixp j layout) (unsigned-byte-p 60 wanted) (equal picked wanted)
                 (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 32 ref))
            (equal (fn2-fields-value target (mv-nth 9 scan)) wanted)))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-layout-scan layout fuel i pos v hi size ref phase next slot gen end pk ps pg f pool)
          :do-not '(preprocess generalize fertilize eliminate-destructors)
          :expand ((fn2-layout-scan layout fuel i pos v hi size ref phase next slot gen end pk ps pg f pool))
          :in-theory (e/d ((:induction fn2-layout-scan) fn2-run-layout-byte-naturals fn2-run-reader-octet
                           fn2-run-reader-nfix)
                          ((:definition fn2-layout-scan) fn2-run-scalar-kindp fn2-run-scalar-prefixp fn2-run-parser-scalar fn2-run-parser-scalar-at-start
                           fn2-run-parser-span fn2-run-parser-span-at-start fn2-run-page-window fn2-layout-store
                           fn2-layout-byte fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-range-code
                           fn2-pool-read fn2-fields-rows fn2-fields-value fn2-fields-ref-off
                           fn2-fields-ref-len fn2-fields-ref-gen fn2-fields-ref-slot fn2-fields-status
                           mod nfix unsigned-byte-p member-equal)))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use ((:instance fn2-run-scalar-window-step (j (- target i)))))))))

(defthm fn2-run-page-scan-returns-source-scalar
 (let* ((bytes (fn2-layout-octets layout row))
        (bound (+ off (len bytes)))
        (scan (fn2-layout-scan layout fuel base 0 0 0 0 0 0 off slot gen end pk ps pg f pool)))
   (implies (and (fn2-run-values-layoutp layout row)
                 (natp j) (fn2-run-scalar-prefixp j layout) (unsigned-byte-p 60 (nth j row))
                 (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (natp base) (<= (+ base (len layout)) (fn2-fields-rows f))
                 (natp off) (<= bound end) (natp fuel) (<= (len bytes) fuel)
                 (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                 (eq (fn2-layout-range-code slot gen off bound nil pk ps pg pool) :ok)
                 (equal (fn2-run-read-bytes (len bytes) slot gen off pk ps pg pool) bytes))
            (equal (fn2-fields-value (+ base j) (mv-nth 9 scan)) (nth j row))))
 :rule-classes nil
 :hints (("Goal" :use (fn2-run-page-scan-consumes-admitted-row
                (:instance fn2-run-parser-scalar-at-start (xs (fn2-layout-octets layout row)))
                (:instance fn2-run-scan-returns-admitted-scalar (target (+ base j)) (wanted (nth j row))
             (next off) (bound (+ off (len (fn2-layout-octets layout row))))
             (i base) (pos 0) (v 0) (hi 0) (size 0) (ref 0) (phase 0)))
          :in-theory (e/d (fn2-run-values-layoutp fn2-run-page-window)
                          (fn2-run-scalar-kindp fn2-run-scalar-prefixp fn2-run-parser-scalar fn2-fields-value unsigned-byte-p nth fn2-layout-kind-code
                           fn2-run-parser-span fn2-layout-scan fn2-layout-parse fn2-layout-octets
                           fn2-run-read-bytes fn2-pool-base fn2-layout-range-code
                           fn2-poolp fn2-pool-wfp fn2-fields-rows fn-b3-octet-listp)))))
