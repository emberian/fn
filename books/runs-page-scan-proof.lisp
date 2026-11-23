; A checked prefix accepted by the layout parser is consumed by the page scanner.
(in-package "ACL2")
(include-book "runs-load-bytes-proof")
(include-book "runs-page-reader-proof")
(local (include-book "runs-page-window-proof"))

(local
 (defthm fn2-run-scan-parser-progress
 (let* ((xs (fn2-run-page-window next bound slot gen pk ps pg pool))
        (parse (fn2-run-parser-span layout xs pos v hi size phase))
        (scan (fn2-layout-scan layout fuel i pos v hi size ref phase next slot gen end pk ps pg f pool)))
   (implies (and (natp next) (natp bound) (<= next bound) (<= bound end)
                 (natp fuel) (<= (- bound next) fuel)
                 (natp i) (<= (+ i (len layout)) (fn2-fields-rows f))
                 (natp pos) (natp v) (natp hi) (natp size) (natp phase)
                 (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                 (eq (fn2-layout-range-code slot gen next bound nil pk ps pg pool) :ok)
                 (eq (car parse) :ok))
            (and (equal (car scan) :ok)
                 (equal (mv-nth 8 scan) (- bound (len (mv-nth 1 parse)))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-layout-scan layout fuel i pos v hi size ref phase next slot gen end pk ps pg f pool)
          :do-not '(preprocess generalize fertilize eliminate-destructors)
          :expand ((fn2-layout-scan layout fuel i pos v hi size ref phase next slot gen end pk ps pg f pool))
          :in-theory (e/d ((:induction fn2-layout-scan) fn2-run-layout-byte-naturals fn2-run-reader-octet
                           fn2-run-reader-nfix)
                          ((:definition fn2-layout-scan) fn2-run-parser-span fn2-run-parser-span-at-start fn2-run-page-window fn2-layout-store
                           fn2-layout-byte fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-range-code
                           fn2-pool-read fn2-fields-rows fn2-fields-value fn2-fields-ref-off
                           fn2-fields-ref-len fn2-fields-ref-gen fn2-fields-ref-slot fn2-fields-status
                           mod nfix unsigned-byte-p member-equal)))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use fn2-run-checked-parser-step)))))

(defthm fn2-run-page-scan-consumes-admitted-row
 (let* ((bytes (fn2-layout-octets layout row))
        (bound (+ off (len bytes)))
        (scan (fn2-layout-scan layout fuel base 0 0 0 0 0 0 off slot gen end pk ps pg f pool)))
   (implies (and (fn2-run-values-layoutp layout row)
                 (natp base) (<= (+ base (len layout)) (fn2-fields-rows f))
                 (natp off) (<= bound end) (natp fuel) (<= (len bytes) fuel)
                 (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                 (eq (fn2-layout-range-code slot gen off bound nil pk ps pg pool) :ok)
                 (equal (fn2-run-read-bytes (len bytes) slot gen off pk ps pg pool) bytes))
            (and (equal (car scan) :ok)
                 (equal (mv-nth 8 scan) bound))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-scan-parser-progress
             (next off) (bound (+ off (len (fn2-layout-octets layout row))))
             (i base) (pos 0) (v 0) (hi 0) (size 0) (ref 0) (phase 0)))
          :in-theory (e/d (fn2-run-values-layoutp fn2-run-page-window)
                          (fn2-run-parser-span fn2-layout-scan fn2-layout-parse fn2-layout-octets
                           fn2-run-read-bytes fn2-pool-base fn2-layout-range-code
                           fn2-poolp fn2-pool-wfp fn2-fields-rows fn-b3-octet-listp)))))
