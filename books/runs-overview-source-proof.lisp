; Physical field references and the line-length bound for the adapter's source row.
(in-package "ACL2")
(include-book "runs-load-overview-proof")

(local
 (defthm fn2-run-line-transition-length
 (let ((step (fn2-layout-byte '(:octets 1024) pos v hi size phase byte)))
  (implies (<= (nfix size) 1024)
           (and (not (equal (car step) :ok))
                (implies (member-eq (car step) '(:done :part :payload))
                         (<= (nfix (mv-nth 3 step)) 1024)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-layout-byte) (mod floor ash))))))

(local
 (defthm fn2-run-taken-line-length (equal (len (take n xs)) (nfix n))
 :hints (("Goal" :induct (take n xs)))))

(local
 (defthm fn2-run-parse-line-length
 (let ((parse (fn2-layout-parse-field '(:octets 1024) bytes rest pos v hi size ref phase next)))
  (implies (and (<= (nfix size) 1024) (equal (car parse) :ok))
           (<= (len (mv-nth 1 parse)) 1024)))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :induct (fn2-layout-parse-field '(:octets 1024) bytes rest pos v hi size ref phase next)
          :in-theory (disable fn2-layout-byte nfix take nthcdr))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use ((:instance fn2-run-line-transition-length (byte (car rest)))))))))

(local
 (defthm fn2-run-parsed-line-limit
 (let ((r (fn2-layout-parse layout bytes)))
  (implies (and (natp i) (equal (cadr (nth i layout)) '(:octets 1024)) (eq (car r) :ok))
           (<= (len (nth i (mv-nth 1 r))) 1024)))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-run-parse-at-induct i layout bytes)
          :expand ((fn2-layout-parse layout bytes))
          :in-theory (disable fn2-layout-parse-field))
         ("Subgoal *1/1" :use ((:instance fn2-run-parse-line-length
           (rest bytes) (pos 0) (v 0) (hi 0) (size 0) (ref 0) (phase 0) (next 0)))))))

(defthm fn2-run-admitted-line-fits-source
 (implies (fn2-run-values-layoutp *fn2-overview-entry* row) (<= (len (nth 4 row)) 1024))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-parsed-line-limit (i 4) (layout *fn2-overview-entry*)
                         (bytes (fn2-layout-octets *fn2-overview-entry* row))))
          :in-theory (e/d (fn2-run-values-layoutp)
                          (fn2-layout-parse fn2-layout-octets fn-b3-octet-listp nth)))))

(defthm fn2-run-overview-source-fields
 (let* ((load (fn2-run-load-values *fn2-overview-entry* row base slot gen off 9 0 1 f pool))
        (sf (mv-nth 2 load)) (i (+ base 4)) (line (car (cddddr row))))
  (implies (and (natp base) (natp off))
           (and (natp (fn2-fields-value base sf)) (natp (fn2-fields-value (+ base 1) sf))
                (natp (fn2-fields-value (+ base 2) sf)) (natp (fn2-fields-value (+ base 3) sf))
                (equal (fn2-fields-ref-slot i sf) slot) (equal (fn2-fields-ref-gen i sf) gen)
                (equal (fn2-fields-ref-off i sf) off) (equal (fn2-fields-ref-len i sf) (len line))
                (equal (mv-nth 3 load) (mv-nth 1 (fn2-run-load-bytes line slot gen off 9 0 1 pool))))))
 :hints (("Goal" :in-theory (e/d (fn2-run-load-values fn2-run-load-ref
                        fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off
                        fn2-fields-ref-len fn2-fields-set-value update-fn2-fields-value$ai
                        fn2-fields-set-ref-slot update-fn2-fields-ref-slot$ai
                        fn2-fields-set-ref-gen update-fn2-fields-ref-gen$ai
                        fn2-fields-set-ref-off update-fn2-fields-ref-off$ai
                        fn2-fields-set-ref-len update-fn2-fields-ref-len$ai nth-update-nth)
                    (nth update-nth nfix fn2-run-load-bytes)))))
