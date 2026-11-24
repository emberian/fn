; The source-row loader used by the overlay and run builder round-trips admitted overview entries.
(in-package "ACL2")
(include-book "ordered")
(include-book "runs-load-bytes-proof")
(include-book "runs-layout-id-proof")

(local
 (defthm fn2-run-octets-append
   (equal (fn-b3-octet-listp (append a b))
          (and (fn-b3-octet-listp (true-list-fix a)) (fn-b3-octet-listp b)))))

(local
 (defthm fn2-run-octets-flat-append
   (equal (fn-b3-octet-listp (true-list-fix (append a b)))
          (and (fn-b3-octet-listp (true-list-fix a)) (fn-b3-octet-listp (true-list-fix b))))))
(local (defthm fn2-run-fifth-value
 (equal (nth 4 values) (car (cddddr values)))
 :hints (("Goal" :expand ((:free (x) (nth 4 x)) (:free (x) (nth 3 x))
                          (:free (x) (nth 2 x)) (:free (x) (nth 1 x)) (:free (x) (nth 0 x)))))))

(local
 (defthm fn2-run-overview-line-octets
   (implies (fn2-run-values-layoutp *fn2-overview-entry* values)
            (fn-b3-octet-listp (true-list-fix (nth 4 values))))
   :hints (("Goal" :in-theory (e/d (fn2-run-values-layoutp fn2-layout-octets fn2-layout-field-octets)
          (fn2-layout-parse fn-b3-octet-listp fn2-layout-varoctets binary-append true-list-fix))))))

(local
 (defthm fn2-run-parse-line-proper
   (let ((res (fn2-layout-parse-field '(:octets 1024) bytes rest pos v hi size ref phase next)))
     (implies (equal (mv-nth 0 res) :ok) (true-listp (mv-nth 1 res))))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (fn2-layout-parse-field '(:octets 1024) bytes rest pos v hi size ref phase next)
            :in-theory (disable fn2-layout-byte take nthcdr nfix len)))))

(local
 (defthm fn2-run-decoded-row-shape
   (let ((res (fn2-layout-parse layout bytes)))
     (implies (eq (mv-nth 0 res) :ok)
              (and (equal (len (mv-nth 1 res)) (len layout)) (true-listp (mv-nth 1 res)))))
   :hints (("Goal" :induct (fn2-layout-parse layout bytes)
            :in-theory (disable fn2-layout-parse-field)))))
(local
 (defthm fn2-run-decoded-line-proper
   (let ((res (fn2-layout-parse layout bytes)))
     (implies (and (natp i) (equal (cadr (nth i layout)) '(:octets 1024)) (eq (mv-nth 0 res) :ok))
              (true-listp (nth i (mv-nth 1 res)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-run-parse-at-induct i layout bytes)
            :expand ((fn2-layout-parse layout bytes))
            :in-theory (disable fn2-layout-parse-field))
           ("Subgoal *1/1" :use
            ((:instance fn2-run-parse-line-proper (rest bytes) (pos 0) (v 0) (hi 0) (size 0)
                        (ref 0) (phase 0) (next 0)))))))
(defthm fn2-run-overview-admitted-row
   (implies (fn2-run-values-layoutp *fn2-overview-entry* values)
            (and (equal (len values) 5) (true-listp values) (true-listp (nth 4 values))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-decoded-row-shape (layout *fn2-overview-entry*)
                                   (bytes (fn2-layout-octets *fn2-overview-entry* values)))
                         (:instance fn2-run-decoded-line-proper (i 4) (layout *fn2-overview-entry*)
                                   (bytes (fn2-layout-octets *fn2-overview-entry* values))))
            :in-theory (e/d (fn2-run-values-layoutp) (fn2-layout-parse fn2-layout-octets
                    fn-b3-octet-listp fn2-run-decoded-row-shape)))))

(local
 (defthm fn2-run-overview-load-view
   (let* ((row (list g n a p line))
          (res (fn2-run-load-values *fn2-overview-entry* row base slot gen off 9 0 1 f pool))
          (load (fn2-run-load-bytes line slot gen off 9 0 1 pool))
          (f2 (mv-nth 2 res)) (pool2 (mv-nth 3 res)))
     (implies (and (natp base) (natp off) (natp g) (natp n) (natp a) (natp p))
              (and (equal (mv-nth 0 res) (mv-nth 0 load)) (equal pool2 (mv-nth 1 load))
                   (equal (mv-nth 1 res) (+ off (len line)))
                   (equal (fn2-run-unload-values *fn2-overview-entry* base f2 pool2)
                          (list g n a p (fn2-run-read-bytes (len line) slot gen off 9 0 1 pool2))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-load-values fn2-run-load-ref fn2-run-unload-values
                        fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len fn2-fields-set-value update-fn2-fields-value$ai
                        fn2-fields-set-ref-slot update-fn2-fields-ref-slot$ai
                        fn2-fields-set-ref-gen update-fn2-fields-ref-gen$ai
                        fn2-fields-set-ref-off update-fn2-fields-ref-off$ai
                        fn2-fields-set-ref-len update-fn2-fields-ref-len$ai nth-update-nth)
                    (fn2-run-fifth-value nth update-nth fn2-pool-base fn2-run-load-bytes fn2-run-read-bytes))))))

(local
 (defthm fn2-run-take-proper-row
   (implies (true-listp xs) (equal (take (len xs) xs) xs))))
(local
 (defthm fn2-run-first-five
   (equal (take 5 xs) (list (nth 0 xs) (nth 1 xs) (nth 2 xs) (nth 3 xs) (nth 4 xs)))
   :hints (("Goal" :in-theory (enable take nth)))))
(local
 (defthm fn2-run-five-fields
   (implies (and (true-listp xs) (equal (len xs) 5))
            (equal (list (nth 0 xs) (nth 1 xs) (nth 2 xs) (nth 3 xs) (nth 4 xs)) xs))
   :rule-classes nil
   :hints (("Goal" :use fn2-run-take-proper-row
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-first-five))))))
(local
 (defthm fn2-run-admitted-overview-ids
   (implies (fn2-run-values-layoutp *fn2-overview-entry* row)
            (and (natp (nth 0 row)) (natp (nth 1 row)) (natp (nth 2 row)) (natp (nth 3 row))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-layout-id-natural (layout *fn2-overview-entry*) (values row) (i 0) (id 'group))
                         (:instance fn2-run-layout-id-natural (layout *fn2-overview-entry*) (values row) (i 1) (id 'group-number))
                         (:instance fn2-run-layout-id-natural (layout *fn2-overview-entry*) (values row) (i 2) (id 'article))
                         (:instance fn2-run-layout-id-natural (layout *fn2-overview-entry*) (values row) (i 3) (id 'position)))
            :in-theory (disable fn2-run-values-layoutp nth)))))
(local (defthm fn2-run-proper-list-fix (implies (true-listp x) (equal (true-list-fix x) x))))
(defthm fn2-run-load-overview-roundtrip
 (let* ((line (nth 4 row)) (end (+ off (len line)))
        (load (fn2-run-load-values *fn2-overview-entry* row base slot gen off 9 0 1 f pool))
        (after (mv-nth 3 load)))
   (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row) (natp base) (natp off)
                 (natp (fn2-pool-base slot pool)) (<= end cap)
                 (eq (fn2-layout-range-code slot gen off cap t 9 0 1 pool) :ok))
            (and (eq (mv-nth 0 load) :ok) (equal (mv-nth 1 load) end)
                 (eq (fn2-layout-range-code slot gen end cap t 9 0 1 after) :ok)
                 (equal (fn2-run-unload-values *fn2-overview-entry* base (mv-nth 2 load) after) row))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-overview-admitted-row (values row))
                       (:instance fn2-run-overview-line-octets (values row))
                       fn2-run-admitted-overview-ids
                       (:instance fn2-run-five-fields (xs row))
                       (:instance fn2-run-overview-load-view (g (nth 0 row)) (n (nth 1 row))
                                  (a (nth 2 row)) (p (nth 3 row)) (line (nth 4 row)))
                       (:instance fn2-run-load-bytes-roundtrip (bytes (nth 4 row)) (pk 9) (ps 0) (pg 1)))
          :in-theory (union-theories (theory 'minimal-theory)
                      '(eq (:e equal) (:e not) fn2-run-proper-list-fix)))))
