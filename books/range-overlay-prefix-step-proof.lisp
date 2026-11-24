; Lift one physical insertion from its per-position result to the index
; predicate over every byte offset of the extended source.
(in-package "ACL2")
(include-book "range-overlay-prefix-insert-proof")
(include-book "range-overlay-prefix-offset-proof")

(defmacro fn2-ov-source-load (rows row src sg f p)
  `(fn2-run-load-values *fn2-overview-entry* ,row *fn2-run-adapter-entry*
                         ,src ,sg (fn2-range-line-bytes ,rows) 9 0 1 ,f ,p))

(defmacro fn2-ov-source-insert (rows row src sg ov ix f p)
  `(let ((load (fn2-ov-source-load ,rows ,row ,src ,sg ,f ,p)))
     (fn2-ov-insert 0 *fn2-run-adapter-entry* *fn2-run-adapter-reader* ,ov ,ix (mv-nth 2 load) (mv-nth 3 load))))

(defun-nx fn2-ov-prefix-step-p (rows row src sg ov ix f pool)
  (and (fn2-ov-load-workspaces-p rows src sg ov ix f pool)
       (fn2-run-entries-layoutp *fn2-overview-entry* rows)
       (fn2-run-values-layoutp *fn2-overview-entry* row)
       (fn2-run-sorted-spec *fn2-overview-range-key* (append rows (list row))) (< (len rows) 48)))

(local
 (defthmd fn2-ov-earlier-offset-after-insert
   (let ((b (fn2-overlays-ibase 0 ov)) (res (fn2-ov-source-insert rows row src sg ov ix f pool)))
     (implies (and (fn2-ov-prefix-step-p rows row src sg ov ix f pool) (natp j) (< j (len rows)))
              (equal (fn2-overlay-index-off (+ b j) (mv-nth 2 res)) (fn2-overlay-index-off (+ b j) ix))))
   :hints (("Goal" :do-not '(preprocess) :use fn2-ov-inserts-next-prefix-row
            :in-theory (e/d (fn2-ov-prefix-step-p)
                       (fn2-ov-load-workspaces-p fn2-run-entries-layoutp fn2-run-values-layoutp fn2-run-sorted-spec
                        fn2-ov-insert fn2-run-load-values fn2-range-line-bytes fn2-run-load-bytes fn2-layout-octets
                        fn2-layout-range-code fn2-run-read-bytes fn2-overlays-ibase fn2-overlays-slot fn2-overlays-gen
                        fn2-overlays-count fn2-overlays-fill fn2-overlay-index-off binary-append nth len))))))

(local (defun fn2-ov-count-offsets (m)
         (if (zp m) 0 (1+ (fn2-ov-count-offsets (1- m))))))

(local
 (defthmd fn2-ov-earlier-index-after-insert
   (let ((b (fn2-overlays-ibase 0 ov)) (res (fn2-ov-source-insert rows row src sg ov ix f pool)))
     (implies (and (fn2-ov-prefix-step-p rows row src sg ov ix f pool) (natp m) (<= m (len rows)))
              (fn2-ov-index-agrees-before-p m b ix (mv-nth 2 res))))
   :hints (("Goal" :induct (fn2-ov-count-offsets m)
           :in-theory (e/d (fn2-ov-earlier-offset-after-insert) (fn2-ov-prefix-step-p fn2-run-load-values
                      fn2-ov-insert fn2-overlays-ibase fn2-overlay-index-off fn2-range-line-bytes len)))
           (and (equal (access clause-id id :pool-lst) '(1)) (equal (len (access clause-id id :case-lst)) 1) (equal (access clause-id id :primes) 0) '(:use ((:instance fn2-ov-earlier-offset-after-insert (j (1- m)))))))))


(defthmd fn2-ov-source-insert-extends-index
  (let ((b (fn2-overlays-ibase 0 ov)) (res (fn2-ov-source-insert rows row src sg ov ix f pool)))
    (implies (fn2-ov-prefix-step-p rows row src sg ov ix f pool)
             (fn2-ov-prefix-offsets-p (1+ (len rows)) (append rows (list row)) b (mv-nth 2 res))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-earlier-index-after-insert (m (len rows)))
                 (:instance fn2-ov-inserts-next-prefix-row (j (len rows)))
                 (:instance fn2-ov-append-extends-prefix-offsets (b (fn2-overlays-ibase 0 ov))
                     (ix2 (mv-nth 2 (fn2-ov-source-insert rows row src sg ov ix f pool)))))
           :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-ov-prefix-step-p fn2-ov-load-workspaces-p fn2-ov-contiguous-arena-p natp
                        (:t len) (:e <) (:e equal) (:e binary-+) (:e not))))))
