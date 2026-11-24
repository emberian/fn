; A writer uses at most the 64 KiB at its assigned slot. The physical
; bytes, headers and child links of all other published pages survive.
(in-package "ACL2")
(include-book "range-published-run-pages-proof")
(include-book "runs-page-copy-proof")

(defun-nx fn2-range-fixed-page-slot-p (slot pool)
  (and (natp slot) (equal (fn2-pool-base slot pool) (* 65536 slot))))

(local
 (defthmd fn2-range-distinct-slots-have-disjoint-bytes
   (implies (and (natp src) (natp dst) (not (equal src dst))
                 (natp at) (natp n) (<= (+ at n) 65536)
                 (natp off) (natp size) (<= (+ off size) 65536))
            (or (<= (+ (* 65536 src) at n) (+ (* 65536 dst) off))
                (<= (+ (* 65536 dst) off size) (+ (* 65536 src) at))))
   :hints (("Goal" :cases ((< src dst))))))

(defmacro fn2-range-distinct-slot-write (body)
  `(let ((after (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 pool))))
     (implies (and (fn2-range-fixed-page-slot-p slot pool) (fn2-range-fixed-page-slot-p dst pool)
                   (not (equal slot dst)) (natp off) (<= (+ off (len bytes)) 65536))
              ,body)))

(defthmd fn2-range-disjoint-write-preserves-page-bytes
  (fn2-range-distinct-slot-write
   (implies (and (natp at) (natp n) (<= (+ at n) 65536))
            (equal (fn2-run-read-bytes n slot gen at 9 0 1 after) (fn2-run-read-bytes n slot gen at 9 0 1 pool))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-range-distinct-slots-have-disjoint-bytes (src slot) (size (len bytes)))
                 (:instance fn2-run-load-preserves-earlier-bytes (src slot) (sg gen) (pk 9) (ps 0) (pg 1)))
           :in-theory (e/d (fn2-range-fixed-page-slot-p)
             (fn2-run-load-preserves-earlier-bytes fn2-run-read-bytes fn2-run-load-bytes fn2-pool-base len)))))

(local
 (defthmd fn2-range-disjoint-write-preserves-stored-header
   (fn2-range-distinct-slot-write
    (implies (and (fn2-run-stored-header-p layout vals slot gen at end 9 0 1 pool) (<= end 65536))
             (fn2-run-stored-header-p layout vals slot gen at end 9 0 1 after)))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-range-disjoint-write-preserves-page-bytes (n (len (fn2-layout-octets layout vals)))))
            :in-theory (e/d (fn2-run-stored-header-p fn2-range-fixed-page-slot-p
                              fn2-run-load-preserves-pool fn2-run-load-preserves-other-range fn2-run-load-preserves-base)
                    (fn2-run-values-layoutp fn2-run-header-scalars-p fn2-run-read-bytes fn2-run-load-bytes
                     fn2-layout-octets fn2-layout-range-code fn2-poolp fn2-pool-wfp fn2-pool-base len))))))

(defthmd fn2-range-disjoint-write-preserves-encoded-page
  (fn2-range-distinct-slot-write
   (implies (fn2-run-encoded-overview-page-p rows level outer inner slot gen 9 0 1 pool)
            (fn2-run-encoded-overview-page-p rows level outer inner slot gen 9 0 1 after)))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-range-disjoint-write-preserves-stored-header (layout *fn2-format-page-header*)
                        (vals outer) (at 0) (end *fn2-run-header-area*))
                 (:instance fn2-range-disjoint-write-preserves-stored-header (layout *fn2-run-page-header*)
                        (vals inner) (at *fn2-run-header-area*) (end *fn2-run-entries-base*))
                 (:instance fn2-range-disjoint-write-preserves-page-bytes (at *fn2-run-entries-base*)
                        (n (len (fn2-run-entries-octets (fn2-run-overview-layout-at level) rows))))
                 (:instance fn2-range-disjoint-write-preserves-page-bytes (at (fn2-run-overview-directory-offset level rows))
                        (n (* 4 (len (fn2-run-overview-page-offsets level rows))))))
           :in-theory (e/d (fn2-range-fixed-page-slot-p fn2-run-encoded-overview-page-p fn2-run-page-headers-p
                            fn2-run-load-preserves-pool fn2-run-load-preserves-other-range fn2-run-load-preserves-base)
              (fn2-run-load-bytes fn2-run-read-bytes fn2-run-stored-header-p fn2-run-entries-layoutp fn2-layout-range-code
               fn2-run-entries-octets fn2-run-restart-offsets-spec fn2-run-directory-octets fn2-poolp fn2-pool-wfp
               fn2-pool-base len nth ceiling ceiling-to-floor unsigned-byte-p)))))

(defun-nx fn2-range-published-slots-apart-p (pages dst pool)
  (if (atom pages) (null pages)
    (let ((slot (nth 3 (car pages))))
      (and (fn2-range-fixed-page-slot-p slot pool) (not (equal slot dst))
           (fn2-range-published-slots-apart-p (cdr pages) dst pool)))))

(local
 (defthmd fn2-range-disjoint-write-preserves-node
   (let ((slot (nth 3 (car node))))
     (fn2-range-distinct-slot-write
      (implies (fn2-range-published-node-p node earlier pool) (fn2-range-published-node-p node earlier after))))
   :hints (("Goal" :use ((:instance fn2-range-disjoint-write-preserves-encoded-page (rows (nth 1 node)) (level (caar node))
                          (outer (nth 2 node)) (inner (nth 3 node)) (slot (nth 3 (car node))) (gen (nth 4 (car node)))))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-published-node-p))))))

(defthmd fn2-range-disjoint-write-preserves-published-run
  (let ((after (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 pool))))
    (implies (and (fn2-range-fixed-page-slot-p dst pool) (natp off) (<= (+ off (len bytes)) 65536)
                  (fn2-range-published-slots-apart-p pages dst pool) (fn2-range-published-run-pages-p records pages pool))
             (fn2-range-published-run-pages-p records pages after)))
  :hints (("Goal" :induct (fn2-range-published-run-pages-p records pages pool)
           :in-theory (union-theories (theory 'minimal-theory)
               '(fn2-range-published-run-pages-p fn2-range-published-slots-apart-p fn2-range-disjoint-write-preserves-node
                 (:induction fn2-range-published-run-pages-p) atom not (:e equal))))))

(local
 (defthm fn2-range-page-write-keeps-slot-assignment
   (equal (fn2-range-fixed-page-slot-p slot (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 pool)))
          (fn2-range-fixed-page-slot-p slot pool))
   :hints (("Goal" :in-theory (e/d (fn2-range-fixed-page-slot-p fn2-run-load-preserves-base)
                                 (fn2-run-load-bytes fn2-pool-base))))))

(local
 (defthm fn2-range-page-write-keeps-separate-slots
   (equal (fn2-range-published-slots-apart-p pages slot (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 pool)))
          (fn2-range-published-slots-apart-p pages slot pool))
   :hints (("Goal" :induct (len pages)
            :in-theory (e/d (fn2-range-published-slots-apart-p) (fn2-range-fixed-page-slot-p fn2-run-load-bytes nth))))))

(defthmd fn2-range-two-writes-retain-published-pages
   (let* ((written (mv-nth 1 (fn2-run-load-bytes first-bytes first-slot first-gen first-off 9 0 1 pool)))
          (result (if secondp (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 written)) written)))
     (implies (and (fn2-range-published-run-pages-p records pages pool)
                   (fn2-range-fixed-page-slot-p first-slot pool) (fn2-range-published-slots-apart-p pages first-slot pool)
                   (natp first-off) (<= (+ first-off (len first-bytes)) 65536)
                   (implies secondp (and (fn2-range-fixed-page-slot-p dst pool) (fn2-range-published-slots-apart-p pages dst pool)
                                      (natp off) (<= (+ off (len bytes)) 65536))))
              (fn2-range-published-run-pages-p records pages result)))
   :hints (("Goal" :do-not '(preprocess) :cases (secondp)
            :in-theory (union-theories (theory 'minimal-theory)
               '(fn2-range-disjoint-write-preserves-published-run fn2-range-page-write-keeps-separate-slots
                 fn2-range-page-write-keeps-slot-assignment)))))
