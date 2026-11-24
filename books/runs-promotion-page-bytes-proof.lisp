; Promotion writes in two places, the digest workspace and the tail of
; the parent. A byte range outside those writes remains readable verbatim.
(in-package "ACL2")
(include-book "runs-index-promotion-proof")
(local (include-book "runs-page-copy-proof"))

(defun-nx fn2-run-write-outside-read-p (view at n dst off size p)
  (let ((start (+ (fn2-pool-base view p) at)) (target (+ (fn2-pool-base dst p) off)))
    (and (natp view) (natp at) (natp n) (natp dst) (natp off)
         (natp (fn2-pool-base view p)) (natp (fn2-pool-base dst p))
         (or (not (equal view dst)) (<= (+ at n) off))
         (or (<= (+ start n) target) (<= (+ target size) start)))))

(local
 (defthm fn2-run-digest-byte-count
   (equal (len (fn2-page-parent-octets i n words)) (nfix n))
   :hints (("Goal" :induct (fn2-page-parent-octets i n words)
            :in-theory (e/d (fn2-page-parent-octets) (fn2-fc-word-byte floor mod nth))))))

(local
 (defthm fn2-run-read-outside-load
   (implies (fn2-run-write-outside-read-p view at n dst off (len bytes) p)
            (equal (fn2-run-read-bytes n view vg at 9 0 1 (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 p)))
                   (fn2-run-read-bytes n view vg at 9 0 1 p)))
   :hints (("Goal" :use ((:instance fn2-run-load-preserves-earlier-bytes (src view) (sg vg) (pool p) (pk 9) (ps 0) (pg 1)))
            :in-theory (e/d (fn2-run-write-outside-read-p)
                        (fn2-run-load-preserves-earlier-bytes fn2-run-read-bytes fn2-run-load-bytes fn2-pool-base))))))

(local
 (defthm fn2-run-load-keeps-read-geometry
   (equal (fn2-run-write-outside-read-p view at n dst off size (mv-nth 1 (fn2-run-load-bytes bytes h hg ha 9 0 1 p)))
          (fn2-run-write-outside-read-p view at n dst off size p))
   :hints (("Goal" :in-theory (e/d (fn2-run-write-outside-read-p) (fn2-run-load-bytes fn2-pool-base))))))

(local
 (defthm fn2-run-reference-and-append-keep-page-bytes
   (let ((rp (mv-nth 1 (fn2-run-load-bytes (fn2-page-parent-octets 0 32 (fn2-digest-list hrow ds))
                                         hslot hgen (* 32 level) 9 0 1 pool))))
     (implies (and (fn2-run-index-promotion-result-p fits level w ordinal dst dg off idx nr bytes rp builds writers restarts commit promote)
                   (fn2-run-write-outside-read-p view at n hslot (* 32 level) 32 pool)
                   (implies fits (fn2-run-write-outside-read-p view at n dst off (len bytes) pool)))
              (equal (fn2-run-read-bytes n view vg at 9 0 1 (mv-nth 5 promote))
                     (fn2-run-read-bytes n view vg at 9 0 1 pool))))
   :rule-classes nil
   :hints (("Goal" :cases (fits) :do-not '(preprocess)
            :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-run-index-promotion-result-p fn2-run-read-outside-load fn2-run-load-keeps-read-geometry
                         fn2-run-digest-byte-count (:e nfix) (:e equal)))))))

(defthm fn2-run-promoting-child-preserves-page-bytes
  (fn2-run-promoting-index-row
   (implies (and (fn2-run-write-outside-read-p view at n hslot (* 32 level) 32 pool)
                 (implies fits (fn2-run-write-outside-read-p view at n dst off (len bytes) pool)))
            (and (fn2-run-parent-promotion-effects)
                 (equal (fn2-run-read-bytes n view vg at 9 0 1 (mv-nth 5 promote))
                        (fn2-run-read-bytes n view vg at 9 0 1 pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-builder-appends-or-retries-promoted-index
                 (:instance fn2-run-promoted-index-row-is-admitted (w level) (ib *fn2-run-build-index*)
                       (hrow (+ 136 level)) (hslot (fn2-run-builds-hslot 0 builds)) (hgen (fn2-run-builds-hgen 0 builds)))
                 (:instance fn2-run-reference-and-append-keep-page-bytes (w (1+ level))
                       (hrow (+ 136 level)) (hslot (fn2-run-builds-hslot 0 builds)) (hgen (fn2-run-builds-hgen 0 builds))
                       (ordinal (1+ (fn2-run-writers-ordinal level writers))) (idx (fn2-run-writers-entries (1+ level) writers))
                       (nr (fn2-run-writers-restarts (1+ level) writers)) (dst (fn2-run-writers-slot (1+ level) writers))
                       (dg (fn2-run-writers-gen (1+ level) writers)) (off (fn2-run-writers-cursor (1+ level) writers))
                       (bytes (fn2-run-child-index-bytes rows level (+ 136 level) writers ds))
                       (fits (fn2-run-index-fits-writer (1+ level) (fn2-run-child-index-bytes rows level (+ 136 level) writers ds) writers))
                       (promote (fn2-run-build-promote 0 level builds writers restarts f pool ds))
                       (commit (let* ((ref (fn2-run-promotion-input level level *fn2-run-build-index*
                                     (fn2-run-writers-cursor level writers) (+ 136 level) (fn2-run-builds-hslot 0 builds)
                                     (fn2-run-builds-hgen 0 builds) writers f pool ds))
                                     (parent (fn2-run-add (1+ level) 3 *fn2-run-build-index* writers restarts
                                                          (mv-nth 1 ref) (mv-nth 2 ref))))
                                 (fn2-run-promote-commit level (car parent) (mv-nth 1 parent))))))
           :in-theory (theory 'minimal-theory))))
