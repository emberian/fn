; The physical request's ARTICLE scratch and page/sector region are one
; preheader admission. No capacity wait may retain a partial query recipe.
(in-package "ACL2")
(include-book "cursor-kind")
(include-book "machines-c-read-loader")
(fn2-book-layer :d)

;; Existing lease selector moved unchanged from cursor.lisp.
(defun fn2-cursor-lease-class-of (fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (fn2-pool-class-for (+ *fn2-article-location-hashes-max* (* 2 *fn2-commit-unit-bytes*)) fn2-pool))

(defun fn2-cursor-article-scratch-p (tag)
 (declare (xargs :guard t))
 (or (equal tag *fn2-nntp-command-article*) (equal tag *fn2-nntp-command-head*)
     (equal tag *fn2-nntp-command-body*) (equal tag *fn2-nntp-command-xfn-zarticle*)
     (equal tag *fn2-nntp-command-hdr*) (equal tag *fn2-nntp-command-xhdr*)
     (equal tag *fn2-nntp-command-xpat*)))

(defmacro fn2-cursor-article-query-mv (code complete slot gen)
 `(mv ,code ,complete ,slot ,gen fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
(defun fn2-cursor-article-query-reserve-children (read0 kind owner generation
 fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 :guard (and (fn2-reads-wfp fn2-reads) (fn2-id-decides-wfp fn2-id-decides) (fn2-run-loads-wfp fn2-run-loads)
             (fn2-run-cursors-wfp fn2-run-cursors) (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
             (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-pool-wfp fn2-pool))))
 (b* ((class (fn2-cursor-lease-class-of fn2-pool))
      ((unless (and (natp class) (< class (fn2-pool-nclasses fn2-pool))))
       (fn2-cursor-article-query-mv :exhausted 0 *fn2-none* 0))
      ((mv code slot gen fn2-pool) (fn2-pool-reserve class kind owner generation fn2-pool))
      ((unless (eq code :ok)) (fn2-cursor-article-query-mv code 0 *fn2-none* 0))
      ((mv code complete fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
       (fn2-run-page-bundle-reserve-children read0 kind owner generation fn2-reads fn2-id-decides
        fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      ;; OK/0 is actual retained partial region ownership, not permission to
      ;; interpret a query. The actor retains BOTH pieces for terminal drain.
      ((when (eq code :ok)) (fn2-cursor-article-query-mv :ok complete slot gen))
      ;; Definite refusal rolls the independent scratch back in this same
      ;; callback. A structural release failure retains its actual handle.
      ((unless (fn2-pool-release-countp slot fn2-pool))
       (fn2-cursor-article-query-mv :recovery-required 0 slot gen))
      ((mv released fn2-pool) (fn2-pool-release slot gen kind owner generation fn2-pool)))
  (if (member-eq released '(:ok :retired))
   (fn2-cursor-article-query-mv code 0 *fn2-none* 0)
   (fn2-cursor-article-query-mv :recovery-required 0 slot gen))))
(fn2-run-load-frames fn2-cursor-article-query-reserve-children
 (read0 kind owner generation fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 ((fn2-run-loads 4) (fn2-run-cursors 5) (fn2-checkpoint-summary 6) (fn2-checkpoint-summary-leases 7) (fn2-pool 8)))
