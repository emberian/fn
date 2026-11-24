; The pool's remaining free suffix lies beyond every published page.
; Taking its head preserves the entire run, including all parent references.
(in-package "ACL2")
(include-book "range-reservation-page-contents-proof")
(include-book "range-published-run-pages-proof")

(defthmd fn2-range-reserve-keeps-encoded-page
  (fn2-range-earlier-page-bindings
   (implies (fn2-run-encoded-overview-page-p rows level outer inner slot gen 9 0 1 p)
            (fn2-run-encoded-overview-page-p rows level outer inner slot gen 9 0 1 after)))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-range-reserve-keeps-stored-page (layout *fn2-format-page-header*)
                       (vals outer) (off 0) (end *fn2-run-header-area*) (pk 9) (ps 0) (pg 1))
                 (:instance fn2-range-reserve-keeps-stored-page (layout *fn2-run-page-header*)
                       (vals inner) (off *fn2-run-header-area*) (end *fn2-run-entries-base*) (pk 9) (ps 0) (pg 1)))
           :in-theory (e/d (fn2-run-encoded-overview-page-p fn2-run-page-headers-p fn2-range-reserve-keeps-earlier-page-bytes
                         fn2-pool-reserve-preserves-type fn2-pool-reserve-preserves-wfp)
              (fn2-pool-reserve fn2-range-pool-available-p fn2-pool-mrefp fn2-run-entries-layoutp
               fn2-run-stored-header-p fn2-run-stored-overview-page-p fn2-run-restart-offsets-spec fn2-run-directory-octets
               fn2-run-entries-octets fn2-run-read-bytes fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-range-code
               ceiling ceiling-to-floor len nth unsigned-byte-p)))))

(defun-nx fn2-range-pages-before-slot-p (pages next)
  (if (atom pages) (null pages)
    (and (natp (nth 3 (car pages))) (< (nth 3 (car pages)) next)
         (fn2-range-pages-before-slot-p (cdr pages) next))))

(local
 (defthmd fn2-range-reservation-keeps-published-node
   (let ((slot (nth 3 (car node))))
     (fn2-range-earlier-page-bindings
      (implies (fn2-range-published-node-p node earlier p)
               (fn2-range-published-node-p node earlier after))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-range-reserve-keeps-encoded-page (rows (nth 1 node)) (level (caar node))
                           (outer (nth 2 node)) (inner (nth 3 node)) (slot (nth 3 (car node))) (gen (nth 4 (car node)))))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-published-node-p))))))

(defthmd fn2-range-reservation-keeps-published-run
  (let ((r (fn2-pool-reserve 0 owner os og p)))
    (implies (and (posp free) (fn2-range-pool-available-p free p) (fn2-pool-mrefp owner os og)
                  (fn2-range-pages-before-slot-p pages (- 327 free))
                  (fn2-range-published-run-pages-p records pages p))
             (and (equal (car r) :ok) (equal (mv-nth 1 r) (- 327 free))
                  (fn2-range-pool-available-p (1- free) (mv-nth 3 r))
                  (fn2-range-published-run-pages-p records pages (mv-nth 3 r)))))
  :hints (("Goal" :induct (fn2-range-published-run-pages-p records pages p)
           :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-range-published-run-pages-p fn2-range-pages-before-slot-p
                         fn2-range-reservation-keeps-published-node (:induction fn2-range-published-run-pages-p)
                         not atom (:e equal))))
          ("Subgoal *1/1" :use ((:instance fn2-range-reserve-preserves-remaining-capacity (pk owner) (ps os) (pg og) (n free))))
          ("Subgoal *1/2" :use ((:instance fn2-range-reserve-preserves-remaining-capacity (pk owner) (ps os) (pg og) (n free))))))
