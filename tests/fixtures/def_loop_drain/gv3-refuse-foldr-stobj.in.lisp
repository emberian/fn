(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-cat-view-last-visible-loop (rev v fn-cat acc)
  (declare (xargs :stobjs fn-cat :guard (natp v) :verify-guards nil))
  (if (consp rev)
      (fn-cat-view-last-visible-loop (cdr rev)
                                     v
                                     fn-cat
                                     (let ((rest acc))
                                       (if rest
                                           rest
                                         (let ((seq (car rev)))
                                           (if (and (natp seq)
                                                    (< seq (fn-cat-count fn-cat))
                                                    (fn-cat-visible-at seq v fn-cat))
                                               seq
                                             nil)))))
    acc))

(defun fn-cat-view-last-visible (seqs v fn-cat)
  (declare (xargs :verify-guards nil :stobjs fn-cat :guard (natp v)
                  :guard-hints (("Goal" :in-theory (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth)))))
  (mbe :logic
       (if (consp seqs)
           (let ((rest (fn-cat-view-last-visible (cdr seqs) v fn-cat)))
             (if rest
                 rest
               (let ((seq (car seqs)))
                 (if (and (natp seq) (< seq (fn-cat-count fn-cat)) (fn-cat-visible-at seq v fn-cat))
                     seq
                   nil))))
         nil)
       :exec (fn-cat-view-last-visible-loop (fn-ag-rev-onto seqs nil) v fn-cat nil)))

(local
 (defthm fn-cat-view-last-visible-loop-of-rev-onto
   (equal (fn-cat-view-last-visible-loop (fn-ag-rev-onto seqs zs) v fn-cat nil)
          (fn-cat-view-last-visible-loop zs v fn-cat (fn-cat-view-last-visible seqs v fn-cat)))
   :hints (("Goal" :induct (fn-ag-rev-onto seqs zs)
                   :in-theory (union-theories '(fn-cat-view-last-visible-loop fn-cat-view-last-visible fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cat-view-last-visible-loop
  :hints (("Goal"
           :in-theory
           (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth))))

(verify-guards fn-cat-view-last-visible
  :hints (("Goal" :in-theory (union-theories '(fn-cat-view-last-visible fn-cat-view-last-visible-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-cat-view-last-visible-loop-of-rev-onto (zs nil))))))
