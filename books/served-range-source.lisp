; Actual old range source vocabulary for full residual reply refinement.
(in-package "ACL2")
(include-book "catalog-number-range-source")
(include-book "served-selected-lines")

(defun fn-scat-range-keep-loop (group seqs fn-cat acc)
  (declare (xargs :stobjs fn-cat :guard (true-listp acc) :verify-guards nil))
  (if (consp seqs)
      (let ((s (car seqs)))
        (if (and (natp s) (< s (fn-cat-count fn-cat)))
            (let* ((h (fn-cat-at s fn-cat))
                   (n (fn-held-number-in group h)))
              (if (and (posp n)
                       (<= n *fn-nntp-max-article-number*)
                       (fn-scat-msgid-idp (fn-record-msgid h)))
                  (fn-scat-range-keep-loop group (cdr seqs) fn-cat (cons n acc))
                (fn-scat-range-keep-loop group (cdr seqs) fn-cat acc)))
          (fn-scat-range-keep-loop group (cdr seqs) fn-cat acc)))
    (revappend acc nil)))

(defun fn-scat-range-keep (group seqs fn-cat)
  (declare (xargs :verify-guards nil :stobjs fn-cat :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-cat-p-is-rowsp fn-cat-count-is-len
                                                            fn-cat-at-is-nth)))))
  (mbe :logic
       (if (consp seqs)
           (let ((s (car seqs)))
             (if (and (natp s) (< s (fn-cat-count fn-cat)))
                 (let* ((h (fn-cat-at s fn-cat))
                        (n (fn-held-number-in group h)))
                   (if (and (posp n) (<= n *fn-nntp-max-article-number*)
                            (fn-scat-msgid-idp (fn-record-msgid h)))
                       (cons n (fn-scat-range-keep group (cdr seqs) fn-cat))
                     (fn-scat-range-keep group (cdr seqs) fn-cat)))
               (fn-scat-range-keep group (cdr seqs) fn-cat)))
         nil)
       :exec (fn-scat-range-keep-loop group seqs fn-cat nil)))

(local
 (defthm fn-scat-range-keep-loop-is-revappend
   (equal (fn-scat-range-keep-loop group seqs fn-cat acc)
          (revappend acc (fn-scat-range-keep group seqs fn-cat)))
   :hints (("Goal" :induct (fn-scat-range-keep-loop group seqs fn-cat acc)
                   :in-theory (union-theories '(fn-scat-range-keep-loop fn-scat-range-keep revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-scat-range-keep-loop
  :hints (("Goal"
           :in-theory
           (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth))))

(verify-guards fn-scat-range-keep
  :hints (("Goal" :in-theory (union-theories '(revappend fn-scat-range-keep)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-scat-range-keep-loop-is-revappend (acc nil))))))

(defun fn-ovw-lines (group k hi v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp k) (natp hi) (fn-scat-guard))))
  (fn-nov-lines-for-numbers-cat
   group (fn-scat-range-keep group (fn-cnx-range-aux group k hi v fn-cat) fn-cat)
   v fn-arena fn-cat))

