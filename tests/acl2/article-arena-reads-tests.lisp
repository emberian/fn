; The prefix theorem's real-arena positive and dropped-octet teeth.
(in-package "ACL2")
(include-book "../../books/article-arena-reads")
(include-book "must-fail-checked")

(defun aart-prefix-run (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((h (fn-arena-count fn-arena))
         (fn-arena (fn-arena-seal-list '(0 70 78 45 82 67 76 50 65 66) fn-arena))
         (bad (fn-arena-count fn-arena))
         (fn-arena (fn-arena-seal-list '(0 70 78 45 82 67 76 51 65 66) fn-arena))
         (prefix *fn-rcl-magic*)
         (mutant '(0 70 78 45 82 67 76)))
    (mv (list (and (natp 0)
                   (fn-nntp-arena-prefixp-span prefix h 0 fn-arena)
                   (equal (fn-nntp-arena-prefixp-span prefix h 0 fn-arena)
                          (fn-nntp-arena-prefixp-byte prefix h 0 fn-arena)))
              (fn-nntp-arena-prefixp-span prefix bad 0 fn-arena)
              (fn-nntp-arena-prefixp-span mutant bad 0 fn-arena)
              (fn-nntp-arena-prefixp-span prefix h 9 fn-arena)
              (fn-nntp-arena-prefixp-span nil h 99 fn-arena))
        fn-arena)))

(defun aart-prefix-check ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena) (aart-prefix-run fn-arena) r)))

(assert-event (equal (aart-prefix-check) '(t nil t nil t)))
(must-fail-checked
 (assert-event (equal (cadr (aart-prefix-check)) (caddr (aart-prefix-check)))))
