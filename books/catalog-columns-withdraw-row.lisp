; Withdrawal changes resident words and their escape values without a row decode.
(in-package "ACL2")
(include-book "catalog-columns-guards")
(include-book "catalog-columns-flags-native-type")
(local (include-book "ihs/logops-lemmas" :dir :system))

(defun fn-lbc-withdrawal-escape-cell (version by cell)
 (declare (xargs :guard (and (natp version) (natp by) (alistp cell))))
 (append (fn-lbc-sparse-u64 '(:withdrawal-at :withdrawal-by) (list version by))
  (remove-assoc-equal :withdrawal-at (remove-assoc-equal :withdrawal-by cell))))

(local (defthm fn-lbcwd-set-preserves-count
 (implies (and (natp i) (< i (len rows)))
  (equal (len (adt-set-a field i value rows)) (len rows)))
 :hints (("Goal" :in-theory (enable adt-set-a)))))
(local (defthm fn-lbcwd-nfix-u64
 (implies (unsigned-byte-p 64 flags) (equal (nfix flags) flags))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(nfix unsigned-byte-p integer-range-p))))))
(local (defthm fn-lbcwd-flags-fit
 (implies (unsigned-byte-p 64 flags)
  (unsigned-byte-p 64 (logior (nfix flags) 4 (if escaped 8 0))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lbcwd-nfix-u64 unsigned-byte-p-logior
    (:executable-counterpart unsigned-byte-p) (:executable-counterpart integerp)))))))

(defun fn-lbc-set-withdrawal (i version by fn-lbc)
 (declare (xargs :stobjs fn-lbc
  :guard (and (natp i) (< i (fn-lbc-count fn-lbc)) (natp version) (natp by)
              (alistp (fn-lbc-escape-store-get i fn-lbc)))
  :verify-guards nil))
 (let* ((cell (fn-lbc-withdrawal-escape-cell version by (fn-lbc-escape-store-get i fn-lbc)))
        (flags (logior (nfix (fn-lbc-word :flags i fn-lbc)) 4
                (if (and (unsigned-byte-p 64 version) (unsigned-byte-p 64 by)) 0 8)))
        (fn-lbc
         (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
          (fn-lbc-rowwords)
          (let* ((fn-lbc-rowwords (fn-lbc-rowwords-set-withdrawal-at i (fn-lbc-u64 version) fn-lbc-rowwords))
                 (fn-lbc-rowwords (fn-lbc-rowwords-set-withdrawal-by i (fn-lbc-u64 by) fn-lbc-rowwords)))
           (fn-lbc-rowwords-set-flags i flags fn-lbc-rowwords)) fn-lbc)))
  (fn-lbc-escape-store-put i cell fn-lbc)))

(verify-guards fn-lbc-set-withdrawal
 :hints (("Goal"
  :use ((:instance fn-lbc-flags-word-has-native-type)
        (:instance fn-lbcwd-flags-fit
         (flags (fn-lbc-word :flags i fn-lbc))
         (escaped (not (and (unsigned-byte-p 64 version) (unsigned-byte-p 64 by))))))
  :in-theory (disable fn-lbc-p fn-lbc-value fn-lbc-escape-store-get
   fn-lbc-escape-store-put fn-lbc-word floor mod logior binary-logior))))
