; Actual binary search/tail workers and duplicate-execution faults.
(in-package "ACL2")
(include-book "../../books/catalog-columns-newnews-cost")
(include-book "lb-column-read-cost-teeth")
(defun fn-lbcnt-zero () (declare (xargs :guard t)) 0)
(defun fn-lbcnt-one () (declare (xargs :guard t)) 1)
(defun fn-lbcnt-double-first-reaching (threshold lo hi fn-lbc)
 (declare (xargs :stobjs fn-lbc :verify-guards nil))
 (list (fn-lbc-first-reaching threshold lo hi fn-lbc) (fn-lbc-first-reaching threshold lo hi fn-lbc)))
(def-cost fn-lbcnt-double-first-reaching
 :unaccounted (fn-lbc-value)
 :calls ((prefix-reads (fn-lbc-value) :stop-at (fn-lbc-newnews-tail))))
(defun fn-lbcnt-double-newnews-tail (groups threshold v lo hi fn-lbc)
 (declare (xargs :stobjs fn-lbc :verify-guards nil))
 (list (fn-lbc-newnews-tail groups threshold v lo hi fn-lbc) (fn-lbc-newnews-tail groups threshold v lo hi fn-lbc)))
(def-cost fn-lbcnt-double-newnews-tail
 :unaccounted (fn-lbc-visiblep fn-lbc-flag fn-lbc-msgid fn-lbc-numbers fn-lbc-value fn-lbc-newnews-candidatep fn-nntp-article-idp fn-nntp-string-octets fn-ng-less-equal)
 :calls ((candidate-reads (fn-lbc-visiblep) :stop-at (fn-lbc-first-reaching))))
(defun fn-lbcnt-double-newnews-range (groups threshold v horizon fn-lbc)
 (declare (xargs :stobjs fn-lbc :verify-guards nil))
 (list (fn-lbc-newnews-range groups threshold v horizon fn-lbc) (fn-lbc-newnews-range groups threshold v horizon fn-lbc)))
(def-cost fn-lbcnt-double-newnews-range
 :unaccounted (fn-lbc-value fn-lbc-visiblep fn-lbc-flag fn-lbc-msgid fn-lbc-numbers fn-lbc-newnews-candidatep fn-nntp-article-idp fn-nntp-string-octets fn-ng-less-equal)
 :calls ((prefix-reads (fn-lbc-value) :stop-at (fn-lbc-newnews-tail)) (candidate-reads (fn-lbc-visiblep) :stop-at (fn-lbc-first-reaching))))
(defthm fn-lbc-first-reaching-logarithmic-prefix-reads-whole-positive
 (<= (fn-lbc-first-reaching-prefix-reads (fn-lbcnt-zero) (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcc-test-one-state))
  (fn-lbc-binary-depth (nfix (- (fn-lbcnt-one) (fn-lbcnt-zero)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   (set-difference-theories (fn-lbcc-test-theory (universal-theory :here))
    '(make-list-ac (:executable-counterpart make-list-ac)))))))
(defthm fn-lbc-first-reaching-logarithmic-prefix-reads-duplicate-fault
 (and (<= (fn-lbc-first-reaching-prefix-reads (fn-lbcnt-zero) (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcc-test-one-state))
  (fn-lbc-binary-depth (nfix (- (fn-lbcnt-one) (fn-lbcnt-zero))))) (not (<= (fn-lbcnt-double-first-reaching-prefix-reads (fn-lbcnt-zero) (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcc-test-one-state))
  (fn-lbc-binary-depth (nfix (- (fn-lbcnt-one) (fn-lbcnt-zero)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   (set-difference-theories (fn-lbcc-test-theory (universal-theory :here))
    '(make-list-ac (:executable-counterpart make-list-ac)))))))
(defteeth fn-lbc-first-reaching-logarithmic-prefix-reads
 :claim (nil (<= (fn-lbc-first-reaching-prefix-reads threshold lo hi fn-lbc-v)
  (fn-lbc-binary-depth (nfix (- hi lo))))) :subject fn-lbc-first-reaching
 :witness ((threshold (fn-lbcnt-zero)) (lo (fn-lbcnt-zero)) (hi (fn-lbcnt-one)) (fn-lbc-v (fn-lbcc-test-one-state)))
 :witness-lemma fn-lbc-first-reaching-logarithmic-prefix-reads-whole-positive :breaks ()
 :mutations ((duplicate-worker (:conclusion (<= (fn-lbcnt-double-first-reaching-prefix-reads threshold lo hi fn-lbc-v)
  (fn-lbc-binary-depth (nfix (- hi lo))))) ((threshold (fn-lbcnt-zero)) (lo (fn-lbcnt-zero)) (hi (fn-lbcnt-one)) (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "execute the actual search or tail worker twice" :lemma fn-lbc-first-reaching-logarithmic-prefix-reads-duplicate-fault)))
(defthm fn-lbc-newnews-tail-exact-candidate-reads-whole-positive
 (equal (fn-lbc-newnews-tail-candidate-reads '("fn.test") (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcc-test-one-state))
  (if (and (natp (fn-lbcnt-zero)) (natp (fn-lbcnt-one))) (nfix (- (fn-lbcnt-one) (fn-lbcnt-zero))) 0))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   (set-difference-theories (fn-lbcc-test-theory (universal-theory :here))
    '(make-list-ac (:executable-counterpart make-list-ac)))))))
(defthm fn-lbc-newnews-tail-exact-candidate-reads-duplicate-fault
 (and (equal (fn-lbc-newnews-tail-candidate-reads '("fn.test") (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcc-test-one-state))
  (if (and (natp (fn-lbcnt-zero)) (natp (fn-lbcnt-one))) (nfix (- (fn-lbcnt-one) (fn-lbcnt-zero))) 0)) (not (equal (fn-lbcnt-double-newnews-tail-candidate-reads '("fn.test") (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcc-test-one-state))
  (if (and (natp (fn-lbcnt-zero)) (natp (fn-lbcnt-one))) (nfix (- (fn-lbcnt-one) (fn-lbcnt-zero))) 0))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   (set-difference-theories (fn-lbcc-test-theory (universal-theory :here))
    '(make-list-ac (:executable-counterpart make-list-ac)))))))
(defteeth fn-lbc-newnews-tail-exact-candidate-reads
 :claim (nil (equal (fn-lbc-newnews-tail-candidate-reads groups threshold v lo hi fn-lbc-v)
  (if (and (natp lo) (natp hi)) (nfix (- hi lo)) 0))) :subject fn-lbc-newnews-tail
 :witness ((groups '("fn.test")) (threshold (fn-lbcnt-zero)) (v (fn-lbcnt-one)) (lo (fn-lbcnt-zero)) (hi (fn-lbcnt-one)) (fn-lbc-v (fn-lbcc-test-one-state)))
 :witness-lemma fn-lbc-newnews-tail-exact-candidate-reads-whole-positive :breaks ()
 :mutations ((duplicate-worker (:conclusion (equal (fn-lbcnt-double-newnews-tail-candidate-reads groups threshold v lo hi fn-lbc-v)
  (if (and (natp lo) (natp hi)) (nfix (- hi lo)) 0))) ((groups '("fn.test")) (threshold (fn-lbcnt-zero)) (v (fn-lbcnt-one)) (lo (fn-lbcnt-zero)) (hi (fn-lbcnt-one)) (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "execute the actual search or tail worker twice" :lemma fn-lbc-newnews-tail-exact-candidate-reads-duplicate-fault)))
(defthm fn-lbc-newnews-range-logarithmic-prefix-reads-whole-positive
 (<= (fn-lbc-newnews-range-prefix-reads '("fn.test") (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcnt-zero) (fn-lbcc-test-one-state))
     (fn-lbc-binary-depth (fn-lbcnt-one)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   (set-difference-theories (fn-lbcc-test-theory (universal-theory :here))
    '(make-list-ac (:executable-counterpart make-list-ac)))))))
(defthm fn-lbc-newnews-range-logarithmic-prefix-reads-duplicate-fault
 (and (<= (fn-lbc-newnews-range-prefix-reads '("fn.test") (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcnt-zero) (fn-lbcc-test-one-state))
     (fn-lbc-binary-depth (fn-lbcnt-one))) (not (<= (fn-lbcnt-double-newnews-range-prefix-reads '("fn.test") (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcnt-zero) (fn-lbcc-test-one-state))
     (fn-lbc-binary-depth (fn-lbcnt-one)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   (set-difference-theories (fn-lbcc-test-theory (universal-theory :here))
    '(make-list-ac (:executable-counterpart make-list-ac)))))))
(defteeth fn-lbc-newnews-range-logarithmic-prefix-reads
 :claim (nil (<= (fn-lbc-newnews-range-prefix-reads groups threshold v horizon fn-lbc-v)
     (fn-lbc-binary-depth v))) :subject fn-lbc-newnews-range
 :witness ((groups '("fn.test")) (threshold (fn-lbcnt-zero)) (v (fn-lbcnt-one)) (horizon (fn-lbcnt-zero)) (fn-lbc-v (fn-lbcc-test-one-state)))
 :witness-lemma fn-lbc-newnews-range-logarithmic-prefix-reads-whole-positive :breaks ()
 :mutations ((duplicate-worker (:conclusion (<= (fn-lbcnt-double-newnews-range-prefix-reads groups threshold v horizon fn-lbc-v)
     (fn-lbc-binary-depth v))) ((groups '("fn.test")) (threshold (fn-lbcnt-zero)) (v (fn-lbcnt-one)) (horizon (fn-lbcnt-zero)) (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "execute the actual search or tail worker twice" :lemma fn-lbc-newnews-range-logarithmic-prefix-reads-duplicate-fault)))
(defthm fn-lbc-newnews-range-exact-tail-reads-whole-positive
 (equal (fn-lbc-newnews-range-candidate-reads '("fn.test") (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcnt-zero) (fn-lbcc-test-one-state))
  (if (and (natp (fn-lbcnt-one)) (natp (fn-lbc-first-reaching (fn-lbcnt-zero) 0 (fn-lbcnt-one) (fn-lbcc-test-one-state))))
   (nfix (- (fn-lbcnt-one) (fn-lbc-first-reaching (fn-lbcnt-zero) 0 (fn-lbcnt-one) (fn-lbcc-test-one-state)))) 0))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   (set-difference-theories (fn-lbcc-test-theory (universal-theory :here))
    '(make-list-ac (:executable-counterpart make-list-ac)))))))
(defthm fn-lbc-newnews-range-exact-tail-reads-duplicate-fault
 (and (equal (fn-lbc-newnews-range-candidate-reads '("fn.test") (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcnt-zero) (fn-lbcc-test-one-state))
  (if (and (natp (fn-lbcnt-one)) (natp (fn-lbc-first-reaching (fn-lbcnt-zero) 0 (fn-lbcnt-one) (fn-lbcc-test-one-state))))
   (nfix (- (fn-lbcnt-one) (fn-lbc-first-reaching (fn-lbcnt-zero) 0 (fn-lbcnt-one) (fn-lbcc-test-one-state)))) 0)) (not (equal (fn-lbcnt-double-newnews-range-candidate-reads '("fn.test") (fn-lbcnt-zero) (fn-lbcnt-one) (fn-lbcnt-zero) (fn-lbcc-test-one-state))
  (if (and (natp (fn-lbcnt-one)) (natp (fn-lbc-first-reaching (fn-lbcnt-zero) 0 (fn-lbcnt-one) (fn-lbcc-test-one-state))))
   (nfix (- (fn-lbcnt-one) (fn-lbc-first-reaching (fn-lbcnt-zero) 0 (fn-lbcnt-one) (fn-lbcc-test-one-state)))) 0))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   (set-difference-theories (fn-lbcc-test-theory (universal-theory :here))
    '(make-list-ac (:executable-counterpart make-list-ac)))))))
(defteeth fn-lbc-newnews-range-exact-tail-reads
 :claim (nil (equal (fn-lbc-newnews-range-candidate-reads groups threshold v horizon fn-lbc-v)
  (if (and (natp v) (natp (fn-lbc-first-reaching threshold 0 v fn-lbc-v)))
   (nfix (- v (fn-lbc-first-reaching threshold 0 v fn-lbc-v))) 0))) :subject fn-lbc-newnews-range
 :witness ((groups '("fn.test")) (threshold (fn-lbcnt-zero)) (v (fn-lbcnt-one)) (horizon (fn-lbcnt-zero)) (fn-lbc-v (fn-lbcc-test-one-state)))
 :witness-lemma fn-lbc-newnews-range-exact-tail-reads-whole-positive :breaks ()
 :mutations ((duplicate-worker (:conclusion (equal (fn-lbcnt-double-newnews-range-candidate-reads groups threshold v horizon fn-lbc-v)
  (if (and (natp v) (natp (fn-lbc-first-reaching threshold 0 v fn-lbc-v)))
   (nfix (- v (fn-lbc-first-reaching threshold 0 v fn-lbc-v))) 0))) ((groups '("fn.test")) (threshold (fn-lbcnt-zero)) (v (fn-lbcnt-one)) (horizon (fn-lbcnt-zero)) (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "execute the actual search or tail worker twice" :lemma fn-lbc-newnews-range-exact-tail-reads-duplicate-fault)))
(defun fn-lbcnt-native-controls ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (ok fn-lbc)
   (let* ((row (fn-lbcc-test-decided-row))
          (log (fn-lb-log-model-append row *fn-lbr13-payload* 1 nil))
          (fn-lbc (fn-lbc-open-rebuild (list row) log fn-lbc))
          (one (list (fn-nntp-string-octets (fn-record-msgid row)))))
    (mv (and (equal (fn-lbc-first-reaching 0 0 1 fn-lbc) 0)
             (equal (fn-lbc-first-reaching 6000 0 1 fn-lbc) 1)
             (equal (fn-lbc-newnews-range '("fn.test") 0 1 0 fn-lbc) one)
             (equal (fn-lbc-newnews-range '("fn.test") 6000 1 0 fn-lbc) nil)
             (equal (fn-lbcnt-double-newnews-range '("fn.test") 0 1 0 fn-lbc) (list one one))) fn-lbc)) ok)))
(with-guard-checking-event t (assert-event (fn-lbcnt-native-controls)))
