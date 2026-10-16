; Exact requested section lengths, with an actual one-extra-octet request fault.
(in-package "ACL2")
(include-book "lb-served-append-teeth")
(include-book "lb-reclaimed-read-cost-teeth")
(include-book "lb-verification-read-cost-teeth")
(defun fn-lbcst-one-extra-octet (i kind fn-lbc log)
 (declare (xargs :stobjs fn-lbc :guard (and (natp i) (< i (fn-lbc-count fn-lbc))
  (fn-lb-log-read-guardp log) (alistp (fn-lbc-escape-store-get i fn-lbc))) :verify-guards nil))
 (let* ((a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc))
        (seg (fn-loc-segment a b)) (off (fn-loc-offset a b)) (n (fn-loc-len a b))
        (raw (nfix (fn-lbc-directory-value i :raw-head-length fn-lbc)))
        (headp (equal kind :head))
        (start (if headp off (+ off raw 2)))
        (length (if headp (nfix (fn-lbc-value i :head-length fn-lbc)) (nfix (- (- n raw) 2)))))
  (fn-lb-log-model-read-range seg start (+ 1 length) log)))
(def-cost fn-lbcst-one-extra-octet
 :unaccounted (fn-lbc-value fn-lbc-directory-value fn-lb-log-model-read-range)
 :calls ((range-bytes (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets) :argument 2)))
(local (defthm fn-lbcst-row-corr-section-ok-by-definition
 (implies (fn-lbc-row-corr i row pm cols log)
  (and (equal (fn-lbc-directory-value i :head-ok cols)
              (equal (car (fn-nntp-section-of-bytes (fn-lb-log-payload row log) :head)) :ok))
       (equal (fn-lbc-directory-value i :body-ok cols)
              (equal (car (fn-nntp-section-of-bytes (fn-lb-log-payload row log) :body)) :ok))))
 :hints (("Goal" :in-theory '(fn-lbc-row-corr)))))
(defthm fn-lbcst-head-and-body-present
 (and (fn-lbc-directory-value 0 :head-ok (fn-lbcc-test-one-state))
      (fn-lbc-directory-value 0 :body-ok (fn-lbcc-test-one-state)))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-fixture-served-invariant fn-lbsa-fixture-domains fn-lbcc-test-head-positive
  (:instance fn-lbc-corresponding-row-at-index (i 0) (fn-lbc (fn-lbcc-test-one-state))
   (rows (list (fn-lbcc-test-decided-row))) (log (fn-lbsa-log)))
  (:instance fn-lbcst-row-corr-section-ok-by-definition (i 0) (row (fn-lbcc-test-decided-row))
   (pm (fn-lbc-value 0 :prefix-max (fn-lbcc-test-one-state))) (cols (fn-lbcc-test-one-state)) (log (fn-lbsa-log))))
  :in-theory (union-theories (theory 'ground-zero)
   (union-theories '(fn-lb-served-log-invp fn-cat$ap fn-held-listp-implies-cat-rowsp nth)
    (executable-counterpart-theory :here))))))

; These typed state controls change the branch facts omitted by a removal witness.
(defun fn-lbcst-reclaimed-word (fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (< 0 (fn-lbc-count fn-lbc)) :verify-guards nil))
 (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc))) (fn-lbc-rowwords)
  (fn-lbc-rowwords-set-flags 0 32 fn-lbc-rowwords) fn-lbc))
(defun fn-lbcst-clear-section-ok (field fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (and (member-eq field '(:head-ok :body-ok))
  (alistp (fn-lbc-escape-store-get 0 fn-lbc))) :verify-guards nil))
 (fn-lbc-escape-store-put 0 (cons (cons field nil) (fn-lbc-escape-store-get 0 fn-lbc)) fn-lbc))
(defun-nx fn-lbcst-reclaimed-columns () (fn-lbcst-reclaimed-word (fn-lbcc-test-one-state)))
(defun-nx fn-lbcst-head-refused-columns () (fn-lbcst-clear-section-ok :head-ok (fn-lbcc-test-one-state)))
(defun-nx fn-lbcst-body-refused-columns () (fn-lbcst-clear-section-ok :body-ok (fn-lbcc-test-one-state)))

(local (defthm fn-lbcst-reclaimed-flag-by-definition
 (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* (fn-lbcst-reclaimed-word cols))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcst-reclaimed-word fn-lbc-flag fn-lbc-word-flags-by-definition
     fn-lbc-row-store update-fn-lbc-row-store fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-get-flags-is-nth adt-set-a fn-dm-nth-update-nth
     nth update-nth len nfix natp logbitp))))))
(local (defthm fn-lbcst-locators-are-words-by-definition
 (implies (and (natp i) (< i (fn-lbc-count cols)))
  (and (equal (fn-lbc-loc0 i cols) (fn-lbc-word :loc0 i cols))
       (equal (fn-lbc-loc1 i cols) (fn-lbc-word :loc1 i cols))))
 :hints (("Goal" :in-theory '(fn-lbc-loc0 fn-lbc-loc1 fn-lbc-word fn-lbc-count)))))
(local (defthm fn-lbcst-escape-of-row-store-update
 (equal (fn-lbc-escape-store-get i (update-fn-lbc-row-store value cols)) (fn-lbc-escape-store-get i cols))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-escape-store-get update-fn-lbc-row-store fn-dm-nth-update-nth))))))
(local (defthm fn-lbcst-directory-of-row-store-update
 (equal (fn-lbc-directory-field field i (update-fn-lbc-row-store value cols)) (fn-lbc-directory-field field i cols))
 :hints (("Goal" :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
  '(fn-lbc-directory-field fn-lbc-directory-store update-fn-lbc-row-store fn-dm-nth-update-nth)) '((tau-system)))))))
(local (defthm fn-lbcst-len-update-zero
 (implies (consp xs) (equal (len (update-nth 0 value xs)) (len xs)))
 :hints (("Goal" :do-not-induct t :expand ((len xs) (update-nth 0 value xs))
  :in-theory (union-theories (theory 'ground-zero) '(update-nth len zp nfix))))))
(local (defthm fn-lbcst-reclaimed-retains-count
 (implies (< 0 (fn-lbc-count cols)) (equal (fn-lbc-count (update-fn-lbc-row-store (fn-lbc-rowwords-set-flags 0 32 (fn-lbc-row-store cols)) cols)) (fn-lbc-count cols)))
 :hints (("Goal" :cases ((consp (fn-lbc-row-store cols))) :do-not-induct t
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcst-reclaimed-word fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbcst-len-update-zero len))))))
(local (defthm fn-lbcst-reclaimed-retains-section-columns
 (implies (< 0 (fn-lbc-count cols))
  (and (equal (fn-lbc-loc0 0 (fn-lbcst-reclaimed-word cols)) (fn-lbc-loc0 0 cols))
       (equal (fn-lbc-loc1 0 (fn-lbcst-reclaimed-word cols)) (fn-lbc-loc1 0 cols))
       (equal (fn-lbc-value 0 :head-length (fn-lbcst-reclaimed-word cols)) (fn-lbc-value 0 :head-length cols))
       (equal (fn-lbc-directory-value 0 :raw-head-length (fn-lbcst-reclaimed-word cols)) (fn-lbc-directory-value 0 :raw-head-length cols))
       (equal (fn-lbc-directory-value 0 :head-ok (fn-lbcst-reclaimed-word cols)) (fn-lbc-directory-value 0 :head-ok cols))
       (equal (fn-lbc-directory-value 0 :body-ok (fn-lbcst-reclaimed-word cols)) (fn-lbc-directory-value 0 :body-ok cols))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcst-reclaimed-word fn-lbcst-reclaimed-retains-count fn-lbcst-locators-are-words-by-definition fn-lbc-value fn-lbc-directory-value
     fn-lbc-escape fn-lbcst-escape-of-row-store-update fn-lbcst-directory-of-row-store-update
     fn-lbc-word-loc0-of-in-bounds-set-flags fn-lbc-word-loc1-of-in-bounds-set-flags
     fn-lbc-word-head-length-of-in-bounds-set-flags))))))

(local (defthm fn-lbcst-refused-retains-other-columns
 (implies (member-eq field '(:head-ok :body-ok))
  (and (equal (fn-lbc-directory-value 0 field (fn-lbcst-clear-section-ok field cols)) nil)
       (equal (fn-lbc-loc0 0 (fn-lbcst-clear-section-ok field cols)) (fn-lbc-loc0 0 cols))
       (equal (fn-lbc-loc1 0 (fn-lbcst-clear-section-ok field cols)) (fn-lbc-loc1 0 cols))
       (equal (fn-lbc-value 0 :head-length (fn-lbcst-clear-section-ok field cols)) (fn-lbc-value 0 :head-length cols))
       (equal (fn-lbc-directory-value 0 :raw-head-length (fn-lbcst-clear-section-ok field cols)) (fn-lbc-directory-value 0 :raw-head-length cols))
       (equal (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* (fn-lbcst-clear-section-ok field cols)) (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* cols))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcst-clear-section-ok fn-lbc-loc0 fn-lbc-loc1 fn-lbc-value fn-lbc-directory-value fn-lbc-flag
     fn-lbc-escape fn-lbc-escape-store-get-of-put fn-lbc-word fn-lbc-row-store
     fn-lbc-directory-field fn-lbc-directory-store fn-lbc-escape-store-put fn-lbc-escape-store-get
     fn-dm-nth-update-nth assoc-eq hons-assoc-equal member-equal))))))

; BEGIN exact section-length teeth
(local (defthm fn-lbcst-head-mutant-request-amount
 (equal (fn-lbcst-one-extra-octet-range-bytes i :head fn-lbc-v log) (+ 1 (nfix (fn-lbc-value i :head-length fn-lbc-v))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbcst-one-extra-octet-range-bytes nfix natp))))))
(defthm fn-lbcst-head-whole-positive
 (and (not (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* (fn-lbcc-test-one-state))) (fn-lbc-directory-value 0 :head-ok (fn-lbcc-test-one-state)) (equal (fn-lbc-stored-range-range-bytes 0 :head (fn-lbcc-test-one-state) (fn-lbzc-log)) (nfix (fn-lbc-value 0 :head-length (fn-lbcc-test-one-state))))) :rule-classes nil
 :hints (("Goal" :use (fn-lbcc-test-head-positive (:instance fn-lbc-head-exact-request-length (i 0) (fn-lbc-v (fn-lbcc-test-one-state)) (log (fn-lbzc-log))))
  :in-theory (theory 'ground-zero))))
(defthm fn-lbcst-head-fault-whole-positive
 (and (not (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* (fn-lbcc-test-one-state))) (fn-lbc-directory-value 0 :head-ok (fn-lbcc-test-one-state)) (equal (fn-lbc-stored-range-range-bytes 0 :head (fn-lbcc-test-one-state) (fn-lbzc-log)) (nfix (fn-lbc-value 0 :head-length (fn-lbcc-test-one-state)))) (not (equal (fn-lbcst-one-extra-octet-range-bytes 0 :head (fn-lbcc-test-one-state) (fn-lbzc-log)) (nfix (fn-lbc-value 0 :head-length (fn-lbcc-test-one-state)))))) :rule-classes nil
 :hints (("Goal" :use fn-lbcst-head-whole-positive
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbcst-head-mutant-request-amount)))))
(defthm fn-lbcst-head-remove-0-whole-positive
 (and (fn-lbc-directory-value 0 :head-ok (fn-lbcst-reclaimed-columns)) (not (not (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* (fn-lbcst-reclaimed-columns)))) (not (equal (fn-lbc-stored-range-range-bytes 0 :head (fn-lbcst-reclaimed-columns) (fn-lbzc-log)) (nfix (fn-lbc-value 0 :head-length (fn-lbcst-reclaimed-columns)))))) :rule-classes nil
 :hints (("Goal" :use fn-lbcc-test-head-positive
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcst-reclaimed-columns fn-lbcst-head-refused-columns fn-lbcst-body-refused-columns
     fn-lbcst-reclaimed-flag-by-definition fn-lbcst-reclaimed-retains-section-columns
     fn-lbcst-refused-retains-other-columns fn-lbc-stored-range-range-bytes nfix natp)))))
(defthm fn-lbcst-head-remove-1-whole-positive
 (and (not (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* (fn-lbcst-head-refused-columns))) (not (fn-lbc-directory-value 0 :head-ok (fn-lbcst-head-refused-columns))) (not (equal (fn-lbc-stored-range-range-bytes 0 :head (fn-lbcst-head-refused-columns) (fn-lbzc-log)) (nfix (fn-lbc-value 0 :head-length (fn-lbcst-head-refused-columns)))))) :rule-classes nil
 :hints (("Goal" :use fn-lbcc-test-head-positive
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcst-reclaimed-columns fn-lbcst-head-refused-columns fn-lbcst-body-refused-columns
     fn-lbcst-reclaimed-flag-by-definition fn-lbcst-reclaimed-retains-section-columns
     fn-lbcst-refused-retains-other-columns fn-lbc-stored-range-range-bytes nfix natp)))))
(defteeth fn-lbc-head-exact-request-length
 :claim (((regular (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc-v))) (section-ok (fn-lbc-directory-value i :head-ok fn-lbc-v))) (equal (fn-lbc-stored-range-range-bytes i :head fn-lbc-v log) (nfix (fn-lbc-value i :head-length fn-lbc-v))))
 :subject fn-lbc-stored-range :witness ((i 0) (fn-lbc-v (fn-lbcc-test-one-state)) (log (fn-lbzc-log))) :witness-lemma fn-lbcst-head-whole-positive
 :breaks ((regular ((i 0) (fn-lbc-v (fn-lbcst-reclaimed-columns)) (log (fn-lbzc-log))) :lemma fn-lbcst-head-remove-0-whole-positive)
          (section-ok ((i 0) (fn-lbc-v (fn-lbcst-head-refused-columns)) (log (fn-lbzc-log))) :lemma fn-lbcst-head-remove-1-whole-positive))
 :mutations ((one-extra-octet (:conclusion (equal (fn-lbcst-one-extra-octet-range-bytes i :head fn-lbc-v log) (nfix (fn-lbc-value i :head-length fn-lbc-v)))) ((i 0) (fn-lbc-v (fn-lbcc-test-one-state)) (log (fn-lbzc-log)))
  :fault "The actual range request includes one octet beyond the selected section" :lemma fn-lbcst-head-fault-whole-positive)))
(local (defthm fn-lbcst-body-mutant-request-amount
 (equal (fn-lbcst-one-extra-octet-range-bytes i :body fn-lbc-v log) (+ 1 (nfix (- (- (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (nfix (fn-lbc-directory-value i :raw-head-length fn-lbc-v))) 2))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbcst-one-extra-octet-range-bytes nfix natp))))))
(defthm fn-lbcst-body-whole-positive
 (and (not (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* (fn-lbcc-test-one-state))) (fn-lbc-directory-value 0 :body-ok (fn-lbcc-test-one-state)) (equal (fn-lbc-stored-range-range-bytes 0 :body (fn-lbcc-test-one-state) (fn-lbzc-log)) (nfix (- (- (fn-loc-len (fn-lbc-loc0 0 (fn-lbcc-test-one-state)) (fn-lbc-loc1 0 (fn-lbcc-test-one-state))) (nfix (fn-lbc-directory-value 0 :raw-head-length (fn-lbcc-test-one-state)))) 2)))) :rule-classes nil
 :hints (("Goal" :use (fn-lbcc-test-head-positive (:instance fn-lbc-body-exact-request-length (i 0) (fn-lbc-v (fn-lbcc-test-one-state)) (log (fn-lbzc-log))))
  :in-theory (theory 'ground-zero))))
(defthm fn-lbcst-body-fault-whole-positive
 (and (not (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* (fn-lbcc-test-one-state))) (fn-lbc-directory-value 0 :body-ok (fn-lbcc-test-one-state)) (equal (fn-lbc-stored-range-range-bytes 0 :body (fn-lbcc-test-one-state) (fn-lbzc-log)) (nfix (- (- (fn-loc-len (fn-lbc-loc0 0 (fn-lbcc-test-one-state)) (fn-lbc-loc1 0 (fn-lbcc-test-one-state))) (nfix (fn-lbc-directory-value 0 :raw-head-length (fn-lbcc-test-one-state)))) 2))) (not (equal (fn-lbcst-one-extra-octet-range-bytes 0 :body (fn-lbcc-test-one-state) (fn-lbzc-log)) (nfix (- (- (fn-loc-len (fn-lbc-loc0 0 (fn-lbcc-test-one-state)) (fn-lbc-loc1 0 (fn-lbcc-test-one-state))) (nfix (fn-lbc-directory-value 0 :raw-head-length (fn-lbcc-test-one-state)))) 2))))) :rule-classes nil
 :hints (("Goal" :use fn-lbcst-body-whole-positive
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbcst-body-mutant-request-amount)))))
(defthm fn-lbcst-body-remove-0-whole-positive
 (and (fn-lbc-directory-value 0 :body-ok (fn-lbcst-reclaimed-columns)) (not (not (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* (fn-lbcst-reclaimed-columns)))) (not (equal (fn-lbc-stored-range-range-bytes 0 :body (fn-lbcst-reclaimed-columns) (fn-lbzc-log)) (nfix (- (- (fn-loc-len (fn-lbc-loc0 0 (fn-lbcst-reclaimed-columns)) (fn-lbc-loc1 0 (fn-lbcst-reclaimed-columns))) (nfix (fn-lbc-directory-value 0 :raw-head-length (fn-lbcst-reclaimed-columns)))) 2))))) :rule-classes nil
 :hints (("Goal" :use fn-lbcc-test-head-positive
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcst-reclaimed-columns fn-lbcst-head-refused-columns fn-lbcst-body-refused-columns
     fn-lbcst-reclaimed-flag-by-definition fn-lbcst-reclaimed-retains-section-columns
     fn-lbcst-refused-retains-other-columns fn-lbc-stored-range-range-bytes nfix natp)))))
(defthm fn-lbcst-body-remove-1-whole-positive
 (and (not (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* (fn-lbcst-body-refused-columns))) (not (fn-lbc-directory-value 0 :body-ok (fn-lbcst-body-refused-columns))) (not (equal (fn-lbc-stored-range-range-bytes 0 :body (fn-lbcst-body-refused-columns) (fn-lbzc-log)) (nfix (- (- (fn-loc-len (fn-lbc-loc0 0 (fn-lbcst-body-refused-columns)) (fn-lbc-loc1 0 (fn-lbcst-body-refused-columns))) (nfix (fn-lbc-directory-value 0 :raw-head-length (fn-lbcst-body-refused-columns)))) 2))))) :rule-classes nil
 :hints (("Goal" :use fn-lbcc-test-head-positive
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcst-reclaimed-columns fn-lbcst-head-refused-columns fn-lbcst-body-refused-columns
     fn-lbcst-reclaimed-flag-by-definition fn-lbcst-reclaimed-retains-section-columns
     fn-lbcst-refused-retains-other-columns fn-lbc-stored-range-range-bytes nfix natp)))))
(defteeth fn-lbc-body-exact-request-length
 :claim (((regular (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc-v))) (section-ok (fn-lbc-directory-value i :body-ok fn-lbc-v))) (equal (fn-lbc-stored-range-range-bytes i :body fn-lbc-v log) (nfix (- (- (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (nfix (fn-lbc-directory-value i :raw-head-length fn-lbc-v))) 2))))
 :subject fn-lbc-stored-range :witness ((i 0) (fn-lbc-v (fn-lbcc-test-one-state)) (log (fn-lbzc-log))) :witness-lemma fn-lbcst-body-whole-positive
 :breaks ((regular ((i 0) (fn-lbc-v (fn-lbcst-reclaimed-columns)) (log (fn-lbzc-log))) :lemma fn-lbcst-body-remove-0-whole-positive)
          (section-ok ((i 0) (fn-lbc-v (fn-lbcst-body-refused-columns)) (log (fn-lbzc-log))) :lemma fn-lbcst-body-remove-1-whole-positive))
 :mutations ((one-extra-octet (:conclusion (equal (fn-lbcst-one-extra-octet-range-bytes i :body fn-lbc-v log) (nfix (- (- (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (nfix (fn-lbc-directory-value i :raw-head-length fn-lbc-v))) 2)))) ((i 0) (fn-lbc-v (fn-lbcc-test-one-state)) (log (fn-lbzc-log)))
  :fault "The actual range request includes one octet beyond the selected section" :lemma fn-lbcst-body-fault-whole-positive)))

(defun fn-lbcst-native-section-controls ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (ok fn-lbc)
   (let* ((row (fn-lbcc-test-decided-row)) (log (fn-lbzc-log))
          (fn-lbc (fn-lbc-open-rebuild (list row) log fn-lbc))
          (ranges (and (equal (len (fn-lbc-stored-range 0 :head fn-lbc log)) 12)
                       (equal (len (fn-lbc-stored-range 0 :body fn-lbc log)) 3)
                       (equal (len (fn-lbcst-one-extra-octet 0 :head fn-lbc log)) 13)
                       (equal (len (fn-lbcst-one-extra-octet 0 :body fn-lbc log)) 4)))
          (fn-lbc (fn-lbcst-reclaimed-word fn-lbc))
          (reclaimed (and (fn-lbc-p fn-lbc) (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* fn-lbc)
                          (fn-lbc-directory-value 0 :head-ok fn-lbc) (fn-lbc-directory-value 0 :body-ok fn-lbc)))
          (fn-lbc (fn-lbc-open-rebuild (list row) log fn-lbc))
          (fn-lbc (fn-lbcst-clear-section-ok :head-ok fn-lbc))
          (head (and (fn-lbc-p fn-lbc) (not (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* fn-lbc))
                     (not (fn-lbc-directory-value 0 :head-ok fn-lbc))
                     (equal (fn-lbc-value 0 :head-length fn-lbc) 12)
                     (equal (fn-lbc-stored-range 0 :head fn-lbc log) nil)))
          (fn-lbc (fn-lbc-open-rebuild (list row) log fn-lbc))
          (fn-lbc (fn-lbcst-clear-section-ok :body-ok fn-lbc)))
    (mv (and ranges reclaimed head (fn-lbc-p fn-lbc)
             (not (fn-lbc-flag 0 *fn-lbc-reclaimed-bit* fn-lbc))
             (not (fn-lbc-directory-value 0 :body-ok fn-lbc))
             (equal (fn-lbc-stored-range 0 :body fn-lbc log) nil)) fn-lbc)) ok)))
(with-guard-checking-event t (assert-event (fn-lbcst-native-section-controls)))
