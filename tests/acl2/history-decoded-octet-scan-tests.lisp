(in-package "ACL2")

(include-book "../../books/history-decoded-octet-scan")

(defun fn-hrcur-dos-test-run (fuel c pool)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (list :fuel c)
   (mv-let (v next) (fn-hrcur-dos-tick c)
     (cond ((eq v :continue) (fn-hrcur-dos-test-run (1- fuel) next pool))
           ((and (consp v) (eq (car v) :need-byte))
            (mv-let (sv sc) (fn-hrcur-dos-supply c (cadr v) (nth (cadr v) pool))
              (if (eq sv :continue) (fn-hrcur-dos-test-run (1- fuel) sc pool)
                (list sv sc))))
           (t (list v next))))))

(defthm fn-hrcur-dos-initial-positive
 (let* ((node '(:pair (:atom 65) (:span 6 0 0 3))) (pool '(66 67 68)) (c (fn-hrcur-dos-begin node :capture :lease)))
 (and (fn-hrcur-dos-domainp node pool)
      (fn-scc-octet-listp pool)
      (< (len (fn-hdc-abstract node pool)) *fn-hrcur-u64-bound*)
      (fn-hrcur-dos-invariantp c pool)))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-initial-remove-domain
 (let* ((node '(:atom (65))) (pool nil) (c (fn-hrcur-dos-begin node :capture :lease)))
 (and (not (fn-hrcur-dos-domainp node pool))
      (fn-scc-octet-listp pool)
      (< (len (fn-hdc-abstract node pool)) *fn-hrcur-u64-bound*)
      (not (fn-hrcur-dos-invariantp c pool))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-initial-remove-pool
 (let* ((node '(:atom 65)) (pool '(256)) (c (fn-hrcur-dos-begin node :capture :lease)))
 (and (fn-hrcur-dos-domainp node pool)
      (not (fn-scc-octet-listp pool))
      (< (len (fn-hdc-abstract node pool)) *fn-hrcur-u64-bound*)
      (not (fn-hrcur-dos-invariantp c pool))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-tick-invariant-positive
 (let* ((node '(:pair (:atom 65) (:span 6 0 0 3))) (pool '(66 67 68)) (c (fn-hrcur-dos-begin node :capture :lease)))
 (and (fn-hrcur-dos-invariantp c pool)
      (fn-hrcur-dos-invariantp (mv-nth 1 (fn-hrcur-dos-tick c)) pool)))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-tick-remove-invariant-corrupted-state
 (let* ((pool '(65)) (c '(:scan (:span 6 0 0 1) (:atom nil) 0 nil :capture :lease)))
 (and (not (fn-hrcur-dos-invariantp c pool))
      (not (fn-hrcur-dos-invariantp (mv-nth 1 (fn-hrcur-dos-tick c)) pool))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-terminal-positive
 (let* ((pool '(66 67 68)) (c (cadr (fn-hrcur-dos-test-run 30 (fn-hrcur-dos-begin '(:pair (:atom 65) (:span 6 0 0 3)) :capture :lease) pool))) (count 4))
 (and (fn-hrcur-dos-invariantp c pool)
      (equal (mv-nth 0 (fn-hrcur-dos-tick c)) (list :done :octets count))
      (and (fn-scc-octets-valuep (fn-hdc-abstract (fn-hrcur-field 1 c) pool)) (equal count (len (fn-hdc-abstract (fn-hrcur-field 1 c) pool))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-terminal-remove-count
 (let* ((pool '(66 67 68)) (c (cadr (fn-hrcur-dos-test-run 30 (fn-hrcur-dos-begin '(:pair (:atom 65) (:span 6 0 0 3)) :capture :lease) pool))) (count 5))
 (and (fn-hrcur-dos-invariantp c pool)
      (not (equal (mv-nth 0 (fn-hrcur-dos-tick c)) (list :done :octets count)))
      (not (and (fn-scc-octets-valuep (fn-hdc-abstract (fn-hrcur-field 1 c) pool)) (equal count (len (fn-hdc-abstract (fn-hrcur-field 1 c) pool)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-terminal-remove-invariant-corrupted-state
 (let* ((pool nil) (c '(:octets (:atom nil) (:atom nil) 1 nil :capture :lease)) (count 1))
 (and (not (fn-hrcur-dos-invariantp c pool))
      (equal (mv-nth 0 (fn-hrcur-dos-tick c)) (list :done :octets count))
      (not (and (fn-scc-octets-valuep (fn-hdc-abstract (fn-hrcur-field 1 c) pool)) (equal count (len (fn-hdc-abstract (fn-hrcur-field 1 c) pool)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-rejection-positive
 (let* ((pool nil) (c (cadr (fn-hrcur-dos-test-run 30 (fn-hrcur-dos-begin '(:pair (:atom 65) (:pair (:atom -1) (:atom nil))) :capture :lease) pool))))
 (and (fn-hrcur-dos-invariantp c pool)
      (equal (mv-nth 0 (fn-hrcur-dos-tick c)) '(:done :not-octets))
      (not (fn-scc-octets-valuep (fn-hdc-abstract (fn-hrcur-field 1 c) pool)))
      (equal (fn-hrcur-field 3 c) 1)))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-rejection-remove-invariant-corrupted-state
 (let* ((pool '(65)) (c '(:not-octets (:span 6 0 0 1) (:span 6 0 0 1) 0 nil :capture :lease)))
 (and (not (fn-hrcur-dos-invariantp c pool))
      (equal (mv-nth 0 (fn-hrcur-dos-tick c)) '(:done :not-octets))
      (not (not (fn-scc-octets-valuep (fn-hdc-abstract (fn-hrcur-field 1 c) pool))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-positive
 (let* ((pool '(78 73 76)) (c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0 (:check 1 0 3 0 :capture :lease) :capture :lease)) (position 0) (byte 78))
 (and (fn-hrcur-dos-invariantp c pool)
      (eq (fn-hrcur-field 0 c) :nil)
      (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
      (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
      (equal byte (nth position pool))
      (and (equal (mv-nth 0 (fn-hrcur-dos-supply c position byte)) :continue) (fn-hrcur-dos-invariantp (mv-nth 1 (fn-hrcur-dos-supply c position byte)) pool))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-remove-invariant-corrupted-state
 (let* ((pool '(78 73 76)) (c '(:nil (:atom nil) (:span 4 1 0 3) 0 (:check 1 0 3 0 :capture :lease) :capture :lease)) (position 0) (byte 78))
 (and (not (fn-hrcur-dos-invariantp c pool))
      (eq (fn-hrcur-field 0 c) :nil)
      (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
      (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
      (equal byte (nth position pool))
      (not (and (equal (mv-nth 0 (fn-hrcur-dos-supply c position byte)) :continue) (fn-hrcur-dos-invariantp (mv-nth 1 (fn-hrcur-dos-supply c position byte)) pool)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-remove-phase
 (let* ((pool '(78 73 76)) (c '(:scan (:span 4 1 0 3) (:span 4 1 0 3) 0 (:check 1 0 3 0 :capture :lease) :capture :lease)) (position 0) (byte 78))
 (and (fn-hrcur-dos-invariantp c pool)
      (not (eq (fn-hrcur-field 0 c) :nil))
      (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
      (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
      (equal byte (nth position pool))
      (not (and (equal (mv-nth 0 (fn-hrcur-dos-supply c position byte)) :continue) (fn-hrcur-dos-invariantp (mv-nth 1 (fn-hrcur-dos-supply c position byte)) pool)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-remove-child-phase
 (let* ((pool '(78 73 76)) (c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0 (:nil 1 0 3 3 :capture :lease) :capture :lease)) (position 3) (byte nil))
 (and (fn-hrcur-dos-invariantp c pool)
      (eq (fn-hrcur-field 0 c) :nil)
      (not (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check))
      (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
      (equal byte (nth position pool))
      (not (and (equal (mv-nth 0 (fn-hrcur-dos-supply c position byte)) :continue) (fn-hrcur-dos-invariantp (mv-nth 1 (fn-hrcur-dos-supply c position byte)) pool)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-remove-position
 (let* ((pool '(78 73 76)) (c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0 (:check 1 0 3 0 :capture :lease) :capture :lease)) (position 1) (byte 73))
 (and (fn-hrcur-dos-invariantp c pool)
      (eq (fn-hrcur-field 0 c) :nil)
      (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
      (not (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c)))))
      (equal byte (nth position pool))
      (not (and (equal (mv-nth 0 (fn-hrcur-dos-supply c position byte)) :continue) (fn-hrcur-dos-invariantp (mv-nth 1 (fn-hrcur-dos-supply c position byte)) pool)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-remove-source-byte
 (let* ((pool '(78 73 76)) (c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0 (:check 1 0 3 0 :capture :lease) :capture :lease)) (position 0) (byte 79))
 (and (fn-hrcur-dos-invariantp c pool)
      (eq (fn-hrcur-field 0 c) :nil)
      (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
      (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
      (not (equal byte (nth position pool)))
      (not (and (equal (mv-nth 0 (fn-hrcur-dos-supply c position byte)) :continue) (fn-hrcur-dos-invariantp (mv-nth 1 (fn-hrcur-dos-supply c position byte)) pool)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-tick-progress-positive
 (let* ((node '(:pair (:atom 65) (:span 6 0 0 3))) (c (fn-hrcur-dos-begin node :capture :lease)))
 (and (equal (mv-nth 0 (fn-hrcur-dos-tick c)) :continue)
      (< (fn-hrcur-dos-work (mv-nth 1 (fn-hrcur-dos-tick c))) (fn-hrcur-dos-work c))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-tick-progress-remove-continue
 (let* ((c '(:octets (:span 6 0 0 1) (:span 6 0 0 1) 1 nil :capture :lease)))
 (and (not (equal (mv-nth 0 (fn-hrcur-dos-tick c)) :continue))
      (not (< (fn-hrcur-dos-work (mv-nth 1 (fn-hrcur-dos-tick c))) (fn-hrcur-dos-work c)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-rejection-remove-verdict
 (let* ((pool '(66 67 68)) (c (cadr (fn-hrcur-dos-test-run 30 (fn-hrcur-dos-begin '(:pair (:atom 65) (:span 6 0 0 3)) :capture :lease) pool))))
 (and (fn-hrcur-dos-invariantp c pool)
      (not (equal (mv-nth 0 (fn-hrcur-dos-tick c)) '(:done :not-octets)))
      (not (not (fn-scc-octets-valuep (fn-hdc-abstract (fn-hrcur-field 1 c) pool))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-progress-positive
 (let* ((c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0 (:check 1 0 3 0 :capture :lease) :capture :lease)) (position 0) (byte 78))
 (and (fn-hrcur-dos-shapep c)
      (eq (fn-hrcur-field 0 c) :nil)
      (fn-hrcur-nil-shapep (fn-hrcur-field 4 c))
      (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
      (< (fn-hrcur-field 4 (fn-hrcur-field 4 c)) 3)
      (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
      (fn-scc-octetp byte)
      (< (fn-hrcur-dos-work (mv-nth 1 (fn-hrcur-dos-supply c position byte))) (fn-hrcur-dos-work c))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-progress-remove-shape-corrupted-state
 (let* ((c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0 (:check 1 0 3 0 :capture :lease) :capture :lease :extra)) (position 0) (byte 78))
 (and (not (fn-hrcur-dos-shapep c))
      (eq (fn-hrcur-field 0 c) :nil)
      (fn-hrcur-nil-shapep (fn-hrcur-field 4 c))
      (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
      (< (fn-hrcur-field 4 (fn-hrcur-field 4 c)) 3)
      (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
      (fn-scc-octetp byte)
      (not (< (fn-hrcur-dos-work (mv-nth 1 (fn-hrcur-dos-supply c position byte))) (fn-hrcur-dos-work c)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-progress-remove-phase
 (let* ((c '(:scan (:span 4 1 0 3) (:span 4 1 0 3) 0 (:check 1 0 3 0 :capture :lease) :capture :lease)) (position 0) (byte 78))
 (and (fn-hrcur-dos-shapep c)
      (not (eq (fn-hrcur-field 0 c) :nil))
      (fn-hrcur-nil-shapep (fn-hrcur-field 4 c))
      (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
      (< (fn-hrcur-field 4 (fn-hrcur-field 4 c)) 3)
      (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
      (fn-scc-octetp byte)
      (not (< (fn-hrcur-dos-work (mv-nth 1 (fn-hrcur-dos-supply c position byte))) (fn-hrcur-dos-work c)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-progress-remove-child-shape-corrupted-state
 (let* ((c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0 (:check 0 0 3 0 :capture :lease) :capture :lease)) (position 0) (byte 78))
 (and (fn-hrcur-dos-shapep c)
      (eq (fn-hrcur-field 0 c) :nil)
      (not (fn-hrcur-nil-shapep (fn-hrcur-field 4 c)))
      (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
      (< (fn-hrcur-field 4 (fn-hrcur-field 4 c)) 3)
      (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
      (fn-scc-octetp byte)
      (not (< (fn-hrcur-dos-work (mv-nth 1 (fn-hrcur-dos-supply c position byte))) (fn-hrcur-dos-work c)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-progress-remove-child-phase
 (let* ((c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0 (:not-nil 1 0 3 0 :capture :lease) :capture :lease)) (position 0) (byte 78))
 (and (fn-hrcur-dos-shapep c)
      (eq (fn-hrcur-field 0 c) :nil)
      (fn-hrcur-nil-shapep (fn-hrcur-field 4 c))
      (not (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check))
      (< (fn-hrcur-field 4 (fn-hrcur-field 4 c)) 3)
      (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
      (fn-scc-octetp byte)
      (not (< (fn-hrcur-dos-work (mv-nth 1 (fn-hrcur-dos-supply c position byte))) (fn-hrcur-dos-work c)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-progress-remove-index
 (let* ((c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0 (:check 1 0 3 3 :capture :lease) :capture :lease)) (position 3) (byte 78))
 (and (fn-hrcur-dos-shapep c)
      (eq (fn-hrcur-field 0 c) :nil)
      (fn-hrcur-nil-shapep (fn-hrcur-field 4 c))
      (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
      (not (< (fn-hrcur-field 4 (fn-hrcur-field 4 c)) 3))
      (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
      (fn-scc-octetp byte)
      (not (< (fn-hrcur-dos-work (mv-nth 1 (fn-hrcur-dos-supply c position byte))) (fn-hrcur-dos-work c)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-progress-remove-position
 (let* ((c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0 (:check 1 0 3 0 :capture :lease) :capture :lease)) (position 1) (byte 78))
 (and (fn-hrcur-dos-shapep c)
      (eq (fn-hrcur-field 0 c) :nil)
      (fn-hrcur-nil-shapep (fn-hrcur-field 4 c))
      (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
      (< (fn-hrcur-field 4 (fn-hrcur-field 4 c)) 3)
      (not (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c)))))
      (fn-scc-octetp byte)
      (not (< (fn-hrcur-dos-work (mv-nth 1 (fn-hrcur-dos-supply c position byte))) (fn-hrcur-dos-work c)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(defthm fn-hrcur-dos-supply-progress-remove-byte
 (let* ((c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0 (:check 1 0 3 0 :capture :lease) :capture :lease)) (position 0) (byte 256))
 (and (fn-hrcur-dos-shapep c)
      (eq (fn-hrcur-field 0 c) :nil)
      (fn-hrcur-nil-shapep (fn-hrcur-field 4 c))
      (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
      (< (fn-hrcur-field 4 (fn-hrcur-field 4 c)) 3)
      (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c)) (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
      (not (fn-scc-octetp byte))
      (not (< (fn-hrcur-dos-work (mv-nth 1 (fn-hrcur-dos-supply c position byte))) (fn-hrcur-dos-work c)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
 (enable fn-hrcur-dos-invariantp fn-hrcur-dos-domainp fn-hrcur-dos-value
         fn-hrcur-dos-prefixp fn-hrcur-dos-shapep fn-hrcur-dos-work
         fn-hrcur-nil-invariantp fn-hrcur-nil-model fn-hrcur-nil-work
         fn-hdc-abstract fn-scc-octet-listp fn-scc-octets-valuep))))

(assert-event
 (let ((c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0
                (:check 1 0 3 0 :capture :lease) :capture :lease)))
   (mv-let (v n) (fn-hrcur-dos-tick c)
     (mv-let (sv sc) (fn-hrcur-dos-supply c 0 78)
       (and (equal v '(:need-byte 0)) (equal n c) (eq sv :continue)
            (equal (fn-hrcur-field 5 n) :capture)
            (equal (fn-hrcur-field 6 n) :lease)
            (equal (fn-hrcur-field 5 sc) :capture)
            (equal (fn-hrcur-field 6 sc) :lease))))))

(assert-event
 (let ((c '(:nil (:span 4 1 0 3) (:span 4 1 0 3) 0
                (:nil 1 0 3 3 :capture :lease) :capture :lease)))
   (mv-let (v n) (fn-hrcur-dos-tick c)
     (and (not (eq (fn-hrcur-field 0 v) :need-byte)) (not (equal n c))))))
