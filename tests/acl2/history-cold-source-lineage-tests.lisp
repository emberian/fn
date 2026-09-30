(in-package "ACL2")
(include-book "../../books/history-cold-source-lineage")

; Reachable positive: actual numeric prefix, complete feed antecedent and conclusion.
(defthm fn-hdcl-test-feed-positive
  (let ((s (fn-hdc-model-run 2 (fn-hdc-begin 0 3 :epoch :lease) '(1 1 17)))) (and (fn-hdcl-source-statep s 0) (fn-scc-octetp 17) (fn-hdcl-source-statep (fn-hdc-feed 17 s) 0)))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool))) :in-theory
    (enable fn-hdcl-source-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep
      fn-hdcl-borrowed-statep fn-hdcl-numeric-statep fn-hdcl-number-budgetp
      fn-hdcl-scalar-stackp fn-hdcl-scalar-lineagep fn-hdcl-stack-weight
      fn-hdcl-payload-charge fn-hdc-node-in-poolp fn-hdc-stack-in-poolp
      fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-statep fn-hdc-numberp
      fn-hrsc-domainp fn-hrsc-codecp fn-scc-atomp fn-scc-nat-encodablep
      fn-scc-octetp fn-scc-octet-listp))))

; Corrupted-state removal: numeric accumulator already exceeds the codec bound.
(defthm fn-hdcl-test-feed-remove-source
  (let ((s (fn-hdc-state :digits 1 0 (list 1 *fn-hrsc-integer-bound* 1) 0 0 0 2 3 nil :epoch :lease))) (and (fn-scc-octetp 0) (not (fn-hdcl-source-statep s 0)) (not (fn-hdcl-source-statep (fn-hdc-feed 0 s) 0))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool))) :in-theory
    (enable fn-hdcl-source-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep
      fn-hdcl-borrowed-statep fn-hdcl-numeric-statep fn-hdcl-number-budgetp
      fn-hdcl-scalar-stackp fn-hdcl-scalar-lineagep fn-hdcl-stack-weight
      fn-hdcl-payload-charge fn-hdc-node-in-poolp fn-hdc-stack-in-poolp
      fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-statep fn-hdc-numberp
      fn-hrsc-domainp fn-hrsc-codecp fn-scc-atomp fn-scc-nat-encodablep
      fn-scc-octetp fn-scc-octet-listp))))

; Corrupted-state/argument mutation: carried potential valid, nonoctet supply exceeds it.
(defthm fn-hdcl-test-feed-remove-byte
  (let ((s (fn-hdc-state :digits 1 0 (list 1 (- *fn-hrsc-integer-bound* 256) 1) 0 0 0 2 3 nil :epoch :lease))) (and (fn-hdcl-source-statep s 0) (not (fn-scc-octetp 256)) (not (fn-hdcl-source-statep (fn-hdc-feed 256 s) 0))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool))) :in-theory
    (enable fn-hdcl-source-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep
      fn-hdcl-borrowed-statep fn-hdcl-numeric-statep fn-hdcl-number-budgetp
      fn-hdcl-scalar-stackp fn-hdcl-scalar-lineagep fn-hdcl-stack-weight
      fn-hdcl-payload-charge fn-hdc-node-in-poolp fn-hdc-stack-in-poolp
      fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-statep fn-hdc-numberp
      fn-hrsc-domainp fn-hrsc-codecp fn-scc-atomp fn-scc-nat-encodablep
      fn-scc-octetp fn-scc-octet-listp))))

; Reachable actual run: complete three-premise preservation boundary.
(defthm fn-hdcl-test-run-positive
  (let ((s (fn-hdc-model-run 2 (fn-hdc-begin 0 3 :epoch :lease) '(1 1 17))) (pool '(1 1 17))) (and (fn-hdcl-source-statep s 0) (fn-scc-octet-listp pool) (<= (nth 8 s) (len pool)) (fn-hdcl-source-statep (fn-hdc-model-run 1 s pool) 0)))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool))) :in-theory
    (enable fn-hdcl-source-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep
      fn-hdcl-borrowed-statep fn-hdcl-numeric-statep fn-hdcl-number-budgetp
      fn-hdcl-scalar-stackp fn-hdcl-scalar-lineagep fn-hdcl-stack-weight
      fn-hdcl-payload-charge fn-hdc-node-in-poolp fn-hdc-stack-in-poolp
      fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-statep fn-hdc-numberp
      fn-hrsc-domainp fn-hrsc-codecp fn-scc-atomp fn-scc-nat-encodablep
      fn-scc-octetp fn-scc-octet-listp))))

; Corrupted-state removal: both retained source-byte/range premises are checked.
(defthm fn-hdcl-test-run-remove-source
  (let ((s (fn-hdc-state :digits 1 0 (list 1 *fn-hrsc-integer-bound* 1) 0 0 0 2 3 nil :epoch :lease)) (pool '(1 1 0))) (and (fn-scc-octet-listp pool) (<= (nth 8 s) (len pool)) (not (fn-hdcl-source-statep s 0)) (not (fn-hdcl-source-statep (fn-hdc-model-run 1 s pool) 0))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool))) :in-theory
    (enable fn-hdcl-source-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep
      fn-hdcl-borrowed-statep fn-hdcl-numeric-statep fn-hdcl-number-budgetp
      fn-hdcl-scalar-stackp fn-hdcl-scalar-lineagep fn-hdcl-stack-weight
      fn-hdcl-payload-charge fn-hdc-node-in-poolp fn-hdc-stack-in-poolp
      fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-statep fn-hdc-numberp
      fn-hrsc-domainp fn-hrsc-codecp fn-scc-atomp fn-scc-nat-encodablep
      fn-scc-octetp fn-scc-octet-listp))))

; Argument mutation: valid prefix receives the actual bad scalar at current pool position.
(defthm fn-hdcl-test-run-remove-pool
  (let ((s (fn-hdc-model-run 2 (fn-hdc-begin 0 3 :epoch :lease) '(1 1 17))) (pool (list 1 1 *fn-hrsc-integer-bound*))) (and (fn-hdcl-source-statep s 0) (<= (nth 8 s) (len pool)) (not (fn-scc-octet-listp pool)) (not (fn-hdcl-source-statep (fn-hdc-model-run 1 s pool) 0))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool))) :in-theory
    (enable fn-hdcl-source-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep
      fn-hdcl-borrowed-statep fn-hdcl-numeric-statep fn-hdcl-number-budgetp
      fn-hdcl-scalar-stackp fn-hdcl-scalar-lineagep fn-hdcl-stack-weight
      fn-hdcl-payload-charge fn-hdc-node-in-poolp fn-hdc-stack-in-poolp
      fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-statep fn-hdc-numberp
      fn-hrsc-domainp fn-hrsc-codecp fn-scc-atomp fn-scc-nat-encodablep
      fn-scc-octetp fn-scc-octet-listp))))

; Argument mutation: missing package byte becomes NIL and destroys parser field invariant.
(defthm fn-hdcl-test-run-remove-range
  (let ((s (fn-hdc-feed 4 (fn-hdc-begin 0 3 :epoch :lease))) (pool '(4))) (and (fn-hdcl-source-statep s 0) (fn-scc-octet-listp pool) (not (<= (nth 8 s) (len pool))) (not (fn-hdcl-source-statep (fn-hdc-model-run 1 s pool) 0))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool))) :in-theory
    (enable fn-hdcl-source-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep
      fn-hdcl-borrowed-statep fn-hdcl-numeric-statep fn-hdcl-number-budgetp
      fn-hdcl-scalar-stackp fn-hdcl-scalar-lineagep fn-hdcl-stack-weight
      fn-hdcl-payload-charge fn-hdc-node-in-poolp fn-hdc-stack-in-poolp
      fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-statep fn-hdc-numberp
      fn-hrsc-domainp fn-hrsc-codecp fn-scc-atomp fn-scc-nat-encodablep
      fn-scc-octetp fn-scc-octet-listp))))

; Actual successful decoder domain: opaque.
(defthm fn-hdcl-test-result-opaque-bounded
  (let* ((pool '(6 1 1 17)) (offset 0) (count 4) (s (fn-hdc-model-run count (fn-hdc-begin offset count :epoch :lease) pool)) (r (fn-hdc-result s))) (and (fn-scc-octet-listp pool) (natp offset) (natp count) (< (+ offset count) *fn-hrcur-u64-bound*) (<= (+ offset count) (len pool)) (equal (car r) :ok) (fn-hdc-node-in-poolp (cadr r) (+ offset count)) (fn-hrcur-cold-domainp (cadr r) pool)))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool))) :use ((:instance fn-hdcl-current-successful-decoder-is-cold-codec-domain (pool '(6 1 1 17)) (offset 0) (count 4) (epoch :epoch) (lease :lease)) (:instance fn-hdcl-current-successful-decoder-retains-node-bounds (pool '(6 1 1 17)) (offset 0) (count 4) (epoch :epoch) (lease :lease)))
    :in-theory (enable fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-result fn-scc-octet-listp fn-scc-octetp))))

; Actual successful decoder domain: nonminimal.
(defthm fn-hdcl-test-result-nonminimal-bounded
  (let* ((pool '(6 2 1 0 17)) (offset 0) (count 5) (s (fn-hdc-model-run count (fn-hdc-begin offset count :epoch :lease) pool)) (r (fn-hdc-result s))) (and (fn-scc-octet-listp pool) (natp offset) (natp count) (< (+ offset count) *fn-hrcur-u64-bound*) (<= (+ offset count) (len pool)) (equal (car r) :ok) (fn-hdc-node-in-poolp (cadr r) (+ offset count)) (fn-hrcur-cold-domainp (cadr r) pool)))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool))) :use ((:instance fn-hdcl-current-successful-decoder-is-cold-codec-domain (pool '(6 2 1 0 17)) (offset 0) (count 5) (epoch :epoch) (lease :lease)) (:instance fn-hdcl-current-successful-decoder-retains-node-bounds (pool '(6 2 1 0 17)) (offset 0) (count 5) (epoch :epoch) (lease :lease)))
    :in-theory (enable fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-result fn-scc-octet-listp fn-scc-octetp))))

; Actual successful decoder domain: pair-collapse.
(defthm fn-hdcl-test-result-pair-collapse-bounded
  (let* ((pool '(1 1 17 0 5)) (offset 0) (count 5) (s (fn-hdc-model-run count (fn-hdc-begin offset count :epoch :lease) pool)) (r (fn-hdc-result s))) (and (fn-scc-octet-listp pool) (natp offset) (natp count) (< (+ offset count) *fn-hrcur-u64-bound*) (<= (+ offset count) (len pool)) (equal (car r) :ok) (fn-hdc-node-in-poolp (cadr r) (+ offset count)) (fn-hrcur-cold-domainp (cadr r) pool)))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool))) :use ((:instance fn-hdcl-current-successful-decoder-is-cold-codec-domain (pool '(1 1 17 0 5)) (offset 0) (count 5) (epoch :epoch) (lease :lease)) (:instance fn-hdcl-current-successful-decoder-retains-node-bounds (pool '(1 1 17 0 5)) (offset 0) (count 5) (epoch :epoch) (lease :lease)))
    :in-theory (enable fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-result fn-scc-octet-listp fn-scc-octetp))))

; Actual successful decoder domain: nil-alias.
(defthm fn-hdcl-test-result-nil-alias-bounded
  (let* ((pool '(4 1 1 3 78 73 76)) (offset 0) (count 7) (s (fn-hdc-model-run count (fn-hdc-begin offset count :epoch :lease) pool)) (r (fn-hdc-result s))) (and (fn-scc-octet-listp pool) (natp offset) (natp count) (< (+ offset count) *fn-hrcur-u64-bound*) (<= (+ offset count) (len pool)) (equal (car r) :ok) (fn-hdc-node-in-poolp (cadr r) (+ offset count)) (fn-hrcur-cold-domainp (cadr r) pool)))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool))) :use ((:instance fn-hdcl-current-successful-decoder-is-cold-codec-domain (pool '(4 1 1 3 78 73 76)) (offset 0) (count 7) (epoch :epoch) (lease :lease)) (:instance fn-hdcl-current-successful-decoder-retains-node-bounds (pool '(4 1 1 3 78 73 76)) (offset 0) (count 7) (epoch :epoch) (lease :lease)))
    :in-theory (enable fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-result fn-scc-octet-listp fn-scc-octetp))))

; Actual successful feed then terminating cold stream: no caller domain premise.
(defthm fn-hdcl-test-decoder-stream-opaque
  (let* ((pool '(6 1 1 17)) (offset 0) (count 4)
         (r (fn-hdc-result (fn-hdc-model-run count
               (fn-hdc-begin offset count :epoch :lease) pool))))
    (and (fn-scc-octet-listp pool) (natp offset)
         (< (+ offset count) *fn-hrcur-u64-bound*)
         (<= (+ offset count) (len pool)) (equal (car r) :ok)
         (equal (fn-hrcur-cold-oracle-run
                  (fn-hrcur-cold-begin (list :decoded (cadr r)) :capture :encoder-lease) pool)
                (fn-scc-encode (fn-hdc-abstract (cadr r) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (:instance fn-hdcl-current-decoder-cold-run-is-canonical-codec
      (pool '(6 1 1 17)) (offset 0) (count 4) (epoch :epoch) (lease :lease)
      (capture :capture) (encoder-lease :encoder-lease))
    :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
    :in-theory (e/d (fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move
                      fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-result
                      fn-scc-octet-listp fn-scc-octetp)
      (fn-hrcur-cold-oracle-run fn-hrcur-cold-begin fn-scc-encode fn-hdc-abstract)))))

; Actual successful feed then terminating cold stream: no caller domain premise.
(defthm fn-hdcl-test-decoder-stream-nil-alias
  (let* ((pool '(4 1 1 3 78 73 76)) (offset 0) (count 7)
         (r (fn-hdc-result (fn-hdc-model-run count
               (fn-hdc-begin offset count :epoch :lease) pool))))
    (and (fn-scc-octet-listp pool) (natp offset)
         (< (+ offset count) *fn-hrcur-u64-bound*)
         (<= (+ offset count) (len pool)) (equal (car r) :ok)
         (equal (fn-hrcur-cold-oracle-run
                  (fn-hrcur-cold-begin (list :decoded (cadr r)) :capture :encoder-lease) pool)
                (fn-scc-encode (fn-hdc-abstract (cadr r) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (:instance fn-hdcl-current-decoder-cold-run-is-canonical-codec
      (pool '(4 1 1 3 78 73 76)) (offset 0) (count 7) (epoch :epoch) (lease :lease)
      (capture :capture) (encoder-lease :encoder-lease))
    :expand ((:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
    :in-theory (e/d (fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move
                      fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-result
                      fn-scc-octet-listp fn-scc-octetp)
      (fn-hrcur-cold-oracle-run fn-hrcur-cold-begin fn-scc-encode fn-hdc-abstract)))))
