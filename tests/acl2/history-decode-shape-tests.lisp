(in-package "ACL2")
(include-book "../../books/history-decode-shape")

; Complete retained provider/feed premises and node-contract conclusion.
(defthm fn-hdc-node-contract-feed-positive
 (let* ((pool '(72 83 84 88 65))
        (s (fn-hdc-state :payload 4 0 '(0 0 1) 0 5 1 4 5 nil 9 17))
        (byte 65))
  (and (fn-hdc-node-contractp s pool) (fn-scc-octet-listp pool)
       (<= (nth 8 s) (len pool)) (fn-scc-octetp byte)
       (equal byte (nth (nth 7 s) pool))
       (fn-hdc-node-contractp (fn-hdc-feed byte s) pool)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hdc-node-contractp fn-hdc-coherent
                                   fn-hdc-state fn-hdc-statep fn-hdc-tag-prefixp
                                   fn-hdc-built-stackp fn-hdc-stack-in-poolp
                                   fn-hdc-tag-normal-stackp fn-hdc-abstract))))

; Hypothesis removal: a lying provider supplies B for immutable final A.
; All retained premises hold; cached recognition misses the real source tag.
(defthm fn-hdc-node-contract-source-hypothesis-removal
 (let* ((pool '(72 83 84 88 65))
        (s (fn-hdc-state :payload 4 0 '(0 0 1) 0 5 1 4 5 nil 9 17))
        (byte 66))
  (and (fn-hdc-node-contractp s pool) (fn-scc-octet-listp pool)
       (<= (nth 8 s) (len pool)) (fn-scc-octetp byte)
       (not (equal byte (nth (nth 7 s) pool)))
       (not (fn-hdc-node-contractp (fn-hdc-feed byte s) pool))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hdc-node-contractp fn-hdc-coherent
                                   fn-hdc-state fn-hdc-statep fn-hdc-tag-prefixp
                                   fn-hdc-built-stackp fn-hdc-stack-in-poolp
                                   fn-hdc-tag-normal-stackp fn-hdc-tag-normal-nodep
                                   fn-hdc-feed fn-hdc-feed-raw fn-hdc-move
                                   fn-hdc-payload-node fn-hdc-tag-byte fn-hdc-span
                                   fn-hdc-atom fn-hdc-abstract))))

; Positive extraction with every literal theorem premise.
(defthm fn-hdc-concrete-pair-extraction-positive
 (let* ((pool nil) (end 0)
        (node (fn-hdc-pair (fn-hdc-atom :hstxa) (fn-hdc-atom nil))))
  (and (fn-hdc-built-nodep node) (fn-hdc-node-in-poolp node end)
       (<= end (len pool)) (fn-scc-octet-listp pool)
       (consp (fn-hdc-abstract node pool))
       (not (fn-scc-octetp (car (fn-hdc-abstract node pool))))
       (equal (car node) :pair)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hdc-built-nodep fn-hdc-node-in-poolp
                                   fn-hdc-abstract fn-hdc-pair fn-hdc-atom))))

; Hypothesis removal: octet span denotes a cons but has no concrete pair.
(defthm fn-hdc-concrete-pair-nonoctet-hypothesis-removal
 (let* ((pool '(65)) (end 1) (node (fn-hdc-span 6 0 0 1)))
  (and (fn-hdc-built-nodep node) (fn-hdc-node-in-poolp node end)
       (<= end (len pool)) (fn-scc-octet-listp pool)
       (consp (fn-hdc-abstract node pool))
       (fn-scc-octetp (car (fn-hdc-abstract node pool)))
       (not (equal (car node) :pair))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hdc-built-nodep fn-hdc-node-in-poolp
                                   fn-hdc-abstract fn-hdc-span))))

; Result theorem is over the actual constant-depth public result extraction.
(defthm fn-hdc-result-contract-positive
 (let* ((pool '(4 0 1 5 72 83 84 88 65 0 5)) (offset 0) (count 11)
        (result (fn-hdc-result
                 (fn-hdc-model-run count (fn-hdc-begin offset count 9 17) pool))))
  (and (fn-scc-octet-listp pool) (natp offset) (natp count)
       (<= (+ offset count) (len pool)) (equal (car result) :ok)
       (fn-hdc-built-nodep (cadr result))
       (fn-hdc-node-in-poolp (cadr result) (+ offset count))
       (fn-hdc-tag-normal-nodep (cadr result) pool)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-hdc-current-decoder-result-node-contract
                         (pool '(4 0 1 5 72 83 84 88 65 0 5))
                         (offset 0) (count 11) (epoch 9) (lease 17)))
          :expand (( :free (s pool) (fn-hdc-model-run 0 s pool)) ( :free (s pool) (fn-hdc-model-run 1 s pool)) ( :free (s pool) (fn-hdc-model-run 2 s pool)) ( :free (s pool) (fn-hdc-model-run 3 s pool)) ( :free (s pool) (fn-hdc-model-run 4 s pool)) ( :free (s pool) (fn-hdc-model-run 5 s pool)) ( :free (s pool) (fn-hdc-model-run 6 s pool)) ( :free (s pool) (fn-hdc-model-run 7 s pool)) ( :free (s pool) (fn-hdc-model-run 8 s pool)) ( :free (s pool) (fn-hdc-model-run 9 s pool)) ( :free (s pool) (fn-hdc-model-run 10 s pool)) ( :free (s pool) (fn-hdc-model-run 11 s pool)))
          :in-theory (enable fn-hdc-model-run fn-hdc-begin fn-hdc-state
                             fn-hdc-feed fn-hdc-feed-raw fn-hdc-move
                             fn-hdc-finish-number fn-hdc-result))))
