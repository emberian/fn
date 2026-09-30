(in-package "ACL2")
(include-book "../../books/history-decode-refinement")

; Literal reachable witnesses of the complete current-codec theorem.
; Ghost semantics are evaluated by ground proofs, never host execution.

(defthm fn-hdc-refinement-positive-nil
  (let ((pool '(0)) (offset 0) (count 1))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(0)) (offset 0) (count 1) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-nonminimal-natural
  (let ((pool '(1 2 37 0)) (offset 0) (count 4))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(1 2 37 0)) (offset 0) (count 4) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-empty-octets
  (let ((pool '(6 0)) (offset 0) (count 2))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(6 0)) (offset 0) (count 2) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-nil-alias
  (let ((pool '(4 1 1 3 78 73 76)) (offset 0) (count 7))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(4 1 1 3 78 73 76)) (offset 0) (count 7) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-arbitrary-symbol
  (let ((pool '(4 2 1 4 90 90 90 90)) (offset 0) (count 8))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(4 2 1 4 90 90 90 90)) (offset 0) (count 8) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-string-cons
  (let ((pool '(3 1 2 65 66 0 5)) (offset 0) (count 7))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(3 1 2 65 66 0 5)) (offset 0) (count 7) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-slice
  (let ((pool '(255 7 65 255)) (offset 1) (count 2))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(255 7 65 255)) (offset 1) (count 2) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-bad-opcode
  (let ((pool '(8)) (offset 0) (count 1))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(8)) (offset 0) (count 1) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-bad-package
  (let ((pool '(4 3)) (offset 0) (count 2))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(4 3)) (offset 0) (count 2) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-underflow
  (let ((pool '(5)) (offset 0) (count 1))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(5)) (offset 0) (count 1) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-truncated-length
  (let ((pool '(1 2 37)) (offset 0) (count 3))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(1 2 37)) (offset 0) (count 3) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-multiple-values
  (let ((pool '(0 0)) (offset 0) (count 2))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(0 0)) (offset 0) (count 2) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-empty-program
  (let ((pool '()) (offset 0) (count 0))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '()) (offset 0) (count 0) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

(defthm fn-hdc-refinement-positive-hstxa
  (let ((pool '(4 0 1 5 72 83 84 88 65)) (offset 0) (count 9))
    (and (fn-scc-octet-listp pool) (natp offset) (natp count)
         (<= (+ offset count) (len pool))
         (equal (fn-hdc-abstract-result
                 (fn-hdc-result (fn-hdc-model-run count
                                 (fn-hdc-begin offset count 9 17) pool)) pool)
                (fn-scc-decode-tree (take count (nthcdr offset pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-current-codec-refinement
                      (pool '(4 0 1 5 72 83 84 88 65)) (offset 0) (count 9) (epoch 9) (lease 17)))
           :in-theory (disable fn-hdc-model-run fn-hdc-abstract-result
                               fn-hdc-result fn-hdc-begin fn-scc-decode-tree))))

; Hypothesis removal: all retained per-feed premises hold; source agreement
; alone fails and the literal denotation equality fails.
(defthm fn-hdc-feed-source-byte-hypothesis-removal
  (let* ((pool '(0)) (s (fn-hdc-begin 0 1 9 17)) (byte 1))
    (and (fn-hdc-coherent s pool) (fn-scc-octet-listp pool)
         (<= (nth 8 s) (len pool)) (fn-scc-octetp byte)
         (not (equal byte (nth (nth 7 s) pool)))
         (not (equal (fn-hdc-denote (fn-hdc-feed byte s) pool)
                     (fn-hdc-denote s pool)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdc-coherent fn-hdc-begin fn-hdc-state
                                   fn-hdc-statep fn-hdc-feed fn-hdc-feed-raw
                                   fn-hdc-move fn-hdc-denote fn-hdc-model-tail
                                   fn-hdc-model-done fn-hdc-stack-abstract))))

; Corrupted-state witness, not a reachable parser execution. Cached tag lies.
(defthm fn-hdc-corrupted-tag-coherence-witness
  (let* ((pool '(72 83 88 88 65))
         (s (fn-hdc-state :payload 4 0 '(0 0 1) 0 5 1 4 5 nil 9 17))
         (byte 65))
    (and (fn-hdc-statep s) (not (fn-hdc-coherent s pool))
         (fn-scc-octet-listp pool) (<= (nth 8 s) (len pool))
         (fn-scc-octetp byte) (equal byte (nth (nth 7 s) pool))
         (not (equal (fn-hdc-denote (fn-hdc-feed byte s) pool)
                     (fn-hdc-denote s pool)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdc-coherent fn-hdc-state fn-hdc-statep
                                   fn-hdc-tag-prefixp fn-hdc-feed fn-hdc-feed-raw
                                   fn-hdc-move fn-hdc-tag-byte fn-hdc-payload-node
                                   fn-hdc-denote fn-hdc-model-tail fn-hdc-model-done
                                   fn-hdc-stack-abstract fn-hdc-abstract fn-hdc-model-payload))))

(defun fn-hdc-refinement-test-feed (bytes s)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp bytes)
      (fn-hdc-refinement-test-feed (cdr bytes) (fn-hdc-feed (car bytes) s))
    s))

; Executable public entry/result behavior, independently of ghost theorem.
(assert-event
 (equal (fn-hdc-result
         (fn-hdc-refinement-test-feed '(1 2 37 0) (fn-hdc-begin 0 4 9 17)))
        '(:ok (:atom 37))))
(assert-event
 (equal (fn-hdc-result (fn-hdc-begin 0 4 9 17)) '(:yield)))
(assert-event
 (equal (fn-hdc-result
         (fn-hdc-refinement-test-feed '(0 0) (fn-hdc-begin 0 2 9 17)))
        '(:refused :tree)))
(assert-event
 (let* ((bytes '(3 1 2 65 66 0 5))
        (start (fn-hdc-begin 100 7 9 17))
        (paused (fn-hdc-refinement-test-feed (take 4 bytes) start))
        (end (fn-hdc-refinement-test-feed (nthcdr 4 bytes) paused)))
   (and (equal (fn-hdc-result paused) '(:yield))
        (equal end (fn-hdc-refinement-test-feed bytes start))
        (equal (nth 8 end) 107) (equal (nth 10 end) 9) (equal (nth 11 end) 17))))

; Literal complete partition antecedent/conclusion: suspension in payload.
(defthm fn-hdc-fuel-partition-positive
  (let ((first 4) (second 3) (pool '(3 1 2 65 66 0 5))
        (s (fn-hdc-begin 0 7 9 17)))
    (and (natp first) (natp second)
         (equal (fn-hdc-model-run second (fn-hdc-model-run first s pool) pool)
                (fn-hdc-model-run (+ first second) s pool))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hdc-model-run-fuel-partition
                         (first 4) (second 3) (pool '(3 1 2 65 66 0 5))
                         (s (fn-hdc-begin 0 7 9 17))))
           :in-theory (disable fn-hdc-model-run fn-hdc-begin))))

(defthm fn-hdc-run-lifetime-positive
  (let ((pool '(8)) (s (fn-hdc-begin 0 1 '(capture 9) '(lease 17))))
    (and (equal (nth 10 (fn-hdc-model-run 1 s pool)) (nth 10 s))
         (equal (nth 11 (fn-hdc-model-run 1 s pool)) (nth 11 s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-hdc-model-run fn-hdc-begin))))

(defthm fn-hdc-node-bounds-positive
 (let* ((pool '(65))
        (s (fn-hdc-state :payload 3 0 '(0 0 1) 0 1 1 0 1 nil 9 17))
        (byte 65))
  (and (fn-hdc-coherent s pool) (fn-scc-octetp byte)
       (fn-hdc-stack-in-poolp (nth 9 s) (nth 8 s))
       (fn-hdc-stack-in-poolp (nth 9 (fn-hdc-feed byte s)) (nth 8 s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hdc-state fn-hdc-coherent fn-hdc-statep
                                   fn-hdc-stack-in-poolp fn-hdc-node-in-poolp))))

; Corrupted node spine: all retained premises hold, but the supplied stack
; already contains an invalid node, which an opcode0 does not repair.
(defthm fn-hdc-node-bounds-stack-hypothesis-removal
 (let* ((pool '(0))
        (s (fn-hdc-state :op 0 0 '(0 0 1) 0 0 0 0 1 '((:bad)) 9 17))
        (byte 0))
  (and (fn-hdc-coherent s pool) (fn-scc-octetp byte)
       (not (fn-hdc-stack-in-poolp (nth 9 s) (nth 8 s)))
       (not (fn-hdc-stack-in-poolp (nth 9 (fn-hdc-feed byte s)) (nth 8 s)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hdc-state fn-hdc-coherent fn-hdc-statep
                                   fn-hdc-stack-in-poolp fn-hdc-node-in-poolp
                                   fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-atom))))
