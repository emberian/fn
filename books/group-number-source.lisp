; Captured group/local-number -> immutable row ordinal. No NNTP entry stack.
(in-package "ACL2")
(include-book "group-number-trie")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-gns-at (i xs)
  (declare (xargs :guard (natp i) :measure (nfix i)))
  (if (zp i) (fn-ag-car xs) (fn-gns-at (1- i) (fn-ag-cdr xs))))

; ACL2 characters are octets. CHAR accesses the retained string directly;
; neither a character list nor an integer representing the whole key is made.
(defun fn-gns-bit (group position bit)
  (declare (xargs :guard t))
  (if (and (stringp group) (natp position) (< position (length group))
           (natp bit) (< bit 8))
      (mod (floor (char-code (char group position)) (expt 2 bit)) 2)
    0))

; Logical suffix lookup. The terminal node is separate from every byte bit.
(defun fn-gns-group-get (group position bit node)
  (declare (xargs :guard (and (stringp group) (natp position)
                              (<= position (length group)) (natp bit) (< bit 8))
                  :measure (nfix (+ (* 8 (- (length group) (nfix position))) (- 8 (nfix bit))))))
  (if (not (and (stringp group) (natp position) (<= position (length group))
                 (natp bit) (< bit 8))) nil
    (if (>= position (length group)) (fn-gnix-val node)
    (fn-gns-group-get group (if (= bit 7) (1+ position) position)
                      (if (= bit 7) 0 (1+ bit))
                      (if (= (fn-gns-bit group position bit) 0)
                          (fn-gnix-zero node) (fn-gnix-one node))))))

; Group cursor fixed6: phase, retained string, character position, bit, node,
; steps. A step inspects one bit; terminal completion performs no descent.
(defun fn-gns-group-begin (group root)
  (declare (xargs :guard t))
  (if (stringp group) (list :walking group 0 0 root 0)
    (list :refused "" 0 0 nil 0)))
(defun fn-gns-group-cursorp (c)
  (declare (xargs :guard t))
  (and (true-listp c) (= (len c) 6)
       (member-eq (fn-gns-at 0 c) '(:walking :done :refused))
       (stringp (fn-gns-at 1 c)) (natp (fn-gns-at 2 c))
       (<= (fn-gns-at 2 c) (length (fn-gns-at 1 c)))
       (natp (fn-gns-at 3 c)) (< (fn-gns-at 3 c) 8)
       (natp (fn-gns-at 5 c))
       (implies (eq (fn-gns-at 0 c) :done)
                (= (fn-gns-at 2 c) (length (fn-gns-at 1 c))))))
(defun fn-gns-group-step (c)
  (declare (xargs :guard (fn-gns-group-cursorp c)))
  (let ((phase (fn-gns-at 0 c)) (group (fn-gns-at 1 c))
        (pos (fn-gns-at 2 c)) (bit (fn-gns-at 3 c))
        (node (fn-gns-at 4 c)) (steps (fn-gns-at 5 c)))
    (cond ((not (eq phase :walking)) c)
          ((>= pos (length group)) (list :done group pos bit node steps))
          (t (list :walking group (if (= bit 7) (1+ pos) pos)
                   (if (= bit 7) 0 (1+ bit))
                   (if (= (fn-gns-bit group pos bit) 0)
                       (fn-gnix-zero node) (fn-gnix-one node)) (1+ steps))))))
(defun fn-gns-group-result (c)
  (declare (xargs :guard t))
  (if (eq (fn-gns-at 0 c) :done)
      (list :number-root (fn-gnix-val (fn-gns-at 4 c)))
    (list :pending)))

; Number cursor fixed5: phase, residual positive number, node, captured count,
; steps. Explicit ordinal option retains zero; a missing node has NIL value.
(defun fn-gns-number-begin (number root count)
  (declare (xargs :guard t))
  (if (and (posp number) (natp count))
      (list :walking number root count 0)
    (list :refused 1 nil 0 0)))
(defun fn-gns-number-cursorp (c)
  (declare (xargs :guard t))
  (and (true-listp c) (= (len c) 5)
       (member-eq (fn-gns-at 0 c) '(:walking :done :refused))
       (posp (fn-gns-at 1 c)) (natp (fn-gns-at 3 c))
       (natp (fn-gns-at 4 c))
       (implies (eq (fn-gns-at 0 c) :done) (= (fn-gns-at 1 c) 1))))
(defun fn-gns-number-step (c)
  (declare (xargs :guard (fn-gns-number-cursorp c)))
  (let ((n (fn-gns-at 1 c)) (node (fn-gns-at 2 c))
        (count (fn-gns-at 3 c)) (steps (fn-gns-at 4 c)))
    (cond ((not (eq (fn-gns-at 0 c) :walking)) c)
          ((<= n 1) (list :done n node count steps))
          (t (list :walking (floor n 2)
                   (if (evenp n) (fn-gnix-zero node) (fn-gnix-one node))
                   count (1+ steps))))))
(defun fn-gns-number-result (c)
  (declare (xargs :guard t))
  (let ((v (fn-gnix-val (fn-gns-at 2 c))))
    (if (not (eq (fn-gns-at 0 c) :done)) '(:pending)
      (if (and (true-listp v) (= (len v) 2) (eq (fn-gns-at 0 v) :ordinal)
               (natp (fn-gns-at 1 v)) (< (fn-gns-at 1 v) (nfix (fn-gns-at 3 c))))
          v
        '(:missing)))))

(defthm fn-gns-group-begin-cursorp
  (fn-gns-group-cursorp (fn-gns-group-begin group root)))
(defthm fn-gns-group-step-cursorp
  (implies (fn-gns-group-cursorp c)
           (fn-gns-group-cursorp (fn-gns-group-step c))))
(defthm fn-gns-number-begin-cursorp
  (fn-gns-number-cursorp (fn-gns-number-begin number root count)))
(defthm fn-gns-number-step-cursorp
  (implies (fn-gns-number-cursorp c)
           (fn-gns-number-cursorp (fn-gns-number-step c))))

; One-step refinements carry the lookup denotation instead of revalidating an
; entire published catalogue at request time.
(defthm fn-gns-group-step-preserves-lookup
  (implies (fn-gns-group-cursorp c)
           (equal (fn-gns-group-get (fn-gns-at 1 (fn-gns-group-step c))
                                    (fn-gns-at 2 (fn-gns-group-step c))
                                    (fn-gns-at 3 (fn-gns-group-step c))
                                    (fn-gns-at 4 (fn-gns-group-step c)))
                  (fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c)
                                    (fn-gns-at 3 c) (fn-gns-at 4 c))))
  :hints (("Goal" :in-theory (enable fn-gns-group-step fn-gns-group-cursorp)
           :expand ((fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c)
                                      (fn-gns-at 3 c) (fn-gns-at 4 c))))))
(defthm fn-gns-number-step-preserves-lookup
  (implies (fn-gns-number-cursorp c)
           (equal (fn-gnix-get (fn-gns-at 1 (fn-gns-number-step c))
                               (fn-gns-at 2 (fn-gns-number-step c)))
                  (fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c))))
  :hints (("Goal" :in-theory (enable fn-gns-number-step fn-gns-number-cursorp)
           :expand ((fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c))))))

(defthm fn-gns-group-done-result-refinement
  (implies (and (fn-gns-group-cursorp c) (eq (fn-gns-at 0 c) :done))
           (equal (fn-gns-group-result c)
                  (list :number-root
                        (fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c)
                                          (fn-gns-at 3 c) (fn-gns-at 4 c)))))
  :hints (("Goal" :in-theory (enable fn-gns-group-cursorp fn-gns-group-result)
           :expand ((fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c)
                                      (fn-gns-at 3 c) (fn-gns-at 4 c))))))
(defthm fn-gns-number-done-result-refinement
  (implies (and (fn-gns-number-cursorp c) (eq (fn-gns-at 0 c) :done)
                (true-listp (fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c)))
                (= (len (fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c))) 2)
                (eq (fn-gns-at 0 (fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c))) :ordinal)
                (natp (fn-gns-at 1 (fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c))))
                (< (fn-gns-at 1 (fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c))) (fn-gns-at 3 c)))
           (equal (fn-gns-number-result c)
                  (fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c))))
  :hints (("Goal" :in-theory (enable fn-gns-number-cursorp fn-gns-number-result)
           :expand ((fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c))))))
