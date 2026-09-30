(in-package "ACL2")
(include-book "../../books/history-decode-size-refinement")

; Ground proof witnesses evaluate the literal ghost relations in logic.
; They do not execute abstractions or a competing decoder in host code.
(defun hdsst-run (bytes s infos prefix usable)
  (if (consp bytes)
      (mv-let (s infos prefix usable) (fn-hds-feed (car bytes) s infos prefix usable)
        (hdsst-run (cdr bytes) s infos prefix usable))
    (list s infos prefix usable)))
(defconst *hdsst-symbol-source* '(4 1 1 3 78 73 76))
(defconst *hdsst-symbol-state*
  (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0) 4 3 1 6 7 nil 17 23))
(assert-event
 (let ((r (hdsst-run '(4 1 1 3 78 73)
                     (fn-hdc-begin 0 7 17 23) nil nil t)))
   (and (equal (car r) *hdsst-symbol-state*)
        (null (nth 1 r)) (nth 2 r) (nth 3 r))))

; Actual byte-fed reachable completion.
(defthm hdsst-feed-reachable-positive
  (let ((s *hdsst-symbol-state*) (pool *hdsst-symbol-source*) (byte 76)
        (infos nil) (prefix t) (usable t))
    (and
      (fn-hdc-coherent s pool)
      (fn-scc-octet-listp pool)
      (<= (nth 8 s) (len pool))
      (equal byte (nth (nth 7 s) pool))
      (fn-hds-prefix-coherent s prefix pool)
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (mv-nth 3 (fn-hds-feed byte s infos prefix usable))
      (fn-hds-stack-correspondsp
          (mv-nth 1 (fn-hds-feed byte s infos prefix usable))
          (nth 9 (mv-nth 0 (fn-hds-feed byte s infos prefix usable))) pool) ))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Independent literal removal; all other premises affirmed. Corrupted/mutated case.
(defthm hdsst-feed-corrupt-coherence
  (let ((s (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0) 4 3 1 5 7 nil 17 23)) (pool *hdsst-symbol-source*) (byte 73)
        (infos nil) (prefix t) (usable t))
    (and
      (not (fn-hdc-coherent s pool))
      (fn-scc-octet-listp pool)
      (<= (nth 8 s) (len pool))
      (equal byte (nth (nth 7 s) pool))
      (fn-hds-prefix-coherent s prefix pool)
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (mv-nth 3 (fn-hds-feed byte s infos prefix usable))
      (not (fn-hds-stack-correspondsp
          (mv-nth 1 (fn-hds-feed byte s infos prefix usable))
          (nth 9 (mv-nth 0 (fn-hds-feed byte s infos prefix usable))) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Independent literal removal; all other premises affirmed. Corrupted/mutated case.
(defthm hdsst-feed-corrupt-source-octets
  (let ((s (fn-hdc-state :payload 6 0 (fn-hdc-number-begin 0) 0 2 1 1 2 nil 17 23)) (pool '(300 1)) (byte 1)
        (infos nil) (prefix nil) (usable t))
    (and
      (fn-hdc-coherent s pool)
      (not (fn-scc-octet-listp pool))
      (<= (nth 8 s) (len pool))
      (equal byte (nth (nth 7 s) pool))
      (fn-hds-prefix-coherent s prefix pool)
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (mv-nth 3 (fn-hds-feed byte s infos prefix usable))
      (not (fn-hds-stack-correspondsp
          (mv-nth 1 (fn-hds-feed byte s infos prefix usable))
          (nth 9 (mv-nth 0 (fn-hds-feed byte s infos prefix usable))) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Independent literal removal; all other premises affirmed. Corrupted/mutated case.
(defthm hdsst-feed-corrupt-source-bound
  (let ((s (fn-hdc-state :payload 6 0 (fn-hdc-number-begin 0) 0 2 1 1 2 nil 17 23)) (pool '(1)) (byte nil)
        (infos nil) (prefix nil) (usable t))
    (and
      (fn-hdc-coherent s pool)
      (fn-scc-octet-listp pool)
      (not (<= (nth 8 s) (len pool)))
      (equal byte (nth (nth 7 s) pool))
      (fn-hds-prefix-coherent s prefix pool)
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (mv-nth 3 (fn-hds-feed byte s infos prefix usable))
      (not (fn-hds-stack-correspondsp
          (mv-nth 1 (fn-hds-feed byte s infos prefix usable))
          (nth 9 (mv-nth 0 (fn-hds-feed byte s infos prefix usable))) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Independent literal removal; all other premises affirmed. Corrupted/mutated case.
(defthm hdsst-feed-mutated-source-byte
  (let ((s *hdsst-symbol-state*) (pool *hdsst-symbol-source*) (byte 77)
        (infos nil) (prefix t) (usable t))
    (and
      (fn-hdc-coherent s pool)
      (fn-scc-octet-listp pool)
      (<= (nth 8 s) (len pool))
      (not (equal byte (nth (nth 7 s) pool)))
      (fn-hds-prefix-coherent s prefix pool)
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (mv-nth 3 (fn-hds-feed byte s infos prefix usable))
      (not (fn-hds-stack-correspondsp
          (mv-nth 1 (fn-hds-feed byte s infos prefix usable))
          (nth 9 (mv-nth 0 (fn-hds-feed byte s infos prefix usable))) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Independent literal removal; all other premises affirmed. Corrupted/mutated case.
(defthm hdsst-feed-corrupt-prefix
  (let ((s *hdsst-symbol-state*) (pool *hdsst-symbol-source*) (byte 76)
        (infos nil) (prefix nil) (usable t))
    (and
      (fn-hdc-coherent s pool)
      (fn-scc-octet-listp pool)
      (<= (nth 8 s) (len pool))
      (equal byte (nth (nth 7 s) pool))
      (not (fn-hds-prefix-coherent s prefix pool))
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (mv-nth 3 (fn-hds-feed byte s infos prefix usable))
      (not (fn-hds-stack-correspondsp
          (mv-nth 1 (fn-hds-feed byte s infos prefix usable))
          (nth 9 (mv-nth 0 (fn-hds-feed byte s infos prefix usable))) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Independent literal removal; all other premises affirmed. Corrupted/mutated case.
(defthm hdsst-feed-corrupt-prior-stack
  (let ((s (fn-hdc-state :op 0 0 (fn-hdc-number-begin 0) 0 0 0 0 2 (list (fn-hdc-atom 7)) 17 23)) (pool '(0 0)) (byte 0)
        (infos (list (fn-hds-info-leaf (fn-scs-summary nil)))) (prefix nil) (usable t))
    (and
      (fn-hdc-coherent s pool)
      (fn-scc-octet-listp pool)
      (<= (nth 8 s) (len pool))
      (equal byte (nth (nth 7 s) pool))
      (fn-hds-prefix-coherent s prefix pool)
      (not (fn-hds-stack-correspondsp infos (nth 9 s) pool))
      (mv-nth 3 (fn-hds-feed byte s infos prefix usable))
      (not (fn-hds-stack-correspondsp
          (mv-nth 1 (fn-hds-feed byte s infos prefix usable))
          (nth 9 (mv-nth 0 (fn-hds-feed byte s infos prefix usable))) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Independent literal removal; all other premises affirmed. Corrupted/mutated case.
(defthm hdsst-feed-corrupt-usability
  (let ((s (fn-hdc-begin 0 1 17 23)) (pool '(0)) (byte 0)
        (infos nil) (prefix nil) (usable nil))
    (and
      (fn-hdc-coherent s pool)
      (fn-scc-octet-listp pool)
      (<= (nth 8 s) (len pool))
      (equal byte (nth (nth 7 s) pool))
      (fn-hds-prefix-coherent s prefix pool)
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (not (mv-nth 3 (fn-hds-feed byte s infos prefix usable)))
      (not (fn-hds-stack-correspondsp
          (mv-nth 1 (fn-hds-feed byte s infos prefix usable))
          (nth 9 (mv-nth 0 (fn-hds-feed byte s infos prefix usable))) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Literal weakened prefix theorem: byte-domain premise removed after proof.
(defthm hdsst-prefix-reachable-positive
  (let ((s (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0) 4 3 3 4 7 nil 17 23)) (pool *hdsst-symbol-source*) (byte 78)
        (infos nil) (prefix nil) (usable t))
    (and
      (fn-hdc-coherent s pool)
      (equal byte (nth (nth 7 s) pool))
      (fn-hds-prefix-coherent s prefix pool)
      (fn-hds-prefix-coherent (mv-nth 0 (fn-hds-feed byte s infos prefix usable))
                              (mv-nth 2 (fn-hds-feed byte s infos prefix usable)) pool)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Literal weakened prefix theorem: byte-domain premise removed after proof.
(defthm hdsst-prefix-corrupt-coherence
  (let ((s (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0) 4 3 3 5 7 nil 17 23)) (pool *hdsst-symbol-source*) (byte 73)
        (infos nil) (prefix nil) (usable t))
    (and
      (not (fn-hdc-coherent s pool))
      (equal byte (nth (nth 7 s) pool))
      (fn-hds-prefix-coherent s prefix pool)
      (not (fn-hds-prefix-coherent (mv-nth 0 (fn-hds-feed byte s infos prefix usable))
                              (mv-nth 2 (fn-hds-feed byte s infos prefix usable)) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Literal weakened prefix theorem: byte-domain premise removed after proof.
(defthm hdsst-prefix-mutated-byte
  (let ((s (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0) 4 3 3 4 7 nil 17 23)) (pool *hdsst-symbol-source*) (byte 77)
        (infos nil) (prefix nil) (usable t))
    (and
      (fn-hdc-coherent s pool)
      (not (equal byte (nth (nth 7 s) pool)))
      (fn-hds-prefix-coherent s prefix pool)
      (not (fn-hds-prefix-coherent (mv-nth 0 (fn-hds-feed byte s infos prefix usable))
                              (mv-nth 2 (fn-hds-feed byte s infos prefix usable)) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Literal weakened prefix theorem: byte-domain premise removed after proof.
(defthm hdsst-prefix-corrupt-prefix
  (let ((s (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0) 4 3 2 5 7 nil 17 23)) (pool *hdsst-symbol-source*) (byte 73)
        (infos nil) (prefix nil) (usable t))
    (and
      (fn-hdc-coherent s pool)
      (equal byte (nth (nth 7 s) pool))
      (not (fn-hds-prefix-coherent s prefix pool))
      (not (fn-hds-prefix-coherent (mv-nth 0 (fn-hds-feed byte s infos prefix usable))
                              (mv-nth 2 (fn-hds-feed byte s infos prefix usable)) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Literal normalized span theorem: package-domain removed after proof.
(defthm hdsst-span-reachable-positive
  (let* ((op 4) (pkg 1) (offset 4) (count 3)
         (pool *hdsst-symbol-source*) (nil-alias t)
         (value (fn-hdc-abstract (fn-hdc-span op pkg offset count) pool)))
    (and
      (member-equal op '(3 4 6))
      (natp offset)
      (natp count)
      (fn-scc-octet-listp pool)
      (<= (+ offset count) (len pool))
      (implies (equal op 4) (iff nil-alias (null value)))
      (equal (fn-hds-leaf-carry (fn-hdc-span op pkg offset count) nil-alias)
             (fn-scs-summary value))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Literal normalized span theorem: package-domain removed after proof.
(defthm hdsst-span-corrupt-opcode
  (let* ((op 7) (pkg 0) (offset 0) (count 1)
         (pool '(1)) (nil-alias nil)
         (value (fn-hdc-abstract (fn-hdc-span op pkg offset count) pool)))
    (and
      (not (member-equal op '(3 4 6)))
      (natp offset)
      (natp count)
      (fn-scc-octet-listp pool)
      (<= (+ offset count) (len pool))
      (implies (equal op 4) (iff nil-alias (null value)))
      (not (equal (fn-hds-leaf-carry (fn-hdc-span op pkg offset count) nil-alias)
             (fn-scs-summary value)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Literal normalized span theorem: package-domain removed after proof.
(defthm hdsst-span-corrupt-offset
  (let* ((op 6) (pkg 0) (offset -1) (count 2)
         (pool '(1)) (nil-alias nil)
         (value (fn-hdc-abstract (fn-hdc-span op pkg offset count) pool)))
    (and
      (member-equal op '(3 4 6))
      (not (natp offset))
      (natp count)
      (fn-scc-octet-listp pool)
      (<= (+ offset count) (len pool))
      (implies (equal op 4) (iff nil-alias (null value)))
      (not (equal (fn-hds-leaf-carry (fn-hdc-span op pkg offset count) nil-alias)
             (fn-scs-summary value)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Literal normalized span theorem: package-domain removed after proof.
(defthm hdsst-span-corrupt-count
  (let* ((op 6) (pkg 0) (offset 0) (count -1)
         (pool '(1)) (nil-alias nil)
         (value (fn-hdc-abstract (fn-hdc-span op pkg offset count) pool)))
    (and
      (member-equal op '(3 4 6))
      (natp offset)
      (not (natp count))
      (fn-scc-octet-listp pool)
      (<= (+ offset count) (len pool))
      (implies (equal op 4) (iff nil-alias (null value)))
      (not (equal (fn-hds-leaf-carry (fn-hdc-span op pkg offset count) nil-alias)
             (fn-scs-summary value)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Literal normalized span theorem: package-domain removed after proof.
(defthm hdsst-span-corrupt-source-octets
  (let* ((op 6) (pkg 0) (offset 0) (count 2)
         (pool '(300 1)) (nil-alias nil)
         (value (fn-hdc-abstract (fn-hdc-span op pkg offset count) pool)))
    (and
      (member-equal op '(3 4 6))
      (natp offset)
      (natp count)
      (not (fn-scc-octet-listp pool))
      (<= (+ offset count) (len pool))
      (implies (equal op 4) (iff nil-alias (null value)))
      (not (equal (fn-hds-leaf-carry (fn-hdc-span op pkg offset count) nil-alias)
             (fn-scs-summary value)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Literal normalized span theorem: package-domain removed after proof.
(defthm hdsst-span-corrupt-source-bound
  (let* ((op 6) (pkg 0) (offset 0) (count 2)
         (pool '(1)) (nil-alias nil)
         (value (fn-hdc-abstract (fn-hdc-span op pkg offset count) pool)))
    (and
      (member-equal op '(3 4 6))
      (natp offset)
      (natp count)
      (fn-scc-octet-listp pool)
      (not (<= (+ offset count) (len pool)))
      (implies (equal op 4) (iff nil-alias (null value)))
      (not (equal (fn-hds-leaf-carry (fn-hdc-span op pkg offset count) nil-alias)
             (fn-scs-summary value)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Literal normalized span theorem: package-domain removed after proof.
(defthm hdsst-span-corrupt-alias
  (let* ((op 4) (pkg 1) (offset 4) (count 3)
         (pool *hdsst-symbol-source*) (nil-alias nil)
         (value (fn-hdc-abstract (fn-hdc-span op pkg offset count) pool)))
    (and
      (member-equal op '(3 4 6))
      (natp offset)
      (natp count)
      (fn-scc-octet-listp pool)
      (<= (+ offset count) (len pool))
      (not (implies (equal op 4) (iff nil-alias (null value))))
      (not (equal (fn-hds-leaf-carry (fn-hdc-span op pkg offset count) nil-alias)
             (fn-scs-summary value)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Final normalization: global pool-octet/end premises removed after proof.
(defthm hdsst-final-reachable-positive
  (let ((s *hdsst-symbol-state*) (pool *hdsst-symbol-source*) (byte 76) (prefix t))
    (and
      (fn-hdc-coherent s pool)
      (equal (nth 0 s) :payload)
      (equal (nth 1 s) 4)
      (equal (nth 6 s) 1)
      (fn-hds-prefix-coherent s prefix pool)
      (equal byte (nth (nth 7 s) pool))
      (iff (fn-hds-nil-byte byte s prefix)
           (null (fn-hdc-abstract (fn-hdc-span 4 (nth 2 s) (nth 4 s) (nth 5 s)) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Final normalization: global pool-octet/end premises removed after proof.
(defthm hdsst-final-corrupt-coherence
  (let ((s (fn-hdc-state :payload 4 3 (fn-hdc-number-begin 0) 4 3 1 6 7 nil 17 23)) (pool *hdsst-symbol-source*) (byte 76) (prefix t))
    (and
      (not (fn-hdc-coherent s pool))
      (equal (nth 0 s) :payload)
      (equal (nth 1 s) 4)
      (equal (nth 6 s) 1)
      (fn-hds-prefix-coherent s prefix pool)
      (equal byte (nth (nth 7 s) pool))
      (not (iff (fn-hds-nil-byte byte s prefix)
           (null (fn-hdc-abstract (fn-hdc-span 4 (nth 2 s) (nth 4 s) (nth 5 s)) pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Final normalization: global pool-octet/end premises removed after proof.
(defthm hdsst-final-corrupt-mode
  (let ((s (fn-hdc-state :done 4 1 (fn-hdc-number-begin 0) 4 3 1 6 7 nil 17 23)) (pool *hdsst-symbol-source*) (byte 76) (prefix t))
    (and
      (fn-hdc-coherent s pool)
      (not (equal (nth 0 s) :payload))
      (equal (nth 1 s) 4)
      (equal (nth 6 s) 1)
      (fn-hds-prefix-coherent s prefix pool)
      (equal byte (nth (nth 7 s) pool))
      (not (iff (fn-hds-nil-byte byte s prefix)
           (null (fn-hdc-abstract (fn-hdc-span 4 (nth 2 s) (nth 4 s) (nth 5 s)) pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Final normalization: global pool-octet/end premises removed after proof.
(defthm hdsst-final-corrupt-opcode
  (let ((s (fn-hdc-state :payload 3 1 (fn-hdc-number-begin 0) 4 3 1 6 7 nil 17 23)) (pool *hdsst-symbol-source*) (byte 76) (prefix t))
    (and
      (fn-hdc-coherent s pool)
      (equal (nth 0 s) :payload)
      (not (equal (nth 1 s) 4))
      (equal (nth 6 s) 1)
      (fn-hds-prefix-coherent s prefix pool)
      (equal byte (nth (nth 7 s) pool))
      (not (iff (fn-hds-nil-byte byte s prefix)
           (null (fn-hdc-abstract (fn-hdc-span 4 (nth 2 s) (nth 4 s) (nth 5 s)) pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Final normalization: global pool-octet/end premises removed after proof.
(defthm hdsst-final-corrupt-final-position
  (let ((s (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0) 4 3 2 5 7 nil 17 23)) (pool '(4 1 1 3 78 73 77)) (byte 73) (prefix t))
    (and
      (fn-hdc-coherent s pool)
      (equal (nth 0 s) :payload)
      (equal (nth 1 s) 4)
      (not (equal (nth 6 s) 1))
      (fn-hds-prefix-coherent s prefix pool)
      (equal byte (nth (nth 7 s) pool))
      (not (iff (fn-hds-nil-byte byte s prefix)
           (null (fn-hdc-abstract (fn-hdc-span 4 (nth 2 s) (nth 4 s) (nth 5 s)) pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Final normalization: global pool-octet/end premises removed after proof.
(defthm hdsst-final-corrupt-prefix
  (let ((s *hdsst-symbol-state*) (pool *hdsst-symbol-source*) (byte 76) (prefix nil))
    (and
      (fn-hdc-coherent s pool)
      (equal (nth 0 s) :payload)
      (equal (nth 1 s) 4)
      (equal (nth 6 s) 1)
      (not (fn-hds-prefix-coherent s prefix pool))
      (equal byte (nth (nth 7 s) pool))
      (not (iff (fn-hds-nil-byte byte s prefix)
           (null (fn-hdc-abstract (fn-hdc-span 4 (nth 2 s) (nth 4 s) (nth 5 s)) pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Final normalization: global pool-octet/end premises removed after proof.
(defthm hdsst-final-mutated-byte
  (let ((s *hdsst-symbol-state*) (pool *hdsst-symbol-source*) (byte 77) (prefix t))
    (and
      (fn-hdc-coherent s pool)
      (equal (nth 0 s) :payload)
      (equal (nth 1 s) 4)
      (equal (nth 6 s) 1)
      (fn-hds-prefix-coherent s prefix pool)
      (not (equal byte (nth (nth 7 s) pool)))
      (not (iff (fn-hds-nil-byte byte s prefix)
           (null (fn-hdc-abstract (fn-hdc-span 4 (nth 2 s) (nth 4 s) (nth 5 s)) pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp))))

; Literal arbitrary-fuel invariant, independent single-quantum removals.
(defthm hdsst-run-reachable-positive
  (let* ((s *hdsst-symbol-state*) (pool *hdsst-symbol-source*)
         (infos nil) (prefix t) (usable t)
         (r (fn-hds-model-run 1 s infos prefix usable pool)))
    (and
      (fn-hdc-coherent s pool)
      (fn-scc-octet-listp pool)
      (<= (nth 8 s) (len pool))
      (fn-hds-prefix-coherent s prefix pool)
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (nth 3 r)
      (and (fn-hds-prefix-coherent (car r) (nth 2 r) pool)
            (fn-hds-stack-correspondsp (nth 1 r) (nth 9 (car r)) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Literal arbitrary-fuel invariant, independent single-quantum removals.
(defthm hdsst-run-corrupt-coherence
  (let* ((s (fn-hdc-state :payload 4 1 (fn-hdc-number-begin 0) 4 3 1 5 7 nil 17 23)) (pool *hdsst-symbol-source*)
         (infos nil) (prefix t) (usable t)
         (r (fn-hds-model-run 1 s infos prefix usable pool)))
    (and
      (not (fn-hdc-coherent s pool))
      (fn-scc-octet-listp pool)
      (<= (nth 8 s) (len pool))
      (fn-hds-prefix-coherent s prefix pool)
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (nth 3 r)
      (not (and (fn-hds-prefix-coherent (car r) (nth 2 r) pool)
            (fn-hds-stack-correspondsp (nth 1 r) (nth 9 (car r)) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Literal arbitrary-fuel invariant, independent single-quantum removals.
(defthm hdsst-run-corrupt-source-octets
  (let* ((s (fn-hdc-state :payload 6 0 (fn-hdc-number-begin 0) 0 2 1 1 2 nil 17 23)) (pool '(300 1))
         (infos nil) (prefix nil) (usable t)
         (r (fn-hds-model-run 1 s infos prefix usable pool)))
    (and
      (fn-hdc-coherent s pool)
      (not (fn-scc-octet-listp pool))
      (<= (nth 8 s) (len pool))
      (fn-hds-prefix-coherent s prefix pool)
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (nth 3 r)
      (not (and (fn-hds-prefix-coherent (car r) (nth 2 r) pool)
            (fn-hds-stack-correspondsp (nth 1 r) (nth 9 (car r)) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Literal arbitrary-fuel invariant, independent single-quantum removals.
(defthm hdsst-run-corrupt-source-bound
  (let* ((s (fn-hdc-state :payload 6 0 (fn-hdc-number-begin 0) 0 2 1 1 2 nil 17 23)) (pool '(1))
         (infos nil) (prefix nil) (usable t)
         (r (fn-hds-model-run 1 s infos prefix usable pool)))
    (and
      (fn-hdc-coherent s pool)
      (fn-scc-octet-listp pool)
      (not (<= (nth 8 s) (len pool)))
      (fn-hds-prefix-coherent s prefix pool)
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (nth 3 r)
      (not (and (fn-hds-prefix-coherent (car r) (nth 2 r) pool)
            (fn-hds-stack-correspondsp (nth 1 r) (nth 9 (car r)) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Literal arbitrary-fuel invariant, independent single-quantum removals.
(defthm hdsst-run-corrupt-prefix
  (let* ((s *hdsst-symbol-state*) (pool *hdsst-symbol-source*)
         (infos nil) (prefix nil) (usable t)
         (r (fn-hds-model-run 1 s infos prefix usable pool)))
    (and
      (fn-hdc-coherent s pool)
      (fn-scc-octet-listp pool)
      (<= (nth 8 s) (len pool))
      (not (fn-hds-prefix-coherent s prefix pool))
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (nth 3 r)
      (not (and (fn-hds-prefix-coherent (car r) (nth 2 r) pool)
            (fn-hds-stack-correspondsp (nth 1 r) (nth 9 (car r)) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Literal arbitrary-fuel invariant, independent single-quantum removals.
(defthm hdsst-run-corrupt-prior-stack
  (let* ((s (fn-hdc-state :op 0 0 (fn-hdc-number-begin 0) 0 0 0 0 2 (list (fn-hdc-atom 7)) 17 23)) (pool '(0 0))
         (infos (list (fn-hds-info-leaf (fn-scs-summary nil)))) (prefix nil) (usable t)
         (r (fn-hds-model-run 1 s infos prefix usable pool)))
    (and
      (fn-hdc-coherent s pool)
      (fn-scc-octet-listp pool)
      (<= (nth 8 s) (len pool))
      (fn-hds-prefix-coherent s prefix pool)
      (not (fn-hds-stack-correspondsp infos (nth 9 s) pool))
      (nth 3 r)
      (not (and (fn-hds-prefix-coherent (car r) (nth 2 r) pool)
            (fn-hds-stack-correspondsp (nth 1 r) (nth 9 (car r)) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Literal arbitrary-fuel invariant, independent single-quantum removals.
(defthm hdsst-run-corrupt-usability
  (let* ((s (fn-hdc-begin 0 1 17 23)) (pool '(0))
         (infos nil) (prefix nil) (usable nil)
         (r (fn-hds-model-run 1 s infos prefix usable pool)))
    (and
      (fn-hdc-coherent s pool)
      (fn-scc-octet-listp pool)
      (<= (nth 8 s) (len pool))
      (fn-hds-prefix-coherent s prefix pool)
      (fn-hds-stack-correspondsp infos (nth 9 s) pool)
      (not (nth 3 r))
      (not (and (fn-hds-prefix-coherent (car r) (nth 2 r) pool)
            (fn-hds-stack-correspondsp (nth 1 r) (nth 9 (car r)) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; These structural six fields represent the full accumulator shape, including
; nonempty snapshot AND verdict children. This is not authority validation.
(defconst *hdsst-six* '(:ok 7 ((snapshot 3)) ((verdict 5)) 3 :complete))
(defconst *hdsst-six-bytes* (fn-scc-encode *hdsst-six*))
(defconst *hdsst-six-result*
  (hdsst-run *hdsst-six-bytes*
             (fn-hdc-begin 0 (len *hdsst-six-bytes*) 17 '(23 7)) nil nil t))
(defconst *hdsst-six-bad-infos*
  (list (fn-hds-info-pair (fn-hds-info-leaf (fn-scs-summary nil))
                          (fn-hds-info-cdr (car (nth 1 *hdsst-six-result*))))))
(assert-event (eq (symbol-class 'fn-hds-result (w state)) :common-lisp-compliant))

; Literal completed-root exposure.
(defthm hdsst-result-root-reachable-positive
  (let* ((parser (car *hdsst-six-result*)) (infos (nth 1 *hdsst-six-result*)) (pool *hdsst-six-bytes*)
         (result (mv-list 6 (fn-hds-result 6 parser infos t))))
    (and
      (fn-hds-stack-correspondsp infos (nth 9 parser) pool)
      (equal (car result) :ok)
      (and (equal (nth 1 result) (cadr (fn-hdc-result parser)))
            (equal (nth 2 result) (fn-scs-summary (fn-hdc-abstract (nth 1 result) pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Literal completed-root exposure.
(defthm hdsst-result-root-corrupt-stack
  (let* ((parser (car *hdsst-six-result*)) (infos *hdsst-six-bad-infos*) (pool *hdsst-six-bytes*)
         (result (mv-list 6 (fn-hds-result 6 parser infos t))))
    (and
      (not (fn-hds-stack-correspondsp infos (nth 9 parser) pool))
      (equal (car result) :ok)
      (not (and (equal (nth 1 result) (cadr (fn-hdc-result parser)))
            (equal (nth 2 result) (fn-scs-summary (fn-hdc-abstract (nth 1 result) pool)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Literal completed-root exposure.
(defthm hdsst-result-root-pending-result
  (let* ((parser (fn-hdc-begin 0 (len *hdsst-six-bytes*) 17 '(23 7))) (infos nil) (pool *hdsst-six-bytes*)
         (result (mv-list 6 (fn-hds-result 6 parser infos t))))
    (and
      (fn-hds-stack-correspondsp infos (nth 9 parser) pool)
      (not (equal (car result) :ok))
      (not (and (equal (nth 1 result) (cadr (fn-hdc-result parser)))
            (equal (nth 2 result) (fn-scs-summary (fn-hdc-abstract (nth 1 result) pool)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Literal selected-field relation, status redundant proved then removed.
(defthm hdsst-result-fields-reachable-positive
  (let* ((n 6) (parser (car *hdsst-six-result*))
         (infos (nth 1 *hdsst-six-result*)) (pool *hdsst-six-bytes*)
         (result (mv-list 6 (fn-hds-result n parser infos t))))
    (and
      (not (zp n))
      (fn-hds-stack-correspondsp infos (nth 9 parser) pool)
      (fn-scs-correspondsp (nth 3 result) (fn-hdc-abstract (nth 1 result) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Literal selected-field relation, status redundant proved then removed.
(defthm hdsst-result-fields-row-mode
  (let* ((n 0) (parser (car *hdsst-six-result*))
         (infos (nth 1 *hdsst-six-result*)) (pool *hdsst-six-bytes*)
         (result (mv-list 6 (fn-hds-result n parser infos t))))
    (and
      (not (not (zp n)))
      (fn-hds-stack-correspondsp infos (nth 9 parser) pool)
      (not (fn-scs-correspondsp (nth 3 result) (fn-hdc-abstract (nth 1 result) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Literal selected-field relation, status redundant proved then removed.
(defthm hdsst-result-fields-corrupt-stack
  (let* ((n 6) (parser (car *hdsst-six-result*))
         (infos *hdsst-six-bad-infos*) (pool *hdsst-six-bytes*)
         (result (mv-list 6 (fn-hds-result n parser infos t))))
    (and
      (not (zp n))
      (not (fn-hds-stack-correspondsp infos (nth 9 parser) pool))
      (not (fn-scs-correspondsp (nth 3 result) (fn-hdc-abstract (nth 1 result) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Arbitrary scheduler partition: complete four-value state equality.
(defthm hdsst-partition-positive
  (let* ((first 2) (second 5)
         (pool *hdsst-symbol-source*) (s (fn-hdc-begin 0 7 17 '(23 7)))
         (mid (fn-hds-model-run first s nil nil t pool)))
    (and (natp first)
         (natp second)
         (equal (fn-hds-model-run (+ first second) s nil nil t pool)
                (fn-hds-model-run second (nth 0 mid) (nth 1 mid) (nth 2 mid) (nth 3 mid) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Arbitrary scheduler partition: complete four-value state equality.
(defthm hdsst-partition-first-nonnatural
  (let* ((first -1) (second 7)
         (pool *hdsst-symbol-source*) (s (fn-hdc-begin 0 7 17 '(23 7)))
         (mid (fn-hds-model-run first s nil nil t pool)))
    (and (not (natp first))
         (natp second)
         (not (equal (fn-hds-model-run (+ first second) s nil nil t pool)
                (fn-hds-model-run second (nth 0 mid) (nth 1 mid) (nth 2 mid) (nth 3 mid) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Arbitrary scheduler partition: complete four-value state equality.
(defthm hdsst-partition-second-nonnatural
  (let* ((first 7) (second -1)
         (pool *hdsst-symbol-source*) (s (fn-hdc-begin 0 7 17 '(23 7)))
         (mid (fn-hds-model-run first s nil nil t pool)))
    (and (natp first)
         (not (natp second))
         (not (equal (fn-hds-model-run (+ first second) s nil nil t pool)
                (fn-hds-model-run second (nth 0 mid) (nth 1 mid) (nth 2 mid) (nth 3 mid) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Complete codec bridge: count-domain redundant proved then removed.
(defthm hdsst-codec-reachable-positive
  (let* ((pool '(4 1 1 3 78 73 77)) (offset 0) (count 7)
         (r (fn-hds-model-run count (fn-hdc-begin offset count 17 '(23 7)) nil nil t pool))
         (result (mv-list 6 (fn-hds-result 0 (car r) (nth 1 r) (nth 3 r))))
         (decoded (fn-scc-decode-tree (take count (nthcdr offset pool)))))
    (and
      (fn-scc-octet-listp pool)
      (natp offset)
      (<= (+ offset count) (len pool))
      (equal (car result) :ok)
      (and (equal (car decoded) :ok)
           (equal (fn-hdc-abstract (nth 1 result) pool) (cadr decoded))
           (equal (nth 2 result) (fn-scs-summary (cadr decoded))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Complete codec bridge: count-domain redundant proved then removed.
(defthm hdsst-codec-corrupt-source-octets
  (let* ((pool '(6 1 1 300)) (offset 0) (count 4)
         (r (fn-hds-model-run count (fn-hdc-begin offset count 17 '(23 7)) nil nil t pool))
         (result (mv-list 6 (fn-hds-result 0 (car r) (nth 1 r) (nth 3 r))))
         (decoded (fn-scc-decode-tree (take count (nthcdr offset pool)))))
    (and
      (not (fn-scc-octet-listp pool))
      (natp offset)
      (<= (+ offset count) (len pool))
      (equal (car result) :ok)
      (not (and (equal (car decoded) :ok)
           (equal (fn-hdc-abstract (nth 1 result) pool) (cadr decoded))
           (equal (nth 2 result) (fn-scs-summary (cadr decoded)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Complete codec bridge: count-domain redundant proved then removed.
(defthm hdsst-codec-corrupt-offset
  (let* ((pool '(7 65)) (offset -1) (count 2)
         (r (fn-hds-model-run count (fn-hdc-begin offset count 17 '(23 7)) nil nil t pool))
         (result (mv-list 6 (fn-hds-result 0 (car r) (nth 1 r) (nth 3 r))))
         (decoded (fn-scc-decode-tree (take count (nthcdr offset pool)))))
    (and
      (fn-scc-octet-listp pool)
      (not (natp offset))
      (<= (+ offset count) (len pool))
      (equal (car result) :ok)
      (not (and (equal (car decoded) :ok)
           (equal (fn-hdc-abstract (nth 1 result) pool) (cadr decoded))
           (equal (nth 2 result) (fn-scs-summary (cadr decoded)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Complete codec bridge: count-domain redundant proved then removed.
(defthm hdsst-codec-corrupt-source-bound
  (let* ((pool '(6 1 2 1)) (offset 0) (count 5)
         (r (fn-hds-model-run count (fn-hdc-begin offset count 17 '(23 7)) nil nil t pool))
         (result (mv-list 6 (fn-hds-result 0 (car r) (nth 1 r) (nth 3 r))))
         (decoded (fn-scc-decode-tree (take count (nthcdr offset pool)))))
    (and
      (fn-scc-octet-listp pool)
      (natp offset)
      (not (<= (+ offset count) (len pool)))
      (equal (car result) :ok)
      (not (and (equal (car decoded) :ok)
           (equal (fn-hdc-abstract (nth 1 result) pool) (cadr decoded))
           (equal (nth 2 result) (fn-scs-summary (cadr decoded)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))

; Complete codec bridge: count-domain redundant proved then removed.
(defthm hdsst-codec-refused-result
  (let* ((pool '(0)) (offset 0) (count 0)
         (r (fn-hds-model-run count (fn-hdc-begin offset count 17 '(23 7)) nil nil t pool))
         (result (mv-list 6 (fn-hds-result 0 (car r) (nth 1 r) (nth 3 r))))
         (decoded (fn-scc-decode-tree (take count (nthcdr offset pool)))))
    (and
      (fn-scc-octet-listp pool)
      (natp offset)
      (<= (+ offset count) (len pool))
      (not (equal (car result) :ok))
      (not (and (equal (car decoded) :ok)
           (equal (fn-hdc-abstract (nth 1 result) pool) (cadr decoded))
           (equal (nth 2 result) (fn-scs-summary (cadr decoded)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (fuel s infos prefix usable pool)
                      (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool)))
           :in-theory (enable fn-hdc-coherent fn-hds-prefix-coherent
                              fn-hds-stack-correspondsp fn-hds-info-correspondsp
                              fn-hdc-abstract fn-hds-feed fn-hds-at
                              fn-hds-info-root fn-hds-info-leaf fn-hds-nil-byte
                              fn-hds-leaf-carry fn-scs-summary fn-scs-atom
                              fn-scs-atom-size fn-scs-octets fn-scs-cons
                              fn-scs-width fn-hdc-span fn-hdc-state
                              fn-hdc-tag-prefixp fn-hds-model-run fn-hds-result fn-hdc-result fn-scs-correspondsp))))
