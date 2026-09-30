; Exact carried size metadata for the actual byte-fed borrowed decoder.
; All recursive relations here are proof-only; ticks inspect fixed metadata.
(in-package "ACL2")
(include-book "history-decode-size")
(include-book "history-decode-refinement")
(include-book "history-symbol-normalize")
(local (include-book "arithmetic/top" :dir :system))

(defun-nx fn-hds-stack-correspondsp (infos nodes pool)
  (if (consp nodes)
      (and (consp infos)
           (fn-hds-info-correspondsp (car infos) (fn-hdc-abstract (car nodes) pool))
           (fn-hds-stack-correspondsp (cdr infos) (cdr nodes) pool))
    (and (null nodes) (null infos))))

(defthm fn-hds-correspondence-implies-root-carry
  (implies (fn-hds-info-correspondsp info value)
           (fn-scs-carryp (fn-hds-info-root info)))
  :hints (("Goal" :in-theory (e/d (fn-hds-info-correspondsp)
                                  (fn-scs-summary fn-scs-carryp)))))

; Empty matched prefix is represented by NIL. The first byte starts a fresh
; match; later bytes require the exact consumed prefix from the same span.
(defun-nx fn-hds-prefix-coherent (s prefix pool)
  (implies (and (eq (nth 0 s) :payload) (equal (nth 1 s) 4)
                (member-equal (nth 2 s) '(1 2)) (equal (nth 5 s) 3))
           (if (equal (nth 6 s) 3) (not prefix)
             (iff prefix
                  (equal (take (- 3 (nth 6 s)) (nthcdr (nth 4 s) pool))
                         (take (- 3 (nth 6 s)) '(78 73 76)))))))

(defthm fn-hds-begin-establishes-size-invariant-by-definition
  (and (fn-hds-stack-correspondsp
                  (mv-nth 1 (fn-hds-begin offset count epoch lease))
                  (nth 9 (mv-nth 0 (fn-hds-begin offset count epoch lease))) pool)
                (fn-hds-prefix-coherent
                  (mv-nth 0 (fn-hds-begin offset count epoch lease))
                  (mv-nth 2 (fn-hds-begin offset count epoch lease)) pool))
  :hints (("Goal" :in-theory (enable fn-hds-begin fn-hdc-begin fn-hdc-state
                                    fn-hds-stack-correspondsp fn-hds-prefix-coherent))))

(local
 (defthm fn-hds-source-relative-byte
   (implies (and (natp start) (natp i))
            (equal (nth i (nthcdr start pool)) (nth (+ start i) pool)))
   :hints (("Goal" :induct (nthcdr start pool)
            :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-hds-source-first-byte
   (implies (natp start)
            (equal (car (nthcdr start pool)) (nth start pool)))
   :hints (("Goal" :use ((:instance fn-hds-source-relative-byte (i 0)))
            :in-theory (e/d (nth) (nthcdr fn-hds-source-relative-byte))))))

(local
 (defthm fn-hds-source-second-byte
   (implies (natp start)
            (equal (cadr (nthcdr start pool)) (nth (+ 1 start) pool)))
   :hints (("Goal" :use ((:instance fn-hds-source-relative-byte (i 1)))
            :expand ((nth 1 (nthcdr start pool))
                     (nth 0 (cdr (nthcdr start pool))))
            :in-theory (disable nth nthcdr fn-hds-source-relative-byte)))))

(local
 (defthm fn-hds-take-one-by-definition
   (equal (take 1 xs) (list (car xs)))
   :hints (("Goal" :expand ((take 1 xs))
            :in-theory (enable take)))))

(local
 (defthm fn-hds-take-two-by-definition
   (equal (take 2 xs) (list (car xs) (cadr xs)))
   :hints (("Goal" :expand ((take 2 xs) (take 1 (cdr xs)))
            :in-theory (enable take)))))

(defthm fn-hds-feed-preserves-prefix-coherence
  (implies (and (fn-hdc-coherent s pool)
                (equal byte (nth (nth 7 s) pool))
                (fn-hds-prefix-coherent s prefix pool))
           (fn-hds-prefix-coherent
             (mv-nth 0 (fn-hds-feed byte s infos prefix usable))
             (mv-nth 2 (fn-hds-feed byte s infos prefix usable)) pool))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hds-prefix-coherent fn-hds-feed fn-hds-nil-byte
                              fn-hdc-coherent fn-hdc-feed fn-hdc-feed-raw
                              fn-hdc-move fn-hdc-finish-number fn-hdc-state
                              take nth)
                            (fn-hds-leaf-carry fn-hds-info-pair fn-hds-info-root
                             fn-hds-info-leaf fn-scs-carryp fn-hdc-number-feed
                             fn-hdc-number-begin fn-hdc-tag-prefixp
                             fn-hdc-tag-byte fn-hdc-payload-node)))))

(local
 (defthm fn-hds-octets-chars-length
   (equal (len (fn-scc-octets-chars bytes)) (len bytes))
   :hints (("Goal" :induct (len bytes)
            :in-theory (enable fn-scc-octets-chars)))))

(local
 (defthm fn-hds-octets-string-length
   (equal (length (coerce (fn-scc-octets-chars bytes) 'string)) (len bytes))
   :hints (("Goal" :in-theory (enable length)))))

(local
 (defthm fn-hds-suffix-length
   (implies (and (natp offset) (<= offset (len pool)))
            (equal (len (nthcdr offset pool)) (- (len pool) offset)))
   :hints (("Goal" :induct (nthcdr offset pool)
            :in-theory (enable nthcdr len)))))

(local
 (defthm fn-hds-take-length
   (implies (natp count) (equal (len (take count pool)) count))
   :hints (("Goal" :induct (take count pool)
            :in-theory (enable take len)))))

(local
 (defthm fn-hds-slice-octets
   (implies (and (fn-scc-octet-listp pool) (natp offset) (natp count)
                 (<= (+ offset count) (len pool)))
            (and (fn-scc-octet-listp (take count (nthcdr offset pool)))
                 (equal (len (take count (nthcdr offset pool))) count)))
   :hints (("Goal" :use ((:instance fn-scc-octet-listp-take
                                    (x (nthcdr offset pool)) (n count)))
            :do-not-induct t
            :in-theory (disable fn-scc-octet-listp-take fn-scc-octet-listp
                                take nthcdr)))))

; The alias premise is discharged from the consumed source-prefix invariant,
; not checked by reconstructing or interning the borrowed name at runtime.
(defthm fn-hds-span-carry-refines-normalized-value
  (let ((value (fn-hdc-abstract (fn-hdc-span op pkg offset count) pool)))
    (implies (and (member-equal op '(3 4 6))
                  (natp offset) (natp count) (fn-scc-octet-listp pool)
                  (<= (+ offset count) (len pool))
                  (implies (equal op 4) (iff nil-alias (null value))))
             (equal (fn-hds-leaf-carry (fn-hdc-span op pkg offset count) nil-alias)
                    (fn-scs-summary value))))
  :hints (("Goal" :do-not-induct t :cases ((member-equal pkg '(0 1 2)))
           :use ((:instance fn-hds-octets-leaf-carry-exact
                             (bytes (take count (nthcdr offset pool))))
                 (:instance fn-hds-string-leaf-carry-exact
                             (text (coerce (fn-scc-octets-chars
                                      (take count (nthcdr offset pool))) 'string)))
                 (:instance fn-hds-symbol-leaf-carry-exact
                             (sym (fn-scc-intern pkg
                                    (coerce (fn-scc-octets-chars
                                      (take count (nthcdr offset pool))) 'string)))))
           :in-theory (e/d (fn-hdc-abstract fn-hdc-span fn-scc-intern fn-hds-leaf-carry fn-hds-at)
                            (fn-scs-summary
                             fn-scc-octets-chars fn-hds-octets-leaf-carry-exact
                             fn-hds-string-leaf-carry-exact
                             fn-hds-symbol-leaf-carry-exact)))))

(local
 (defthm fn-hds-chars-octets-inverse
   (implies (fn-scc-octet-listp bytes)
            (equal (fn-scc-chars-octets (fn-scc-octets-chars bytes)) bytes))
   :hints (("Goal" :induct (len bytes)
            :in-theory (enable fn-scc-octet-listp fn-scc-octetp
                               fn-scc-octets-chars fn-scc-chars-octets)))))

(local
 (defthm fn-hds-code-char-ascii
 (implies (and (characterp c) (not (equal (char-code c) 0)))
  (equal (equal (code-char x) c) (equal x (char-code c))))
 :hints (("Goal" :cases ((fn-scc-octetp x))
          :use ((:instance char-code-code-char-is-identity (n x)))
          :in-theory (e/d (fn-scc-octetp) (char-code-code-char-is-identity))))))

(local
 (defthm fn-hds-chars-consp
   (iff (fn-scc-octets-chars xs) (consp xs))
   :hints (("Goal" :expand ((fn-scc-octets-chars xs))))))

(local
 (defthm fn-hds-nil-string-iff-octets
 (implies (true-listp bytes)
  (equal (equal (coerce (fn-scc-octets-chars bytes) 'string) "NIL")
         (equal bytes '(78 73 76))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance coerce-inverse-1 (x (fn-scc-octets-chars bytes)))
                (:instance fn-hds-octets-chars-length))
          :cases ((equal (coerce (fn-scc-octets-chars bytes) 'string) "NIL"))
          :expand ((fn-scc-octets-chars bytes)
                   (fn-scc-octets-chars (cdr bytes))
                   (fn-scc-octets-chars (cddr bytes)))
          :in-theory (e/d (len true-listp)
                          (fn-scc-octets-chars coerce-inverse-1 fn-hds-octets-chars-length))))))

(local
 (defthm fn-hds-source-third-byte
   (implies (natp start)
            (equal (caddr (nthcdr start pool)) (nth (+ 2 start) pool)))
   :hints (("Goal" :use ((:instance fn-hds-source-relative-byte (i 2)))
            :expand ((nth 2 (nthcdr start pool))
                     (nth 1 (cdr (nthcdr start pool)))
                     (nth 0 (cddr (nthcdr start pool))))
            :in-theory (disable nth nthcdr fn-hds-source-relative-byte)))))

(local
 (defthm fn-hds-take-three-by-definition
   (equal (take 3 xs) (list (car xs) (cadr xs) (caddr xs)))
   :hints (("Goal" :expand ((take 3 xs))
            :in-theory (enable take)))))

(defthm fn-hds-final-symbol-prefix-refines-nil-normalization
  (implies (and (fn-hdc-coherent s pool) (equal (nth 0 s) :payload)
                (equal (nth 1 s) 4) (equal (nth 6 s) 1)
                (fn-hds-prefix-coherent s prefix pool)
                (equal byte (nth (nth 7 s) pool)))
           (iff (fn-hds-nil-byte byte s prefix)
                (null (fn-hdc-abstract
                        (fn-hdc-span 4 (nth 2 s) (nth 4 s) (nth 5 s)) pool))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hds-take-length (count (nth 5 s))
                   (pool (nthcdr (nth 4 s) pool)))
                 (:instance fn-hdsn-intern-nil (pkg (nth 2 s))
                   (name (coerce (fn-scc-octets-chars
                            (take (nth 5 s) (nthcdr (nth 4 s) pool))) 'string)))
                 (:instance fn-hds-nil-string-iff-octets
                   (bytes (take (nth 5 s) (nthcdr (nth 4 s) pool)))))
           :in-theory (e/d (fn-hdc-coherent fn-hds-prefix-coherent
                            fn-hds-nil-byte fn-hdc-abstract fn-hdc-span)
                           (fn-scc-intern fn-scc-octets-chars take nthcdr
                            fn-hdc-tag-prefixp fn-hdsn-intern-nil
                            fn-hds-nil-string-iff-octets fn-hds-slice-octets fn-hds-take-length)))))

(local
 (defthm fn-hds-source-octet
   (implies (and (fn-scc-octet-listp pool) (natp index) (< index (len pool)))
            (fn-scc-octetp (nth index pool)))
   :hints (("Goal" :induct (nth index pool)
            :in-theory (enable nth fn-scc-octet-listp len)))))

(local
 (defthm fn-hds-empty-symbol-is-not-nil
   (implies (and (member-equal pkg '(0 1 2)) (natp offset))
            (fn-hdc-abstract (fn-hdc-span 4 pkg offset 0) pool))
   :hints (("Goal" :use ((:instance fn-hdsn-intern-nil (name "")))
            :in-theory (e/d (fn-hdc-abstract fn-hdc-span)
                             (fn-scc-intern fn-hdsn-intern-nil))))))

(local
 (defthm fn-hds-number-scalar-field
   (implies (fn-hdc-numberp number) (natp (cadr number)))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn-hdc-numberp)))))

(local
 (defthm fn-hds-state-number-fields
   (implies (fn-hdc-statep s)
            (and (natp (cadr (nth 3 s))) (posp (caddr (nth 3 s)))))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :use fn-hdc-state-fields
            :in-theory (e/d (fn-hdc-numberp)
                             (fn-hdc-state-fields fn-hdc-statep nth))))))

(local
 (defthm fn-hds-package-index-membership
   (implies (and (natp pkg) (< pkg 3)) (member-equal pkg '(0 1 2)))
   :hints (("Goal" :cases ((equal pkg 0) (equal pkg 1))
            :in-theory (enable member-equal)))
   :rule-classes (:rewrite :forward-chaining)))

(local
 (defthm fn-hds-empty-symbol-carry-exact
   (implies (and (natp pkg) (< pkg 3) (natp offset))
     (equal (fn-hds-leaf-carry (fn-hdc-span 4 pkg offset 0) nil)
            (fn-scs-summary (fn-hdc-abstract (fn-hdc-span 4 pkg offset 0) pool))))
   :hints (("Goal" :use ((:instance fn-hds-symbol-leaf-carry-exact
                           (count 0) (nil-alias nil) (sym (fn-scc-intern pkg "")))
                         (:instance fn-hdsn-intern-name (name ""))
                         (:instance fn-hdsn-intern-nil (name "")))
            :in-theory (e/d (fn-hdc-abstract fn-hdc-span)
                            (fn-hds-leaf-carry fn-scs-summary fn-scc-intern
                             fn-hds-symbol-leaf-carry-exact fn-hdsn-intern-nil
                             fn-hdsn-intern-name))))))

(defthm fn-hds-feed-preserves-annotation-stack
  (implies (and (fn-hdc-coherent s pool) (fn-scc-octet-listp pool)
                (<= (nth 8 s) (len pool))
                (equal byte (nth (nth 7 s) pool))
                (fn-hds-prefix-coherent s prefix pool)
                (fn-hds-stack-correspondsp infos (nth 9 s) pool)
                (mv-nth 3 (fn-hds-feed byte s infos prefix usable)))
           (fn-hds-stack-correspondsp
             (mv-nth 1 (fn-hds-feed byte s infos prefix usable))
             (nth 9 (mv-nth 0 (fn-hds-feed byte s infos prefix usable))) pool))
  :hints (("Goal" :do-not-induct t
           :use (fn-hds-final-symbol-prefix-refines-nil-normalization
                 (:instance fn-hds-source-octet (index (nth 7 s)))
                 fn-hdc-state-fields)
           :in-theory (e/d (fn-hds-stack-correspondsp fn-hds-feed fn-hds-at fn-hds-nil-byte
                            fn-hdc-coherent fn-hdc-feed fn-hdc-feed-raw
                            fn-hdc-move fn-hdc-finish-number fn-hdc-state
                            fn-hdc-payload-node fn-hdc-numberp fn-hdc-number-feed)
                           (fn-hds-info-correspondsp fn-hds-info-pair
                            fn-hds-info-root fn-hds-info-leaf fn-hds-leaf-carry
                            fn-scs-carryp fn-scs-summary
                            fn-hdc-number-begin fn-hdc-tag-prefixp
                            fn-hdc-tag-byte fn-hdc-span fn-hdc-atom fn-hdc-pair
                            (:executable-counterpart fn-hdc-atom)
                            (:executable-counterpart fn-hds-info-leaf)
                            fn-hds-prefix-coherent
                            fn-hds-final-symbol-prefix-refines-nil-normalization
                            fn-hds-source-octet fn-hdc-state-fields)))))

(in-theory (disable fn-hds-stack-correspondsp fn-hds-prefix-coherent))


; Ghost scheduler fold: every step is the actual additive public feed API.
; It stops at terminal parser states and preserves all four resumable values.
(defun-nx fn-hds-model-run (fuel s infos prefix usable pool)
  (if (or (zp fuel) (member-eq (nth 0 s) '(:done :refused)))
      (list s infos prefix usable)
    (mv-let (next next-infos next-prefix next-usable)
      (fn-hds-feed (nth (nth 7 s) pool) s infos prefix usable)
      (fn-hds-model-run (1- fuel) next next-infos next-prefix next-usable pool))))

(defthm fn-hds-model-run-parser-is-actual
  (equal (car (fn-hds-model-run fuel s infos prefix usable pool))
         (fn-hdc-model-run fuel s pool))
  :hints (("Goal" :induct (fn-hds-model-run fuel s infos prefix usable pool)
           :in-theory (e/d (fn-hds-model-run fn-hdc-model-run)
                            (fn-hds-feed fn-hdc-feed)))))

(defthm fn-hds-model-run-unusable-stays-unusable
  (implies (not usable)
           (not (nth 3 (fn-hds-model-run fuel s infos prefix usable pool))))
  :hints (("Goal" :induct (fn-hds-model-run fuel s infos prefix usable pool)
           :in-theory (e/d (fn-hds-model-run) (fn-hds-feed)))))

(defthm fn-hds-model-run-preserves-source-end
  (equal (nth 8 (car (fn-hds-model-run fuel s infos prefix usable pool)))
         (nth 8 s))
  :hints (("Goal" :in-theory (disable fn-hds-model-run fn-hdc-model-run))))

(local
 (defthm fn-hds-active-source-octet
   (implies (and (fn-hdc-coherent s pool) (fn-scc-octet-listp pool)
                 (<= (nth 8 s) (len pool))
                 (not (member-eq (nth 0 s) '(:done :refused))))
            (fn-scc-octetp (nth (nth 7 s) pool)))
   :hints (("Goal" :use ((:instance fn-hds-source-octet (index (nth 7 s))))
            :in-theory (e/d (fn-hdc-coherent)
                            (fn-hds-source-octet fn-hdc-statep fn-hdc-tag-prefixp
                             fn-scc-octet-listp fn-scc-octetp))))))

(defthm fn-hds-model-run-preserves-size-invariant
  (let* ((r (fn-hds-model-run fuel s infos prefix usable pool))
         (next (car r)))
    (implies (and (fn-hdc-coherent s pool) (fn-scc-octet-listp pool)
                  (<= (nth 8 s) (len pool))
                  (fn-hds-prefix-coherent s prefix pool)
                  (fn-hds-stack-correspondsp infos (nth 9 s) pool)
                  (nth 3 r))
             (and (fn-hds-prefix-coherent next (nth 2 r) pool)
                  (fn-hds-stack-correspondsp (nth 1 r) (nth 9 next) pool))))
  :hints (("Goal" :induct (fn-hds-model-run fuel s infos prefix usable pool)
           :in-theory (e/d (fn-hds-model-run)
                            (fn-hds-feed fn-hdc-feed fn-hdc-coherent
                             fn-hds-prefix-coherent fn-hds-stack-correspondsp
                             fn-hdc-model-run fn-scc-octet-listp fn-scc-octetp)))
          ("Subgoal *1/2"
           :use (fn-hds-active-source-octet
                 (:instance fn-hds-model-run-unusable-stays-unusable
                   (fuel (1- fuel))
                   (s (mv-nth 0 (fn-hds-feed (nth (nth 7 s) pool) s infos prefix usable)))
                   (infos (mv-nth 1 (fn-hds-feed (nth (nth 7 s) pool) s infos prefix usable)))
                   (prefix (mv-nth 2 (fn-hds-feed (nth (nth 7 s) pool) s infos prefix usable)))
                   (usable (mv-nth 3 (fn-hds-feed (nth (nth 7 s) pool) s infos prefix usable))))
                 (:instance fn-hds-feed-preserves-prefix-coherence
                   (byte (nth (nth 7 s) pool)))
                 (:instance fn-hds-feed-preserves-annotation-stack
                   (byte (nth (nth 7 s) pool)))))))

(in-theory (disable fn-hds-model-run))


; Success exposes exactly the original completed descriptor and its carry.
; No claim about source authentication or row metadata is made here.
(defthm fn-hds-result-preserves-root-correspondence
  (implies (and (fn-hds-stack-correspondsp infos (nth 9 s) pool)
                (equal (mv-nth 0 (fn-hds-result n s infos usable)) :ok))
           (and (equal (mv-nth 1 (fn-hds-result n s infos usable))
                       (cadr (fn-hdc-result s)))
                (equal (mv-nth 2 (fn-hds-result n s infos usable))
                       (fn-scs-summary
                        (fn-hdc-abstract
                         (mv-nth 1 (fn-hds-result n s infos usable)) pool)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hds-result fn-hdc-result fn-hds-stack-correspondsp
                            fn-hds-info-correspondsp)
                           (fn-hds-info-root fn-hds-select-fields fn-scs-summary
                            fn-hdc-abstract)))))

(local
 (defthm fn-hds-empty-exposure-fields-by-definition
   (fn-scs-correspondsp nil (fn-hdc-abstract nil pool))
   :hints (("Goal" :in-theory (enable fn-hdc-abstract fn-scs-correspondsp)))))

(defthm fn-hds-result-preserves-selected-fields
  (implies (and (not (zp n))
                (fn-hds-stack-correspondsp infos (nth 9 s) pool))
           (fn-scs-correspondsp
            (mv-nth 3 (fn-hds-result n s infos usable))
            (fn-hdc-abstract
             (mv-nth 1 (fn-hds-result n s infos usable)) pool)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hds-select-fields-preserves-correspondence
                   (info (car infos))
                   (xs (fn-hdc-abstract (car (nth 9 s)) pool))))
           :in-theory (e/d (fn-hds-result fn-hds-stack-correspondsp)
                           (fn-hds-info-correspondsp fn-hds-info-root
                            fn-hds-select-fields fn-scs-correspondsp
                            fn-hds-select-fields-preserves-correspondence
                            fn-hdc-abstract)))))


; Arbitrary scheduler partitions preserve all annotations and the unusable bit,
; not just the projection to the parser. No quantum exhaustion truncates data.
(defthm fn-hds-model-run-fuel-partition
  (implies (and (natp first) (natp second))
    (let ((mid (fn-hds-model-run first s infos prefix usable pool)))
      (equal (fn-hds-model-run (+ first second) s infos prefix usable pool)
             (fn-hds-model-run second (nth 0 mid) (nth 1 mid)
                               (nth 2 mid) (nth 3 mid) pool))))
  :hints (("Goal" :induct (fn-hds-model-run first s infos prefix usable pool)
           :in-theory (e/d (fn-hds-model-run)
                            (fn-hds-feed fn-hds-model-run-parser-is-actual
                             fn-hdc-model-run)))))


; Complete-source bridge to the current codec. The fold is ghost vocabulary;
; the served producer obtains the same parser/annotations by bounded feeds.
(defthm fn-hds-completed-root-refines-current-codec
  (let* ((initial (fn-hdc-begin offset count epoch lease))
         (r (fn-hds-model-run count initial nil nil t pool))
         (s (car r)) (infos (nth 1 r)) (usable (nth 3 r))
         (result (mv-list 6 (fn-hds-result n s infos usable)))
         (decoded (fn-scc-decode-tree (take count (nthcdr offset pool)))))
    (implies (and (fn-scc-octet-listp pool) (natp offset)
                  (<= (+ offset count) (len pool)) (equal (car result) :ok))
             (and (equal (car decoded) :ok)
                  (equal (fn-hdc-abstract (nth 1 result) pool) (cadr decoded))
                  (equal (nth 2 result) (fn-scs-summary (cadr decoded))))))
  :hints (("Goal" :do-not-induct t :cases ((natp count))
           :use ((:instance fn-hdc-begin-coherent)
                 (:instance fn-hds-begin-establishes-size-invariant-by-definition)
                 (:instance fn-hds-model-run-preserves-size-invariant
                   (fuel count) (s (fn-hdc-begin offset count epoch lease))
                   (infos nil) (prefix nil) (usable t))
                 (:instance fn-hds-result-preserves-root-correspondence
                   (s (car (fn-hds-model-run count (fn-hdc-begin offset count epoch lease)
                                             nil nil t pool)))
                   (infos (nth 1 (fn-hds-model-run count (fn-hdc-begin offset count epoch lease)
                                                  nil nil t pool)))
                   (usable (nth 3 (fn-hds-model-run count (fn-hdc-begin offset count epoch lease)
                                                   nil nil t pool))))
                 (:instance fn-hdc-current-codec-refinement))
           :in-theory (e/d (fn-hds-begin fn-hdc-begin fn-hdc-state fn-hdc-abstract-result fn-hdc-result fn-hds-result)
                            (fn-hds-model-run fn-hdc-model-run
                             fn-hdc-abstract fn-hds-info-root fn-hds-select-fields
                             fn-scs-summary fn-scc-decode-tree fn-hdc-coherent
                             fn-hds-stack-correspondsp fn-hds-prefix-coherent)))
          ("Subgoal 2"
           :expand ((:free (fuel s infos prefix usable pool)
                       (fn-hds-model-run fuel s infos prefix usable pool))
                    (:free (fuel s pool) (fn-hdc-model-run fuel s pool))))))
