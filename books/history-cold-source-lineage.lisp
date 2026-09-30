; Proof-only source lineage for the actual borrowed history decoder.
; No served node validation, extra parser implementation or new input ceiling.
(in-package "ACL2")
(include-book "history-decode-lineage-model")
(include-book "history-cold-record-cursor")
(local (include-book "arithmetic/top" :dir :system))

; A remaining-digit potential proves the existing 255-digit codec bound.
; This recursive exponent is ghost vocabulary and never runs in a feed.
(defun-nx fn-hdcl-number-budgetp (c)
  (and (fn-hdc-numberp c)
       (< (+ (cadr c) (* (caddr c) (1- (expt 256 (car c)))))
          *fn-hrsc-integer-bound*)))
(local
 (defthm fn-hdcl-expt-256-monotone-unfolds
   (implies (and (natp n) (natp k) (<= n k))
            (<= (expt 256 n) (expt 256 k)))
   :rule-classes nil
   :hints (("Goal" :induct (expt 256 k)
     :in-theory (enable expt)))))
(defthm fn-hdcl-number-begin-establishes-codec-budget
  (implies (fn-scc-octetp digits)
           (fn-hdcl-number-budgetp (fn-hdc-number-begin digits)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdc-number-begin-valid
          (:instance fn-hdcl-expt-256-monotone-unfolds (n digits) (k 255)))
    :in-theory (e/d (fn-hdcl-number-budgetp fn-hdc-number-begin fn-scc-octetp)
                    (expt fn-hdc-numberp)))))
(defthm fn-hdcl-number-feed-preserves-codec-budget
  (implies (and (fn-hdcl-number-budgetp c) (fn-scc-octetp byte))
           (fn-hdcl-number-budgetp (fn-hdc-number-feed byte c)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdc-number-feed-valid
          (:instance *-preserves->=-for-nonnegatives
            (x1 255) (x2 byte) (y1 (caddr c)) (y2 (caddr c))))
    :expand ((expt 256 (car c)))
    :in-theory (e/d (fn-hdcl-number-budgetp fn-hdc-numberp fn-hdc-number-feed fn-scc-octetp natp posp)
                    (expt *-preserves->=-for-nonnegatives fn-hdc-number-feed-valid
                     <-*-left-cancel <-*-right-cancel)))))
(local
 (defthm fn-hdcl-digits-width-by-expt-unfolds
   (implies (and (natp n) (natp k) (< n (expt 256 k)))
            (<= (len (fn-scc-le-digits n)) k))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scc-u64 n k)
     :in-theory (e/d (fn-scc-u64 fn-scc-le-digits expt) (floor mod))))))
(local
 (defthm fn-hdcl-codec-bound-implies-encodable-unfolds
   (implies (fn-hrsc-codecp n) (fn-scc-nat-encodablep n))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hdcl-digits-width-by-expt-unfolds (k 255)))
     :in-theory (e/d (fn-hrsc-codecp fn-scc-nat-encodablep) (fn-scc-le-digits))))))
(defthm fn-hdcl-terminal-number-is-scalar-codec-domain
  (implies (and (fn-hdcl-number-budgetp c) (equal (car c) 0))
           (and (fn-hrsc-codecp (cadr c))
                (fn-hrsc-domainp (cadr c))
                (fn-hrsc-domainp (- -1 (cadr c)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-hdcl-codec-bound-implies-encodable-unfolds (n (cadr c))))
    :in-theory (enable fn-hdcl-number-budgetp fn-hdc-numberp
                       fn-hrsc-codecp fn-hrsc-domainp fn-scc-atomp))))
; Weight charges a pair constructor and every opaque payload byte. It is a
; logical lower bound on bytes consumed by the actual postfix parser.
(defun-nx fn-hdcl-node-weight (node)
  (declare (xargs :measure (acl2-count node)))
  (cond ((not (consp node)) 0)
        ((eq (car node) :pair)
         (+ 1 (fn-hdcl-node-weight (cadr node)) (fn-hdcl-node-weight (caddr node))))
        ((and (eq (car node) :span) (equal (cadr node) 6))
         (+ 1 (nfix (nth 4 node))))
        (t 1)))
(defun-nx fn-hdcl-node-lineagep (node pool)
  (declare (xargs :measure (acl2-count node)))
  (and (fn-hrcur-dos-domainp node pool)
       (case (car node)
         (:atom (fn-hrsc-domainp (cadr node)))
         (:pair (and (fn-hdcl-node-lineagep (cadr node) pool)
                     (fn-hdcl-node-lineagep (caddr node) pool)))
         (:span (or (equal (cadr node) 4) (equal (caddr node) 0)))
         (otherwise nil))))
(local
 (defthm fn-hdcl-take-length-unfolds
   (equal (len (take n xs)) (nfix n))
   :hints (("Goal" :induct (take n xs) :in-theory (enable take)))))
(local
 (defthm fn-hdcl-node-weight-natural-unfolds
   (natp (fn-hdcl-node-weight node))
   :hints (("Goal" :induct (fn-hdcl-node-weight node)
     :in-theory (enable fn-hdcl-node-weight)))))
(defthm fn-hdcl-abstract-list-length-bounded-by-node-weight
  (implies (fn-hdcl-node-lineagep node pool)
           (<= (len (fn-hdc-abstract node pool)) (fn-hdcl-node-weight node)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-hdcl-node-lineagep node pool)
    :in-theory (e/d (fn-hdcl-node-lineagep fn-hdcl-node-weight fn-hdc-abstract
                     fn-hrcur-dos-domainp fn-hrcur-field fn-scc-intern)
                    (fn-scc-atomp fn-hrsc-domainp fn-scc-octets-chars nthcdr take)))))
(defthm fn-hdcl-weighted-source-establishes-cold-domain
  (implies (and (fn-hdcl-node-lineagep node pool)
                (< (fn-hdcl-node-weight node) *fn-hrcur-u64-bound*))
           (fn-hrcur-cold-domainp node pool))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hdcl-node-lineagep node pool)
    :in-theory (e/d (fn-hdcl-node-lineagep fn-hdcl-node-weight
                     fn-hrcur-cold-domainp fn-hrcur-field)
                    (fn-hrcur-dos-domainp fn-hdc-abstract fn-hrsc-domainp)))
    ("Subgoal *1/5.1"
     :use ((:instance fn-hdcl-abstract-list-length-bounded-by-node-weight))
     :in-theory (e/d (fn-hdcl-node-lineagep fn-hdcl-node-weight
                       fn-hrcur-cold-domainp fn-hrcur-field)
                      (fn-hrcur-dos-domainp fn-hdc-abstract fn-hrsc-domainp
                       fn-hdcl-abstract-list-length-bounded-by-node-weight)))))
; Consumed source bytes pay for every retained constructor and opaque byte.
; The pending payload charge grows one at a time, rather than charging its
; entire announced length before those source bytes have been read.
(defun-nx fn-hdcl-stack-weight (stack)
  (if (consp stack)
      (+ (fn-hdcl-node-weight (car stack)) (fn-hdcl-stack-weight (cdr stack)))
    0))
(defun-nx fn-hdcl-payload-charge (s)
  (if (eq (nth 0 s) :payload) (+ 1 (- (nth 5 s) (nth 6 s))) 0))
(defun-nx fn-hdcl-weighted-statep (s offset)
  (and (fn-hdc-statep s) (natp offset) (<= offset (nth 7 s))
       (true-listp (nth 9 s))
       (if (eq (nth 0 s) :payload)
           (and (member-equal (nth 1 s) '(3 4 6))
                (< 0 (nth 6 s)) (<= (nth 6 s) (nth 5 s))
                (equal (nth 7 s) (+ (nth 4 s) (- (nth 5 s) (nth 6 s)))))
         t)
       (<= (+ (fn-hdcl-stack-weight (nth 9 s)) (fn-hdcl-payload-charge s))
           (- (nth 7 s) offset))))
(local
 (defthm fn-hdcl-stack-weight-natural-unfolds
   (natp (fn-hdcl-stack-weight stack))
   :hints (("Goal" :induct (fn-hdcl-stack-weight stack)
     :in-theory (enable fn-hdcl-stack-weight)))))
(local
 (defthm fn-hdcl-constructor-weight-unfolds
   (and (equal (fn-hdcl-node-weight (cons :atom tail)) 1)
        (equal (fn-hdcl-node-weight (list* :pair a d tail))
               (+ 1 (fn-hdcl-node-weight a) (fn-hdcl-node-weight d)))
        (equal (fn-hdcl-node-weight (list* :span op pkg start count tail))
               (if (equal op 6) (+ 1 (nfix count)) 1))
        (equal (fn-hdcl-node-weight (fn-hdc-atom v)) 1)
        (equal (fn-hdcl-node-weight (fn-hdc-pair a d))
               (+ 1 (fn-hdcl-node-weight a) (fn-hdcl-node-weight d)))
        (equal (fn-hdcl-node-weight (fn-hdc-span op pkg start count))
               (if (equal op 6) (+ 1 (nfix count)) 1)))
   :hints (("Goal" :in-theory (enable fn-hdcl-node-weight
      fn-hdc-atom fn-hdc-pair fn-hdc-span)))))
(defthm fn-hdcl-begin-establishes-consumed-byte-budget
  (implies (and (natp offset) (natp length))
           (fn-hdcl-weighted-statep (fn-hdc-begin offset length epoch lease) offset))
  :rule-classes nil
  :hints (("Goal" :use fn-hdc-begin-valid
    :in-theory (e/d (fn-hdcl-weighted-statep
     fn-hdcl-stack-weight fn-hdcl-payload-charge fn-hdc-begin fn-hdc-state)
     (fn-hdc-begin-valid fn-hdc-statep)))))
(defthm fn-hdcl-finish-number-preserves-consumed-byte-budget
  (implies (and (fn-hdc-statep s) (natp value) (natp op) (< op 8)
                (natp pkg) (< pkg 3) (natp pos) (<= pos (nth 8 s))
                (natp offset) (< offset pos) (true-listp stack)
                (<= (fn-hdcl-stack-weight stack) (- (- pos offset) 1)))
           (fn-hdcl-weighted-statep
             (fn-hdc-finish-number value op pkg pos stack s) offset))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdc-state-fields fn-hdc-finish-number-valid)
    :in-theory (e/d (fn-hdcl-weighted-statep fn-hdcl-payload-charge
                      fn-hdcl-stack-weight fn-hdc-finish-number fn-hdc-move fn-hdc-state)
                     (fn-hdc-state-fields fn-hdc-finish-number-valid fn-hdcl-node-weight)))))
(local
 (defthm fn-hdcl-payload-node-weight-unfolds
   (implies (natp count)
            (<= (fn-hdcl-node-weight (fn-hdc-payload-node op pkg start count number))
                (+ 1 count)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-hdc-payload-node)))))
(defthm fn-hdcl-feed-raw-preserves-consumed-byte-budget
  (implies (and (fn-hdcl-weighted-statep s offset) (fn-scc-octetp byte))
           (fn-hdcl-weighted-statep (fn-hdc-feed-raw byte s) offset))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdc-state-fields fn-hdc-feed-raw-valid
          (:instance fn-hdc-number-feed-valid (c (nth 3 s))))
    :in-theory (e/d (fn-hdcl-weighted-statep fn-hdcl-payload-charge
       fn-hdcl-stack-weight fn-hdc-feed-raw fn-hdc-finish-number fn-hdc-move
       fn-hdc-state fn-scc-octetp fn-hdc-numberp)
      (fn-hdc-state-fields fn-hdc-feed-raw-valid fn-hdc-number-feed-valid
       fn-hdcl-node-weight fn-hdc-number-feed fn-hdc-payload-node)))))
(local
 (defthm fn-hdcl-terminal-mode-preserves-byte-budget-unfolds
   (implies (and (fn-hdcl-weighted-statep s offset)
                 (member-eq mode '(:done :refused)))
            (fn-hdcl-weighted-statep (cons mode (cdr s)) offset))
   :hints (("Goal" :use (fn-hdc-state-fields fn-hdc-new-mode-valid)
    :in-theory (e/d (fn-hdcl-weighted-statep fn-hdcl-payload-charge)
     (fn-hdc-state-fields fn-hdc-new-mode-valid))))))
(defthm fn-hdcl-feed-preserves-consumed-byte-budget
  (implies (and (fn-hdcl-weighted-statep s offset) (fn-scc-octetp byte))
           (fn-hdcl-weighted-statep (fn-hdc-feed byte s) offset))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use fn-hdcl-feed-raw-preserves-consumed-byte-budget
    :in-theory (e/d (fn-hdc-feed fn-hdcl-weighted-statep)
      (fn-hdc-feed-raw fn-hdcl-payload-charge fn-hdcl-stack-weight)))))
(defun-nx fn-hdcl-numeric-statep (s)
  (and (fn-hdc-statep s)
       (implies (eq (nth 0 s) :digits)
                (fn-hdcl-number-budgetp (nth 3 s)))))
(defthm fn-hdcl-begin-establishes-numeric-budget
  (implies (and (natp offset) (natp length))
           (fn-hdcl-numeric-statep (fn-hdc-begin offset length epoch lease)))
  :rule-classes nil
  :hints (("Goal" :use fn-hdc-begin-valid
    :in-theory (e/d (fn-hdcl-numeric-statep fn-hdc-begin fn-hdc-state)
       (fn-hdc-begin-valid fn-hdc-statep)))))
(defthm fn-hdcl-feed-raw-preserves-numeric-budget
  (implies (and (fn-hdcl-numeric-statep s) (fn-scc-octetp byte))
           (fn-hdcl-numeric-statep (fn-hdc-feed-raw byte s)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdc-state-fields fn-hdc-feed-raw-valid
          (:instance fn-hdcl-number-begin-establishes-codec-budget (digits byte))
          (:instance fn-hdcl-number-feed-preserves-codec-budget (c (nth 3 s))))
    :in-theory (e/d (fn-hdcl-numeric-statep fn-hdc-feed-raw
       fn-hdc-finish-number fn-hdc-move fn-hdc-state fn-scc-octetp)
      (fn-hdc-state-fields fn-hdc-feed-raw-valid fn-hdcl-number-budgetp
       fn-hdc-number-feed fn-hdc-number-begin)))))
(defthm fn-hdcl-feed-preserves-numeric-budget
  (implies (and (fn-hdcl-numeric-statep s) (fn-scc-octetp byte))
           (fn-hdcl-numeric-statep (fn-hdc-feed byte s)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdcl-feed-raw-preserves-numeric-budget fn-hdc-feed-valid)
    :in-theory (e/d (fn-hdcl-numeric-statep fn-hdc-feed)
      (fn-hdc-feed-raw fn-hdcl-number-budgetp fn-hdc-statep)))))
; Scalar and package lineage is independent of source-page bytes. Existing
; parsed-node shape/span attribution intersects this carry at the source join.
(defun-nx fn-hdcl-scalar-lineagep (node)
  (declare (xargs :measure (acl2-count node)))
  (case (car node)
    (:atom (fn-hrsc-domainp (cadr node)))
    (:pair (and (fn-hdcl-scalar-lineagep (cadr node))
                (fn-hdcl-scalar-lineagep (caddr node))))
    (:span (or (equal (cadr node) 4) (equal (caddr node) 0)))
    (otherwise nil)))
(defun-nx fn-hdcl-scalar-stackp (stack)
  (if (consp stack)
      (and (fn-hdcl-scalar-lineagep (car stack)) (fn-hdcl-scalar-stackp (cdr stack)))
    (null stack)))
(defun-nx fn-hdcl-scalar-statep (s)
  (and (fn-hdcl-numeric-statep s) (fn-hdcl-scalar-stackp (nth 9 s))
       (implies (eq (nth 0 s) :package) (equal (nth 1 s) 4))
       (implies (member-eq (nth 0 s) '(:length :digits :payload))
                (or (equal (nth 1 s) 4) (equal (nth 2 s) 0)))))
(local
 (defthm fn-hdcl-scalar-constructor-lineage-unfolds
   (and (equal (fn-hdcl-scalar-lineagep (fn-hdc-atom v)) (fn-hrsc-domainp v))
        (equal (fn-hdcl-scalar-lineagep (fn-hdc-pair a d))
          (and (fn-hdcl-scalar-lineagep a) (fn-hdcl-scalar-lineagep d)))
        (equal (fn-hdcl-scalar-lineagep (fn-hdc-span op pkg start count))
          (or (equal op 4) (equal pkg 0))))
   :hints (("Goal" :in-theory (enable fn-hdcl-scalar-lineagep
      fn-hdc-atom fn-hdc-pair fn-hdc-span)))))
(defthm fn-hdcl-begin-establishes-scalar-lineage
  (implies (and (natp offset) (natp length))
           (fn-hdcl-scalar-statep (fn-hdc-begin offset length epoch lease)))
  :rule-classes nil
  :hints (("Goal" :use fn-hdcl-begin-establishes-numeric-budget
    :in-theory (e/d (fn-hdcl-scalar-statep fn-hdcl-scalar-stackp fn-hdc-begin fn-hdc-state)
       (fn-hdcl-numeric-statep)))))
(local
 (defthm fn-hdcl-fed-terminal-number-domain-unfolds
   (implies (and (fn-hdcl-number-budgetp c) (fn-scc-octetp byte)
                 (equal (car (fn-hdc-number-feed byte c)) 0))
            (and (fn-hrsc-domainp (cadr (fn-hdc-number-feed byte c)))
                 (fn-hrsc-domainp (- -1 (cadr (fn-hdc-number-feed byte c))))))
   :hints (("Goal" :do-not-induct t
     :use (fn-hdcl-number-feed-preserves-codec-budget
           (:instance fn-hdcl-terminal-number-is-scalar-codec-domain
             (c (fn-hdc-number-feed byte c))))
     :in-theory (disable fn-hdcl-number-budgetp fn-hdc-number-feed fn-hrsc-domainp)))))
(local
 (defthm fn-hdcl-payload-scalar-lineage-unfolds
   (implies (or (equal op 4) (equal pkg 0))
            (fn-hdcl-scalar-lineagep (fn-hdc-payload-node op pkg start count number)))
   :hints (("Goal" :in-theory (enable fn-hdc-payload-node fn-hdcl-scalar-lineagep fn-hdc-atom fn-hdc-span)))))
(local
 (defthm fn-hdcl-character-is-scalar-domain-unfolds
   (implies (fn-scc-octetp byte) (fn-hrsc-domainp (code-char byte)))
   :hints (("Goal" :in-theory (enable fn-scc-octetp fn-hrsc-domainp fn-scc-atomp)))))
(defthm fn-hdcl-feed-raw-preserves-scalar-lineage
  (implies (and (fn-hdcl-scalar-statep s) (fn-scc-octetp byte))
           (fn-hdcl-scalar-statep (fn-hdc-feed-raw byte s)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdc-state-fields fn-hdcl-feed-raw-preserves-numeric-budget
          (:instance fn-hdc-number-feed-valid (c (nth 3 s)))
          (:instance fn-hdcl-fed-terminal-number-domain-unfolds (c (nth 3 s))))
    :in-theory (e/d (fn-hdcl-scalar-statep fn-hdcl-numeric-statep fn-hdcl-scalar-stackp
       fn-hdcl-scalar-lineagep fn-hdc-feed-raw fn-hdc-finish-number fn-hdc-move fn-hdc-state
       fn-scc-octetp fn-hdc-numberp)
      (fn-hdc-state-fields fn-hdcl-number-budgetp fn-hdc-number-feed fn-hdc-number-begin
       fn-hdc-payload-node fn-hdcl-fed-terminal-number-domain-unfolds
       fn-hdc-number-feed-valid fn-hrsc-domainp fn-scc-atomp)))))
(defthm fn-hdcl-feed-preserves-scalar-lineage
  (implies (and (fn-hdcl-scalar-statep s) (fn-scc-octetp byte))
           (fn-hdcl-scalar-statep (fn-hdc-feed byte s)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdcl-feed-raw-preserves-scalar-lineage fn-hdcl-feed-preserves-numeric-budget)
    :in-theory (e/d (fn-hdcl-scalar-statep fn-hdc-feed)
      (fn-hdc-feed-raw fn-hdcl-numeric-statep fn-hdcl-scalar-stackp)))))
(defthm fn-hdcl-feed-established-active-position
  (implies (and (fn-hdc-statep s) (fn-scc-octetp byte))
           (let ((next (fn-hdc-feed byte s)))
             (or (member-eq (nth 0 next) '(:done :refused))
                 (< (nth 7 next) (nth 8 next)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdc-feed-raw-valid (:instance fn-hdc-state-fields (s (fn-hdc-feed-raw byte s))))
    :in-theory (e/d (fn-hdc-feed)
      (fn-hdc-feed-raw fn-hdc-statep fn-hdc-state-fields fn-hdc-feed-raw-valid)))))
; Node extents are carried separately from canonical scalar width and weight.
; Only new nodes are allocated by a feed; retained descendants are borrowed.
(defun-nx fn-hdcl-borrowed-statep (s)
  (and (fn-hdc-statep s) (fn-hdc-stack-in-poolp (nth 9 s) (nth 8 s))
       (implies (eq (nth 0 s) :payload)
                (<= (+ (nth 4 s) (nth 5 s)) (nth 8 s)))))
(local
 (defthm fn-hdcl-constructor-pool-bounds-unfolds
   (and (fn-hdc-node-in-poolp (list :atom v) end)
        (equal (fn-hdc-node-in-poolp (list :pair a d) end)
          (and (fn-hdc-node-in-poolp a end) (fn-hdc-node-in-poolp d end)))
        (equal (fn-hdc-node-in-poolp (list :span op pkg start count) end)
          (and (member-equal op '(3 4 6)) (natp pkg) (< pkg 3)
               (natp start) (natp count) (<= (+ start count) end)))
        (fn-hdc-node-in-poolp (fn-hdc-atom v) end)
        (equal (fn-hdc-node-in-poolp (fn-hdc-pair a d) end)
          (and (fn-hdc-node-in-poolp a end) (fn-hdc-node-in-poolp d end)))
        (equal (fn-hdc-node-in-poolp (fn-hdc-span op pkg start count) end)
          (and (member-equal op '(3 4 6)) (natp pkg) (< pkg 3)
               (natp start) (natp count) (<= (+ start count) end))))
   :hints (("Goal" :in-theory (enable fn-hdc-node-in-poolp fn-hdc-atom fn-hdc-pair fn-hdc-span)))))
(defthm fn-hdcl-begin-establishes-borrowed-node-bounds
  (implies (and (natp offset) (natp count))
           (fn-hdcl-borrowed-statep (fn-hdc-begin offset count epoch lease)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :use (:instance fn-hdc-begin-valid (length count))
    :in-theory (e/d (fn-hdcl-borrowed-statep fn-hdc-stack-in-poolp fn-hdc-begin fn-hdc-state)
      (fn-hdc-begin-valid fn-hdc-statep)))))
(defthm fn-hdcl-feed-raw-preserves-borrowed-node-bounds
  (implies (and (fn-hdcl-borrowed-statep s) (fn-scc-octetp byte))
           (fn-hdcl-borrowed-statep (fn-hdc-feed-raw byte s)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdc-state-fields fn-hdc-feed-raw-valid
          (:instance fn-hdc-number-feed-valid (c (nth 3 s))))
    :in-theory (e/d (fn-hdcl-borrowed-statep fn-hdc-stack-in-poolp
       fn-hdc-feed-raw fn-hdc-finish-number fn-hdc-move fn-hdc-state fn-hdc-payload-node
       fn-hdc-numberp fn-scc-octetp)
      (fn-hdc-node-in-poolp fn-hdc-number-feed fn-hdc-state-fields
       fn-hdc-feed-raw-valid fn-hdc-number-feed-valid)))))
(defthm fn-hdcl-feed-preserves-borrowed-node-bounds
  (implies (and (fn-hdcl-borrowed-statep s) (fn-scc-octetp byte))
           (fn-hdcl-borrowed-statep (fn-hdc-feed byte s)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdcl-feed-raw-preserves-borrowed-node-bounds fn-hdc-feed-valid)
    :in-theory (e/d (fn-hdcl-borrowed-statep fn-hdc-feed)
      (fn-hdc-feed-raw fn-hdc-node-in-poolp fn-hdc-stack-in-poolp fn-hdc-statep)))))
(defun-nx fn-hdcl-source-statep (s offset)
  (and (fn-hdcl-weighted-statep s offset) (fn-hdcl-scalar-statep s)
       (fn-hdcl-borrowed-statep s)
       (or (member-eq (nth 0 s) '(:done :refused)) (< (nth 7 s) (nth 8 s)))))
(defthm fn-hdcl-begin-establishes-source-lineage
  (implies (and (natp offset) (natp count))
           (fn-hdcl-source-statep (fn-hdc-begin offset count epoch lease) offset))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-hdcl-begin-establishes-consumed-byte-budget (length count))
          (:instance fn-hdcl-begin-establishes-scalar-lineage (length count))
          fn-hdcl-begin-establishes-borrowed-node-bounds)
    :in-theory (e/d (fn-hdcl-source-statep fn-hdc-begin fn-hdc-state)
      (fn-hdcl-weighted-statep fn-hdcl-scalar-statep fn-hdcl-borrowed-statep)))))
(local
 (defthm fn-hdcl-weighted-state-valid-unfolds
   (implies (fn-hdcl-weighted-statep s offset) (fn-hdc-statep s))
   :hints (("Goal" :in-theory (e/d (fn-hdcl-weighted-statep)
      (fn-hdc-statep fn-hdcl-stack-weight fn-hdcl-payload-charge))))))
(defthm fn-hdcl-feed-preserves-source-lineage
  (implies (and (fn-hdcl-source-statep s offset) (fn-scc-octetp byte))
           (fn-hdcl-source-statep (fn-hdc-feed byte s) offset))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdcl-feed-preserves-consumed-byte-budget fn-hdcl-feed-preserves-scalar-lineage
          fn-hdcl-feed-established-active-position fn-hdcl-feed-preserves-borrowed-node-bounds)
    :in-theory (e/d (fn-hdcl-source-statep)
      (fn-hdc-feed fn-hdc-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep
       fn-hdcl-borrowed-statep fn-hdcl-numeric-statep fn-hdcl-stack-weight fn-hdcl-payload-charge
       fn-hdcl-scalar-stackp fn-hdcl-number-budgetp)))))
(local
 (defthm fn-hdcl-width-is-proper-length-unfolds
   (implies (natp width)
            (equal (fn-hrcur-widthp node width)
                   (and (true-listp node) (equal (len node) width))))
   :hints (("Goal" :induct (fn-hrcur-widthp node width)
     :in-theory (enable fn-hrcur-widthp true-listp len)))))

(local
 (defthm fn-hdcl-pool-source-octet-unfolds
   (implies (and (fn-scc-octet-listp pool) (natp position) (< position (len pool)))
            (fn-scc-octetp (nth position pool)))
   :hints (("Goal" :induct (nth position pool)
     :in-theory (enable nth fn-scc-octet-listp fn-scc-octetp)))))
(local
 (defthm fn-hdcl-active-source-octet-unfolds
   (implies (and (fn-hdcl-source-statep s offset) (fn-scc-octet-listp pool)
                 (<= (nth 8 s) (len pool))
                 (not (member-eq (nth 0 s) '(:done :refused))))
            (fn-scc-octetp (nth (nth 7 s) pool)))
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hdcl-pool-source-octet-unfolds (position (nth 7 s)))
           fn-hdc-state-fields)
     :in-theory (e/d (fn-hdcl-source-statep fn-hdcl-weighted-statep)
       (fn-hdc-state-fields fn-hdcl-scalar-statep fn-scc-octet-listp fn-scc-octetp
        fn-hdcl-stack-weight fn-hdcl-payload-charge))))))
(defthm fn-hdcl-actual-model-run-preserves-source-lineage
  (implies (and (fn-hdcl-source-statep s offset) (fn-scc-octet-listp pool)
                (<= (nth 8 s) (len pool)))
           (fn-hdcl-source-statep (fn-hdc-model-run fuel s pool) offset))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hdc-model-run fuel s pool)
    :in-theory (e/d (fn-hdc-model-run)
      (fn-hdcl-source-statep fn-hdc-feed fn-scc-octet-listp fn-scc-octetp)))
    ("Subgoal *1/2"
      :use (fn-hdcl-active-source-octet-unfolds
            (:instance fn-hdcl-feed-preserves-source-lineage (byte (nth (nth 7 s) pool)))))))
(defthm fn-hdcl-successful-result-has-scalar-and-size-lineage
  (implies (and (fn-hdcl-source-statep s offset)
                (< (nth 8 s) *fn-hrcur-u64-bound*)
                (equal (car (fn-hdc-result s)) :ok))
           (and (fn-hdcl-scalar-lineagep (cadr (fn-hdc-result s)))
                (< (fn-hdcl-node-weight (cadr (fn-hdc-result s)))
                   *fn-hrcur-u64-bound*)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :use fn-hdc-state-fields
    :in-theory (e/d (fn-hdcl-source-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep
       fn-hdcl-scalar-stackp fn-hdcl-stack-weight fn-hdcl-payload-charge fn-hdc-result)
      (fn-hdc-state-fields fn-hdcl-numeric-statep fn-hdcl-scalar-lineagep
       fn-hdcl-node-weight)))))

(local
 (defthm fn-hdcl-codec-atoms-are-noncons-unfolds
   (implies (fn-scc-atomp x) (not (consp x)))
   :hints (("Goal" :in-theory (enable fn-scc-atomp fn-scc-nat-encodablep)))))
(defthm fn-hdcl-bounded-scalar-source-is-node-lineage
  (implies (and (fn-hdc-node-in-poolp node end)
                (fn-hdcl-scalar-lineagep node) (natp end)
                (< end *fn-hrcur-u64-bound*) (<= end (len pool)))
           (fn-hdcl-node-lineagep node pool))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hdcl-scalar-lineagep node)
    :in-theory (e/d (fn-hdcl-scalar-lineagep fn-hdcl-node-lineagep
       fn-hdc-node-in-poolp fn-hrcur-dos-domainp fn-hrcur-field fn-hrsc-domainp)
      (fn-scc-atomp fn-hdc-abstract fn-hrcur-widthp)))))
(defthm fn-hdcl-successful-bounded-result-is-cold-codec-domain
  (implies (and (fn-hdcl-source-statep s offset)
                (< (nth 8 s) *fn-hrcur-u64-bound*) (<= (nth 8 s) (len pool))
                (equal (car (fn-hdc-result s)) :ok)
                (fn-hdc-node-in-poolp (cadr (fn-hdc-result s)) (nth 8 s)))
           (fn-hrcur-cold-domainp (cadr (fn-hdc-result s)) pool))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdcl-successful-result-has-scalar-and-size-lineage fn-hdc-state-fields
          (:instance fn-hdcl-bounded-scalar-source-is-node-lineage
            (node (cadr (fn-hdc-result s))) (end (nth 8 s)))
          (:instance fn-hdcl-weighted-source-establishes-cold-domain
            (node (cadr (fn-hdc-result s)))))
    :in-theory (e/d (fn-hdcl-source-statep fn-hdcl-weighted-statep)
      (fn-hdc-state-fields fn-hdcl-scalar-statep fn-hdcl-node-lineagep fn-hdcl-node-weight
       fn-hrcur-cold-domainp fn-hdc-result fn-hdcl-stack-weight fn-hdcl-payload-charge)))))
(local
 (defthm fn-hdcl-successful-result-retains-node-bounds-unfolds
   (implies (and (fn-hdcl-source-statep s offset)
                 (equal (car (fn-hdc-result s)) :ok))
            (fn-hdc-node-in-poolp (cadr (fn-hdc-result s)) (nth 8 s)))
   :hints (("Goal" :do-not-induct t
     :in-theory (e/d (fn-hdcl-source-statep fn-hdcl-borrowed-statep
                       fn-hdc-stack-in-poolp fn-hdc-result)
       (fn-hdcl-weighted-statep fn-hdcl-scalar-statep fn-hdc-statep fn-hdc-node-in-poolp))))))
(defthm fn-hdcl-successful-source-result-retains-node-bounds
  (implies (and (fn-hdcl-source-statep s offset)
                (equal (car (fn-hdc-result s)) :ok))
           (fn-hdc-node-in-poolp (cadr (fn-hdc-result s)) (nth 8 s)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :in-theory (e/d (fn-hdcl-source-statep fn-hdcl-borrowed-statep
                      fn-hdc-stack-in-poolp fn-hdc-result)
      (fn-hdcl-weighted-statep fn-hdcl-scalar-statep fn-hdc-statep fn-hdc-node-in-poolp)))))
(defthm fn-hdcl-successful-source-result-is-cold-codec-domain
  (implies (and (fn-hdcl-source-statep s offset)
                (< (nth 8 s) *fn-hrcur-u64-bound*) (<= (nth 8 s) (len pool))
                (equal (car (fn-hdc-result s)) :ok))
           (fn-hrcur-cold-domainp (cadr (fn-hdc-result s)) pool))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdcl-successful-result-retains-node-bounds-unfolds
          fn-hdcl-successful-bounded-result-is-cold-codec-domain)
    :in-theory (disable fn-hdcl-source-statep fn-hdc-result fn-hdc-node-in-poolp
                        fn-hrcur-cold-domainp))))
(defthm fn-hdcl-current-decoder-result-is-cold-codec-domain
  (implies (and (fn-scc-octet-listp pool) (natp offset) (natp count)
                (< (+ offset count) *fn-hrcur-u64-bound*)
                (<= (+ offset count) (len pool)))
           (let* ((s (fn-hdc-model-run count (fn-hdc-begin offset count epoch lease) pool))
                  (result (fn-hdc-result s)))
             (implies (equal (car result) :ok)
                      (fn-hrcur-cold-domainp (cadr result) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdcl-begin-establishes-source-lineage
          (:instance fn-hdcl-actual-model-run-preserves-source-lineage
            (s (fn-hdc-begin offset count epoch lease)) (fuel count))
          (:instance fn-hdc-model-run-preserves-source-end
            (s (fn-hdc-begin offset count epoch lease)) (fuel count))
          (:instance fn-hdcl-successful-source-result-is-cold-codec-domain
            (s (fn-hdc-model-run count (fn-hdc-begin offset count epoch lease) pool))))
    :in-theory (e/d (fn-hdc-begin fn-hdc-state)
      (fn-hdcl-source-statep fn-hdc-model-run fn-hdc-result fn-hrcur-cold-domainp)))))
(defthm fn-hdcl-current-successful-decoder-retains-node-bounds
  (implies (and (fn-scc-octet-listp pool) (natp offset) (natp count)
                (<= (+ offset count) (len pool)))
           (let* ((s (fn-hdc-model-run count (fn-hdc-begin offset count epoch lease) pool))
                  (result (fn-hdc-result s)))
             (implies (equal (car result) :ok)
                      (fn-hdc-node-in-poolp (cadr result) (+ offset count)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdcl-begin-establishes-source-lineage
          (:instance fn-hdcl-actual-model-run-preserves-source-lineage
            (s (fn-hdc-begin offset count epoch lease)) (fuel count))
          (:instance fn-hdc-model-run-preserves-source-end
            (s (fn-hdc-begin offset count epoch lease)) (fuel count)))
    :in-theory (e/d (fn-hdc-begin fn-hdc-state fn-hdc-result
                      fn-hdcl-source-statep fn-hdcl-borrowed-statep fn-hdc-stack-in-poolp)
      (fn-hdcl-weighted-statep fn-hdcl-scalar-statep fn-hdc-model-run fn-hdc-node-in-poolp)))))
; A nonnatural fuel makes BEGIN refuse immediately. No caller count-domain
; premise is needed for this conditional successful-result boundary.
(defthm fn-hdcl-current-successful-decoder-is-cold-codec-domain
  (implies (and (fn-scc-octet-listp pool) (natp offset)
                (< (+ offset count) *fn-hrcur-u64-bound*)
                (<= (+ offset count) (len pool)))
           (let* ((s (fn-hdc-model-run count (fn-hdc-begin offset count epoch lease) pool))
                  (result (fn-hdc-result s)))
             (implies (equal (car result) :ok)
                      (fn-hrcur-cold-domainp (cadr result) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :cases ((natp count))
    :use fn-hdcl-current-decoder-result-is-cold-codec-domain
    :expand ((:free (s) (fn-hdc-model-run count s pool)))
    :in-theory (e/d (fn-hdc-begin fn-hdc-state fn-hdc-result zp)
      (fn-hdcl-source-statep fn-hdc-model-run fn-hrcur-cold-domainp)))))
(defthm fn-hdcl-current-decoder-cold-run-is-canonical-codec
  (implies (and (fn-scc-octet-listp pool) (natp offset)
                (< (+ offset count) *fn-hrcur-u64-bound*)
                (<= (+ offset count) (len pool)))
           (let* ((s (fn-hdc-model-run count (fn-hdc-begin offset count epoch lease) pool))
                  (result (fn-hdc-result s))
                  (source (list :decoded (cadr result))))
             (implies (equal (car result) :ok)
                      (equal (fn-hrcur-cold-oracle-run
                               (fn-hrcur-cold-begin source capture encoder-lease) pool)
                             (fn-scc-encode (fn-hdc-abstract (cadr result) pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hdcl-current-successful-decoder-is-cold-codec-domain
          (:instance fn-hrcur-cold-supported-source-run-is-current-codec
            (source (list :decoded (cadr (fn-hdc-result
                      (fn-hdc-model-run count (fn-hdc-begin offset count epoch lease) pool)))))
            (lease encoder-lease)))
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-hrcur-widthp car-cons cdr-cons eq not)))) )
(in-theory (disable fn-hdcl-number-budgetp fn-hdcl-node-weight fn-hdcl-node-lineagep
  fn-hdcl-stack-weight fn-hdcl-payload-charge fn-hdcl-weighted-statep
  fn-hdcl-numeric-statep fn-hdcl-scalar-lineagep fn-hdcl-scalar-stackp
  fn-hdcl-scalar-statep fn-hdcl-borrowed-statep fn-hdcl-source-statep))
