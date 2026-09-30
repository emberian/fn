(in-package "ACL2")

(include-book "history-decode-refinement")

(include-book "history-symbol-normalize")

(local (include-book "arithmetic/top" :dir :system))

(defun-nx fn-hdc-built-nodep (node)
 (declare (xargs :measure (acl2-count node)))
 (and (true-listp node)
      (cond ((eq (car node) :atom)
             (and (equal (len node) 2)
                  (or (null (cadr node)) (integerp (cadr node))
                      (characterp (cadr node)) (eq (cadr node) :hstxa))))
            ((eq (car node) :pair)
             (and (equal (len node) 3) (fn-hdc-built-nodep (cadr node))
                  (fn-hdc-built-nodep (caddr node))))
            ((eq (car node) :span)
             (and (equal (len node) 5) (member-equal (cadr node) '(3 4 6))
                  (natp (caddr node)) (< (caddr node) 3)
                  (natp (nth 3 node)) (natp (nth 4 node))))
            (t nil))))

(defun-nx fn-hdc-built-stackp (stack)
 (if (consp stack)
     (and (fn-hdc-built-nodep (car stack)) (fn-hdc-built-stackp (cdr stack)))
   (null stack)))

(local
 (defthm fn-hdc-state-number-feed-natural
 (implies (and (fn-hdc-statep s) (fn-scc-octetp byte))
          (natp (cadr (fn-hdc-number-feed byte (nth 3 s)))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hdc-state-fields)
                (:instance fn-hdc-number-feed-valid (c (nth 3 s))))
          :in-theory (e/d (fn-hdc-numberp)
                           (fn-hdc-state-fields fn-hdc-number-feed-valid
                            fn-hdc-statep fn-hdc-number-feed))))))

(defthm fn-hdc-feed-preserves-built-nodes
 (implies (and (fn-hdc-coherent s pool) (fn-scc-octetp byte)
               (fn-hdc-built-stackp (nth 9 s)))
          (fn-hdc-built-stackp (nth 9 (fn-hdc-feed byte s))))
 :hints (("Goal" :do-not-induct t :use fn-hdc-state-number-feed-natural
          :in-theory (e/d ( fn-hdc-coherent fn-hdc-feed fn-hdc-feed-raw
                             fn-hdc-move fn-hdc-finish-number fn-hdc-state
                             fn-hdc-built-stackp fn-hdc-built-nodep
                             fn-hdc-atom fn-hdc-pair fn-hdc-span
                             fn-hdc-payload-node) (fn-hdc-state-number-feed-natural)))))

(local
 (defthm fn-hdc-intern-keyword-hstxa
 (implies (and (member-equal pkg '(0 1 2)) (stringp name))
          (equal (equal (fn-scc-intern pkg name) :hstxa)
                 (and (equal pkg 0) (equal name "HSTXA"))))
 :hints (("Goal" :do-not-induct t :use fn-hdsn-intern-name
          :cases ((equal name "HSTXA"))
          :in-theory (enable fn-scc-intern)))))

(local
 (defthm fn-hdc-chars-octets-of-octets-chars
 (implies (fn-scc-octet-listp bytes)
          (equal (fn-scc-chars-octets (fn-scc-octets-chars bytes)) bytes))
 :hints (("Goal" :induct (fn-scc-octets-chars bytes)
          :in-theory (enable fn-scc-octets-chars fn-scc-chars-octets
                             fn-scc-octet-listp fn-scc-octetp)))))

(local
 (defthm fn-hdc-hstxa-string-is-five-bytes
 (implies (fn-scc-octet-listp bytes)
  (equal (equal (coerce (fn-scc-octets-chars bytes) 'string) "HSTXA")
         (equal bytes '(72 83 84 88 65))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hdc-chars-octets-of-octets-chars)
        (:instance coerce-inverse-1 (x (fn-scc-octets-chars bytes))))
  :cases ((equal bytes '(72 83 84 88 65)))
  :in-theory (disable fn-hdc-chars-octets-of-octets-chars fn-scc-octets-chars fn-scc-chars-octets)))))

(local
 (defthm fn-hdc-payload-hstxa-characterization
 (implies (and (member-equal op '(3 4 6)) (member-equal pkg '(0 1 2))
               (fn-scc-octet-listp bytes))
  (equal (equal (fn-hdc-model-payload op pkg bytes) :hstxa)
         (and (equal op 4) (equal pkg 0) (equal bytes '(72 83 84 88 65)))))
 :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-hdc-model-payload) (fn-scc-intern))))))

(local
 (defthm fn-hdc-shape-nthcdr-length
 (implies (and (natp n) (<= n (len xs)))
          (equal (len (nthcdr n xs)) (- (len xs) n)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr len)))))

(local
 (defthm fn-hdc-shape-window-octets
 (implies (and (fn-scc-octet-listp pool) (natp start) (natp count)
               (<= (+ start count) (len pool)))
          (fn-scc-octet-listp (take count (nthcdr start pool))))
 :hints (("Goal" :in-theory (disable take nthcdr fn-scc-octet-listp)))))

(local
 (defthm fn-hdc-shape-take-length
 (equal (len (take n bytes)) (nfix n))
 :hints (("Goal" :induct (take n bytes) :in-theory (enable take)))))

(local
 (defthm fn-hdc-five-source-prefix
 (implies (equal (take 5 bytes) '(72 83 84 88 65))
          (and (equal (take 4 bytes) '(72 83 84 88)) (equal (nth 4 bytes) 65)))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (xs) (take 5 xs)) (:free (xs) (take 4 xs))
           (:free (xs) (take 3 xs)) (:free (xs) (take 2 xs)) (:free (xs) (take 1 xs)))
  :in-theory (enable take nth)))))

(local
 (defthm fn-hdc-shape-nth-after-offset
 (implies (and (natp i) (natp j)) (equal (nth i (nthcdr j pool)) (nth (+ i j) pool)))
 :hints (("Goal" :induct (nthcdr j pool) :in-theory (enable nth nthcdr)))))

(defthm fn-hdc-payload-node-final-hstxa-normal-form
 (implies (and (member-equal op '(3 4 6)) (member-equal pkg '(0 1 2))
               (natp start) (natp count) (fn-scc-octet-listp pool)
               (<= (+ start count) (len pool))
               (fn-hdc-tag-prefixp op pkg start count (- count 1) number pool)
               (equal byte (nth (+ start count -1) pool)))
          (let ((node (fn-hdc-payload-node op pkg start count
                        (fn-hdc-tag-byte op pkg count 1 byte number))))
            (equal (equal (fn-hdc-abstract node pool) :hstxa)
                   (equal node (fn-hdc-atom :hstxa)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use (fn-hdc-payload-node-final-refines
                (:instance fn-hdc-five-source-prefix
                    (bytes (nthcdr start pool)))
                (:instance fn-hdc-shape-nth-after-offset (i 4) (j start))
                (:instance fn-hdc-shape-take-length
                    (n count) (bytes (nthcdr start pool)))
                (:instance fn-hdc-payload-hstxa-characterization
                    (bytes (take count (nthcdr start pool)))))
          :expand ((fn-hdc-abstract '(:atom :hstxa) pool))
          :cases ((and (equal op 4) (equal pkg 0) (equal count 5)))
          :in-theory (e/d (fn-hdc-payload-node fn-hdc-tag-byte fn-hdc-atom
                            fn-hdc-span fn-hdc-tag-prefixp)
                           (fn-hdc-abstract fn-hdc-model-payload fn-hdc-payload-hstxa-characterization fn-hdc-shape-take-length fn-hdc-five-source-prefix fn-hdc-shape-nth-after-offset)))))


(defun-nx fn-hdc-tag-normal-nodep (node pool)
 (declare (xargs :measure (acl2-count node)))
 (and (equal (equal (fn-hdc-abstract node pool) :hstxa)
             (equal node (fn-hdc-atom :hstxa)))
      (if (eq (car node) :pair)
          (and (fn-hdc-tag-normal-nodep (cadr node) pool)
               (fn-hdc-tag-normal-nodep (caddr node) pool))
        t)))
(defun-nx fn-hdc-tag-normal-stackp (stack pool)
 (if (consp stack)
     (and (fn-hdc-tag-normal-nodep (car stack) pool)
          (fn-hdc-tag-normal-stackp (cdr stack) pool))
   (null stack)))
(defthm fn-hdc-tag-normal-atom
 (fn-hdc-tag-normal-nodep (fn-hdc-atom value) pool)
 :hints (("Goal" :in-theory (enable fn-hdc-tag-normal-nodep fn-hdc-atom fn-hdc-abstract))))
(defthm fn-hdc-tag-normal-pair
 (equal (fn-hdc-tag-normal-nodep (fn-hdc-pair a d) pool)
        (and (fn-hdc-tag-normal-nodep a pool) (fn-hdc-tag-normal-nodep d pool)))
 :hints (("Goal" :in-theory (enable fn-hdc-tag-normal-nodep fn-hdc-pair fn-hdc-abstract fn-hdc-atom))))
(defthm fn-hdc-empty-span-tag-normal
 (implies (and (member-equal op '(3 4 6)) (member-equal pkg '(0 1 2)))
          (fn-hdc-tag-normal-nodep (fn-hdc-span op pkg start 0) pool))
 :hints (("Goal" :in-theory (e/d (fn-hdc-tag-normal-nodep fn-hdc-span fn-hdc-atom fn-hdc-abstract)
                                  (fn-scc-intern)))))

(local
 (defthm fn-hdc-payload-node-never-pair
  (not (equal (car (fn-hdc-payload-node op pkg start count number)) :pair))
  :hints (("Goal" :in-theory (enable fn-hdc-payload-node fn-hdc-atom fn-hdc-span)))))
(defthm fn-hdc-payload-node-final-tag-normal
 (implies (and (member-equal op '(3 4 6)) (member-equal pkg '(0 1 2))
               (natp start) (natp count) (fn-scc-octet-listp pool)
               (<= (+ start count) (len pool))
               (fn-hdc-tag-prefixp op pkg start count (- count 1) number pool)
               (equal byte (nth (+ start count -1) pool)))
          (fn-hdc-tag-normal-nodep
            (fn-hdc-payload-node op pkg start count
              (fn-hdc-tag-byte op pkg count 1 byte number)) pool))
 :hints (("Goal" :do-not-induct t
          :use fn-hdc-payload-node-final-hstxa-normal-form
          :expand ((fn-hdc-abstract '(:atom :hstxa) pool))
          :in-theory (e/d (fn-hdc-tag-normal-nodep)
                           (fn-hdc-payload-node fn-hdc-span fn-hdc-atom
                            fn-hdc-tag-prefixp fn-scc-octet-listp
                            fn-hdc-abstract fn-hdc-tag-byte)))))

(defthm fn-hdc-actual-final-payload-tag-normal
 (implies (and (fn-hdc-coherent s pool) (eq (nth 0 s) :payload)
               (equal (nth 6 s) 1) (fn-scc-octet-listp pool)
               (<= (nth 8 s) (len pool))
               (equal byte (nth (nth 7 s) pool)))
          (fn-hdc-tag-normal-nodep
           (fn-hdc-payload-node (nth 1 s) (nth 2 s) (nth 4 s) (nth 5 s)
            (fn-hdc-tag-byte (nth 1 s) (nth 2 s) (nth 5 s) 1 byte (nth 3 s))) pool))
 :hints (("Goal" :do-not-induct t
          :use (fn-hdc-state-fields
                (:instance fn-hdc-payload-node-final-tag-normal
                     (op (nth 1 s)) (pkg (nth 2 s)) (start (nth 4 s))
                     (count (nth 5 s)) (number (nth 3 s))))
          :in-theory (e/d (fn-hdc-coherent)
                           (fn-hdc-state-fields fn-hdc-statep fn-hdc-tag-prefixp
                            fn-scc-octet-listp fn-hdc-payload-node-final-tag-normal
                            fn-hdc-tag-normal-nodep fn-hdc-payload-node fn-hdc-tag-byte)))))


(defthm fn-hdc-feed-preserves-tag-normal-nodes
 (implies (and (fn-hdc-coherent s pool) (fn-scc-octet-listp pool)
               (<= (nth 8 s) (len pool)) (fn-scc-octetp byte)
               (equal byte (nth (nth 7 s) pool))
               (fn-hdc-tag-normal-stackp (nth 9 s) pool))
          (fn-hdc-tag-normal-stackp (nth 9 (fn-hdc-feed byte s)) pool))
 :hints (("Goal" :do-not-induct t :use fn-hdc-actual-final-payload-tag-normal
          
          :in-theory (e/d (fn-hdc-feed fn-hdc-feed-raw
                            fn-hdc-move fn-hdc-state fn-hdc-finish-number
                            fn-hdc-tag-normal-stackp)
                           (fn-hdc-abstract fn-hdc-tag-normal-nodep
                            fn-hdc-atom (:executable-counterpart fn-hdc-atom)
                            fn-hdc-pair fn-hdc-span
                            fn-hdc-tag-byte fn-hdc-payload-node
                            fn-hdc-coherent fn-hdc-tag-prefixp fn-scc-octet-listp)))))


(defun-nx fn-hdc-node-contractp (s pool)
 (and (fn-hdc-coherent s pool)
      (fn-hdc-built-stackp (nth 9 s))
      (fn-hdc-stack-in-poolp (nth 9 s) (nth 8 s))
      (fn-hdc-tag-normal-stackp (nth 9 s) pool)))

(defthm fn-hdc-feed-preserves-node-contract
 (implies (and (fn-hdc-node-contractp s pool) (fn-scc-octet-listp pool)
               (<= (nth 8 s) (len pool)) (fn-scc-octetp byte)
               (equal byte (nth (nth 7 s) pool)))
          (fn-hdc-node-contractp (fn-hdc-feed byte s) pool))
 :hints (("Goal" :do-not-induct t
          :use (fn-hdc-feed-preserves-coherence fn-hdc-feed-preserves-built-nodes
                fn-hdc-feed-preserves-borrowed-node-bounds
                fn-hdc-feed-preserves-tag-normal-nodes)
          :in-theory (e/d (fn-hdc-node-contractp)
                           (fn-hdc-feed fn-hdc-coherent fn-hdc-built-stackp
                            fn-hdc-stack-in-poolp fn-hdc-tag-normal-stackp
                            fn-hdc-feed-preserves-coherence
                            fn-hdc-feed-preserves-built-nodes
                            fn-hdc-feed-preserves-borrowed-node-bounds
                            fn-hdc-feed-preserves-tag-normal-nodes)))))

(defthm fn-hdc-node-contract-begin
 (implies (and (natp offset) (natp count))
          (fn-hdc-node-contractp (fn-hdc-begin offset count epoch lease) pool))
 :hints (("Goal" :do-not-induct t
          :use fn-hdc-begin-coherent
          :in-theory (e/d (fn-hdc-node-contractp fn-hdc-begin fn-hdc-state
                            fn-hdc-built-stackp fn-hdc-stack-in-poolp fn-hdc-tag-normal-stackp)
                           (fn-hdc-coherent fn-hdc-begin-coherent)))))

(defthm fn-hdc-shape-source-octet
 (implies (and (fn-scc-octet-listp pool) (natp pos) (< pos (len pool)))
          (fn-scc-octetp (nth pos pool)))
 :hints (("Goal" :induct (nth pos pool)
          :in-theory (enable nth fn-scc-octet-listp fn-scc-octetp))))

(defthm fn-hdc-contract-active-source-octet
 (implies (and (fn-hdc-node-contractp s pool) (fn-scc-octet-listp pool)
               (<= (nth 8 s) (len pool))
               (not (member-eq (nth 0 s) '(:done :refused))))
          (fn-scc-octetp (nth (nth 7 s) pool)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hdc-shape-source-octet (pos (nth 7 s)))
                fn-hdc-coherent-fields fn-hdc-state-fields)
          :in-theory (e/d (fn-hdc-node-contractp)
                           (fn-hdc-shape-source-octet fn-hdc-coherent-fields
                            fn-hdc-state-fields fn-hdc-coherent fn-hdc-statep
                            fn-scc-octet-listp fn-scc-octetp)))))


(defthm fn-hdc-model-run-preserves-node-contract
 (implies (and (fn-hdc-node-contractp s pool) (fn-scc-octet-listp pool)
               (<= (nth 8 s) (len pool)))
  (fn-hdc-node-contractp (fn-hdc-model-run fuel s pool) pool))
 :hints (("Goal" :induct (fn-hdc-model-run fuel s pool)
  :in-theory (e/d (fn-hdc-model-run)
   (fn-hdc-node-contractp fn-hdc-feed fn-scc-octet-listp fn-scc-octetp
    fn-hdc-feed-preserves-node-contract fn-hdc-contract-active-source-octet)))
 ("Subgoal *1/2" :use ((:instance fn-hdc-feed-preserves-node-contract
                      (byte (nth (nth 7 s) pool))) fn-hdc-contract-active-source-octet))))

(defthm fn-hdc-abstract-nonoctet-cons-is-concrete-pair
 (implies (and (fn-hdc-built-nodep node) (fn-hdc-node-in-poolp node end)
               (<= end (len pool)) (fn-scc-octet-listp pool)
               (consp (fn-hdc-abstract node pool))
               (not (fn-scc-octetp (car (fn-hdc-abstract node pool)))))
  (equal (car node) :pair))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hdc-built-nodep fn-hdc-node-in-poolp fn-hdc-abstract fn-scc-octetp)
                  (fn-scc-intern fn-scc-octet-listp)))))

(local
 (defthm fn-hdc-shape-begin-source-end-unfolds
 (equal (nth 8 (fn-hdc-begin offset count epoch lease)) (+ offset count))
 :hints (("Goal" :in-theory (enable fn-hdc-begin fn-hdc-state)))))

(defthm fn-hdc-current-decoder-result-node-contract
 (implies (and (fn-scc-octet-listp pool) (natp offset) (natp count)
               (<= (+ offset count) (len pool)))
  (let* ((s (fn-hdc-model-run count (fn-hdc-begin offset count epoch lease) pool))
         (result (fn-hdc-result s)))
   (implies (equal (car result) :ok)
    (and (fn-hdc-built-nodep (cadr result))
         (fn-hdc-node-in-poolp (cadr result) (+ offset count))
         (fn-hdc-tag-normal-nodep (cadr result) pool)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use (fn-hdc-node-contract-begin
                (:instance fn-hdc-model-run-preserves-node-contract
                    (fuel count) (s (fn-hdc-begin offset count epoch lease))))
          :in-theory (e/d (fn-hdc-node-contractp fn-hdc-result fn-hdc-built-stackp
                            fn-hdc-stack-in-poolp fn-hdc-tag-normal-stackp)
                           (fn-hdc-model-run fn-hdc-begin fn-hdc-coherent
                            fn-hdc-node-contract-begin
                            fn-hdc-model-run-preserves-node-contract
                            fn-hdc-built-nodep fn-hdc-node-in-poolp fn-hdc-tag-normal-nodep)))))

(defthm fn-hdc-pair-accessors-refine-abstraction
 (implies (and (fn-hdc-built-nodep node) (equal (car node) :pair))
          (and (equal (fn-hdc-abstract (fn-hdc-car node) pool)
                      (car (fn-hdc-abstract node pool)))
               (equal (fn-hdc-abstract (fn-hdc-cdr node) pool)
                      (cdr (fn-hdc-abstract node pool)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :in-theory (enable fn-hdc-built-nodep fn-hdc-car fn-hdc-cdr fn-hdc-abstract))))
