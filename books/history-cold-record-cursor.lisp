; Proof-only residual/invariant composition for the single guarded cold runtime.
(in-package "ACL2")
(include-book "history-cold-record-runtime")
(local (include-book "arithmetic/top" :dir :system))

(defun-nx fn-hrcur-cold-task-rest (task pool)
  (if (eq (fn-hrcur-field 0 task) :byte)
      (list (fn-hrcur-field 1 task))
    (fn-scc-encode (fn-hdc-abstract (fn-hrcur-field 1 task) pool))))
(defun-nx fn-hrcur-cold-tasks-rest (tasks pool)
  (if (consp tasks)
      (append (fn-hrcur-cold-task-rest (car tasks) pool)
              (fn-hrcur-cold-tasks-rest (cdr tasks) pool)) nil))
(defun-nx fn-hrcur-cold-rest (c pool)
  (let ((phase (fn-hrcur-field 0 c)) (child (fn-hrcur-field 2 c))
        (node (fn-hrcur-field 7 c)) (count (fn-hrcur-field 8 c))
        (pending (fn-hrcur-cold-tasks-rest (fn-hrcur-field 1 c) pool)))
    (case phase
      (:work pending)
      ((:classify :symbol)
       (append (fn-scc-encode (fn-hdc-abstract node pool)) pending))
      (:scalar (append (fn-hrsc-rest child) pending))
      (:span (append (fn-hrcur-span-rest child pool) pending))
      (:opaque-prefix (append (fn-hrcur-field 6 c)
                              (append (fn-hdc-abstract node pool) pending)))
      (:opaque (append (fn-hdc-abstract node pool) pending))
      (:opaque-span (append (take (nfix count) (nthcdr (nfix child) pool)) pending))
      (otherwise nil))))

(defthm fn-hrcur-cold-begin-rest-unfolds
  (implies (and (fn-hrcur-widthp source 2) (eq (car source) :decoded))
           (equal (fn-hrcur-cold-rest (fn-hrcur-cold-begin source capture lease) pool)
                  (fn-scc-encode (fn-hdc-abstract (cadr source) pool))))
  :hints (("Goal" :in-theory
           (enable fn-hrcur-cold-rest fn-hrcur-cold-begin
                   fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest))))

(defthm fn-hrcur-cold-tick-keeps-capture-lease
  (and (equal (fn-hrcur-field 4 (mv-nth 2 (fn-hrcur-cold-tick c)))
              (fn-hrcur-field 4 c))
       (equal (fn-hrcur-field 5 (mv-nth 2 (fn-hrcur-cold-tick c)))
              (fn-hrcur-field 5 c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hrcur-cold-tick fn-hrcur-cold-state))))
(defthm fn-hrcur-cold-supply-keeps-capture-lease
  (and (equal (fn-hrcur-field 4 (mv-nth 2 (fn-hrcur-cold-supply c position byte)))
              (fn-hrcur-field 4 c))
       (equal (fn-hrcur-field 5 (mv-nth 2 (fn-hrcur-cold-supply c position byte)))
              (fn-hrcur-field 5 c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hrcur-cold-supply fn-hrcur-cold-state))))
(local
 (defthm fn-hrcur-cold-scalar-does-not-demand-unfolds
   (not (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrsc-tick child))) :need-byte))
   :hints (("Goal" :do-not-induct t :in-theory (enable fn-hrsc-tick)))))

(defthm fn-hrcur-cold-demand-keeps-cursor
  (implies (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
           (equal (mv-nth 2 (fn-hrcur-cold-tick c)) c))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-cold-scalar-does-not-demand-unfolds
                            (child (fn-hrcur-field 2 c))))
           :in-theory (e/d (fn-hrcur-cold-tick fn-hrcur-cold-demand)
                           (fn-hrcur-cold-scalar-does-not-demand-unfolds)))))

; These recursive facts are carried source lineage, never runtime guards.
(defun-nx fn-hrcur-cold-domainp (node pool)
  (declare (xargs :measure (acl2-count node)))
  (and (fn-hrcur-dos-domainp node pool)
       (< (len (fn-hdc-abstract node pool)) *fn-hrcur-u64-bound*)
       (case (fn-hrcur-field 0 node)
         (:atom (fn-hrsc-domainp (fn-hrcur-field 1 node)))
         (:pair (and (fn-hrcur-cold-domainp (fn-hrcur-field 1 node) pool)
                     (fn-hrcur-cold-domainp (fn-hrcur-field 2 node) pool)))
         (:span (or (equal (fn-hrcur-field 1 node) 4)
                    (equal (fn-hrcur-field 2 node) 0)))
         (otherwise nil))))

(defun-nx fn-hrcur-cold-rejected-prefixp (node count pool)
  (declare (xargs :measure (nfix count)))
  (and (not (fn-scc-octets-valuep (fn-hdc-abstract node pool)))
       (if (zp count) t
         (and (eq (fn-hrcur-field 0 node) :pair)
              (eq (fn-hrcur-field 0 (fn-hrcur-field 1 node)) :atom)
              (fn-scc-octetp (fn-hrcur-field 1 (fn-hrcur-field 1 node)))
              (fn-hrcur-cold-rejected-prefixp
                (fn-hrcur-field 2 node) (1- count) pool)))))

(defun-nx fn-hrcur-cold-taskp (task pool)
  (case (fn-hrcur-field 0 task)
    (:byte (and (fn-hrcur-widthp task 2) (fn-scc-octetp (fn-hrcur-field 1 task))))
    (:node (and (fn-hrcur-widthp task 2)
                (fn-hrcur-cold-domainp (fn-hrcur-field 1 task) pool)))
    (:no-octets (and (fn-hrcur-widthp task 3)
                    (fn-hrcur-cold-domainp (fn-hrcur-field 1 task) pool)
                    (fn-hrcur-cold-countp (fn-hrcur-field 2 task))
                    (fn-hrcur-cold-rejected-prefixp
                      (fn-hrcur-field 1 task) (fn-hrcur-field 2 task) pool)))
    (otherwise nil)))
(defun-nx fn-hrcur-cold-tasksp (tasks pool)
  (if (consp tasks)
      (and (fn-hrcur-cold-taskp (car tasks) pool)
           (fn-hrcur-cold-tasksp (cdr tasks) pool))
    (null tasks)))

(defun-nx fn-hrcur-cold-name (node pool)
  (coerce (fn-scc-octets-chars
            (take (nfix (fn-hrcur-field 4 node))
                  (nthcdr (nfix (fn-hrcur-field 3 node)) pool))) 'string))

; The normalizer's serial limit derives from its finite static-table work,
; never from an arbitrary stored-name ceiling. This relation is proof only.
(defun-nx fn-hrcur-cold-symbol-budgetp (c)
  (and (fn-hdsn-coherent c)
       (<= (+ (nth 5 c) (fn-hdsn-work c)) 12250)))

(local
 (defthm fn-hrcur-cold-symbol-tick-budget-unfolds
   (implies (fn-hdsn-coherent c)
            (<= (+ (nth 5 (mv-nth 1 (fn-hdsn-tick c)))
                   (fn-hdsn-work (mv-nth 1 (fn-hdsn-tick c))))
                (+ (nth 5 c) (fn-hdsn-work c))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hdsn-candidate-work (nth 3 c)))
            :in-theory (enable fn-hdsn-coherent fn-hdsn-statep fn-hdsn-tick
                               fn-hdsn-next-candidate fn-hdsn-state fn-hdsn-work)))))
(local
 (defthm fn-hrcur-cold-symbol-supply-budget-unfolds
   (implies (fn-hdsn-coherent c)
            (<= (+ (nth 5 (mv-nth 1 (fn-hdsn-supply position serial byte c)))
                   (fn-hdsn-work (mv-nth 1 (fn-hdsn-supply position serial byte c))))
                (+ (nth 5 c) (fn-hdsn-work c))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hdsn-candidate-work (nth 3 c)))
            :in-theory (enable fn-hdsn-coherent fn-hdsn-statep fn-hdsn-supply
                               fn-hdsn-next-candidate fn-hdsn-state fn-hdsn-work)))))

(defthm fn-hrcur-cold-symbol-begin-budget
  (implies (and (member-equal pkg '(0 1 2)) (natp offset) (natp count))
           (fn-hrcur-cold-symbol-budgetp (fn-hdsn-begin pkg offset count)))
  :hints (("Goal" :use (fn-hdsn-initial-work-bound fn-hdsn-begin-coherent)
           :in-theory (e/d (fn-hrcur-cold-symbol-budgetp fn-hdsn-begin fn-hdsn-state)
                            (fn-hdsn-work fn-hdsn-coherent fn-hdsn-begin-coherent)))))
(defthm fn-hrcur-cold-symbol-tick-preserves-budget
  (implies (fn-hrcur-cold-symbol-budgetp c)
           (fn-hrcur-cold-symbol-budgetp (mv-nth 1 (fn-hdsn-tick c))))
  :hints (("Goal" :use (fn-hrcur-cold-symbol-tick-budget-unfolds fn-hdsn-tick-coherent)
           :in-theory (e/d (fn-hrcur-cold-symbol-budgetp)
                            (fn-hdsn-coherent fn-hdsn-work fn-hdsn-tick
                             fn-hdsn-tick-coherent fn-hrcur-cold-symbol-tick-budget-unfolds)))))
(defthm fn-hrcur-cold-symbol-supply-preserves-budget
  (implies (fn-hrcur-cold-symbol-budgetp c)
           (fn-hrcur-cold-symbol-budgetp (mv-nth 1 (fn-hdsn-supply position serial byte c))))
  :hints (("Goal" :use (fn-hrcur-cold-symbol-supply-budget-unfolds fn-hdsn-supply-coherent)
           :in-theory (e/d (fn-hrcur-cold-symbol-budgetp)
                            (fn-hdsn-coherent fn-hdsn-work fn-hdsn-supply
                             fn-hdsn-supply-coherent fn-hrcur-cold-symbol-supply-budget-unfolds)))))
(defthm fn-hrcur-cold-symbol-serial-bound
  (implies (fn-hrcur-cold-symbol-budgetp c) (<= (nth 5 c) 12250))
  :hints (("Goal" :in-theory (enable fn-hrcur-cold-symbol-budgetp fn-hdsn-work))))

(defun-nx fn-hrcur-cold-invariantp (c pool)
  (let* ((phase (fn-hrcur-field 0 c)) (child (fn-hrcur-field 2 c))
         (node (fn-hrcur-field 7 c)) (count (fn-hrcur-field 8 c)))
    (and (fn-hrcur-widthp c 9) (fn-scc-octet-listp pool)
         (fn-hrcur-cold-tasksp (fn-hrcur-field 1 c) pool)
         (case phase
           (:work t)
           (:classify
            (and (fn-hrcur-cold-domainp node pool)
                 (fn-hrcur-dos-invariantp child pool)
                 (equal (fn-hrcur-field 1 child) node)))
           (:scalar (fn-hrsc-invariantp child))
           (:span (fn-hrcur-span-invariantp child pool))
           (:symbol
            (and (fn-hrcur-cold-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :span)
                 (equal (fn-hrcur-field 1 node) 4)
                 (fn-hrcur-cold-symbol-childp child)
                 (fn-hrcur-cold-symbol-budgetp child)
                 (equal (nth 0 child) (fn-hrcur-field 2 node))
                 (equal (nth 1 child) (fn-hrcur-field 3 node))
                 (equal (nth 2 child) (fn-hrcur-field 4 node))
                 (equal (fn-hdsn-denote child (fn-hrcur-cold-name node pool))
                        (fn-hdsn-classify-name (fn-hrcur-field 2 node)
                                              (fn-hrcur-cold-name node pool)))))
           ((:opaque-prefix :opaque)
            (and (fn-hrcur-dos-domainp node pool)
                 (fn-scc-octet-listp (fn-hdc-abstract node pool))
                 (fn-hrcur-cold-countp count)
                 (equal count (len (fn-hdc-abstract node pool)))
                 (implies (eq phase :opaque-prefix)
                          (fn-scc-octet-listp (fn-hrcur-field 6 c)))))
           (:opaque-span
            (and (fn-hrcur-cold-countp child) (fn-hrcur-cold-countp count)
                 (< (+ child count) *fn-hrcur-u64-bound*)
                 (<= (+ child count) (len pool))))
           (:done (null (fn-hrcur-field 1 c)))
           (otherwise nil)))))

(defthm fn-hrcur-cold-begin-establishes-invariant
  (implies (and (fn-hrcur-widthp source 2) (eq (car source) :decoded)
                (fn-hrcur-cold-domainp (cadr source) pool)
                (fn-scc-octet-listp pool))
           (and (fn-hrcur-cold-invariantp
                  (fn-hrcur-cold-begin source capture lease) pool)
                (equal (fn-hrcur-cold-rest
                         (fn-hrcur-cold-begin source capture lease) pool)
                       (fn-scc-encode (fn-hdc-abstract (cadr source) pool)))))
  :hints (("Goal" :in-theory
           (enable fn-hrcur-cold-invariantp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
                   fn-hrcur-cold-begin fn-hrcur-cold-rest fn-hrcur-cold-tasks-rest
                   fn-hrcur-cold-task-rest))))

; Actual outer calls, not a parallel encoder: lift the existing child residual
; through this controller's pending task continuation.
(defthm fn-hrcur-cold-scalar-tick-refines-residual
  (implies (and (fn-hrcur-widthp c 9)
                (eq (fn-hrcur-field 0 c) :scalar)
                (fn-hrsc-invariantp (fn-hrcur-field 2 c)))
    (let ((v (mv-nth 0 (fn-hrcur-cold-tick c)))
          (b (mv-nth 1 (fn-hrcur-cold-tick c)))
          (next (mv-nth 2 (fn-hrcur-cold-tick c))))
      (and (member-eq v '(:continue :emit))
           (equal (fn-hrcur-cold-rest c pool)
                  (if (eq v :emit) (cons b (fn-hrcur-cold-rest next pool))
                    (fn-hrcur-cold-rest next pool)))
           (implies (eq (fn-hrcur-field 0 next) :scalar)
                    (fn-hrsc-invariantp (fn-hrcur-field 2 next))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrsc-tick-refines-atom-residual
                            (c (fn-hrcur-field 2 c)))
                 (:instance fn-hrsc-tick-preserves-invariant
                            (c (fn-hrcur-field 2 c))))
           :in-theory (e/d (fn-hrcur-cold-tick fn-hrcur-cold-state
                              fn-hrcur-cold-rest)
                             (fn-hrsc-tick fn-hrsc-rest fn-hrsc-invariantp
                              fn-hrsc-tick-refines-atom-residual
                              fn-hrsc-tick-preserves-invariant)))))

(defthm fn-hrcur-cold-span-tick-refines-residual
  (implies (and (eq (fn-hrcur-field 0 c) :span)
                (fn-hrcur-span-invariantp (fn-hrcur-field 2 c) pool))
    (let ((v (mv-nth 0 (fn-hrcur-cold-tick c)))
          (b (mv-nth 1 (fn-hrcur-cold-tick c)))
          (next (mv-nth 2 (fn-hrcur-cold-tick c))))
      (and (equal (fn-hrcur-cold-rest c pool)
                  (if (eq v :emit) (cons b (fn-hrcur-cold-rest next pool))
                    (fn-hrcur-cold-rest next pool)))
           (implies (eq (fn-hrcur-field 0 next) :span)
                    (fn-hrcur-span-invariantp (fn-hrcur-field 2 next) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-span-tick-refines-wire
                            (c (fn-hrcur-field 2 c))))
           :in-theory (e/d (fn-hrcur-cold-tick fn-hrcur-cold-state
                              fn-hrcur-cold-rest fn-hrcur-span-tick
                              fn-hrcur-span-invariantp fn-hrcur-span-shapep)
                             (fn-hrcur-span-rest fn-hrcur-span-tick-refines-wire
                              fn-hrcur-span-supply-refines-wire)))))

(defthm fn-hrcur-cold-span-supply-refines-residual
  (implies (and (fn-hrcur-widthp c 9)
                (eq (fn-hrcur-field 0 c) :span)
                (fn-hrcur-span-invariantp (fn-hrcur-field 2 c) pool)
                (eq (fn-hrcur-field 0 (fn-hrcur-field 2 c)) :body)
                (< 0 (fn-hrcur-field 3 (fn-hrcur-field 2 c)))
                (equal position (fn-hrcur-field 2 (fn-hrcur-field 2 c)))
                (equal byte (nth position pool)))
    (let ((next (mv-nth 2 (fn-hrcur-cold-supply c position byte))))
      (and (eq (mv-nth 0 (fn-hrcur-cold-supply c position byte)) :emit)
           (equal (mv-nth 1 (fn-hrcur-cold-supply c position byte)) byte)
           (fn-hrcur-span-invariantp (fn-hrcur-field 2 next) pool)
           (equal (fn-hrcur-cold-rest c pool)
                  (cons byte (fn-hrcur-cold-rest next pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-span-supply-refines-wire
                            (c (fn-hrcur-field 2 c))))
           :in-theory (e/d (fn-hrcur-cold-supply fn-hrcur-cold-state
                              fn-hrcur-cold-rest)
                             (fn-hrcur-span-supply fn-hrcur-span-rest
                              fn-hrcur-span-invariantp
                              fn-hrcur-span-tick-refines-wire
                              fn-hrcur-span-supply-refines-wire)))))

(defthm fn-hrcur-cold-scalar-tick-preserves-invariant
  (implies (and (fn-hrcur-cold-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :scalar))
           (fn-hrcur-cold-invariantp (mv-nth 2 (fn-hrcur-cold-tick c)) pool))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrsc-tick-refines-atom-residual
                            (c (fn-hrcur-field 2 c)))
                 (:instance fn-hrsc-tick-preserves-invariant
                            (c (fn-hrcur-field 2 c))))
           :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-tick fn-hrcur-cold-state)
                            (fn-hrsc-tick fn-hrsc-rest fn-hrsc-invariantp
                             fn-hrsc-tick-refines-atom-residual fn-hrsc-tick-preserves-invariant
                             fn-hrcur-cold-tasksp fn-hrcur-cold-domainp
                             fn-hrcur-cold-name fn-hrcur-cold-symbol-budgetp)))))

(local
 (defthm fn-hrcur-cold-span-verdict-unfolds
   (implies (fn-hrcur-span-invariantp child pool)
            (or (member-eq (mv-nth 0 (fn-hrcur-span-tick child))
                           '(:continue :emit :prepared))
                (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-span-tick child))) :need-byte)))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-hrcur-span-tick fn-hrcur-span-invariantp
                               fn-hrcur-span-shapep)))))

(defthm fn-hrcur-cold-span-tick-preserves-invariant
  (implies (and (fn-hrcur-cold-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :span))
           (fn-hrcur-cold-invariantp (mv-nth 2 (fn-hrcur-cold-tick c)) pool))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-cold-span-verdict-unfolds
                            (child (fn-hrcur-field 2 c)))
                 (:instance fn-hrcur-span-tick-refines-wire
                            (c (fn-hrcur-field 2 c))))
           :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-tick fn-hrcur-cold-state)
                            (fn-hrcur-span-tick fn-hrcur-span-rest fn-hrcur-span-invariantp
                             fn-hrcur-cold-span-verdict-unfolds fn-hrcur-span-tick-refines-wire
                             fn-hrcur-span-supply-refines-wire fn-hrcur-cold-tasksp
                             fn-hrcur-cold-domainp fn-hrcur-cold-name fn-hrcur-cold-symbol-budgetp)))))

(defthm fn-hrcur-cold-prefix-tick-refines-residual
  (implies (and (fn-hrcur-cold-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :opaque-prefix))
    (let ((v (mv-nth 0 (fn-hrcur-cold-tick c)))
          (b (mv-nth 1 (fn-hrcur-cold-tick c)))
          (next (mv-nth 2 (fn-hrcur-cold-tick c))))
      (and (member-eq v '(:continue :emit))
           (fn-hrcur-cold-invariantp next pool)
           (equal (fn-hrcur-cold-rest c pool)
                  (if (eq v :emit) (cons b (fn-hrcur-cold-rest next pool))
                    (fn-hrcur-cold-rest next pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-tick
                              fn-hrcur-cold-state fn-hrcur-cold-rest fn-scc-octet-listp)
                             (fn-hrcur-cold-tasksp fn-hrcur-dos-domainp fn-hdc-abstract
                              fn-hrcur-cold-countp fn-hrcur-cold-tasks-rest)))))

(local
 (defthm fn-hrcur-cold-octets-zero-length
   (implies (and (fn-scc-octet-listp x) (equal (len x) 0)) (equal x nil))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-scc-octet-listp len)))))

(local
 (defthm fn-hrcur-cold-take-zero-unfolds
   (equal (take 0 x) nil)
   :hints (("Goal" :in-theory (enable take)))))

(defthm fn-hrcur-cold-opaque-span-tick-refines-residual
  (implies (and (fn-hrcur-cold-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :opaque-span))
    (let ((v (mv-nth 0 (fn-hrcur-cold-tick c)))
          (next (mv-nth 2 (fn-hrcur-cold-tick c))))
      (and (or (eq v :continue) (eq (fn-hrcur-field 0 v) :need-byte))
           (fn-hrcur-cold-invariantp next pool)
           (equal (fn-hrcur-cold-rest c pool)
                  (fn-hrcur-cold-rest next pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-tick
                              fn-hrcur-cold-state fn-hrcur-cold-rest fn-hrcur-cold-countp
                              fn-hrcur-cold-demand)
                             (fn-hrcur-cold-tasksp fn-hrcur-cold-tasks-rest take nthcdr)))))

(local
 (defthm fn-hrcur-cold-pool-byte
   (implies (and (fn-scc-octet-listp pool) (natp position) (< position (len pool)))
            (fn-scc-octetp (nth position pool)))
   :hints (("Goal" :induct (nth position pool)
            :in-theory (enable nth fn-scc-octet-listp fn-scc-octetp)))))
(local
 (defthm fn-hrcur-cold-pool-slice-step
   (implies (and (natp position) (natp count) (< 0 count))
            (equal (take count (nthcdr position pool))
                   (cons (nth position pool)
                         (take (1- count) (nthcdr (+ 1 position) pool)))))
   :hints (("Goal" :induct (nthcdr position pool)
            :in-theory (enable take nthcdr nth)))))

(defthm fn-hrcur-cold-opaque-span-supply-refines-residual
  (implies (and (fn-hrcur-cold-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :opaque-span)
                (< 0 (fn-hrcur-field 8 c))
                (equal position (fn-hrcur-field 2 c))
                (equal byte (nth position pool)))
    (let ((next (mv-nth 2 (fn-hrcur-cold-supply c position byte))))
      (and (eq (mv-nth 0 (fn-hrcur-cold-supply c position byte)) :emit)
           (equal (mv-nth 1 (fn-hrcur-cold-supply c position byte)) byte)
           (fn-hrcur-cold-invariantp next pool)
           (equal (fn-hrcur-cold-rest c pool)
                  (cons byte (fn-hrcur-cold-rest next pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-cold-pool-slice-step
                            (position (fn-hrcur-field 2 c)) (count (fn-hrcur-field 8 c)))
                 (:instance fn-hrcur-cold-pool-byte (position (fn-hrcur-field 2 c))))
           :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-supply
                              fn-hrcur-cold-state fn-hrcur-cold-rest fn-hrcur-cold-countp)
                             (fn-hrcur-cold-tasksp fn-hrcur-cold-tasks-rest take nthcdr nth
                              fn-hrcur-cold-pool-slice-step fn-hrcur-cold-pool-byte)))))

(local
 (defthm fn-hrcur-cold-abstract-pair-unfolds
   (implies (eq (fn-hrcur-field 0 node) :pair)
            (equal (fn-hdc-abstract node pool)
                   (cons (fn-hdc-abstract (fn-hrcur-field 1 node) pool)
                         (fn-hdc-abstract (fn-hrcur-field 2 node) pool))))
   :hints (("Goal" :do-not-induct t :expand ((fn-hdc-abstract node pool))
            :in-theory (enable fn-hrcur-field)))))
(local
 (defthm fn-hrcur-cold-abstract-atom-unfolds
   (implies (eq (fn-hrcur-field 0 node) :atom)
            (equal (fn-hdc-abstract node pool) (fn-hrcur-field 1 node)))
   :hints (("Goal" :do-not-induct t :expand ((fn-hdc-abstract node pool))
            :in-theory (enable fn-hrcur-field)))))
(local
 (defthm fn-hrcur-cold-abstract-octet-unfolds
   (implies (fn-hrcur-dos-domainp node pool)
            (equal (fn-scc-octetp (fn-hdc-abstract node pool))
                   (and (eq (fn-hrcur-field 0 node) :atom)
                        (fn-scc-octetp (fn-hrcur-field 1 node)) t)))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hrcur-dos-domainp node pool) (fn-hdc-abstract node pool))
            :in-theory (enable fn-hrcur-dos-domainp fn-hdc-abstract
                               fn-hrcur-field fn-scc-octetp fn-scc-intern)))))
(local
 (defthm fn-hrcur-cold-rejected-tail-unfolds
   (implies (and (fn-hrcur-dos-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :pair)
                 (eq (fn-hrcur-field 0 (fn-hrcur-field 1 node)) :atom)
                 (fn-scc-octetp (fn-hrcur-field 1 (fn-hrcur-field 1 node)))
                 (not (fn-scc-octets-valuep (fn-hdc-abstract node pool))))
            (not (fn-scc-octets-valuep
                    (fn-hdc-abstract (fn-hrcur-field 2 node) pool))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-cold-abstract-pair-unfolds)
                  (:instance fn-hrcur-cold-abstract-octet-unfolds
                             (node (fn-hrcur-field 1 node))))
            :expand ((fn-hrcur-dos-domainp node pool))
            :in-theory (e/d (fn-scc-octets-valuep fn-scc-octet-listp)
                             (fn-hrcur-dos-domainp fn-hdc-abstract
                              fn-hrcur-cold-abstract-pair-unfolds
                              fn-hrcur-cold-abstract-octet-unfolds))))))
(local
 (defthm fn-hrcur-cold-prefix-to-rejected-unfolds
   (implies (and (fn-hrcur-dos-domainp original pool)
                 (fn-hrcur-dos-prefixp original current count)
                 (not (fn-scc-octets-valuep (fn-hdc-abstract original pool))))
            (fn-hrcur-cold-rejected-prefixp original count pool))
   :hints (("Goal" :induct (fn-hrcur-dos-prefixp original current count)
            :in-theory (e/d (fn-hrcur-dos-prefixp fn-hrcur-cold-rejected-prefixp)
                             (fn-hdc-abstract fn-scc-octets-valuep fn-scc-octet-listp))
            :expand ((fn-hrcur-dos-domainp original pool))))))
(local
 (defthm fn-hrcur-cold-dos-keeps-original-unfolds
   (and (equal (fn-hrcur-field 1 (mv-nth 1 (fn-hrcur-dos-tick child)))
               (fn-hrcur-field 1 child))
        (equal (fn-hrcur-field 1 (mv-nth 1 (fn-hrcur-dos-supply child position byte)))
               (fn-hrcur-field 1 child)))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-hrcur-dos-tick fn-hrcur-dos-supply
                               fn-hrcur-dos-set fn-hrcur-dos-close)))))
(local
 (defthm fn-hrcur-cold-dos-control-unfolds
   (implies (fn-hrcur-dos-invariantp child pool)
            (and (fn-hrcur-dos-shapep child)
                 (fn-hrcur-cold-countp (fn-hrcur-field 3 child))
                 (member-eq (fn-hrcur-field 0 child) '(:scan :nil :octets :not-octets))))
   :hints (("Goal" :in-theory (e/d (fn-hrcur-dos-invariantp fn-hrcur-dos-shapep fn-hrcur-cold-countp)
                                  (fn-hrcur-dos-domainp fn-hrcur-dos-prefixp
                                   fn-hrcur-dos-value fn-hdc-abstract))))))
(local
 (defthm fn-hrcur-cold-dos-verdicts-unfolds
   (implies (fn-hrcur-dos-invariantp child pool)
     (let ((v (mv-nth 0 (fn-hrcur-dos-tick child))))
       (or (eq v :continue) (eq (fn-hrcur-field 0 v) :need-byte)
           (equal v '(:done :not-octets))
           (and (equal (fn-hrcur-field 0 v) :done)
                (equal (fn-hrcur-field 1 v) :octets)
                (fn-hrcur-cold-countp (fn-hrcur-field 2 v))
                (< 0 (fn-hrcur-field 2 v))))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-dos-tick-preserves-classification (c child))
                  (:instance fn-hrcur-cold-dos-control-unfolds))
            :in-theory (e/d (fn-hrcur-dos-tick fn-hrcur-dos-invariantp fn-hrcur-dos-shapep
                              fn-hrcur-dos-set fn-hrcur-dos-close fn-hrcur-cold-countp
                              fn-hrcur-nil-tick)
                             (fn-hrcur-dos-tick-preserves-classification
                              fn-hrcur-cold-dos-control-unfolds fn-hrcur-dos-domainp
                              fn-hrcur-dos-prefixp fn-hrcur-dos-value fn-hdc-abstract))))))

(local
 (defthm fn-hrcur-cold-dos-rejected-prefix-unfolds
   (implies (and (fn-hrcur-dos-invariantp child pool)
                 (equal (mv-nth 0 (fn-hrcur-dos-tick child)) '(:done :not-octets)))
            (fn-hrcur-cold-rejected-prefixp
              (fn-hrcur-field 1 child) (fn-hrcur-field 3 child) pool))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-dos-terminal-rejection-refines-current-codec (c child))
                  (:instance fn-hrcur-cold-prefix-to-rejected-unfolds
                             (original (fn-hrcur-field 1 child))
                             (current (fn-hrcur-field 2 child))
                             (count (fn-hrcur-field 3 child))))
            :in-theory (e/d (fn-hrcur-dos-invariantp fn-hrcur-dos-tick fn-hrcur-nil-tick)
                             (fn-hrcur-cold-prefix-to-rejected-unfolds
                              fn-hrcur-dos-terminal-rejection-refines-current-codec
                              fn-hrcur-dos-domainp fn-hrcur-dos-prefixp fn-hrcur-dos-value
                              fn-hrcur-cold-rejected-prefixp fn-hdc-abstract))))))
(local
 (defthm fn-hrcur-cold-dos-octets-terminal-unfolds
   (implies (and (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-dos-tick child))) :done)
                 (eq (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-dos-tick child))) :octets))
            (and (eq (fn-hrcur-field 0 child) :octets)
                 (equal (mv-nth 0 (fn-hrcur-dos-tick child))
                        (list :done :octets (fn-hrcur-field 3 child)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-hrcur-dos-tick fn-hrcur-nil-tick)))))
(local
 (defthm fn-hrcur-cold-opaque-codec-unfolds
   (implies (fn-scc-octets-valuep x)
            (equal (fn-scc-encode x)
                   (append (cons 6 (fn-scc-nat-octets (len x))) x)))
   :hints (("Goal" :in-theory (e/d (fn-scc-program)
                                  (fn-scc-octets-valuep fn-scc-atom-octets fn-scc-nat-octets))))))
; One more digit only when n reaches 256^k: floor(n/256) < p from n < 256p.
(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-hrcur-floor-256-below
     (implies (and (natp n) (natp p) (< n (* 256 p)))
              (< (floor n 256) p))
     :rule-classes :linear)))
(local
 (defthm fn-hrcur-cold-digits-length-bound
   (implies (and (natp n) (natp k) (< n (expt 256 k)))
            (<= (len (fn-scc-le-digits n)) k))
   :hints (("Goal" :induct (fn-scc-u64 n k)
            :in-theory (e/d (fn-scc-le-digits fn-scc-u64) (floor))))))
(local
 (defthm fn-hrcur-cold-header-octets-unfolds
   (implies (fn-hrcur-cold-countp n)
            (fn-scc-octet-listp (cons 6 (fn-scc-nat-octets n))))
   :hints (("Goal" :use ((:instance fn-hrcur-cold-digits-length-bound (k 8)))
            :in-theory (e/d (fn-hrcur-cold-countp fn-scc-nat-octets
                              fn-scc-octet-listp fn-scc-octetp)
                             (fn-scc-le-digits fn-hrcur-cold-digits-length-bound))))))

(defthm fn-hrcur-cold-classify-tick-refines-residual
  (implies (and (fn-hrcur-cold-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :classify))
    (let ((v (mv-nth 0 (fn-hrcur-cold-tick c)))
          (next (mv-nth 2 (fn-hrcur-cold-tick c))))
      (and (or (eq v :continue) (eq (fn-hrcur-field 0 v) :need-byte))
           (fn-hrcur-cold-invariantp next pool)
           (equal (fn-hrcur-cold-rest c pool) (fn-hrcur-cold-rest next pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-dos-tick-preserves-classification (c (fn-hrcur-field 2 c)))
                 (:instance fn-hrcur-cold-dos-control-unfolds (child (fn-hrcur-field 2 c)))
                 (:instance fn-hrcur-cold-dos-verdicts-unfolds (child (fn-hrcur-field 2 c)))
                 (:instance fn-hrcur-cold-dos-keeps-original-unfolds (child (fn-hrcur-field 2 c)))
                 (:instance fn-hrcur-cold-dos-rejected-prefix-unfolds (child (fn-hrcur-field 2 c)))
                 (:instance fn-hrcur-cold-dos-octets-terminal-unfolds (child (fn-hrcur-field 2 c)))
                 (:instance fn-hrcur-dos-terminal-refines-current-codec-classification
                   (c (fn-hrcur-field 2 c)) (count (fn-hrcur-field 3 (fn-hrcur-field 2 c)))))
           :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-tick fn-hrcur-cold-state
                              fn-hrcur-cold-rest fn-hrcur-cold-demand fn-hrcur-cold-tasksp
                              fn-hrcur-cold-taskp fn-hrcur-cold-task-rest fn-hrcur-cold-tasks-rest
                              fn-scc-octets-valuep fn-hrcur-cold-domainp)
                             (fn-hrcur-dos-tick fn-hrcur-dos-invariantp fn-hrcur-dos-domainp
                              fn-hrcur-dos-tick-preserves-classification fn-hdc-abstract
                              fn-hrcur-cold-dos-control-unfolds
                              fn-hrcur-cold-dos-verdicts-unfolds fn-hrcur-cold-dos-keeps-original-unfolds
                              fn-hrcur-cold-dos-rejected-prefix-unfolds
                              fn-hrcur-cold-dos-octets-terminal-unfolds
                              fn-hrcur-cold-rejected-prefixp fn-scc-nat-octets)))))

(local
 (defthm fn-hrcur-cold-field-is-nth
   (implies (natp i) (equal (fn-hrcur-field i x) (nth i x)))
   :hints (("Goal" :induct (fn-hrcur-field i x)
            :in-theory (enable fn-hrcur-field nth)))))
(local (in-theory (disable fn-hrcur-cold-field-is-nth)))
(local
 (defthm fn-hrcur-cold-len-take-unfolds
   (equal (len (take n xs)) (nfix n))
   :hints (("Goal" :induct (take n xs) :in-theory (enable take)))))
(local
 (defthm fn-hrcur-cold-span-six-abstract-unfolds
   (implies (and (fn-hrcur-dos-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :span)
                 (equal (fn-hrcur-field 1 node) 6))
            (and (equal (fn-hdc-abstract node pool)
                        (take (fn-hrcur-field 4 node)
                              (nthcdr (fn-hrcur-field 3 node) pool)))
                 (equal (len (fn-hdc-abstract node pool)) (fn-hrcur-field 4 node))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hrcur-dos-domainp node pool) (fn-hdc-abstract node pool))
            :in-theory (e/d (fn-hrcur-cold-field-is-nth)
                             (fn-hrcur-dos-domainp fn-hdc-abstract take nthcdr))))))
(local
 (defthm fn-hrcur-cold-opaque-node-kind-unfolds
   (implies (and (fn-hrcur-dos-domainp node pool)
                 (fn-scc-octet-listp (fn-hdc-abstract node pool))
                 (consp (fn-hdc-abstract node pool)))
            (or (eq (fn-hrcur-field 0 node) :pair)
                (and (eq (fn-hrcur-field 0 node) :span)
                     (equal (fn-hrcur-field 1 node) 6))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hrcur-dos-domainp node pool) (fn-hdc-abstract node pool))
            :in-theory (enable fn-hrcur-field fn-scc-octet-listp fn-scc-intern)))))
(local
 (defthm fn-hrcur-cold-domain-fields-unfolds
   (implies (fn-hrcur-dos-domainp node pool)
            (and
             (implies (eq (fn-hrcur-field 0 node) :pair)
               (and (fn-hrcur-dos-domainp (fn-hrcur-field 1 node) pool)
                    (fn-hrcur-dos-domainp (fn-hrcur-field 2 node) pool)))
             (implies (eq (fn-hrcur-field 0 node) :span)
               (and (fn-hrcur-cold-countp (fn-hrcur-field 3 node))
                    (fn-hrcur-cold-countp (fn-hrcur-field 4 node))
                    (< (+ (fn-hrcur-field 3 node) (fn-hrcur-field 4 node))
                       *fn-hrcur-u64-bound*)
                    (<= (+ (fn-hrcur-field 3 node) (fn-hrcur-field 4 node))
                        (len pool))))))
   :hints (("Goal" :expand ((fn-hrcur-dos-domainp node pool))
            :in-theory (e/d (fn-hrcur-cold-countp) (fn-hrcur-dos-domainp))))))

(local
 (defthm fn-hrcur-cold-opaque-pair-unfolds
   (implies (and (fn-hrcur-dos-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :pair)
                 (fn-scc-octet-listp (fn-hdc-abstract node pool)))
     (and (eq (fn-hrcur-field 0 (fn-hrcur-field 1 node)) :atom)
          (fn-scc-octetp (fn-hrcur-field 1 (fn-hrcur-field 1 node)))
          (fn-hrcur-dos-domainp (fn-hrcur-field 2 node) pool)
          (fn-scc-octet-listp (fn-hdc-abstract (fn-hrcur-field 2 node) pool))
          (equal (fn-hdc-abstract node pool)
                 (cons (fn-hrcur-field 1 (fn-hrcur-field 1 node))
                       (fn-hdc-abstract (fn-hrcur-field 2 node) pool)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-cold-abstract-pair-unfolds)
                  (:instance fn-hrcur-cold-abstract-octet-unfolds (node (fn-hrcur-field 1 node)))
                  (:instance fn-hrcur-cold-abstract-atom-unfolds (node (fn-hrcur-field 1 node))))
            :expand ((fn-hrcur-dos-domainp node pool))
            :in-theory (e/d (fn-scc-octet-listp)
                             (fn-hrcur-dos-domainp fn-hdc-abstract fn-scc-octetp
                              fn-hrcur-cold-abstract-pair-unfolds
                              fn-hrcur-cold-abstract-octet-unfolds
                              fn-hrcur-cold-abstract-atom-unfolds))))))

(defthm fn-hrcur-cold-opaque-tick-refines-residual
  (implies (and (fn-hrcur-cold-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :opaque))
    (let ((v (mv-nth 0 (fn-hrcur-cold-tick c)))
          (b (mv-nth 1 (fn-hrcur-cold-tick c)))
          (next (mv-nth 2 (fn-hrcur-cold-tick c))))
      (and (member-eq v '(:continue :emit))
           (fn-hrcur-cold-invariantp next pool)
           (equal (fn-hrcur-cold-rest c pool)
                  (if (eq v :emit) (cons b (fn-hrcur-cold-rest next pool))
                    (fn-hrcur-cold-rest next pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((equal (fn-hrcur-field 8 c) 0)
                   (eq (fn-hrcur-field 0 (fn-hrcur-field 7 c)) :pair))
           :use ((:instance fn-hrcur-cold-octets-zero-length
                            (x (fn-hdc-abstract (fn-hrcur-field 7 c) pool)))
                 (:instance fn-hrcur-cold-opaque-node-kind-unfolds (node (fn-hrcur-field 7 c)))
                 (:instance fn-hrcur-cold-domain-fields-unfolds (node (fn-hrcur-field 7 c)))
                 (:instance fn-hrcur-cold-opaque-pair-unfolds (node (fn-hrcur-field 7 c)))
                 (:instance fn-hrcur-cold-span-six-abstract-unfolds (node (fn-hrcur-field 7 c))))
           :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-tick fn-hrcur-cold-state
                              fn-hrcur-cold-rest fn-hrcur-cold-countp fn-scc-octet-listp)
                             (fn-hrcur-cold-tasksp fn-hrcur-cold-tasks-rest fn-hrcur-dos-domainp
                              fn-hdc-abstract take nthcdr fn-scc-octetp
                              fn-hrcur-cold-opaque-node-kind-unfolds fn-hrcur-cold-domain-fields-unfolds
                              fn-hdsn-denote fn-hdsn-coherent fn-hdsn-classify-name
                              fn-hrcur-cold-opaque-pair-unfolds
                              fn-hrcur-cold-abstract-atom-unfolds
                              fn-hrcur-cold-abstract-pair-unfolds fn-hrcur-cold-abstract-octet-unfolds
                              fn-hrcur-cold-span-six-abstract-unfolds)))))

; Shared proof predicate over the actual public tick, not an alternate machine.
(defun-nx fn-hrcur-cold-tick-lawp (c pool)
  (let ((v (mv-nth 0 (fn-hrcur-cold-tick c)))
        (b (mv-nth 1 (fn-hrcur-cold-tick c)))
        (next (mv-nth 2 (fn-hrcur-cold-tick c))))
    (and (or (member-eq v '(:continue :emit :prepared))
             (eq (fn-hrcur-field 0 v) :need-byte))
         (fn-hrcur-cold-invariantp next pool)
         (equal (fn-hrcur-cold-rest c pool)
                (if (eq v :emit) (cons b (fn-hrcur-cold-rest next pool))
                  (fn-hrcur-cold-rest next pool)))
         (implies (eq v :emit) (fn-scc-octetp b))
         (implies (eq v :prepared) (equal (fn-hrcur-cold-rest c pool) nil)))))

(local
 (defthm fn-hrcur-cold-tasksp-cons-unfolds
   (equal (fn-hrcur-cold-tasksp (cons a d) pool)
          (and (fn-hrcur-cold-taskp a pool) (fn-hrcur-cold-tasksp d pool)))
   :hints (("Goal" :in-theory (enable fn-hrcur-cold-tasksp)))))
(local
 (defthm fn-hrcur-cold-tasks-rest-cons-unfolds
   (equal (fn-hrcur-cold-tasks-rest (cons a d) pool)
          (append (fn-hrcur-cold-task-rest a pool) (fn-hrcur-cold-tasks-rest d pool)))
   :hints (("Goal" :in-theory (enable fn-hrcur-cold-tasks-rest)))))
(local
 (defthm fn-hrcur-cold-tasksp-control-unfolds
   (implies (fn-hrcur-cold-tasksp tasks pool)
            (if (consp tasks)
                (and (fn-hrcur-cold-taskp (car tasks) pool)
                     (fn-hrcur-cold-tasksp (cdr tasks) pool))
              (equal tasks nil)))
   :hints (("Goal" :expand ((fn-hrcur-cold-tasksp tasks pool))
            :in-theory (disable fn-hrcur-cold-tasksp)))))
(local
 (defthm fn-hrcur-cold-tasks-empty-rest-unfolds
   (equal (fn-hrcur-cold-tasks-rest nil pool) nil)
   :hints (("Goal" :in-theory (enable fn-hrcur-cold-tasks-rest)))))
(local
 (defthm fn-hrcur-cold-work-empty-law
   (implies (and (fn-hrcur-cold-invariantp c pool)
                 (eq (fn-hrcur-field 0 c) :work)
                 (not (consp (fn-hrcur-field 1 c))))
            (fn-hrcur-cold-tick-lawp c pool))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-cold-tasksp-control-unfolds
                             (tasks (fn-hrcur-field 1 c))))
            :in-theory (e/d (fn-hrcur-cold-tick-lawp fn-hrcur-cold-invariantp
                              fn-hrcur-cold-tick fn-hrcur-cold-state fn-hrcur-cold-rest)
                             (fn-hrcur-cold-tasksp fn-hrcur-cold-tasks-rest
                              fn-hrcur-cold-tasksp-control-unfolds))))))
(local
 (defthm fn-hrcur-cold-work-byte-law
   (implies (and (fn-hrcur-cold-invariantp c pool)
                 (eq (fn-hrcur-field 0 c) :work)
                 (consp (fn-hrcur-field 1 c))
                 (eq (fn-hrcur-field 0 (car (fn-hrcur-field 1 c))) :byte))
            (fn-hrcur-cold-tick-lawp c pool))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-cold-tasksp-control-unfolds
                             (tasks (fn-hrcur-field 1 c))))
            :expand ((fn-hrcur-cold-tasks-rest (fn-hrcur-field 1 c) pool))
            :in-theory (e/d (fn-hrcur-cold-tick-lawp fn-hrcur-cold-invariantp
                              fn-hrcur-cold-tick fn-hrcur-cold-state fn-hrcur-cold-rest
                              fn-hrcur-cold-taskp fn-hrcur-cold-task-rest)
                             (fn-hrcur-cold-tasksp fn-hrcur-cold-tasks-rest
                              fn-hrcur-cold-tasksp-control-unfolds))))))

(local
 (defthm fn-hrcur-cold-atom-domain-control-unfolds
   (implies (and (fn-hrcur-cold-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :atom))
            (and (fn-hrsc-domainp (fn-hrcur-field 1 node))
                 (not (consp (fn-hrcur-field 1 node)))
                 (equal (fn-hdc-abstract node pool) (fn-hrcur-field 1 node))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hrcur-cold-domainp node pool)
                     (fn-hrcur-dos-domainp node pool) (fn-hdc-abstract node pool))
            :in-theory (e/d (fn-hrcur-field)
                             (fn-hrcur-cold-domainp fn-hrcur-dos-domainp fn-hdc-abstract
                              fn-hrsc-domainp))))))
(local
 (defthm fn-hrcur-cold-atom-codec-unfolds
   (implies (not (consp x))
            (equal (fn-scc-encode x) (fn-scc-atom-octets x)))
   :hints (("Goal" :in-theory (e/d (fn-scc-program fn-scc-octets-valuep)
                                  (fn-scc-atom-octets))))))
(local
 (defthm fn-hrcur-cold-work-atom-law
   (implies (and (fn-hrcur-cold-invariantp c pool)
                 (eq (fn-hrcur-field 0 c) :work)
                 (consp (fn-hrcur-field 1 c))
                 (member-eq (fn-hrcur-field 0 (car (fn-hrcur-field 1 c))) '(:node :no-octets))
                 (eq (fn-hrcur-field 0 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))) :atom))
            (fn-hrcur-cold-tick-lawp c pool))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-cold-tasksp-control-unfolds (tasks (fn-hrcur-field 1 c)))
                  (:instance fn-hrcur-cold-atom-domain-control-unfolds
                    (node (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
                  (:instance fn-hrsc-begin-refines-atom-codec
                    (x (fn-hrcur-field 1 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
                    (capture (fn-hrcur-field 4 c)) (lease (fn-hrcur-field 5 c))))
            :expand ((fn-hrcur-cold-tasks-rest (fn-hrcur-field 1 c) pool))
            :in-theory (e/d (fn-hrcur-cold-tick-lawp fn-hrcur-cold-invariantp
                              fn-hrcur-cold-tick fn-hrcur-cold-state fn-hrcur-cold-rest
                              fn-hrcur-cold-taskp fn-hrcur-cold-task-rest)
                             (fn-hrcur-cold-tasksp fn-hrcur-cold-tasks-rest
                              fn-hrcur-cold-tasksp-control-unfolds
                              fn-hrcur-cold-atom-domain-control-unfolds
                              fn-hrcur-cold-domainp fn-hdc-abstract fn-hrsc-begin
                              fn-hrsc-rest fn-hrsc-invariantp fn-hrsc-domainp
                              fn-hrsc-begin-refines-atom-codec fn-hrcur-cold-rejected-prefixp))))))

(local
 (defthm fn-hrcur-cold-pair-domain-control-unfolds
   (implies (and (fn-hrcur-cold-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :pair))
            (and (fn-hrcur-dos-domainp node pool)
                 (< (len (fn-hdc-abstract node pool)) *fn-hrcur-u64-bound*)
                 (fn-hrcur-cold-domainp (fn-hrcur-field 1 node) pool)
                 (fn-hrcur-cold-domainp (fn-hrcur-field 2 node) pool)))
   :hints (("Goal" :expand ((fn-hrcur-cold-domainp node pool))
            :in-theory (disable fn-hrcur-cold-domainp)))))
(local
 (defthm fn-hrcur-cold-work-pair-start-law
   (implies (and (fn-hrcur-cold-invariantp c pool)
                 (eq (fn-hrcur-field 0 c) :work)
                 (consp (fn-hrcur-field 1 c))
                 (eq (fn-hrcur-field 0 (car (fn-hrcur-field 1 c))) :node)
                 (eq (fn-hrcur-field 0 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))) :pair))
            (fn-hrcur-cold-tick-lawp c pool))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-cold-tasksp-control-unfolds (tasks (fn-hrcur-field 1 c)))
                  (:instance fn-hrcur-cold-pair-domain-control-unfolds
                    (node (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
                  (:instance fn-hrcur-dos-begin-establishes-invariant
                    (node (fn-hrcur-field 1 (car (fn-hrcur-field 1 c))))
                    (capture (fn-hrcur-field 4 c)) (lease (fn-hrcur-field 5 c))))
            :expand ((fn-hrcur-cold-tasks-rest (fn-hrcur-field 1 c) pool))
            :in-theory (e/d (fn-hrcur-cold-tick-lawp fn-hrcur-cold-invariantp
                              fn-hrcur-cold-tick fn-hrcur-cold-state fn-hrcur-cold-rest
                              fn-hrcur-cold-taskp fn-hrcur-cold-task-rest fn-hrcur-dos-begin)
                             (fn-hrcur-cold-tasksp fn-hrcur-cold-tasks-rest
                              fn-hrcur-cold-tasksp-control-unfolds
                              fn-hrcur-cold-pair-domain-control-unfolds
                              fn-hrcur-cold-domainp fn-hdc-abstract fn-hrcur-dos-invariantp
                              fn-hrcur-dos-begin-establishes-invariant))))))

(local
 (defthm fn-hrcur-cold-cons-codec-unfolds
   (implies (not (fn-scc-octets-valuep (cons a d)))
            (equal (fn-scc-encode (cons a d))
                   (append (fn-scc-encode a) (fn-scc-encode d) '(5))))
   :hints (("Goal" :expand ((fn-scc-program (cons a d)))
            :in-theory (disable fn-scc-program fn-scc-octets-valuep fn-scc-atom-octets)))))
(local
 (defthm fn-hrcur-cold-rejected-control-unfolds
   (implies (fn-hrcur-cold-rejected-prefixp node count pool)
            (and (not (fn-scc-octets-valuep (fn-hdc-abstract node pool)))
                 (implies (and (natp count) (< 0 count))
                   (fn-hrcur-cold-rejected-prefixp
                     (fn-hrcur-field 2 node) (1- count) pool))))
   :hints (("Goal" :expand ((fn-hrcur-cold-rejected-prefixp node count pool))
            :in-theory (disable fn-hrcur-cold-rejected-prefixp fn-hdc-abstract
                                fn-scc-octets-valuep)))))
(local
 (defthm fn-hrcur-cold-work-rejected-pair-law
   (implies (and (fn-hrcur-cold-invariantp c pool)
                 (eq (fn-hrcur-field 0 c) :work)
                 (consp (fn-hrcur-field 1 c))
                 (eq (fn-hrcur-field 0 (car (fn-hrcur-field 1 c))) :no-octets)
                 (eq (fn-hrcur-field 0 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))) :pair))
            (fn-hrcur-cold-tick-lawp c pool))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-cold-tasksp-control-unfolds (tasks (fn-hrcur-field 1 c)))
                  (:instance fn-hrcur-cold-pair-domain-control-unfolds
                    (node (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
                  (:instance fn-hrcur-cold-abstract-pair-unfolds
                    (node (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
                  (:instance fn-hrcur-cold-rejected-control-unfolds
                    (node (fn-hrcur-field 1 (car (fn-hrcur-field 1 c))))
                    (count (fn-hrcur-field 2 (car (fn-hrcur-field 1 c)))))
                  (:instance fn-hrcur-cold-cons-codec-unfolds
                    (a (fn-hdc-abstract (fn-hrcur-field 1 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))) pool))
                    (d (fn-hdc-abstract (fn-hrcur-field 2 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))) pool))))
            :expand ((fn-hrcur-cold-tasks-rest (fn-hrcur-field 1 c) pool))
            :in-theory (e/d (fn-hrcur-cold-tick-lawp fn-hrcur-cold-invariantp
                              fn-hrcur-cold-tick fn-hrcur-cold-state fn-hrcur-cold-rest
                              fn-hrcur-cold-taskp fn-hrcur-cold-task-rest fn-hrcur-cold-countp
                              fn-scc-octetp)
                             (fn-hrcur-cold-tasksp fn-hrcur-cold-tasks-rest
                              fn-hrcur-cold-tasksp-control-unfolds
                              fn-hrcur-cold-pair-domain-control-unfolds
                              fn-hrcur-cold-abstract-pair-unfolds fn-hrcur-cold-rejected-control-unfolds
                              fn-hrcur-cold-cons-codec-unfolds
                              fn-hrcur-cold-domainp fn-hdc-abstract fn-hrcur-cold-rejected-prefixp
                              fn-scc-octets-valuep)))))

)

(local
 (defthm fn-hrcur-cold-span-domain-control-unfolds
   (implies (and (fn-hrcur-cold-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :span))
     (and (fn-hrcur-widthp node 5)
          (member-equal (fn-hrcur-field 1 node) '(3 4 6))
          (member-equal (fn-hrcur-field 2 node) '(0 1 2))
          (or (equal (fn-hrcur-field 1 node) 4) (equal (fn-hrcur-field 2 node) 0))
          (fn-hrcur-cold-countp (fn-hrcur-field 3 node))
          (fn-hrcur-cold-countp (fn-hrcur-field 4 node))
          (< (+ (fn-hrcur-field 3 node) (fn-hrcur-field 4 node)) *fn-hrcur-u64-bound*)
          (<= (+ (fn-hrcur-field 3 node) (fn-hrcur-field 4 node)) (len pool))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
              (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
              '(fn-hrcur-cold-domainp fn-hrcur-dos-domainp fn-hrcur-cold-countp
                fn-hrcur-field natp member-equal))))))
(local
 (defthm fn-hrcur-cold-body-span-wire-unfolds
   (implies (and (fn-hrcur-cold-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :span)
                 (member-equal (fn-hrcur-field 1 node) '(3 6))
                 (fn-scc-octet-listp pool))
     (equal (fn-hrcur-span-wire (fn-hrcur-field 1 node) 0
              (fn-hrcur-field 3 node) (fn-hrcur-field 4 node) pool)
            (fn-scc-encode (fn-hdc-abstract node pool))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-cold-span-domain-control-unfolds)
                  (:instance fn-hrcur-span-string-refines-abstract-codec
                    (offset (fn-hrcur-field 3 node)) (count (fn-hrcur-field 4 node)))
                  (:instance fn-hrcur-span-octets-refines-abstract-codec
                    (offset (fn-hrcur-field 3 node)) (count (fn-hrcur-field 4 node))))
            :expand ((fn-hdc-abstract node pool))
            :in-theory (e/d (fn-hrcur-cold-field-is-nth fn-hdc-span fn-hdc-abstract)
                             (fn-hrcur-cold-domainp fn-hrcur-cold-span-domain-control-unfolds
                              fn-hrcur-span-wire fn-hrcur-span-string-refines-abstract-codec
                              fn-hrcur-span-octets-refines-abstract-codec))))))
(local
 (defthm fn-hrcur-cold-work-body-span-law
   (implies (and (fn-hrcur-cold-invariantp c pool)
                 (eq (fn-hrcur-field 0 c) :work)
                 (consp (fn-hrcur-field 1 c))
                 (member-eq (fn-hrcur-field 0 (car (fn-hrcur-field 1 c))) '(:node :no-octets))
                 (eq (fn-hrcur-field 0 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))) :span)
                 (member-equal (fn-hrcur-field 1 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))) '(3 6)))
     (fn-hrcur-cold-tick-lawp c pool))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :do-not '(preprocess)
     :use ((:instance fn-hrcur-cold-tasksp-control-unfolds (tasks (fn-hrcur-field 1 c)))
           (:instance fn-hrcur-cold-span-domain-control-unfolds
             (node (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
           (:instance fn-hrcur-cold-body-span-wire-unfolds
             (node (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
           (:instance fn-hrcur-span-begin-refines-wire
             (op (fn-hrcur-field 1 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
             (pkg (fn-hrcur-field 2 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
             (offset (fn-hrcur-field 3 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
             (count (fn-hrcur-field 4 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
             (capture (fn-hrcur-field 4 c)) (lease (fn-hrcur-field 5 c)))
)
     :expand ((fn-hrcur-cold-tasks-rest (fn-hrcur-field 1 c) pool))
     :in-theory (e/d (fn-hrcur-cold-tick-lawp fn-hrcur-cold-invariantp
                      fn-hrcur-cold-tick fn-hrcur-cold-state fn-hrcur-cold-rest
                      fn-hrcur-cold-taskp fn-hrcur-cold-task-rest fn-hrcur-cold-countp)
                     (fn-hrcur-cold-tasksp fn-hrcur-cold-tasks-rest
                      fn-hrcur-cold-tasksp-control-unfolds fn-hrcur-cold-span-domain-control-unfolds
                      fn-hrcur-cold-domainp fn-hdc-abstract fn-hrcur-cold-rejected-prefixp
                      fn-hrcur-cold-domain-fields-unfolds fn-hrcur-cold-opaque-node-kind-unfolds
                      fn-hrcur-cold-pair-domain-control-unfolds fn-hrcur-cold-atom-domain-control-unfolds
                      fn-hrcur-cold-span-six-abstract-unfolds fn-hrcur-cold-opaque-pair-unfolds
                      fn-hrcur-cold-abstract-octet-unfolds fn-hrcur-cold-rejected-tail-unfolds
                      fn-hrcur-cold-rejected-control-unfolds
                      fn-hrcur-span-begin fn-hrcur-span-rest fn-hrcur-span-invariantp fn-hrcur-span-wire
                      fn-hrcur-span-begin-refines-wire fn-hrcur-span-tick-refines-wire
                      fn-hrcur-span-supply-refines-wire fn-hrcur-span-string-refines-abstract-codec
                      fn-hrcur-span-octets-refines-abstract-codec))))))

(local
 (defthm fn-hrcur-cold-chars-length-unfolds
   (equal (len (fn-scc-octets-chars xs)) (len xs))
   :hints (("Goal" :induct (fn-scc-octets-chars xs)
            :in-theory (enable fn-scc-octets-chars)))))
(local
 (defthm fn-hrcur-cold-name-length-unfolds
   (implies (and (fn-hrcur-cold-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :span)
                 (fn-scc-octet-listp pool))
     (and (stringp (fn-hrcur-cold-name node pool))
          (equal (length (fn-hrcur-cold-name node pool)) (fn-hrcur-field 4 node))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-cold-span-domain-control-unfolds)
                  (:instance fn-hrcur-cold-chars-length-unfolds
                    (xs (take (fn-hrcur-field 4 node) (nthcdr (fn-hrcur-field 3 node) pool))))
                  (:instance fn-hrcur-cold-len-take-unfolds
                    (n (fn-hrcur-field 4 node)) (xs (nthcdr (fn-hrcur-field 3 node) pool))))
            :in-theory (e/d (fn-hrcur-cold-name length)
                            (fn-hrcur-cold-domainp fn-hrcur-cold-span-domain-control-unfolds
                             fn-scc-octets-chars take nthcdr))))))
(local
 (defthm fn-hrcur-cold-symbol-child-begin-unfolds
   (implies (and (member-equal pkg '(0 1 2))
                 (fn-hrcur-cold-countp off) (fn-hrcur-cold-countp count))
     (fn-hrcur-cold-symbol-childp (fn-hdsn-begin pkg off count)))
   :hints (("Goal" :use ((:instance fn-hdsn-begin-valid (offset off)))
            :in-theory (enable fn-hrcur-cold-symbol-childp fn-hdsn-begin fn-hdsn-state
                               fn-hrcur-cold-countp fn-hrcur-cold-field-is-nth)))))
(local
 (defthm fn-hrcur-cold-work-symbol-span-law
   (implies (and (fn-hrcur-cold-invariantp c pool)
                 (eq (fn-hrcur-field 0 c) :work)
                 (consp (fn-hrcur-field 1 c))
                 (member-eq (fn-hrcur-field 0 (car (fn-hrcur-field 1 c))) '(:node :no-octets))
                 (eq (fn-hrcur-field 0 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))) :span)
                 (equal (fn-hrcur-field 1 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))) 4))
     (fn-hrcur-cold-tick-lawp c pool))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hrcur-cold-tasksp-control-unfolds (tasks (fn-hrcur-field 1 c)))
           (:instance fn-hrcur-cold-span-domain-control-unfolds
             (node (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
           (:instance fn-hrcur-cold-name-length-unfolds
             (node (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
           (:instance fn-hrcur-cold-symbol-child-begin-unfolds
             (pkg (fn-hrcur-field 2 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
             (off (fn-hrcur-field 3 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
             (count (fn-hrcur-field 4 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c))))))
           (:instance fn-hrcur-cold-symbol-begin-budget
             (pkg (fn-hrcur-field 2 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
             (offset (fn-hrcur-field 3 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
             (count (fn-hrcur-field 4 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c))))))
           (:instance fn-hdsn-begin-denotes-canonical-classification
             (pkg (fn-hrcur-field 2 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
             (offset (fn-hrcur-field 3 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
             (count (fn-hrcur-field 4 (fn-hrcur-field 1 (car (fn-hrcur-field 1 c)))))
             (name (fn-hrcur-cold-name (fn-hrcur-field 1 (car (fn-hrcur-field 1 c))) pool))))
     :expand ((fn-hrcur-cold-tasks-rest (fn-hrcur-field 1 c) pool))
     :in-theory (e/d (fn-hrcur-cold-tick-lawp fn-hrcur-cold-invariantp
                      fn-hrcur-cold-tick fn-hrcur-cold-state fn-hrcur-cold-rest
                      fn-hrcur-cold-taskp fn-hrcur-cold-task-rest fn-hrcur-cold-countp
                      fn-hdsn-begin fn-hdsn-state)
                     (fn-hrcur-cold-tasksp fn-hrcur-cold-tasks-rest
                      fn-hrcur-cold-tasksp-control-unfolds fn-hrcur-cold-span-domain-control-unfolds
                      fn-hrcur-cold-name-length-unfolds fn-hrcur-cold-domainp fn-hrcur-cold-name
                      fn-hdc-abstract fn-hrcur-cold-rejected-prefixp fn-hdsn-denote
                      fn-hdsn-classify-name fn-hrcur-cold-symbol-childp fn-hrcur-cold-symbol-budgetp
                      fn-hrcur-cold-symbol-child-begin-unfolds fn-hrcur-cold-symbol-begin-budget))))))

(local
 (defthm fn-hrcur-cold-task-control-unfolds
   (implies (fn-hrcur-cold-taskp task pool)
     (or (and (eq (fn-hrcur-field 0 task) :byte)
              (fn-scc-octetp (fn-hrcur-field 1 task)))
         (and (member-eq (fn-hrcur-field 0 task) '(:node :no-octets))
              (fn-hrcur-cold-domainp (fn-hrcur-field 1 task) pool)
              (member-eq (fn-hrcur-field 0 (fn-hrcur-field 1 task)) '(:atom :pair :span))
              (implies (eq (fn-hrcur-field 0 (fn-hrcur-field 1 task)) :span)
                (member-equal (fn-hrcur-field 1 (fn-hrcur-field 1 task)) '(3 4 6))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :expand ((fn-hrcur-cold-domainp (fn-hrcur-field 1 task) pool)
              (fn-hrcur-dos-domainp (fn-hrcur-field 1 task) pool))
     :in-theory (e/d (fn-hrcur-cold-taskp)
                     (fn-hrcur-cold-domainp fn-hrcur-dos-domainp fn-hdc-abstract
                      fn-hrcur-cold-span-domain-control-unfolds
                      fn-hrcur-cold-pair-domain-control-unfolds
                      fn-hrcur-cold-atom-domain-control-unfolds
                      fn-hrcur-cold-domain-fields-unfolds))))))
(local
 (defthm fn-hrcur-cold-work-invariant-control-unfolds
   (implies (and (fn-hrcur-cold-invariantp c pool) (eq (fn-hrcur-field 0 c) :work))
     (fn-hrcur-cold-tasksp (fn-hrcur-field 1 c) pool))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-hrcur-cold-invariantp)))))
(local
 (defthm fn-hrcur-cold-work-tick-law
   (implies (and (fn-hrcur-cold-invariantp c pool) (eq (fn-hrcur-field 0 c) :work))
     (fn-hrcur-cold-tick-lawp c pool))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use (fn-hrcur-cold-work-invariant-control-unfolds fn-hrcur-cold-work-empty-law fn-hrcur-cold-work-byte-law
           fn-hrcur-cold-work-atom-law fn-hrcur-cold-work-pair-start-law
           fn-hrcur-cold-work-rejected-pair-law fn-hrcur-cold-work-body-span-law
           fn-hrcur-cold-work-symbol-span-law
           (:instance fn-hrcur-cold-tasksp-control-unfolds (tasks (fn-hrcur-field 1 c)))
           (:instance fn-hrcur-cold-task-control-unfolds (task (car (fn-hrcur-field 1 c)))))
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(member-equal))))))

(local
 (defthm fn-hrcur-cold-symbol-tick-coordinates-unfolds
   (and (equal (nth 0 (mv-nth 1 (fn-hdsn-tick child))) (nth 0 child))
        (equal (nth 1 (mv-nth 1 (fn-hdsn-tick child))) (nth 1 child))
        (equal (nth 2 (mv-nth 1 (fn-hdsn-tick child))) (nth 2 child)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hdsn-source-coordinate-preserved (c child)))
     :in-theory (disable fn-hdsn-tick fn-hdsn-supply fn-hdsn-next-candidate
                         fn-hdsn-source-coordinate-preserved)))))
(local
 (defthm fn-hrcur-cold-symbol-supply-coordinates-unfolds
   (and (equal (nth 0 (mv-nth 1 (fn-hdsn-supply position serial byte child))) (nth 0 child))
        (equal (nth 1 (mv-nth 1 (fn-hdsn-supply position serial byte child))) (nth 1 child))
        (equal (nth 2 (mv-nth 1 (fn-hdsn-supply position serial byte child))) (nth 2 child)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hdsn-source-coordinate-preserved (c child) (offset position)))
     :in-theory (disable fn-hdsn-tick fn-hdsn-supply fn-hdsn-next-candidate
                         fn-hdsn-source-coordinate-preserved)))))
(local
 (defthm fn-hrcur-cold-symbol-tick-child-unfolds
   (implies (and (fn-hrcur-cold-symbol-childp child)
                 (fn-hrcur-cold-symbol-budgetp child))
     (fn-hrcur-cold-symbol-childp (mv-nth 1 (fn-hdsn-tick child))))
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hrcur-cold-symbol-tick-coordinates-unfolds (child child))
           (:instance fn-hdsn-tick-valid (c child))
           (:instance fn-hdsn-state-fields (c (mv-nth 1 (fn-hdsn-tick child))))
           (:instance fn-hrcur-cold-symbol-tick-preserves-budget (c child))
           (:instance fn-hrcur-cold-symbol-serial-bound (c (mv-nth 1 (fn-hdsn-tick child)))))
     :in-theory (e/d (fn-hrcur-cold-symbol-childp fn-hrcur-cold-countp fn-hrcur-cold-field-is-nth)
                     (fn-hdsn-tick fn-hdsn-statep fn-hdsn-state-fields fn-hdsn-source-coordinate-preserved
                      fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-tick-preserves-budget))))))
(local
 (defthm fn-hrcur-cold-symbol-tick-verdict-unfolds
   (implies (fn-hdsn-coherent child)
     (or (eq (mv-nth 0 (fn-hdsn-tick child)) :continue)
         (eq (car (mv-nth 0 (fn-hdsn-tick child))) :need-byte)
         (eq (car (mv-nth 0 (fn-hdsn-tick child))) :done)))
   :hints (("Goal" :do-not-induct t
     :expand ((fn-hdsn-imports-p (nth 3 child)))
     :in-theory (e/d (fn-hdsn-coherent fn-hdsn-tick fn-hdsn-imports-p)
                     (fn-hdsn-statep))))))
(local
 (defthm fn-hrcur-cold-symbol-begin-wire-unfolds
   (implies (and (fn-hrcur-cold-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :span)
                 (equal (fn-hrcur-field 1 node) 4)
                 (fn-scc-octet-listp pool)
                 (equal descriptor (fn-hdsn-classify-name (fn-hrcur-field 2 node)
                                      (fn-hrcur-cold-name node pool))))
     (and (fn-hrcur-span-invariantp
            (fn-hrcur-ns-begin descriptor (fn-hrcur-field 3 node) (fn-hrcur-field 4 node) capture lease) pool)
          (equal (fn-hrcur-span-rest
                   (fn-hrcur-ns-begin descriptor (fn-hrcur-field 3 node) (fn-hrcur-field 4 node) capture lease) pool)
                 (fn-scc-encode (fn-hdc-abstract node pool)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hrcur-cold-span-domain-control-unfolds)
           (:instance fn-hrcur-ns-begin-refines-abstract-codec
             (pkg (fn-hrcur-field 2 node)) (offset (fn-hrcur-field 3 node)) (count (fn-hrcur-field 4 node))))
     :in-theory (e/d (fn-hrcur-cold-field-is-nth fn-hrcur-cold-countp fn-hrcur-cold-name
                      fn-hdc-abstract fn-hdc-span)
                     (fn-hrcur-cold-domainp fn-hrcur-cold-span-domain-control-unfolds
                      fn-hrcur-ns-begin fn-hrcur-span-invariantp fn-hrcur-span-rest
                      fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire
                      fn-hrcur-ns-begin-refines-abstract-codec fn-hdsn-classify-name))))))
(local
 (defthm fn-hrcur-cold-symbol-control-unfolds
   (and (implies (fn-hrcur-cold-symbol-childp child) (fn-hdsn-statep child))
        (implies (fn-hrcur-cold-symbol-budgetp child) (fn-hdsn-coherent child)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-hrcur-cold-symbol-childp fn-hrcur-cold-symbol-budgetp)
                                   (fn-hdsn-statep fn-hdsn-coherent fn-hdsn-work))))))
(defthm fn-hrcur-cold-symbol-tick-refines-residual
   (implies (and (fn-hrcur-cold-invariantp c pool) (eq (fn-hrcur-field 0 c) :symbol))
     (and (or (eq (mv-nth 0 (fn-hrcur-cold-tick c)) :continue)
              (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte))
          (fn-hrcur-cold-invariantp (mv-nth 2 (fn-hrcur-cold-tick c)) pool)
          (equal (fn-hrcur-cold-rest c pool)
                 (fn-hrcur-cold-rest (mv-nth 2 (fn-hrcur-cold-tick c)) pool))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hrcur-cold-symbol-tick-coordinates-unfolds (child (fn-hrcur-field 2 c)))
           (:instance fn-hrcur-cold-symbol-control-unfolds (child (fn-hrcur-field 2 c)))
           (:instance fn-hrcur-cold-name-length-unfolds (node (fn-hrcur-field 7 c)))
           (:instance fn-hrcur-cold-symbol-tick-child-unfolds (child (fn-hrcur-field 2 c)))
           (:instance fn-hrcur-cold-symbol-tick-verdict-unfolds (child (fn-hrcur-field 2 c)))
           (:instance fn-hdsn-tick-preserves-denotation
             (c (fn-hrcur-field 2 c)) (name (fn-hrcur-cold-name (fn-hrcur-field 7 c) pool)))
           (:instance fn-hdsn-done-is-denotation
             (c (fn-hrcur-field 2 c)) (name (fn-hrcur-cold-name (fn-hrcur-field 7 c) pool)))
           (:instance fn-hrcur-cold-symbol-begin-wire-unfolds
             (node (fn-hrcur-field 7 c))
             (descriptor (fn-hrcur-field 1 (mv-nth 0 (fn-hdsn-tick (fn-hrcur-field 2 c)))))
             (capture (fn-hrcur-field 4 c)) (lease (fn-hrcur-field 5 c))))
     :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-tick fn-hrcur-cold-state
                      fn-hrcur-cold-rest fn-hrcur-cold-demand fn-hrcur-cold-field-is-nth)
                     (fn-hrcur-cold-symbol-childp fn-hrcur-cold-symbol-budgetp fn-hdsn-work
                      fn-hrcur-cold-tasksp fn-hrcur-cold-tasks-rest fn-hrcur-cold-domainp fn-hrcur-cold-name
                      fn-hrcur-cold-name-length-unfolds fn-hrcur-cold-symbol-tick-child-unfolds
                      fn-hrcur-cold-symbol-tick-verdict-unfolds fn-hdsn-tick fn-hdsn-denote fn-hdsn-coherent
                      fn-hdsn-classify-name fn-hdsn-statep fn-hdsn-supply fn-hdsn-next-candidate fn-hdsn-source-coordinate-preserved fn-hrcur-ns-begin fn-hrcur-span-rest
                      fn-hrcur-span-invariantp fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire)))))

(local
 (defthm fn-hrcur-cold-nth-chars-unfolds
   (implies (and (fn-scc-octet-listp xs) (natp i) (< i (len xs)))
     (equal (char-code (nth i (fn-scc-octets-chars xs))) (nth i xs)))
   :hints (("Goal" :induct (nth i xs)
     :in-theory (enable nth fn-scc-octets-chars fn-scc-octet-listp fn-scc-octetp)))))
(local
 (defun fn-hrcur-cold-take-induct (i n xs)
   (declare (xargs :measure (nfix i)))
   (if (zp i) (list n xs)
     (fn-hrcur-cold-take-induct (1- i) (1- n) (cdr xs)))))
(local
 (defthm fn-hrcur-cold-nth-take-unfolds
   (implies (and (natp i) (natp n) (< i n))
     (equal (nth i (take n xs)) (nth i xs)))
   :hints (("Goal" :induct (fn-hrcur-cold-take-induct i n xs) :in-theory (enable nth take)))))
(local
 (defthm fn-hrcur-cold-nth-tail-unfolds
   (implies (and (natp off) (natp i))
     (equal (nth i (nthcdr off xs)) (nth (+ off i) xs)))
   :hints (("Goal" :induct (nthcdr off xs) :in-theory (enable nth nthcdr)))))
(local
 (defthm fn-hrcur-cold-tail-length-unfolds
   (implies (and (natp off) (<= off (len xs)))
     (equal (len (nthcdr off xs)) (- (len xs) off)))
   :hints (("Goal" :induct (nthcdr off xs) :in-theory (enable nthcdr)))))
(local
 (defthm fn-hrcur-cold-name-byte-unfolds
   (implies (and (fn-hrcur-cold-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :span)
                 (fn-scc-octet-listp pool) (natp i) (< i (fn-hrcur-field 4 node)))
     (equal (char-code (char (fn-hrcur-cold-name node pool) i))
            (nth (+ (fn-hrcur-field 3 node) i) pool)))
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hrcur-cold-span-domain-control-unfolds)
           (:instance fn-scc-octet-listp-take
             (x (nthcdr (fn-hrcur-field 3 node) pool)) (n (fn-hrcur-field 4 node)))
           (:instance fn-hrcur-cold-tail-length-unfolds
             (off (fn-hrcur-field 3 node)) (xs pool))
           (:instance fn-hrcur-cold-nth-take-unfolds
             (n (fn-hrcur-field 4 node)) (xs (nthcdr (fn-hrcur-field 3 node) pool)))
           (:instance fn-hrcur-cold-nth-tail-unfolds
             (off (fn-hrcur-field 3 node)) (xs pool))
           (:instance fn-hrcur-cold-nth-chars-unfolds
             (xs (take (fn-hrcur-field 4 node) (nthcdr (fn-hrcur-field 3 node) pool)))))
     :in-theory (e/d (fn-hrcur-cold-name fn-hrcur-cold-countp char)
                     (fn-hrcur-cold-domainp fn-hrcur-cold-span-domain-control-unfolds
                      fn-scc-octets-chars take nthcdr nth fn-hrcur-cold-pool-slice-step))))))

(local
 (defthm fn-hrcur-cold-symbol-demand-control-unfolds
   (implies (and (fn-hdsn-coherent child)
                 (eq (car (mv-nth 0 (fn-hdsn-tick child))) :need-byte))
     (and (< (nth 4 child) (nth 2 child))
          (equal (cadr (mv-nth 0 (fn-hdsn-tick child))) (+ (nth 1 child) (nth 4 child)))
          (equal (caddr (mv-nth 0 (fn-hdsn-tick child))) (nth 5 child))))
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hdsn-state-fields (c child)))
     :in-theory (e/d (fn-hdsn-tick fn-hdsn-coherent)
                     (fn-hdsn-state-fields fn-hdsn-statep))))))
(local
 (defthm fn-hrcur-cold-symbol-demand-supply-unfolds
   (implies (and (fn-hdsn-coherent child)
                 (eq (car (mv-nth 0 (fn-hdsn-tick child))) :need-byte)
                 (equal position (cadr (mv-nth 0 (fn-hdsn-tick child))))
                 (fn-scc-octetp byte))
     (eq (mv-nth 0 (fn-hdsn-supply position (nth 5 child) byte child)) :continue))
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hdsn-state-fields (c child)))
     :in-theory (e/d (fn-hdsn-tick fn-hdsn-supply fn-hdsn-coherent)
                     (fn-hdsn-state-fields fn-hdsn-statep))))))
(local
 (defthm fn-hrcur-cold-symbol-supply-child-unfolds
   (implies (and (fn-hrcur-cold-symbol-childp child)
                 (fn-hrcur-cold-symbol-budgetp child))
     (fn-hrcur-cold-symbol-childp (mv-nth 1 (fn-hdsn-supply position serial byte child))))
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hrcur-cold-symbol-supply-coordinates-unfolds (child child))
           (:instance fn-hdsn-supply-valid (c child) (offset position))
           (:instance fn-hdsn-state-fields (c (mv-nth 1 (fn-hdsn-supply position serial byte child))))
           (:instance fn-hrcur-cold-symbol-supply-preserves-budget (c child))
           (:instance fn-hrcur-cold-symbol-serial-bound
             (c (mv-nth 1 (fn-hdsn-supply position serial byte child)))))
     :in-theory (e/d (fn-hrcur-cold-symbol-childp fn-hrcur-cold-countp fn-hrcur-cold-field-is-nth)
                     (fn-hdsn-supply fn-hdsn-statep fn-hdsn-state-fields fn-hdsn-source-coordinate-preserved
                      fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-supply-preserves-budget))))))
(local
 (defthm fn-hrcur-cold-symbol-demand-projection-unfolds
   (implies (and (fn-hrcur-widthp c 9)
                 (eq (fn-hrcur-field 0 c) :symbol)
                 (fn-hrcur-cold-symbol-childp (fn-hrcur-field 2 c))
                 (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte))
     (and (eq (car (mv-nth 0 (fn-hdsn-tick (fn-hrcur-field 2 c)))) :need-byte)
          (equal (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c)))
                 (cadr (mv-nth 0 (fn-hdsn-tick (fn-hrcur-field 2 c)))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :in-theory (e/d (fn-hrcur-cold-tick fn-hrcur-cold-demand fn-hrcur-cold-field-is-nth)
                     (fn-hdsn-tick fn-hrcur-cold-symbol-childp))))))
(local
 (defthm fn-hrcur-cold-symbol-supply-source-unfolds
  (implies (and (fn-hrcur-cold-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :symbol)
                (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
                (equal byte (nth position pool)))
    (and (fn-scc-octetp byte) (fn-hrcur-cold-countp position)
         (equal position (+ (nth 1 (fn-hrcur-field 2 c)) (nth 4 (fn-hrcur-field 2 c))))
         (< (nth 4 (fn-hrcur-field 2 c)) (nth 2 (fn-hrcur-field 2 c)))
         (equal (char-code (char (fn-hrcur-cold-name (fn-hrcur-field 7 c) pool)
                                (nth 4 (fn-hrcur-field 2 c)))) byte)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-hrcur-cold-symbol-demand-projection-unfolds)
          (:instance fn-hrcur-cold-symbol-control-unfolds (child (fn-hrcur-field 2 c)))
          (:instance fn-hrcur-cold-span-domain-control-unfolds (node (fn-hrcur-field 7 c)))
          (:instance fn-hrcur-cold-symbol-demand-control-unfolds (child (fn-hrcur-field 2 c)))
          (:instance fn-hdsn-state-fields (c (fn-hrcur-field 2 c)))
          (:instance fn-hrcur-cold-name-byte-unfolds
            (node (fn-hrcur-field 7 c)) (i (nth 4 (fn-hrcur-field 2 c))))
          (:instance fn-hrcur-cold-pool-byte))
    :in-theory (e/d (fn-hrcur-cold-invariantp
                     fn-hrcur-cold-countp fn-hrcur-cold-field-is-nth)
                    (fn-hrcur-cold-symbol-childp fn-hrcur-cold-symbol-budgetp fn-hdsn-work
                     fn-hrcur-cold-domainp fn-hrcur-cold-name fn-hrcur-cold-tasksp
                     fn-hrcur-cold-tick fn-hdsn-tick fn-hdsn-statep fn-hdsn-state-fields fn-hdsn-coherent
                     fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-begin
                     fn-hrcur-cold-span-domain-control-unfolds
                     fn-hrcur-cold-symbol-demand-control-unfolds
                     fn-hrcur-cold-name-byte-unfolds fn-hrcur-cold-pool-byte))))))
(local
 (defthm fn-hrcur-cold-symbol-supply-step-unfolds
   (implies (and (fn-hrcur-widthp c 9) (eq (fn-hrcur-field 0 c) :symbol)
                 (fn-hrcur-cold-symbol-childp (fn-hrcur-field 2 c))
                 (fn-hdsn-coherent (fn-hrcur-field 2 c))
                 (fn-hrcur-cold-countp position) (fn-scc-octetp byte)
                 (eq (car (mv-nth 0 (fn-hdsn-tick (fn-hrcur-field 2 c)))) :need-byte)
                 (equal position (cadr (mv-nth 0 (fn-hdsn-tick (fn-hrcur-field 2 c))))))
     (and (equal (mv-nth 0 (fn-hrcur-cold-supply c position byte)) :continue)
          (equal (mv-nth 2 (fn-hrcur-cold-supply c position byte))
                 (fn-hrcur-cold-state :symbol (fn-hrcur-field 1 c)
                   (mv-nth 1 (fn-hdsn-supply position (nth 5 (fn-hrcur-field 2 c)) byte
                                           (fn-hrcur-field 2 c)))
                   nil (fn-hrcur-field 7 c) 0 c))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hrcur-cold-symbol-demand-supply-unfolds (child (fn-hrcur-field 2 c))))
     :in-theory (e/d (fn-hrcur-cold-supply fn-hrcur-cold-field-is-nth)
                     (fn-hrcur-cold-symbol-childp fn-hrcur-cold-countp fn-hrcur-cold-state
                      fn-hdsn-tick fn-hdsn-supply fn-hdsn-coherent
                      fn-hrcur-cold-symbol-demand-supply-unfolds))))))
(local
 (defthm fn-hrcur-cold-symbol-invariant-control-unfolds
   (implies (and (fn-hrcur-cold-invariantp c pool) (eq (fn-hrcur-field 0 c) :symbol))
     (and (fn-hrcur-widthp c 9)
          (fn-hrcur-cold-symbol-childp (fn-hrcur-field 2 c))
          (fn-hrcur-cold-symbol-budgetp (fn-hrcur-field 2 c))
          (fn-hdsn-statep (fn-hrcur-field 2 c))
          (fn-hdsn-coherent (fn-hrcur-field 2 c))
          (stringp (fn-hrcur-cold-name (fn-hrcur-field 7 c) pool))
          (equal (length (fn-hrcur-cold-name (fn-hrcur-field 7 c) pool))
                 (nth 2 (fn-hrcur-field 2 c)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hrcur-cold-symbol-control-unfolds (child (fn-hrcur-field 2 c)))
           (:instance fn-hrcur-cold-name-length-unfolds (node (fn-hrcur-field 7 c))))
     :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-field-is-nth)
                     (fn-hrcur-cold-tasksp fn-hrcur-cold-domainp fn-hrcur-cold-name
                      fn-hrcur-cold-symbol-childp fn-hrcur-cold-symbol-budgetp
                      fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-coherent fn-hdsn-statep
                      fn-hrcur-cold-name-length-unfolds))))))
(local
 (defthm fn-hrcur-cold-symbol-replace-child-unfolds
   (implies (and (fn-hrcur-cold-invariantp c pool) (eq (fn-hrcur-field 0 c) :symbol)
                 (fn-hrcur-cold-symbol-childp next) (fn-hrcur-cold-symbol-budgetp next)
                 (equal (nth 0 next) (nth 0 (fn-hrcur-field 2 c)))
                 (equal (nth 1 next) (nth 1 (fn-hrcur-field 2 c)))
                 (equal (nth 2 next) (nth 2 (fn-hrcur-field 2 c)))
                 (equal (fn-hdsn-denote next (fn-hrcur-cold-name (fn-hrcur-field 7 c) pool))
                        (fn-hdsn-denote (fn-hrcur-field 2 c)
                                       (fn-hrcur-cold-name (fn-hrcur-field 7 c) pool))))
     (and (fn-hrcur-cold-invariantp
            (fn-hrcur-cold-state :symbol (fn-hrcur-field 1 c) next nil (fn-hrcur-field 7 c) 0 c) pool)
          (equal (fn-hrcur-cold-rest
                   (fn-hrcur-cold-state :symbol (fn-hrcur-field 1 c) next nil (fn-hrcur-field 7 c) 0 c) pool)
                 (fn-hrcur-cold-rest c pool))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-state fn-hrcur-cold-rest
                      fn-hrcur-cold-field-is-nth fn-hrcur-widthp)
                     (fn-hrcur-cold-tasksp fn-hrcur-cold-domainp fn-hrcur-cold-name
                      fn-hrcur-cold-symbol-childp fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-tasks-rest
                      fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-coherent fn-hdsn-statep))))))
(defthm fn-hrcur-cold-symbol-supply-refines-residual
  (implies (and (fn-hrcur-cold-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :symbol)
                (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
                (equal byte (nth position pool)))
    (and (eq (mv-nth 0 (fn-hrcur-cold-supply c position byte)) :continue)
         (fn-hrcur-cold-invariantp (mv-nth 2 (fn-hrcur-cold-supply c position byte)) pool)
         (equal (fn-hrcur-cold-rest c pool)
                (fn-hrcur-cold-rest (mv-nth 2 (fn-hrcur-cold-supply c position byte)) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-hrcur-cold-symbol-supply-source-unfolds)
          (:instance fn-hrcur-cold-symbol-demand-projection-unfolds)
          (:instance fn-hrcur-cold-symbol-invariant-control-unfolds)
          (:instance fn-hrcur-cold-symbol-supply-step-unfolds)
          (:instance fn-hrcur-cold-symbol-replace-child-unfolds
            (next (mv-nth 1 (fn-hdsn-supply position (nth 5 (fn-hrcur-field 2 c)) byte
                                          (fn-hrcur-field 2 c)))))
          (:instance fn-hrcur-cold-symbol-supply-preserves-budget (c (fn-hrcur-field 2 c))
            (serial (nth 5 (fn-hrcur-field 2 c))))
          (:instance fn-hrcur-cold-symbol-supply-coordinates-unfolds
            (child (fn-hrcur-field 2 c)) (serial (nth 5 (fn-hrcur-field 2 c))))
          (:instance fn-hrcur-cold-symbol-supply-child-unfolds
            (child (fn-hrcur-field 2 c)) (serial (nth 5 (fn-hrcur-field 2 c))))
          (:instance fn-hdsn-supply-preserves-denotation
            (c (fn-hrcur-field 2 c)) (offset position) (serial (nth 5 (fn-hrcur-field 2 c)))
            (name (fn-hrcur-cold-name (fn-hrcur-field 7 c) pool))))
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(eq not)))))

(local
 (defthm fn-hrcur-cold-classify-demand-control-unfolds
   (implies (and (fn-hrcur-dos-invariantp child pool)
                 (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-dos-tick child))) :need-byte))
     (and (eq (fn-hrcur-field 0 child) :nil)
          (eq (fn-hrcur-field 0 (fn-hrcur-field 4 child)) :check)
          (equal (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-dos-tick child)))
                 (+ (fn-hrcur-field 2 (fn-hrcur-field 4 child))
                    (fn-hrcur-field 4 (fn-hrcur-field 4 child))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :in-theory (e/d (fn-hrcur-dos-tick fn-hrcur-dos-invariantp fn-hrcur-dos-shapep
                      fn-hrcur-nil-tick fn-hrcur-cold-field-is-nth)
                     (fn-hrcur-dos-domainp fn-hrcur-dos-prefixp fn-hrcur-dos-value
                      fn-hrcur-nil-invariantp fn-hdc-abstract))))))
(defthm fn-hrcur-cold-classify-supply-refines-residual
  (implies (and (fn-hrcur-cold-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :classify)
                (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
                (equal byte (nth position pool)))
    (and (eq (mv-nth 0 (fn-hrcur-cold-supply c position byte)) :continue)
         (fn-hrcur-cold-invariantp (mv-nth 2 (fn-hrcur-cold-supply c position byte)) pool)
         (equal (fn-hrcur-cold-rest c pool)
                (fn-hrcur-cold-rest (mv-nth 2 (fn-hrcur-cold-supply c position byte)) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-hrcur-cold-classify-demand-control-unfolds (child (fn-hrcur-field 2 c)))
          (:instance fn-hrcur-dos-supply-preserves-classification (c (fn-hrcur-field 2 c)))
          (:instance fn-hrcur-cold-dos-keeps-original-unfolds (child (fn-hrcur-field 2 c))))
    :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-tick fn-hrcur-cold-supply
                     fn-hrcur-cold-state fn-hrcur-cold-rest fn-hrcur-cold-demand)
                    (fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-tasks-rest
                     fn-hrcur-dos-invariantp fn-hrcur-dos-tick fn-hrcur-dos-supply
                     fn-hrcur-dos-supply-preserves-classification
                     fn-hdsn-denote fn-hdsn-coherent fn-hdsn-classify-name
                     fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
                     fn-hrcur-cold-dos-keeps-original-unfolds)))))

(local
 (defthm fn-hrcur-cold-invariant-control-unfolds
   (implies (fn-hrcur-cold-invariantp c pool)
     (and (fn-hrcur-widthp c 9)
          (member-eq (fn-hrcur-field 0 c)
            '(:work :classify :scalar :span :symbol :opaque-prefix :opaque :opaque-span :done))
          (implies (eq (fn-hrcur-field 0 c) :scalar) (fn-hrsc-invariantp (fn-hrcur-field 2 c)))
          (implies (eq (fn-hrcur-field 0 c) :span) (fn-hrcur-span-invariantp (fn-hrcur-field 2 c) pool))
          (implies (eq (fn-hrcur-field 0 c) :done) (null (fn-hrcur-field 1 c)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(fn-hrcur-cold-invariantp member-eq member-equal eq not))))))
(local
 (defthm fn-hrcur-cold-done-law-unfolds
   (implies (and (fn-hrcur-cold-invariantp c pool) (eq (fn-hrcur-field 0 c) :done))
     (and (equal (mv-nth 0 (fn-hrcur-cold-tick c)) :prepared)
          (equal (mv-nth 2 (fn-hrcur-cold-tick c)) c)
          (equal (fn-hrcur-cold-rest c pool) nil)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-tick fn-hrcur-cold-rest)
                     (fn-hrcur-cold-tasksp fn-hrcur-cold-domainp fn-hrcur-cold-symbol-childp
                      fn-hrcur-cold-symbol-budgetp fn-hdsn-denote fn-hdsn-classify-name))))))
(local
 (defthm fn-hrcur-cold-span-tick-not-prepared-unfolds
   (implies (eq (fn-hrcur-field 0 c) :span)
            (not (eq (mv-nth 0 (fn-hrcur-cold-tick c)) :prepared)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :in-theory (e/d (fn-hrcur-cold-tick)
                     (fn-hrcur-span-tick fn-hrsc-tick))))))
(defthm fn-hrcur-cold-tick-preserves-current-codec-residual
   (implies (fn-hrcur-cold-invariantp c pool)
     (let ((v (mv-nth 0 (fn-hrcur-cold-tick c)))
           (b (mv-nth 1 (fn-hrcur-cold-tick c)))
           (next (mv-nth 2 (fn-hrcur-cold-tick c))))
       (and (fn-hrcur-cold-invariantp next pool)
            (equal (fn-hrcur-cold-rest c pool)
                   (if (eq v :emit) (cons b (fn-hrcur-cold-rest next pool))
                     (fn-hrcur-cold-rest next pool)))
            (implies (eq v :prepared) (equal (fn-hrcur-cold-rest c pool) nil)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use (fn-hrcur-cold-span-tick-not-prepared-unfolds
           fn-hrcur-cold-invariant-control-unfolds
           fn-hrcur-cold-work-tick-law
           fn-hrcur-cold-classify-tick-refines-residual
           fn-hrcur-cold-scalar-tick-refines-residual
           fn-hrcur-cold-scalar-tick-preserves-invariant
           fn-hrcur-cold-span-tick-refines-residual
           fn-hrcur-cold-span-tick-preserves-invariant
           fn-hrcur-cold-symbol-tick-refines-residual
           fn-hrcur-cold-prefix-tick-refines-residual
           fn-hrcur-cold-opaque-tick-refines-residual
           fn-hrcur-cold-opaque-span-tick-refines-residual
           fn-hrcur-cold-done-law-unfolds)
     :cases ((eq (fn-hrcur-field 0 c) :work) (eq (fn-hrcur-field 0 c) :classify)
             (eq (fn-hrcur-field 0 c) :scalar) (eq (fn-hrcur-field 0 c) :span)
             (eq (fn-hrcur-field 0 c) :symbol) (eq (fn-hrcur-field 0 c) :opaque-prefix)
             (eq (fn-hrcur-field 0 c) :opaque) (eq (fn-hrcur-field 0 c) :opaque-span))
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(fn-hrcur-cold-tick-lawp member-eq member-equal eq not)))))

(local
 (defthm fn-hrcur-cold-span-demand-control-unfolds
   (implies (and (fn-hrcur-cold-invariantp c pool) (eq (fn-hrcur-field 0 c) :span)
                 (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte))
     (and (eq (fn-hrcur-field 0 (fn-hrcur-field 2 c)) :body)
          (< 0 (fn-hrcur-field 3 (fn-hrcur-field 2 c)))
          (equal (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c)))
                 (fn-hrcur-field 2 (fn-hrcur-field 2 c)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-tick fn-hrcur-cold-demand
                      fn-hrcur-span-tick fn-hrcur-span-invariantp fn-hrcur-span-shapep
                      fn-hrcur-cold-field-is-nth)
                     (fn-hrcur-cold-tasksp fn-hrcur-cold-domainp fn-hrcur-cold-symbol-budgetp
                      fn-hrcur-cold-symbol-childp fn-hdsn-denote fn-hdsn-classify-name
                      fn-hdsn-coherent fn-hdsn-tick fn-hrcur-span-rest
                      fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire))))))
(local
 (defthm fn-hrcur-cold-span-supply-full-law
   (implies (and (fn-hrcur-cold-invariantp c pool) (eq (fn-hrcur-field 0 c) :span)
                 (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
                 (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
                 (equal byte (nth position pool)))
     (and (equal (mv-nth 0 (fn-hrcur-cold-supply c position byte)) :emit)
          (fn-hrcur-cold-invariantp (mv-nth 2 (fn-hrcur-cold-supply c position byte)) pool)
          (equal (fn-hrcur-cold-rest c pool)
                 (cons (mv-nth 1 (fn-hrcur-cold-supply c position byte))
                       (fn-hrcur-cold-rest (mv-nth 2 (fn-hrcur-cold-supply c position byte)) pool)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use (fn-hrcur-cold-span-demand-control-unfolds fn-hrcur-cold-span-supply-refines-residual)
     :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-supply fn-hrcur-cold-state)
                     (fn-hrcur-span-supply fn-hrcur-span-invariantp fn-hrcur-cold-rest
                      fn-hrcur-cold-tasksp fn-hrcur-cold-domainp fn-hrcur-cold-symbol-budgetp
                      fn-hrcur-cold-symbol-childp fn-hdsn-denote fn-hdsn-classify-name
                      fn-hdsn-coherent fn-hdsn-tick))))))
(local
 (defthm fn-hrcur-cold-demand-phase-control-unfolds
   (implies (and (fn-hrcur-cold-invariantp c pool)
                 (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte))
     (member-eq (fn-hrcur-field 0 c) '(:classify :symbol :span :opaque-span)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use (fn-hrcur-cold-invariant-control-unfolds
           (:instance fn-hrcur-cold-scalar-does-not-demand-unfolds (child (fn-hrcur-field 2 c))))
     :in-theory (e/d (fn-hrcur-cold-tick fn-hrcur-cold-demand fn-hrcur-cold-field-is-nth)
                     (fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-tasksp
                      fn-hrcur-cold-domainp fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
                      fn-hrcur-cold-scalar-does-not-demand-unfolds
                      fn-hdsn-tick fn-hdsn-begin fn-hrsc-tick fn-hrcur-span-tick fn-hrcur-dos-tick))))))
(local
 (defthm fn-hrcur-cold-opaque-span-demand-control-unfolds
   (implies (and (fn-hrcur-cold-invariantp c pool) (eq (fn-hrcur-field 0 c) :opaque-span)
                 (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte))
     (and (< 0 (fn-hrcur-field 8 c))
          (equal (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))) (fn-hrcur-field 2 c))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-tick fn-hrcur-cold-demand)
                     (fn-hrcur-cold-tasksp fn-hrcur-cold-domainp fn-hrcur-cold-symbol-budgetp
                      fn-hrcur-cold-symbol-childp fn-hdsn-denote fn-hdsn-classify-name
                      fn-hdsn-coherent))))))
(defthm fn-hrcur-cold-supply-preserves-current-codec-residual
   (implies (and (fn-hrcur-cold-invariantp c pool)
                 (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
                 (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
                 (equal byte (nth position pool)))
     (let ((v (mv-nth 0 (fn-hrcur-cold-supply c position byte)))
           (b (mv-nth 1 (fn-hrcur-cold-supply c position byte)))
           (next (mv-nth 2 (fn-hrcur-cold-supply c position byte))))
       (and (member-eq v '(:continue :emit)) (fn-hrcur-cold-invariantp next pool)
            (equal (fn-hrcur-cold-rest c pool)
                   (if (eq v :emit) (cons b (fn-hrcur-cold-rest next pool))
                     (fn-hrcur-cold-rest next pool))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use (fn-hrcur-cold-demand-phase-control-unfolds
           fn-hrcur-cold-opaque-span-demand-control-unfolds
           fn-hrcur-cold-classify-supply-refines-residual
           fn-hrcur-cold-symbol-supply-refines-residual
           fn-hrcur-cold-span-supply-full-law
           fn-hrcur-cold-opaque-span-supply-refines-residual)
     :cases ((eq (fn-hrcur-field 0 c) :classify) (eq (fn-hrcur-field 0 c) :symbol)
             (eq (fn-hrcur-field 0 c) :span))
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(eq not member-eq member-equal)))))

; Logical progress rank only. Runtime begin/tick/supply never evaluate it.
(defun-nx fn-hrcur-cold-task-credit (task)
  (case (fn-hrcur-field 0 task)
    (:byte 1)
    (:no-octets (nfix (- (* 2 (acl2-count (fn-hrcur-field 1 task))) 2)))
    (otherwise (* 2 (acl2-count (fn-hrcur-field 1 task))))))
(defun-nx fn-hrcur-cold-tasks-credit (tasks)
  (if (consp tasks)
      (+ (fn-hrcur-cold-task-credit (car tasks)) (fn-hrcur-cold-tasks-credit (cdr tasks)))
    0))
(defun-nx fn-hrcur-cold-phase-credit (phase)
  (case phase (:work 5) ((:classify :symbol) 4) ((:scalar :span :opaque-prefix) 3)
    (:opaque 2) (:opaque-span 1) (otherwise 0)))
(defun-nx fn-hrcur-cold-structural-credit (c)
  (+ (fn-hrcur-cold-tasks-credit (fn-hrcur-field 1 c))
     (case (fn-hrcur-field 0 c)
       (:classify (nfix (- (* 2 (acl2-count (fn-hrcur-field 7 c))) 1)))
       ((:symbol :scalar :span :opaque-prefix :opaque :opaque-span)
        (nfix (- (* 2 (acl2-count (fn-hrcur-field 7 c))) 2)))
       (otherwise 0))))
(defun-nx fn-hrcur-cold-child-credit (c)
  (let ((child (fn-hrcur-field 2 c)))
    (nfix (case (fn-hrcur-field 0 c)
      (:classify (fn-hrcur-dos-work child)) (:symbol (fn-hdsn-work child))
      (:scalar (fn-hrsc-work child)) (:span (fn-hrcur-span-work child))
      (:opaque-prefix (len (fn-hrcur-field 6 c)))
      (:opaque-span (fn-hrcur-field 8 c)) (otherwise 0)))))
(defun-nx fn-hrcur-cold-rank (c)
  (make-ord 2 (+ 1 (fn-hrcur-cold-structural-credit c))
    (make-ord 1 (+ 1 (fn-hrcur-cold-phase-credit (fn-hrcur-field 0 c)))
      (fn-hrcur-cold-child-credit c))))

(defun-nx fn-hrcur-cold-progress-invariantp (c pool)
  (and (fn-hrcur-cold-invariantp c pool)
       (implies (member-eq (fn-hrcur-field 0 c)
                  '(:classify :symbol :scalar :span :opaque-prefix :opaque :opaque-span))
                (<= 2 (acl2-count (fn-hrcur-field 7 c))))))
(local
 (defthm fn-hrcur-cold-task-credit-natural-unfolds
   (natp (fn-hrcur-cold-task-credit task))
   :hints (("Goal" :in-theory (enable fn-hrcur-cold-task-credit)))))
(local
 (defthm fn-hrcur-cold-tasks-credit-natural-unfolds
   (natp (fn-hrcur-cold-tasks-credit tasks))
   :hints (("Goal" :induct (fn-hrcur-cold-tasks-credit tasks)
     :in-theory (enable fn-hrcur-cold-tasks-credit)))))
(local
 (defthm fn-hrcur-cold-structural-credit-natural-unfolds
   (natp (fn-hrcur-cold-structural-credit c))
   :hints (("Goal" :in-theory (enable fn-hrcur-cold-structural-credit)))))
(defthm fn-hrcur-cold-rank-is-well-founded-ordinal
   (o-p (fn-hrcur-cold-rank c))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :in-theory (e/d (fn-hrcur-cold-rank fn-hrcur-cold-phase-credit
                      fn-hrcur-cold-child-credit make-ord o-p)
                     (fn-hrcur-cold-structural-credit fn-hdsn-work fn-hrsc-work
                      fn-hrcur-span-work fn-hrcur-dos-work)))))

; Output type is checked by the actual runtime, even for malformed cursors.
(local
 (defthm fn-hrcur-cold-classifier-does-not-emit-unfolds
   (not (eq (mv-nth 0 (fn-hrcur-dos-tick child)) :emit))
   :hints (("Goal" :do-not-induct t
     :in-theory (enable fn-hrcur-dos-tick fn-hrcur-nil-tick)))))
(local
 (defthm fn-hrcur-cold-symbol-does-not-emit-unfolds
   (not (eq (mv-nth 0 (fn-hdsn-tick child)) :emit))
   :hints (("Goal" :do-not-induct t
     :in-theory (e/d (fn-hdsn-tick) (fn-hdsn-next-candidate))))))
(local
 (defthm fn-hrcur-cold-span-emits-one-octet
   (implies (eq (mv-nth 0 (fn-hrcur-span-tick child)) :emit)
            (fn-scc-octetp (mv-nth 1 (fn-hrcur-span-tick child))))
   :hints (("Goal" :do-not-induct t
     :in-theory (enable fn-hrcur-span-tick)))))
(defthm fn-hrcur-cold-tick-emits-one-octet
   (implies (eq (mv-nth 0 (fn-hrcur-cold-tick c)) :emit)
            (fn-scc-octetp (mv-nth 1 (fn-hrcur-cold-tick c))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hrcur-cold-classifier-does-not-emit-unfolds (child (fn-hrcur-field 2 c)))
           (:instance fn-hrcur-cold-symbol-does-not-emit-unfolds (child (fn-hrcur-field 2 c)))
           (:instance fn-hrcur-cold-span-emits-one-octet (child (fn-hrcur-field 2 c)))
           (:instance fn-hrsc-tick-emits-one-octet (c (fn-hrcur-field 2 c))))
     :in-theory (e/d (fn-hrcur-cold-tick)
                     (fn-hrcur-dos-tick fn-hdsn-tick fn-hrcur-span-tick fn-hrsc-tick
                      fn-hrsc-tick-emits-one-octet
                      fn-hrcur-cold-classifier-does-not-emit-unfolds
                      fn-hrcur-cold-symbol-does-not-emit-unfolds
                      fn-hrcur-cold-span-emits-one-octet)))))
(local
 (defthm fn-hrcur-cold-span-supply-emits-one-octet
   (implies (eq (mv-nth 0 (fn-hrcur-span-supply child position byte)) :emit)
            (fn-scc-octetp (mv-nth 1 (fn-hrcur-span-supply child position byte))))
   :hints (("Goal" :do-not-induct t
     :in-theory (enable fn-hrcur-span-supply)))))
(local
 (defthm fn-hrcur-cold-classifier-supply-does-not-emit-unfolds
   (not (eq (mv-nth 0 (fn-hrcur-dos-supply child position byte)) :emit))
   :hints (("Goal" :do-not-induct t
     :in-theory (enable fn-hrcur-dos-supply fn-hrcur-nil-supply)))))
(local
 (defthm fn-hrcur-cold-symbol-supply-does-not-emit-unfolds
   (not (eq (mv-nth 0 (fn-hdsn-supply position serial byte child)) :emit))
   :hints (("Goal" :do-not-induct t
     :in-theory (e/d (fn-hdsn-supply) (fn-hdsn-next-candidate))))))
(defthm fn-hrcur-cold-supply-emits-one-octet
   (implies (eq (mv-nth 0 (fn-hrcur-cold-supply c position byte)) :emit)
            (fn-scc-octetp (mv-nth 1 (fn-hrcur-cold-supply c position byte))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hrcur-cold-classifier-supply-does-not-emit-unfolds (child (fn-hrcur-field 2 c)))
           (:instance fn-hrcur-cold-symbol-supply-does-not-emit-unfolds (child (fn-hrcur-field 2 c))
                      (serial (fn-hrcur-field 5 (fn-hrcur-field 2 c))))
           (:instance fn-hrcur-cold-span-supply-emits-one-octet (child (fn-hrcur-field 2 c))))
     :in-theory (e/d (fn-hrcur-cold-supply)
                     (fn-hrcur-dos-supply fn-hdsn-supply fn-hrcur-span-supply
                      fn-hrcur-cold-classifier-supply-does-not-emit-unfolds
                      fn-hrcur-cold-symbol-supply-does-not-emit-unfolds
                      fn-hrcur-cold-span-supply-emits-one-octet)))))

(defthm fn-hrcur-cold-begin-establishes-progress-invariant
  (implies (and (fn-hrcur-widthp source 2) (eq (car source) :decoded)
                (fn-hrcur-cold-domainp (cadr source) pool)
                (fn-scc-octet-listp pool))
           (fn-hrcur-cold-progress-invariantp
             (fn-hrcur-cold-begin source capture lease) pool))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hrcur-cold-begin-establishes-invariant)
    :in-theory (e/d (fn-hrcur-cold-progress-invariantp fn-hrcur-cold-begin)
                    (fn-hrcur-cold-invariantp fn-hrcur-cold-domainp
                     fn-hrcur-cold-begin-establishes-invariant)))))
(local
 (defthm fn-hrcur-cold-domain-node-credit-positive
   (implies (fn-hrcur-dos-domainp node pool) (<= 2 (acl2-count node)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :expand ((fn-hrcur-dos-domainp node pool)
              (fn-hrcur-widthp node 2) (fn-hrcur-widthp node 3) (fn-hrcur-widthp node 5)
              (fn-hrcur-widthp (cdr node) 1) (fn-hrcur-widthp (cdr node) 2)
              (fn-hrcur-widthp (cdr node) 4)
              (acl2-count node) (acl2-count (cdr node)))
     :in-theory (e/d (fn-hrcur-field)
                     (fn-hrcur-widthp acl2-count fn-hrcur-dos-domainp fn-hdc-abstract fn-scc-atomp))))))
(local
 (defthm fn-hrcur-cold-span-tick-verdict-control-unfolds
   (implies (and (fn-hrcur-cold-invariantp c pool) (eq (fn-hrcur-field 0 c) :span))
     (let ((v (mv-nth 0 (fn-hrcur-cold-tick c))))
       (or (member-eq v '(:continue :emit))
           (eq (fn-hrcur-field 0 v) :need-byte))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :in-theory (e/d (fn-hrcur-cold-invariantp fn-hrcur-cold-tick fn-hrcur-cold-demand fn-hrcur-span-tick
                      fn-hrcur-span-invariantp fn-hrcur-span-shapep fn-scc-octet-listp)
                     (fn-hrcur-cold-tasksp fn-hrcur-cold-domainp fn-hrcur-cold-rest
                      fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-coherent
                      fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp))))))
(defthm fn-hrcur-cold-tick-current-codec-boundary
   (implies (fn-hrcur-cold-invariantp c pool) (fn-hrcur-cold-tick-lawp c pool))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use (fn-hrcur-cold-tick-preserves-current-codec-residual
           fn-hrcur-cold-tick-emits-one-octet
           fn-hrcur-cold-invariant-control-unfolds
           fn-hrcur-cold-work-tick-law fn-hrcur-cold-classify-tick-refines-residual
           fn-hrcur-cold-scalar-tick-refines-residual
           fn-hrcur-cold-span-tick-verdict-control-unfolds
           fn-hrcur-cold-symbol-tick-refines-residual
           fn-hrcur-cold-prefix-tick-refines-residual
           fn-hrcur-cold-opaque-tick-refines-residual
           fn-hrcur-cold-opaque-span-tick-refines-residual
           fn-hrcur-cold-done-law-unfolds)
     :cases ((eq (fn-hrcur-field 0 c) :work) (eq (fn-hrcur-field 0 c) :classify)
             (eq (fn-hrcur-field 0 c) :scalar) (eq (fn-hrcur-field 0 c) :span)
             (eq (fn-hrcur-field 0 c) :symbol) (eq (fn-hrcur-field 0 c) :opaque-prefix)
             (eq (fn-hrcur-field 0 c) :opaque) (eq (fn-hrcur-field 0 c) :opaque-span))
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(fn-hrcur-cold-tick-lawp member-eq member-equal eq not)))))

(in-theory (disable fn-hrcur-cold-state fn-hrcur-cold-begin fn-hrcur-cold-countp
                    fn-hrcur-cold-symbol-childp fn-hrcur-cold-demand fn-hrcur-cold-tick fn-hrcur-cold-supply
                    fn-hrcur-cold-task-rest fn-hrcur-cold-tasks-rest fn-hrcur-cold-rest
                    fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-domainp
                    fn-hrcur-cold-rejected-prefixp fn-hrcur-cold-taskp
                    fn-hrcur-cold-tasksp fn-hrcur-cold-name fn-hrcur-cold-invariantp
                    fn-hrcur-cold-tick-lawp
                    fn-hrcur-cold-task-credit fn-hrcur-cold-tasks-credit fn-hrcur-cold-phase-credit
                    fn-hrcur-cold-structural-credit fn-hrcur-cold-child-credit fn-hrcur-cold-rank
                    fn-hrcur-cold-progress-invariantp))
