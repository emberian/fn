; Bounded numbering against one immutable captured group-high root.
; Publication authority and catalog lineage belong to the registered publisher.
(in-package "ACL2")
(include-book "group-number-source")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-gns-group-valuep (v)
  (declare (xargs :guard t))
  (and (consp v) (eq (car v) :group-number)
       (consp (cdr v)) (natp (cadr v))
       (consp (cddr v)) (not (cdddr v))))
(defun fn-gns-group-value (high number-root)
  (declare (xargs :guard (natp high)))
  (list :group-number high number-root))
(defun fn-gns-group-value-high (v)
  (declare (xargs :guard t))
  (if (fn-gns-group-valuep v) (cadr v) 0))
(defun fn-gns-group-value-root (v)
  (declare (xargs :guard t))
  (if (fn-gns-group-valuep v) (caddr v) nil))
(defun fn-gns-group-selected-result (c)
  (declare (xargs :guard t))
  (if (eq (fn-gns-at 0 c) :done)
      (list :number-root (fn-gns-group-value-root (fn-gnix-val (fn-gns-at 4 c))))
    '(:pending)))
(defun fn-gns-group-high-result (c)
  (declare (xargs :guard t))
  (if (eq (fn-gns-at 0 c) :done)
      (list :high (fn-gns-group-value-high (fn-gnix-val (fn-gns-at 4 c))))
    '(:pending)))
(defthm fn-gns-group-value-high-type
  (natp (fn-gns-group-value-high v))
  :rule-classes (:rewrite :type-prescription))
(defthm fn-gns-group-value-projections
  (implies (natp high)
    (and (equal (fn-gns-group-value-high (fn-gns-group-value high root)) high)
         (equal (fn-gns-group-value-root (fn-gns-group-value high root)) root))))
(defthm fn-gns-group-selected-result-refinement
  (implies (and (fn-gns-group-cursorp c) (eq (fn-gns-at 0 c) :done))
    (equal (fn-gns-group-selected-result c)
      (list :number-root
        (fn-gns-group-value-root
          (fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c)
                            (fn-gns-at 3 c) (fn-gns-at 4 c))))))
  :hints (("Goal" :in-theory (enable fn-gns-group-cursorp fn-gns-group-selected-result)
           :expand ((fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c)
                                      (fn-gns-at 3 c) (fn-gns-at 4 c))))))
(defthm fn-gns-group-high-result-refinement
  (implies (and (fn-gns-group-cursorp c) (eq (fn-gns-at 0 c) :done))
    (equal (fn-gns-group-high-result c)
      (list :high
        (fn-gns-group-value-high
          (fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c)
                            (fn-gns-at 3 c) (fn-gns-at 4 c))))))
  :hints (("Goal" :in-theory (enable fn-gns-group-cursorp fn-gns-group-high-result)
           :expand ((fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c)
                                      (fn-gns-at 3 c) (fn-gns-at 4 c))))))

; Specification only: fn-cat-assign uses the SAME initial catalog for each
; membership, including repeated group names in one pending row.
(defun fn-gns-assigned-memberships (groups root)
  (declare (xargs :guard t))
  (if (consp groups)
      (cons (cons (car groups)
                  (1+ (fn-gns-group-value-high
                        (if (stringp (car groups))
                            (fn-gns-group-get (car groups) 0 0 root) nil))))
            (fn-gns-assigned-memberships (cdr groups) root))
    nil))

; Fixed12: phase, remaining original groups, immutable initial root,
; reversed assigned memberships, reversal input, forward result, child,
; original heldref, exact PC token, expected catalog count, allocated conses
; and expected registered group-root ID (retained, never issued here).
; One bit per walk, one membership pair per terminal, one reverse cons per
; reversal action. No row/list scan occurs at begin or at a scheduling step.
(defun fn-gns-assign-begin (groups root heldref token expected-count root-id)
  (declare (xargs :guard t))
  (list (if (natp expected-count) :next :refused) groups root nil nil nil nil
        heldref token (nfix expected-count) 0 root-id))
(defun fn-gns-assign-cursorp (c)
  (declare (xargs :guard t))
  (and (true-listp c) (= (len c) 12)
       (member-eq (fn-gns-at 0 c) '(:next :group :reverse :done :refused))
       (natp (fn-gns-at 9 c)) (natp (fn-gns-at 10 c))
       (implies (eq (fn-gns-at 0 c) :group)
         (and (consp (fn-gns-at 1 c)) (stringp (car (fn-gns-at 1 c)))
              (fn-gns-group-cursorp (fn-gns-at 6 c))))))
(defun fn-gns-assign-step (c)
  (declare (xargs :guard (fn-gns-assign-cursorp c)))
  (let ((phase (fn-gns-at 0 c)) (groups (fn-gns-at 1 c))
        (root (fn-gns-at 2 c)) (rev (fn-gns-at 3 c))
        (todo (fn-gns-at 4 c)) (out (fn-gns-at 5 c)) (child (fn-gns-at 6 c))
        (held (fn-gns-at 7 c)) (token (fn-gns-at 8 c))
        (count (fn-gns-at 9 c)) (cells (fn-gns-at 10 c)) (root-id (fn-gns-at 11 c)))
    (cond
      ((eq phase :next)
       (cond ((not (consp groups))
              (list :reverse nil root rev rev nil nil held token count cells root-id))
             ((stringp (car groups))
              (list :group groups root rev todo out
                    (fn-gns-group-begin (car groups) root) held token count cells root-id))
             (t (list :refused groups root rev todo out nil held token count cells root-id))))
      ((eq phase :group)
       (let ((next (fn-gns-group-step child)))
         (if (eq (fn-gns-at 0 next) :done)
             (list :next (cdr groups) root
               (cons (cons (car groups)
                      (1+ (fn-gns-group-value-high (fn-gnix-val (fn-gns-at 4 next))))) rev)
               todo out nil held token count (+ 2 cells) root-id)
           (list :group groups root rev todo out next held token count cells root-id))))
      ((eq phase :reverse)
       (if (consp todo)
           (list :reverse groups root rev (cdr todo) (cons (car todo) out)
                 nil held token count (1+ cells) root-id)
         (list :done groups root rev nil out nil held token count cells root-id)))
      (t c))))
(defun fn-gns-assign-result (c)
  (declare (xargs :guard t))
  (if (eq (fn-gns-at 0 c) :done)
      (list :assigned-memberships (fn-gns-at 7 c) (fn-gns-at 8 c) (fn-gns-at 9 c)
            (fn-gns-at 11 c) (fn-gns-at 5 c) (fn-gns-at 10 c))
    '(:pending)))
(defthm fn-gns-assign-begin-cursorp
  (fn-gns-assign-cursorp (fn-gns-assign-begin groups root held token count root-id)))
(defthm fn-gns-assign-step-cursorp
  (implies (fn-gns-assign-cursorp c)
    (fn-gns-assign-cursorp (fn-gns-assign-step c)))
  :hints (("Goal" :use ((:instance fn-gns-group-step-cursorp (c (fn-gns-at 6 c))))
           :in-theory (disable fn-gns-group-step fn-gns-group-begin
                               fn-gns-group-cursorp fn-gns-group-step-cursorp))))
(defthm fn-gns-assign-step-retains-pending-binding
  (implies (fn-gns-assign-cursorp c)
    (and (equal (fn-gns-at 7 (fn-gns-assign-step c)) (fn-gns-at 7 c))
         (equal (fn-gns-at 8 (fn-gns-assign-step c)) (fn-gns-at 8 c))
         (equal (fn-gns-at 9 (fn-gns-assign-step c)) (fn-gns-at 9 c))
         (equal (fn-gns-at 2 (fn-gns-assign-step c)) (fn-gns-at 2 c))
         (equal (fn-gns-at 11 (fn-gns-assign-step c)) (fn-gns-at 11 c))))
  :hints (("Goal" :in-theory (disable fn-gns-group-step fn-gns-group-value-high))))
(defthm fn-gns-assign-step-cons-bound
  (implies (fn-gns-assign-cursorp c)
    (and (<= (fn-gns-at 10 c) (fn-gns-at 10 (fn-gns-assign-step c)))
         (<= (fn-gns-at 10 (fn-gns-assign-step c)) (+ 2 (fn-gns-at 10 c)))))
  :hints (("Goal" :in-theory (disable fn-gns-group-step fn-gns-group-value-high))))

; This logical denotation is proof-only: the actual scheduler never reverses
; or scans a membership list in one action.
(defun fn-gns-assign-denotation (c)
  (declare (xargs :guard (fn-gns-assign-cursorp c)))
  (let ((phase (fn-gns-at 0 c)) (groups (fn-gns-at 1 c))
        (root (fn-gns-at 2 c)) (rev (fn-gns-at 3 c))
        (todo (fn-gns-at 4 c)) (out (fn-gns-at 5 c)) (child (fn-gns-at 6 c)))
    (cond ((eq phase :next)
           (fn-ag-rev-onto rev (fn-gns-assigned-memberships groups root)))
          ((eq phase :group)
           (fn-ag-rev-onto rev
             (cons (cons (car groups)
               (1+ (fn-gns-group-value-high
                     (fn-gns-group-get (fn-gns-at 1 child) (fn-gns-at 2 child)
                                      (fn-gns-at 3 child) (fn-gns-at 4 child)))))
               (fn-gns-assigned-memberships (cdr groups) root))))
          ((eq phase :reverse) (fn-ag-rev-onto todo out))
          (t out))))
(defthm fn-gns-assign-begin-denotation
  (implies (natp count)
    (equal (fn-gns-assign-denotation (fn-gns-assign-begin groups root held token count root-id))
           (fn-gns-assigned-memberships groups root))))
(local
 (defthm fn-gns-assign-terminal-lookup
  (implies (and (fn-gns-group-cursorp c) (eq (fn-gns-at 0 c) :done))
    (equal (fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c)
                             (fn-gns-at 3 c) (fn-gns-at 4 c))
           (fn-gnix-val (fn-gns-at 4 c))))
  :hints (("Goal" :in-theory (enable fn-gns-group-cursorp)
           :expand ((fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c)
                                      (fn-gns-at 3 c) (fn-gns-at 4 c)))))))
(defthm fn-gns-assign-step-preserves-denotation
  (implies (and (fn-gns-assign-cursorp c)
                (implies (eq (fn-gns-at 0 c) :next)
                  (or (not (consp (fn-gns-at 1 c)))
                      (stringp (car (fn-gns-at 1 c))))))
    (equal (fn-gns-assign-denotation (fn-gns-assign-step c))
           (fn-gns-assign-denotation c)))
  :hints (("Goal"
    :use ((:instance fn-gns-group-step-preserves-lookup (c (fn-gns-at 6 c)))
          (:instance fn-gns-assign-terminal-lookup
                     (c (fn-gns-group-step (fn-gns-at 6 c))))
          (:instance fn-gns-group-step-cursorp (c (fn-gns-at 6 c))))
    :in-theory (e/d (fn-gns-assign-denotation fn-gns-assign-step
                     fn-gns-assign-cursorp fn-ag-rev-onto)
                    (fn-gns-group-step fn-gns-group-value-high fn-gns-group-get
                     fn-gns-group-cursorp fn-gns-group-step-cursorp
                     fn-gns-group-step-preserves-lookup fn-gns-assign-terminal-lookup)))))
(defthm fn-gns-assign-done-result-refinement
  (implies (eq (fn-gns-at 0 c) :done)
    (equal (fn-gns-at 5 (fn-gns-assign-result c))
           (fn-gns-assign-denotation c)))
  :hints (("Goal" :in-theory (enable fn-gns-assign-result fn-gns-assign-denotation))))
