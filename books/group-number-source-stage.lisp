; Assigned membership insertion, shared by prepublish staging and loading.
; This pure cursor creates no publication authority or issued root identity.
(in-package "ACL2")
(include-book "group-number-source-update")
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-gns-update-counter-types
  (implies (fn-gns-update-cursorp c)
           (and (natp (fn-gns-at 8 c)) (natp (fn-gns-at 9 c)) (natp (fn-gns-at 10 c))))
  :hints (("Goal" :in-theory (enable fn-gns-update-cursorp)))))
(local
 (defthm fn-gns-update-step-counter-types
  (implies (fn-gns-update-cursorp c)
           (and (natp (fn-gns-at 8 (fn-gns-update-step c)))
                (natp (fn-gns-at 9 (fn-gns-update-step c)))
                (natp (fn-gns-at 10 (fn-gns-update-step c)))))
  :hints (("Goal" :use ((:instance fn-gns-update-step-cursorp))
           :in-theory (disable fn-gns-update-cursorp fn-gns-update-step
                               fn-gns-update-step-cursorp)))))

; Fixed10: phase, remaining assigned memberships, working group root,
; assigned catalog ordinal, current group, current number, active child,
; cumulative copied trie nodes, trie conses and descent frames.
(defun fn-gns-stage-begin (memberships ordinal group-root)
  (declare (xargs :guard t))
  (list (if (natp ordinal) :next :refused) memberships group-root
        (nfix ordinal) "" 1 nil 0 0 0))
(defun fn-gns-stage-cursorp (c)
  (declare (xargs :guard t))
  (and (true-listp c) (= (len c) 10)
       (member-eq (fn-gns-at 0 c) '(:next :group :number :publish :done :refused))
       (natp (fn-gns-at 3 c)) (stringp (fn-gns-at 4 c)) (posp (fn-gns-at 5 c))
       (natp (fn-gns-at 7 c)) (natp (fn-gns-at 8 c)) (natp (fn-gns-at 9 c))
       (implies (eq (fn-gns-at 0 c) :group) (fn-gns-group-cursorp (fn-gns-at 6 c)))
       (implies (member-eq (fn-gns-at 0 c) '(:number :publish))
                (fn-gns-update-cursorp (fn-gns-at 6 c)))))
(defun fn-gns-stage-step (c)
  (declare (xargs :guard (fn-gns-stage-cursorp c)
    :guard-hints (("Goal"
      :use ((:instance fn-gns-update-step-counter-types (c (fn-gns-at 6 c))))
      :in-theory (e/d (fn-gns-stage-cursorp)
        (fn-gns-update-step fn-gns-group-step fn-gns-update-begin
         fn-gns-group-begin fn-gns-update-step-counter-types
         fn-gns-update-done-is-denotation fn-gns-update-cursorp
         fn-gns-group-cursorp fn-gns-update-step-counter-types
      fn-gns-update-step-cursorp fn-gns-group-step-cursorp))))))
  (let ((phase (fn-gns-at 0 c)) (members (fn-gns-at 1 c)) (root (fn-gns-at 2 c))
        (ordinal (fn-gns-at 3 c)) (group (fn-gns-at 4 c)) (number (fn-gns-at 5 c))
        (child (fn-gns-at 6 c)) (copies (fn-gns-at 7 c))
        (cells (fn-gns-at 8 c)) (frames (fn-gns-at 9 c)))
    (cond
     ((eq phase :next)
      (cond ((not members) (list :done nil root ordinal group number nil copies cells frames))
            ((and (consp members) (consp (car members))
                  (stringp (car (car members))) (posp (cdr (car members))))
             (let ((g (car (car members))) (n (cdr (car members))))
               (list :group members root ordinal g n (fn-gns-group-begin g root) copies cells frames)))
            (t (list :refused members root ordinal group number nil copies cells frames))))
     ((eq phase :group)
      (let ((next (fn-gns-group-step child)))
        (if (eq (fn-gns-at 0 next) :done)
            (list :number members root ordinal group number
                  (fn-gns-update-begin :number number
                                       (fn-gnix-val (fn-gns-at 4 next)) (list :ordinal ordinal))
                  copies cells frames)
          (list :group members root ordinal group number next copies cells frames))))
     ((eq phase :number)
      (let ((next (fn-gns-update-step child)))
        (if (eq (fn-gns-at 0 next) :done)
            (list :publish members root ordinal group number
                  (fn-gns-update-begin :group group root (fn-gns-at 5 next))
                  (+ copies (fn-gns-at 8 next)) (+ cells (fn-gns-at 10 next))
                  (+ frames (fn-gns-at 9 next)))
          (list :number members root ordinal group number next copies cells frames))))
     ((eq phase :publish)
      (let ((next (fn-gns-update-step child)))
        (if (eq (fn-gns-at 0 next) :done)
            (list :next (fn-ag-cdr members) (fn-gns-at 5 next) ordinal "" 1 nil
                  (+ copies (fn-gns-at 8 next)) (+ cells (fn-gns-at 10 next))
                  (+ frames (fn-gns-at 9 next)))
          (list :publish members root ordinal group number next copies cells frames))))
     (t c))))
(defun fn-gns-stage-result (c)
  (declare (xargs :guard t))
  (if (eq (fn-gns-at 0 c) :done)
      (list :staged (fn-gns-at 2 c) (fn-gns-at 3 c)
            (fn-gns-at 7 c) (fn-gns-at 8 c) (fn-gns-at 9 c))
    '(:pending)))
(defthm fn-gns-stage-begin-cursorp
  (fn-gns-stage-cursorp (fn-gns-stage-begin memberships ordinal root)))
(defthm fn-gns-stage-step-cursorp
  (implies (fn-gns-stage-cursorp c)
           (fn-gns-stage-cursorp (fn-gns-stage-step c)))
  :hints (("Goal"
    :use ((:instance fn-gns-update-step-counter-types (c (fn-gns-at 6 c)))
          (:instance fn-gns-update-step-cursorp (c (fn-gns-at 6 c)))
          (:instance fn-gns-group-step-cursorp (c (fn-gns-at 6 c))))
    :in-theory (e/d (fn-gns-stage-step fn-gns-stage-cursorp)
     (fn-gns-update-step fn-gns-group-step fn-gns-update-begin
      fn-gns-group-begin fn-gns-update-done-is-denotation fn-gns-update-cursorp
         fn-gns-group-cursorp fn-gns-update-step-counter-types
      fn-gns-update-step-cursorp fn-gns-group-step-cursorp)))))

; Independent assigned-membership fold, logical specification only.
(defun fn-gns-memberships-root (members ordinal root)
  (declare (xargs :guard (natp ordinal)))
  (if (and (consp members) (consp (car members))
           (stringp (car (car members))) (posp (cdr (car members))))
      (let* ((g (car (car members))) (n (cdr (car members)))
             (nr (fn-gnix-set n (list :ordinal ordinal) (fn-gns-group-get g 0 0 root))))
        (fn-gns-memberships-root (cdr members) ordinal (fn-gns-group-set g 0 0 nr root)))
    root))
(defun fn-gns-stage-denotation (c)
  (declare (xargs :guard (fn-gns-stage-cursorp c)))
  (let ((phase (fn-gns-at 0 c)) (members (fn-gns-at 1 c)) (root (fn-gns-at 2 c))
        (ordinal (fn-gns-at 3 c)) (group (fn-gns-at 4 c)) (number (fn-gns-at 5 c))
        (child (fn-gns-at 6 c)))
    (cond
     ((eq phase :next) (fn-gns-memberships-root members ordinal root))
     ((eq phase :group)
      (fn-gns-memberships-root (fn-ag-cdr members) ordinal
        (fn-gns-group-set group 0 0
          (fn-gnix-set number (list :ordinal ordinal)
            (fn-gns-group-get (fn-gns-at 1 child) (fn-gns-at 2 child)
                              (fn-gns-at 3 child) (fn-gns-at 4 child))) root)))
     ((eq phase :number)
      (fn-gns-memberships-root (fn-ag-cdr members) ordinal
        (fn-gns-group-set group 0 0 (fn-gns-update-denotation child) root)))
     ((eq phase :publish)
      (fn-gns-memberships-root (fn-ag-cdr members) ordinal (fn-gns-update-denotation child)))
     (t root))))
(local
 (defthm fn-gns-group-done-lookup
  (implies (and (fn-gns-group-cursorp c) (eq (fn-gns-at 0 c) :done))
           (equal (fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c)
                                    (fn-gns-at 3 c) (fn-gns-at 4 c))
                  (fn-gnix-val (fn-gns-at 4 c))))
  :hints (("Goal" :use ((:instance fn-gns-group-done-result-refinement))
           :in-theory (e/d (fn-gns-group-result)
             (fn-gns-group-done-result-refinement fn-gns-group-get fn-gns-group-cursorp))))))
(local
 (defthm fn-gns-update-done-root
  (implies (and (fn-gns-update-cursorp c) (eq (fn-gns-at 0 c) :done))
           (equal (fn-gns-at 5 c) (fn-gns-update-denotation c)))
  :hints (("Goal" :in-theory (e/d (fn-gns-update-cursorp)
                                 (fn-gns-update-denotation))))))
(defthm fn-gns-stage-step-preserves-denotation
  (implies (fn-gns-stage-cursorp c)
           (equal (fn-gns-stage-denotation (fn-gns-stage-step c))
                  (fn-gns-stage-denotation c)))
  :hints (("Goal"
    :use ((:instance fn-gns-group-step-preserves-lookup (c (fn-gns-at 6 c)))
          (:instance fn-gns-update-step-preserves-denotation (c (fn-gns-at 6 c)))
          (:instance fn-gns-group-step-cursorp (c (fn-gns-at 6 c)))
          (:instance fn-gns-update-step-cursorp (c (fn-gns-at 6 c))))
    :in-theory (union-theories (theory 'minimal-theory)
      '(fn-gns-stage-step fn-gns-stage-denotation fn-gns-stage-cursorp
        fn-gns-at fn-ag-car fn-ag-cdr natp posp zp member-equal member-eq
        car-cons cdr-cons (:executable-counterpart binary-+)
        (:executable-counterpart unary--) (:executable-counterpart zp)
        fn-gns-group-begin
        fn-gns-update-begin-number-denotation fn-gns-update-begin-group-denotation
        fn-gns-group-done-lookup fn-gns-update-done-root))
    :expand ((fn-gns-memberships-root (fn-gns-at 1 c) (fn-gns-at 3 c) (fn-gns-at 2 c))))))
(defthm fn-gns-stage-begin-denotation
  (implies (natp ordinal)
           (equal (fn-gns-stage-denotation (fn-gns-stage-begin members ordinal root))
                  (fn-gns-memberships-root members ordinal root)))
  :hints (("Goal" :in-theory (disable fn-gns-memberships-root))))
(defthm fn-gns-stage-done-result-refinement
  (implies (and (fn-gns-stage-cursorp c) (eq (fn-gns-at 0 c) :done))
           (equal (fn-gns-stage-result c)
                  (list :staged (fn-gns-stage-denotation c) (fn-gns-at 3 c)
                        (fn-gns-at 7 c) (fn-gns-at 8 c) (fn-gns-at 9 c)))))
; Include the in-progress child's already copied nodes, not just completed
; membership subtotals. Cancelling does not subtract this constructor census.
(defun fn-gns-stage-copied-nodes (c)
  (declare (xargs :guard (fn-gns-stage-cursorp c)))
  (+ (fn-gns-at 7 c)
     (if (member-eq (fn-gns-at 0 c) '(:number :publish))
         (fn-gns-at 8 (fn-gns-at 6 c)) 0)))
(defthm fn-gns-stage-step-copy-bound
  (implies (fn-gns-stage-cursorp c)
           (and (<= (fn-gns-stage-copied-nodes c)
                    (fn-gns-stage-copied-nodes (fn-gns-stage-step c)))
                (<= (fn-gns-stage-copied-nodes (fn-gns-stage-step c))
                    (1+ (fn-gns-stage-copied-nodes c)))))
  :hints (("Goal" :use ((:instance fn-gns-update-step-copy-bound (c (fn-gns-at 6 c))))
           :in-theory (union-theories (theory 'minimal-theory)
             '(fn-gns-stage-copied-nodes fn-gns-stage-step fn-gns-stage-cursorp
               fn-gns-update-begin fn-gns-group-begin fn-gns-at fn-ag-car fn-ag-cdr
               natp posp zp member-equal member-eq car-cons cdr-cons
               normalize-addends associativity-of-+ commutativity-of-+
               commutativity-2-of-+ (:executable-counterpart binary-+)
               (:executable-counterpart unary--) (:executable-counterpart zp))))))
