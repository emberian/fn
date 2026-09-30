; Additive report-field emitter. Runtime profile/tariffs are external obligations.
; Descriptors borrow their strings. No width limit or whole-string conversion.
(in-package "ACL2")
(include-book "acceptance-alloc")
(include-book "defrecord")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-orf-fieldp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)
       (or (and (eq (car x) :text) (stringp (cadr x)))
           (and (eq (car x) :nat) (natp (cadr x))))))

(defun fn-orf-fieldsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-orf-fieldp (car xs)) (fn-orf-fieldsp (cdr xs)))
    (equal xs nil)))

(defun fn-orf-digitsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (integerp (car xs)) (<= 48 (car xs)) (<= (car xs) 57)
           (fn-orf-digitsp (cdr xs)))
    (equal xs nil)))

; Phase-dependent relation is separate from the constant-size record shape.
(fn-defrecord fn-orf-cursor
  :constructor (fn-orf-cursor phase fields text index number digits)
  :fields ((fn-orf-phase t) (fn-orf-fields t) (fn-orf-text t)
           (fn-orf-index t) (fn-orf-number t) (fn-orf-digits t)))

(defun fn-orf-terminalp (c)
  (declare (xargs :guard t))
  (eq (fn-orf-phase c) :idle))

(defun fn-orf-next-field (fields)
  (declare (xargs :guard t))
  (fn-orf-cursor (if (consp fields) :field :idle) fields "" 0 0 nil))

(defun fn-orf-start (fields)
  (declare (xargs :guard (fn-orf-fieldsp fields)))
  (fn-orf-next-field fields))

; This guard checks only the fixed cursor and the current descriptor/digit.
; The complete descriptor and digit invariants are carried, not rescanned.
(defun fn-orf-ready-p (c)
  (declare (xargs :guard t))
  (and (fn-orf-cursorp c)
       (stringp (fn-orf-text c)) (natp (fn-orf-index c))
       (<= (fn-orf-index c) (length (fn-orf-text c)))
       (natp (fn-orf-number c))
       (case (fn-orf-phase c)
         (:idle t)
         (:field (and (consp (fn-orf-fields c))
                      (fn-orf-fieldp (car (fn-orf-fields c)))))
         (:text t)
         (:prepare t)
         (:emit (or (not (consp (fn-orf-digits c)))
                    (and (integerp (car (fn-orf-digits c)))
                         (<= 48 (car (fn-orf-digits c)))
                         (<= (car (fn-orf-digits c)) 57))))
         (otherwise nil))))

(defun fn-orf-step (c)
  (declare (xargs :guard (fn-orf-ready-p c)))
  (let ((phase (fn-orf-phase c)) (fields (fn-orf-fields c))
        (text (fn-orf-text c)) (index (fn-orf-index c))
        (number (fn-orf-number c)) (digits (fn-orf-digits c)))
    (case phase
      (:idle (mv c nil t))
      (:field
       (let ((field (car fields)))
         (mv (if (eq (car field) :text)
                 (fn-orf-cursor :text fields (cadr field) 0 0 nil)
               (fn-orf-cursor :prepare fields "" 0 (cadr field) nil))
             nil nil)))
      (:text
       (if (< index (length text))
           (mv (fn-orf-cursor :text fields text (+ 1 index) 0 nil)
               (list (char-code (char text index))) nil)
         (let ((next (fn-orf-next-field (fn-ag-cdr fields))))
           (mv next nil (fn-orf-terminalp next)))))
      (:prepare
       (if (< number 10)
           (mv (fn-orf-cursor :emit fields "" 0 0
                             (cons (+ 48 number) digits)) nil nil)
         (mv (fn-orf-cursor :prepare fields "" 0 (floor number 10)
                           (cons (+ 48 (mod number 10)) digits)) nil nil)))
      (:emit
       (if (consp digits)
           (mv (fn-orf-cursor :emit fields "" 0 0 (cdr digits))
               (list (car digits)) nil)
         (let ((next (fn-orf-next-field (fn-ag-cdr fields))))
           (mv next nil (fn-orf-terminalp next)))))
      (otherwise (mv c nil nil)))))

; Logical reference only: these traversals are never performed by STEP.
(defun fn-orf-decimal (n acc)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (< (nfix n) 10)
      (cons (+ 48 (nfix n)) acc)
    (fn-orf-decimal (floor n 10) (cons (+ 48 (mod n 10)) acc))))

(defun fn-orf-text-tail (text index)
  (declare (xargs :guard (and (stringp text) (natp index)
                            (<= index (length text)))
                  :measure (nfix (- (length text) (nfix index)))))
  (if (and (stringp text) (natp index) (< index (length text)))
      (cons (char-code (char text index))
            (fn-orf-text-tail text (+ 1 index)))
    nil))

(defthm fn-orf-decimal-true-listp
  (implies (true-listp acc) (true-listp (fn-orf-decimal n acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-orf-decimal n acc))))

(defthm fn-orf-text-tail-true-listp
  (true-listp (fn-orf-text-tail text index))
  :rule-classes :type-prescription)

(defun fn-orf-reference (fields)
  (declare (xargs :guard (fn-orf-fieldsp fields)))
  (if (consp fields)
      (append (if (eq (caar fields) :text)
                  (fn-orf-text-tail (cadar fields) 0)
                (fn-orf-decimal (cadar fields) nil))
              (fn-orf-reference (cdr fields)))
    nil))

(defun fn-orf-invariant (c)
  (declare (xargs :guard t))
  (and (fn-orf-ready-p c) (fn-orf-fieldsp (fn-orf-fields c))
       (fn-orf-digitsp (fn-orf-digits c))
       (if (fn-orf-terminalp c) (equal (fn-orf-fields c) nil)
         (consp (fn-orf-fields c)))))

(defthm fn-orf-fieldsp-tail
  (implies (fn-orf-fieldsp fields)
           (fn-orf-fieldsp (fn-ag-cdr fields))))

(defthm fn-orf-digitsp-tail
  (implies (fn-orf-digitsp digits)
           (fn-orf-digitsp (fn-ag-cdr digits))))

(defthm fn-orf-digitsp-true-listp
  (implies (fn-orf-digitsp xs) (true-listp xs))
  :rule-classes :forward-chaining)

(defun fn-orf-denotation (c)
  (declare (xargs :guard (fn-orf-invariant c)))
  (case (fn-orf-phase c)
    (:idle nil)
    (:field (fn-orf-reference (fn-orf-fields c)))
    (:text (append (fn-orf-text-tail (fn-orf-text c) (fn-orf-index c))
                   (fn-orf-reference (fn-ag-cdr (fn-orf-fields c)))))
    (:prepare (append (fn-orf-decimal (fn-orf-number c) (fn-orf-digits c))
                      (fn-orf-reference (fn-ag-cdr (fn-orf-fields c)))))
    (:emit (append (fn-orf-digits c)
                   (fn-orf-reference (fn-ag-cdr (fn-orf-fields c)))))
    (otherwise nil)))

(defthm fn-orf-start-invariant
  (implies (fn-orf-fieldsp fields)
           (fn-orf-invariant (fn-orf-start fields))))

(defthm fn-orf-step-preserves-invariant
  (implies (fn-orf-invariant c)
           (fn-orf-invariant (mv-nth 0 (fn-orf-step c)))))

(defthm fn-orf-start-denotation
  (implies (fn-orf-fieldsp fields)
           (equal (fn-orf-denotation (fn-orf-start fields))
                  (fn-orf-reference fields))))

(defthm fn-orf-step-conserves-denotation
  (implies (fn-orf-invariant c)
           (equal (append (mv-nth 1 (fn-orf-step c))
                          (fn-orf-denotation (mv-nth 0 (fn-orf-step c))))
                  (fn-orf-denotation c))))

(defthm fn-orf-step-output-quantum
  (implies (fn-orf-invariant c)
           (and (true-listp (mv-nth 1 (fn-orf-step c)))
                (<= (len (mv-nth 1 (fn-orf-step c))) 1))))

(defthm fn-orf-step-output-octet
  (implies (and (fn-orf-invariant c)
                (consp (mv-nth 1 (fn-orf-step c))))
           (and (integerp (car (mv-nth 1 (fn-orf-step c))))
                (<= 0 (car (mv-nth 1 (fn-orf-step c))))
                (< (car (mv-nth 1 (fn-orf-step c))) 256))))

(defthm fn-orf-step-done-is-terminal
  (implies (fn-orf-invariant c)
           (equal (mv-nth 2 (fn-orf-step c))
                  (fn-orf-terminalp (mv-nth 0 (fn-orf-step c))))))

(defthm fn-orf-terminal-stable
  (implies (and (fn-orf-invariant c) (fn-orf-terminalp c))
           (equal (fn-orf-step c) (mv c nil t))))

; Ghost relation to the borrowed input and the already emitted prefix.
; It carries the complete string/digit relation without executable rescans.
(defun fn-orf-conservation-statep (fields prefix c)
  (declare (xargs :guard (and (fn-orf-fieldsp fields) (true-listp prefix)
                            (fn-orf-invariant c))))
  (and (fn-orf-fieldsp fields) (true-listp prefix) (fn-orf-invariant c)
       (equal (append prefix (fn-orf-denotation c)) (fn-orf-reference fields))))

(defthm fn-orf-start-conservation-state
  (implies (fn-orf-fieldsp fields)
           (fn-orf-conservation-statep fields nil (fn-orf-start fields)))
  :hints (("Goal" :in-theory (disable fn-orf-start fn-orf-denotation
                                     fn-orf-reference fn-orf-invariant))))

(local (defthm fn-orf-append-associative
  (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-orf-step-preserves-conservation-state
  (implies (fn-orf-conservation-statep fields prefix c)
           (fn-orf-conservation-statep
            fields (append prefix (mv-nth 1 (fn-orf-step c)))
            (mv-nth 0 (fn-orf-step c))))
  :hints (("Goal" :in-theory (disable fn-orf-step fn-orf-denotation
                                     fn-orf-reference fn-orf-invariant mv-nth))))

(defthm fn-orf-terminal-prefix-is-complete-reference
  (implies (and (fn-orf-conservation-statep fields prefix c)
                (fn-orf-terminalp c))
           (equal prefix (fn-orf-reference fields)))
  :rule-classes nil)

; A logical termination rank, not a served-path cost computation or tariff.
(defun fn-orf-prepare-count (n)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (< (nfix n) 10) 1
    (+ 1 (fn-orf-prepare-count (floor n 10)))))

(defun fn-orf-fields-rank (fields)
  (declare (xargs :guard (fn-orf-fieldsp fields)))
  (if (consp fields)
      (+ 2 (if (eq (caar fields) :text)
               (length (cadar fields))
             (* 2 (fn-orf-prepare-count (cadar fields))))
         (fn-orf-fields-rank (cdr fields)))
    0))

(defun fn-orf-rank (c)
  (declare (xargs :guard (fn-orf-invariant c)))
  (case (fn-orf-phase c)
    (:idle 0)
    (:field (fn-orf-fields-rank (fn-orf-fields c)))
    (:text (+ 1 (- (length (fn-orf-text c)) (fn-orf-index c))
              (fn-orf-fields-rank (fn-ag-cdr (fn-orf-fields c)))))
    (:prepare (+ 1 (* 2 (fn-orf-prepare-count (fn-orf-number c)))
                 (len (fn-orf-digits c))
                 (fn-orf-fields-rank (fn-ag-cdr (fn-orf-fields c)))))
    (:emit (+ 1 (len (fn-orf-digits c))
              (fn-orf-fields-rank (fn-ag-cdr (fn-orf-fields c)))))
    (otherwise 0)))

(defthm fn-orf-rank-natural
  (implies (fn-orf-invariant c) (natp (fn-orf-rank c)))
  :rule-classes :type-prescription)

(defthm fn-orf-step-decreases-rank
  (implies (and (fn-orf-invariant c) (not (fn-orf-terminalp c)))
           (< (fn-orf-rank (mv-nth 0 (fn-orf-step c))) (fn-orf-rank c))))

; Proof-only complete interpreter. Host uses STEP, never RUN or RANK.
(defun fn-orf-run (c)
  (declare (xargs :guard (fn-orf-invariant c)
                  :measure (if (fn-orf-invariant c) (nfix (fn-orf-rank c)) 0)
                  :hints (("Goal" :use (fn-orf-step-decreases-rank fn-orf-step-preserves-invariant)
                           :in-theory (disable fn-orf-rank fn-orf-step
                                               fn-orf-invariant fn-orf-terminalp mv-nth)))))
  (if (or (not (fn-orf-invariant c)) (fn-orf-terminalp c)) nil
    (mv-let (next output done) (fn-orf-step c)
      (declare (ignore done))
      (append output (fn-orf-run next)))))

(defthm fn-orf-terminal-denotation
  (implies (fn-orf-terminalp c) (equal (fn-orf-denotation c) nil)))

(defthm fn-orf-run-is-complete-denotation
  (implies (fn-orf-invariant c)
           (equal (fn-orf-run c) (fn-orf-denotation c)))
  :hints (("Goal" :induct (fn-orf-run c)
           :in-theory (disable fn-orf-step fn-orf-invariant fn-orf-denotation mv-nth fn-orf-terminalp))))

(defthm fn-orf-start-run-is-complete-reference
  (implies (fn-orf-fieldsp fields)
           (equal (fn-orf-run (fn-orf-start fields))
                  (fn-orf-reference fields)))
  :hints (("Goal" :in-theory (disable fn-orf-run fn-orf-start
                                     fn-orf-reference fn-orf-denotation))))
