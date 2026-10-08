; Quantum composition with an accumulator, fixed context and a mutable stobj.
(in-package "ACL2")
(include-book "../../books/def-loop-run")
(include-book "must-fail-checked")

(defun dlt-run-row (x acc bad)
 (declare (xargs :guard t))
 (if (equal x bad) (mv '(:refused :row) (cons :ignored acc))
   (mv nil (cons x acc))))

(def-loop/run dlt-run (xs acc bad)  :acc acc :quantum 2
 :row (dlt-run-row (car xs) acc bad))

(assert-event (equal (mv-list 3 (dlt-run-run 0 '(a b) '(z) :bad)) '(:more (a b) (z))))
(assert-event (equal (mv-list 3 (dlt-run-run 0 nil '(z) :bad)) '(:done nil (z))))
(assert-event (equal (mv-list 3 (dlt-run-run 1 '(a b) '(z) :bad)) '(:more (b) (a z))))
(assert-event (equal (mv-list 3 (dlt-run-run 2 '(a b) '(z) :bad)) '(:done nil (b a z))))
(assert-event (equal (mv-list 2 (dlt-run-drive 4 '(a b c) '(z) :bad)) '(nil (c b a z))))
(assert-event (equal (mv-list 2 (dlt-run-drive 0 '(a b) '(z) :bad)) '((:refused :fuel) (z))))
(assert-event (equal (mv-list 2 (dlt-run-drive 4 '(a :bad c) '(z) :bad)) '((:refused :row) (a z))))
(assert-event (equal (mv-list 3 (dlt-run-run 2 '(a . b) nil :bad)) '(:done nil (a))))

(defstobj dlt-run-store (dlt-run-count :type integer :initially 0))
(defun dlt-run-store-row (x acc delta dlt-run-store)
 (declare (xargs :stobjs dlt-run-store :guard t))
 (let ((dlt-run-store (update-dlt-run-count
                       (+ (nfix delta) (dlt-run-count dlt-run-store)) dlt-run-store)))
   (if (eq x :bad) (mv '(:refused :row) (cons :ignored acc) dlt-run-store)
     (mv :ok (cons x acc) dlt-run-store))))

(def-loop/run dlt-run-with-store (xs acc delta dlt-run-store)
  :acc acc :st dlt-run-store :quantum 2 :success :ok
 :row (dlt-run-store-row (car xs) acc delta dlt-run-store))

; Refusal preserves the prior accumulator but propagates the row's store
; effects. This makes the third result of the generic bridge observable.
(assert-event
 (let ((dlt-run-store (update-dlt-run-count 0 dlt-run-store)))
   (mv-let (v rest acc dlt-run-store)
     (dlt-run-with-store-run 1 '(a :bad c) nil 3 dlt-run-store)
     (let ((first (and (eq v :more) (equal rest '(:bad c))
                       (equal acc '(a)) (equal (dlt-run-count dlt-run-store) 3))))
       (mv-let (v acc dlt-run-store)
         (dlt-run-with-store-drive 3 rest acc 3 dlt-run-store)
         (mv (and first (equal v '(:refused :row)) (equal acc '(a))
                  (equal (dlt-run-count dlt-run-store) 6))
             dlt-run-store)))))
 :stobjs-out '(nil dlt-run-store))

(assert-event
 (let ((dlt-run-store (update-dlt-run-count 0 dlt-run-store)))
   (mv-let (v acc dlt-run-store)
     (dlt-run-with-store-drive 4 '(a b c) nil 3 dlt-run-store)
     (mv (and (equal v :ok) (equal acc '(c b a))
              (equal (dlt-run-count dlt-run-store) 9)) dlt-run-store)))
 :stobjs-out '(nil dlt-run-store))

; @mutation-witness: ignoring the store's final effect is false on a row.
(must-fail-checked
 (defthm dlt-run-drops-effect
   (equal (mv-nth 2 (dlt-run-with-store-drive 2 '(a) nil 3 '(0))) '(0)))
 :step-limit 10000)

; A zero quantum cannot progress and cannot instantiate the library contract.
(must-fail-checked
 (def-loop/run dlt-run-zero (xs acc)  :acc acc :quantum 0
   :row (dlt-run-row (car xs) acc :bad))
 :unchecked "encapsulate must fail the positive-quantum instantiation obligation"
 :step-limit 10000)

(defun dlt-run-reserved-row (x acc)
 (declare (xargs :guard t) (ignore x)) (mv :more acc))
(must-fail-checked
 (def-loop/run dlt-run-reserved (xs acc)  :acc acc :quantum 1
   :row (dlt-run-reserved-row (car xs) acc))
 :unchecked "encapsulate must fail the reserved-status instantiation obligation"
 :step-limit 10000)
(must-fail-checked
 (def-loop/run dlt-run-no-acc (xs)  :quantum 2 :row (dlt-run-row (car xs) nil :bad))
 :unchecked "refused at expansion: accumulator must be a formal")
(must-fail-checked
 (def-loop/run dlt-run-colliding (xs) :acc xs :quantum 2
   :row (dlt-run-row (car xs) xs :bad))
 :unchecked "refused at expansion: row list and accumulator must be distinct")

; A carried input/accumulator invariant also survives quantum boundaries.
(defun dlt-run-count-row (x n)
 (declare (xargs :guard (natp n)) (ignore x))
 (mv nil (+ 1 n)))
(defthm dlt-run-count-row-preserves-natp
 (implies (natp n) (natp (mv-nth 1 (dlt-run-count-row x n)))))
(def-loop/run dlt-run-counting (xs n)  :acc n :quantum 2
 :guard (and (true-listp xs) (natp n))
 :row (dlt-run-count-row (car xs) n))
(assert-event (equal (mv-list 2 (dlt-run-counting-drive 4 '(a b c) 7)) '(nil 10)))

; Refuse improper input at a quantum boundary without scanning ahead.
(def-loop/run dlt-run-proper (xs acc) :acc acc :quantum 1
 :row (dlt-run-row (car xs) acc :bad)
 :end-status (if (null xs) nil '(:refused :tail)))
(assert-event (equal (mv-list 2 (dlt-run-proper-drive 3 '(a b . c) nil))
                     '((:refused :tail) (b a))))
