;; Layer C4 unit: the folds' summary contract through the real engine
;; (books/folds-served.lisp) and the keystones' teeth.
(in-package "ACL2")
(include-book "../books/folds-served")

;; Teeth for NAME-SUMMARY-ADEQUATE-KIND. Positive: at each witness event (one
;; on a key the rows hold, one on a fresh key or refused) and with the rows
;; sealed in a run and held in the overlay, the premise holds and both
;; equations do. Negative (TRANSPORT §9 tooth 2, a mutated step): an engine
;; whose step adds one to the first value field disagrees with the fold at
;; BAD, sealed or not.
(defmacro fn2-ft-adequate (name kind sid key rows events qs bad)
 (let* ((thm (fn2-columns-sym name (concatenate 'string "-SUMMARY-ADEQUATE-" (symbol-name kind))))
        (holds (fn2-columns-sym thm "-HOLDS"))
        (layout (fn2-codec-constant (fn2-columns-sym name "-ENTRY") ""))
        (statep (fn2-columns-sym name "-FOLD-STATEP")) (eventp (fn2-columns-sym name "-FOLD-EVENTP"))
        (keysp (fn2-columns-sym name "-FOLD-KEYSP")) (obs (fn2-columns-sym name "-FOLD-OBSERVE-ALL"))
        (apply (fn2-columns-sym name "-FOLD-APPLY-SPEC")))
  `(progn
    (defun ,holds (rows es seal qs)
     (declare (xargs :verify-guards nil))
     (or (atom es)
         (and (,statep rows) (<= (len rows) 8) (,eventp (car es)) (eq (car (car es)) ,kind) (,keysp qs) (<= (len qs) 8)
              (equal (fn2-fold-image ,sid ,layout ',key rows nil seal qs) (,obs rows qs))
              (equal (fn2-fold-image ,sid ,layout ',key rows (list (car es)) seal qs) (,obs (,apply rows (car es)) qs))
              (,holds rows (cdr es) seal qs))))
    (defun ,(fn2-columns-sym thm "-POSITIVE") ()
     (declare (xargs :verify-guards nil))
     (and (,holds ',rows ',events nil ',qs) (,holds ',rows ',events t ',qs)))
    (defun ,(fn2-columns-sym thm "-NEGATIVE") ()
     (declare (xargs :verify-guards nil))
     (let ((want (,obs (,apply ',rows ',bad) ',qs)))
      (and (,eventp ',bad)
           (not (equal (car (fn2-fold-image-bug ,sid ,layout ',key ',rows (list ',bad) nil ',qs :plus1)) want))
           (not (equal (car (fn2-fold-image-bug ,sid ,layout ',key ',rows (list ',bad) t ',qs :plus1)) want)))))
    (fn2-assert-owed-teeth ,thm))))

;; Teeth for NAME-ASSIGN-ADEQUATE-KIND. Positive: at each witness event (on a
;; key the rows hold, on a fresh key), sealed and held in the overlay, the
;; premise holds and the engine's assignment is the declaration's. Negative:
;; an engine that adds one to the assigned arg disagrees, sealed or not.
(defmacro fn2-ft-assign (name kind sid key rows events)
 (let* ((thm (fn2-columns-sym name (concatenate 'string "-ASSIGN-ADEQUATE-" (symbol-name kind))))
        (holds (fn2-columns-sym thm "-HOLDS"))
        (layout (fn2-codec-constant (fn2-columns-sym name "-ENTRY") ""))
        (statep (fn2-columns-sym name "-FOLD-STATEP")) (eventp (fn2-columns-sym name "-FOLD-EVENTP"))
        (spec (fn2-columns-sym name "-FOLD-ASSIGN-SPEC")) (value (fn2-columns-sym name "-FOLD-VALUE"))
        (fkey (fn2-columns-sym name "-FOLD-KEY")))
  `(progn
    (defun ,holds (rows es seal)
     (declare (xargs :verify-guards nil))
     (or (atom es)
         (and (,statep rows) (<= (len rows) 8) (,eventp (car es)) (eq (car (car es)) ,kind)
              (equal (fn2-fold-assign-image ,sid ,layout ',key rows (car es) seal) (,spec (,value rows (,fkey (car es))) (car es)))
              (,holds rows (cdr es) seal))))
    (defun ,(fn2-columns-sym thm "-POSITIVE") ()
     (declare (xargs :verify-guards nil))
     (and (,holds ',rows ',events nil) (,holds ',rows ',events t)))
    (defun ,(fn2-columns-sym thm "-NEGATIVE") ()
     (declare (xargs :verify-guards nil))
     (let* ((e ',(car events)) (want (,spec (,value ',rows (,fkey e)) e)))
      (and (,eventp e)
           (not (equal (fn2-fold-assign-image-bug ,sid ,layout ',key ',rows e nil :plus1) want))
           (not (equal (fn2-fold-assign-image-bug ,sid ,layout ',key ',rows e t :plus1) want)))))
    (fn2-assert-owed-teeth ,thm))))

;; Teeth for NAME-SUMMARY-CUT. Positive, exhaustive over the tiny scenario:
;; every cut k of EVENTS, the summary sealed and held in the overlay.
;; Negative: at cut K a summary that drops its first row, and a summary step
;; mutated (TWICE: the event at the cut applied twice; else the engine's
;; step off by one), each disagree with the whole fold. WEAK (TRANSPORT §9
;; tooth 1): a relation weaker than the observation is not step-closed: WA and
;; WB agree on the projection WEAK (a function) of their observations at WQ
;; and one event WE separates them on it.
(defun fn2-ft-cuts (holds events qs k n)
 (declare (xargs :mode :program))
 (if (< n k) nil (cons `(,holds ',events ,k ',qs) (fn2-ft-cuts holds events qs (+ 1 k) n))))
(defmacro fn2-ft-cut (name sid key events qs k twice wa wb we wq weak)
 (let* ((thm (fn2-columns-sym name "-SUMMARY-CUT"))
        (holds (fn2-columns-sym thm "-HOLDS"))
        (layout (fn2-codec-constant (fn2-columns-sym name "-ENTRY") ""))
        (spec (fn2-columns-sym name "-FOLD-SPEC")) (eventsp (fn2-columns-sym name "-FOLD-EVENTSP"))
        (keysp (fn2-columns-sym name "-FOLD-KEYSP")) (obs (fn2-columns-sym name "-FOLD-OBSERVE-ALL"))
        (observe (fn2-columns-sym name "-FOLD-OBSERVE")) (apply (fn2-columns-sym name "-FOLD-APPLY-SPEC")))
  `(progn
    (defun ,holds (events k qs)
     (declare (xargs :verify-guards nil))
     (and (,eventsp events) (<= (len events) 8) (natp k) (<= k (len events)) (,keysp qs) (<= (len qs) 8)
          (equal (fn2-fold-image ,sid ,layout ',key (,spec (take k events)) (nthcdr k events) nil qs) (,obs (,spec events) qs))
          (equal (fn2-fold-image ,sid ,layout ',key (,spec (take k events)) (nthcdr k events) t qs) (,obs (,spec events) qs))))
    (defun ,(fn2-columns-sym thm "-POSITIVE") ()
     (declare (xargs :verify-guards nil))
     (and ,@(fn2-ft-cuts holds events qs 0 (len events))))
    (defun ,(fn2-columns-sym thm "-NEGATIVE") ()
     (declare (xargs :verify-guards nil))
     (let ((want (,obs (,spec ',events) ',qs)) (summary (,spec (take ,k ',events))))
      (and (consp summary)
           (not (equal (fn2-fold-image ,sid ,layout ',key (cdr summary) (nthcdr ,k ',events) t ',qs) want))
           ,(if twice
                `(not (equal (fn2-fold-image ,sid ,layout ',key summary (cons (nth ,k ',events) (nthcdr ,k ',events)) t ',qs) want))
              `(not (equal (car (fn2-fold-image-bug ,sid ,layout ',key summary (nthcdr ,k ',events) t ',qs :plus1)) want))))))
    (defun ,(fn2-columns-sym thm "-WEAK") ()
     (declare (xargs :verify-guards nil))
     (and (equal (,weak (,observe ',wa ',wq)) (,weak (,observe ',wb ',wq)))
          (not (equal (,weak (,observe (,apply ',wa ',we) ',wq)) (,weak (,observe (,apply ',wb ',we) ',wq))))))
    (fn2-assert-owed-teeth ,thm))))

;; Group counts: group 1 holds 2 articles, numbers 3..5.
(fn2-ft-adequate fn2-group-counts :accept 5 ((group (:id group))) (((1) 2 3 5)) ((:accept 1 7) (:accept 2 4)) ((1) (2) (3)) (:accept 1 7))
(fn2-ft-adequate fn2-group-counts :withdraw 5 ((group (:id group))) (((1) 2 3 5)) ((:withdraw 1 3) (:withdraw 2 1)) ((1) (2)) (:withdraw 1 3))
;; The accept's number is assigned high + 1: 6 in group 1, 1 in the empty group 2.
(fn2-ft-assign fn2-group-counts :accept 5 ((group (:id group))) (((1) 2 3 5)) ((:accept 1 0) (:accept 2 9)))
(assert-event (equal (fn2-fold-assign-image 5 *fn2-group-counts-entry* '((group (:id group))) '(((1) 2 3 5)) '(:accept 1 0) t)
                     '(:ok (:accept 1 6))))
;; Six events over two groups (one withdrawal refused: group 2 is empty
;; then); the weak relation observes LOW alone.
(fn2-ft-cut fn2-group-counts 5 ((group (:id group)))
 ((:accept 1 1) (:withdraw 2 1) (:accept 2 4) (:accept 1 2) (:withdraw 1 1) (:accept 1 6)) ((1) (2) (3)) 4 t
 (((1) 0 9 9)) (((1) 1 9 9)) (:accept 1 12) (1) second)

;; The consumer cursor: consumer 7, epoch 1 at position 10 under version 2.
(fn2-ft-adequate fn2-consumer-cursor :ack 6 ((consumer (:id consumer)) (epoch :u32)) (((7 1) 10 2))
 ((:ack 7 1 15) (:ack 8 1 4) (:ack 7 1 5)) ((7 1) (8 1) (7 2)) (:ack 7 1 15))
(fn2-ft-adequate fn2-consumer-cursor :rebase 6 ((consumer (:id consumer)) (epoch :u32)) (((7 1) 10 2))
 ((:rebase 7 1 3 0) (:rebase 7 2 1 5) (:rebase 7 1 1 9)) ((7 1) (7 2)) (:rebase 7 1 3 0))
;; Acks and rebases are idempotent, so the mutated summary step is the
;; engine's off-by-one; the weak relation observes the position alone.
(fn2-ft-cut fn2-consumer-cursor 6 ((consumer (:id consumer)) (epoch :u32))
 ((:ack 7 1 4) (:rebase 7 1 1 2) (:ack 7 1 3) (:ack 8 1 6) (:ack 7 1 2) (:rebase 8 1 4 1)) ((7 1) (8 1)) 2 nil
 (((7 1) 5 1)) (((7 1) 5 3)) (:rebase 7 1 2 0) (7 1) car)

;; Principal charges: principal 1 charged 10 in dimension 0.
(fn2-ft-adequate fn2-principal-charges :charge 7 ((principal (:id principal)) (dimension :u8)) (((1 0) 10))
 ((:charge 1 0 5) (:charge 2 3 1)) ((1 0) (2 3) (1 1)) (:charge 1 0 5))
(fn2-ft-adequate fn2-principal-charges :refund 7 ((principal (:id principal)) (dimension :u8)) (((1 0) 10))
 ((:refund 1 0 4) (:refund 1 0 11)) ((1 0) (2 3)) (:refund 1 0 4))
;; The weak relation observes only whether anything is charged.
(defun fn2-ft-charged-p (obs) (declare (xargs :verify-guards nil)) (< 0 (nfix (car obs))))
(fn2-ft-cut fn2-principal-charges 7 ((principal (:id principal)) (dimension :u8))
 ((:charge 1 0 5) (:charge 1 1 2) (:refund 1 0 3) (:refund 1 1 9) (:charge 2 0 1) (:charge 1 0 2)) ((1 0) (1 1) (2 0)) 4 t
 (((1 0) 5)) (((1 0) 3)) (:refund 1 0 5) (1 0) fn2-ft-charged-p)
