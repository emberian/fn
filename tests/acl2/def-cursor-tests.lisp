(in-package "ACL2")
(include-book "../../books/def-cursor")
(include-book "must-fail-checked")

; A candidate contributes five octets, exceeding the two-octet output
; quantum. Saved scan progress is distinct from its three pending octets.
(defun fn-cur-test-one (progress)
  (declare (xargs :guard t))
  (mv '(65 66 67 68 69) (if (consp progress) (cdr progress) nil)))
(defthm fn-cur-test-visits
  (<= (- (len progress) (len (mv-nth 1 (fn-cur-test-one progress)))) 1))
(def-cursor fn-cur-test ()
  :call (fn-cur-test-one progress)
  :visit-proof fn-cur-test-visits :visit-metric (len progress))

(verify-guards fn-cur-test-step)

(assert-event
 (let* ((cur (fn-cur-make '(:view root-a :config cfg-a) '(a b) nil nil))
        (step (mv-list 4 (fn-cur-test-step cur 1 2)))
        (next (nth 1 step))
        (drain (mv-list 4 (fn-cur-test-step next 0 2))))
   (and (equal (nth 0 step) '(65 66))
        (equal (fn-cur-progress next) '(b))
        (equal (fn-cur-pending next) '(67 68 69))
        (equal (fn-cur-context next) (fn-cur-context cur))
        (equal (nth 2 step) 1)
        (equal (nth 0 drain) '(67 68))
        (equal (fn-cur-progress (nth 1 drain)) '(b))
        (equal (fn-cur-pending (nth 1 drain)) '(69))
        (equal (nth 2 drain) 0))))

; Zero budgets preserve obligations. A pending physical operation carries
; its nested resource token unchanged: neither drain nor timeout settles it.
(assert-event
 (let* ((token '(:resource (7 . 13) 5 19))
        (dependency (list :operation '(2 . 11) token))
        (cur (fn-cur-make '(:view root-a) '(a b) '(65 66) dependency)))
   (and (equal (nth 1 (mv-list 4 (fn-cur-test-step cur 1 2))) cur)
        (equal (nth 3 (mv-list 4 (fn-cur-test-step cur 1 2))) :suspended)
        (equal (nth 0 (mv-list 4 (fn-cur-test-step cur 1 2))) nil)
        (equal (nth 2 (mv-list 4 (fn-cur-test-step cur 1 2))) 0))))
(assert-event
 (let ((cur (fn-cur-make '(:view root-a) '(a b) nil nil)))
   (and (equal (nth 1 (mv-list 4 (fn-cur-test-step cur 0 2))) cur)
        (equal (nth 1 (mv-list 4 (fn-cur-test-step cur 1 0))) cur))))

; Missing named candidate obligation is refused before emitting definitions.
(must-fail-checked
 (def-cursor fn-cur-absent ()
   :call (fn-cur-test-one progress)
   :visit-proof fn-cur-nonexistent-proof :visit-metric (len progress))
 :unchecked "def-cursor refuses a :visit-proof that names no theorem")

; An admitted theorem of another statement cannot license a declaration.
(defthm fn-cur-unrelated t :rule-classes nil)
(must-fail-checked
 (def-cursor fn-cur-wrong-proof ()
   :call (fn-cur-test-one progress)
   :visit-proof fn-cur-unrelated :visit-metric (len progress))
 :unchecked "def-cursor refuses a :visit-proof of another statement")

; An output phase must prove its actual call preserves candidate progress.
(defun fn-cur-test-output-one (progress)
  (declare (xargs :guard t))
  (mv '(65) progress))
(defthm fn-cur-test-output-visits
  (<= (- (len progress) (len (mv-nth 1 (fn-cur-test-output-one progress)))) 1))
(defthm fn-cur-test-output-no-visits
  (implies t
           (equal (- (len progress) (len (mv-nth 1 (fn-cur-test-output-one progress)))) 0)))
(must-fail-checked
 (def-cursor/output fn-cur-output-without-proof ()
   :call (fn-cur-test-output-one progress) :output-phase t
   :visit-proof fn-cur-test-output-visits :visit-metric (len progress))
 :unchecked "def-cursor/output refuses an :output-phase without its :output-proof")
(must-fail-checked
 (def-cursor/output fn-cur-output-wrong-proof ()
   :call (fn-cur-test-output-one progress) :output-phase t :output-proof fn-cur-unrelated
   :visit-proof fn-cur-test-output-visits :visit-metric (len progress))
 :unchecked "def-cursor/output refuses an :output-proof of another statement")
(def-cursor/output fn-cur-output ()
  :call (fn-cur-test-output-one progress) :output-phase t
  :output-proof fn-cur-test-output-no-visits
  :visit-proof fn-cur-test-output-visits :visit-metric (len progress))
(assert-event
 (let* ((cur (fn-cur-make '(:view root-a) '(a b) nil nil))
        (step (mv-list 4 (fn-cur-output-step cur 0 1))))
   (and (equal (car step) '(65)) (equal (nth 2 step) 0)
        (equal (fn-cur-progress (nth 1 step)) '(a b))
        (equal (nth 3 step) :output))))

; -----------------------------------------------------------------------------
; Demand (lane generators with cold-line, 2026-10-04): a step counts the
; payload heads it touches in its progress; the batch stops at the budget.
(include-book "../../books/def-cursor-batch")

; PROGRESS is (READS . ITEMS): each call consumes one item and reads one head.
; The metric is guard-total (the generated batch evaluates it on any cursor).
(defun fn-cur-dtest-reads (progress)
  (declare (xargs :guard t))
  (if (consp progress) (nfix (car progress)) 0))
(defun fn-cur-dtest-one (progress)
  (declare (xargs :guard t))
  (mv nil (if (and (consp progress) (consp (cdr progress)))
              (cons (+ 1 (fn-cur-dtest-reads progress)) (cddr progress))
            nil)))
(defthm fn-cur-dtest-visits
  (<= (- (len (cdr progress)) (len (cdr (mv-nth 1 (fn-cur-dtest-one progress))))) 1))
(defthm fn-cur-dtest-demand
  (<= (- (nfix (fn-cur-dtest-reads (mv-nth 1 (fn-cur-dtest-one progress))))
         (nfix (fn-cur-dtest-reads progress)))
      1))
(def-cursor fn-cur-dtest ()
  :call (fn-cur-dtest-one progress)
  :visit-proof fn-cur-dtest-visits :visit-metric (len (cdr progress))
  :demand-proof fn-cur-dtest-demand :demand-metric (fn-cur-dtest-reads progress))
(verify-guards fn-cur-dtest-step)
(assert-event
 (equal (getpropc 'fn-cur-dtest-step-demand-bound 'theorem nil (w state))
        '(not (< '1 (binary-+ (nfix (fn-cur-dtest-reads (fn-cur-progress (mv-nth '1 (fn-cur-dtest-step cur visits bytes)))))
                              (unary-- (nfix (fn-cur-dtest-reads (fn-cur-progress cur)))))))))
(assert-event
 (equal (cadr (member-eq :demand-bound (cdr (assoc-eq 'fn-cur-dtest (table-alist 'fn-cursor (w state))))))
        'fn-cur-dtest-step-demand-bound))

; Nothing is owed beyond the buffered output: the residual is the pending list.
(local (defthm fn-cur-test-append-fold
         (equal (append a (append b c)) (append (append a b) c))))
(local (in-theory (disable fn-cur-test-append-fold)))
(defun fn-cur-dtest-remaining (cur)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-cur-pending cur) nil))
(defthm fn-cur-dtest-step-residual
  (equal (append (car (fn-cur-dtest-step cur visits bytes))
                 (fn-cur-dtest-remaining (mv-nth 1 (fn-cur-dtest-step cur visits bytes))))
         (fn-cur-dtest-remaining cur))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cur-dtest-step fn-cur-test-append-fold) (fn-cur-split fn-cur-split-residual))
           :use ((:instance fn-cur-split-residual (xs (fn-cur-pending cur)) (n bytes))
                 (:instance fn-cur-split-residual (xs nil) (n bytes))))))
(def-cursor/batch fn-cur-dtest ()
  :step fn-cur-dtest-step
  :byte-proof fn-cur-dtest-step-byte-bound
  :call-proof fn-cur-dtest-step-call-bound
  :remaining (fn-cur-dtest-remaining cur)
  :residual-proof fn-cur-dtest-step-residual
  :demand-metric (fn-cur-dtest-reads progress) :demand-proof fn-cur-dtest-step-demand-bound)

; Budget 2 over four items: two reading steps, then the batch stops with the
; third item unread; budget 0 yields without a step; a large budget runs to
; the end (four reads, a fifth call that ends the progress, then :done).
(assert-event
 (let* ((cur (fn-cur-make '(:view root-a) '(0 a b c d) nil nil))
        (two (mv-list 4 (fn-cur-dtest-batch cur 10 2 2)))
        (zero (mv-list 4 (fn-cur-dtest-batch cur 10 2 0)))
        (all (mv-list 4 (fn-cur-dtest-batch cur 10 2 9))))
   (and (equal (fn-cur-progress (nth 1 two)) '(2 c d))
        (equal (nth 2 two) 2) (equal (nth 3 two) :candidate) (null (nth 0 two))
        (equal (nth 1 zero) cur) (equal (nth 2 zero) 0) (equal (nth 3 zero) :yield)
        (equal (fn-cur-progress (nth 1 all)) nil)
        (equal (nth 2 all) 5) (equal (nth 3 all) :done))))
(assert-event
 (equal (getpropc 'fn-cur-dtest-batch-demand-bound 'theorem nil (w state))
        '(not (< (nfix demand)
                 (binary-+ (nfix (fn-cur-dtest-reads (fn-cur-progress (mv-nth '1 (fn-cur-dtest-batch cur visits bytes demand)))))
                           (unary-- (nfix (fn-cur-dtest-reads (fn-cur-progress cur)))))))))

; A demand metric without its proof, a proof of another statement, and a
; batch whose demand proof is not the step's demand bound are refused.
(must-fail-checked
 (def-cursor fn-cur-dtest-noproof ()
   :call (fn-cur-dtest-one progress)
   :visit-proof fn-cur-dtest-visits :visit-metric (len (cdr progress))
   :demand-metric (fn-cur-dtest-reads progress))
 :unchecked "def-cursor refuses a :demand-metric without its :demand-proof")
(must-fail-checked
 (def-cursor fn-cur-dtest-wrong ()
   :call (fn-cur-dtest-one progress)
   :visit-proof fn-cur-dtest-visits :visit-metric (len (cdr progress))
   :demand-proof fn-cur-dtest-visits :demand-metric (fn-cur-dtest-reads progress))
 :unchecked "def-cursor refuses a :demand-proof of another statement")
(must-fail-checked
 (def-cursor/batch fn-cur-dtest-wrong-batch ()
   :step fn-cur-dtest-step
   :byte-proof fn-cur-dtest-step-byte-bound
   :call-proof fn-cur-dtest-step-call-bound
   :remaining (fn-cur-dtest-remaining cur)
   :residual-proof fn-cur-dtest-step-residual
   :demand-metric (fn-cur-dtest-reads progress) :demand-proof fn-cur-dtest-step-call-bound)
 :unchecked "def-cursor/batch refuses a :demand-proof that is not the step's demand bound")

; The budget-free batch keeps its arity (today's fn-nnw-stream instance):
; the same step shape without :demand, three formals, runs to :done.
(def-cursor fn-cur-dfree ()
  :call (fn-cur-dtest-one progress)
  :visit-proof fn-cur-dtest-visits :visit-metric (len (cdr progress)))
(verify-guards fn-cur-dfree-step)
(defun fn-cur-dfree-remaining (cur)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-cur-pending cur) nil))
(defthm fn-cur-dfree-step-residual
  (equal (append (car (fn-cur-dfree-step cur visits bytes))
                 (fn-cur-dfree-remaining (mv-nth 1 (fn-cur-dfree-step cur visits bytes))))
         (fn-cur-dfree-remaining cur))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cur-dfree-step fn-cur-test-append-fold) (fn-cur-split fn-cur-split-residual))
           :use ((:instance fn-cur-split-residual (xs (fn-cur-pending cur)) (n bytes))
                 (:instance fn-cur-split-residual (xs nil) (n bytes))))))
(def-cursor/batch fn-cur-dfree ()
  :step fn-cur-dfree-step
  :byte-proof fn-cur-dfree-step-byte-bound
  :call-proof fn-cur-dfree-step-call-bound
  :remaining (fn-cur-dfree-remaining cur)
  :residual-proof fn-cur-dfree-step-residual)
(assert-event
 (and (equal (formals 'fn-cur-dfree-batch (w state)) '(cur visits bytes))
      (equal (formals 'fn-cur-dtest-batch (w state)) '(cur visits bytes demand))
      (let ((all (mv-list 4 (fn-cur-dfree-batch (fn-cur-make '(:view root-a) '(0 a b c d) nil nil) 10 2))))
        (and (equal (fn-cur-progress (nth 1 all)) nil)
             (equal (nth 2 all) 5) (equal (nth 3 all) :done)))))
