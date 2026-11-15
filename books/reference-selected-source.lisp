; Bind an explicitly selected dispatcher to the live source/attachment world.
; This is source identity and a theorem about the resolved program. It is NOT
; an equality between a constrained logical stub and its executable attachment,
; nor a proof about the host executing that attachment map.
(in-package "ACL2")
(include-book "translation-validation")

(defun fn2-selected-pairs (stubs world)
 (declare (xargs :verify-guards nil))
 (if (atom stubs) (mv nil nil)
  (let ((pair (fn2-tv-attachment (car stubs) world)))
   (if (not (and (consp pair) (eq (car pair) (car stubs))
                 (symbolp (cdr pair)) (function-symbolp (cdr pair) world)))
       (mv (list :missing-selection (car stubs)) nil)
    (mv-let (err rest) (fn2-selected-pairs (cdr stubs) world)
     (mv err (cons pair rest)))))))

; Replace function-position names only. Quoted data and lambda-bound variables
; retain their identity. The map is deliberately one step: a selected function
; that itself needs resolving requires its own declared source square.
(mutual-recursion
 (defun fn2-selected-body (term pairs)
  (declare (xargs :verify-guards nil))
  (cond ((atom term) term) ((eq (car term) 'quote) term)
        ((consp (car term))
         (cons (list 'lambda (cadar term)
                     (fn2-selected-body (caddar term) pairs))
               (fn2-selected-body-list (cdr term) pairs)))
        (t (cons (let ((pair (assoc-eq (car term) pairs)))
                   (if pair (cdr pair) (car term)))
                 (fn2-selected-body-list (cdr term) pairs)))))
 (defun fn2-selected-body-list (terms pairs)
  (declare (xargs :verify-guards nil))
  (if (atom terms) nil
   (cons (fn2-selected-body (car terms) pairs)
         (fn2-selected-body-list (cdr terms) pairs)))))

(defun fn2-reference-selected-body-formula (source selected stubs world)
 (declare (xargs :verify-guards nil))
 (mv-let (err pairs) (fn2-selected-pairs stubs world)
  (let ((body (getpropc source 'unnormalized-body nil world)))
   (and (not err) (pseudo-termp body) body
        `(equal (,selected ,@(getpropc source 'formals nil world))
                ,(fn2-selected-body body pairs))))))

(defun fn2-selected-metadata (fn world)
 (declare (xargs :verify-guards nil))
 (list (fn2-tv-function fn world) (symbol-class fn world)))

(defun fn2-selected-calls (fn world)
 (declare (xargs :verify-guards nil))
 (let* ((body (getpropc fn 'unnormalized-body nil world))
        (guard (getpropc fn 'guard nil world))
        (justification (getpropc fn 'justification nil world))
        (measure (and (getpropc fn 'recursivep nil world) justification
                      (access justification justification :measure)))
        (pair (fn2-tv-attachment fn world)))
  (append (fn2-tv-calls body) (fn2-tv-calls guard) (fn2-tv-calls measure)
          (and pair (list (cdr pair))))))

; Snapshot the actual reachable graph, including scalar helpers, guards,
; recursive measures and selected implementations. Repeated/recursive nodes
; terminate through SEEN, not by silently dropping an unresolved dependency.
; The finite generator budget refuses exhaustion; it does not truncate.
(defun fn2-selected-closure (pending seen rows world fuel)
 (declare (xargs :verify-guards nil :measure (nfix fuel)))
 (cond ((atom pending) (mv nil (reverse rows)))
       ((zp fuel) (mv :source-graph-budget nil))
       ((or (member-eq (car pending) seen)
            (member-eq (car pending) *fn2-tv-native-boundary*))
        (fn2-selected-closure (cdr pending) seen rows world (1- fuel)))
       ((not (function-symbolp (car pending) world))
        (mv (list :missing-source-function (car pending)) nil))
       (t
        (let* ((fn (car pending))
               (body (getpropc fn 'unnormalized-body nil world))
               (pair (fn2-tv-attachment fn world)))
         (if (not (or body pair))
             (mv (list :unresolved-source-function fn) nil)
          (fn2-selected-closure
           (append (fn2-selected-calls fn world) (cdr pending))
           (cons fn seen) (acons fn (fn2-selected-metadata fn world) rows)
           world (1- fuel)))))))

(defun fn2-selected-reachable-attachments (rows world)
 (declare (xargs :verify-guards nil))
 (if (atom rows) nil
  (let ((pair (fn2-tv-attachment (caar rows) world)))
   (append (and pair (list pair))
           (fn2-selected-reachable-attachments (cdr rows) world)))))

(defun fn2-selected-direct-stubs (calls world)
 (declare (xargs :verify-guards nil))
 (if (atom calls) nil
  (let ((rest (fn2-selected-direct-stubs (cdr calls) world)))
   (if (fn2-tv-attachment (car calls) world)
       (add-to-set-eq (car calls) rest) rest))))

(defun fn2-selected-stateful-attachments (pairs world)
 (declare (xargs :verify-guards nil))
 (if (atom pairs) nil
  (append
   (and (or (remove-eq nil (getpropc (caar pairs) 'stobjs-in nil world))
            (remove-eq nil (getpropc (caar pairs) 'stobjs-out nil world)))
        (list (car pairs)))
   (fn2-selected-stateful-attachments (cdr pairs) world))))

(defun fn2-selected-source-problem (source selected stubs theorem world)
 (declare (xargs :verify-guards nil))
 (let* ((body (getpropc source 'unnormalized-body nil world))
        (expected (fn2-reference-selected-body-formula source selected stubs world)))
  (cond
   ((not (and (function-symbolp source world) (function-symbolp selected world)
              (not (eq source selected)))) :source-or-selected-name)
   ((not (and (symbol-listp stubs) (no-duplicatesp-eq stubs))) :selection-census)
   ((not (subsetp-eq stubs (fn2-tv-calls body))) :selection-not-in-source-body)
   ((not (subsetp-eq (fn2-selected-direct-stubs (fn2-tv-calls body) world) stubs))
    :incomplete-dispatch-selection)
   ((not (equal (getpropc source 'formals nil world)
                (getpropc selected 'formals nil world))) :selected-formals)
   ((not (and (equal (getpropc source 'stobjs-in nil world)
                    (getpropc selected 'stobjs-in nil world))
              (equal (getpropc source 'stobjs-out nil world)
                    (getpropc selected 'stobjs-out nil world)))) :selected-abi)
   ((not (equal (getpropc source 'guard t world)
                (getpropc selected 'guard t world))) :selected-guard)
   ((not (eq (symbol-class source world) :common-lisp-compliant)) :source-guards-unverified)
   ((not (eq (symbol-class selected world) :common-lisp-compliant)) :selected-guards-unverified)
   ((not (and expected (getpropc theorem 'theorem nil world)
              (equal (getpropc theorem 'untranslated-theorem nil world) expected)))
    :resolved-source-equation)
   (t nil))))

; A binding record retains the equation's exact subject and all reachable
; metadata. Remaining scalar attachments are an explicit shared-parametric
; census, not discharged by this dispatcher square. Remaining state-bearing
; hooks refuse completion: their selected-source and full-R squares must be
; connected before this dispatcher is accepted as the selected subject.
(defun fn2-reference-selected-record (source selected stubs theorem world)
 (declare (xargs :verify-guards nil))
 (let ((problem (fn2-selected-source-problem source selected stubs theorem world)))
  (if problem (mv problem nil)
   (mv-let (err pairs) (fn2-selected-pairs stubs world)
    (mv-let (closure-error rows)
      (fn2-selected-closure (list source selected) nil nil world 1000000)
     (mv-let (selected-error selected-rows)
       (fn2-selected-closure (list selected) nil nil world 1000000)
      (let* ((remaining (fn2-selected-reachable-attachments selected-rows world))
             (stateful (fn2-selected-stateful-attachments remaining world))
             (problem (or err closure-error selected-error
                          (and stateful (list :remaining-stateful-attachments stateful)))))
       (mv problem
        (and (not problem)
         (list :source source :selected selected :stubs stubs :pairs pairs
               :source-theorem theorem
               :source-formula (fn2-reference-selected-body-formula source selected stubs world)
               :native-boundary *fn2-tv-native-boundary* :graph rows
               :reachable-attachments (fn2-selected-reachable-attachments rows world)
               :selected-shared-scalar-attachments remaining
               :scope :declared-dispatch-resolution
               :logical-stub-equality nil :host-execution-proof nil))))))))))

(defun fn2-selected-get (key row)
 (declare (xargs :verify-guards nil))
 (if (atom row) nil
  (if (eq key (car row)) (cadr row) (fn2-selected-get key (cddr row)))))

(defun fn2-reference-selected-currentp (record world)
 (declare (xargs :verify-guards nil))
 (and (consp record)
  (mv-let (err current)
   (fn2-reference-selected-record
    (fn2-selected-get :source record) (fn2-selected-get :selected record)
    (fn2-selected-get :stubs record) (fn2-selected-get :source-theorem record) world)
   (and (not err) (equal record current)))))

(defmacro fn2-reference-selected-bind (key source selected stubs theorem)
 `(make-event
   (mv-let (problem record)
     (fn2-reference-selected-record ',source ',selected ',stubs ',theorem (w state))
    (if problem
        (er soft 'fn2-reference-selected-bind "Refused selected source ~x0: ~x1." ',source problem)
      (value (list 'table 'fn2-reference-selected-sources
                   (list 'quote ',key) (list 'quote record)))))))

; Consumers must run this in their final assembled world. A stale table row,
; or a different callback selected after registration, is not valid evidence.
(defmacro fn2-reference-selected-check (key)
 `(make-event
   (if (fn2-reference-selected-currentp
        (cdr (assoc-equal ',key (table-alist 'fn2-reference-selected-sources (w state)))) (w state))
       '(value-triple :selected-source-current)
     (er soft 'fn2-reference-selected-check "Selected source ~x0 changed or is missing." ',key))))
