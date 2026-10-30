; Static callback-level change detector, not a per-source-phase refinement proof.
; Shared callbacks use the UNION of their source states' successors. Scenario
; microsteps separately check exact source/destination edges, including harvest.
(in-package "ACL2")
(include-book "../sim/commit-resources")
(fn2-book-layer :b)
(make-event (value `(defconst *fn2-cru-arms*
 ',(fn2-machine-property 'fn2-commit :continuations (w state)))))
(make-event (value `(defconst *fn2-cru-observers*
 ',(fn2-machine-property 'fn2-commit :observes (w state)))))
(make-event (value `(defconst *fn2-cru-phases*
 ',(pairlis$ (strip-cars (strip-cdrs (fn2-columns-enum-constants 'fn2-commit-state
      (fn2-machine-property 'fn2-commit :states (w state)) 0)))
             (fn2-machine-property 'fn2-commit :states (w state))))))
(defun fn2-cru-definitions (forms)
 (declare (xargs :verify-guards nil))
 (if (atom forms) nil
  (let ((form (car forms)))
   (if (member-eq (car form) '(defun defmachine-callback))
       (cons (cons (cadr form) (if (eq (car form) 'defun) (cdddr form) (nthcdr 5 form)))
             (fn2-cru-definitions (cdr forms))) (fn2-cru-definitions (cdr forms))))))
(defun fn2-cru-calls (term names)
 (declare (xargs :verify-guards nil))
 (if (or (atom term) (member-eq (car term) '(quote declare))) nil
  (union-eq (and (member-eq (car term) names) (list (car term)))
   (union-eq (fn2-cru-calls (car term) names) (fn2-cru-calls (cdr term) names)))))
(defun fn2-cru-expand (names defs)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (union-eq (fn2-cru-calls (cdr (assoc-eq (car names) defs)) (strip-cars defs))
            (fn2-cru-expand (cdr names) defs))))
; N definitions bound every simple callgraph path by N-1 edges. No magic fuel.
(defun fn2-cru-closure (left names defs)
 (declare (xargs :verify-guards nil :measure (nfix left)))
 (if (zp left) names
  (let ((next (union-eq names (fn2-cru-expand names defs))))
   (if (subsetp-eq next names) names (fn2-cru-closure (- left 1) next defs)))))
(defun fn2-cru-phase-values (expression)
 (declare (xargs :verify-guards nil))
 (cond ((assoc-eq expression *fn2-cru-phases*) (list (cdr (assoc-eq expression *fn2-cru-phases*))))
       ((and (consp expression) (eq (car expression) 'if))
        (union-eq (fn2-cru-phase-values (caddr expression)) (fn2-cru-phase-values (cadddr expression))))
       (t (list :unknown-phase-expression))))
(defun fn2-cru-writes (term)
 (declare (xargs :verify-guards nil))
 (if (or (atom term) (member-eq (car term) '(quote declare))) nil
  (if (eq (car term) 'fn2-commit-put-core)
      (let ((phase (assoc-eq 'phase (cddr term)))) (and phase (fn2-cru-phase-values (cadr phase))))
    (union-eq (fn2-cru-writes (car term)) (fn2-cru-writes (cdr term))))))
(defun fn2-cru-targets (names defs)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (union-eq (fn2-cru-writes (cdr (assoc-eq (car names) defs))) (fn2-cru-targets (cdr names) defs))))
(defun fn2-cru-allowed (callback arms)
 (declare (xargs :verify-guards nil))
 (if (atom arms) nil
  (union-eq (and (eq callback (cadar arms))
                (cons (caar arms) (cdr (assoc-eq (caar arms) *fn2-commit-transitions*))))
            (fn2-cru-allowed callback (cdr arms)))))
(defun fn2-cru-observer-allowed (states)
 (declare (xargs :verify-guards nil))
 (if (atom states) (strip-cars *fn2-commit-transitions*)
  (intersection-eq (cons (car states) (cdr (assoc-eq (car states) *fn2-commit-transitions*)))
                   (fn2-cru-observer-allowed (cdr states)))))
(defun fn2-cru-audit (callbacks defs)
 (declare (xargs :verify-guards nil))
 (if (atom callbacks) t
  (let* ((name (car callbacks)) (observer (member-eq name (strip-cars (strip-cdrs *fn2-cru-observers*))))
         (allowed (if observer (fn2-cru-observer-allowed (remove-eq :free (strip-cars *fn2-commit-transitions*)))
                    (fn2-cru-allowed name *fn2-cru-arms*))))
   (and (assoc-eq name defs)
        (subsetp-eq (fn2-cru-targets (fn2-cru-closure (len defs) (list name) defs) defs) allowed)
        (fn2-cru-audit (cdr callbacks) defs)))))
;; The commit kind's events are two sections since the assembly split (71c1fb2f2); the audit reads both.
(defconst *fn2-cru-defs* (fn2-cru-definitions (append (cdr (fn2-commit-event-forms))
                                                      (cdr (fn2-commit-event-forms-2)))))
(defconst *fn2-cru-callbacks* (remove-duplicates-equal
 (append (strip-cars (strip-cdrs *fn2-cru-arms*)) (strip-cars (strip-cdrs *fn2-cru-observers*)))))
(assert-event (fn2-cru-audit *fn2-cru-callbacks* *fn2-cru-defs*))
(assert-event
 (and (member-eq :seal (fn2-cru-targets (fn2-cru-closure (len *fn2-cru-defs*) '(fn2-commit-collect) *fn2-cru-defs*) *fn2-cru-defs*))
      (member-eq :draining (fn2-cru-targets (fn2-cru-closure (len *fn2-cru-defs*) '(fn2-commit-notify) *fn2-cru-defs*) *fn2-cru-defs*))
      (equal (fn2-cru-targets (fn2-cru-closure (len *fn2-cru-defs*) '(fn2-commit-observe) *fn2-cru-defs*) *fn2-cru-defs*) '(:uncertain))))
(assert-event (not (fn2-cru-audit *fn2-cru-callbacks*
 (put-assoc-eq 'fn2-commit-notify
  (cons '(fn2-commit-put-core id (phase *fn2-commit-state-free*))
        (cdr (assoc-eq 'fn2-commit-notify *fn2-cru-defs*))) *fn2-cru-defs*))))
; Independent prefix inventory check over the ACTUAL generated P/V word.
; Reusable holdings return to zero; immutable-root holdings remain declared.
(defun fn2-cru-potential-delta (values)
 (if (atom (cdr values)) 0
  (+ (- (ifix (cadr values)) (ifix (car values))) (fn2-cru-potential-delta (cdr values)))))
(defthm fn2-cru-potential-telescopes
 (equal (fn2-cru-potential-delta values)
  (if (consp values) (- (ifix (car (last values))) (ifix (car values))) 0)))
(defthm fn2-cru-every-cycle-conservative
 (implies (equal (car (last values)) (car values))
          (equal (fn2-cru-potential-delta values) 0)))
(defun fn2-cru-cycle (name word retained)
 (declare (xargs :verify-guards nil))
 (let ((caps (pairlis$ *fn2-commit-resource-order* (make-list (len *fn2-commit-resource-order*) :initial-element 1))))
  (mv-let (ok intervals) (fn2-pv-word word caps 0 1 nil retained)
   (declare (ignore intervals))
   (list (if (and ok (fn2-pv-capsp retained) (fn2-pv-retention-valid retained caps)) :ok :refused) name))))
(defun fn2-cru-drop-release (word resource)
 (declare (xargs :verify-guards nil))
 (if (atom word) nil
  (if (equal (car word) (list :v resource)) (cdr word)
    (cons (car word) (fn2-cru-drop-release (cdr word) resource)))))
(assert-event (equal (fn2-cru-cycle :baseline (fn2-cr-commit-word 0) *fn2-commit-resource-retained*) '(:ok :baseline)))
(assert-event (equal (fn2-cru-cycle :preflush-fua (fn2-cr-commit-word 1) *fn2-commit-resource-retained*) '(:ok :preflush-fua)))
(assert-event (equal (fn2-cru-cycle :baseline-missing-vpool
 (fn2-cru-drop-release (fn2-cr-commit-word 0) :pool) *fn2-commit-resource-retained*) '(:refused :baseline-missing-vpool)))
(assert-event (and (= (len *fn2-commit-seal-stages*) 19)
 (= *fn2-commit-seal-stage-records* 10) (= *fn2-commit-seal-stage-save-seal* 17)
 (= *fn2-commit-seal-stage-hash-seal-frame* 18) (= *fn2-commit-unit-bytes* 4096)
 (= *fn2-commit-write-resources* 3) (= *fn2-commit-pools* 4) (= *fn2-commit-extent-bytes* 12288)
 (= *fn2-commit-frame-trailer* 4063) (= *fn2-commit-frame-digest* 4064)))
(make-event (value `(assert-event
 (and (= ,(fn2-machine-property 'fn2-commit :capacity (w state)) 2)
      (equal ',(fn2-decl-get :init (fn2-decl-row '(:core-child fn2-core-commit-io) (w state)))
             '(fn2-commit-io-init 6 fn2-commit-io))
      (< (+ (* 1 *fn2-commit-write-resources*) (- *fn2-commit-write-resources* 1)) 6)))))

; DM0b: check every B arm against the same input and forwarding checks used by
; defmachine-callback, and check the admitted operation's authoritative formals.
(defun fn2-cru-callback-contracts (names defs world)
 (declare (xargs :verify-guards nil))
 (if (atom names) t
  (let* ((name (car names)) (body (cdr (assoc-eq name defs)))
         (operation (fn2-operation-row name world))
         (rows (fn2-decl-get :row-bindings operation)))
   (and body operation
        (equal (fn2-decl-get :owner operation) '(:machine fn2-commit))
        (equal (fn2-decl-get :calling-convention operation)
               (getpropc name 'formals nil world))
        (not (fn2-callback-input-error body world))
        (not (fn2-callback-forwarding body rows world))
        (fn2-cru-callback-contracts (cdr names) defs world)))))
(assert-event (fn2-cru-callback-contracts *fn2-cru-callbacks* *fn2-cru-defs* (w state)))
(assert-event
 (not (fn2-cru-callback-contracts *fn2-cru-callbacks*
  (put-assoc-eq 'fn2-commit-writes
   '((b* (((when t) (fn2-machine-yield id fn2-core)))
       (fn2-machine-yield id fn2-core))) *fn2-cru-defs*) (w state))))
(value-triple (cw "B3c DM0b: 11 callback contracts; unsupported-binder control PASS~%"))
