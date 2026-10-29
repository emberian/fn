; The deadlock-freedom keystone of D0, owed, over the assembled core. Kept
; out of resources.lisp so that book stays a library (it includes only the
; declaration machinery); this one includes the served assembly through the
; executor. Teeth: tests/sim-acquisition.lisp.
(in-package "ACL2")
(include-book "resources")
(include-book "executor")
(fn2-book-layer :d)

(make-event (value (fn2-declare '(:operation-set fn2-resources) nil nil nil)))

; The assembled machine kinds in kind-tag order with their phase names, and
; the common wait-reason enum's names in code order: both read from the
; declarations, never a second list.
(defun fn2-resource-kind-states (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons (cons (car names) (fn2-machine-property (car names) :states world))
          (fn2-resource-kind-states (cdr names) world))))
(make-event
 (value `(defconst *fn2-resource-machine-states*
           ',(fn2-resource-kind-states (fn2-machine-names (w state)) (w state)))))
; Each kind's holds per phase, read from its defmachine :holds (R7); every
; declared phase listed, () when it holds nothing.
(defun fn2-resource-phase-holds (states holds)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (cons (cons (car states) (fn2-arm-holds-of (car states) holds))
          (fn2-resource-phase-holds (cdr states) holds))))
(defun fn2-resource-kind-holds (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons (cons (car names) (fn2-resource-phase-holds (fn2-machine-property (car names) :states world)
                                                      (fn2-machine-property (car names) :holds world)))
          (fn2-resource-kind-holds (cdr names) world))))
(make-event
 (value `(defconst *fn2-resource-machine-holds*
           ',(fn2-resource-kind-holds (fn2-machine-names (w state)) (w state)))))
(assert-event (fn2-resource-machine-holds-p *fn2-resource-machine-holds* *fn2-resource-order*))
; Every arm's resource effect rows (one per operation reached from a source
; phase), the same rows defmachine-run checked per arm.
(defun fn2-resource-arms-rows (name arms observationp world)
  (declare (xargs :verify-guards nil))
  (if (atom arms) nil
    (let* ((c (cddar arms))
           (states (fn2-machine-property name :states world))
           (sources (if observationp (or (fn2-arm-get :from c) (fn2-machine-observe-default-from states))
                      (list (caar arms)))))
      (append (fn2-arm-effect-rows name sources (fn2-arm-get :uses c)
                                   (fn2-machine-property name :holds world) world)
              (fn2-resource-arms-rows name (cdr arms) observationp world)))))
(defun fn2-resource-all-arm-rows (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (append (fn2-resource-arms-rows (car names) (fn2-machine-property (car names) :continuations world) nil world)
            (fn2-resource-arms-rows (car names) (fn2-machine-property (car names) :observes world) t world)
            (fn2-resource-all-arm-rows (cdr names) world))))
(make-event
 (value `(defconst *fn2-resource-arm-effects*
           ',(remove-duplicates-equal (fn2-resource-all-arm-rows (fn2-machine-names (w state)) (w state))))))
(assert-event (fn2-resource-effects-p *fn2-resource-arm-effects* *fn2-resource-order*))
(defconst *fn2-resource-wait-names*
  (caddr (cadr (assoc-eq 'wait-reason *fn2-machine-common-fields*))))
(assert-event (equal *fn2-resource-wait-names*
                     (list* :none :completion (strip-cars *fn2-resource-order*))))

; Coverage: every assembled kind has a holds entry for every phase it
; declares; a wait reason is a kind by name, or :none / :completion.
; A kind added to the assembly without its holds (R7 moves them into
; defmachine) is refused here by name.
(defun fn2-resource-holds-cover-p (kinds table)
  (declare (xargs :verify-guards nil))
  (if (atom kinds) t
    (let ((phases (cdr (assoc-eq (caar kinds) table))))
      (and (fn2-resource-subsetp (cdar kinds) (strip-cars phases))
           (fn2-resource-holds-cover-p (cdr kinds) table)))))
(assert-event (fn2-resource-holds-cover-p *fn2-resource-machine-states* *fn2-resource-machine-holds*)
              :msg (msg "A machine kind or phase lacks its D0 holds: ~x0" *fn2-resource-machine-states*))

; The wait-for projection of one row: (held . awaited) when the row waits
; for a resource kind, nil otherwise (free, running, or waiting for an
; operation's completion, which its reserved result cells guarantee).
(defun fn2-resource-row-waiter (kind phase reason)
  (declare (xargs :verify-guards nil))
  (let* ((entry (nth kind *fn2-resource-machine-states*))
         (phase-name (nth phase (cdr entry)))
         (held (cdr (assoc-eq phase-name (cdr (assoc-eq (car entry) *fn2-resource-machine-holds*)))))
         (name (nth reason *fn2-resource-wait-names*))
         (awaited (and (fn2-resource-kindp name *fn2-resource-order*) name)))
    (and awaited (cons held awaited))))

(defun fn2-resource-waiters-from (id n fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix (- (nfix n) (nfix id)))))
  (if (or (not (natp id)) (not (natp n)) (>= id n)) nil
    (let ((w (fn2-resource-row-waiter (fn2-machine-kind id fn2-core) (fn2-machine-phase id fn2-core)
                                      (fn2-machine-wait-reason id fn2-core))))
      (if w (cons w (fn2-resource-waiters-from (+ 1 id) n fn2-core))
        (fn2-resource-waiters-from (+ 1 id) n fn2-core)))))

; Every waiting row of the core, as (held . awaited).
(defun fn2-resource-waiters (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((n (stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
             (n) (fn2-machines-rows fn2-machines) n)))
    (fn2-resource-waiters-from 0 n fn2-core)))

(defun fn2-resource-core-ranked-p (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (fn2-resource-waiters-ranked-p (fn2-resource-waiters fn2-core) *fn2-resource-order*))

; The keystone: initialization establishes, and every turn preserves, that
; each waiting holder's held kinds rank below the kind it awaits. With the
; proved fn2-resource-ranked-no-cycle this excludes a wait-for cycle, so no
; reachable state has every holder waiting on another holder.
(defthm-owed fn2-resource-no-deadlock (profile core)
  (and (implies (fn2-core-profilep profile)
                (fn2-resource-core-ranked-p (fn2-init-executor profile :echo t core)))
       (implies (and (fn2-corep core) (fn2-core-wfp core) (fn2-resource-core-ranked-p core))
                (fn2-resource-core-ranked-p (mv-nth 4 (fn2-turn core)))))
  :schema :invariant :from (:operation-set fn2-resources)
  :teeth (fn2-resource-test-no-deadlock fn2-resource-test-no-deadlock-negative)
  :doc "Init establishes and every turn preserves: each waiting machine holds only resource kinds ranked below the kind it awaits (D0's order), so with fn2-resource-ranked-no-cycle no wait-for cycle exists.")
