; B3 resource abstraction, logic/tests only. One healthy admitted two-batch wave.
; Existing roots subtract capacity; installed ownership is retained at terminal.
; No retirement, fault recovery, actual notification Send, or full A ownership claim.
(in-package "ACL2")
(include-book "../books/assembly")
(include-book "check-deadlock")
(fn2-book-layer :b)

(defconst *fn2-commit-resource-order*
 '(:batch :pool :extent :root :prepared :installed :gate :op :queued :io :fence :send))
(defconst *fn2-commit-resource-retained* '((:extent . 1) (:root . 1) (:installed . 1)))
(defun fn2-cr-count (resource holds)
 (declare (xargs :verify-guards nil)) (nfix (cdr (assoc-eq resource holds))))
(defun fn2-cr-base (phase)
 (declare (xargs :verify-guards nil)) (cdr (assoc-eq phase *fn2-commit-holds*)))
(defun fn2-cr-phase-path (mode)
 (declare (xargs :verify-guards nil))
 (append '(:free :collect :seal :dependencies)
         (if (equal mode 1) '(:fence :log-write) '(:log-write :fence))
         '(:durable :install :publish :notify :draining :free)))
(defun fn2-cr-declared-pathp (path)
 (declare (xargs :verify-guards nil))
 (if (atom (cdr path)) t
  (and (member-eq (cadr path) (cdr (assoc-eq (car path) *fn2-commit-transitions*)))
       (fn2-cr-declared-pathp (cdr path)))))
(defun fn2-cr-overlay (base op queued io gate fence)
 (declare (xargs :verify-guards nil))
 (append (list (cons :op op) (cons :queued queued) (cons :io io)
               (cons :gate gate) (cons :fence fence)) base))
(defun fn2-cr-repeat (n operation resource)
 (declare (xargs :verify-guards nil :measure (nfix n)))
 (if (zp n) nil (cons (list operation resource) (fn2-cr-repeat (- n 1) operation resource))))
; Acquire before release: the install edge exists before prepared edge removal.
; Splitting atomic bundles only adds possible hold/wait, never early releases.
(defun fn2-cr-delta (resources before after acquire)
 (declare (xargs :verify-guards nil))
 (if (atom resources) nil
  (let* ((r (car resources)) (delta (- (fn2-cr-count r after) (fn2-cr-count r before))))
   (append (fn2-cr-repeat (if acquire (nfix delta) (nfix (- delta))) (if acquire :p :v) r)
           (fn2-cr-delta (cdr resources) before after acquire)))))
(defun fn2-cr-compile (potentials before)
 (declare (xargs :verify-guards nil))
 (if (atom potentials) nil
  (append (fn2-cr-delta *fn2-commit-resource-order* before (car potentials) t)
          (fn2-cr-delta *fn2-commit-resource-order* before (car potentials) nil)
          (fn2-cr-compile (cdr potentials) (car potentials)))))
(defun fn2-cr-write-states (base logs)
 (declare (xargs :verify-guards nil))
 (if logs
  ; Both logs overlap: first result may release its op but BOTH allocator edges
  ; remain until the class completes. Early actual releases are pessimistically delayed.
  (list (fn2-cr-overlay base 1 1 1 0 0) (fn2-cr-overlay base 2 2 2 0 0)
        (fn2-cr-overlay base 2 0 2 0 0) (fn2-cr-overlay base 1 0 2 0 0) base)
  (list (fn2-cr-overlay base 1 1 1 0 0) (fn2-cr-overlay base 1 0 1 0 0) base)))
(defun fn2-cr-fence-states (base gate)
 (declare (xargs :verify-guards nil))
 ; Physical F is acquired at adapter take BEFORE Q release. Physical completion
 ; releases F independently of outbox drain; harvest subsequently releases O/G.
 (list (fn2-cr-overlay base 0 0 0 gate 0) (fn2-cr-overlay base 1 1 0 gate 0)
       (fn2-cr-overlay base 1 1 0 gate 1) (fn2-cr-overlay base 1 0 0 gate 1)
       (fn2-cr-overlay base 1 0 0 gate 0) base))
(defun fn2-cr-drain-states (left base)
 (declare (xargs :verify-guards nil :measure (nfix left)))
 (if (zp left) (list *fn2-commit-resource-retained*)
  (cons (put-assoc-eq :pool (- left 1) base) (fn2-cr-drain-states (- left 1) base))))
(defun fn2-cr-commit-word (mode)
 (declare (xargs :verify-guards nil))
 (let ((dep (fn2-cr-base :dependencies)) (log (fn2-cr-base :log-write))
       (fence (fn2-cr-base :fence)) (drain (fn2-cr-base :draining)))
  (fn2-cr-compile
   (append (list (fn2-cr-base :collect) (fn2-cr-base :seal) dep)
    (fn2-cr-write-states dep nil)
    (if (equal mode 1)
        (append (list fence) (fn2-cr-fence-states fence 1)
                (list log) (fn2-cr-write-states log t))
      (append (list log) (fn2-cr-write-states log t)
              (list fence) (fn2-cr-fence-states fence 1)))
    (list (fn2-cr-base :durable) (fn2-cr-base :install) (fn2-cr-base :publish)
          (fn2-cr-base :notify) drain)
    (fn2-cr-drain-states (fn2-cr-count :pool drain) drain)) (fn2-cr-base :free))))
(defun fn2-cr-scribe-word ()
 (declare (xargs :verify-guards nil))
 ; A's scribe retains its pool through NEXT; this finite iteration retains it too.
 (let ((base '((:pool . 1))))
  (fn2-cr-compile (append (list base (fn2-cr-overlay base 1 1 0 0 0)
                              (fn2-cr-overlay base 1 0 0 0 0) base)
                   (fn2-cr-fence-states base 0)
                   (list (fn2-cr-overlay base 1 1 0 0 0)
                         (fn2-cr-overlay base 1 0 0 0 0) base)) nil)))
(defun fn2-cr-pool-count (classes size count)
 (declare (xargs :verify-guards nil))
 (if (atom classes) count
  (let ((bytes (cdar classes)))
   (if (and (natp bytes) (<= 4096 bytes) (or (zp size) (< bytes size)))
       (fn2-cr-pool-count (cdr classes) bytes (nfix (caar classes)))
     (fn2-cr-pool-count (cdr classes) size count)))))
(defun fn2-cr-profile (key default profile)
 (declare (xargs :verify-guards nil))
 (nfix (if (assoc-eq key profile) (cdr (assoc-eq key profile)) default)))
(defun fn2-cr-recipient-name (n)
 (declare (xargs :verify-guards nil))
 (intern-in-package-of-symbol
  (concatenate 'string "RECIPIENT-" (coerce (explode-nonnegative-integer (nfix n) 10 nil) 'string)) :send))
(defun fn2-cr-recipients (n slots)
 (declare (xargs :verify-guards nil :measure (nfix n)))
 (if (zp n) (mv nil nil)
  (mv-let (threads caps) (fn2-cr-recipients (- n 1) slots)
   (let ((r (fn2-cr-recipient-name (- n 1))))
    (mv (cons (list (list :p r) (list :v r)) threads) (cons (cons r slots) caps))))))
(defun fn2-commit-resource-model (profile mode)
 (declare (xargs :verify-guards nil))
 (let* ((word (fn2-cr-commit-word mode))
        (c (fn2-cr-profile :c 0 profile))
        (a (fn2-cr-profile :accept-credits 0 profile))
        (existing (fn2-cr-profile :commit-existing-roots 0 profile))
        (extents (nfix (- (fn2-cr-profile :extent-slots 16 profile) existing)))
        (pool (fn2-cr-pool-count (fn2-profile-pool-classes profile) 0 0)))
  (mv-let (recipients sends) (fn2-cr-recipients c (fn2-cr-profile :recipient-send-slots 1 profile))
   (let ((threads (append (list word word (if (zp pool) nil (fn2-cr-scribe-word)))
                    ; Explicit A projection: ONLY outbox contention, not A ownership.
                    (make-list (+ c a) :initial-element '((:p :queued) (:v :queued))) recipients)))
    (mv threads
     (append (list (cons :batch 2) (cons :pool pool) (cons :extent extents) (cons :root extents)
                   (cons :prepared 2) (cons :installed extents) (cons :gate 1)
                   (cons :op (fn2-profile-o profile)) (cons :queued (fn2-profile-qa profile))
                   (cons :io 6) (cons :fence (fn2-profile-fence-slots profile))) sends)
     (append (list *fn2-commit-resource-retained* *fn2-commit-resource-retained*
                   (if (zp pool) nil '((:pool . 1))))
             (make-list (+ c a c) :initial-element nil)))))))
(defun fn2-commit-deadlock-check (profile mode)
 (declare (xargs :verify-guards nil))
 (mv-let (threads caps retained) (fn2-commit-resource-model profile mode)
  (if (not (and (member-equal mode '(0 1)) (fn2-cr-declared-pathp (fn2-cr-phase-path mode))
                (<= 2 (fn2-cr-count :extent caps))
                (<= 2 (fn2-cr-count :root caps)) (<= 8 (fn2-cr-count :pool caps))))
      '((:status . :not-admitted-two-batch-wave))
   (fn2-pv-check-retained threads caps retained))))

; The predecessor seal/publication waits do not acquire capacity: seal performs
; bounded work on pre-admitted buffers; publication precedes its successor's
; install wait. No operation/G/F holding crosses the install wait. FIFO head
; blocking never disables independent physical completion or reserved-cell harvest.
; Recipients start from replayable published-root debt, after batch ownership
; has exited; cursors and Send are abstract integration, not implemented I/O.
; A zero result covers this resource projection under bounded completion, not
; starvation, crashes, quarantine, arbitrary adapters, or an exact PV refinement.
(defun fn2-cr-wrong-order (resource)
 (declare (xargs :verify-guards nil))
 (fn2-pv-check
  (list (list '(:p :batch) (list :p resource) (list :v resource) '(:v :batch))
        (list '(:p :batch) (list :p resource) (list :v resource) '(:v :batch))
        (list (list :p resource) '(:p :batch) '(:v :batch) (list :v resource)))
  (list (cons :batch 2) (cons resource 1))))
(defun fn2-commit-wrong-mutex-order ()
 (declare (xargs :verify-guards nil)) (fn2-cr-wrong-order :fence))
(defun fn2-commit-held-notification ()
 (declare (xargs :verify-guards nil)) (fn2-cr-wrong-order :send))
(assert-event (equal (cdr (assoc-eq :witnesses (fn2-commit-wrong-mutex-order))) '((2 2 2))))
(assert-event (equal (cdr (assoc-eq :witnesses (fn2-commit-held-notification))) '((2 2 2))))
