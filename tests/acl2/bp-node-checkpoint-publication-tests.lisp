(in-package "ACL2")
(include-book "../../books/bp-node-checkpoint-publication")

(defun fn-bpckpt-emit (job fuel)
  (declare (xargs :guard t :measure (nfix fuel) :verify-guards nil))
  (if (or (zp (nfix fuel)) (not (equal (fn-bpn-nth 6 job) :emit))) job
    (fn-bpckpt-emit (car (fn-bpck-emit-step job)) (1- (nfix fuel)))))
(defun fn-bpckpt-control-run (control observations)
  (declare (xargs :guard t))
  (if (atom observations) control
    (fn-bpckpt-control-run (fn-bpck-io-step control (car observations)) (cdr observations))))
(defun fn-bpckpt-publication-run (control observations)
  (declare (xargs :guard t))
  (if (atom observations) control
    (fn-bpckpt-publication-run (fn-bpck-publication-step control (car observations))
                              (cdr observations))))
(defconst *fn-bpckpt-initial*
  (fn-bpck-begin '(:maintenance 0 7 0) 7 1 8 nil nil 0 0 10000))
(defconst *fn-bpckpt-counted* (fn-bpck-census-step *fn-bpckpt-initial* 128))
(defconst *fn-bpckpt-emitting*
  (fn-bpck-stage-granted *fn-bpckpt-counted* '(:grown (:maintenance 0 7 0))))
(defconst *fn-bpckpt-private*
  (fn-bpck-stage-observation (fn-bpckpt-emit *fn-bpckpt-emitting* 128) :created))
(defconst *fn-bpckpt-written-control*
  (fn-bpckpt-control-run (fn-bpck-io-begin *fn-bpckpt-emitting*)
                         '(:ok :prefix-end :ok :trailer-ready :ok :ok :ok)))
(defconst *fn-bpckpt-publication*
  (fn-bpck-publication-begin *fn-bpckpt-private* *fn-bpckpt-written-control*
                             :returned :closed nil nil))
(defconst *fn-bpckpt-final-barrier*
  (fn-bpckpt-publication-run *fn-bpckpt-publication* (make-list 10 :initial-element :ok)))
(defconst *fn-bpckpt-durable*
  (fn-bpck-publication-step *fn-bpckpt-final-barrier* :ok))
(assert-event
 (and (equal *fn-bpckpt-written-control* '(:done :written))
      (equal *fn-bpckpt-publication* '(:directory :pending))
      (not (equal (fn-bpn-nth 0 *fn-bpckpt-final-barrier*) :done))
      (equal (fn-bpck-publication-outcome *fn-bpckpt-durable*) :durable)
      (equal (fn-bpn-nth 0 *fn-bpckpt-final-barrier*) :close-final-root)
      (equal :ok :ok)))
; Omit the nonterminal hypothesis: a reached terminal durable state stays
; durable even on ERROR, but is not the final-root-barrier phase.
(assert-event
 (and (not (not (equal (fn-bpn-nth 0 *fn-bpckpt-durable*) :done)))
      (equal (fn-bpck-publication-outcome
               (fn-bpck-publication-step *fn-bpckpt-durable* :error)) :durable)
      (not (and (equal (fn-bpn-nth 0 *fn-bpckpt-durable*) :close-final-root)
                (equal :error :ok)))))
; Omit durable-result hypothesis on a reached first publication turn.
(assert-event
 (and (not (equal (fn-bpn-nth 0 *fn-bpckpt-publication*) :done))
      (not (equal (fn-bpck-publication-outcome
                    (fn-bpck-publication-step *fn-bpckpt-publication* :ok)) :durable))
      (not (and (equal (fn-bpn-nth 0 *fn-bpckpt-publication*) :close-final-root)
                (equal :ok :ok)))))
(assert-event
 (let ((uncertain (fn-bpck-publication-step *fn-bpckpt-final-barrier* :error)))
   (and (equal uncertain '(:done :uncertain))
        (equal (fn-bpck-publication-step uncertain :ok) uncertain))))
(assert-event
 (and (not (equal *fn-bpckpt-final-barrier* '(:done :uncertain)))
      (not (equal (fn-bpck-publication-step *fn-bpckpt-final-barrier* :ok)
                  *fn-bpckpt-final-barrier*))))
(assert-event
 (let ((answer (fn-bpck-publication-observe *fn-bpckpt-private*
                                          *fn-bpckpt-final-barrier* :ok)))
   (and (equal (fn-bpck-publication-outcome (car answer)) :durable)
        (equal (fn-bpn-nth 11 (cadr answer)) :published))))
(assert-event
 (and (equal (fn-bpck-publication-begin *fn-bpckpt-private* *fn-bpckpt-written-control*
                                        :running :closed nil nil) '(:done :uncertain))
      (equal (fn-bpck-publication-begin *fn-bpckpt-private* *fn-bpckpt-written-control*
                                        :returned :uncertain nil nil) '(:done :uncertain))
      (equal (fn-bpck-publication-begin *fn-bpckpt-emitting* *fn-bpckpt-written-control*
                                        :returned :closed nil nil) '(:done :uncertain))
      (equal (fn-bpck-publication-begin *fn-bpckpt-private* '(:done :cancelled)
                                        :returned :closed nil nil) '(:done :uncertain))))

(assert-event
 (and (equal (fn-bpck-publication-begin *fn-bpckpt-private* *fn-bpckpt-written-control*
                                        :returned :closed t nil) '(:done :uncertain))
      (equal (fn-bpck-publication-begin *fn-bpckpt-private* *fn-bpckpt-written-control*
                                        :returned :closed nil t) '(:done :uncertain))))
(assert-event
 (let* ((job *fn-bpckpt-private*) (control *fn-bpckpt-final-barrier*)
        (answer (fn-bpck-publication-observe job control :ok)) (next (cadr answer)))
   (and (equal (fn-bpn-nth 11 job) :private)
        (not (equal (fn-bpn-nth 0 control) :done))
        (equal (fn-bpck-publication-outcome (car answer)) :durable)
        (equal (fn-bpn-nth 0 control) :close-final-root) (equal :ok :ok)
        (equal (fn-bpn-nth 11 next) :published)
        (equal (fn-bpn-nth 1 next) (fn-bpn-nth 1 job))
        (equal (fn-bpn-nth 2 next) (fn-bpn-nth 2 job))
        (equal (fn-bpn-nth 3 next) (fn-bpn-nth 3 job))
        (equal (fn-bpn-nth 5 next) (fn-bpn-nth 5 job)))))
; Corrupted job stage: every other retained antecedent holds.
(assert-event
 (let* ((job (fn-bpck-stage-observation *fn-bpckpt-private* :deleted))
        (control *fn-bpckpt-final-barrier*)
        (answer (fn-bpck-publication-observe job control :ok)))
   (and (not (equal (fn-bpn-nth 11 job) :private))
        (not (equal (fn-bpn-nth 0 control) :done))
        (equal (fn-bpck-publication-outcome (car answer)) :durable)
        (not (equal (fn-bpn-nth 11 (cadr answer)) :published)))))
; Corrupted coupled state: old writer job paired with already terminal control.
(assert-event
 (let* ((job *fn-bpckpt-private*) (control *fn-bpckpt-durable*)
        (answer (fn-bpck-publication-observe job control :error)))
   (and (equal (fn-bpn-nth 11 job) :private)
        (not (not (equal (fn-bpn-nth 0 control) :done)))
        (equal (fn-bpck-publication-outcome (car answer)) :durable)
        (not (equal (fn-bpn-nth 0 control) :close-final-root)))))
(assert-event
 (let* ((job *fn-bpckpt-private*) (control *fn-bpckpt-publication*)
        (answer (fn-bpck-publication-observe job control :ok)))
   (and (equal (fn-bpn-nth 11 job) :private)
        (not (equal (fn-bpn-nth 0 control) :done))
        (not (equal (fn-bpck-publication-outcome (car answer)) :durable))
        (not (equal (fn-bpn-nth 0 control) :close-final-root)))))
(assert-event
 (and (equal (fn-bpck-publication-action '(:done :uncertain) :open) :close)
      (equal (fn-bpck-publication-action '(:done :uncertain) :closed) :done)
      (equal (fn-bpck-publication-action '(:done :uncertain) :uncertain) :done)
      (equal (fn-bpck-publication-action '(:open-generation :pending) :open) :fence)))

; Cancellation cannot replace a running source's retained job/control.
(assert-event
 (let ((control '(:open-generation :pending)) (job *fn-bpckpt-private*))
   (and (not (equal :running :returned))
        (equal (fn-bpck-publication-cancel job control :running) (list control job)))))
(assert-event
 (let* ((control '(:replace :pending)) (job *fn-bpckpt-private*)
        (answer (fn-bpck-publication-cancel job control :returned)))
   (and (equal :returned :returned)
        (not (equal (fn-bpck-publication-cancel job control :returned) (list control job)))
        (equal (car answer) '(:done :cancelled)) (equal (cadr answer) job)
        (equal (fn-bpck-publication-action (car answer) :open) :close)
        (equal (fn-bpck-publication-action (car answer) :uncertain) :done))))
(assert-event
 (let ((answer (fn-bpck-publication-cancel *fn-bpckpt-private* '(:open-final-root :pending) :returned)))
   (and (equal (car answer) '(:done :uncertain))
        (equal (fn-bpn-nth 11 (cadr answer)) :uncertain))))
