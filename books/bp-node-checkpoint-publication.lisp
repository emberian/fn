; Bounded publication after the private checkpoint writer has returned and
; closed its barriered source. Actual indexed grant/fence installation is a
; separate prerequisite; this controller creates no resource authority.
(in-package "ACL2")
(include-book "bp-node-checkpoint-job")

(defun fn-bpck-publication-begin (job control source fd prior-failure prior-core-failure)
  (declare (xargs :guard t))
  (if (and (not prior-failure) (not prior-core-failure)
           (equal control '(:done :written))
           (equal source :returned) (equal fd :closed)
           (equal (fn-bpn-nth 11 job) :private))
      '(:directory :pending)
    '(:done :uncertain)))

(defun fn-bpck-publication-action (control fd-result)
  (declare (xargs :guard t))
  (case (fn-bpn-nth 0 control)
    (:directory (if (equal fd-result :closed) :make-directory :fence))
    (:open-generation (if (equal fd-result :closed) :open-generation :fence))
    (:generation-barrier (if (equal fd-result :open) :barrier :fence))
    (:close-generation (if (equal fd-result :open) :close :fence))
    (:open-initial-root (if (equal fd-result :closed) :open-root :fence))
    (:initial-root-barrier (if (equal fd-result :open) :barrier :fence))
    (:close-initial-root (if (equal fd-result :open) :close :fence))
    (:replace (if (equal fd-result :closed) :replace :fence))
    (:open-final-root (if (equal fd-result :closed) :open-root :fence))
    (:final-root-barrier (if (equal fd-result :open) :barrier :fence))
    (:close-final-root (if (equal fd-result :open) :close :fence))
    (:done (if (and (member-equal (fn-bpn-nth 1 control) '(:uncertain :cancelled))
                    (equal fd-result :open)) :close :done))
    (otherwise :fence)))

(defun fn-bpck-publication-step (control observation)
  (declare (xargs :guard t))
  (let ((phase (fn-bpn-nth 0 control)))
    (cond ((equal phase :done) control)
          ((not (equal observation :ok)) '(:done :uncertain))
          ((equal phase :directory) '(:open-generation :pending))
          ((equal phase :open-generation) '(:generation-barrier :pending))
          ((equal phase :generation-barrier) '(:close-generation :pending))
          ((equal phase :close-generation) '(:open-initial-root :pending))
          ((equal phase :open-initial-root) '(:initial-root-barrier :pending))
          ((equal phase :initial-root-barrier) '(:close-initial-root :pending))
          ((equal phase :close-initial-root) '(:replace :pending))
          ((equal phase :replace) '(:open-final-root :pending))
          ((equal phase :open-final-root) '(:final-root-barrier :pending))
          ((equal phase :final-root-barrier) '(:close-final-root :pending))
          ((equal phase :close-final-root) '(:done :durable))
          (t '(:done :uncertain)))))

(defun fn-bpck-publication-outcome (control)
  (declare (xargs :guard t))
  (if (equal (fn-bpn-nth 0 control) :done)
      (case (fn-bpn-nth 1 control) (:durable :durable) (:cancelled :cancelled)
        (otherwise :uncertain))
    :pending))

(defun fn-bpck-publication-observe (job control observation)
  (declare (xargs :guard t))
  (let ((next (fn-bpck-publication-step control observation)))
    (list next
          (if (equal (fn-bpck-publication-outcome next) :durable)
              (fn-bpck-stage-observation job :published)
            (if (equal (fn-bpck-publication-outcome next) :uncertain)
                (fn-bpck-stage-observation job :ambiguous) job)))))

(defun fn-bpck-publication-cancel (job control source)
  (declare (xargs :guard t))
  (cond ((not (equal source :returned)) (list control job))
        ((equal (fn-bpn-nth 0 control) :done) (list control job))
        ((member-equal (fn-bpn-nth 0 control)
           '(:directory :open-generation :generation-barrier :close-generation
             :open-initial-root :initial-root-barrier :close-initial-root :replace))
         (list '(:done :cancelled) job))
        (t (list '(:done :uncertain) (fn-bpck-stage-observation job :ambiguous)))))

(defthm fn-bpck-publication-cancel-running-keeps-exact-job
  (implies (not (equal source :returned))
           (equal (fn-bpck-publication-cancel job control source) (list control job))))

(defthm fn-bpck-publication-step-durable-requires-final-barrier-close
  (implies (and (not (equal (fn-bpn-nth 0 control) :done))
                (equal (fn-bpck-publication-outcome
                         (fn-bpck-publication-step control observation)) :durable))
           (and (equal (fn-bpn-nth 0 control) :close-final-root)
                (equal observation :ok)))
  :rule-classes nil)

(defthm fn-bpck-publication-step-uncertain-never-becomes-durable
  (implies (equal control '(:done :uncertain))
           (equal (fn-bpck-publication-step control observation) control)))

(defthm fn-bpck-publication-observe-durable-is-final-barrier-close-for-same-job
  (implies (and (equal (fn-bpn-nth 11 job) :private)
                (not (equal (fn-bpn-nth 0 control) :done))
                (equal (fn-bpck-publication-outcome
                         (fn-bpn-nth 0 (fn-bpck-publication-observe job control observation)))
                       :durable))
    (let ((next (fn-bpn-nth 1 (fn-bpck-publication-observe job control observation))))
      (and (equal (fn-bpn-nth 0 control) :close-final-root)
           (equal observation :ok)
           (equal (fn-bpn-nth 11 next) :published)
           (equal (fn-bpn-nth 1 next) (fn-bpn-nth 1 job))
           (equal (fn-bpn-nth 2 next) (fn-bpn-nth 2 job))
           (equal (fn-bpn-nth 3 next) (fn-bpn-nth 3 job))
           (equal (fn-bpn-nth 5 next) (fn-bpn-nth 5 job)))))
  :hints (("Goal" :in-theory
    (enable fn-bpck-publication-observe fn-bpck-publication-step
            fn-bpck-publication-outcome fn-bpck-stage-observation fn-bpck-make fn-bpn-nth)))
  :rule-classes nil)

(in-theory (disable fn-bpck-publication-begin fn-bpck-publication-action
                    fn-bpck-publication-step fn-bpck-publication-outcome
                    fn-bpck-publication-observe fn-bpck-publication-cancel))
