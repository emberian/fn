; Immutable no-replace publication for application journals.
;
; The host executes the requested syscall and reports only its observation.
; This machine owns the phase and the durable/refused/uncertain result. It is
; narrower than the Store publisher: FNWF and FNRJ records never replace an
; authority file and never repair a prefix.
(in-package "ACL2")

(defun fn-jpub-state (phase authorityp outcome)
  (list phase (if authorityp t nil) outcome))

(defun fn-jpub-phase (s) (if (consp s) (car s) nil))
(defun fn-jpub-authorityp (s) (if (consp (cdr s)) (car (cdr s)) nil))
(defun fn-jpub-outcome (s) (if (consp (cdr (cdr s))) (car (cdr (cdr s))) nil))

(defun fn-jpub-phasep (x)
  (member-equal x '(:staging :file-barrier :link-ready :link-attempted
                    :directory-barrier :durable :refused :fenced)))

(defun fn-jpub-outcomep (x)
  (member-equal x '(nil :durable :refused :uncertain)))

(defun fn-jpub-statep (s)
  (and (true-listp s)
       (equal (len s) 3)
       (fn-jpub-phasep (fn-jpub-phase s))
       (booleanp (fn-jpub-authorityp s))
       (fn-jpub-outcomep (fn-jpub-outcome s))
       (if (equal (fn-jpub-phase s) :durable)
           (equal (fn-jpub-outcome s) :durable)
         (if (equal (fn-jpub-phase s) :refused)
             (equal (fn-jpub-outcome s) :refused)
           (if (equal (fn-jpub-phase s) :fenced)
               (equal (fn-jpub-outcome s) :uncertain)
             (equal (fn-jpub-outcome s) nil))))))

(defun fn-jpub-initial (authorityp)
  ; AUTHORITYP means the caller owns the journal lock and established that the
  ; next final name was absent before this publication. Only under that
  ; premise can EEXIST prove that this operation did not publish anything.
  (if authorityp
      (fn-jpub-state :staging t nil)
    (fn-jpub-state :fenced nil :uncertain)))

(defun fn-jpub-terminalp (s)
  (member-equal (fn-jpub-phase s) '(:durable :refused :fenced)))

(defun fn-jpub-next-action (s)
  (case (fn-jpub-phase s)
    (:staging :stage)
    (:file-barrier :file-barrier)
    (:link-ready :begin-link)
    (:link-attempted :link)
    (:directory-barrier :directory-barrier)
    (otherwise :none)))

(defun fn-jpub-step (s event)
  (if (not (fn-jpub-statep s))
      (fn-jpub-state :fenced nil :uncertain)
    (case (fn-jpub-phase s)
      (:staging
       (if (equal event '(:stage-result :ok))
           (fn-jpub-state :file-barrier (fn-jpub-authorityp s) nil)
         (fn-jpub-state :refused (fn-jpub-authorityp s) :refused)))
      (:file-barrier
       (if (equal event '(:file-barrier-result :ok))
           (fn-jpub-state :link-ready (fn-jpub-authorityp s) nil)
         (fn-jpub-state :refused (fn-jpub-authorityp s) :refused)))
      (:link-ready
       ; Move into the ambiguity window before issuing link(2).
       (if (equal event '(:link-begin))
           (fn-jpub-state :link-attempted (fn-jpub-authorityp s) nil)
         (fn-jpub-state :fenced (fn-jpub-authorityp s) :uncertain)))
      (:link-attempted
       (cond ((equal event '(:link-result :ok))
              (fn-jpub-state :directory-barrier (fn-jpub-authorityp s) nil))
             ; With exclusive authority and an absent next name established
             ; before link, EEXIST is a definite conflict, not our publish.
             ((and (equal event '(:link-result :exists))
                   (fn-jpub-authorityp s))
              (fn-jpub-state :refused t :refused))
             (t (fn-jpub-state :fenced (fn-jpub-authorityp s) :uncertain))))
      (:directory-barrier
       (if (equal event '(:directory-barrier-result :ok))
           (fn-jpub-state :durable (fn-jpub-authorityp s) :durable)
         ; A visible final name after a failed namespace barrier is evidence,
         ; never proof that the operation is durable.
         (fn-jpub-state :fenced (fn-jpub-authorityp s) :uncertain)))
      (otherwise s))))

(defun fn-jpub-crash-outcome (s)
  (case (fn-jpub-phase s)
    (:durable :durable)
    (:refused :refused)
    ((:staging :file-barrier :link-ready) :refused)
    (otherwise :uncertain)))

(defthm fn-jpub-statep-of-initial
  (fn-jpub-statep (fn-jpub-initial authorityp)))

(defthm fn-jpub-step-preserves-statep
  (implies (fn-jpub-statep s)
           (fn-jpub-statep (fn-jpub-step s event))))

(defthm fn-jpub-durable-only-after-directory-barrier
  (implies (and (fn-jpub-statep s)
                (equal (fn-jpub-outcome s) nil)
                (equal (fn-jpub-outcome (fn-jpub-step s event)) :durable))
           (and (equal (fn-jpub-phase s) :directory-barrier)
                (equal event '(:directory-barrier-result :ok))))
  :rule-classes nil)

(defthm fn-jpub-error-after-link-begin-is-uncertain
  (implies (and (fn-jpub-statep s)
                (equal (fn-jpub-phase s) :link-attempted)
                (not (member-equal event
                                   '((:link-result :ok)
                                     (:link-result :exists)))))
           (equal (fn-jpub-outcome (fn-jpub-step s event)) :uncertain)))

(defthm fn-jpub-eexist-refusal-requires-authority
  (implies (and (fn-jpub-statep s)
                (equal (fn-jpub-phase s) :link-attempted)
                (equal (fn-jpub-outcome
                        (fn-jpub-step s '(:link-result :exists)))
                       :refused))
           (fn-jpub-authorityp s)))

(deftheory fn-journal-publish-vocabulary
  '(fn-jpub-state fn-jpub-phase fn-jpub-authorityp fn-jpub-outcome
    fn-jpub-phasep fn-jpub-outcomep fn-jpub-statep fn-jpub-initial
    fn-jpub-terminalp fn-jpub-next-action fn-jpub-step fn-jpub-crash-outcome))
(in-theory (disable fn-journal-publish-vocabulary))
