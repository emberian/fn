; Preservation and authorization for the host-called outbound BP lifecycle.
(in-package "ACL2")
(include-book "bp-node-machine")

; Reachable machine states never combine an uncertainty fence with an
; outstanding persistence proposal.  A live proposal is for the state's
; current token and is applicable to the exact state it will update after the
; host reports the persistence outcome.
(defun fn-bpn-machine-invariantp (st)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bpn-machine-statep st)
       (<= (fn-bpn-machine-state-next-token st)
           *fn-bpn-machine-max-records*)
       (not (and (fn-bpn-machine-state-fenced st)
                 (fn-bpn-machine-state-pending st)))
       (or (null (fn-bpn-machine-state-pending st))
           (and (< (fn-bpn-machine-state-next-token st)
                   *fn-bpn-machine-max-records*)
                (fn-bpn-record-applicablep
                 st
                 (fn-bpn-pending-record
                  (fn-bpn-machine-state-pending st)))))))

; The native adapter bounds the lifecycle namespace before constructing a
; restart event.  Other event arms validate their operands inside fn-bpn-step.
(defun fn-bpn-machine-eventp (event)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bpn-eventp event)
       (or (not (equal (car event) :restart))
           (and (true-listp (nth 1 event))
                (<= (len (nth 1 event)) *fn-bpn-machine-max-records*)))))

(defthm fn-bpn-machine-statep-components
  (implies
   (fn-bpn-machine-statep st)
   (and (fn-bpn-configp (fn-bpn-machine-state-config st))
        (fn-bpn-job-listp (fn-bpn-machine-state-jobs st))
        (fn-bpn-contact-listp (fn-bpn-machine-state-contacts st))
        (fn-bpn-maybe-pendingp (fn-bpn-machine-state-pending st))
        (fn-bpn-machine-boolp (fn-bpn-machine-state-fenced st))
        (fn-bpn-machine-u64p (fn-bpn-machine-state-next-token st))
        (fn-bpn-machine-limitp (fn-bpn-machine-state-max-jobs st))
        (fn-bpn-machine-limitp (fn-bpn-machine-state-max-octets st))
        (<= (len (fn-bpn-machine-state-jobs st))
            (fn-bpn-machine-state-max-jobs st))
        (<= (fn-bpn-jobs-octets (fn-bpn-machine-state-jobs st))
            (fn-bpn-machine-state-max-octets st))))
  :hints (("Goal"
           :in-theory (e/d (fn-bpn-machine-statep)
                           (fn-bpn-configp fn-bpn-job-listp
                            fn-bpn-contact-listp fn-bpn-maybe-pendingp
                            fn-bpn-machine-boolp fn-bpn-machine-u64p
                            fn-bpn-machine-limitp))))
  :rule-classes :forward-chaining)

(defthm fn-bpn-machine-recordp-of-constructor
  (equal
   (fn-bpn-machine-recordp
    (fn-bpn-make-machine-state config jobs contacts pending fenced
                               next-token max-jobs max-octets))
   (and (fn-bpn-configp config)
        (fn-bpn-job-listp jobs)
        (fn-bpn-contact-listp contacts)
        (fn-bpn-maybe-pendingp pending)
        (fn-bpn-machine-boolp fenced)
        (fn-bpn-machine-u64p next-token)
        (fn-bpn-machine-limitp max-jobs)
        (fn-bpn-machine-limitp max-octets))))

(defthm fn-bpn-machine-constructor-accessors
  (let ((st (fn-bpn-make-machine-state config jobs contacts pending fenced
                                        next-token max-jobs max-octets)))
    (and (equal (fn-bpn-machine-state-config st) config)
         (equal (fn-bpn-machine-state-jobs st) jobs)
         (equal (fn-bpn-machine-state-contacts st) contacts)
         (equal (fn-bpn-machine-state-pending st) pending)
         (equal (fn-bpn-machine-state-fenced st) fenced)
         (equal (fn-bpn-machine-state-next-token st) next-token)
         (equal (fn-bpn-machine-state-max-jobs st) max-jobs)
         (equal (fn-bpn-machine-state-max-octets st) max-octets))))

(defthm fn-bpn-machine-statep-of-state-with
  (implies
   (and (fn-bpn-machine-statep st)
        (fn-bpn-job-listp jobs)
        (fn-bpn-contact-listp contacts)
        (fn-bpn-maybe-pendingp pending)
        (fn-bpn-machine-boolp fenced)
        (fn-bpn-machine-u64p next-token)
        (<= (len jobs) (fn-bpn-machine-state-max-jobs st))
        (<= (fn-bpn-jobs-octets jobs)
            (fn-bpn-machine-state-max-octets st))
        (or (null pending)
            (equal (fn-bpn-pending-token pending) next-token)))
   (fn-bpn-machine-statep
    (fn-bpn-state-with st jobs contacts pending fenced next-token)))
  :hints (("Goal"
           :use ((:instance fn-bpn-machine-statep-components))
           :in-theory
           (union-theories
            '(fn-bpn-state-with fn-bpn-machine-statep
              fn-bpn-machine-recordp-of-constructor
              fn-bpn-machine-constructor-accessors)
            (theory 'minimal-theory)))))

(defthm fn-bpn-contact-step-is-noop-while-fenced
  (implies (fn-bpn-machine-state-fenced st)
           (equal (fn-bpn-contact-step st peer openp)
                  (fn-bpn-answer st nil)))
  :hints (("Goal" :in-theory (enable fn-bpn-contact-step))))

(defthm fn-bpn-contact-step-is-noop-while-pending
  (implies (fn-bpn-machine-state-pending st)
           (equal (fn-bpn-contact-step st peer openp)
                  (fn-bpn-answer st nil)))
  :hints (("Goal" :in-theory (enable fn-bpn-contact-step))))

(defthm fn-bpn-job-with-status-is-a-job
  (implies (and (fn-bpn-jobp job)
                (fn-bpn-job-statusp status)
                (fn-bpn-machine-u64p token))
           (fn-bpn-jobp (fn-bpn-job-with-status job status token)))
  :hints (("Goal"
           :in-theory (enable fn-bpn-job-with-status fn-bpn-jobp))))

(defthm fn-bpn-nth-is-nth-on-true-lists
  (implies (and (natp n) (true-listp values))
           (equal (fn-bpn-nth n values)
                  (nth n values)))
  :hints (("Goal"
           :induct (fn-bpn-nth n values)
           :in-theory (enable fn-bpn-nth nth))))

(defthm fn-bpn-job-key-of-job-with-status
  (equal (fn-bpn-job-key (fn-bpn-job-with-status job status token))
         (fn-bpn-job-key job))
  :hints (("Goal"
           :in-theory (enable fn-bpn-job-with-status fn-bpn-job-key))))

(defthm fn-bpn-job-wire-of-job-with-status
  (equal (fn-bpn-job-wire (fn-bpn-job-with-status job status token))
         (fn-bpn-job-wire job))
  :hints (("Goal" :in-theory (enable fn-bpn-job-with-status))))

(defthm fn-bpn-find-job-of-append
  (implies
   (fn-bpn-job-listp left)
   (equal (fn-bpn-find-job key (fn-bpn-append left right))
          (if (fn-bpn-find-job key left)
              (fn-bpn-find-job key left)
            (fn-bpn-find-job key right))))
  :hints (("Goal"
           :induct (fn-bpn-append left right)
           :in-theory (enable fn-bpn-append fn-bpn-find-job
                              fn-bpn-job-listp fn-bpn-jobp))))

(defthm fn-bpn-job-listp-of-append-new-job
  (implies (and (fn-bpn-job-listp jobs)
                (fn-bpn-jobp job)
                (not (fn-bpn-job-key-memberp (fn-bpn-job-key job) jobs)))
           (fn-bpn-job-listp (fn-bpn-append jobs (list job))))
  :hints (("Goal"
           :induct (fn-bpn-append jobs (list job))
           :in-theory (e/d (fn-bpn-append fn-bpn-job-listp
                                           fn-bpn-job-key-memberp
                                           fn-bpn-find-job)
                           (fn-bpn-jobp fn-bpn-job-key)))))

(defthm fn-bpn-len-of-append-one
  (equal (len (fn-bpn-append jobs (list job)))
         (+ 1 (len jobs)))
  :hints (("Goal"
           :induct (fn-bpn-append jobs (list job))
           :in-theory (enable fn-bpn-append))))

(defthm fn-bpn-jobs-octets-of-append-one
  (equal (fn-bpn-jobs-octets (fn-bpn-append jobs (list job)))
         (+ (fn-bpn-jobs-octets jobs)
            (len (fn-bpn-job-wire job))))
  :hints (("Goal"
           :induct (fn-bpn-append jobs (list job))
           :in-theory (enable fn-bpn-append fn-bpn-jobs-octets))))

(defthm fn-bpn-find-job-of-replace-other-key
  (implies (and (not (equal sought key))
                (equal (fn-bpn-job-key replacement) key))
           (equal (fn-bpn-find-job
                   sought (fn-bpn-replace-job key replacement jobs))
                  (fn-bpn-find-job sought jobs)))
  :hints (("Goal"
           :induct (fn-bpn-replace-job key replacement jobs)
           :in-theory (enable fn-bpn-replace-job fn-bpn-find-job))))

(defthm fn-bpn-find-job-is-a-job
  (implies (and (fn-bpn-job-listp jobs)
                (fn-bpn-find-job key jobs))
           (fn-bpn-jobp (fn-bpn-find-job key jobs)))
  :hints (("Goal"
           :induct (fn-bpn-find-job key jobs)
           :in-theory (enable fn-bpn-job-listp fn-bpn-find-job))))

(defthm fn-bpn-key-of-found-job
  (implies (and (fn-bpn-job-listp jobs)
                (fn-bpn-find-job key jobs))
           (equal (fn-bpn-job-key (fn-bpn-find-job key jobs)) key))
  :hints (("Goal"
           :induct (fn-bpn-find-job key jobs)
           :in-theory (enable fn-bpn-job-listp fn-bpn-find-job))))

(defthm fn-bpn-replace-job-preserves-job-listp
  (implies (and (fn-bpn-job-listp jobs)
                (fn-bpn-jobp replacement)
                (equal (fn-bpn-job-key replacement) key))
           (fn-bpn-job-listp (fn-bpn-replace-job key replacement jobs)))
  :hints (("Goal"
           :induct (fn-bpn-replace-job key replacement jobs)
           :in-theory (e/d (fn-bpn-replace-job fn-bpn-job-listp
                                               fn-bpn-job-key-memberp
                                               fn-bpn-find-job)
                           (fn-bpn-jobp fn-bpn-job-key)))))

(defthm fn-bpn-len-of-replace-job
  (equal (len (fn-bpn-replace-job key replacement jobs))
         (len jobs))
  :hints (("Goal"
           :induct (fn-bpn-replace-job key replacement jobs)
           :in-theory (enable fn-bpn-replace-job))))

(defthm fn-bpn-jobs-octets-of-status-replacement
  (equal (fn-bpn-jobs-octets
          (fn-bpn-replace-job
           key
           (fn-bpn-job-with-status (fn-bpn-find-job key jobs) status token)
           jobs))
         (fn-bpn-jobs-octets jobs))
  :hints (("Goal"
           :induct (fn-bpn-replace-job
                    key
                    (fn-bpn-job-with-status (fn-bpn-find-job key jobs)
                                            status token)
                    jobs)
           :in-theory (enable fn-bpn-replace-job fn-bpn-jobs-octets
                              fn-bpn-find-job))))

(defthm fn-bpn-status-replacement-preserves-job-listp
  (implies (and (fn-bpn-job-listp jobs)
                (fn-bpn-find-job key jobs)
                (fn-bpn-job-statusp status)
                (fn-bpn-machine-u64p token))
           (fn-bpn-job-listp
            (fn-bpn-replace-job
             key
             (fn-bpn-job-with-status (fn-bpn-find-job key jobs)
                                     status token)
             jobs)))
  :hints (("Goal"
           :use ((:instance fn-bpn-replace-job-preserves-job-listp
                            (replacement
                             (fn-bpn-job-with-status
                              (fn-bpn-find-job key jobs) status token)))
                 (:instance fn-bpn-job-with-status-is-a-job
                            (job (fn-bpn-find-job key jobs))))
           :in-theory
           (union-theories
            '(fn-bpn-find-job-is-a-job fn-bpn-key-of-found-job
              fn-bpn-job-key-of-job-with-status)
            (theory 'minimal-theory)))))

(defthm fn-bpn-queued-update-preserves-machine-statep
  (implies
   (and (fn-bpn-machine-statep st)
        (< (fn-bpn-machine-state-next-token st)
           *fn-bpn-machine-max-records*)
        (fn-bpn-jobp job)
        (not (fn-bpn-job-key-memberp (fn-bpn-job-key job)
                                     (fn-bpn-machine-state-jobs st)))
        (< (len (fn-bpn-machine-state-jobs st))
           (fn-bpn-machine-state-max-jobs st))
        (<= (+ (fn-bpn-jobs-octets (fn-bpn-machine-state-jobs st))
               (len (fn-bpn-job-wire job)))
            (fn-bpn-machine-state-max-octets st)))
   (fn-bpn-machine-statep
    (fn-bpn-state-with
     st
     (fn-bpn-append (fn-bpn-machine-state-jobs st) (list job))
     (fn-bpn-machine-state-contacts st)
     nil nil (1+ (fn-bpn-machine-state-next-token st)))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-statep-components)
          (:instance fn-bpn-job-listp-of-append-new-job
                     (jobs (fn-bpn-machine-state-jobs st)))
          (:instance fn-bpn-machine-statep-of-state-with
                     (jobs (fn-bpn-append
                            (fn-bpn-machine-state-jobs st) (list job)))
                     (contacts (fn-bpn-machine-state-contacts st))
                     (pending nil) (fenced nil)
                     (next-token
                      (1+ (fn-bpn-machine-state-next-token st)))))
    :in-theory
    (union-theories
     '(fn-bpn-len-of-append-one fn-bpn-jobs-octets-of-append-one
       fn-bpn-machine-u64p fn-bpn-maybe-pendingp fn-bpn-machine-boolp
       fn-bpn-machine-limitp natp posp
       (:type-prescription len) (:type-prescription fn-bpn-jobs-octets))
     (theory 'minimal-theory)))))

(defthm fn-bpn-status-update-preserves-machine-statep
  (implies
   (and (fn-bpn-machine-statep st)
        (< (fn-bpn-machine-state-next-token st)
           *fn-bpn-machine-max-records*)
        (fn-bpn-find-job key (fn-bpn-machine-state-jobs st))
        (fn-bpn-job-statusp status))
   (fn-bpn-machine-statep
    (fn-bpn-state-with
     st
     (fn-bpn-replace-job
      key
      (fn-bpn-job-with-status
       (fn-bpn-find-job key (fn-bpn-machine-state-jobs st))
       status (fn-bpn-machine-state-next-token st))
      (fn-bpn-machine-state-jobs st))
     (fn-bpn-machine-state-contacts st)
     nil nil (1+ (fn-bpn-machine-state-next-token st)))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-statep-components)
          (:instance fn-bpn-status-replacement-preserves-job-listp
                     (jobs (fn-bpn-machine-state-jobs st))
                     (token (fn-bpn-machine-state-next-token st)))
          (:instance fn-bpn-machine-statep-of-state-with
                     (jobs
                      (fn-bpn-replace-job
                       key
                       (fn-bpn-job-with-status
                        (fn-bpn-find-job key (fn-bpn-machine-state-jobs st))
                        status (fn-bpn-machine-state-next-token st))
                       (fn-bpn-machine-state-jobs st)))
                     (contacts (fn-bpn-machine-state-contacts st))
                     (pending nil) (fenced nil)
                     (next-token
                      (1+ (fn-bpn-machine-state-next-token st)))))
    :in-theory
    (union-theories
     '(fn-bpn-len-of-replace-job
       fn-bpn-jobs-octets-of-status-replacement
       fn-bpn-machine-u64p fn-bpn-maybe-pendingp fn-bpn-machine-boolp
       fn-bpn-machine-limitp natp posp
       (:type-prescription len) (:type-prescription fn-bpn-jobs-octets))
     (theory 'minimal-theory)))))

(defthm fn-bpn-apply-record-preserves-machine-statep
  (implies (and (fn-bpn-machine-statep st)
                (< (fn-bpn-machine-state-next-token st)
                   *fn-bpn-machine-max-records*)
                (fn-bpn-record-applicablep st record))
           (fn-bpn-machine-statep (fn-bpn-apply-record st record)))
  :hints (("Goal"
           :use ((:instance fn-bpn-machine-statep-components))
           :in-theory
           (union-theories
            '(fn-bpn-apply-record fn-bpn-record-applicablep
              fn-bpn-lifecycle-recordp fn-bpn-record-key fn-bpn-record-token
              fn-bpn-nth fn-bpn-nth-is-nth-on-true-lists
              fn-bpn-job-key-memberp
              fn-bpn-queued-update-preserves-machine-statep
              fn-bpn-status-update-preserves-machine-statep
              fn-bpn-job-statusp fn-bpn-machine-u64p fn-bpn-member
              fn-bpn-maybe-pendingp fn-bpn-machine-boolp
              fn-bpn-machine-limitp natp posp)
            (theory 'minimal-theory)))))

(defthm fn-bpn-step-effects-are-typed
  (implies (fn-bpn-machine-invariantp st)
           (fn-bpn-effect-listp
            (fn-bpn-answer-effects (fn-bpn-step st event)))))

(defthm fn-bpn-step-preserves-machine-invariant
  (implies (fn-bpn-machine-invariantp st)
           (fn-bpn-machine-invariantp
            (fn-bpn-answer-state (fn-bpn-step st event)))))
