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
           (< (fn-bpn-machine-state-next-token st)
              *fn-bpn-machine-max-records*))))

(defthm fn-bpn-state-with-accessors
  (let ((next (fn-bpn-state-with st jobs contacts pending fenced next-token)))
    (and (equal (fn-bpn-machine-state-config next)
                (fn-bpn-machine-state-config st))
         (equal (fn-bpn-machine-state-jobs next) jobs)
         (equal (fn-bpn-machine-state-contacts next) contacts)
         (equal (fn-bpn-machine-state-pending next) pending)
         (equal (fn-bpn-machine-state-fenced next) fenced)
         (equal (fn-bpn-machine-state-next-token next) next-token)
         (equal (fn-bpn-machine-state-max-jobs next)
                (fn-bpn-machine-state-max-jobs st))
         (equal (fn-bpn-machine-state-max-octets next)
                (fn-bpn-machine-state-max-octets st))))
  :hints (("Goal" :in-theory (enable fn-bpn-state-with))))

(defthm fn-bpn-pendingp-of-constructor
  (equal
   (fn-bpn-pendingp
    (fn-bpn-make-pending token record success refusal uncertain))
   (and (fn-bpn-machine-u64p token)
        (fn-bpn-lifecycle-recordp record)
        (fn-bpn-effect-listp success)
        (fn-bpn-effectp refusal)
        (fn-bpn-effectp uncertain))))

(defthm fn-bpn-pending-constructor-accessors
  (let ((pending (fn-bpn-make-pending token record success refusal uncertain)))
    (and (equal (fn-bpn-pending-token pending) token)
         (equal (fn-bpn-pending-record pending) record)
         (equal (fn-bpn-pending-success-effects pending) success)
         (equal (fn-bpn-pending-refusal-effect pending) refusal)
         (equal (fn-bpn-pending-uncertainty-effect pending) uncertain))))

(defthm fn-bpn-answer-constructor-accessors
  (and (equal (fn-bpn-answer-state (fn-bpn-answer st effects)) st)
       (equal (fn-bpn-answer-effects (fn-bpn-answer st effects)) effects)))

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
  ;; The field predicates stay closed: each field of the result is the
  ;; job's own field or an argument, so the hypotheses supply them as
  ;; literals.  Opened, they cost 2.9 s.
  :hints (("Goal"
           :in-theory (e/d (fn-bpn-job-with-status fn-bpn-jobp)
                           (fn-bpn-machine-textp fn-bpn-machine-u64p
                            fn-bpp-timep fn-clock-age-anchorp fn-bpp-eidp
                            fn-bpn-routep fn-bpb-bundlep fn-cbor-octet-listp
                            fn-bpn-job-statusp)))))

(defthm fn-bpn-jobp-of-constructor
  (equal
   (fn-bpn-jobp
    (fn-bpn-make-job work attempt generation sequence age peer route
                     bundle wire status token))
   (and (fn-bpn-machine-textp work)
        (fn-bpn-machine-textp attempt)
        (fn-bpn-machine-u64p generation)
        (fn-bpp-timep sequence)
        (fn-clock-age-anchorp age)
        (fn-bpp-eidp peer)
        (fn-bpn-routep route)
        (fn-bpb-bundlep bundle)
        (fn-cbor-octet-listp wire)
        (fn-bpn-job-statusp status)
        (fn-bpn-machine-u64p token))))

(defthm fn-bpn-jobp-components
  (implies
   (fn-bpn-jobp job)
   (and (fn-bpn-machine-textp (fn-bpn-job-work-id job))
        (fn-bpn-machine-textp (fn-bpn-job-attempt-id job))
        (fn-bpn-machine-u64p (fn-bpn-job-generation job))
        (fn-bpp-timep (fn-bpn-job-sequence job))
        (fn-clock-age-anchorp (fn-bpn-job-age-anchor job))
        (fn-bpp-eidp (fn-bpn-job-peer job))
        (fn-bpn-routep (fn-bpn-job-route job))
        (fn-bpb-bundlep (fn-bpn-job-bundle job))
        (fn-cbor-octet-listp (fn-bpn-job-wire job))
        (fn-bpn-job-statusp (fn-bpn-job-status job))
        (fn-bpn-machine-u64p (fn-bpn-job-last-token job))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpn-jobp)
                (fn-bpn-machine-textp fn-bpn-machine-u64p
                 fn-bpp-timep fn-clock-age-anchorp fn-bpp-eidp
                 fn-bpn-routep fn-bpb-bundlep fn-cbor-octet-listp
                 fn-bpn-job-statusp))))
  :rule-classes :forward-chaining)

(defthm fn-bpn-primary-encode-is-an-octet-list
  (fn-cbor-octet-listp (fn-bpp-encode primary))
  :hints (("Goal"
           :use ((:instance fn-bpc-enc-are-octets
                            (flg :item)
                            (x (fn-bpp-block-value
                                primary (fn-bpp-block-crc primary)))))
           :in-theory
           (union-theories '(fn-bpp-encode fn-bpc-enc-are-octets)
                           (theory 'minimal-theory)))))

(defthm fn-bpb-encode-is-an-octet-list
  (implies (fn-bpb-bundlep bundle)
           (fn-cbor-octet-listp (fn-bpb-encode bundle)))
  :hints (("Goal"
           :use ((:instance fn-bpn-primary-encode-is-an-octet-list
                            (primary (fn-bpb-bundle-primary bundle)))
                 (:instance fn-bpb-encode-blocks-are-octets
                            (xs (fn-bpb-bundle-blocks bundle)))
                 (:instance fn-bpb-encode-block-are-octets
                            (b (fn-bpb-bundle-payload bundle))))
           ;; The primary block's recognizer stays closed: the instances
           ;; need only the three field facts `fn-bpb-bundlep' states, and
           ;; opened, `fn-bpp-blockp' split the goal 108 ways over its CRC,
           ;; EID and time fields, 16.9 s
           ;; (planning/evidence/misc-books-cost-2026-09-23.md).
           :in-theory (e/d (fn-bpb-encode fn-bpb-bundlep)
                           (fn-bpp-encode fn-bpb-encode-blocks
                            fn-bpb-encode-block fn-bpb-blockp
                            fn-bpb-block-listp fn-bpb-payload-blockp
                            fn-bpb-splitp fn-bpp-blockp)))))

(defthm fn-bpn-send-bundle-destination
  (equal
   (fn-bpp-destination
    (fn-bpb-bundle-primary
     (fn-bpn-send-bundle config peer adu sequence obs)))
   peer)
  :hints (("Goal" :in-theory (enable fn-bpn-send-bundle))))

(defthm fn-bpn-send-bundle-anchor-is-typed
  (implies (fn-clock-observationp obs)
           (fn-clock-age-anchorp
            (fn-bpn-anchor-of
             (fn-bpn-send-bundle config peer adu sequence obs) obs)))
  ;; The anchor is either nil or the bundle's age, tested to be a time,
  ;; paired with the observation's monotonic reading; which age the sent
  ;; bundle carries does not matter.  Opening the bundle and decoding its
  ;; age block cost 1.2 s and 470 k steps; closed, 551 steps.
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpn-anchor-of fn-clock-age-anchorp
                 fn-clock-observationp fn-clock-timep)
                (fn-bpn-send-bundle fn-bpb-bundle-age)))))

(defthm fn-bpn-keyp-of-list
  (equal (fn-bpn-keyp (list work attempt generation))
         (and (fn-bpn-machine-textp work)
              (fn-bpn-machine-textp attempt)
              (fn-bpn-machine-u64p generation)))
  :hints (("Goal" :in-theory (enable fn-bpn-keyp len nth zp))))

(defthm fn-bpn-enqueue-record-is-typed
  (implies
   (and (fn-bpn-configp config)
        (fn-bpn-keyp (list work attempt generation))
        (fn-bpp-timep sequence)
        (fn-bpn-routep route)
        (fn-bpp-eidp peer)
        (fn-bpb-datap adu)
        (fn-clock-observationp obs)
        (fn-bpn-machine-u64p token)
        (<= (len (fn-bpn-send config peer adu sequence obs))
            *fn-bpn-machine-max-job-octets*))
   (fn-bpn-lifecycle-recordp
    (list
     :queued token
     (fn-bpn-make-job
      work attempt generation sequence
      (fn-bpn-anchor-of
       (fn-bpn-send-bundle config peer adu sequence obs) obs)
      peer route
      (fn-bpn-send-bundle config peer adu sequence obs)
      (fn-bpn-send config peer adu sequence obs)
      :queued token))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-send-bundle-is-a-bundle)
          (:instance fn-bpn-send-bundle-anchor-is-typed)
          (:instance fn-bpb-encode-is-an-octet-list
                     (bundle (fn-bpn-send-bundle
                              config peer adu sequence obs))))
    :in-theory
    (union-theories
     '(fn-bpn-lifecycle-recordp fn-bpn-jobp-of-constructor
       fn-bpn-keyp-of-list fn-bpn-machine-textp fn-bpn-send
       fn-bpn-send-bundle-destination fn-bpn-job-statusp
       fn-bpn-member fn-bpn-nth fn-bpn-machine-u64p natp
       fn-cbor-ag-car car-cons cdr-cons true-listp len nth zp
       fn-bpn-job-status-of-fn-bpn-make-job
       fn-bpn-job-last-token-of-fn-bpn-make-job
       fn-bpn-job-wire-of-fn-bpn-make-job
       fn-bpn-job-peer-of-fn-bpn-make-job
       fn-bpn-job-bundle-of-fn-bpn-make-job
       (:type-prescription len))
     (theory 'minimal-theory)))))

(defthm fn-bpn-attempting-record-is-typed
  (implies (and (fn-bpn-jobp job)
                (fn-bpn-machine-u64p token))
           (fn-bpn-lifecycle-recordp
            (list :attempting token
                  (fn-bpn-job-work-id job)
                  (fn-bpn-job-attempt-id job)
                  (fn-bpn-job-generation job))))
  :hints (("Goal"
           :use ((:instance fn-bpn-jobp-components))
           :in-theory
           (e/d (fn-bpn-lifecycle-recordp fn-bpn-record-key
                  fn-bpn-record-token fn-bpn-nth)
                (fn-bpn-jobp)))))

(defthm fn-bpn-terminal-record-is-typed
  (implies
   (and (fn-bpn-keyp key)
        (fn-bpn-machine-u64p token)
        (fn-bpn-member kind '(:requeued :finished :expired))
        (if (equal kind :requeued)
            (fn-bpn-member reason '(:refused :failed :uncertain))
          (equal reason :none)))
   (fn-bpn-lifecycle-recordp
    (list kind token (nth 0 key) (nth 1 key) (nth 2 key) reason kind)))
  :hints (("Goal"
           :in-theory
           (enable fn-bpn-lifecycle-recordp fn-bpn-keyp
                   fn-bpn-machine-textp fn-bpn-machine-u64p
                   fn-bpn-member fn-bpn-nth))))

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

(defthm fn-bpn-job-key-is-typed
  (implies (fn-bpn-jobp job)
           (fn-bpn-keyp (fn-bpn-job-key job)))
  :hints (("Goal"
           :in-theory (enable fn-bpn-jobp fn-bpn-job-key fn-bpn-keyp
                              fn-bpn-machine-textp fn-bpn-machine-u64p))))

(defthm fn-bpn-job-key-accessors
  (and (equal (nth 0 (fn-bpn-job-key job)) (fn-bpn-job-work-id job))
       (equal (nth 1 (fn-bpn-job-key job)) (fn-bpn-job-attempt-id job))
       (equal (nth 2 (fn-bpn-job-key job)) (fn-bpn-job-generation job)))
  :hints (("Goal" :in-theory (enable fn-bpn-job-key))))

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
  ;; The job recognizer stays closed: the step needs `(fn-bpn-jobp (car
  ;; jobs))' as `fn-bpn-job-listp' states it.  Opened, its eleven field
  ;; predicates split the induction step 64 ways, 14.2 s
  ;; (planning/evidence/misc-books-cost-2026-09-23.md).
  :hints (("Goal"
           :induct (fn-bpn-find-job key jobs)
           :in-theory (e/d (fn-bpn-job-listp fn-bpn-find-job)
                           (fn-bpn-jobp fn-bpn-job-key-memberp)))))

(defthm fn-bpn-find-queued-for-peer-is-a-job
  (implies (and (fn-bpn-job-listp jobs)
                (fn-bpn-find-queued-for-peer peer jobs))
           (and (fn-bpn-jobp (fn-bpn-find-queued-for-peer peer jobs))
                (equal (fn-bpn-job-status
                        (fn-bpn-find-queued-for-peer peer jobs))
                       :queued)))
  :hints (("Goal"
           :induct (fn-bpn-find-queued-for-peer peer jobs)
           :in-theory
           (e/d (fn-bpn-find-queued-for-peer fn-bpn-job-listp)
                (fn-bpn-jobp)))))

(defthm fn-bpn-find-expired-is-a-job
  (implies (and (fn-bpn-job-listp jobs)
                (fn-bpn-find-expired jobs obs))
           (fn-bpn-jobp (fn-bpn-find-expired jobs obs)))
  :hints (("Goal"
           :induct (fn-bpn-find-expired jobs obs)
           :in-theory
           (e/d (fn-bpn-find-expired fn-bpn-job-listp)
                (fn-bpn-jobp)))))

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

(defthm fn-bpn-contact-state-with-preserves-machine-invariant
  (implies
   (and (fn-bpn-machine-invariantp st)
        (fn-bpn-contact-listp contacts))
   (fn-bpn-machine-invariantp
    (fn-bpn-state-with
     st (fn-bpn-machine-state-jobs st) contacts
     (fn-bpn-machine-state-pending st)
     (fn-bpn-machine-state-fenced st)
     (fn-bpn-machine-state-next-token st))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-statep-components)
          (:instance fn-bpn-machine-statep-of-state-with
                     (jobs (fn-bpn-machine-state-jobs st))
                     (pending (fn-bpn-machine-state-pending st))
                     (fenced (fn-bpn-machine-state-fenced st))
                     (next-token (fn-bpn-machine-state-next-token st))))
    :in-theory
    (union-theories
     '(fn-bpn-machine-invariantp fn-bpn-state-with-accessors)
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

(defthm fn-bpn-machine-invariant-components
  (implies
   (fn-bpn-machine-invariantp st)
   (and (fn-bpn-machine-statep st)
        (<= (fn-bpn-machine-state-next-token st)
            *fn-bpn-machine-max-records*)
        (not (and (fn-bpn-machine-state-fenced st)
                  (fn-bpn-machine-state-pending st)))
        (or (null (fn-bpn-machine-state-pending st))
            (< (fn-bpn-machine-state-next-token st)
               *fn-bpn-machine-max-records*))))
  :hints (("Goal"
           :in-theory
           (union-theories '(fn-bpn-machine-invariantp)
                           (theory 'minimal-theory))))
  :rule-classes :forward-chaining)

(defthm fn-bpn-record-applicablep-of-metadata-state-with
  (equal
   (fn-bpn-record-applicablep
    (fn-bpn-state-with
     st (fn-bpn-machine-state-jobs st) contacts pending fenced
     (fn-bpn-machine-state-next-token st))
    record)
   (fn-bpn-record-applicablep st record))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     '(fn-bpn-record-applicablep fn-bpn-state-with
       fn-bpn-machine-constructor-accessors)
     (theory 'minimal-theory)))))

(defthm fn-bpn-propose-preserves-machine-invariant
  (implies
   (and (fn-bpn-machine-invariantp st)
        (fn-bpn-lifecycle-recordp record)
        (fn-bpn-effect-listp success)
        (fn-bpn-effectp refusal)
        (fn-bpn-effectp uncertain))
   (fn-bpn-machine-invariantp
    (fn-bpn-answer-state
     (fn-bpn-propose st record success refusal uncertain))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-invariant-components)
          (:instance fn-bpn-machine-statep-components)
          (:instance fn-bpn-machine-statep-of-state-with
                     (jobs (fn-bpn-machine-state-jobs st))
                     (contacts (fn-bpn-machine-state-contacts st))
                     (pending
                      (fn-bpn-make-pending
                       (fn-bpn-machine-state-next-token st)
                       record success refusal uncertain))
                     (fenced nil)
                     (next-token (fn-bpn-machine-state-next-token st))))
    :in-theory
    (union-theories
     '(fn-bpn-propose fn-bpn-machine-invariantp
       fn-bpn-answer-constructor-accessors
       fn-bpn-pendingp-of-constructor fn-bpn-pending-constructor-accessors
       fn-bpn-maybe-pendingp fn-bpn-machine-boolp
       fn-bpn-state-with-accessors)
     (theory 'minimal-theory)))))

(defthm fn-bpn-clear-pending-preserves-machine-invariant
  (implies
   (and (fn-bpn-machine-invariantp st)
        (fn-bpn-machine-boolp fenced))
   (fn-bpn-machine-invariantp
    (fn-bpn-state-with
     st (fn-bpn-machine-state-jobs st)
     (fn-bpn-machine-state-contacts st)
     nil fenced (fn-bpn-machine-state-next-token st))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-invariant-components)
          (:instance fn-bpn-machine-statep-components)
          (:instance fn-bpn-machine-statep-of-state-with
                     (jobs (fn-bpn-machine-state-jobs st))
                     (contacts (fn-bpn-machine-state-contacts st))
                     (pending nil)
                     (next-token (fn-bpn-machine-state-next-token st))))
    :in-theory
    (union-theories
     '(fn-bpn-machine-invariantp fn-bpn-state-with-accessors
       fn-bpn-maybe-pendingp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-initial-machine-state-has-invariant
  (implies
   (and (fn-bpn-configp config)
        (fn-bpn-machine-limitp max-jobs)
        (fn-bpn-machine-limitp max-octets))
   (fn-bpn-machine-invariantp
    (fn-bpn-initial-machine-state config max-jobs max-octets)))
  :hints (("Goal"
           :in-theory
           (enable fn-bpn-initial-machine-state fn-bpn-machine-invariantp
                   fn-bpn-machine-statep fn-bpn-job-listp
                   fn-bpn-contact-listp fn-bpn-jobs-octets
                   fn-bpn-maybe-pendingp fn-bpn-machine-boolp))))

(defthm fn-bpn-next-token-of-initial-machine-state
  (implies
   (and (fn-bpn-configp config)
        (fn-bpn-machine-limitp max-jobs)
        (fn-bpn-machine-limitp max-octets))
   (equal
    (fn-bpn-machine-state-next-token
     (fn-bpn-initial-machine-state config max-jobs max-octets))
    0))
  :hints (("Goal" :in-theory (enable fn-bpn-initial-machine-state))))

(defthm fn-bpn-limits-of-initial-machine-state
  (implies
   (and (fn-bpn-configp config)
        (fn-bpn-machine-limitp max-jobs)
        (fn-bpn-machine-limitp max-octets))
   (and (equal
         (fn-bpn-machine-state-max-jobs
          (fn-bpn-initial-machine-state config max-jobs max-octets))
         max-jobs)
        (equal
         (fn-bpn-machine-state-max-octets
          (fn-bpn-initial-machine-state config max-jobs max-octets))
         max-octets)))
  :hints (("Goal" :in-theory (enable fn-bpn-initial-machine-state))))

(defthm fn-bpn-apply-record-preserves-machine-invariant
  (implies
   (and (fn-bpn-machine-invariantp st)
        (< (fn-bpn-machine-state-next-token st)
           *fn-bpn-machine-max-records*)
        (fn-bpn-record-applicablep st record))
   (fn-bpn-machine-invariantp (fn-bpn-apply-record st record)))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-invariant-components)
          (:instance fn-bpn-machine-statep-components)
          (:instance fn-bpn-apply-record-preserves-machine-statep))
    :in-theory
    (union-theories
     '(fn-bpn-apply-record fn-bpn-machine-invariantp
       fn-bpn-state-with-accessors fn-bpn-record-token
       fn-bpn-record-applicablep fn-bpn-machine-u64p natp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-next-token-of-applicable-record
  (implies
   (fn-bpn-record-applicablep st record)
   (equal
    (fn-bpn-machine-state-next-token (fn-bpn-apply-record st record))
    (1+ (fn-bpn-machine-state-next-token st))))
  ;; Only the token test of applicability and the token the successor
  ;; state carries matter; the record, job and list recognizers stay closed.
  ;; Opened, they split the goal 242 ways, 6.3 s
  ;; (planning/evidence/misc-books-cost-2026-09-23.md).
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpn-apply-record fn-bpn-record-applicablep
                 fn-bpn-record-token fn-bpn-state-with)
                (fn-bpn-jobp fn-bpn-lifecycle-recordp fn-bpn-find-job
                 fn-bpn-append fn-bpn-replace-job fn-bpn-job-with-status
                 fn-bpn-record-key fn-bpn-member)))))

(defthm fn-bpn-apply-inapplicable-record-is-noop
  (implies (not (fn-bpn-record-applicablep st record))
           (equal (fn-bpn-apply-record st record) st))
  ;; The first branch of `fn-bpn-apply-record'; the applicability test stays
  ;; a literal (open, it cost 1.3 s and 359 k steps; closed, 39 steps).
  :hints (("Goal" :in-theory (e/d (fn-bpn-apply-record)
                                  (fn-bpn-record-applicablep)))))

(defthm fn-bpn-replay-records-preserves-machine-invariant
  (implies
   (and (fn-bpn-machine-invariantp st)
        (true-listp records)
        (<= (+ (fn-bpn-machine-state-next-token st) (len records))
            *fn-bpn-machine-max-records*))
   (fn-bpn-machine-invariantp
    (nth 1 (fn-bpn-replay-records st records))))
  :hints
  (("Goal"
    :induct (fn-bpn-replay-records st records)
    :in-theory
    (union-theories
     '(fn-bpn-replay-records fn-bpn-apply-record-preserves-machine-invariant
       fn-bpn-next-token-of-applicable-record len nth car-cons cdr-cons
       true-listp zp (:type-prescription len))
     (theory 'minimal-theory)))))

(defthm fn-bpn-key-memberp-of-resume-jobs
  (equal (fn-bpn-job-key-memberp key (fn-bpn-resume-jobs jobs))
         (fn-bpn-job-key-memberp key jobs))
  :hints (("Goal"
           :induct (fn-bpn-resume-jobs jobs)
           :in-theory
           (enable fn-bpn-resume-jobs fn-bpn-job-key-memberp
                   fn-bpn-find-job fn-bpn-job-key-of-job-with-status))))

(defthm fn-bpn-key-memberp-of-nil
  (not (fn-bpn-job-key-memberp key nil))
  :hints (("Goal" :in-theory (enable fn-bpn-job-key-memberp
                                     fn-bpn-find-job))))

(defthm fn-bpn-job-listp-of-cons
  (equal (fn-bpn-job-listp (cons job jobs))
         (and (fn-bpn-jobp job)
              (not (fn-bpn-job-key-memberp (fn-bpn-job-key job) jobs))
              (fn-bpn-job-listp jobs)))
  :hints (("Goal" :expand ((fn-bpn-job-listp (cons job jobs)))
                   :in-theory (disable fn-bpn-jobp fn-bpn-job-key))))

(defthm fn-bpn-resume-jobs-preserves-job-listp
  (implies (fn-bpn-job-listp jobs)
           (fn-bpn-job-listp (fn-bpn-resume-jobs jobs)))
  :hints (("Goal"
           :induct (fn-bpn-resume-jobs jobs)
           :in-theory
           (union-theories
            '(fn-bpn-resume-jobs fn-bpn-job-listp fn-bpn-job-listp-of-cons
              fn-bpn-job-with-status-is-a-job
              fn-bpn-job-key-of-job-with-status
              fn-bpn-key-memberp-of-resume-jobs
              fn-bpn-key-memberp-of-nil
              fn-bpn-jobp-components fn-bpn-job-statusp fn-bpn-member)
            (theory 'minimal-theory)))))

(defthm fn-bpn-len-of-resume-jobs
  (equal (len (fn-bpn-resume-jobs jobs)) (len jobs))
  :hints (("Goal" :induct (fn-bpn-resume-jobs jobs)
                   :in-theory (enable fn-bpn-resume-jobs))))

(defthm fn-bpn-jobs-octets-of-resume-jobs
  (equal (fn-bpn-jobs-octets (fn-bpn-resume-jobs jobs))
         (fn-bpn-jobs-octets jobs))
  :hints (("Goal" :induct (fn-bpn-resume-jobs jobs)
                   :in-theory (enable fn-bpn-resume-jobs
                                      fn-bpn-jobs-octets))))

(defthm fn-bpn-restart-state-with-preserves-machine-invariant
  (implies
   (and (fn-bpn-machine-invariantp st)
        (fn-bpn-job-listp jobs)
        (<= (len jobs) (fn-bpn-machine-state-max-jobs st))
        (<= (fn-bpn-jobs-octets jobs)
            (fn-bpn-machine-state-max-octets st))
        (fn-bpn-machine-boolp fenced))
   (fn-bpn-machine-invariantp
    (fn-bpn-state-with
     st jobs nil nil fenced (fn-bpn-machine-state-next-token st))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-invariant-components)
          (:instance fn-bpn-machine-statep-components)
          (:instance fn-bpn-machine-statep-of-state-with
                     (contacts nil) (pending nil)
                     (next-token (fn-bpn-machine-state-next-token st))))
    :in-theory
    (union-theories
     '(fn-bpn-machine-invariantp fn-bpn-state-with-accessors
       fn-bpn-contact-listp fn-bpn-maybe-pendingp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-sequence-fault-state-has-invariant
  (implies
   (fn-bpn-machine-invariantp st)
   (fn-bpn-machine-invariantp
    (fn-bpn-state-with
     (fn-bpn-initial-machine-state
      (fn-bpn-machine-state-config st)
      (fn-bpn-machine-state-max-jobs st)
      (fn-bpn-machine-state-max-octets st))
     nil nil nil t 0)))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-initial-machine-state-has-invariant
                (config (fn-bpn-machine-state-config st))
                (max-jobs (fn-bpn-machine-state-max-jobs st))
                (max-octets (fn-bpn-machine-state-max-octets st)))
     (:instance fn-bpn-restart-state-with-preserves-machine-invariant
                (st (fn-bpn-initial-machine-state
                     (fn-bpn-machine-state-config st)
                     (fn-bpn-machine-state-max-jobs st)
                     (fn-bpn-machine-state-max-octets st)))
                (jobs nil)
                (fenced t)))
    :in-theory
    (union-theories
     '(fn-bpn-next-token-of-initial-machine-state
       fn-bpn-limits-of-initial-machine-state
       fn-bpn-job-listp fn-bpn-jobs-octets fn-bpn-machine-boolp
       fn-bpn-machine-limitp posp len)
     (theory 'minimal-theory)))))

(defthm fn-bpn-effect-listp-of-singleton
  (equal (fn-bpn-effect-listp (list effect))
         (fn-bpn-effectp effect))
  :hints (("Goal" :in-theory (enable fn-bpn-effect-listp))))

(defthm fn-bpn-effect-listp-of-nil
  (fn-bpn-effect-listp nil)
  :hints (("Goal" :in-theory (enable fn-bpn-effect-listp))))

(defthm fn-bpn-effect-listp-of-pair
  (equal (fn-bpn-effect-listp (list first second))
         (and (fn-bpn-effectp first) (fn-bpn-effectp second)))
  :hints (("Goal" :in-theory (enable fn-bpn-effect-listp))))

(defthm fn-bpn-persist-effect-is-typed
  (fn-bpn-effectp (list :persist token record))
  :hints (("Goal" :in-theory (enable fn-bpn-effectp fn-bpn-member))))

(defthm fn-bpn-propose-effects-are-typed
  (implies (fn-bpn-effectp refusal)
           (fn-bpn-effect-listp
            (fn-bpn-answer-effects
             (fn-bpn-propose st record success refusal uncertain))))
  :hints (("Goal"
           :in-theory
           (union-theories
            '(fn-bpn-propose fn-bpn-answer-constructor-accessors
              fn-bpn-effect-listp-of-singleton
              fn-bpn-persist-effect-is-typed)
            (theory 'minimal-theory)))))

(defthm fn-bpn-enqueue-step-effects-are-typed
  (fn-bpn-effect-listp
   (fn-bpn-answer-effects
    (fn-bpn-enqueue-step st work attempt generation sequence
                         route peer adu obs)))
  :hints (("Goal"
           :in-theory
           (union-theories
            '(fn-bpn-enqueue-step fn-bpn-propose-effects-are-typed
              fn-bpn-answer-constructor-accessors
              fn-bpn-effect-listp-of-singleton
              fn-bpn-effectp fn-bpn-member car-cons cdr-cons
              true-listp)
            (theory 'minimal-theory)))))

(defthm fn-bpn-start-one-effects-are-typed
  (fn-bpn-effect-listp
   (fn-bpn-answer-effects (fn-bpn-start-one st peer)))
  :hints (("Goal"
           :in-theory
           (union-theories
            '(fn-bpn-start-one fn-bpn-propose-effects-are-typed
              fn-bpn-answer-constructor-accessors
              fn-bpn-effect-listp-of-singleton
              fn-bpn-effect-listp-of-nil
              fn-bpn-effectp fn-bpn-member car-cons cdr-cons
              true-listp)
            (theory 'minimal-theory)))))

(defthm fn-bpn-contact-step-effects-are-typed
  (fn-bpn-effect-listp
   (fn-bpn-answer-effects (fn-bpn-contact-step st peer openp)))
  :hints (("Goal"
           :in-theory
           (union-theories
            '(fn-bpn-contact-step fn-bpn-start-one-effects-are-typed
              fn-bpn-answer-constructor-accessors
              fn-bpn-effect-listp-of-singleton fn-bpn-effect-listp-of-nil
              fn-bpn-effectp fn-bpn-member
              car-cons cdr-cons true-listp)
            (theory 'minimal-theory)))))

(defthm fn-bpn-persist-result-step-effects-are-typed
  (implies (fn-bpn-machine-statep st)
           (fn-bpn-effect-listp
            (fn-bpn-answer-effects
             (fn-bpn-persist-result-step st token outcome))))
  :hints (("Goal"
           :use ((:instance fn-bpn-machine-statep-components))
           :in-theory
           (union-theories
            '(fn-bpn-persist-result-step fn-bpn-answer-constructor-accessors
              fn-bpn-effect-listp-of-singleton
              fn-bpn-effect-listp-of-nil
              fn-bpn-maybe-pendingp fn-bpn-pendingp)
            (theory 'minimal-theory)))))

(defthm fn-bpn-forward-result-step-effects-are-typed
  (fn-bpn-effect-listp
   (fn-bpn-answer-effects (fn-bpn-forward-result-step st key outcome)))
  :hints (("Goal"
           :in-theory
           (union-theories
            '(fn-bpn-forward-result-step fn-bpn-propose-effects-are-typed
              fn-bpn-answer-constructor-accessors
              fn-bpn-effect-listp-of-singleton fn-bpn-effect-listp-of-pair
              fn-bpn-effect-listp-of-nil
              fn-bpn-effectp fn-bpn-member car-cons cdr-cons
              true-listp)
            (theory 'minimal-theory)))))

(defthm fn-bpn-clock-step-effects-are-typed
  (fn-bpn-effect-listp
   (fn-bpn-answer-effects (fn-bpn-clock-step st obs)))
  :hints (("Goal"
           :in-theory
           (union-theories
            '(fn-bpn-clock-step fn-bpn-propose-effects-are-typed
              fn-bpn-answer-constructor-accessors
              fn-bpn-effect-listp-of-singleton
              fn-bpn-effect-listp-of-nil
              fn-bpn-effectp fn-bpn-member car-cons cdr-cons
              true-listp)
            (theory 'minimal-theory)))))

(defthm fn-bpn-restart-step-effects-are-typed
  (fn-bpn-effect-listp
   (fn-bpn-answer-effects (fn-bpn-restart-step st records sequence-ready)))
  :hints (("Goal"
           :in-theory
           (union-theories
            '(fn-bpn-restart-step fn-bpn-answer-constructor-accessors
              fn-bpn-effect-listp-of-singleton
              fn-bpn-effectp fn-bpn-member car-cons cdr-cons
              true-listp)
            (theory 'minimal-theory)))))

(defthm fn-bpn-enqueue-step-preserves-machine-invariant
  (implies
   (fn-bpn-machine-invariantp st)
   (fn-bpn-machine-invariantp
    (fn-bpn-answer-state
     (fn-bpn-enqueue-step st work attempt generation sequence
                          route peer adu obs))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-invariant-components)
          (:instance fn-bpn-machine-statep-components))
    :in-theory
    (union-theories
     '(fn-bpn-enqueue-step fn-bpn-propose-preserves-machine-invariant
       fn-bpn-enqueue-record-is-typed fn-bpn-answer-constructor-accessors
       fn-bpn-effect-listp-of-singleton fn-bpn-effectp fn-bpn-member
       car-cons cdr-cons true-listp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-start-one-preserves-machine-invariant
  (implies
   (fn-bpn-machine-invariantp st)
   (fn-bpn-machine-invariantp
    (fn-bpn-answer-state (fn-bpn-start-one st peer))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-invariant-components)
          (:instance fn-bpn-machine-statep-components)
          (:instance fn-bpn-find-queued-for-peer-is-a-job
                     (jobs (fn-bpn-machine-state-jobs st))))
    :in-theory
    (union-theories
     '(fn-bpn-start-one fn-bpn-propose-preserves-machine-invariant
       fn-bpn-attempting-record-is-typed fn-bpn-answer-constructor-accessors
       fn-bpn-job-key-accessors
       fn-bpn-effect-listp-of-singleton fn-bpn-effectp fn-bpn-member
       car-cons cdr-cons true-listp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-contact-step-preserves-machine-invariant
  (implies
   (fn-bpn-machine-invariantp st)
   (fn-bpn-machine-invariantp
    (fn-bpn-answer-state (fn-bpn-contact-step st peer openp))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-invariant-components)
          (:instance fn-bpn-machine-statep-components)
          (:instance fn-bpn-contact-state-with-preserves-machine-invariant
                     (contacts
                      (fn-bpn-open-contact
                       peer (fn-bpn-machine-state-contacts st))))
          (:instance fn-bpn-contact-state-with-preserves-machine-invariant
                     (contacts
                      (fn-bpn-close-contact
                       peer (fn-bpn-machine-state-contacts st)))))
    :in-theory
    (union-theories
     '(fn-bpn-contact-step fn-bpn-start-one-preserves-machine-invariant
       fn-bpn-open-contact-preserves-contact-listp
       fn-bpn-close-contact-preserves-contact-listp
       fn-bpn-answer-constructor-accessors)
     (theory 'minimal-theory)))))

(defthm fn-bpn-persist-result-step-preserves-machine-invariant
  (implies
   (fn-bpn-machine-invariantp st)
   (fn-bpn-machine-invariantp
    (fn-bpn-answer-state
     (fn-bpn-persist-result-step st token outcome))))
  :hints
  (("Goal"
    :cases ((fn-bpn-record-applicablep
             st
             (fn-bpn-pending-record (fn-bpn-machine-state-pending st))))
    :use ((:instance fn-bpn-machine-invariant-components)
          (:instance fn-bpn-clear-pending-preserves-machine-invariant
                     (fenced nil))
          (:instance fn-bpn-clear-pending-preserves-machine-invariant
                     (fenced t)))
    :in-theory
    (union-theories
     '(fn-bpn-persist-result-step
       fn-bpn-apply-record-preserves-machine-invariant
       fn-bpn-apply-inapplicable-record-is-noop
       fn-bpn-answer-constructor-accessors fn-bpn-machine-boolp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-forward-result-step-preserves-machine-invariant
  (implies
   (fn-bpn-machine-invariantp st)
   (fn-bpn-machine-invariantp
    (fn-bpn-answer-state (fn-bpn-forward-result-step st key outcome))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-invariant-components)
          (:instance fn-bpn-machine-statep-components)
          (:instance fn-bpn-find-job-is-a-job
                     (jobs (fn-bpn-machine-state-jobs st)))
          (:instance fn-bpn-key-of-found-job
                     (jobs (fn-bpn-machine-state-jobs st)))
          (:instance fn-bpn-job-key-is-typed
                     (job (fn-bpn-find-job
                           key (fn-bpn-machine-state-jobs st)))))
    :in-theory
    (union-theories
     '(fn-bpn-forward-result-step
       fn-bpn-propose-preserves-machine-invariant
       fn-bpn-terminal-record-is-typed fn-bpn-job-key-is-typed
       fn-bpn-answer-constructor-accessors
       fn-bpn-effect-listp-of-singleton fn-bpn-effect-listp-of-pair
       fn-bpn-effectp fn-bpn-member car-cons cdr-cons true-listp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-clock-step-preserves-machine-invariant
  (implies
   (fn-bpn-machine-invariantp st)
   (fn-bpn-machine-invariantp
    (fn-bpn-answer-state (fn-bpn-clock-step st obs))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-invariant-components)
          (:instance fn-bpn-machine-statep-components)
          (:instance fn-bpn-find-expired-is-a-job
                     (jobs (fn-bpn-machine-state-jobs st)))
          (:instance fn-bpn-job-key-is-typed
                     (job (fn-bpn-find-expired
                           (fn-bpn-machine-state-jobs st) obs))))
    :in-theory
    (union-theories
     '(fn-bpn-clock-step fn-bpn-propose-preserves-machine-invariant
       fn-bpn-terminal-record-is-typed fn-bpn-answer-constructor-accessors
       fn-bpn-effect-listp-of-singleton fn-bpn-effectp fn-bpn-member
       car-cons cdr-cons true-listp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-restart-step-preserves-machine-invariant
  (implies
   (and (fn-bpn-machine-invariantp st)
        (true-listp records)
        (<= (len records) *fn-bpn-machine-max-records*))
   (fn-bpn-machine-invariantp
    (fn-bpn-answer-state (fn-bpn-restart-step st records sequence-ready))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-sequence-fault-state-has-invariant)
     (:instance fn-bpn-initial-machine-state-has-invariant
                (config (fn-bpn-machine-state-config st))
                (max-jobs (fn-bpn-machine-state-max-jobs st))
                (max-octets (fn-bpn-machine-state-max-octets st)))
     (:instance fn-bpn-replay-records-preserves-machine-invariant
                (st (fn-bpn-initial-machine-state
                     (fn-bpn-machine-state-config st)
                     (fn-bpn-machine-state-max-jobs st)
                     (fn-bpn-machine-state-max-octets st))))
     (:instance fn-bpn-machine-invariant-components
                (st (nth 1
                         (fn-bpn-replay-records
                          (fn-bpn-initial-machine-state
                           (fn-bpn-machine-state-config st)
                           (fn-bpn-machine-state-max-jobs st)
                           (fn-bpn-machine-state-max-octets st))
                          records))))
     (:instance fn-bpn-machine-statep-components
                (st (nth 1
                         (fn-bpn-replay-records
                          (fn-bpn-initial-machine-state
                           (fn-bpn-machine-state-config st)
                           (fn-bpn-machine-state-max-jobs st)
                           (fn-bpn-machine-state-max-octets st))
                          records))))
     (:instance fn-bpn-restart-state-with-preserves-machine-invariant
                (st (nth 1
                         (fn-bpn-replay-records
                          (fn-bpn-initial-machine-state
                           (fn-bpn-machine-state-config st)
                           (fn-bpn-machine-state-max-jobs st)
                           (fn-bpn-machine-state-max-octets st))
                          records)))
                (jobs
                 (fn-bpn-resume-jobs
                  (fn-bpn-machine-state-jobs
                   (nth 1
                        (fn-bpn-replay-records
                         (fn-bpn-initial-machine-state
                          (fn-bpn-machine-state-config st)
                          (fn-bpn-machine-state-max-jobs st)
                          (fn-bpn-machine-state-max-octets st))
                         records)))))
                (fenced nil))
     (:instance fn-bpn-restart-state-with-preserves-machine-invariant
                (st (nth 1
                         (fn-bpn-replay-records
                          (fn-bpn-initial-machine-state
                           (fn-bpn-machine-state-config st)
                           (fn-bpn-machine-state-max-jobs st)
                           (fn-bpn-machine-state-max-octets st))
                          records)))
                (jobs
                 (fn-bpn-machine-state-jobs
                  (nth 1
                       (fn-bpn-replay-records
                        (fn-bpn-initial-machine-state
                         (fn-bpn-machine-state-config st)
                         (fn-bpn-machine-state-max-jobs st)
                         (fn-bpn-machine-state-max-octets st))
                        records))))
                (fenced t)))
    :in-theory
    (union-theories
     '(fn-bpn-restart-step fn-bpn-answer-constructor-accessors
       fn-bpn-sequence-fault-state-has-invariant
       fn-bpn-restart-state-with-preserves-machine-invariant
       fn-bpn-next-token-of-initial-machine-state
       fn-bpn-resume-jobs-preserves-job-listp
       fn-bpn-len-of-resume-jobs fn-bpn-jobs-octets-of-resume-jobs
       fn-bpn-machine-boolp)
     (theory 'minimal-theory)))))

; Keystone: the effect output of the host-called dispatcher is typed from the
; maintained input invariant, rather than assumed typed after the fact.
(defthm fn-bpn-step-effects-are-typed
  (fn-bpn-effect-listp
   (fn-bpn-answer-effects (fn-bpn-step st event)))
  :hints (("Goal"
           :in-theory
           (union-theories
            '(fn-bpn-step fn-bpn-dispatch
              fn-bpn-enqueue-step-effects-are-typed
              fn-bpn-contact-step-effects-are-typed
              fn-bpn-start-one-effects-are-typed
              fn-bpn-persist-result-step-effects-are-typed
              fn-bpn-forward-result-step-effects-are-typed
              fn-bpn-clock-step-effects-are-typed
              fn-bpn-restart-step-effects-are-typed
              fn-bpn-answer-constructor-accessors fn-bpn-effect-listp)
            (theory 'minimal-theory)))))

(defthm fn-bpn-step-emits-no-release-from-actual-effects
  (not (fn-bpn-effect-kind-memberp
        :release (fn-bpn-answer-effects (fn-bpn-step st event))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-effect-listp-excludes-release
                (effects (fn-bpn-answer-effects (fn-bpn-step st event)))))
    :in-theory
    (union-theories '(fn-bpn-step-effects-are-typed)
                    (theory 'minimal-theory)))))

(defthm fn-bpn-effectp-excludes-receipt-prepare
  (implies (fn-bpn-effectp effect)
           (not (equal (fn-cbor-ag-car effect) :receipt-prepare)))
  :hints (("Goal" :in-theory (enable fn-bpn-effectp fn-bpn-member))))

(defthm fn-bpn-effect-listp-excludes-receipt-prepare
  (implies (fn-bpn-effect-listp effects)
           (not (fn-bpn-effect-kind-memberp :receipt-prepare effects)))
  :hints
  (("Goal" :induct (fn-bpn-effect-listp effects)
    :in-theory
    (enable fn-bpn-effect-listp fn-bpn-effect-kind-memberp
            fn-bpn-effectp-excludes-receipt-prepare))))

(defthm fn-bpn-step-emits-no-receipt-prepare
  (not (fn-bpn-effect-kind-memberp
        :receipt-prepare (fn-bpn-answer-effects (fn-bpn-step st event))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-effect-listp-excludes-receipt-prepare
                (effects (fn-bpn-answer-effects (fn-bpn-step st event)))))
    :in-theory
    (union-theories '(fn-bpn-step-effects-are-typed)
                    (theory 'minimal-theory)))))

(defthm fn-bpn-step-preserves-machine-invariant
  (implies (and (fn-bpn-machine-invariantp st)
                (fn-bpn-machine-eventp event))
           (fn-bpn-machine-invariantp
            (fn-bpn-answer-state (fn-bpn-step st event))))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     '(fn-bpn-machine-eventp fn-bpn-eventp fn-bpn-step fn-bpn-dispatch
       fn-bpn-enqueue-step-preserves-machine-invariant
       fn-bpn-contact-step-preserves-machine-invariant
       fn-bpn-start-one-preserves-machine-invariant
       fn-bpn-persist-result-step-preserves-machine-invariant
       fn-bpn-forward-result-step-preserves-machine-invariant
       fn-bpn-clock-step-preserves-machine-invariant
       fn-bpn-restart-step-preserves-machine-invariant
       fn-bpn-answer-constructor-accessors fn-bpn-member)
     (theory 'minimal-theory)))))
