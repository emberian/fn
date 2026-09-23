; Queue one recovered deletion report as an administrative BP bundle.
; This remains the one foundation/base lifecycle owner: ordinary events
; delegate to fn-bpn-report-step, and the base journal owns the queued job.
(in-package "ACL2")
(include-book "bp-report-outbox")
(set-verify-guards-eagerness 0)

(defun fn-bpn-report-bundle (config peer payload sequence observation)
  (declare (xargs :guard t))
  (fn-bpb-make-bundle
   (fn-bpp-make-block
    *fn-bpp-flag-administrative* (fn-bpn-config-crc-type config)
    peer (fn-bpn-config-node-id config) '(:dtn-none)
    (if (fn-clock-has-wall observation)
        (fn-clock-wall observation) 0)
    sequence (fn-bpn-config-lifetime config) nil nil)
   (fn-bpn-send-blocks config)
   (fn-bpb-payload-block (fn-bpn-config-crc-type config) payload)))

(defun fn-bpn-report-job-matchp (base view)
  (declare (xargs :guard t))
  (let* ((key (list (fn-bpn-nth 4 view) (fn-bpn-nth 5 view)
                    (fn-bpn-nth 6 view)))
         (job (fn-bpn-find-job key (fn-bpn-machine-state-jobs base))))
    (and (equal (fn-bpn-nth 0 view) :report-outbox)
         (fn-bpn-jobp job)
         (let* ((bundle (fn-bpn-job-bundle job))
                (primary (fn-bpb-bundle-primary bundle)))
           (and (fn-bpb-bundlep bundle)
                (equal (fn-bpn-job-peer job) (fn-bpn-nth 2 view))
                (equal (fn-bpb-payload bundle) (fn-bpn-nth 3 view))
                (equal (fn-bpn-job-wire job) (fn-bpb-encode bundle))
                (equal (fn-bpn-job-sequence job)
                       (fn-bpp-sequence primary))
                (equal (fn-bpp-flags primary) *fn-bpp-flag-administrative*)
                (equal (fn-bpp-destination primary) (fn-bpn-nth 2 view))
                (equal (fn-bpp-source primary)
                       (fn-bpn-config-node-id
                        (fn-bpn-machine-state-config base)))
                (equal (fn-bpp-report-to primary) '(:dtn-none)))))))

(defun fn-bpn-report-queue-step (st arrival sequence route observation)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((base (fn-bpnf-base st))
         (held (fn-bpnf-find-arrival arrival (fn-bpnf-held-list st)))
         (view (fn-bpn-report-outbox-view held))
         (work (fn-bpn-nth 4 view))
         (attempt (fn-bpn-nth 5 view))
         (generation (fn-bpn-nth 6 view))
         (key (list work attempt generation))
         (old (fn-bpn-find-job key (fn-bpn-machine-state-jobs base))))
    (cond
     ((or (fn-bpnf-issued st) (fn-bpnf-waits st)
          (fn-bpn-machine-state-fenced base)
          (fn-bpn-machine-state-pending base)
          (not view))
      (fn-bpnf-answer st nil))
     ((not (and (fn-bpn-machine-statep base)
                (fn-bpn-routep route)
                (fn-bpp-timep sequence)
                (fn-clock-observationp observation)
                (fn-bpn-keyp key)
                (fn-bpb-datap (fn-bpn-nth 3 view))))
      (fn-bpnf-answer st (list (list :bundle-queue-refused
                                   work attempt generation :arguments))))
     (old
      (fn-bpnf-answer
       st (list (if (fn-bpn-report-job-matchp base view)
                    (list :bundle-queue-accepted work attempt generation
                          (fn-bpn-job-sequence old) :duplicate)
                  (list :bundle-queue-refused work attempt generation
                        :enqueue-conflict)))))
     (t
      (let* ((config (fn-bpn-machine-state-config base))
             (peer (fn-bpn-nth 2 view))
             (bundle (fn-bpn-report-bundle
                      config peer (fn-bpn-nth 3 view) sequence observation))
             (wire (and (fn-bpb-bundlep bundle) (fn-bpb-encode bundle))))
        (if (not (and (fn-bpb-bundlep bundle)
                      (fn-cbor-octet-listp wire)
                      (<= (len wire) *fn-bpn-machine-max-job-octets*)
                      (< (len (fn-bpn-machine-state-jobs base))
                         (fn-bpn-machine-state-max-jobs base))
                      (<= (+ (fn-bpn-jobs-octets
                              (fn-bpn-machine-state-jobs base))
                             (len wire))
                          (fn-bpn-machine-state-max-octets base))))
            (fn-bpnf-answer st (list (list :bundle-queue-refused
                                         work attempt generation :capacity)))
          (let* ((token (fn-bpn-machine-state-next-token base))
                 (job (fn-bpn-make-job
                       work attempt generation sequence
                       (fn-bpn-anchor-of bundle observation) peer route
                       bundle wire :queued token))
                 (record (list :queued token job)))
            (if (not (fn-bpn-lifecycle-recordp record))
                (fn-bpnf-answer st (list (list :bundle-queue-refused
                                             work attempt generation :arguments)))
          (let ((ans
                  (fn-bpn-propose
                   base record
                   (list (list :bundle-queue-accepted
                               work attempt generation sequence :durable))
                   (list :bundle-queue-refused work attempt generation
                         :persistence-refused)
                   (list :bundle-queue-uncertain work attempt generation
                         :persistence))))
            (fn-bpnf-answer
             (fn-bpnf-with-base st (fn-bpn-answer-state ans))
             (fn-bpn-answer-effects ans)))))))))))

(defun fn-bpn-report-author-step (st event)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (fn-cbor-ag-car event) :queue-report)
      (fn-bpn-report-queue-step
       st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
       (fn-bpn-nth 3 event) (fn-bpn-nth 4 event))
    (fn-bpn-report-step st event)))

(defthm fn-bpn-report-author-step-delegates-ordinary-events
  (implies (not (equal (fn-cbor-ag-car event) :queue-report))
           (equal (fn-bpn-report-author-step st event)
                  (fn-bpn-report-step st event)))
  :hints (("Goal" :in-theory (disable fn-bpn-report-step)))
  :rule-classes nil)
