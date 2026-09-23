; Received administrative status reports are remote observations only.
; This read-only selector has no transition, retry, receipt, or release effect.
(in-package "ACL2")
(include-book "bp-report-author")
(set-verify-guards-eagerness 0)

(defun fn-bpn-report-correlate-job (jobs report)
  (declare (xargs :guard t :measure (acl2-count jobs)))
  (if (atom jobs)
      nil
    (let* ((job (car jobs))
           (bundle (fn-bpn-job-bundle job))
           (primary (fn-bpb-bundle-primary bundle)))
      (if (and (fn-bpn-jobp job)
               (fn-bpb-bundlep bundle)
               (equal (fn-bpp-source primary) (fn-bpn-nth 3 report))
               (equal (fn-bpp-creation-time primary)
                      (fn-bpn-nth 0 (fn-bpn-nth 4 report)))
               (equal (fn-bpp-sequence primary)
                      (fn-bpn-nth 1 (fn-bpn-nth 4 report))))
          (fn-bpn-job-key job)
        (fn-bpn-report-correlate-job (cdr jobs) report)))))

(defun fn-bpn-report-observe-held (st held node)
  (declare (xargs :guard t))
  (if (not (and (fn-bpnf-heldp held)
                (fn-bpp-eidp node)
                (null (fn-bpn-nth 14 held))
                (null (fn-bpn-nth 10 held))))
      nil
    (let* ((bundle (fn-bpnf-held-bundle held))
           (primary (fn-bpb-bundle-primary bundle))
           (flags (fn-bpp-flags primary)))
      (if (not (and (fn-bpp-administrativep flags)
                    (fn-bpp-flags-conformantp primary)
                    (equal (fn-bpp-destination primary) node)))
          nil
        (let* ((decoded (fn-bpn-report-decode (fn-bpb-payload bundle)))
               (report (and (fn-cbor-result-okp decoded)
                            (fn-cbor-result-value decoded))))
          (if report
              (list :observed (fn-bpn-nth 3 held)
                    (fn-bpn-report-correlate-job
                     (fn-bpn-machine-state-jobs (fn-bpnf-base st)) report)
                    report)
            (list :malformed (fn-bpn-nth 3 held))))))))

(defun fn-bpn-report-observe-next-aux (st held-list node after selected)
  (declare (xargs :guard t :measure (acl2-count held-list)))
  (if (atom held-list)
      selected
    (let* ((held (car held-list))
           (answer (and (or (null after)
                            (and (natp after)
                                 (< after (fn-bpn-nth 3 held))))
                        (fn-bpn-report-observe-held st held node))))
      (fn-bpn-report-observe-next-aux
       st (cdr held-list) node after
       (if (and answer
                (or (null selected)
                    (< (fn-bpn-nth 1 answer) (fn-bpn-nth 1 selected))))
           answer selected)))))

(defun fn-bpn-report-observe-next (st node after)
  (declare (xargs :guard t))
  (fn-bpn-report-observe-next-aux
   st (fn-bpnf-held-list st) node after nil))
