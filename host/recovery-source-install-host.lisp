; PRF-1149: final actual Store installation, separate from cold start/observe.
(in-package "ACL2")
(include-book "recovery-source-host")
(include-book "../books/store-node")

; Called in the same actual owner installation action after configured open,
; with the field carries from that same SSR/summary producer. This wrapper
; reads actual Store count/frontier/CP; native never fabricates those values.
(defun fn-owner-recovery-source-install (token fields cpfields pool rows state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((c (fn-owner-recovery-global 'fn-owner-recovery-source state))
         (st (fn-owner-recovery-global 'fn-store-sn state))
         (files (fn-sn-files st))
         (epoch (fn-owner-canonical-epoch state)))
    (if (not (and (if (fn-rsoa-originp (fn-omk-at 3 c))
                     (fn-owner-recovery-source-currentp-value c (fn-rsa-token c) state)
                   (fn-rsa-metap (fn-store-sco-recovery-source-value state)))
                  (fn-owner-recovery-records-formp (fn-sf-records-field files))))
        (value '(:unavailable :verified-source))
    (if (not (eq (fn-sf-phase files) :ready)) (value '(:unavailable :recovery-store))
      (let ((count (fn-sf-records-count files)) (frontier (fn-sf-frontier files)))
        ; Configurations and the recovered log kernel can advance the final
        ; frontier beyond the event fold. Read that frontier from the actual
        ; completed Store; retain the same ORIGINAL ctx and require exact
        ; event count before this metadata completion. No second replay.
        (if (not (equal count (fn-omk-at 4 c)))
            (value '(:unavailable :recovery-count))
          (mv-let (completed ready)
            (fn-rsa-observe c token epoch (fn-owner-recovery-source-generation-value c state)
                            (fn-omk-at 6 c) frontier)
            (if (not (eq completed :counted))
                (value '(:unavailable :recovery-frontier))
              (mv-let (word source next)
                (fn-rsa-seal ready (fn-rsa-token ready) epoch
                             (fn-owner-recovery-source-generation-value c state)
                             count frontier)
                (if (not (eq word :sealed)) (value '(:unavailable :recovery-completion))
                  (mv-let (installed state)
                    (fn-owner-canonical-install epoch count (fn-omk-at 6 ready) fields
                                                (fn-sn-consumer st) cpfields pool rows source state)
                    (if (not (eq installed :installed)) (value '(:unavailable :canonical-carry))
                      (let ((state (f-put-global 'fn-owner-recovery-source next state)))
                        (value (list :installed source)))))))))))))
))
