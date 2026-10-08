; Prepared owners refresh from the resident history, whose content prepares preserve.
(in-package "ACL2")
(include-book "owner-history-io")
(include-book "history-served-prepare-kernel")
(include-book "owner-prepare-deferred-carried")

(defthm fn-hsp-owner-with-store-preserves-invariant
  (implies (and (fn-lgoc-invariantp oc)
                (fn-cst-relation st)
                (fn-cstp-carriedp st)
                (equal (fn-sn-config-history st)
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                (equal (fn-sf-records (fn-sn-files st))
                       (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
           (fn-lgoc-invariantp (fn-ocfg-with-owner oc
                                                   (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
                                                                               st
                                                                               fn-hist))))
  :hints (("Goal"
           :use
           (fn-lgoc-ocl-relation-of-owner-with-store-ix fn-lgoc-invariant-statep
                                                     (:instance fn-sf-prefixp-reflexive
                                                                (xs (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                                                     (:instance fn-sf-state-records-are-true-list
                                                                (s (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                                                     (:instance fn-cstp-sn-statep-files
                                                                (st (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory
           (quote (fn-lgoc-invariantp fn-hsv-store-of-owner-with-store)))))

(defun fn-hsp-ocfg-prepare-retention (oc event fn-hist)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc)))) :stobjs fn-hist))
  (mbe :logic (fn-ocfg-with-owner oc
                      (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
                                                  (fn-pdc-sn-prepare-retention (fn-own-store (fn-ocfg-owner oc))
                                                                               event)
                                                  fn-hist))
       :exec (fn-ocfg-with-owner oc
                      (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
                                                  (fn-hpf-pdc-sn-prepare-retention (fn-own-store (fn-ocfg-owner oc))
                                                                               event)
                                                  fn-hist))))

(defthm fn-hsp-ocfg-prepare-retention-is-reference
 (implies (and (fn-lgoc-invariantp oc)
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-ocfg-prepare-retention oc event hist) (fn-pdc-ocfg-prepare-retention oc event)))
 :hints (("Goal" :in-theory '(fn-pdc-ocfg-prepare-retention fn-hsp-ocfg-prepare-retention fn-sbud-oc-store fn-hist-of-storep fn-pdc-sn-prepares-keep-histories fn-ccar-cpe-projection-step-is-cpe-projection-step fn-ocl-owner-with-store-ix-is-reference fn-cstp-relation-is-statep fn-lgoc-invariantp fn-lgoc-ocl-relation-cst) :use ((:instance fn-pdc-sn-prepare-retention-preserves (s (fn-own-store (fn-ocfg-owner oc))) (e event))))))

(in-theory (disable fn-hsp-ocfg-prepare-retention))

(defthm fn-hsp-ocfg-prepare-retention-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-hsp-ocfg-prepare-retention oc e fn-hist)))
  :hints (("Goal"
           :use
           ((:instance fn-pdc-sn-prepare-retention-preserves (s (fn-own-store (fn-ocfg-owner oc))))
            (:instance fn-hsp-owner-with-store-preserves-invariant
                       (st (fn-pdc-sn-prepare-retention (fn-own-store (fn-ocfg-owner oc)) e)))
            fn-lgoc-ocl-relation-cst)
           :in-theory
           (quote (fn-hsp-ocfg-prepare-retention fn-pdc-sn-prepares-keep-histories
                                                 fn-lgoc-invariantp)))))

(defun fn-hsp-ocfg-prepare-consumer (oc event fn-hist)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc)))) :stobjs fn-hist))
  (mbe :logic (fn-ocfg-with-owner oc
                      (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
                                                  (fn-pdc-sn-prepare-consumer (fn-own-store (fn-ocfg-owner oc))
                                                                              event)
                                                  fn-hist))
       :exec (fn-ocfg-with-owner oc
                      (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
                                                  (fn-hpf-pdc-sn-prepare-consumer (fn-own-store (fn-ocfg-owner oc))
                                                                              event)
                                                  fn-hist))))

(defthm fn-hsp-ocfg-prepare-consumer-is-reference
 (implies (and (fn-lgoc-invariantp oc)
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-ocfg-prepare-consumer oc event hist) (fn-pdc-ocfg-prepare-consumer oc event)))
 :hints (("Goal" :in-theory '(fn-pdc-ocfg-prepare-consumer fn-hsp-ocfg-prepare-consumer fn-sbud-oc-store fn-hist-of-storep fn-pdc-sn-prepares-keep-histories fn-ccar-cpe-projection-step-is-cpe-projection-step fn-ocl-owner-with-store-ix-is-reference fn-cstp-relation-is-statep fn-lgoc-invariantp fn-lgoc-ocl-relation-cst fn-hsp-ocfg-prepare-retention-is-reference) :use ((:instance fn-pdc-sn-prepare-consumer-preserves (s (fn-own-store (fn-ocfg-owner oc))) (e event))))))

(in-theory (disable fn-hsp-ocfg-prepare-consumer))

(defthm fn-hsp-ocfg-prepare-consumer-preserves-invariant
  (implies (fn-lgoc-invariantp oc) (fn-lgoc-invariantp (fn-hsp-ocfg-prepare-consumer oc e fn-hist)))
  :hints (("Goal"
           :use
           ((:instance fn-pdc-sn-prepare-consumer-preserves (s (fn-own-store (fn-ocfg-owner oc))))
            (:instance fn-hsp-owner-with-store-preserves-invariant
                       (st (fn-pdc-sn-prepare-consumer (fn-own-store (fn-ocfg-owner oc)) e)))
            fn-lgoc-ocl-relation-cst)
           :in-theory
           (quote (fn-hsp-ocfg-prepare-consumer fn-pdc-sn-prepares-keep-histories
                                                fn-lgoc-invariantp)))))

(defun fn-hsp-psrv-prepare-topic (oc event fn-hist)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc)))) :stobjs fn-hist))
  (mbe :logic (let* ((o (fn-ocfg-owner oc)) (s (fn-own-store o)))
    (if (and (fn-store-event-p event)
             (eq (car (fn-ccar-cpe-projection-step (fn-sn-consumer s) event (fn-sn-identity-next s)))
                 :ok))
        (fn-ocfg-with-owner oc
                            (fn-ocl-owner-with-store-ix o (fn-pdc-sn-prepare-topic s event) fn-hist))
      oc))
       :exec (let* ((o (fn-ocfg-owner oc)) (s (fn-own-store o)))
    (if (and (fn-store-event-p event)
             (eq (car (fn-ccar-cpe-projection-step (fn-sn-consumer s) event (fn-sn-identity-next s)))
                 :ok))
        (fn-ocfg-with-owner oc
                            (fn-ocl-owner-with-store-ix o (fn-hpf-pdc-sn-prepare-topic s event) fn-hist))
      oc))))

(defthm fn-hsp-psrv-prepare-topic-is-reference
 (implies (and (fn-lgoc-invariantp oc)
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-psrv-prepare-topic oc event hist) (fn-pdc-psrv-prepare-topic oc event)))
 :hints (("Goal" :in-theory '(fn-pdc-psrv-prepare-topic fn-hsp-psrv-prepare-topic fn-sbud-oc-store fn-hist-of-storep fn-pdc-sn-prepares-keep-histories fn-ccar-cpe-projection-step-is-cpe-projection-step fn-ocl-owner-with-store-ix-is-reference fn-cstp-relation-is-statep fn-lgoc-invariantp fn-lgoc-ocl-relation-cst fn-hsp-ocfg-prepare-retention-is-reference fn-hsp-ocfg-prepare-consumer-is-reference) :use ((:instance fn-pdc-sn-prepare-topic-preserves (s (fn-own-store (fn-ocfg-owner oc))) (e event))))))

(in-theory (disable fn-hsp-psrv-prepare-topic))

(defthm fn-hsp-psrv-prepare-topic-preserves-invariant
  (implies (fn-lgoc-invariantp oc) (fn-lgoc-invariantp (fn-hsp-psrv-prepare-topic oc e fn-hist)))
  :hints (("Goal"
           :use
           ((:instance fn-pdc-sn-prepare-topic-preserves (s (fn-own-store (fn-ocfg-owner oc))))
            (:instance fn-hsp-owner-with-store-preserves-invariant
                       (st (fn-pdc-sn-prepare-topic (fn-own-store (fn-ocfg-owner oc)) e)))
            fn-lgoc-ocl-relation-cst)
           :in-theory
           (quote (fn-hsp-psrv-prepare-topic fn-pdc-sn-prepares-keep-histories
                                             fn-ccar-cpe-projection-step-is-cpe-projection-step
                                             fn-lgoc-invariantp)))))

(defun fn-hsp-pout-prepare-retention (oc e fn-hist)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc)) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store)))
                  :stobjs fn-hist))
  (let ((next (fn-hsp-ocfg-prepare-retention oc e fn-hist)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next)) :prepared :refused)
        next)))

(defthm fn-hsp-pout-prepare-retention-is-reference
 (implies (and (fn-lgoc-invariantp oc)
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-pout-prepare-retention oc e hist) (fn-pdc-pout-prepare-retention oc e)))
 :hints (("Goal" :in-theory '(fn-pdc-pout-prepare-retention fn-hsp-pout-prepare-retention fn-sbud-oc-store fn-hist-of-storep fn-pdc-sn-prepares-keep-histories fn-ccar-cpe-projection-step-is-cpe-projection-step fn-ocl-owner-with-store-ix-is-reference fn-cstp-relation-is-statep fn-lgoc-invariantp fn-lgoc-ocl-relation-cst fn-hsp-ocfg-prepare-retention-is-reference fn-hsp-ocfg-prepare-consumer-is-reference fn-hsp-psrv-prepare-topic-is-reference) )))

(in-theory (disable fn-hsp-pout-prepare-retention))

(defun fn-hsp-pout-prepare-consumer (oc e fn-hist)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc)) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store)))
                  :stobjs fn-hist))
  (let ((next (fn-hsp-ocfg-prepare-consumer oc e fn-hist)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next)) :prepared :refused)
        next)))

(defthm fn-hsp-pout-prepare-consumer-is-reference
 (implies (and (fn-lgoc-invariantp oc)
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-pout-prepare-consumer oc e hist) (fn-pdc-pout-prepare-consumer oc e)))
 :hints (("Goal" :in-theory '(fn-pdc-pout-prepare-consumer fn-hsp-pout-prepare-consumer fn-sbud-oc-store fn-hist-of-storep fn-pdc-sn-prepares-keep-histories fn-ccar-cpe-projection-step-is-cpe-projection-step fn-ocl-owner-with-store-ix-is-reference fn-cstp-relation-is-statep fn-lgoc-invariantp fn-lgoc-ocl-relation-cst fn-hsp-ocfg-prepare-retention-is-reference fn-hsp-ocfg-prepare-consumer-is-reference fn-hsp-psrv-prepare-topic-is-reference fn-hsp-pout-prepare-retention-is-reference) )))

(in-theory (disable fn-hsp-pout-prepare-consumer))

(defun fn-hsp-pout-prepare-topic (oc e fn-hist)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc)) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store)))
                  :stobjs fn-hist))
  (let ((next (fn-hsp-psrv-prepare-topic oc e fn-hist)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next)) :prepared :refused)
        next)))

(defthm fn-hsp-pout-prepare-topic-is-reference
 (implies (and (fn-lgoc-invariantp oc)
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-pout-prepare-topic oc e hist) (fn-pdc-pout-prepare-topic oc e)))
 :hints (("Goal" :in-theory '(fn-pdc-pout-prepare-topic fn-hsp-pout-prepare-topic fn-sbud-oc-store fn-hist-of-storep fn-pdc-sn-prepares-keep-histories fn-ccar-cpe-projection-step-is-cpe-projection-step fn-ocl-owner-with-store-ix-is-reference fn-cstp-relation-is-statep fn-lgoc-invariantp fn-lgoc-ocl-relation-cst fn-hsp-ocfg-prepare-retention-is-reference fn-hsp-ocfg-prepare-consumer-is-reference fn-hsp-psrv-prepare-topic-is-reference fn-hsp-pout-prepare-retention-is-reference fn-hsp-pout-prepare-consumer-is-reference) )))

(in-theory (disable fn-hsp-pout-prepare-topic))
