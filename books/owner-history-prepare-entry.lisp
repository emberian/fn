; Host prepare entries over the resident history.
(in-package "ACL2")
(include-book "history-served-prepare")

(include-book "owner-retain-writer-frame")

(defun fn-owner-prepare-consumer (event fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :guard (and (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))))
           (ignorable fn-arena))
  (if (not (fn-cpe-eventp event))
      (value :invalid)
    ; fn-pdc-pout-prepare-consumer: (:store (:prepare-consumer E)) with the
    ; carried Store prepare, no appended-history replay
    ; (books/owner-prepare-deferred-carried.lisp: equal to
    ; fn-pout-prepare-consumer under fn-snt-relation and whenever the
    ; reference stages; keeps fn-lgoc-invariantp), and its word
    ; (fn-pdc-pout-prepares-answer-the-store-change).
    (mv-let (word next)
      (fn-pdc-pout-prepare-consumer (fn-owner-ocfg state) event)
      (let ((state (fn-owner-install-ocfg next state)))
        (value word)))))

(defun fn-owner-prepare-topic (event fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :guard (and (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))))
           (ignorable fn-arena))
  (if (not (fn-th-topic-eventp event))
      (value :invalid)
    ; fn-psrv-prepare-topic (lane prepare-served): (:store (:prepare-topic
    ; E)) when the consumer projection accepts E, which its completion
    ; needs (fn-psrv-prepare-topic-is-ocfg-step-when-admitted,
    ; fn-psrv-prepare-topic-preserves-invariant); fn-pout-prepare-topic
    ; answers its word (KEYSTONE
    ; fn-pout-prepare-topic-answers-the-store-change).
    ; Since lane served-incremental-2: fn-pdc-pout-prepare-topic, the same
    ; with the carried Store prepare (no appended-history replay; equal to
    ; fn-pout-prepare-topic under fn-snt-relation and whenever the reference
    ; stages; fn-pdc-psrv-prepare-topic-preserves-invariant).
    (mv-let (word next)
      (fn-pdc-pout-prepare-topic (fn-owner-ocfg state) event)
      (let ((state (fn-owner-install-ocfg next state)))
        (value word)))))

(defun fn-owner-prepare-consumer-served (event fn-arena fn-hist state)
  (declare (xargs :stobjs (state fn-arena fn-hist)
                  :guard (and (and (boundp-global (quote fn-owner) state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))) (fn-cst-relation (fn-owner-store state))))
           (ignorable fn-arena))
  (if (not (fn-cpe-eventp event))
      (value :invalid)
    (mv-let (word next) (fn-hsp-pout-prepare-consumer (fn-owner-ocfg state) event fn-hist)
      (let ((state (fn-owner-install-ocfg next state))) (value word)))))

(defthm fn-owner-prepare-consumer-served-is-reference
 (implies (and (fn-owner-retain-statep state)
               (fn-hist-of-storep hist (fn-owner-store state)))
  (equal (fn-owner-prepare-consumer-served event arena hist state) (fn-owner-prepare-consumer event arena state)))
 :hints (("Goal" :in-theory '(fn-owner-prepare-consumer-served fn-owner-prepare-consumer fn-owner-retain-statep
 fn-owner-store fn-owner-core fn-owner-ocfg fn-hsp-pout-prepare-consumer-is-reference))))
(defthm fn-owner-prepare-consumer-served-preserves-carried-state
 (implies (fn-owner-retain-statep state)
  (fn-owner-retain-statep (mv-nth 2 (fn-owner-prepare-consumer-served event fn-arena fn-hist state))))
 :hints (("Goal" :use ((:instance fn-owner-retain-statep-implies-lgoc))
 :in-theory '(fn-owner-prepare-consumer-served fn-hsp-pout-prepare-consumer
 fn-hsp-ocfg-prepare-consumer-preserves-invariant
 fn-orh-retain-statep-of-install-ocfg mv-nth nth zp car-cons cdr-cons
 (:executable-counterpart zp) (:executable-counterpart equal)))))
(in-theory (disable fn-owner-prepare-consumer-served))

(defun fn-owner-prepare-topic-served (event fn-arena fn-hist state)
  (declare (xargs :stobjs (state fn-arena fn-hist)
                  :guard (and (and (boundp-global (quote fn-owner) state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))) (fn-cst-relation (fn-owner-store state))))
           (ignorable fn-arena))
  (if (not (fn-th-topic-eventp event))
      (value :invalid)
    (mv-let (word next) (fn-hsp-pout-prepare-topic (fn-owner-ocfg state) event fn-hist)
      (let ((state (fn-owner-install-ocfg next state))) (value word)))))

(defthm fn-owner-prepare-topic-served-is-reference
 (implies (and (fn-owner-retain-statep state)
               (fn-hist-of-storep hist (fn-owner-store state)))
  (equal (fn-owner-prepare-topic-served event arena hist state) (fn-owner-prepare-topic event arena state)))
 :hints (("Goal" :in-theory '(fn-owner-prepare-topic-served fn-owner-prepare-topic fn-owner-retain-statep
 fn-owner-store fn-owner-core fn-owner-ocfg fn-hsp-pout-prepare-topic-is-reference))))
(defthm fn-owner-prepare-topic-served-preserves-carried-state
 (implies (fn-owner-retain-statep state)
  (fn-owner-retain-statep (mv-nth 2 (fn-owner-prepare-topic-served event fn-arena fn-hist state))))
 :hints (("Goal" :use ((:instance fn-owner-retain-statep-implies-lgoc))
 :in-theory '(fn-owner-prepare-topic-served fn-hsp-pout-prepare-topic
 fn-hsp-psrv-prepare-topic-preserves-invariant
 fn-orh-retain-statep-of-install-ocfg mv-nth nth zp car-cons cdr-cons
 (:executable-counterpart zp) (:executable-counterpart equal)))))
(in-theory (disable fn-owner-prepare-topic-served))
