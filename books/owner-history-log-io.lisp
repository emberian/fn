; The fixed log route observes the same file steps, synchronizing the resident suffix.
(in-package "ACL2")
(include-book "owner-history-io")

(defun fn-hsv-log-reserve (oc fn-hist)
 (declare (xargs :stobjs fn-hist :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
 :guard-hints (("Goal" :in-theory (union-theories '(fn-hsv-observe-car-preserves-state) (theory 'ground-zero))))))
 (mv-let (oc fn-hist) (fn-hsv-observe oc :start-frontier nil fn-hist)
    (mv-let (oc fn-hist) (fn-hsv-observe oc :frontier-file :ok fn-hist)
    (mv-let (oc fn-hist) (fn-hsv-observe oc :frontier-replace :ok fn-hist)
    (mv-let (oc fn-hist) (fn-hsv-observe oc :frontier-directory :ok fn-hist)
    (mv oc fn-hist))))))

(defthm fn-hsv-log-reserve-preserves-state
 (implies (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
  (fn-sn-statep (fn-own-store (fn-ocfg-owner (mv-nth 0 (fn-hsv-log-reserve oc hist))))))
 :hints (("Goal" :in-theory '((:type-prescription fn-hsv-observe) mv-nth zp car-cons cdr-cons (:executable-counterpart zp) fn-hsv-log-reserve fn-hsv-observe-car-preserves-state))))

(defthm fn-hsv-log-reserve-preserves-history
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (fn-hist-of-storep (mv-nth 1 (fn-hsv-log-reserve oc hist))
                    (fn-own-store (fn-ocfg-owner (mv-nth 0 (fn-hsv-log-reserve oc hist))))))
 :hints (("Goal" :in-theory '((:type-prescription fn-hsv-observe) mv-nth zp car-cons cdr-cons (:executable-counterpart zp) fn-hsv-log-reserve fn-hsv-observe-car-preserves-history fn-hsv-observe-car-preserves-state))))

(defthm fn-hsv-log-reserve-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (mv-nth 0 (fn-hsv-log-reserve oc hist)) (fn-olr-ocfg-reserve oc)))
 :hints (("Goal" :in-theory '((:type-prescription fn-hsv-observe) mv-nth zp car-cons cdr-cons (:executable-counterpart zp) fn-hsv-log-reserve fn-olr-ocfg-reserve fn-hsv-observe-car-is-reference fn-hsv-observe-history-of-reference fn-rcon-ocfg-io-keeps-the-store-a-state
 fn-hsv-observe-car-preserves-state fn-hsv-observe-car-preserves-history))))

(defthm fn-hsv-log-reserve-preserves-invariant
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (mv-nth 0 (fn-hsv-log-reserve oc hist))))
 :hints (("Goal" :in-theory '((:type-prescription fn-hsv-observe) mv-nth zp car-cons cdr-cons (:executable-counterpart zp) fn-hsv-log-reserve fn-hsv-observe-car-preserves-invariant
 (:executable-counterpart fn-psrv-io-safep)))))

(in-theory (disable fn-hsv-log-reserve))

(defun fn-hsv-log-order (oc fn-hist)
 (declare (xargs :stobjs fn-hist :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
 :guard-hints (("Goal" :in-theory (union-theories '(fn-hsv-observe-car-preserves-state) (theory 'ground-zero))))))
 (mv-let (oc fn-hist) (fn-hsv-observe oc :record-file :ok fn-hist)
    (mv-let (oc fn-hist) (fn-hsv-observe oc :record-link :ok fn-hist)
    (mv-let (oc fn-hist) (fn-hsv-observe oc :record-directory :ok fn-hist)
    (mv oc fn-hist)))))

(defthm fn-hsv-log-order-preserves-state
 (implies (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
  (fn-sn-statep (fn-own-store (fn-ocfg-owner (mv-nth 0 (fn-hsv-log-order oc hist))))))
 :hints (("Goal" :in-theory '((:type-prescription fn-hsv-observe) mv-nth zp car-cons cdr-cons (:executable-counterpart zp) fn-hsv-log-order fn-hsv-observe-car-preserves-state))))

(defthm fn-hsv-log-order-preserves-history
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (fn-hist-of-storep (mv-nth 1 (fn-hsv-log-order oc hist))
                    (fn-own-store (fn-ocfg-owner (mv-nth 0 (fn-hsv-log-order oc hist))))))
 :hints (("Goal" :in-theory '((:type-prescription fn-hsv-observe) mv-nth zp car-cons cdr-cons (:executable-counterpart zp) fn-hsv-log-order fn-hsv-observe-car-preserves-history fn-hsv-observe-car-preserves-state))))

(defthm fn-hsv-log-order-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (mv-nth 0 (fn-hsv-log-order oc hist)) (fn-olr-ocfg-order oc)))
 :hints (("Goal" :in-theory '((:type-prescription fn-hsv-observe) mv-nth zp car-cons cdr-cons (:executable-counterpart zp) fn-hsv-log-order fn-olr-ocfg-order fn-hsv-observe-car-is-reference fn-hsv-observe-history-of-reference fn-rcon-ocfg-io-keeps-the-store-a-state
 fn-hsv-observe-car-preserves-state fn-hsv-observe-car-preserves-history))))

(defthm fn-hsv-log-order-preserves-invariant
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (mv-nth 0 (fn-hsv-log-order oc hist))))
 :hints (("Goal" :in-theory '((:type-prescription fn-hsv-observe) mv-nth zp car-cons cdr-cons (:executable-counterpart zp) fn-hsv-log-order fn-hsv-observe-car-preserves-invariant
 (:executable-counterpart fn-psrv-io-safep)))))

(in-theory (disable fn-hsv-log-order))

(defthm fn-hsv-log-reserve-car-preserves-invariant
 (implies (fn-lgoc-invariantp oc) (fn-lgoc-invariantp (car (fn-hsv-log-reserve oc hist))))
 :hints (("Goal" :use fn-hsv-log-reserve-preserves-invariant
 :in-theory (union-theories '(mv-nth zp) (theory 'ground-zero)))))
(defthm fn-hsv-log-order-car-preserves-invariant
 (implies (fn-lgoc-invariantp oc) (fn-lgoc-invariantp (car (fn-hsv-log-order oc hist))))
 :hints (("Goal" :use fn-hsv-log-order-preserves-invariant
 :in-theory (union-theories '(mv-nth zp) (theory 'ground-zero)))))
