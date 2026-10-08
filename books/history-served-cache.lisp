; Served carried folds have no whole-history disk fallback.
(in-package "ACL2")
(include-book "history-columns-store")
(include-book "state-globals")

(defun fn-hist-cache-ready-p (cache count numeric)
  (declare (xargs :guard t))
  (and (consp cache) (natp (car cache))
       (or (not numeric) (natp (cdr cache)))
       (<= (car cache) (nfix count))))

(defun fn-hist-debt-served (cache fn-hist)
  (declare (xargs :stobjs fn-hist :guard t))
  (if (fn-hist-cache-ready-p cache (fn-hist-count fn-hist) t)
      (fn-hist-debt-advance (car cache) (fn-hist-count fn-hist) (cdr cache) fn-hist)
    (prog2$ (er hard? 'fn-hist-debt-served "Owner debt cache is not initialized.") 0)))

(defun fn-hist-bytes-served (cache fn-hist)
  (declare (xargs :stobjs fn-hist :guard t))
  (if (fn-hist-cache-ready-p cache (fn-hist-count fn-hist) t)
      (fn-hist-octets-advance (car cache) (fn-hist-count fn-hist) (cdr cache) fn-hist)
    (prog2$ (er hard? 'fn-hist-bytes-served "Owner byte cache is not initialized.") 0)))

(defun fn-hist-usage-served (cache fn-hist)
  (declare (xargs :stobjs fn-hist :guard t))
  (if (fn-hist-cache-ready-p cache (fn-hist-count fn-hist) nil)
      (fn-hist-tally-advance (car cache) (fn-hist-count fn-hist) (cdr cache) fn-hist)
    (prog2$ (er hard? 'fn-hist-usage-served "Owner usage cache is not initialized.") nil)))

(defthm fn-hist-debt-served-is-carried
  (implies (fn-hist-cache-ready-p cache (fn-hist-count hist) t)
           (equal (fn-hist-debt-served cache hist)
                  (fn-hist-debt-carried cache s hist)))
  :hints (("Goal" :in-theory (enable fn-hist-debt-carried))))

(defthm fn-hist-bytes-served-is-carried
  (implies (fn-hist-cache-ready-p cache (fn-hist-count hist) t)
           (equal (fn-hist-bytes-served cache hist)
                  (fn-hist-bytes-carried cache s hist)))
  :hints (("Goal" :in-theory (enable fn-hist-bytes-carried))))

(defthm fn-hist-usage-served-is-carried
  (implies (fn-hist-cache-ready-p cache (fn-hist-count hist) nil)
           (equal (fn-hist-usage-served cache hist)
                  (fn-hist-usage-carried cache s hist)))
  :hints (("Goal" :in-theory (enable fn-hist-usage-carried))))

(defthm fn-hist-cache-ready-p-monotone
  (implies (and (fn-hist-cache-ready-p cache n numeric)
                (<= (nfix n) (nfix m)))
           (fn-hist-cache-ready-p cache m numeric)))

(defun fn-owner-history-cache-statep (count state)
  (declare (xargs :stobjs state :guard t))
  (and (boundp-global 'fn-owner-record-octets state)
       (boundp-global 'fn-owner-record-debt state)
       (boundp-global 'fn-owner-carried-usage state)
       (fn-hist-cache-ready-p (f-get-global 'fn-owner-record-octets state) count t)
       (fn-hist-cache-ready-p (f-get-global 'fn-owner-record-debt state) count t)
       (fn-hist-cache-ready-p (f-get-global 'fn-owner-carried-usage state) count nil)))

(defun fn-owner-history-cache-put (octets debt usage state)
  (declare (xargs :stobjs state :guard t))
  (let* ((state (f-put-global 'fn-owner-record-octets octets state))
         (state (f-put-global 'fn-owner-record-debt debt state))
         (state (f-put-global 'fn-owner-carried-usage usage state)))
    state))

(defthm fn-owner-history-cache-put-establishes-ready
  (implies (and (fn-hist-cache-ready-p octets count t)
                (fn-hist-cache-ready-p debt count t)
                (fn-hist-cache-ready-p usage count nil))
           (fn-owner-history-cache-statep
            count (fn-owner-history-cache-put octets debt usage st))))

(defthm fn-owner-history-cache-statep-of-other-global-put
  (implies (not (member-eq key '(fn-owner-record-octets fn-owner-record-debt
                                fn-owner-carried-usage)))
           (equal (fn-owner-history-cache-statep count (f-put-global key value st))
                  (fn-owner-history-cache-statep count st))))

(defthm fn-owner-history-cache-statep-monotone
  (implies (and (fn-owner-history-cache-statep n st)
                (<= (nfix n) (nfix m)))
           (fn-owner-history-cache-statep m st)))

(defthm fn-hist-debt-advance-natural
  (natp (fn-hist-debt-advance k count debt fn-hist))
  :rule-classes :type-prescription)

(defthm fn-hist-octets-advance-natural
  (implies (natp sum) (natp (fn-hist-octets-advance k count sum fn-hist)))
  :rule-classes :type-prescription)

(defun fn-owner-history-cache-startup (fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :guard t))
  (let ((count (fn-hist-count fn-hist)))
    (fn-owner-history-cache-put
     (cons count (fn-hist-octets-advance 0 count 0 fn-hist))
     (cons count (fn-hist-debt-advance 0 count 0 fn-hist))
     (cons count (fn-hist-tally-advance 0 count nil fn-hist)) state)))

(defthm fn-owner-history-cache-startup-establishes-ready
  (fn-owner-history-cache-statep (fn-hist-count hist)
                                (fn-owner-history-cache-startup hist st)))

(defthm fn-owner-history-cache-startup-keeps-other-globals
  (implies (not (member-eq key '(fn-owner-record-octets fn-owner-record-debt
                                fn-owner-carried-usage)))
           (and (equal (boundp-global key (fn-owner-history-cache-startup fn-hist state))
                       (boundp-global key state))
                (equal (f-get-global key (fn-owner-history-cache-startup fn-hist state))
                       (f-get-global key state)))))

(in-theory (disable fn-hist-cache-ready-p fn-hist-debt-served fn-hist-bytes-served
                    fn-hist-usage-served fn-owner-history-cache-statep
                    fn-owner-history-cache-put fn-owner-history-cache-startup))
