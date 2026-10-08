; The actual host readers: suffix sync and proved cache-only folds.
(in-package "ACL2")
(include-book "owner-history-sync")

(defun fn-owner-record-octets (fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :guard (boundp-global 'fn-owner state)))
  (mv-let (fn-hist state)
      (fn-host-hist-sync (fn-owner-store state) fn-hist state)
    (let* ((cache (if (boundp-global 'fn-owner-record-octets state)
                    (f-get-global 'fn-owner-record-octets state)
                  nil))
         (bytes (fn-hist-bytes-served cache fn-hist))
         (state (f-put-global 'fn-owner-record-octets
                              (cons (fn-hist-count fn-hist) bytes) state)))
      (mv bytes fn-hist state))))

(defun fn-owner-record-debt (fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :guard (boundp-global 'fn-owner state)))
  (mv-let (fn-hist state)
      (fn-host-hist-sync (fn-owner-store state) fn-hist state)
    (let* ((cache (if (boundp-global 'fn-owner-record-debt state)
                    (f-get-global 'fn-owner-record-debt state)
                  nil))
         (debt (fn-hist-debt-served cache fn-hist))
         (state (f-put-global 'fn-owner-record-debt
                              (cons (fn-hist-count fn-hist) debt) state)))
      (mv debt fn-hist state))))

(defun fn-owner-carried-usage (evidence fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :guard (boundp-global 'fn-owner state)))
  (mv-let (fn-hist state)
      (fn-host-hist-sync (fn-owner-store state) fn-hist state)
    (let* ((cache (if (boundp-global 'fn-owner-carried-usage state)
                    (f-get-global 'fn-owner-carried-usage state)
                  nil))
         (tally (fn-hist-usage-served cache fn-hist))
         (state (f-put-global 'fn-owner-carried-usage
                              (cons (fn-hist-count fn-hist) tally) state)))
      (mv (fn-pcb-tally-get evidence tally) fn-hist state))))

(defthm fn-host-hist-sync-count-monotone
  (<= (fn-hist-count hist)
      (fn-hist-count (mv-nth 0 (fn-host-hist-sync store hist st))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-hist-served-sync-count-monotone
                                   (files (fn-sn-files store))))
           :in-theory (enable fn-host-hist-sync))))

(defthm fn-owner-record-debt-preserves-history-caches
  (implies (fn-owner-history-cache-statep (fn-hist-count hist) st)
           (fn-owner-history-cache-statep
            (fn-hist-count (mv-nth 1 (fn-owner-record-debt hist st)))
            (mv-nth 2 (fn-owner-record-debt hist st))))
  :hints (("Goal"
           :use ((:instance fn-host-hist-sync-count-monotone
                            (store (fn-owner-store st)))
                 (:instance fn-owner-history-cache-statep-monotone
                            (n (fn-hist-count hist))
                            (m (fn-hist-count (mv-nth 0 (fn-host-hist-sync
                                                       (fn-owner-store st) hist st))))))
           :in-theory (e/d (fn-owner-record-debt fn-owner-history-cache-statep
                             fn-hist-cache-ready-p fn-hist-debt-served)
                            (fn-hist-debt-advance fn-host-hist-sync)))))

(defthm fn-owner-record-octets-preserves-history-caches
  (implies (fn-owner-history-cache-statep (fn-hist-count hist) st)
           (fn-owner-history-cache-statep
            (fn-hist-count (mv-nth 1 (fn-owner-record-octets hist st)))
            (mv-nth 2 (fn-owner-record-octets hist st))))
  :hints (("Goal"
           :use ((:instance fn-host-hist-sync-count-monotone
                            (store (fn-owner-store st)))
                 (:instance fn-owner-history-cache-statep-monotone
                            (n (fn-hist-count hist))
                            (m (fn-hist-count (mv-nth 0 (fn-host-hist-sync
                                                       (fn-owner-store st) hist st))))))
           :in-theory (e/d (fn-owner-record-octets fn-owner-history-cache-statep
                             fn-hist-cache-ready-p fn-hist-bytes-served)
                            (fn-hist-octets-advance fn-host-hist-sync)))))

(defthm fn-owner-carried-usage-preserves-history-caches
  (implies (fn-owner-history-cache-statep (fn-hist-count hist) st)
           (fn-owner-history-cache-statep
            (fn-hist-count (mv-nth 1 (fn-owner-carried-usage evidence hist st)))
            (mv-nth 2 (fn-owner-carried-usage evidence hist st))))
  :hints (("Goal"
           :use ((:instance fn-host-hist-sync-count-monotone
                            (store (fn-owner-store st)))
                 (:instance fn-owner-history-cache-statep-monotone
                            (n (fn-hist-count hist))
                            (m (fn-hist-count (mv-nth 0 (fn-host-hist-sync
                                                       (fn-owner-store st) hist st))))))
           :in-theory (e/d (fn-owner-carried-usage fn-owner-history-cache-statep
                             fn-hist-cache-ready-p)
                            (fn-hist-usage-served fn-host-hist-sync)))))

(in-theory (disable fn-owner-record-octets fn-owner-record-debt fn-owner-carried-usage))
