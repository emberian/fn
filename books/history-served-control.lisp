(in-package "ACL2")

(include-book "history-served-find")
(include-book "history-served-row-table")

(include-book "control-visible-effect")

(defun fn-ctl-row-event-served (m files fn-hist)
  (declare (xargs :stobjs fn-hist :guard t) (ignore files))
  (if (stringp m)
      (let ((rs (fn-hist-msgid-records m fn-hist)))
        (if (consp rs)
            (let* ((r (car rs))
                   (k (fn-record-sequence r))
                   (e (if (and (natp k) (< k (fn-hist-count fn-hist)))
                          (fn-hist-at k fn-hist)
                        nil)))
              (if (and e
                       (equal (fn-ctl-event-row e) r)
                       (not (member-equal r (cdr rs))))
                  e
                (fn-hist-control-event m fn-hist)))
          nil))
    (fn-hist-control-event m fn-hist)))

(defthm fn-ctl-row-event-served-is-fx
  (implies (equal hist (fn-sf-records files))
           (equal (fn-ctl-row-event-served m files hist)
                  (fn-ctl-row-event-fx m files hist)))
  :hints (("Goal"
           :in-theory
           (e/d (fn-ctl-row-event-served fn-ctl-row-event-fx
                                         fn-ctl-row-event-ix
                                         fn-ctl-article-withdrawals-ix
                                         fn-ctl-resolve-tlocks-ix)
                (fn-ctl-row-event fn-ctl-event-row
                                  fn-ctl-row-control-ix
                                  fn-ctl-article-plan-ix
                                  fn-ctl-withdrawal-plan
                                  fn-ctl-w-with-tlocks
                                  fn-ctl-control-locks
                                  fn-ctl-lookup-verdict
                                  fn-ctl-config-at
                                  fn-ctl-articles-withdrawals
                                  fn-ctl-set-tlocks
                                  fn-ctl-targets-p
                                  fn-ctl-prepend
                                  fn-sf-records
                                  fn-ctl-control-target
                                  fn-ctl-control-keys
                                  fn-store-event-txid
                                  fn-article-msgid
                                  fn-ctl-withdrawalp)))))

(in-theory (disable fn-ctl-row-event-served))

(defun fn-ctl-row-control-served (msgid files fn-hist)
  (declare (xargs :stobjs fn-hist :guard t))
  (let ((e (fn-ctl-row-event-served msgid files fn-hist)))
    (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil)))

(defthm fn-ctl-row-control-served-is-fx
  (implies (equal hist (fn-sf-records files))
           (equal (fn-ctl-row-control-served msgid files hist)
                  (fn-ctl-row-control-fx msgid files hist)))
  :hints (("Goal"
           :in-theory
           (e/d (fn-ctl-row-control-served fn-ctl-row-control-fx
                                           fn-ctl-row-control-ix
                                           fn-ctl-article-withdrawals-ix
                                           fn-ctl-resolve-tlocks-ix)
                (fn-ctl-row-event fn-ctl-event-row
                                  fn-ctl-row-event-ix
                                  fn-ctl-article-plan-ix
                                  fn-ctl-withdrawal-plan
                                  fn-ctl-w-with-tlocks
                                  fn-ctl-control-locks
                                  fn-ctl-lookup-verdict
                                  fn-ctl-config-at
                                  fn-ctl-articles-withdrawals
                                  fn-ctl-set-tlocks
                                  fn-ctl-targets-p
                                  fn-ctl-prepend
                                  fn-sf-records
                                  fn-ctl-control-target
                                  fn-ctl-control-keys
                                  fn-store-event-txid
                                  fn-article-msgid
                                  fn-ctl-withdrawalp)))))

(in-theory (disable fn-ctl-row-control-served))

(defun fn-ctl-article-plan-served (a verdicts files fn-hist configs)
  (declare (xargs :stobjs fn-hist :guard t))
  (if (consp a)
      (let* ((m (fn-article-msgid a))
             (e (fn-ctl-row-event-served m files fn-hist))
             (control (if e
                          (fn-hf-control (fn-held-facts (fn-ctl-event-row e)))
                        nil))
             (target (fn-ctl-control-target control)))
        (if target
            (fn-ctl-w-with-tlocks (fn-ctl-withdrawal-plan m
                                                          (fn-ctl-lookup-verdict m
                                                                                 verdicts)
                                                          target
                                                          (fn-ctl-control-keys control)
                                                          (fn-ctl-config-at (fn-store-event-txid e)
                                                                            configs))
                                  (fn-ctl-control-locks (fn-ctl-row-control-served target
                                                                                   files
                                                                                   fn-hist)))
          nil))
    nil))

(defthm fn-ctl-article-plan-served-is-fx
  (implies (equal hist (fn-sf-records files))
           (equal (fn-ctl-article-plan-served a verdicts files hist configs)
                  (fn-ctl-article-plan-fx a verdicts files hist configs)))
  :hints (("Goal"
           :in-theory
           (e/d (fn-ctl-article-plan-served fn-ctl-article-plan-fx
                                            fn-ctl-article-plan-ix
                                            fn-ctl-article-withdrawals-ix
                                            fn-ctl-resolve-tlocks-ix)
                (fn-ctl-row-event fn-ctl-event-row
                                  fn-ctl-row-control-ix
                                  fn-ctl-row-event-ix
                                  fn-ctl-withdrawal-plan
                                  fn-ctl-w-with-tlocks
                                  fn-ctl-control-locks
                                  fn-ctl-lookup-verdict
                                  fn-ctl-config-at
                                  fn-ctl-articles-withdrawals
                                  fn-ctl-set-tlocks
                                  fn-ctl-targets-p
                                  fn-ctl-prepend
                                  fn-sf-records
                                  fn-ctl-control-target
                                  fn-ctl-control-keys
                                  fn-store-event-txid
                                  fn-article-msgid
                                  fn-ctl-withdrawalp)))))

(in-theory (disable fn-ctl-article-plan-served))

(defun fn-ctl-articles-withdrawals-served (arts verdicts files fn-hist configs)
 (declare (ignore files) (xargs :stobjs fn-hist :guard t))
 (let ((tbl (fn-hist-control-row-table nil fn-hist)))
  (fast-alist-free-on-exit
   tbl (fn-ctl-articles-withdrawals-in arts verdicts tbl configs))))

(defthm fn-ctl-article-plan-served-is-reference
  (implies (and (equal hist (fn-sf-records files)) (fn-ctl-rows-okp hist))
           (equal (fn-ctl-article-plan-served a verdicts files hist configs)
                  (fn-ctl-article-plan a verdicts hist configs)))
  :hints (("Goal" :in-theory
           '(fn-ctl-article-plan-served-is-fx fn-ctl-article-plan-fx
             fn-ctl-article-plan-ix fn-ctl-article-plan
             fn-ctl-row-control-ix-is-row-control
             fn-ctl-row-event-ix-is-row-event))))

(defthm fn-ctl-articles-withdrawals-served-is-reference
 (equal (fn-ctl-articles-withdrawals-served arts verdicts files hist configs)
        (fn-ctl-articles-withdrawals arts verdicts hist configs))
 :hints (("Goal" :in-theory '(fn-ctl-articles-withdrawals-served
   fn-hist-control-row-table-is-reference fn-ctl-articles-withdrawals-in-row-table))))

(in-theory (disable fn-ctl-articles-withdrawals-served))

(defun fn-ctl-refresh-withdrawals-served (new old ws verdicts files fn-hist configs)
  (declare (xargs :stobjs fn-hist :guard t))
  (cond ((equal new old) ws)
        ((and (consp new) (equal (cdr new) old))
         (fn-ctl-prepend (let ((plan (fn-ctl-article-plan-served (car new)
                                                                 verdicts
                                                                 files
                                                                 fn-hist
                                                                 configs)))
                           (if (fn-ctl-withdrawalp plan) (list plan) nil))
                         (if (consp (car new))
                             (let ((m (fn-article-msgid (car new))))
                               (if (fn-ctl-targets-p ws m)
                                   (fn-ctl-set-tlocks ws
                                                      m
                                                      (fn-ctl-control-locks (fn-ctl-row-control-served m
                                                                                                       files
                                                                                                       fn-hist)))
                                 ws))
                           ws)))
        (t (fn-ctl-articles-withdrawals-served new verdicts files fn-hist configs))))

(defthm fn-ctl-refresh-withdrawals-served-is-fx
  (implies (and (equal hist (fn-sf-records files)) (fn-ctl-rows-okp hist))
           (equal (fn-ctl-refresh-withdrawals-served new
                                                     old
                                                     ws
                                                     verdicts
                                                     files
                                                     hist
                                                     configs)
                  (fn-ctl-refresh-withdrawals-fx new
                                                 old
                                                 ws
                                                 verdicts
                                                 files
                                                 hist
                                                 configs)))
  :hints (("Goal" :in-theory
           '(fn-ctl-refresh-withdrawals-served fn-ctl-refresh-withdrawals-fx
             fn-ctl-refresh-withdrawals-ix fn-ctl-article-withdrawals-ix
             fn-ctl-resolve-tlocks-ix
             fn-ctl-article-plan-served-is-fx fn-ctl-article-plan-fx
             fn-ctl-row-control-served-is-fx fn-ctl-row-control-fx
             fn-ctl-articles-withdrawals-served-is-reference))))

(in-theory (disable fn-ctl-refresh-withdrawals-served))
