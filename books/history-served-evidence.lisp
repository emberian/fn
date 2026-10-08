; Evidence reports consult the resident history, including every fallback.
(in-package "ACL2")
(include-book "history-served-find")
(include-book "control-evidence")

(defun fn-ctl-row-control-resident (msgid fn-hist)
  (declare (xargs :stobjs fn-hist :guard t))
  (let ((e (fn-hist-control-event msgid fn-hist)))
    (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil)))

(defthm fn-ctl-row-control-resident-is-reference
 (equal (fn-ctl-row-control-resident msgid hist) (fn-ctl-row-control msgid hist))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-ctl-row-control-resident fn-ctl-row-control fn-hist-control-event-is-reference)))))
(in-theory (disable fn-ctl-row-control-resident))

(defun fn-ctl-article-plan-resident (a verdicts fn-hist configs)
  (declare (xargs :stobjs fn-hist :guard t))
  (if (consp a)
      (let* ((m (fn-article-msgid a))
             (e (fn-hist-control-event m fn-hist))
             (control (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil))
             (target (fn-ctl-control-target control)))
        (if target
            (fn-ctl-w-with-tlocks
             (fn-ctl-withdrawal-plan
              m (fn-ctl-lookup-verdict m verdicts) target
              (fn-ctl-control-keys control)
              (fn-ctl-config-at (fn-store-event-txid e) configs))
             (fn-ctl-control-locks (fn-ctl-row-control-resident target fn-hist)))
          nil))
    nil))

(defthm fn-ctl-article-plan-resident-is-reference
 (equal (fn-ctl-article-plan-resident a verdicts hist configs) (fn-ctl-article-plan a verdicts hist configs))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-ctl-article-plan-resident fn-ctl-article-plan fn-ctl-row-control-resident-is-reference fn-hist-control-event-is-reference)))))
(in-theory (disable fn-ctl-article-plan-resident))

(defun fn-cev-plan-resident (a verdicts fn-hist configs)
  (declare (xargs :stobjs fn-hist :guard t))
  (fn-ctl-article-plan-resident a verdicts fn-hist configs))

(defthm fn-cev-plan-resident-is-reference
 (equal (fn-cev-plan-resident a verdicts hist configs) (fn-cev-plan a verdicts hist configs))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-cev-plan-resident fn-cev-plan fn-ctl-row-control-resident-is-reference fn-ctl-article-plan-resident-is-reference fn-hist-control-event-is-reference)))))
(in-theory (disable fn-cev-plan-resident))

(defun fn-cev-evidence-report-resident (msgid ws raw verdicts fn-hist configs)
  (declare (xargs :stobjs fn-hist :guard t))
  (let ((a (fn-cev-find-article msgid raw)))
    (append (fn-nls-text "evidence message-id=") (fn-cev-string msgid)
            (if (consp a)
                (append (fn-nls-text " stored=yes txid=")
                        (fn-cev-txid-words
                         (fn-store-event-txid (fn-hist-control-event msgid fn-hist)))
                        (fn-nls-text " verdict=")
                        (fn-cev-verdict-word (fn-ctl-lookup-verdict msgid verdicts))
                        *fn-nls-lf*
                        (fn-cev-decision-line (fn-cev-plan-resident a verdicts fn-hist configs)))
              (append (fn-nls-text " stored=no") *fn-nls-lf*))
            (fn-cev-targeting-lines msgid ws a verdicts))))

(defthm fn-cev-evidence-report-resident-is-reference
 (equal (fn-cev-evidence-report-resident msgid ws raw verdicts hist configs) (fn-cev-evidence-report msgid ws raw verdicts hist configs))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-cev-evidence-report-resident fn-cev-evidence-report fn-ctl-row-control-resident-is-reference fn-ctl-article-plan-resident-is-reference fn-cev-plan-resident-is-reference fn-hist-control-event-is-reference)))))
(in-theory (disable fn-cev-evidence-report-resident))

(defun fn-cev-report-resident (kind ws raw verdicts fn-hist configs)
  (declare (xargs :stobjs fn-hist :guard t))
  (cond ((and (consp kind) (equal (car kind) :moderation-list))
         (fn-cev-moderation-report (cdr kind) ws raw verdicts configs))
        ((consp kind)
         (fn-cev-evidence-report-resident (cdr kind) ws raw verdicts fn-hist configs))
        (t (fn-cev-log-report ws))))

(defthm fn-cev-report-resident-is-reference
 (equal (fn-cev-report-resident kind ws raw verdicts hist configs) (fn-cev-report kind ws raw verdicts hist configs))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-cev-report-resident fn-cev-report fn-ctl-row-control-resident-is-reference fn-ctl-article-plan-resident-is-reference fn-cev-plan-resident-is-reference fn-cev-evidence-report-resident-is-reference fn-hist-control-event-is-reference)))))
(in-theory (disable fn-cev-report-resident))

(defun fn-cev-live-report-resident (kind oc fn-hist)
 (declare (xargs :stobjs fn-hist :guard t
                 :guard-hints (("Goal" :in-theory (enable fn-oig-kindp)))))
 (let* ((o (fn-ocfg-owner oc)) (v (fn-own-view o)) (s (fn-own-store o)))
  (if (ec-call (fn-oig-kindp kind))
      (ec-call (fn-oig-report (cdr kind) (fn-own-view-archive v)))
    (fn-cev-report-resident kind (fn-own-view-withdrawals v) (fn-own-view-raw v)
      (fn-own-view-verdicts v) fn-hist (fn-sn-config-history s)))))
(defthm fn-cev-live-report-resident-is-reference
 (implies (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc)))
  (equal (fn-cev-live-report-resident kind oc hist) (fn-cev-live-report kind oc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-cev-live-report-resident fn-cev-live-report fn-cev-report-resident-is-reference
 fn-hist-of-storep)))))
(in-theory (disable fn-cev-live-report-resident))
