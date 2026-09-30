; Actual refresh/control producer shared by owner completion and recovery.
; This leaf contains the existing indexed FILES readers unchanged. Effect
; annotations reuse decisions in the same refresh; they never compare views.
; Existing withdrawal scans remain existing work, not a new quantum claim.
(in-package "ACL2")
(include-book "control-visible-indexed")

; The same readers over the kernel state FILES instead of its history list:
; the history is held as a snoc-list (books/store-files.lisp), so reading
; (fn-sf-records files) conses it back; each -fx is its -ix with RECORDS =
; (fn-sf-records files) (its logic, by definition), and executes that read
; only on the arms that walk the history (a Message-ID the index does not
; answer, the recovery arm).  The POST's refresh reads none.
(defun fn-ctl-row-event-fx (m files fn-hist)
  (declare (xargs :stobjs fn-hist :guard t
                  :guard-hints (("Goal" :in-theory (e/d (fn-ctl-row-event-ix)
                                                        (fn-cei-msgid-records fn-cei-get fn-ctl-row-event fn-ctl-event-row fn-held-facts fn-hf-control fn-ctl-withdrawal-plan fn-ctl-w-with-tlocks fn-ctl-control-locks fn-ctl-lookup-verdict fn-ctl-config-at fn-ctl-articles-withdrawals fn-ctl-set-tlocks fn-ctl-targets-p fn-ctl-prepend fn-sf-records fn-ctl-control-target fn-ctl-control-keys fn-store-event-txid fn-article-msgid fn-ctl-withdrawalp))))))
  (mbe :logic (fn-ctl-row-event-ix m (fn-sf-records files) fn-hist)
       :exec (if (stringp m)
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
                           (fn-ctl-row-event m (fn-sf-records files))))
                     nil))
               (fn-ctl-row-event m (fn-sf-records files)))))

(defun fn-ctl-row-control-fx (msgid files fn-hist)
  (declare (xargs :stobjs fn-hist :guard t
                  :guard-hints (("Goal" :in-theory (e/d (fn-ctl-row-control-ix)
                                                        (fn-cei-msgid-records fn-cei-get fn-ctl-row-event fn-ctl-event-row fn-held-facts fn-hf-control fn-ctl-withdrawal-plan fn-ctl-w-with-tlocks fn-ctl-control-locks fn-ctl-lookup-verdict fn-ctl-config-at fn-ctl-articles-withdrawals fn-ctl-set-tlocks fn-ctl-targets-p fn-ctl-prepend fn-sf-records fn-ctl-control-target fn-ctl-control-keys fn-store-event-txid fn-article-msgid fn-ctl-withdrawalp))))))
  (mbe :logic (fn-ctl-row-control-ix msgid (fn-sf-records files) fn-hist)
       :exec (let ((e (fn-ctl-row-event-fx msgid files fn-hist)))
               (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil))))

(defun fn-ctl-article-plan-fx (a verdicts files fn-hist configs)
  (declare (xargs :stobjs fn-hist :guard t
                  :guard-hints (("Goal" :in-theory (e/d (fn-ctl-article-plan-ix)
                                                        (fn-cei-msgid-records fn-cei-get fn-ctl-row-event fn-ctl-event-row fn-held-facts fn-hf-control fn-ctl-withdrawal-plan fn-ctl-w-with-tlocks fn-ctl-control-locks fn-ctl-lookup-verdict fn-ctl-config-at fn-ctl-articles-withdrawals fn-ctl-set-tlocks fn-ctl-targets-p fn-ctl-prepend fn-sf-records fn-ctl-control-target fn-ctl-control-keys fn-store-event-txid fn-article-msgid fn-ctl-withdrawalp))))))
  (mbe :logic (fn-ctl-article-plan-ix a verdicts (fn-sf-records files) fn-hist configs)
       :exec (if (consp a)
                 (let* ((m (fn-article-msgid a))
                        (e (fn-ctl-row-event-fx m files fn-hist))
                        (control (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil))
                        (target (fn-ctl-control-target control)))
                   (if target
                       (fn-ctl-w-with-tlocks
                        (fn-ctl-withdrawal-plan
                         m (fn-ctl-lookup-verdict m verdicts) target
                         (fn-ctl-control-keys control)
                         (fn-ctl-config-at (fn-store-event-txid e) configs))
                        (fn-ctl-control-locks (fn-ctl-row-control-fx target files fn-hist)))
                     nil))
               nil)))

(defun fn-ctl-refresh-withdrawals-fx (new old ws verdicts files fn-hist configs)
  (declare (xargs :stobjs fn-hist :guard t
                  :guard-hints (("Goal" :in-theory (e/d (fn-ctl-refresh-withdrawals-ix fn-ctl-article-withdrawals-ix fn-ctl-resolve-tlocks-ix)
                                                        (fn-cei-msgid-records fn-cei-get fn-ctl-row-event fn-ctl-event-row fn-held-facts fn-hf-control fn-ctl-withdrawal-plan fn-ctl-w-with-tlocks fn-ctl-control-locks fn-ctl-lookup-verdict fn-ctl-config-at fn-ctl-articles-withdrawals fn-ctl-set-tlocks fn-ctl-targets-p fn-ctl-prepend fn-sf-records fn-ctl-control-target fn-ctl-control-keys fn-store-event-txid fn-article-msgid fn-ctl-withdrawalp))))))
  (mbe :logic (fn-ctl-refresh-withdrawals-ix new old ws verdicts (fn-sf-records files)
                                             fn-hist configs)
       :exec (cond ((equal new old) ws)
                   ((and (consp new) (equal (cdr new) old))
                    (fn-ctl-prepend
                     (let ((plan (fn-ctl-article-plan-fx (car new) verdicts files
                                                         fn-hist configs)))
                       (if (fn-ctl-withdrawalp plan) (list plan) nil))
                     (if (consp (car new))
                         (let ((m (fn-article-msgid (car new))))
                           (if (fn-ctl-targets-p ws m)
                               (fn-ctl-set-tlocks ws m (fn-ctl-control-locks
                                                        (fn-ctl-row-control-fx m files fn-hist)))
                             ws))
                       ws)))
                   (t (fn-ctl-articles-withdrawals new verdicts (fn-sf-records files)
                                                   configs)))))

; One execution of the existing single-append decisions produces both
; withdrawals and their conservative semantic effect. In particular target
; resolution changes withdrawal reports even when no old article is visible.
(defun fn-ctl-refresh-withdrawals-effect-fx
    (new old ws verdicts files fn-hist configs)
  (declare (xargs :stobjs fn-hist :guard t))
  (cond ((equal new old) (mv ws :preserved))
        ((and (consp new) (equal (cdr new) old))
         (let* ((a (car new))
                (plan (fn-ctl-article-plan-fx a verdicts files fn-hist configs))
                (planp (fn-ctl-withdrawalp plan))
                (m (if (consp a) (fn-article-msgid a) nil))
                (targeted (and (consp a) (fn-ctl-targets-p ws m)))
                (resolved (if targeted
                              (fn-ctl-set-tlocks
                               ws m (fn-ctl-control-locks
                                     (fn-ctl-row-control-fx m files fn-hist)))
                            ws)))
           (mv (fn-ctl-prepend (if planp (list plan) nil) resolved)
               (if (or planp targeted) :changed :preserved))))
        (t (mv (fn-ctl-articles-withdrawals
                new verdicts (fn-sf-records files) configs)
               :changed))))

(defthm fn-ctl-refresh-withdrawals-effect-fx-keeps-value
  (equal (mv-nth 0 (fn-ctl-refresh-withdrawals-effect-fx
                    new old ws verdicts files fn-hist configs))
         (fn-ctl-refresh-withdrawals-fx
          new old ws verdicts files fn-hist configs))
  :hints (("Goal" :in-theory
           (e/d (fn-ctl-refresh-withdrawals-effect-fx
                 fn-ctl-refresh-withdrawals-fx
                 fn-ctl-refresh-withdrawals-ix
                 fn-ctl-article-withdrawals-ix fn-ctl-resolve-tlocks-ix
                 fn-ctl-article-plan-fx fn-ctl-row-control-fx)
                (fn-ctl-article-plan-ix fn-ctl-row-control-ix
                 fn-ctl-targets-p fn-ctl-set-tlocks fn-ctl-prepend
                 fn-ctl-withdrawalp fn-ctl-articles-withdrawals
                 fn-sf-records fn-article-msgid)))))

; Same visible refresh, sharing its existing verdict-growth decision with
; the effect result. A verdict change about an old article is not a plain
; append, even if the raw article list itself has not changed.
(defun fn-ctl-refresh-visible-effect
    (new old old-visible ws old-verdicts verdicts withdrawal-effect)
  (declare (xargs :guard t))
  (cond ((and (equal new old) (equal verdicts old-verdicts))
         (mv old-visible (if (eq withdrawal-effect :preserved)
                             :preserved :changed)))
        ((and (consp new) (equal (cdr new) old))
         (let ((growth (fn-ctl-verdicts-grow-by-p verdicts old-verdicts (car new))))
           (mv (if growth (fn-ctl-visible-add (car new) old-visible old ws verdicts)
                 (fn-ctl-visible-articles new ws verdicts))
               (if (and growth (eq withdrawal-effect :preserved))
                   :preserved :changed))))
        (t (mv (fn-ctl-visible-articles new ws verdicts) :changed))))

(defthm fn-ctl-refresh-visible-effect-keeps-value
  (equal (mv-nth 0 (fn-ctl-refresh-visible-effect
                    new old old-visible ws old-verdicts verdicts effect))
         (fn-ctl-refresh-visible new old old-visible ws old-verdicts verdicts))
  :hints (("Goal" :in-theory
           (e/d (fn-ctl-refresh-visible-effect fn-ctl-refresh-visible)
                (fn-ctl-verdicts-grow-by-p fn-ctl-visible-add
                 fn-ctl-visible-articles)))))

; The preservation tag has this specific conservative meaning. Configuration
; and account authority changes must be combined separately at publication.
(defthm fn-ctl-refresh-visible-effect-preserved-append
  (implies (and (consp new) (equal (cdr new) old)
                (fn-ctl-verdicts-grow-by-p verdicts old-verdicts (car new))
                (eq effect :preserved))
           (eq (mv-nth 1 (fn-ctl-refresh-visible-effect
                          new old old-visible ws old-verdicts verdicts effect))
               :preserved))
  :hints (("Goal" :in-theory
           (e/d (fn-ctl-refresh-visible-effect)
                (fn-ctl-verdicts-grow-by-p fn-ctl-visible-add
                 fn-ctl-visible-articles)))))

; Pre-frontier overlay. Historical rows keep their oldest-selection meaning,
; including rows whose article has expired. The candidate is selected only
; where appending it would be the first row for this exact Message-ID.
(defun fn-ctl-row-event-candidate-fx (m files fn-hist candidate)
  (declare (xargs :stobjs fn-hist :guard t))
  (let ((old (fn-ctl-row-event-fx m files fn-hist)))
    (if old old
      (let ((row (fn-ctl-event-row candidate)))
        (if (and m row (equal (fn-record-msgid row) m)) candidate nil)))))

(defthm fn-ctl-row-event-append-one-selection
  (equal (fn-ctl-row-event m (append records (list candidate)))
         (let ((old (fn-ctl-row-event m records)))
           (if old old
             (let ((row (fn-ctl-event-row candidate)))
               (if (and m row (equal (fn-record-msgid row) m)) candidate nil)))))
  :hints (("Goal" :induct (fn-ctl-row-event m records)
           :in-theory (e/d (fn-ctl-row-event append)
                            (fn-ctl-event-row fn-record-msgid)))))

(defthm fn-ctl-row-event-candidate-fx-is-post-install-selection
  (implies (and (equal fn-hist (fn-sf-records files))
                (fn-ctl-rows-okp (fn-sf-records files)))
           (equal (fn-ctl-row-event-candidate-fx m files fn-hist candidate)
                  (fn-ctl-row-event m (append (fn-sf-records files)
                                             (list candidate)))))
  :hints (("Goal" :use ((:instance fn-ctl-row-event-ix-is-row-event
                                  (records (fn-sf-records files))))
           :in-theory (e/d (fn-ctl-row-event-candidate-fx fn-ctl-row-event-fx)
                            (fn-ctl-row-event fn-ctl-row-event-ix
                             fn-ctl-event-row fn-record-msgid
                             fn-sf-records fn-ctl-rows-okp)))))

(defun fn-ctl-row-control-candidate-fx (m files fn-hist candidate)
  (declare (xargs :stobjs fn-hist :guard t))
  (let ((e (fn-ctl-row-event-candidate-fx m files fn-hist candidate)))
    (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil)))

(defun fn-ctl-article-plan-candidate-fx (a verdicts files fn-hist configs candidate)
  (declare (xargs :stobjs fn-hist :guard t))
  (if (consp a)
      (let* ((m (fn-article-msgid a))
             (e (fn-ctl-row-event-candidate-fx m files fn-hist candidate))
             (control (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil))
             (target (fn-ctl-control-target control)))
        (if target
            (fn-ctl-w-with-tlocks
             (fn-ctl-withdrawal-plan
              m (fn-ctl-lookup-verdict m verdicts) target
              (fn-ctl-control-keys control)
              (fn-ctl-config-at (fn-store-event-txid e) configs))
             (fn-ctl-control-locks
              (fn-ctl-row-control-candidate-fx target files fn-hist candidate)))
          nil))
    nil))

; This preflight accepts only the same append arm used by actual completion.
; A nonappend preparation remains unsupported, rather than cloning history.
; Candidate validity/coordinate/authority and post-yield freshness are carried
; by the owner admission contract, not asserted by the socket adapter.
(defun fn-ctl-append-withdrawals-candidate-effect-fx
    (new old ws verdicts files fn-hist configs candidate)
  (declare (xargs :stobjs fn-hist :guard t))
  (if (and (consp new) (equal (cdr new) old))
      (let* ((a (car new))
             (plan (fn-ctl-article-plan-candidate-fx
                    a verdicts files fn-hist configs candidate))
             (planp (fn-ctl-withdrawalp plan))
             (m (if (consp a) (fn-article-msgid a) nil))
             (targeted (and (consp a) (fn-ctl-targets-p ws m)))
             (resolved (if targeted
                           (fn-ctl-set-tlocks
                            ws m (fn-ctl-control-locks
                                  (fn-ctl-row-control-candidate-fx
                                   m files fn-hist candidate)))
                         ws)))
        (mv (fn-ctl-prepend (if planp (list plan) nil) resolved)
            (if (or planp targeted) :changed :preserved)))
    (mv ws :unknown)))

(defthm fn-ctl-article-plan-candidate-fx-is-post-install-plan
  (implies (and (equal fn-hist (fn-sf-records files))
                (fn-ctl-rows-okp (fn-sf-records files)))
           (equal (fn-ctl-article-plan-candidate-fx
                   a verdicts files fn-hist configs candidate)
                  (fn-ctl-article-plan
                   a verdicts (append (fn-sf-records files) (list candidate)) configs)))
  :hints (("Goal" :in-theory
           (e/d (fn-ctl-article-plan-candidate-fx fn-ctl-article-plan
                 fn-ctl-row-control-candidate-fx fn-ctl-row-control)
                (fn-ctl-row-event-candidate-fx fn-ctl-row-event
                 fn-ctl-event-row fn-sf-records fn-ctl-rows-okp
                 fn-ctl-control-target fn-ctl-control-keys
                 fn-ctl-withdrawal-plan fn-ctl-w-with-tlocks
                 fn-ctl-control-locks fn-ctl-config-at
                 fn-ctl-lookup-verdict fn-store-event-txid
                 fn-article-msgid fn-held-facts fn-hf-control)))))

(defthm fn-ctl-append-withdrawals-candidate-effect-fx-keeps-post-install-value
  (implies (and (equal fn-hist (fn-sf-records files))
                (fn-ctl-rows-okp (fn-sf-records files))
                (consp new) (equal (cdr new) old))
           (equal (mv-nth 0 (fn-ctl-append-withdrawals-candidate-effect-fx
                            new old ws verdicts files fn-hist configs candidate))
                  (fn-ctl-refresh-withdrawals
                   new old ws verdicts
                   (append (fn-sf-records files) (list candidate)) configs)))
  :hints (("Goal" :in-theory
           (e/d (fn-ctl-append-withdrawals-candidate-effect-fx
                 fn-ctl-refresh-withdrawals fn-ctl-article-withdrawals
                 fn-ctl-resolve-tlocks fn-ctl-row-control-candidate-fx
                 fn-ctl-row-control)
                (fn-ctl-article-plan-candidate-fx fn-ctl-article-plan
                 fn-ctl-row-event-candidate-fx fn-ctl-row-event
                 fn-ctl-event-row fn-sf-records fn-ctl-rows-okp
                 fn-ctl-control-locks fn-ctl-prepend fn-ctl-targets-p
                 fn-ctl-set-tlocks fn-ctl-withdrawalp
                 fn-article-msgid fn-held-facts fn-hf-control)))))
