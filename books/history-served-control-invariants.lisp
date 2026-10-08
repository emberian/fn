; View consistency is independent of which history supplies withdrawal decisions.
(in-package "ACL2")
(include-book "history-served-control")

(defthm fn-ctl-served-plan-names-cause
 (implies (fn-ctl-withdrawalp (fn-ctl-article-plan-served a verdicts files hist configs))
  (equal (fn-ctl-w-cause (fn-ctl-article-plan-served a verdicts files hist configs)) (fn-article-msgid a)))
 :hints (("Goal" :in-theory (e/d (fn-ctl-article-plan-served)
 (fn-ctl-w-cause fn-ctl-control-target fn-ctl-control-keys fn-ctl-control-locks fn-ctl-withdrawal-plan fn-ctl-withdrawalp fn-ctl-config-at fn-ctl-row-event-served fn-ctl-row-control-served fn-ctl-w-with-tlocks fn-ctl-lookup-verdict))
 :use ((:instance fn-ctl-withdrawal-plan-names-its-cause
 (cause (fn-article-msgid a))
 (verdict (fn-ctl-lookup-verdict (fn-article-msgid a) verdicts))
 (target (fn-ctl-control-target (fn-hf-control (fn-held-facts (fn-ctl-event-row (fn-ctl-row-event-served (fn-article-msgid a) files hist))))))
 (keys (fn-ctl-control-keys (fn-hf-control (fn-held-facts (fn-ctl-event-row (fn-ctl-row-event-served (fn-article-msgid a) files hist))))))
 (cfg (fn-ctl-config-at (fn-store-event-txid (fn-ctl-row-event-served (fn-article-msgid a) files hist)) configs)))))))
(defthm fn-ctl-served-causes-all-p
 (fn-ctl-causes-all-p
 (if (fn-ctl-withdrawalp (fn-ctl-article-plan-served a verdicts files hist configs))
  (list (fn-ctl-article-plan-served a verdicts files hist configs)) nil)
 (fn-article-msgid a))
 :hints (("Goal" :in-theory '(fn-ctl-causes-all-p fn-ctl-served-plan-names-cause car-cons cdr-cons (:executable-counterpart consp)))))
(defthm fn-ctl-visible-of-cause-records-and-verdicts
 (implies (and (fn-ctl-causes-all-p recs (fn-article-msgid a))
               (not (member-equal (fn-article-msgid a) (fn-article-msgids old)))
               (fn-ctl-verdicts-grow-by-p verdicts old-verdicts a))
  (equal (fn-ctl-visible-articles old (fn-ctl-prepend recs ws) verdicts)
         (fn-ctl-visible-articles old ws old-verdicts)))
 :hints (("Goal" :in-theory (e/d (fn-ctl-visible-articles fn-ctl-verdicts-grow-by-p) (fn-ctl-visible-filter fn-ctl-causes-all-p))
 :use ((:instance fn-ctl-has-msgid-p-means-member-msgids (m (fn-article-msgid a)) (arts old))
       (:instance fn-ctl-visible-filter-of-absent-causes-append (c (fn-article-msgid a)) (xs old) (arts old))))))
(defthm fn-ctl-visible-of-cause-records-and-resolved
 (implies (and (fn-ctl-causes-all-p recs (fn-article-msgid a))
               (not (member-equal (fn-article-msgid a) (fn-article-msgids old)))
               (fn-ctl-verdicts-grow-by-p verdicts old-verdicts a))
  (equal (fn-ctl-visible-articles old
          (fn-ctl-prepend recs (fn-ctl-set-tlocks ws (fn-article-msgid a) locks)) verdicts)
         (fn-ctl-visible-articles old ws old-verdicts)))
 :hints (("Goal" :in-theory (e/d (fn-ctl-visible-articles) (fn-ctl-visible-filter fn-ctl-causes-all-p
 fn-ctl-set-tlocks fn-ctl-verdicts-grow-by-p fn-ctl-visible-of-cause-records-and-verdicts))
 :use ((:instance fn-ctl-visible-of-cause-records-and-verdicts
        (ws (fn-ctl-set-tlocks ws (fn-article-msgid a) locks)))
       (:instance fn-ctl-visible-filter-of-set-tlocks-other
        (m (fn-article-msgid a)) (xs old) (arts old) (verdicts old-verdicts))))))
(defthm fn-ctl-served-refresh-visible-is-visible
 (implies (and (equal old-visible (fn-ctl-visible-articles old ws old-verdicts))
               (no-duplicatesp-equal (fn-article-msgids new)))
  (let ((ws2 (fn-ctl-refresh-withdrawals-served new old ws verdicts files hist configs)))
   (equal (fn-ctl-refresh-visible new old old-visible ws2 old-verdicts verdicts)
          (fn-ctl-visible-articles new ws2 verdicts))))
 :hints (("Goal" :use ((:instance fn-ctl-visible-of-cause-records-and-verdicts
 (a (car new)) (old (cdr new))
 (recs (if (fn-ctl-withdrawalp (fn-ctl-article-plan-served (car new) verdicts files hist configs))
 (list (fn-ctl-article-plan-served (car new) verdicts files hist configs)) nil)))
 (:instance fn-ctl-visible-of-cause-records-and-resolved
 (a (car new)) (old (cdr new))
 (recs (if (fn-ctl-withdrawalp (fn-ctl-article-plan-served (car new) verdicts files hist configs))
 (list (fn-ctl-article-plan-served (car new) verdicts files hist configs)) nil))
 (locks (fn-ctl-control-locks (fn-ctl-row-control-served (fn-article-msgid (car new)) files hist)))))
 :in-theory (e/d (fn-ctl-visible-add-is-visible
 fn-ctl-refresh-withdrawals-served fn-ctl-refresh-visible)
 (fn-ctl-visible-add fn-ctl-visible-articles fn-ctl-verdicts-grow-by-p
 fn-ctl-articles-withdrawals-served fn-ctl-prepend-is-append fn-ctl-set-tlocks fn-ctl-row-control-served fn-ctl-article-plan-served)))))

(defthm fn-ctl-served-refresh-state-is-visible
  (implies (and (equal old-archive (fn-ctl-visible-state old-p ws old-verdicts))
                (equal old-raw (fn-state-articles old-p))
                (no-duplicatesp-equal (fn-article-msgids (fn-state-articles new-p))))
           (let ((ws2 (fn-ctl-refresh-withdrawals-served
                       (fn-state-articles new-p) old-raw ws verdicts files hist configs)))
             (equal (fn-ctl-visible-state-of
                     new-p
                     (fn-ctl-refresh-visible (fn-state-articles new-p) old-raw
                                            (fn-state-articles old-archive)
                                            ws2 old-verdicts verdicts))
                    (fn-ctl-visible-state new-p ws2 verdicts))))
  :hints (("Goal" :in-theory (e/d (fn-ctl-visible-state)
                                  (fn-ctl-refresh-visible fn-ctl-refresh-withdrawals-served
                                   fn-ctl-visible-articles fn-ctl-visible-state-of))
           :use ((:instance fn-ctl-served-refresh-visible-is-visible
                            (new (fn-state-articles new-p))
                            (old (fn-state-articles old-p))
                            (old-visible (fn-ctl-visible-articles
                                          (fn-state-articles old-p) ws old-verdicts)))))))
