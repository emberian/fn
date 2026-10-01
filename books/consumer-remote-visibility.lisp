; Bounded current-view lookup for EACH dense event, before raw query matching.
; Current view children come only from the installed owner readout under its
; retained source span. No supplied shape grants visibility/source authority.
(in-package "ACL2")
(include-book "consumer-remote-scan")
(include-book "control-authority")
(include-book "peer-inbound")

; Fixed10: key, event, its article Message-ID, visible suffix, withdrawn root,
; withdrawn suffix, withdrawal-record suffix, phase, selected target.
(defun fn-crv-state (key row msgid visible withdrawn scan records phase target)
 (declare (xargs :guard t))
 (list :remote-visibility key row msgid visible withdrawn scan records phase target))

(defun fn-crv-begin (key row current-view)
 (declare (xargs :guard t))
 (let ((article (fn-crps-row-article row)))
  (if (not article) '(:excluded :nonarticle)
   (let ((withdrawn (fn-cp-nth 8 current-view)))
    (list :yield (fn-crv-state key row (fn-record-msgid article)
      (fn-state-articles (fn-cp-nth 2 current-view)) withdrawn withdrawn
      (fn-cp-nth 6 current-view) :own-withdrawn nil))))))

; One maintained view row or withdrawal cell per tick; no FnHist prefix walk,
; whole state validator, arbitrary window, or inference from catalog gaps.
; Withdrawn results contain the TARGET article, never the cause's content or
; groups. Query selection and bounded READ projection still precede reports.
(defun fn-crv-tick (s current-key)
 (declare (xargs :guard t))
 (let ((key (fn-cp-nth 1 s)) (row (fn-cp-nth 2 s)) (msgid (fn-cp-nth 3 s))
       (visible (fn-cp-nth 4 s)) (withdrawn (fn-cp-nth 5 s)) (scan (fn-cp-nth 6 s))
       (records (fn-cp-nth 7 s)) (phase (fn-cp-nth 8 s)) (target (fn-cp-nth 9 s)))
  (cond
   ((not (equal key current-key)) '(:refused :remote-view-source-changed))
   ((eq phase :own-withdrawn)
    (if (consp scan)
        (if (and (consp (car scan)) (equal (fn-article-msgid (car scan)) msgid))
            (list :withdrawn (car scan) (fn-crv-state key row msgid visible withdrawn nil records :causes nil))
          (list :yield (fn-crv-state key row msgid visible withdrawn (cdr scan) records phase nil)))
     (if (null scan) (list :yield (fn-crv-state key row msgid visible withdrawn nil records :causes nil))
       '(:refused :remote-view-withdrawn))))
   ((eq phase :visible)
    (if (consp visible)
        (if (and (consp (car visible)) (equal (fn-article-msgid (car visible)) msgid))
            (list :visible (car visible))
          (list :yield (fn-crv-state key row msgid (cdr visible) withdrawn nil records phase nil)))
     (if (null visible) '(:excluded :retired-or-not-visible)
       '(:refused :remote-view-visible))))
   ((eq phase :causes)
    (if (consp records)
        (let ((w (car records)))
         (if (and (fn-ctl-withdrawalp w) (equal (fn-ctl-w-cause w) msgid))
             (list :yield (fn-crv-state key row msgid visible withdrawn withdrawn (cdr records)
                            :target (fn-ctl-w-target w)))
          (list :yield (fn-crv-state key row msgid visible withdrawn nil (cdr records) phase nil))))
     (if (null records) (list :yield (fn-crv-state key row msgid visible withdrawn nil nil :visible nil))
       '(:refused :remote-view-withdrawals))))
   ((eq phase :target)
    (if (consp scan)
        (if (and (consp (car scan)) (equal (fn-article-msgid (car scan)) target))
            (list :withdrawal-target (car scan)
                  (fn-crv-state key row msgid visible withdrawn nil records :causes nil))
          (list :yield (fn-crv-state key row msgid visible withdrawn (cdr scan) records phase target)))
     (if (null scan) (list :yield (fn-crv-state key row msgid visible withdrawn nil records :causes nil))
       '(:refused :remote-view-withdrawn))))
   (t '(:refused :remote-view-phase)))))

(in-theory (disable fn-crv-state fn-crv-begin fn-crv-tick))

; Current ARTICLE groups are text; the durable ordered query is octets.
; One bounded name comparison per tick, including a withdrawal target whose
; cause was filed in another group. Full query traversal never occurs here.
(defun fn-crv-query-tick (key current-key groups suffix query)
 (declare (xargs :guard t))
 (cond ((not (equal key current-key)) '(:refused :remote-view-source-changed))
       ((not (consp groups))
        (if (null groups) '(:excluded :query) '(:refused :remote-view-groups)))
       ((not (consp suffix))
        (if (null suffix) (list :yield (cdr groups) query) '(:refused :query)))
       ((not (fn-crs-namep (car suffix))) '(:refused :query))
       ((equal (car groups) (fn-record-octets-string (car suffix))) '(:query-match))
       (t (list :yield groups (cdr suffix)))))

(in-theory (disable fn-crv-query-tick))
