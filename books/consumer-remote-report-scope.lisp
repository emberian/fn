; Candidate metadata projection, using the SAME bounded current READ and
; moderation semantics as remote definition admission. This produces inputs
; for a bounded report writer, never a raw accepted-statement wire report.
; Actual current view visibility/withdrawal/retention must be decided before
; this internal producer is begun; its config/row children require custody.
(in-package "ACL2")
(include-book "consumer-remote-scope")
(include-book "consumer-remote-scan")

; Fixed14: key, authenticated ingress, config generation, policy projection,
; held article, group suffix, numbering suffix, phase, child scope/search,
; reversed groups/numbers, ordered groups/numbers.
(defun fn-crrs-state (key ingress generation config article groups numbers phase child rg rn outg outn)
 (declare (xargs :guard t))
 (list :remote-report-scope key ingress generation config article groups numbers
       phase child rg rn outg outn))

(defun fn-crrs-begin (ingress generation config row)
 (declare (xargs :guard t))
 (let ((article (fn-crps-row-article row)))
  (if (or (not (eq (fn-cp-nth 0 ingress) :authenticated)) (not article))
      '(:refused :remote-report-article-or-account)
   (list :yield (fn-crrs-state (fn-crs-key ingress generation) ingress generation config
                 article (fn-record-groups article) (fn-cp-nth 13 article)
                 :groups nil nil nil nil nil)))))

; The current-view eligibility producer returns actual maintained ARTICLEs,
; including withdrawal targets. Preserve the distinct representation tag;
; an original held event/composite is never substituted for this view row.
(defun fn-crrs-begin-view (ingress generation config article)
 (declare (xargs :guard t))
 (if (not (eq (fn-cp-nth 0 ingress) :authenticated))
     '(:refused :remote-report-account)
  (list :yield (fn-crrs-state (fn-crs-key ingress generation) ingress generation config
                (list :current-article article) (fn-article-groups article)
                (fn-article-memberships article) :groups nil nil nil nil nil))))

; Each invocation performs one existing scope tick OR one list-cell action.
; Excluding an unreadable/hidden group excludes its local-number metadata too.
; Never deliver an original composite: its signed wire child can name groups
; the login cannot read and cannot be rewritten while preserving a signature.
(defun fn-crrs-tick (s current-key query-limit)
 (declare (xargs :guard t))
 (let* ((key (fn-cp-nth 1 s)) (ingress (fn-cp-nth 2 s)) (generation (fn-cp-nth 3 s))
        (config (fn-cp-nth 4 s)) (article (fn-cp-nth 5 s)) (groups (fn-cp-nth 6 s))
        (numbers (fn-cp-nth 7 s)) (phase (fn-cp-nth 8 s)) (child (fn-cp-nth 9 s))
        (rg (fn-cp-nth 10 s)) (rn (fn-cp-nth 11 s)) (outg (fn-cp-nth 12 s)) (outn (fn-cp-nth 13 s)))
  (cond
   ((not (equal key current-key)) '(:refused :remote-report-source-changed))
   ((not (and (posp query-limit) (fn-cp-uintp query-limit))) '(:refused :consumer-query-count))
   ((eq phase :groups)
    (if (not (consp groups))
        (if (null groups)
            (list :yield (fn-crrs-state key ingress generation config article nil numbers
                            :reverse-groups nil rg rn nil nil))
          '(:refused :remote-report-groups))
     (if (not (stringp (car groups))) '(:refused :remote-report-group)
      (let ((answer (fn-crs-begin ingress generation config
                       (list (fn-nntp-string-octets (car groups))))))
       (if (eq (fn-cp-nth 0 answer) :yield)
           (list :yield (fn-crrs-state key ingress generation config article groups numbers
                         :scope (fn-cp-nth 1 answer) rg rn nil nil)) answer)))))
   ((eq phase :scope)
    (let* ((answer (fn-crs-tick child current-key query-limit)) (word (fn-cp-nth 0 answer)))
     (cond
      ((eq word :yield)
       (list :yield (fn-crrs-state key ingress generation config article groups numbers
                      :scope (fn-cp-nth 1 answer) rg rn nil nil)))
      ((eq word :ready)
       (list :yield (fn-crrs-state key ingress generation config article (if (consp groups) (cdr groups) nil) numbers
                      :groups nil (cons (if (consp groups) (car groups) nil) rg) rn nil nil)))
      ((and (eq word :refused) (eq (fn-cp-nth 1 answer) :read-scope))
       (list :yield (fn-crrs-state key ingress generation config article (if (consp groups) (cdr groups) nil) numbers
                      :groups nil rg rn nil nil)))
      (t answer))))
   ((eq phase :reverse-groups)
    (if (consp rg)
        (list :yield (fn-crrs-state key ingress generation config article nil numbers :reverse-groups
                       nil (cdr rg) rn (cons (car rg) outg) nil))
     (if outg
         (list :yield (fn-crrs-state key ingress generation config article nil numbers :numbers nil nil rn outg nil))
       '(:excluded :remote-report-read-scope))))
   ((eq phase :numbers)
    (if (consp numbers)
        (list :yield (fn-crrs-state key ingress generation config article nil numbers :number-search outg nil rn outg nil))
     (if (null numbers)
         (list :yield (fn-crrs-state key ingress generation config article nil nil :reverse-numbers nil nil rn outg nil))
       '(:refused :remote-report-numbers))))
   ((eq phase :number-search)
    (cond
     ((not (consp numbers)) '(:refused :remote-report-numbers))
     ((not (consp child))
      (list :yield (fn-crrs-state key ingress generation config article nil (cdr numbers) :numbers nil nil rn outg nil)))
     ((and (consp (car numbers)) (equal (car (car numbers)) (car child)))
      (list :yield (fn-crrs-state key ingress generation config article nil (cdr numbers) :numbers nil nil (cons (car numbers) rn) outg nil)))
     (t (list :yield (fn-crrs-state key ingress generation config article nil numbers :number-search (cdr child) nil rn outg nil)))))
   ((eq phase :reverse-numbers)
    (if (consp rn)
        (list :yield (fn-crrs-state key ingress generation config article nil nil :reverse-numbers nil nil (cdr rn) outg (cons (car rn) outn)))
     (list :report-input article outg outn)))
   (t '(:refused :remote-report-phase)))))

(in-theory (disable fn-crrs-state fn-crrs-begin fn-crrs-begin-view fn-crrs-tick))
