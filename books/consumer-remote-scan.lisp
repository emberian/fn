; One retained event and one bounded group-name pair per scheduling step.
; This selector owns decisions only. It grants no history/arena custody,
; allocation, retention pin or durable ACK. The actual owner must retain and
; revalidate the current source before every call and before reply publication.
(in-package "ACL2")
(include-book "consumer-remote-fields")
(include-book "held-record")

; Fixed12: key,CP,selected entry,ordered query,position,pinned frontier,
; window end,phase,retained event,article-group suffix,query suffix.
(defun fn-crps-state (key cp entry query position frontier end phase event articles remaining)
 (declare (xargs :guard t))
 (list :remote-scan key cp entry query position frontier end phase event articles remaining))

(defun fn-crps-begin (plan current-key scan-limit)
 (declare (xargs :guard t))
 (let* ((cp (fn-cp-nth 2 plan)) (entry (fn-cp-nth 3 plan))
        (position (fn-cp-nth 7 entry)) (frontier (fn-cp-nth 3 cp)))
  (cond ((not (eq (fn-cp-nth 0 plan) :scan-request)) '(:refused :scan-plan))
        ((not (and (fn-cp-uintp position) (fn-cp-uintp frontier) (<= position frontier)))
         '(:refused :coordinates))
        ((not (and (posp scan-limit) (fn-cp-uintp scan-limit))) '(:refused :scan-policy))
        (t (list :yield (fn-crps-state current-key cp entry (fn-cp-nth 4 plan)
              position frontier (min frontier (+ position scan-limit)) :read nil nil nil))))))

; The maintained history producer supplies valid held rows. Bare held rows
; have a natural sequence at slot0; accepted composites have the :hstxa tag.
; Do not run fn-held-p/fn-hstxa-p (whole row validators) on this served step.
(defun fn-crps-row-article (row)
 (declare (xargs :guard t))
 (cond ((eq (fn-cp-nth 0 row) :hstxa) (fn-hstxa-held row))
       ((natp (fn-cp-nth 0 row)) row)
       (t nil)))

(defun fn-crps-page (s event)
 (declare (xargs :guard t))
 (list :poll (update-nth 9 (fn-cp-nth 5 s)
               (fn-cp-scope-cursor (fn-cp-nth 2 s) (fn-cp-nth 3 s)))
       event (fn-cp-nth 6 s) (< (nfix (fn-cp-nth 5 s)) (nfix (fn-cp-nth 6 s)))))

; ROW is used only in :read. One validated published history array read is
; performed by the concrete caller, never a journal-prefix traversal. A
; absent retained row is unavailable at that exact position, never skipped.
(defun fn-crps-tick (s current-key row)
 (declare (xargs :guard t))
 (let* ((key (fn-cp-nth 1 s)) (cp (fn-cp-nth 2 s)) (entry (fn-cp-nth 3 s))
        (query (fn-cp-nth 4 s)) (position (nfix (fn-cp-nth 5 s)))
        (frontier (fn-cp-nth 6 s)) (end (nfix (fn-cp-nth 7 s)))
        (phase (fn-cp-nth 8 s)) (event (fn-cp-nth 9 s))
        (articles (fn-cp-nth 10 s)) (remaining (fn-cp-nth 11 s)))
  (cond ((not (equal key current-key)) '(:refused :consumer-source-changed))
        ((eq phase :read)
         (cond ((<= end position) (fn-crps-page s nil))
               ((not row) (list :unavailable :history position))
               (t
                (let ((article (fn-crps-row-article row)))
                 (cond ((and (eq (fn-cp-nth 0 row) :hstxa) (not article))
                        (list :refused :article-binding position))
                       ((not article)
                        (list :yield (fn-crps-state key cp entry query (1+ position) frontier end :read nil nil nil)))
                       ((not (equal (fn-record-sequence article) position))
                        (list :refused :history position))
                       (t (list :yield (fn-crps-state key cp entry query position frontier end
                                  :match row (fn-record-groups article) query))))))))
        ((eq phase :match)
         (cond ((not (consp articles))
                (if (null articles)
                    (list :yield (fn-crps-state key cp entry query (1+ position) frontier end :read nil nil nil))
                  (list :refused :article-groups position)))
               ((not (consp remaining))
                (if (null remaining)
                    (list :yield (fn-crps-state key cp entry query position frontier end :match event (cdr articles) query))
                  (list :refused :query position)))
               ((not (fn-crs-namep (car remaining))) (list :refused :query position))
               ((equal (car articles) (fn-record-octets-string (car remaining)))
                (fn-crps-page (fn-crps-state key cp entry query (1+ position) frontier end :read nil nil nil) event))
               (t (list :yield (fn-crps-state key cp entry query position frontier end :match event articles (cdr remaining))))))
        (t '(:refused :scan-phase)))))

(in-theory (disable fn-crps-state fn-crps-begin fn-crps-row-article fn-crps-page fn-crps-tick))
