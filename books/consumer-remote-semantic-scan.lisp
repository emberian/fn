; One dense event's bounded visibility -> query -> current READ continuation.
; Internal producer only: actual owner capture/authentication/CP revalidation
; must supply and retain these children. A report input is not a reply, durable
; progress, a writer completion receipt, or permission to release an alias.
(in-package "ACL2")
(include-book "consumer-remote-visibility")
(include-book "consumer-remote-report-scope")

; Fixed16: source key, READ key, scanner, authenticated ingress, generation,
; posting config, phase, child, selected article/kind, visibility continuation,
; article-group/query suffixes, whole ordered query, retained dense event.
(defun fn-crm-state (key scope-key scanner ingress generation config phase child
                    article kind resume groups suffix query row)
 (declare (xargs :guard t))
 (list :remote-semantic key scope-key scanner ingress generation config phase child
       article kind resume groups suffix query row))

(defun fn-crm-change (s phase child article kind resume groups suffix)
 (declare (xargs :guard t))
 (fn-crm-state (fn-cp-nth 1 s) (fn-cp-nth 2 s) (fn-cp-nth 3 s)
  (fn-cp-nth 4 s) (fn-cp-nth 5 s) (fn-cp-nth 6 s) phase child article kind resume
  groups suffix (fn-cp-nth 14 s) (fn-cp-nth 15 s)))

(defun fn-crm-begin (scanner row ingress generation posting-config current-view)
 (declare (xargs :guard t))
 (let* ((key (fn-cp-nth 1 scanner)) (query (fn-cp-nth 4 scanner))
        (article (fn-crps-row-article row)))
  (cond ((not row) (list :unavailable :history (fn-cp-nth 5 scanner)))
        ((not (eq (fn-cp-nth 0 ingress) :authenticated)) ingress)
        ((not (eq (fn-cp-nth 8 scanner) :read)) '(:refused :semantic-scan-phase))
        ((and (eq (fn-cp-nth 0 row) :hstxa) (not article))
         '(:refused :article-binding))
        ((not (and (fn-cp-uintp (fn-cp-nth 5 scanner))
                    (fn-cp-uintp (fn-cp-nth 6 scanner))
                    (fn-cp-uintp (fn-cp-nth 7 scanner))
                    (< (fn-cp-nth 5 scanner) (fn-cp-nth 7 scanner))
                    (<= (fn-cp-nth 7 scanner) (fn-cp-nth 6 scanner))))
         '(:refused :semantic-scan-coordinate))
        ((and article (not (equal (fn-record-sequence article) (fn-cp-nth 5 scanner))))
         '(:refused :semantic-history-coordinate))
        (t (list :yield (fn-crm-state key (fn-crs-key ingress generation) scanner
              ingress generation posting-config :visibility (fn-crv-begin key row current-view)
              nil nil nil nil nil query row))))))

; No candidate advances the event position: a cause can name multiple targets.
; The writer must consume each report input before resuming its continuation.
; Only exhaustion of the event's visibility continuation advances ONE dense
; position. The owner still owes current-source rechecks and physical joins.
(defun fn-crm-complete-event (s)
 (declare (xargs :guard t))
 (let ((scanner (fn-cp-nth 3 s)))
  (list :event-complete
   (fn-crps-state (fn-cp-nth 1 scanner) (fn-cp-nth 2 scanner) (fn-cp-nth 3 scanner)
    (fn-cp-nth 4 scanner) (1+ (nfix (fn-cp-nth 5 scanner))) (fn-cp-nth 6 scanner)
    (fn-cp-nth 7 scanner) :read nil nil nil))))

(defun fn-crm-after-selection (s)
 (declare (xargs :guard t))
 (if (fn-cp-nth 11 s)
     (list :yield (fn-crm-change s :visibility (list :yield (fn-cp-nth 11 s))
                                nil nil nil nil nil))
   (list :yield (fn-crm-change s :finished nil nil nil nil nil nil))))

; Each call performs at most ONE existing visibility, bounded name comparison
; or current scope tick. Source and READ keys are independently rechecked;
; a changed account/configuration cannot inherit a saved visibility result.
(defun fn-crm-tick (s current-key current-scope-key query-limit)
 (declare (xargs :guard t))
 (let* ((key (fn-cp-nth 1 s)) (scope-key (fn-cp-nth 2 s))
        (phase (fn-cp-nth 7 s)) (child (fn-cp-nth 8 s))
        (article (fn-cp-nth 9 s)) (kind (fn-cp-nth 10 s))
        (resume (fn-cp-nth 11 s)) (groups (fn-cp-nth 12 s))
        (suffix (fn-cp-nth 13 s)) (query (fn-cp-nth 14 s)))
  (cond
   ((not (and (equal key current-key) (equal scope-key current-scope-key)))
    '(:refused :remote-semantic-source-changed))
   ((not (and (posp query-limit) (fn-cp-uintp query-limit)))
    '(:refused :consumer-query-count))
   ((eq phase :finished) (fn-crm-complete-event s))
   ((eq phase :visibility)
    (let* ((answer (if (eq (fn-cp-nth 0 child) :yield)
                      (fn-crv-tick (fn-cp-nth 1 child) current-key) child))
           (word (fn-cp-nth 0 answer)))
     (cond ((eq word :yield)
            (list :yield (fn-crm-change s phase answer nil nil nil nil nil)))
           ((member-eq word '(:visible :withdrawn :withdrawal-target))
            (let ((selected (fn-cp-nth 1 answer)))
             (list :yield (fn-crm-change s :query nil selected word (fn-cp-nth 2 answer)
                                         (fn-article-groups selected) query))))
           ((eq word :excluded) (fn-crm-complete-event s))
           (t answer))))
   ((eq phase :query)
    (let* ((answer (fn-crv-query-tick key current-key groups suffix query))
           (word (fn-cp-nth 0 answer)))
     (cond ((eq word :yield)
            (list :yield (fn-crm-change s phase nil article kind resume
                                         (fn-cp-nth 1 answer) (fn-cp-nth 2 answer))))
           ((eq word :query-match)
            (list :yield (fn-crm-change s :scope
              (fn-crrs-begin-view (fn-cp-nth 4 s) (fn-cp-nth 5 s) (fn-cp-nth 6 s) article)
              article kind resume nil nil)))
           ((eq word :excluded) (fn-crm-after-selection s))
           (t answer))))
   ((eq phase :scope)
    (let* ((answer (if (eq (fn-cp-nth 0 child) :yield)
                      (fn-crrs-tick (fn-cp-nth 1 child) current-scope-key query-limit) child))
           (word (fn-cp-nth 0 answer)))
     (cond ((eq word :yield)
            (list :yield (fn-crm-change s phase answer article kind resume nil nil)))
           ((eq word :report-input)
            (list :report-input kind answer (fn-crm-after-selection s)))
           ((eq word :excluded) (fn-crm-after-selection s))
           (t answer))))
   (t '(:refused :remote-semantic-phase)))))

(in-theory (disable fn-crm-state fn-crm-change fn-crm-begin fn-crm-complete-event
                   fn-crm-after-selection fn-crm-tick))
