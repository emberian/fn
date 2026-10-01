; Internal endpoint assembly over the actual retained dense event source.
; The installed authenticated caller must prepare/revalidate the semantic key
; and policy span. Raw matches are candidates; this book never emits reports
; or grants article visibility, withdrawal status, retention or READ custody.
(in-package "ACL2")
(include-book "consumer-remote-scan")
(include-book "consumer-remote-terminal-return")

(defun fn-owner-remote-scan-begin-internal (token plan key scan-limit fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :guard t))
 (let ((source (fn-hhc-at 3 (fn-owner-history-capture-slot state))))
  (cond ((not (and (eq (fn-owner-history-recheck token state) :history-source-current)
                   (fn-hep-capture-livep source token fn-history-backing)))
         (mv '(:unavailable :history-source) state))
        ((fn-owner-history-read-slot state) (mv '(:refused :remote-history-reader-busy) state))
        ((not (equal (fn-cp-nth 3 (fn-cp-nth 2 plan)) (fn-hhc-at 7 source)))
         (mv '(:refused :remote-history-frontier) state))
        (t
         (let ((answer (fn-crps-begin plan key scan-limit)))
          (if (not (eq (fn-cp-nth 0 answer) :yield)) (mv answer state)
           (fn-owner-remote-scan-hold-internal token (fn-cp-nth 1 answer)
             nil nil nil key state)))))))

; Preserve scanner/reader/candidate aliases in the real STATE holder. No
; consumer cursor or ACK becomes durable by this transition. A final candidate
; must pass bounded current policy/visibility/withdrawal/retention processing.
(defun fn-owner-remote-scan-keep-result (token answer state)
 (declare (xargs :stobjs state :guard t))
 (let* ((held (fn-owner-remote-scan-read state))
        (yieldp (eq (fn-cp-nth 0 answer) :yield))
        (scanner (if yieldp (fn-cp-nth 1 answer) (fn-cp-nth 3 held))))
  (mv-let (word state)
   (fn-owner-remote-scan-update-internal token scanner
     (fn-owner-history-read-slot state) (if yieldp nil answer)
     (fn-cp-nth 6 held) (if yieldp nil :candidate) state)
   (mv (if (eq (fn-cp-nth 0 word) :held)
           (if yieldp '(:yield) (list :candidate answer)) word) state))))

; Every retained event reaches current visibility/withdrawal processing BEFORE
; query selection. Raw article-group matching would miss a withdrawal cause
; filed outside the query whose TARGET is inside it. NIL remains a dense gap.
(defun fn-owner-remote-scan-observe-row (token scanner row state)
 (declare (xargs :stobjs state :guard t))
 (fn-owner-remote-scan-keep-result token
   (if row (list :event-before-query row (fn-cp-nth 5 scanner))
     (list :unavailable :history (fn-cp-nth 5 scanner))) state))

; At most one backing read action OR one bounded group comparison per call.
; The semantic key comes only from the internal authenticated current-source
; span; it is not a public supplied freshness Boolean or constructor grant.
(defun fn-owner-remote-scan-step-internal (token current-key fuel fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :guard t))
 (let* ((held (fn-owner-remote-scan-read state)) (scanner (fn-cp-nth 3 held))
        (source (fn-hhc-at 3 (fn-owner-history-capture-slot state))))
  (cond
   ((not (and (eq (fn-cp-nth 0 held) :remote-scan-holder)
               (equal token (fn-cp-nth 1 held)) (eq (fn-cp-nth 2 held) :active)))
    (mv '(:refused :remote-scan-token-or-phase) (nfix fuel) state))
   ((not (equal current-key (fn-cp-nth 7 held)))
    (mv '(:refused :consumer-source-changed) (nfix fuel) state))
   ((not (and (eq (fn-owner-history-recheck token state) :history-source-current)
               (fn-hep-capture-livep source token fn-history-backing)))
    (mv '(:unavailable :history-source) (nfix fuel) state))
   ((fn-cp-nth 5 held) (mv '(:candidate-held) (nfix fuel) state))
   ((and (fn-owner-history-read-slot state)
         (not (and (equal token (fn-cp-nth 1 (fn-owner-history-read-slot state)))
                    (equal (fn-cp-nth 5 scanner)
                           (fn-cp-nth 2 (fn-owner-history-read-slot state))))))
    (mv '(:refused :remote-history-reader-coordinate) (nfix fuel) state))
   ((not (natp fuel)) (mv '(:refused :remote-scan-fuel) 0 state))
   ((zp fuel) (mv '(:yield) fuel state))
   ((or (not (eq (fn-cp-nth 8 scanner) :read))
        (<= (nfix (fn-cp-nth 7 scanner)) (nfix (fn-cp-nth 5 scanner))))
    (mv-let (word state)
     (fn-owner-remote-scan-keep-result token (fn-crps-tick scanner current-key nil) state)
     (mv word (- fuel 1) state)))
   ((not (fn-owner-history-read-slot state))
    (mv-let (word state)
     (fn-owner-history-read-begin token (fn-cp-nth 5 scanner) fn-history-backing state)
     (if (eq word :history-read-started)
         (let ((state (f-put-global 'fn-owner-remote-scan
                         (fn-crt-holder token :active scanner (fn-owner-history-read-slot state)
                           nil (fn-cp-nth 6 held) current-key nil) state)))
          (mv '(:yield) (- fuel 1) state))
      (mv (list :unavailable word) (- fuel 1) state))))
   (t
    (mv-let (word row left state) (fn-owner-history-read-step fuel fn-history-backing state)
     (cond ((eq word :row)
            (mv-let (answer state)
             (fn-owner-remote-scan-observe-row token scanner row state)
             (mv answer left state)))
           ((eq word :yield)
            (mv-let (answer state)
             (fn-owner-remote-scan-update-internal token scanner (fn-owner-history-read-slot state)
               nil (fn-cp-nth 6 held) nil state)
             (mv (if (eq (fn-cp-nth 0 answer) :held) '(:yield) answer) left state)))
           (t (mv (list :unavailable word) left state))))))))

(in-theory (disable fn-owner-remote-scan-begin-internal
 fn-owner-remote-scan-keep-result fn-owner-remote-scan-observe-row fn-owner-remote-scan-step-internal))
