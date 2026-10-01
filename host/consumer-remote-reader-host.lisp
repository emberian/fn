; Actual owner-input caller under owner serialization and genuine history pin.
; These internal branches are not a native export. The separate activation
; entry refuses until atomic CP/carries/root association and operation BODY
; are installed. No supplied view/CP/carries tuple or freshness flag is used.
(in-package "ACL2")
(include-book "consumer-remote-host")
(include-book "history-owner-view-host")
(include-book "../books/consumer-remote-reader-source")

; Inputs13: key, freshly authenticated ingress, actual CP7, generation, actual
; current view/posting config, sole carries, source9, request, query allowance,
; typed current config, actual installed record ceiling. This observation grants no allocation/authority.
(defun fn-owner-remote-reader-inputs (request protectedp g token fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :mode :program))
 (let ((captured (fn-hhc-at 3 (fn-owner-history-capture-slot state))))
  (if (not (and (eq (fn-owner-history-recheck token state) :history-source-current)
                 (fn-hep-capture-livep captured token fn-history-backing)))
      (mv '(:unavailable :history-source) nil state)
   (mv-let (word source view typed-config posting-config state)
    (fn-owner-history-current-view fn-history-backing state)
    (if (not (eq word :history-view)) (mv (list :unavailable word) nil state)
     (let* ((store (fn-owner-store state)) (cp (fn-sn-consumer store))
            (count (fn-sf-records-count (fn-sn-files store)))
            (generation (fn-cfg-generation typed-config))
            (record-ceiling (fn-owner-remote-query-record-ceiling state))
            (ingress (fn-cre-ingress request protectedp g cp
                       (fn-owner-canonical-epoch state) count (fn-owner-account-root-state state))))
      (cond
       ((not (eq (fn-cp-nth 0 ingress) :authenticated)) (mv ingress nil state))
       ((not (member-eq (fn-cp-nth 1 request) '(:poll :wait)))
        (mv '(:refused :remote-reader-operation) nil state))
       ((not (natp record-ceiling)) (mv '(:unavailable :store-profile) nil state))
       ((not (and (posp g) (fn-cp-uintp g)))
        (mv '(:refused :consumer-query-count) nil state))
       ((not (and (fn-hep-source-stamps-equal source captured)
                   (equal count (fn-hhc-at 7 source))
                   (equal (fn-cp-nth 3 cp) count)))
        (mv '(:refused :consumer-source-changed) nil state))
       (t (mv '(:inputs)
             (list :remote-reader-inputs (fn-crr-source-key token source ingress cp generation count g record-ceiling)
                   ingress cp generation view posting-config (fn-owner-account-carries-read state)
                   source request g typed-config record-ceiling) state)))))))))

; INTERNAL preparation: every borrowed child originates in the preceding
; actual owner getter, and every tick recaptures/revalidates that source.
; Selector8: tag, sourcekey, savedinputs, phase, policy/CEP child, ready CEP, scope,
; supported scan quantum. No whole CP/config equality or revalidation walk.
(defun fn-owner-remote-reader-begin-internal
 (request protectedp g token scan-limit fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :mode :program))
 (mv-let (word inputs state)
  (fn-owner-remote-reader-inputs request protectedp g token fn-history-backing state)
  (if (not (eq (fn-cp-nth 0 word) :inputs)) (mv word state)
   (if (not (and (posp scan-limit) (fn-cp-uintp scan-limit)))
       (mv '(:refused :scan-policy) state)
    (let ((start (fn-crp-begin (fn-cp-nth 1 inputs)
                    (fn-cfg-limits (fn-cfg-value (fn-cp-nth 11 inputs))) (fn-cp-nth 12 inputs))))
     (if (not (eq (fn-cp-nth 0 start) :yield)) (mv start state)
      (fn-owner-remote-scan-hold-internal token
       (list :remote-reader-selection (fn-cp-nth 1 inputs) inputs :policy
             (fn-cp-nth 1 start) nil nil scan-limit) nil nil nil (fn-cp-nth 1 inputs) state)))))))

; The actual supported native entry stays unavailable. No caller Boolean or
; completed candidate can bypass the real current-publication/BODY producer.
(defun fn-owner-remote-reader-begin
 (request protectedp g token scan-limit fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :mode :program))
 (mv-let (availability state) (fn-owner-remote-reader-activation-status state)
  (if (not (eq (fn-cp-nth 0 availability) :reader-installed)) (mv availability state)
   (fn-owner-remote-reader-begin-internal request protectedp g token scan-limit fn-history-backing state))))

(defun fn-owner-remote-reader-save (token selector state)
 (declare (xargs :stobjs state :mode :program))
 (let ((held (fn-owner-remote-scan-read state)))
  (mv-let (word state)
   (fn-owner-remote-scan-update-internal token selector (fn-owner-history-read-slot state)
      (fn-cp-nth 5 held) (fn-cp-nth 6 held) (fn-cp-nth 8 held) state)
   (mv (if (eq (fn-cp-nth 0 word) :held) '(:yield) word) state))))

(defun fn-owner-remote-reader-step-internal
 (request protectedp g token fuel fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :mode :program))
 (let* ((held (fn-owner-remote-scan-read state)) (selector (fn-cp-nth 3 held)))
  (cond
   ((not (and (equal token (fn-cp-nth 1 held)) (eq (fn-cp-nth 2 held) :active)))
    (mv '(:refused :remote-scan-token-or-phase) (nfix fuel) state))
   ((not (natp fuel)) (mv '(:refused :remote-scan-fuel) 0 state))
   ((zp fuel) (mv '(:yield) fuel state))
   (t
    (mv-let (word inputs state)
     (fn-owner-remote-reader-inputs request protectedp g token fn-history-backing state)
     (cond
      ((not (eq (fn-cp-nth 0 word) :inputs)) (mv word fuel state))
      ((not (equal (fn-cp-nth 1 inputs) (fn-cp-nth 7 held)))
       (mv '(:refused :consumer-source-changed) fuel state))
      ((not (eq (fn-cp-nth 0 selector) :remote-reader-selection))
       (if (fn-cp-nth 5 held)
           (mv-let (answer state)
            (fn-owner-remote-semantic-step-internal token (fn-cp-nth 1 inputs)
             (fn-cp-nth 2 inputs) (fn-cp-nth 4 inputs) (fn-cp-nth 6 inputs)
             (fn-cp-nth 5 inputs) g fn-history-backing state)
            (mv answer (1- fuel) state))
        (fn-owner-remote-scan-step-internal token (fn-cp-nth 1 inputs) fuel fn-history-backing state)))
      (t
       (let* ((saved (fn-cp-nth 2 selector)) (phase (fn-cp-nth 3 selector))
              (child (fn-cp-nth 4 selector)) (cep (fn-cp-nth 5 selector))
              (scope (fn-cp-nth 6 selector)) (limit (fn-cp-nth 7 selector))
              (ingress (fn-cp-nth 2 inputs)) (cp (fn-cp-nth 3 saved))
              (generation (fn-cp-nth 4 inputs)))
        (mv-let (answer state)
         (cond
          ((eq phase :policy)
           (let ((answer (fn-crp-tick child (fn-cp-nth 1 inputs) (fn-cp-nth 12 inputs))))
            (case (fn-cp-nth 0 answer)
             (:yield (fn-owner-remote-reader-save token
               (list :remote-reader-selection (fn-cp-nth 1 selector) saved phase
                     (fn-cp-nth 1 answer) nil nil limit) state))
             (:ready
              (let ((policy (fn-crp-finish (fn-cp-nth 1 answer)
                                 (fn-cp-nth 1 inputs) (fn-cp-nth 12 inputs))))
               (if (not (and (eq (fn-cp-nth 0 policy) :query-policy)
                              (equal g (fn-cp-nth 1 policy))))
                   (mv '(:refused :consumer-query-policy-changed) state)
                (let ((start (fn-cep-begin cp (list :remote-select (fn-cp-nth 4 request))
                                           (fn-cp-nth 7 saved))))
                 (if (eq (fn-cp-nth 0 start) :yield)
                     (fn-owner-remote-reader-save token
                      (list :remote-reader-selection (fn-cp-nth 1 selector) saved :selection
                            (fn-cp-nth 1 start) nil nil limit) state)
                   (mv start state))))))
             (otherwise (mv answer state)))))
          ((eq phase :selection)
           (let ((answer (fn-cep-tick child)))
            (case (fn-cp-nth 0 answer)
             (:yield (fn-owner-remote-reader-save token
               (list :remote-reader-selection (fn-cp-nth 1 selector) saved phase
                     (fn-cp-nth 1 answer) nil nil limit) state))
             (:ready
              (let* ((ready (fn-cp-nth 1 answer))
                     (route (fn-cre-selected-route ingress (fn-cp-nth 9 ready)))
                     (start (if (eq (fn-cp-nth 0 route) :definition-request)
                                 (fn-crs-begin ingress generation (fn-cp-nth 6 saved) (fn-cp-nth 1 route)) route)))
               (if (eq (fn-cp-nth 0 start) :yield)
                   (fn-owner-remote-reader-save token
                    (list :remote-reader-selection (fn-cp-nth 1 selector) saved :scope
                          nil ready (fn-cp-nth 1 start) limit) state)
                 (mv start state))))
             (otherwise (mv answer state)))))
          ((eq phase :scope)
           (let ((answer (fn-crs-tick scope (fn-crs-key ingress generation) g)))
            (case (fn-cp-nth 0 answer)
             (:yield (fn-owner-remote-reader-save token
               (list :remote-reader-selection (fn-cp-nth 1 selector) saved phase
                     nil cep (fn-cp-nth 1 answer) limit) state))
             (:ready
              (let* ((plan (fn-crx-selected-plan cp ingress cep (fn-cp-nth 1 answer) generation))
                     (start (if (eq (fn-cp-nth 0 plan) :scan-request)
                                 (fn-crps-begin plan (fn-cp-nth 1 inputs) limit) plan)))
               (if (eq (fn-cp-nth 0 start) :yield)
                   (fn-owner-remote-reader-save token (fn-cp-nth 1 start) state)
                 (mv start state))))
             (otherwise (mv answer state)))))
          (t (mv '(:refused :remote-reader-phase) state)))
         (mv answer (1- fuel) state))))))))))

(defun fn-owner-remote-reader-step
 (request protectedp g token fuel fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :mode :program))
 (mv-let (availability state) (fn-owner-remote-reader-activation-status state)
  (if (not (eq (fn-cp-nth 0 availability) :reader-installed))
      (mv availability (nfix fuel) state)
   (fn-owner-remote-reader-step-internal request protectedp g token fuel fn-history-backing state))))
