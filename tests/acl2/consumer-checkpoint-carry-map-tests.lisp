(in-package "ACL2")
(include-book "../../books/consumer-checkpoint-carry-map-model")
(local (include-book "consumer-authority-carried-result-tests"))
(local (include-book "consumer-entry-completion-tests"))

; A ghost info fixture, not a wire parse or source-attribution witness.
; Collapsed octet leaves deliberately have no invented child annotations.
(defun fn-ccmt-info (x)
 (declare (xargs :guard t :verify-guards nil :measure (acl2-count x)))
 (if (and (consp x) (not (fn-scc-octet-listp x)))
     (cons (fn-scs-summary x)
           (cons (fn-ccmt-info (car x)) (fn-ccmt-info (cdr x))))
   (list (fn-scs-summary x))))

; Test driver only. Runtime callers schedule individual context ticks.
(defun fn-ccmt-run (fuel one)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (and (not (zp fuel)) (eq (fn-cp-nth 0 one) :yield))
     (fn-ccmt-run (1- fuel) (fn-ccm-context-tick (fn-cp-nth 1 one)))
   one))

(defun fn-ccmt-correctp (cp)
 (declare (xargs :guard t :verify-guards nil))
 (equal (fn-ccmt-run 1000 (fn-ccm-context-begin cp (fn-ccmt-info cp)))
        (list :ok (fn-cpmm-annotation cp))))

;@mutation-witness fn-ccm-actual-pending-stage-and-ready-trie-map-completely
(assert-event
 (and (fn-ccmt-correctp (fn-cp-nth 1 *carfct-begin*))
      (fn-ccmt-correctp (fn-cp-nth 1 *carfct-row*))
      (fn-ccmt-correctp (fn-cp-nth 1 *carfct-seal*))
      (fn-ccmt-correctp (fn-cp-nth 1 *carfct-prepare*))))
;@mutation-witness fn-ccm-actual-adopted-delete-tombstone-recreated-map-completely
(assert-event
 (and (fn-ccmt-correctp (fn-cp-nth 1 *carfct-fence*))
      (fn-ccmt-correctp (fn-cp-nth 1 *carfct-delete-fence*))
      (fn-ccmt-correctp (fn-cp-nth 1 *carfct-recreate-fence*))))
;@mutation-witness fn-ccm-actual-four-entry-table-map-is-full-fixed-five
(assert-event (fn-ccmt-correctp *cect-cp*))
;@mutation-witness fn-ccm-collapsed-root-or-missing-child-never-resummarizes
(assert-event
 (and (equal (fn-ccm-context-begin (fn-cp-nth 1 *carfct-fence*)
              (list (fn-scs-summary (fn-cp-nth 1 *carfct-fence*))))
             '(:refused :checkpoint-consumer-infos))
      (equal (fn-ccmt-run 1000
              (fn-ccm-context-begin (fn-cp-nth 1 *carfct-fence*)
               (update-nth 1 nil (fn-ccmt-info (fn-cp-nth 1 *carfct-fence*)))))
             '(:refused :checkpoint-consumer-infos))))
;@mutation-witness fn-ccm-legacy-six-fields-refuse-and-empty-seed-remains-unavailable
(assert-event
 (and (equal (fn-ccm-context-begin '(:consumer-state (1) (2) 0 1 nil) nil)
             '(:refused :checkpoint-consumer-schema))
      (equal (fn-ccm-context-begin nil nil) '(:ok nil))))
;@mutation-witness fn-ccm-exhausted-test-fuel-yields-with-retained-original-carries
(assert-event
 (let ((initial (fn-ccm-context-begin (fn-cp-nth 1 *carfct-row*)
                                    (fn-ccmt-info (fn-cp-nth 1 *carfct-row*)))))
  (and (eq (fn-cp-nth 0 initial) :yield)
       (equal (fn-ccmt-run 0 initial) initial)
       (eq (fn-cp-nth 0 (fn-ccmt-run 1 initial)) :yield))))

(defun fn-ccmt-last-cursor (fuel cursor)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (let ((one (fn-ccm-tick cursor)))
  (if (and (not (zp fuel)) (eq (fn-cp-nth 0 one) :yield))
      (fn-ccmt-last-cursor (1- fuel) (fn-cp-nth 1 one))
    cursor)))
(defconst *ccmt-list-rows*
 (fn-cp-nth 4 (fn-cp-nth 6 (fn-cp-nth 1 *carfct-fence*))))
(defconst *ccmt-list-start*
 (fn-cp-nth 1 (fn-ccm-begin :list *ccmt-list-rows* (fn-ccmt-info *ccmt-list-rows*))))
(defconst *ccmt-list-end* (fn-ccmt-last-cursor 100 *ccmt-list-start*))
;@positive fn-ccmm-actual-tick-preserves-complete-annotation-target
(assert-event
 (and (eq (fn-cp-nth 0 (fn-ccm-tick *ccmt-list-start*)) :yield)
      (equal (fn-ccmm-denotation (fn-cp-nth 1 (fn-ccm-tick *ccmt-list-start*)))
             (fn-ccmm-denotation *ccmt-list-start*))))
;@hypothesis-removal fn-ccmm-actual-tick-preserves-complete-annotation-target yielding-step
; Reachable phase change: an actual completed tick is no longer a cursor.
(assert-event
 (and (not (eq (fn-cp-nth 0 (fn-ccm-tick *ccmt-list-end*)) :yield))
      (not (equal (fn-ccmm-denotation (fn-cp-nth 1 (fn-ccm-tick *ccmt-list-end*)))
                   (fn-ccmm-denotation *ccmt-list-end*)))))
;@positive fn-ccmm-actual-finish-is-complete-annotation-target
(assert-event
 (and (eq (fn-cp-nth 0 (fn-ccm-tick *ccmt-list-end*)) :ok)
      (equal (fn-cp-nth 1 (fn-ccm-tick *ccmt-list-end*))
             (fn-ccmm-denotation *ccmt-list-end*))
      (equal (fn-cp-nth 1 (fn-ccm-tick *ccmt-list-end*))
             (fn-caam-list-annotation *ccmt-list-rows*))))
;@hypothesis-removal fn-ccmm-actual-finish-is-complete-annotation-target completed-step
; Reachable phase change: the initial yielding value has not completed.
(assert-event
 (and (not (eq (fn-cp-nth 0 (fn-ccm-tick *ccmt-list-start*)) :ok))
      (not (equal (fn-cp-nth 1 (fn-ccm-tick *ccmt-list-start*))
                   (fn-ccmm-denotation *ccmt-list-start*)))))

(defun fn-ccmt-last-context (fuel context)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (let ((one (fn-ccm-context-tick context)))
  (if (and (not (zp fuel)) (eq (fn-cp-nth 0 one) :yield))
      (fn-ccmt-last-context (1- fuel) (fn-cp-nth 1 one))
    context)))
(defconst *ccmt-context-start*
 (fn-cp-nth 1 (fn-ccm-context-begin (fn-cp-nth 1 *carfct-row*)
                                  (fn-ccmt-info (fn-cp-nth 1 *carfct-row*)))))
(defconst *ccmt-context-end* (fn-ccmt-last-context 1000 *ccmt-context-start*))
;@positive fn-ccmm-actual-context-tick-preserves-complete-target
(assert-event
 (and (eq (fn-cp-nth 0 (fn-ccm-context-tick *ccmt-context-start*)) :yield)
      (equal (fn-ccmm-context-denotation
               (fn-cp-nth 1 (fn-ccm-context-tick *ccmt-context-start*)))
             (fn-ccmm-context-denotation *ccmt-context-start*))))
;@hypothesis-removal fn-ccmm-actual-context-tick-preserves-complete-target yielding-step
(assert-event
 (and (not (eq (fn-cp-nth 0 (fn-ccm-context-tick *ccmt-context-end*)) :yield))
      (not (equal (fn-ccmm-context-denotation
                    (fn-cp-nth 1 (fn-ccm-context-tick *ccmt-context-end*)))
                   (fn-ccmm-context-denotation *ccmt-context-end*)))))
;@positive fn-ccmm-actual-context-finish-is-complete-target
(assert-event
 (and (eq (fn-cp-nth 0 (fn-ccm-context-tick *ccmt-context-end*)) :ok)
      (equal (fn-cp-nth 1 (fn-ccm-context-tick *ccmt-context-end*))
             (fn-ccmm-context-denotation *ccmt-context-end*))))
;@hypothesis-removal fn-ccmm-actual-context-finish-is-complete-target completed-step
(assert-event
 (and (not (eq (fn-cp-nth 0 (fn-ccm-context-tick *ccmt-context-start*)) :ok))
      (not (equal (fn-cp-nth 1 (fn-ccm-context-tick *ccmt-context-start*))
                   (fn-ccmm-context-denotation *ccmt-context-start*)))))
