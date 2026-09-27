; Teeth for books/bp-handoff-report.lisp (PRF-224, lane bp-fragments-10mib).
; The witness is bp-node-debt-tests' construction: a local request received
; durably through the foundation step, delivered, the application's STATUS
; recorded, and the kind-7 publication answered.  SCN-077's case is the
; :request-refused run: the Store refused the article (oversize), kind 7 is
; durable, and the report is :refused, not :durable.
(in-package "ACL2")
(include-book "../../books/bp-handoff-report")
(include-book "../../books/bp-node-receive-boundary")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bphr-local* (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47)))
(defconst *bphr-sender* (cons :dtn '(47 47 98 112 45 115 101 110 100 101 114 47)))
(defconst *bphr-local-config* (fn-bpn-config *bphr-local* 3600000 2 32 1048576))
(defconst *bphr-sender-config* (fn-bpn-config *bphr-sender* 3600000 2 32 1048576))
(defconst *bphr-observation* (fn-clock-observation 1000 0 0 nil))
(defconst *bphr-ingress*
  (list :cl (cons 0 1) 1 *bphr-sender* '(115 101 110 100 101 114) 0))
(defconst *bphr-request*
  (fn-bpa-encode
   (fn-bpa-make-request "w" "s" "dtn://bp-sender/" "dtn://bp-local/"
                        "p" "i" "c" "t" '(88 13 10))))
(defconst *bphr-bundle*
  (fn-bpn-send-bundle *bphr-sender-config* *bphr-local*
                      *bphr-request* 8 *bphr-observation*))

(defun bphr-durable-receive (st bundle)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((prepared (fn-bpnf-receive-wire-event
                    *bphr-local-config* (fn-bpb-encode bundle)
                    *bphr-observation* *bphr-ingress*))
         (proposal (fn-bpnf-step
                    st (fn-bpnf-receive-wire-event-value prepared)))
         (effect (car (fn-bpnf-answer-effects proposal))))
    (if (and (fn-bpnf-receive-wire-readyp prepared)
             (equal (car effect) :persist))
        (fn-bpnf-answer-state
         (fn-bpnf-step
          (fn-bpnf-answer-state proposal)
          (list :persist-result (fn-bpn-nth 1 effect)
                (fn-bpn-nth 2 effect) :durable)))
      st)))

(defconst *bphr-s0* (fn-bpnf-initial-state *bphr-local-config* 8 1048576))
(defconst *bphr-s1* (bphr-durable-receive *bphr-s0* *bphr-bundle*))
(defconst *bphr-held* (first (fn-bpnf-held-list *bphr-s1*)))
(defconst *bphr-key*
  (fn-bpnf-held-key (fn-bpnf-held-principal *bphr-held*)
                    (fn-bpnf-held-id *bphr-held*)))
; The host's :deliver event through the dispatcher: the marker state.
(defconst *bphr-delivery*
  (fn-bpnf-step *bphr-s1* (list :deliver *bphr-key* *bphr-local*)))
(defconst *bphr-marked* (fn-bpnf-answer-state *bphr-delivery*))
(defconst *bphr-deliver* (car (fn-bpnf-answer-effects *bphr-delivery*)))
(defconst *bphr-epoch* (fn-bpn-nth 1 *bphr-deliver*))
(defconst *bphr-marker* (fn-bpn-nth 2 *bphr-deliver*))

(defun bphr-a1 (st status detail)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpah-deliver-result-step st *bphr-epoch* *bphr-marker* *bphr-key*
                               status detail))
(defun bphr-e1 (st status detail)
  (declare (xargs :guard t :verify-guards nil))
  (car (fn-bpnf-answer-effects (bphr-a1 st status detail))))
(defun bphr-report (st status detail result)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((a1 (bphr-a1 st status detail))
         (e1 (car (fn-bpnf-answer-effects a1))))
    (fn-bpah-handoff-report
     (car (fn-bpnf-answer-effects
           (fn-bpah-persist-delivery-step
            (fn-bpnf-answer-state a1) (fn-bpn-nth 1 e1) (fn-bpn-nth 2 e1)
            result))))))
(defun bphr-applies (record held)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (ok updated handoff)
    (fn-bpah-apply-delivery record held)
    (declare (ignore updated handoff))
    ok))
(defun bphr-apply-okp (st status detail)
  (declare (xargs :guard t :verify-guards nil))
  (bphr-applies (fn-bpn-nth 3 (bphr-e1 st status detail))
                (fn-bpnf-held-list st)))
; The keystone's statement over concrete arguments.
(defun bphr-keystone (st status detail result)
  (declare (xargs :guard t :verify-guards nil))
  (let ((report (bphr-report st status detail result)))
    (and (member-equal report (list (fn-bpah-disposition-report status)
                                    :uncertain))
         (implies (and (equal result :durable)
                       (bphr-apply-okp st status detail))
                  (equal report (fn-bpah-disposition-report status))))))

(assert-event (and (fn-bpnf-heldp *bphr-held*)
                   (equal (car *bphr-deliver*) :deliver)
                   (not (fn-bpnf-issued *bphr-marked*))))

; Positive witnesses (reachable): the complete antecedent and conclusion.
; Accepted: the handoff is reported durable, naming the disposition.
(assert-event
 (and (equal (car (bphr-e1 *bphr-marked* :request-accepted '(114 105 100)))
             :persist-delivery)
      (bphr-apply-okp *bphr-marked* :request-accepted '(114 105 100))
      (equal (bphr-report *bphr-marked* :request-accepted '(114 105 100) :durable)
             :durable)
      (bphr-keystone *bphr-marked* :request-accepted '(114 105 100) :durable)))
; SCN-077's case: the Store refused the article.  Kind 7 is durable (the
; answer is (:delivery-answer :durable :request-refused)); the report is
; :refused by name, never :durable.
(assert-event
 (let* ((a1 (bphr-a1 *bphr-marked* :request-refused '(0)))
        (e1 (car (fn-bpnf-answer-effects a1)))
        (a2 (fn-bpah-persist-delivery-step (fn-bpnf-answer-state a1)
                                           (fn-bpn-nth 1 e1) (fn-bpn-nth 2 e1)
                                           :durable)))
   (and (equal (car e1) :persist-delivery)
        (bphr-apply-okp *bphr-marked* :request-refused '(0))
        (equal (fn-bpnf-answer-effects a2)
               '((:delivery-answer :durable :request-refused)))
        (equal (bphr-report *bphr-marked* :request-refused '(0) :durable)
               :refused)
        (bphr-keystone *bphr-marked* :request-refused '(0) :durable))))
; The same run through the dispatcher the host calls (fn-bpnf-step).
(assert-event
 (let* ((a1 (fn-bpnf-step *bphr-marked*
                          (list :deliver-result *bphr-epoch* *bphr-marker*
                                *bphr-key* :request-refused '(0))))
        (e1 (car (fn-bpnf-answer-effects a1)))
        (a2 (fn-bpnf-step (fn-bpnf-answer-state a1)
                          (list :persist-result (fn-bpn-nth 1 e1)
                                (fn-bpn-nth 2 e1) :durable))))
   (equal (fn-bpah-handoff-report (car (fn-bpnf-answer-effects a2)))
          :refused)))
; An uncertain publication reports :uncertain (a member of the conclusion).
(assert-event
 (equal (bphr-report *bphr-marked* :request-refused '(0) :uncertain)
        :uncertain))

; Hypothesis removal, keystone.
; (1) (car e1) = :persist-delivery.  CORRUPTED-STATE witness: a state whose
; issued operation is a pending accepted delivery under the callback
; identity (:delivery-answer :refused) answers, so the deliver-result step
; refuses (issued is set) and the persist step settles the OTHER record:
; with STATUS :request-refused the report is :durable.  Retained hypotheses
; (result :durable, apply ok) hold; the omitted one fails; the conclusion
; fails.
(defconst *bphr-accepted-issued*
  (fn-bpnf-issued (fn-bpnf-answer-state
                   (bphr-a1 *bphr-marked* :request-accepted '(114 105 100)))))
(defconst *bphr-corrupt*
  (fn-bpnf-with-issued
   *bphr-marked*
   (fn-bpnf-operation :refused nil :deliver
                      (fn-bpn-nth 4 *bphr-accepted-issued*) :pending)))
(assert-event
 (and (not (equal (car (bphr-e1 *bphr-corrupt* :request-refused '(0)))
                  :persist-delivery))
      (bphr-applies (fn-bpn-nth 4 *bphr-accepted-issued*)
                    (fn-bpnf-held-list *bphr-corrupt*))
      (equal (bphr-report *bphr-corrupt* :request-refused '(0) :durable)
             :durable)
      (not (bphr-keystone *bphr-corrupt* :request-refused '(0) :durable))))
; The weakened statement (without the hypothesis) at that instance: a
; ground formula ACL2 evaluates to false.
(must-fail
 (defthm bphr-keystone-without-issue
   (bphr-keystone *bphr-corrupt* :request-refused '(0) :durable)
   :hints (("Goal" :in-theory (disable bphr-keystone)))))
; (2) result = :durable (second conjunct).  Reachable: an uncertain
; publication with apply ok reports :uncertain, not :durable.
(assert-event
 (and (equal (car (bphr-e1 *bphr-marked* :request-accepted '(114 105 100)))
             :persist-delivery)
      (bphr-apply-okp *bphr-marked* :request-accepted '(114 105 100))
      (not (equal (bphr-report *bphr-marked* :request-accepted '(114 105 100)
                               :uncertain)
                  (fn-bpah-disposition-report :request-accepted)))))
; (3) apply ok (second conjunct).  CORRUPTED-STATE witness: a second row
; with the same arrival and no bundle ahead of the delivered row: the
; deliver-result step finds the real row by key and issues, the publication
; applies to the first row with that arrival, which does not match, so the
; durable answer is :uncertain, not the accepted disposition.
(defconst *bphr-shadow*
  (update-nth 1 *bphr-sender* (update-nth 7 nil *bphr-held*)))
(defconst *bphr-shadowed*
  (fn-bpnf-state-with-arrival
   (fn-bpnf-base *bphr-marked*)
   (cons *bphr-shadow* (fn-bpnf-held-list *bphr-marked*))
   (fn-bpnf-outcomes *bphr-marked*) (fn-bpnf-handoffs *bphr-marked*)
   (fn-bpnf-correlation *bphr-marked*) (fn-bpnf-issued *bphr-marked*)
   (fn-bpnf-waits *bphr-marked*) (fn-bpnf-epoch *bphr-marked*)
   (fn-bpnf-next-op *bphr-marked*) (fn-bpnf-next-arrival *bphr-marked*)))
(assert-event
 (and (equal (car (bphr-e1 *bphr-shadowed* :request-accepted '(114 105 100)))
             :persist-delivery)
      (not (bphr-apply-okp *bphr-shadowed* :request-accepted '(114 105 100)))
      (equal (bphr-report *bphr-shadowed* :request-accepted '(114 105 100)
                          :durable)
             :uncertain)
      (not (equal :uncertain (fn-bpah-disposition-report :request-accepted)))))

; Hypothesis removal, fn-bpah-persist-delivery-reports-exactly: each
; hypothesis dropped in turn over the accepted issued state (the retained
; ones hold, the omitted one fails, the report is :uncertain, not :durable).
(defconst *bphr-issued-state*
  (fn-bpnf-answer-state (bphr-a1 *bphr-marked* :request-accepted '(114 105 100))))
(defun bphr-exact-report (st epoch op result)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpah-handoff-report
   (car (fn-bpnf-answer-effects
         (fn-bpah-persist-delivery-step st epoch op result)))))
(defconst *bphr-e* (fn-bpn-nth 1 *bphr-accepted-issued*))
(defconst *bphr-o* (fn-bpn-nth 2 *bphr-accepted-issued*))
(assert-event
 (and (equal (bphr-exact-report *bphr-issued-state* *bphr-e* *bphr-o* :durable)
             :durable)
      ; matchp dropped
      (equal (bphr-exact-report *bphr-issued-state* (1+ *bphr-e*) *bphr-o*
                                :durable) :uncertain)
      ; :deliver dropped
      (equal (bphr-exact-report
              (fn-bpnf-with-issued *bphr-issued-state*
                                   (update-nth 3 :family *bphr-accepted-issued*))
              *bphr-e* *bphr-o* :durable) :uncertain)
      ; :pending dropped
      (equal (bphr-exact-report
              (fn-bpnf-with-issued *bphr-issued-state*
                                   (update-nth 5 :uncertain *bphr-accepted-issued*))
              *bphr-e* *bphr-o* :durable) :uncertain)
      ; :durable dropped
      (equal (bphr-exact-report *bphr-issued-state* *bphr-e* *bphr-o* :uncertain)
             :uncertain)))

; The report function: a refusing disposition is never :durable.
(assert-event
 (and (equal (fn-bpah-handoff-report '(:delivery-answer :durable :request-refused))
             :refused)
      (equal (fn-bpah-handoff-report '(:delivery-answer :durable :receipt-refused))
             :refused)
      (equal (fn-bpah-handoff-report '(:delivery-answer :durable :request-accepted))
             :durable)
      (equal (fn-bpah-handoff-report '(:delivery-answer :durable)) :uncertain)
      (equal (fn-bpah-handoff-report '(:delivery-answer :refused)) :refused)
      (equal (fn-bpah-handoff-report '(:delivery-answer :uncertain)) :uncertain)))
