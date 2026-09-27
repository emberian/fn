; PRF-224 (lane bp-fragments-10mib, PKT-630 (7)): the BP application
; handoff's reported outcome is the application's disposition.
;
; SCN-077's 10 MiB case printed "BP application handoff durable" while the
; Store held no article: the receiving Store ran the development profile
; (32,768-octet articles), refused the article, the node's kind-7 record of
; that refusal became durable, and the host printed the publication's
; durability as the handoff's outcome.  A durable kind 7 completes a
; delivery at this layer whatever the application decided (spec
; bp-node-machine 3.1), so the host now prints fn-bpah-handoff-report of the
; answer, and fn-bpah-persist-delivery-step's durable answer names the
; disposition its kind-7 record holds.
;
; Host: host/native/bp-service.lisp fnn-bps-drive-effects, the
; :delivery-answer arm, prints (fn-bpah-handoff-report EFFECT) for every
; answer fnn-bps-foundation-step returns.  The two events are the ones
; host/native/bp-node.lisp fnn-bpnode-dispatch-one sends through
; fnn-bps-foundation-step (fn-bpnj-step): (:deliver-result E M KEY STATUS
; DETAIL) with the application's STATUS, then the (:persist-result E OP
; RESULT) of its kind-7 publication.  Both reach the foundation arms below
; through fn-bpnf-step (fn-bpnf-step-deliver-result-is-step,
; fn-bpnf-step-persist-delivery-is-step here; the layers above fn-bpnf-step
; pass an answer's effects through or replace a :deliver answer by
; (:delivery-answer :uncertain), fn-bpnp-publication-fault-effect).
(in-package "ACL2")
(include-book "bp-node-foundation")

(defthm fn-bpah-disposition-report-cases
  (member-equal (fn-bpah-disposition-report status)
                '(:durable :refused :uncertain))
  :rule-classes nil)

; A refusal is never reported durable, and only an accepting disposition is.
(defthm fn-bpah-disposition-report-durable-is-accepting
  (equal (equal (fn-bpah-disposition-report status) :durable)
         (fn-bpah-accepting-dispositionp status)))

(defthm fn-bpah-disposition-report-of-refusal
  (implies (fn-bpah-refusing-dispositionp status)
           (equal (fn-bpah-disposition-report status) :refused)))

; The step: every answer of the kind-7 publication step reports either the
; disposition its issued record holds or :uncertain, and a durable report
; needs a durable publication.
(defthm fn-bpah-persist-delivery-reports-the-record
  (let ((report (fn-bpah-handoff-report
                 (car (fn-bpnf-answer-effects
                       (fn-bpah-persist-delivery-step st epoch op result))))))
    (and (member-equal report
                       (list (fn-bpah-disposition-report
                              (fn-bpn-nth 5 (fn-bpn-nth 4 (fn-bpnf-issued st))))
                             :uncertain))
         (implies (equal report :durable)
                  (equal result :durable))))
  :hints (("Goal" :in-theory (disable fn-bpah-apply-delivery
                                      fn-bpah-disposition-report
                                      fn-bpnf-state-with-arrival
                                      fn-bpnf-with-issued)))
  :rule-classes nil)

(defthm fn-bpah-persist-delivery-reports-exactly
  (implies (and (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op)
                (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :deliver)
                (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)
                (equal result :durable)
                (mv-nth 0 (fn-bpah-apply-delivery
                           (fn-bpn-nth 4 (fn-bpnf-issued st))
                           (fn-bpnf-held-list st))))
           (equal (fn-bpah-handoff-report
                   (car (fn-bpnf-answer-effects
                         (fn-bpah-persist-delivery-step st epoch op result))))
                  (fn-bpah-disposition-report
                   (fn-bpn-nth 5 (fn-bpn-nth 4 (fn-bpnf-issued st))))))
  :hints (("Goal" :in-theory (disable fn-bpah-apply-delivery
                                      fn-bpah-disposition-report
                                      fn-bpnf-state-with-arrival
                                      fn-bpnf-with-issued)))
  :rule-classes nil)

; What the deliver-result step issues when it proposes kind 7: the pending
; :deliver operation whose record carries the application's STATUS, over
; the unchanged held list.
(local
 (defthm fn-bpah-deliver-result-step-issues-status
   (let* ((a1 (fn-bpah-deliver-result-step st epoch marker key status detail))
          (e1 (car (fn-bpnf-answer-effects a1)))
          (s1 (fn-bpnf-answer-state a1)))
     (implies (equal (car e1) :persist-delivery)
              (and (fn-bpnf-operation-matchp (fn-bpnf-issued s1)
                                             (fn-bpn-nth 1 e1)
                                             (fn-bpn-nth 2 e1))
                   (equal (fn-bpn-nth 3 (fn-bpnf-issued s1)) :deliver)
                   (equal (fn-bpn-nth 5 (fn-bpnf-issued s1)) :pending)
                   (equal (fn-bpn-nth 4 (fn-bpnf-issued s1)) (fn-bpn-nth 3 e1))
                   (equal (fn-bpn-nth 5 (fn-bpn-nth 3 e1)) status)
                   (equal (fn-bpnf-held-list s1) (fn-bpnf-held-list st)))))
   :hints (("Goal" :in-theory (disable fn-bpah-delivery-matches-heldp
                                       fn-bpnf-find-held
                                       fn-bpah-held-primary-identity
                                       fn-frame-natp)))
   :rule-classes nil))

; KEYSTONE: the handoff's outcome is the application's.  After the
; application's STATUS is recorded (the deliver-result step issues the kind-7
; publication), the publication's answer reports STATUS's disposition or
; :uncertain; with a durable publication that applies to the held row it
; reports exactly STATUS's disposition.  So a refused delivery is reported
; refused by name, never durable.
(defthm fn-bpah-handoff-report-is-application-disposition
  (let* ((a1 (fn-bpah-deliver-result-step st epoch marker key status detail))
         (e1 (car (fn-bpnf-answer-effects a1)))
         (a2 (fn-bpah-persist-delivery-step
              (fn-bpnf-answer-state a1) (fn-bpn-nth 1 e1) (fn-bpn-nth 2 e1)
              result))
         (report (fn-bpah-handoff-report (car (fn-bpnf-answer-effects a2)))))
    (implies (equal (car e1) :persist-delivery)
             (and (member-equal report
                                (list (fn-bpah-disposition-report status)
                                      :uncertain))
                  (implies (and (equal result :durable)
                                (mv-nth 0 (fn-bpah-apply-delivery
                                           (fn-bpn-nth 3 e1)
                                           (fn-bpnf-held-list st))))
                           (equal report
                                  (fn-bpah-disposition-report status))))))
  :hints (("Goal"
           :use ((:instance fn-bpah-deliver-result-step-issues-status)
                 (:instance fn-bpah-persist-delivery-reports-the-record
                            (st (fn-bpnf-answer-state
                                 (fn-bpah-deliver-result-step
                                  st epoch marker key status detail)))
                            (epoch (fn-bpn-nth 1 (car (fn-bpnf-answer-effects
                                                       (fn-bpah-deliver-result-step
                                                        st epoch marker key status detail)))))
                            (op (fn-bpn-nth 2 (car (fn-bpnf-answer-effects
                                                    (fn-bpah-deliver-result-step
                                                     st epoch marker key status detail))))))
                 (:instance fn-bpah-persist-delivery-reports-exactly
                            (st (fn-bpnf-answer-state
                                 (fn-bpah-deliver-result-step
                                  st epoch marker key status detail)))
                            (epoch (fn-bpn-nth 1 (car (fn-bpnf-answer-effects
                                                       (fn-bpah-deliver-result-step
                                                        st epoch marker key status detail)))))
                            (op (fn-bpn-nth 2 (car (fn-bpnf-answer-effects
                                                    (fn-bpah-deliver-result-step
                                                     st epoch marker key status detail)))))))
           :in-theory (disable fn-bpah-deliver-result-step
                               fn-bpah-persist-delivery-step
                               fn-bpah-apply-delivery
                               fn-bpah-disposition-report
                               fn-bpah-handoff-report
                               fn-bpnf-operation-matchp)))
  :rule-classes nil)

; The foundation dispatcher routes the two host events to these steps.
(defthm fn-bpnf-step-persist-delivery-is-step
  (implies (and (not (fn-bpah-delivery-uncertainp st))
                (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op)
                (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :deliver)
                (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending))
           (equal (fn-bpnf-step st (list :persist-result epoch op result))
                  (fn-bpah-persist-delivery-step st epoch op result)))
  :hints (("Goal" :in-theory (disable fn-bpah-persist-delivery-step
                                      fn-bpn-step))))

(defthm fn-bpnf-step-deliver-result-is-step
  (implies (not (fn-bpah-delivery-uncertainp st))
           (equal (fn-bpnf-step st (list :deliver-result epoch marker key
                                         status detail))
                  (fn-bpah-deliver-result-step st epoch marker key status
                                               detail)))
  :hints (("Goal" :in-theory (disable fn-bpah-deliver-result-step
                                      fn-bpn-step))))
