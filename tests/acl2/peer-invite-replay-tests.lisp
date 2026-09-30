(in-package "ACL2")
(include-book "peer-invite-retry-tests")
(include-book "../../books/peer-invite-replay")

(defmacro par-replay-record (stamp)
  `(fn-cfg-record-make 1 1 1 (list (par-delta)) ,stamp))
(defmacro par-replay-result (stamp)
  `(fn-config-replay-loop (fn-cfg-initial) 0 512
                          (list (par-replay-record ,stamp))))
(defmacro par-replayed-plan (cfg)
  `(fn-par-accept-record-plan
    (pit-inv) *pit-a-ml* :verified :verified (pit-a-snapshots)
    (fn-cfg-peers (fn-cfg-value ,cfg)) *par-ident* (fn-cfg-generation ,cfg)))

; Reachable accepted record: the full antecedent and replay conclusion.
(assert-event
 (fn-cfg-record-acceptablep (fn-cfg-initial)
                            (par-replay-record (fn-clock-observation 7 1000 5 t))
                            0 512))
(assert-event
 (let ((stamp (fn-clock-observation 7 1000 5 t)))
   (and (equal (list (car (par-plan)) (fn-cfg-delta-kind (par-delta)))
               '(:configure :accept-peer))
        (fn-cfg-record-acceptablep (fn-cfg-initial) (par-replay-record stamp) 0 512)
        (equal (par-replayed-plan (par-replay-result stamp)) '(:resume)))))

; Missing acceptability: keep the producer trigger, refuse a malformed stamp.
(assert-event
 (and (equal (list (car (par-plan)) (fn-cfg-delta-kind (par-delta)))
              '(:configure :accept-peer))
      (not (fn-cfg-record-acceptablep (fn-cfg-initial) (par-replay-record nil) 0 512))
      (equal (par-replay-result nil) :fault)
      (not (equal (par-replayed-plan (par-replay-result nil)) '(:resume)))))

 ; Missing internal producer trigger: unknown-inviter configuration needs enrolment.
(assert-event
 (let* ((plan (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                                       nil nil *par-ident* 0))
        (delta (fn-cfg-ag-car (fn-pinv-at 1 plan)))
        (record (fn-cfg-record-make 1 1 1 (list delta)
                                    (fn-clock-observation 7 1000 5 t)))
        (replayed (fn-config-replay-loop (fn-cfg-initial) 0 512 (list record))))
   (and (fn-cfg-record-acceptablep (fn-cfg-initial) record 0 512)
        (not (equal (list (car plan) (fn-cfg-delta-kind delta))
                     '(:configure :accept-peer)))
        (not (equal (fn-par-accept-record-plan
                     (pit-inv) *pit-a-ml* :verified :verified nil
                     (fn-cfg-peers (fn-cfg-value replayed)) *par-ident*
                     (fn-cfg-generation replayed)) '(:resume))))))
