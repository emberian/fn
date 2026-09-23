; E2 durable Store event witnesses through prepare, file publication, finish,
; crash and observed reopen.  No host consumer command uses this path yet.
(in-package "ACL2")
(include-book "../../books/store-observed")
(include-book "../../books/consumer-store-projection")
(include-book "../../books/config-physical-replay")

(defun csnt-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun csnt-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))
(defun csnt-commit (s event)
  (fn-sn-finish (csnt-publish (fn-sn-prepare-consumer
                              (csnt-reserve s) event))))

(defconst *csnt-boot* (fn-cpe-make 0 0 0 '(:bootstrap (1) (2))))
(defconst *csnt-reg* (fn-cpe-make 1 1 1 '(:register (3) (4) (5) 1 1 1)))
(defconst *csnt-cursor* (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 1 1 2))
(defconst *csnt-ack* (fn-cpe-make 2 2 2 (list :ack *csnt-cursor*)))
(defconst *csnt-initial* (fn-sn-initial '("g") 32))
(defconst *csnt-after-boot* (csnt-commit *csnt-initial* *csnt-boot*))
(assert-event (equal (fn-sf-phase (fn-sn-files *csnt-after-boot*)) :ready))
(assert-event (equal (nth 3 (fn-sn-consumer *csnt-after-boot*)) 1))
(assert-event (equal (fn-sn-identity-next *csnt-after-boot*) 1))
(assert-event (equal (fn-sn-prepare-consumer (csnt-reserve *csnt-after-boot*)
                                           (fn-cpe-make 1 1 1 '(:bootstrap (1) (2))))
                     (csnt-reserve *csnt-after-boot*)))
(defconst *csnt-after-reg* (csnt-commit *csnt-after-boot* *csnt-reg*))
(assert-event (equal (nth 3 (fn-sn-consumer *csnt-after-reg*)) 2))
(assert-event (equal (nth 6 (fn-cp-find '(3) (nth 5 (fn-sn-consumer *csnt-after-reg*)))) 1))
(defconst *csnt-after-ack* (csnt-commit *csnt-after-reg* *csnt-ack*))
(assert-event (equal (nth 3 (fn-sn-consumer *csnt-after-ack*)) 3))
(assert-event (equal (nth 7 (fn-cp-find '(3) (nth 5 (fn-sn-consumer *csnt-after-ack*)))) 2))
(assert-event (equal (fn-sn-index *csnt-after-ack*) (fn-sn-index *csnt-initial*)))
(assert-event (equal (fn-sn-node *csnt-after-ack*)
                     (fn-sf-replay-node '("g") 32
                                        (list *csnt-boot* *csnt-reg* *csnt-ack*) 3)))

; Reopen discards the live projection and reconstructs it from the committed
; bytes.  The same projection is obtained by a normal model crash/recovery.
(defconst *csnt-open*
  (fn-sn-open-observed '("g") 32 3
                       (list *csnt-boot* *csnt-reg* *csnt-ack*)))
(assert-event (equal (fn-sn-open-kind *csnt-open*) :ok))
(assert-event (equal (fn-sn-consumer (fn-sn-open-state *csnt-open*))
                     (fn-sn-consumer *csnt-after-ack*)))
(assert-event (equal (fn-sn-consumer
                      (fn-sn-recover (fn-sn-crash *csnt-after-ack* :old :absent)))
                     (fn-sn-consumer *csnt-after-ack*)))

; Config generation 2 at txid 1 precedes the registration event at txid 1,
; while Store events keep their own dense sequence.  The consumer event is
; transaction-neutral for the configured article node and still advances its
; Store prefix coordinate.
(defconst *csnt-tied-config*
  (fn-cfg-record-make 1 1 2 (list (fn-cfg-set-capacity 64))
                      *fn-cfg-default-stamp*))
(defconst *csnt-physical-open*
  (fn-cpr-replay (list *fn-cfg-default-record* *csnt-tied-config*)
                 (list *csnt-boot* *csnt-reg* *csnt-ack*)))
(assert-event (equal (fn-replay-result-kind *csnt-physical-open*) :ok))
(assert-event
 (equal (fn-state-next-txid
         (fn-node-acceptance
          (fn-cnode-node (fn-replay-result-node *csnt-physical-open*))))
        3))


; The staged write has no durable acknowledgement; a known absent link
; leaves the previously committed registration unchanged after recovery.
(defconst *csnt-staged-ack*
  (fn-sn-prepare-consumer (csnt-reserve *csnt-after-reg*) *csnt-ack*))
(assert-event (equal (fn-sn-consumer *csnt-staged-ack*)
                     (fn-sn-consumer *csnt-after-reg*)))

; The article/identity replay can accept this shape, but consumer recovery
; rejects a registration without its committed bootstrap.
(assert-event (not (fn-sn-observed-consumer-okp (list
                  (fn-cpe-make 0 0 0 '(:register (3) (4) (5) 1 1 1))))))
(assert-event
 (equal (fn-sn-open-kind
         (fn-sn-open-observed '("g") 32 1
          (list (fn-cpe-make 0 0 0 '(:register (3) (4) (5) 1 1 1)))))
        :error))
(defconst *csnt-absent*
  (fn-sn-recover
   (fn-sn-crash (fn-sn-io (fn-sn-io *csnt-staged-ack* :record-file :ok)
                            :record-link :error)
                :old :absent)))
(assert-event (equal (fn-sn-consumer *csnt-absent*)
                     (fn-sn-consumer *csnt-after-reg*)))

; A damaged live projection cannot be papered over at the durable finish.
; The file barrier has appended the ack, but the consumer frontier required
; for that record is absent, so the actual completion entrypoint stays fenced.
(defconst *csnt-bad-completion*
  (fn-sn-with-consumer (csnt-publish *csnt-staged-ack*) nil))
(assert-event (fn-sn-statep *csnt-bad-completion*))
(assert-event (not (fn-sn-completion-enabledp *csnt-bad-completion*)))
(assert-event (equal (fn-sn-finish *csnt-bad-completion*)
                     *csnt-bad-completion*))
