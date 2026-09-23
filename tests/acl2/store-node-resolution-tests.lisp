; Resolution traces for synchronous refusal and known prepublication abort.
(in-package "ACL2")
(include-book "../../books/store-node-resolution")
(include-book "../../books/codec-attach")

(defconst *snr-groups* '("fn.letters" "fn.test"))

(defun fn-snr-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))

(defun fn-snr-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))

(defconst *snr-initial* (fn-sn-initial *snr-groups* 10))
(defconst *snr-reserved-zero* (fn-snr-reserve *snr-initial*))
(defconst *snr-refused-zero*
  (fn-sn-refuse-reservation *snr-reserved-zero* 0))

(assert-event (fn-snt-relation *snr-refused-zero*))
(assert-event (equal (fn-sf-phase (fn-sn-files *snr-refused-zero*)) :ready))
(assert-event (equal (fn-sf-frontier (fn-sn-files *snr-refused-zero*)) 1))
(assert-event (equal (fn-state-next-txid
                      (fn-node-acceptance (fn-sn-node *snr-refused-zero*))) 1))
(assert-event (not (fn-sf-successes (fn-sn-files *snr-refused-zero*))))

; The consumed reservation cannot be prepared.  A fresh reservation uses txid
; one while journal sequence zero remains available and can complete normally.
(defconst *snr-stale-record*
  (fn-record-make 0 0 0 "<stale@example>" '(65) *snr-groups*
                  "stale-pin" "stale-content" "stale-release" 1 841000000))
(assert-event
 (equal (fn-sn-prepare *snr-refused-zero* *snr-stale-record*)
        *snr-refused-zero*))

(defconst *snr-reserved-one* (fn-snr-reserve *snr-refused-zero*))
(defconst *snr-record-one*
  (fn-record-make 0 1 1 "<one@example>" '(66) *snr-groups*
                  "one-pin" "one-content" "one-release" 1 841000000))
(defconst *snr-prepared-one*
  (fn-sn-prepare *snr-reserved-one* *snr-record-one*))
(defconst *snr-finished-one*
  (fn-sn-finish (fn-snr-publish *snr-prepared-one*)))
(assert-event (fn-snt-relation *snr-finished-one*))
(assert-event (equal (fn-sf-successes (fn-sn-files *snr-finished-one*))
                     '((0 . 1))))
(assert-event
 (fn-sn-committed-recordp (fn-sn-node *snr-finished-one*) *snr-record-one*))

; A staged candidate can be resolved as known absent.  The actual pending node
; is aborted at its exact txid/generation and the file reservation is consumed.
(defconst *snr-abort-record*
  (fn-record-make 0 0 0 "<abort@example>" '(67) *snr-groups*
                  "abort-pin" "abort-content" "abort-release" 1 841000000))
(defconst *snr-abort-prepared*
  (fn-sn-prepare *snr-reserved-zero* *snr-abort-record*))
(defconst *snr-aborted* (fn-sn-known-abort *snr-abort-prepared*))
(assert-event (fn-snt-relation *snr-aborted*))
(assert-event (equal (fn-sf-phase (fn-sn-files *snr-aborted*)) :ready))
(assert-event (equal (fn-state-next-txid
                      (fn-node-acceptance (fn-sn-node *snr-aborted*))) 1))
(assert-event (not (fn-state-articles
                    (fn-node-acceptance (fn-sn-node *snr-aborted*)))))
(assert-event (not (fn-retain-pins (fn-node-retention (fn-sn-node *snr-aborted*)))))
(assert-event (not (fn-sf-successes (fn-sn-files *snr-aborted*))))
(assert-event (equal (fn-sn-known-abort *snr-aborted*) *snr-aborted*))

; The same resolution is valid after the record file barrier, but ceases to be
; available once immutable publication has been attempted.
(defconst *snr-data-durable*
  (fn-sn-io *snr-abort-prepared* :record-file :ok))
(defconst *snr-data-aborted* (fn-sn-known-abort *snr-data-durable*))
(assert-event (fn-snt-relation *snr-data-aborted*))
(assert-event (equal *snr-data-aborted* *snr-aborted*))

(defconst *snr-after-link*
  (fn-sn-io *snr-data-durable* :record-link :ok))
(assert-event (equal (fn-sf-phase (fn-sn-files *snr-after-link*))
                     :record-attempted))
(assert-event (equal (fn-sn-known-abort *snr-after-link*) *snr-after-link*))
(assert-event (equal (fn-sn-refuse-reservation *snr-after-link* 0)
                     *snr-after-link*))
