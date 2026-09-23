; A physical recovery image whose accepted historical undertaking exceeded
; the final (validly reduced) capacity. The observed opener must preserve it.
(in-package "ACL2")
(include-book "../../books/config-observed")

(defconst *cpo-t-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "forward-cpo" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "forward-cpo" "subject" "evidence" 0)))
(defconst *cpo-t-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1))
                            *fn-cfg-default-stamp*)))
(defconst *cpo-t-open*
  (fn-cpo-open-observed *cpo-t-configs* 8 *cpo-t-events*))

(assert-event (fn-sn-observed-historyp 8 *cpo-t-events*))
(assert-event (fn-sn-open-okp *cpo-t-open*))
(assert-event
 (equal (fn-sn-capacity (fn-sn-open-state *cpo-t-open*)) 1))
(assert-event
 (equal (fn-sf-records (fn-sn-files (fn-sn-open-state *cpo-t-open*)))
        *cpo-t-events*))
(assert-event
 (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state *cpo-t-open*)))
        :recovering))
(assert-event
 (equal (fn-sn-config-history (fn-sn-open-state *cpo-t-open*))
        *cpo-t-configs*))
(assert-event
 (fn-cpo-history-relation (fn-sn-open-state *cpo-t-open*)))
(assert-event
 (equal (fn-sn-open-kind
         (fn-sn-open-observed '("fn.letters" "fn.test") 1
                              8 *cpo-t-events*))
        :error))

; A configuration illegally placed before the release is refused at its
; historical reservation total, even though its final capacity could hold
; the post-release state.
(assert-event
 (equal (fn-sn-open-kind
         (fn-cpo-open-observed
          (list *fn-cfg-default-record*
                (fn-cfg-record-make 1 1 2 (list (fn-cfg-set-capacity 1))
                                    *fn-cfg-default-stamp*))
          8 *cpo-t-events*))
        :error))

; The five real recovery barriers are still required before an administrative
; config transition. It changes the carried history, domain/capacity and node
; together, while the Store event list and frontier remain exact.
(defconst *cpo-t-ready*
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io
             (fn-sn-open-state *cpo-t-open*) :recovery-barrier :ok)
             :recovery-barrier :ok) :recovery-barrier :ok)
             :recovery-barrier :ok) :recovery-barrier :ok))
(defconst *cpo-t-increase*
  (fn-cfg-record-make 2 8 3 (list (fn-cfg-set-capacity 20))
                      *fn-cfg-default-stamp*))
(defconst *cpo-t-live*
  (fn-cpo-configure-durable *cpo-t-ready* *cpo-t-increase*))
(assert-event (equal (fn-sf-phase (fn-sn-files *cpo-t-ready*)) :ready))
(assert-event (fn-cpo-history-relation *cpo-t-ready*))
(assert-event (fn-cpo-history-relation *cpo-t-live*))
(assert-event (equal (fn-sn-capacity *cpo-t-live*) 20))
(assert-event (equal (fn-sn-config-history *cpo-t-live*)
                     (append *cpo-t-configs* (list *cpo-t-increase*))))
(assert-event (equal (fn-sf-records (fn-sn-files *cpo-t-live*))
                     *cpo-t-events*))
(assert-event (equal (fn-sf-frontier (fn-sn-files *cpo-t-live*)) 8))
(assert-event
 (equal (fn-cpo-configure-durable
         *cpo-t-ready*
         (fn-cfg-record-make 2 8 3 (list (fn-cfg-set-capacity 0))
                             *fn-cfg-default-stamp*))
        *cpo-t-ready*))
