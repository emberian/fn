; fn: the owner's transaction observation through the concrete record twins.
;
; host/owner-host.lisp fn-owner-io reports each transaction observation to
; the owner as the event (:store (:io operation result)).  fn-ocfg-step runs
; it through fn-ocfg-pass, fn-own-step's :store arm, fn-own-store-step,
; fn-snrt-step and fn-snt-step to fn-sn-io, whose :record-directory arm
; pairs the staged record's sequence and transaction id through the list
; dispatchers (fn-sf-record-dir-result, fn-store-event-sequence/-txid).
; fn-rcon-ocfg-io is that event with fn-sn-io replaced by fn-rcon-sn-io
; (books/records-concrete.lisp); fn-rcon-ocfg-io-is-ocfg-step equates it
; with fn-ocfg-step on that event for every configured owner, operation and
; result, with no hypothesis.  Its guard is fn-sn-statep of the store, the
; guard fn-rcon-sn-io and fn-sn-io share, which fn-own-relation carries.
;
; A separate book because the owner closure (owner-config) is not in the
; developer store and DTN images that load host/store-host.lisp and
; host/store-node-host.lisp, which call the store-level twins.

(in-package "ACL2")
(include-book "records-concrete")
(include-book "owner-config")

; The owner's transaction observation, the host's fn-owner-io: fn-ocfg-step
; of (:store (:io operation result)) is fn-ocfg-pass, fn-own-step's :store
; arm, fn-snrt-step's and fn-snt-step's :io arm, which is fn-sn-io.
(defun fn-rcon-own-store-io (o operation result)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))))
  (fn-own-refresh
   (fn-own-make (fn-rcon-sn-io (fn-own-store o) operation result) (fn-own-view o)
                (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
                (fn-own-pending o) (fn-own-ledger o) (fn-own-clock o)
                (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o))))
(defun fn-rcon-ocfg-io (oc operation result)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
  (fn-ocfg-with-owner oc (fn-rcon-own-store-io (fn-ocfg-owner oc) operation result)))
(defthm fn-rcon-ocfg-io-is-ocfg-step
  (equal (fn-rcon-ocfg-io oc operation result)
         (fn-ocfg-step oc (list :store (list :io operation result))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-ocfg-io fn-rcon-own-store-io fn-ocfg-step fn-ocfg-pass
                                fn-own-step fn-own-store-step fn-snrt-step fn-snt-step
                                fn-rcon-sn-io-is-sn-io car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(in-theory (disable fn-rcon-own-store-io fn-rcon-ocfg-io))
