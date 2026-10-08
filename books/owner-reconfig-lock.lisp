; fn: the staged configuration record is the configuration lock across a
; phased live reconfiguration's windows (ruling 19, item
; LOCK-R2-LIVE-RECONFIGURE-IO; books/owner-reconfig-phased.lisp, the gaps).
;
; Between quantum 1 (stage, authorize) and quantum 2 (complete) of a phased
; live reconfiguration the owner releases O.  The gate then admits only
; readers and inspection (the hold, host side owed with C).  These theorems
; say what the owner's own transition guarantees across that gap:
;   L1 fn-orl-own-step-opens-no-pending: no owner event but :begin and :take
;      opens a pending article transaction (fn-ocfg-step refuses both while a
;      record is staged).
;   L2 fn-orl-staged-record-holds-the-configuration: while a record is staged
;      (and, as staging requires, no article transaction is pending), every
;      event but :complete keeps the live configuration, the staged record
;      and the empty pending slot.  :begin and :take are refused outright
;      (fn-ocfg-step), and a second :reconfigure is refused (:busy).
;   L3 fn-orl-reader-events-keep-the-authorization: across the events a
;      reader or inspection quantum sends, a record authorized in quantum 1
;      (fn-oclc-live-authorizep) is still authorized in quantum 2, so its
;      completion is :durable (fn-oclc-live-authorizep-is-durable-completion).
(in-package "ACL2")
(include-book "config-owner-carried")

; Keep the event arms visible and their data-processing callees opaque.
; Only the pending projection of a constructed owner is needed for L1.
(defthm fn-orl-own-step-opens-no-pending
  (implies (and (not (fn-own-pending o))
                (not (member-equal (car event) '(:begin :take))))
           (not (fn-own-pending (fn-own-step o event fn-arena))))
  :hints (("Goal" :in-theory
    (union-theories (theory 'minimal-theory)
     '(car-cons cdr-cons member-equal fn-own-pending-of-fn-own-make
       fn-own-step fn-own-open fn-own-open-peer fn-own-read fn-own-read-step
       fn-own-read-full fn-own-read-step-full fn-own-finish-read
       fn-own-set-conns fn-own-enqueue fn-own-advance fn-own-advance-result
       fn-own-close fn-own-store-step fn-own-refresh fn-own-complete
       fn-own-reopen fn-own-observe fn-own-declare-group fn-own-configure
       fn-own-control-submit fn-own-legacy-control-submit fn-own-bp-transit-submit
       fn-own-operator-submit fn-own-outcome fn-own-control-outcome
       fn-own-bp-transit-outcome fn-own-transit-outcome fn-own-with-feeds
       fn-own-feeds-reconfigure fn-own-feed-connect fn-own-feed-lost
       fn-own-feed-recover fn-own-tick fn-own-tick-peer fn-own-feed-reply)))))

; Staging refuses both article starters and a second reconfiguration.
(defthm fn-orl-staged-record-holds-the-configuration
  (implies (and (fn-ocfg-staged oc)
                (not (fn-own-pending (fn-ocfg-owner oc)))
                (not (equal (car event) :complete)))
           (let ((next (fn-ocfg-step oc event fn-arena)))
             (and (equal (fn-ocfg-config next) (fn-ocfg-config oc))
                  (equal (fn-ocfg-staged next) (fn-ocfg-staged oc))
                  (not (fn-own-pending (fn-ocfg-owner next))))))
  :hints (("Goal" :in-theory
    (union-theories (theory 'minimal-theory)
     '(car-cons cdr-cons natp member-equal
       fn-orl-own-step-opens-no-pending
       fn-ocfg-owner-of-fn-ocfg-make fn-ocfg-config-of-fn-ocfg-make
       fn-ocfg-staged-of-fn-ocfg-make fn-own-pending-of-fn-own-make
       fn-ocfg-step fn-ocfg-open fn-ocfg-advance fn-ocfg-close
       fn-ocfg-read fn-ocfg-read-step fn-ocfg-open-peer fn-ocfg-fault
       fn-ocfg-reconfigure fn-ocfg-reconfig-okp fn-ocfg-pass
       fn-ocfg-with-owner fn-ocfg-with-read-owner
       fn-own-open fn-own-open-peer fn-own-reader-context fn-own-set-conns
       fn-own-advance-result fn-own-close fn-own-fault
       fn-own-read-full fn-own-read-step-full fn-own-finish-read
       fn-own-enqueue)))))

; Readers retain the entire store, including the authorization history.
(local
 (defthm fn-orl-reader-events-preserve-store
   (implies (member-equal (car event) '(:open :close :read :octets :fault))
            (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-step oc event fn-arena)))
                   (fn-own-store (fn-ocfg-owner oc))))
   :hints (("Goal" :in-theory
     (union-theories (theory 'minimal-theory)
      '(car-cons cdr-cons member-equal
        fn-ocfg-owner-of-fn-ocfg-make fn-own-store-of-fn-own-make
        fn-ocfg-step fn-ocfg-open fn-ocfg-close fn-ocfg-read
        fn-ocfg-read-step fn-ocfg-fault fn-ocfg-with-read-owner
        fn-own-open fn-own-reader-context fn-own-set-conns fn-own-close
        fn-own-fault fn-own-read-full fn-own-read-step-full
        fn-own-finish-read fn-own-enqueue))))))

(defthm fn-orl-reader-events-keep-the-authorization
  (implies (and (fn-ocfg-staged oc)
                (not (fn-own-pending (fn-ocfg-owner oc)))
                (member-equal (car event) '(:open :close :read :octets :fault))
                (fn-oclc-live-authorizep oc))
           (fn-oclc-live-authorizep (fn-ocfg-step oc event fn-arena)))
  :hints (("Goal" :in-theory
    (union-theories (theory 'minimal-theory)
     '(member-equal fn-oclc-live-authorizep
       fn-orl-staged-record-holds-the-configuration
       fn-orl-reader-events-preserve-store)))))
