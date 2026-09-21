; fn: correspondence for the native shared-owner prepare call.
;
; The native owner owns the live configured owner, not a bare store.  Its
; POST path used to reach fn-sn-prepare through
;
;   fn-ocfg-step -> fn-ocfg-pass -> fn-own-step -> fn-own-store-step
;
; and therefore paid the specification's complete-history replay for every
; accepted candidate.  This book lifts the store projection through exactly
; those owner/configuration wrappers.  It does not test a recognizer or the
; correspondence relation at execution time.

(in-package "ACL2")

(include-book "owner-config")
(include-book "store-prepare-correspondence")

; The owner-level projection changes only the store field, then performs the
; same refresh as fn-own-store-step.  Every other owner field is copied from
; the live owner rather than reconstructed by the host.
(defun fn-opc-owner-prepare (o record)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))
                  :verify-guards nil))
  (fn-own-refresh
   (fn-own-make (fn-spc-prepare (fn-own-store o) record)
                (fn-own-view o) (fn-own-conns o)
                (fn-own-next-id o) (fn-own-max-conns o)
                (fn-own-pending o) (fn-own-ledger o)
                (fn-own-clock o) (fn-own-facts o)
                (fn-own-config o) (fn-own-queue o)
                (fn-own-inflight o) (fn-own-feeds o))))

(verify-guards fn-opc-owner-prepare)

; This is the subject called by host/owner-host.lisp:fn-owner-prepare.  The
; configured-owner wrapper preserves the live configuration, every pin, and
; any staged configuration record byte-for-byte.
(defun fn-opc-prepare (oc record)
  (declare (xargs :guard (fn-sn-statep
                          (fn-own-store (fn-ocfg-owner oc)))))
  (fn-ocfg-with-owner
   oc (fn-opc-owner-prepare (fn-ocfg-owner oc) record)))

; The owner relation contains the store-node trace relation needed by the
; lower correspondence theorem.  Keeping this bridge named makes the exact
; maintained premise visible without adding it to the executable path.
(local
 (defthm fn-opc-owner-relation-implies-store-relation
   (implies (fn-own-relation o)
            (fn-snt-relation (fn-own-store o)))
   :hints (("Goal" :in-theory (enable fn-own-relation)))))

(defthm fn-opc-owner-prepare-equals-owner-store-step-under-relation
  (implies (fn-own-relation o)
           (equal (fn-opc-owner-prepare o record)
                  (fn-own-store-step o (list :prepare record))))
  :hints (("Goal"
           :use ((:instance fn-spc-prepare-equals-specification-under-relation
                            (s (fn-own-store o))))
           :in-theory
           (e/d (fn-opc-owner-prepare fn-own-store-step fn-snrt-step
                                      fn-snt-step)
                (fn-own-relation fn-spc-prepare fn-sn-prepare
                 fn-spc-prepare-equals-specification-under-relation)))))

; KEYSTONE.  This equality names both sides of the actual native owner call:
; fn-opc-prepare is now invoked by fn-owner-prepare, while the right side is
; the previous configured-owner event.  Its sole premise is maintained from
; observed recovery through the owner transitions below.
(defthm fn-opc-prepare-equals-owner-event-under-relation
  (implies (fn-own-relation (fn-ocfg-owner oc))
           (equal (fn-opc-prepare oc record)
                  (fn-ocfg-step oc (list :store (list :prepare record)))))
  :hints (("Goal"
           :use ((:instance
                  fn-opc-owner-prepare-equals-owner-store-step-under-relation
                  (o (fn-ocfg-owner oc))))
           :in-theory
           (e/d (fn-opc-prepare fn-ocfg-step fn-ocfg-pass fn-own-step)
                (fn-own-relation fn-opc-owner-prepare fn-own-store-step
                 fn-opc-owner-prepare-equals-owner-store-step-under-relation)))))

; The fast transition carries the same owner/store relation used to license
; the next prepare.  No relation test occurs in fn-opc-prepare.
(defthm fn-opc-prepare-preserves-owner-relation
  (implies (fn-own-relation (fn-ocfg-owner oc))
           (fn-own-relation (fn-ocfg-owner
                             (fn-opc-prepare oc record))))
  :hints (("Goal"
           :use (fn-opc-prepare-equals-owner-event-under-relation
                 (:instance fn-own-step-preserves-relation
                            (o (fn-ocfg-owner oc))
                            (event (list :store (list :prepare record)))))
           :in-theory
           (e/d (fn-ocfg-step fn-ocfg-pass)
                (fn-opc-prepare fn-own-step fn-own-relation
                 fn-opc-prepare-equals-owner-event-under-relation
                 fn-own-step-preserves-relation)))))

; Every configured-owner event the native host can issue carries the same
; owner relation.  The configuration wrapper sometimes handles connection
; pins or a staged configuration record specially, but its owner component
; is always one of the already proved owner transitions (or unchanged).
(defthm fn-opc-configured-step-preserves-owner-relation
  (implies (fn-own-relation (fn-ocfg-owner oc))
           (fn-own-relation (fn-ocfg-owner (fn-ocfg-step oc event))))
  :hints
  (("Goal"
    :use ((:instance fn-own-open-preserves-relation
                     (o (fn-ocfg-owner oc)) (acfg (cadr event)))
          (:instance fn-own-open-peer-preserves-relation
                     (o (fn-ocfg-owner oc)) (peer (cadr event))
                     (cfg (fn-ocfg-config oc)) (acfg (cadddr event)))
          (:instance fn-own-read-preserves-relation
                     (o (fn-ocfg-owner oc)) (id (cadr event))
                     (octets (caddr event)))
          (:instance fn-own-read-step-preserves-relation
                     (o (fn-ocfg-owner oc)) (id (cadr event))
                     (event (caddr event)))
          (:instance fn-own-advance-preserves-relation
                     (o (fn-ocfg-owner oc)) (id (cadr event)))
          (:instance fn-own-close-preserves-relation
                     (o (fn-ocfg-owner oc)) (id (cadr event)))
          (:instance fn-own-complete-preserves-relation
                     (o (fn-ocfg-owner oc)))
          (:instance fn-own-step-preserves-relation
                     (o (fn-ocfg-owner oc))))
    :in-theory
    (e/d (fn-ocfg-step fn-ocfg-open fn-ocfg-open-peer fn-ocfg-read
                        fn-ocfg-read-step fn-ocfg-advance fn-ocfg-close
                        fn-ocfg-fault fn-own-fault fn-ocfg-reconfigure
                        fn-ocfg-complete fn-ocfg-pass fn-ocfg-with-owner)
         (fn-own-relation fn-own-open fn-own-open-peer fn-own-read
          fn-own-read-step fn-own-advance fn-own-close fn-own-complete
          fn-own-step fn-own-open-preserves-relation
          fn-own-open-peer-preserves-relation fn-own-read-preserves-relation
          fn-own-read-step-preserves-relation fn-own-advance-preserves-relation
          fn-own-close-preserves-relation fn-own-complete-preserves-relation
          fn-own-step-preserves-relation)))))

(defthm fn-opc-configured-run-preserves-owner-relation
  (implies (fn-own-relation (fn-ocfg-owner oc))
           (fn-own-relation (fn-ocfg-owner (fn-ocfg-run oc events))))
  :hints (("Goal" :induct (fn-ocfg-run oc events)
           :in-theory
           (e/d (fn-ocfg-run)
                (fn-ocfg-step fn-own-relation)))))

; These are the configured-owner functions the host calls directly for
; socket membership and input.  Stating them together avoids treating the
; uncalled run helper above as evidence for those entries.
(defthm fn-opc-direct-configured-entries-preserve-owner-relation
  (implies
   (fn-own-relation (fn-ocfg-owner oc))
   (and (fn-own-relation (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))
        (fn-own-relation
         (fn-ocfg-owner (cdr (fn-ocfg-open-peer oc peer acfg))))
        (fn-own-relation
         (fn-ocfg-owner (cdr (fn-ocfg-read oc id octets))))
        (fn-own-relation
         (fn-ocfg-owner (cdr (fn-ocfg-read-step oc id event))))
        (fn-own-relation
         (fn-ocfg-owner (cdr (fn-ocfg-fault oc id))))))
  :hints
  (("Goal"
    :use ((:instance fn-own-open-preserves-relation
                     (o (fn-ocfg-owner oc)))
          (:instance fn-own-open-peer-preserves-relation
                     (o (fn-ocfg-owner oc))
                     (cfg (fn-ocfg-config oc)))
          (:instance fn-own-read-preserves-relation
                     (o (fn-ocfg-owner oc)))
          (:instance fn-own-read-step-preserves-relation
                     (o (fn-ocfg-owner oc)))
          (:instance fn-own-close-preserves-relation
                     (o (fn-ocfg-owner oc))))
    :in-theory
    (e/d (fn-ocfg-open fn-ocfg-open-peer fn-ocfg-read fn-ocfg-read-step
                        fn-ocfg-fault fn-own-fault fn-ocfg-with-owner)
         (fn-own-relation fn-own-open fn-own-open-peer fn-own-read
          fn-own-read-step fn-own-close fn-own-open-preserves-relation
          fn-own-open-peer-preserves-relation fn-own-read-preserves-relation
          fn-own-read-step-preserves-relation
          fn-own-close-preserves-relation)))))

; Exact non-store effects: the configuration generation, pin table, and
; staged configuration record are unchanged by prepare.
(defthm fn-opc-prepare-keeps-configured-owner-context
  (and (equal (fn-ocfg-config (fn-opc-prepare oc record))
              (fn-ocfg-config oc))
       (equal (fn-ocfg-pins (fn-opc-prepare oc record))
              (fn-ocfg-pins oc))
       (equal (fn-ocfg-staged (fn-opc-prepare oc record))
              (fn-ocfg-staged oc)))
  :hints (("Goal" :in-theory (enable fn-opc-prepare fn-ocfg-with-owner))))

; The native writer reads these exact bytes after a successful prepare.  The
; host wrapper below calls this projection rather than duplicating it.
(defun fn-opc-pending-octets (oc)
  (declare (xargs :guard t))
  (let ((record
         (fn-sf-record-candidate
          (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
    (if record (fn-record-encode record) nil)))

; This is a projection of the equality keystone, not a second proof event.
(defthm fn-opc-pending-octets-equal-owner-event-under-relation
  (implies (fn-own-relation (fn-ocfg-owner oc))
           (equal (fn-opc-pending-octets (fn-opc-prepare oc record))
                  (fn-opc-pending-octets
                   (fn-ocfg-step oc
                                 (list :store (list :prepare record))))))
  :hints (("Goal"
           :use fn-opc-prepare-equals-owner-event-under-relation
           :in-theory
           (disable fn-opc-prepare fn-ocfg-step fn-opc-pending-octets
                    fn-opc-prepare-equals-owner-event-under-relation))))

; The recovery constructor used in host/owner-host.lisp establishes the exact
; premise: observed store opening, fn-own-start, then fn-own-configure.  The
; outer configured-owner fields do not weaken that owner relation.
(defthm fn-opc-observed-open-configured-owner-has-relation
  (implies
   (and (fn-sn-open-okp
         (fn-sn-open-observed groups capacity frontier records))
        (natp max-conns))
   (fn-own-relation
    (fn-ocfg-owner
     (fn-ocfg-make
      (fn-own-configure
       (fn-own-start
        (fn-sn-open-state
         (fn-sn-open-observed groups capacity frontier records))
        max-conns)
       config)
      live-config nil nil))))
  :hints (("Goal"
           :use (fn-own-open-observed-start-relation
                 (:instance fn-own-configure-preserves-relation
                            (o (fn-own-start
                                (fn-sn-open-state
                                 (fn-sn-open-observed
                                  groups capacity frontier records))
                                max-conns))
                            (config config)))
           :in-theory
           (disable fn-own-start fn-own-configure fn-own-relation
                    fn-own-open-observed-start-relation
                    fn-own-configure-preserves-relation))))

(in-theory (disable fn-opc-owner-prepare fn-opc-prepare
                    fn-opc-pending-octets))
