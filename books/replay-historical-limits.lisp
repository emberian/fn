; fn: the historical limits at replay (row S1 item 3, lane limits-live-8,
; PRF-1026).
;
; A limit the operator changes is a configuration record (`:set-limit', books/
; config.lisp fn-cfg-set-limit; books/limits-live.lisp).  The claim: a store
; event is admitted at replay by the node and the configuration in force at
; its position in the history (books/config-physical-replay.lisp
; `fn-cpr-loop', the position-by-position fold), and no `:set-limit' value
; enters that decision: an article accepted under a limit is replayed after
; the limit is lowered below its size.  What replay does decide
; historically is the retention capacity (`:set-capacity'), carried in the
; node (`fn-cnode-statep': the node's capacity is the configuration's).
;
; The statement is an invariance.  Two histories that differ only in the
; values of their `:set-limit' deltas (`fn-rhl-configs-variantp': each pair
; of records equal once those values are blanked, and each record of the
; pair decoded, fitting and within its limit ceilings alike) fold to the
; same node, the same position and the same verdict: the results are equal
; once the configurations' limit slots are blanked (`fn-rhl-blank-result').
;
; The host's subject: host/store-node-host.lisp fn-store-sn-recover-rows
; calls books/replay-identity-index.lisp `fn-rii-sco-extend-open', whose
; extension is the checkpoint extension (fn-rii-sco-extend-is-sco-extend)
; and whose configuration fold over the capture of an admitted history is
; the full replay `fn-cpr-replay' (books/store-checkpoint-open.lisp
; fn-sco-extend-of-capture-when-history).  The keystone
; `fn-rhl-extend-open-is-limit-free' is stated over that call.
;
; Scope: the fold's node and verdict.  The log-scan bounds the open applies
; before the fold (max-record-octets, max-open-suffix) are the sealed
; profile's (books/limits-live.lisp's header), not configuration values.

(in-package "ACL2")

(include-book "replay-identity-index")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Blanking the limit values

(defun fn-rhl-blank-value (v)
  ; The configuration value with its limits slot (the seventh) emptied.
  (declare (xargs :guard t))
  (fn-cfg-value-make-full (fn-cfg-groups v) (fn-cfg-capacity v)
                          (fn-cfg-quotas v) (fn-cfg-policies v)
                          (fn-cfg-listeners v) (fn-cfg-peers v)
                          nil
                          (fn-cfg-authorities v) (fn-cfg-invitations v)
                          (fn-cfg-accounts v) (fn-cfg-descriptions v)))

(defun fn-rhl-blank-cfg (c)
  (declare (xargs :guard t))
  (fn-cfg-make (fn-cfg-generation c) (fn-rhl-blank-value (fn-cfg-value c))))

(defun fn-rhl-blank-cnode (cn)
  (declare (xargs :guard t))
  (fn-cnode-make (fn-cnode-node cn) (fn-rhl-blank-cfg (fn-cnode-config cn))))

(defun fn-rhl-blank-result (r)
  ; A fold's result, (:ok CN POSITION) or (:fault CN POSITION REASON), with
  ; its configured node's limits blanked.
  (declare (xargs :guard t))
  (if (and (consp r) (consp (cdr r)))
      (list* (car r) (fn-rhl-blank-cnode (cadr r)) (cddr r))
    r))

(defun fn-rhl-blank-delta (d)
  ; A `:set-limit' delta with its value 0 (within every ceiling).
  (declare (xargs :guard t))
  (if (and (fn-cfg-delta-shapep d) (equal (fn-cfg-delta-kind d) :set-limit))
      (fn-cfg-delta-make :set-limit (fn-cfg-delta-a d) (fn-cfg-delta-b d) 0
                         (fn-cfg-delta-rows d))
    d))

(defun fn-rhl-blank-deltas (ds)
  (declare (xargs :guard t))
  (if (consp ds)
      (cons (fn-rhl-blank-delta (car ds)) (fn-rhl-blank-deltas (cdr ds)))
    ds))

(defun fn-rhl-blank-record (r)
  (declare (xargs :guard t))
  (fn-cfg-record-make (fn-cfg-record-sequence r) (fn-cfg-record-txid r)
                      (fn-cfg-record-generation r)
                      (fn-rhl-blank-deltas (fn-cfg-record-change r))
                      (fn-cfg-record-stamp r)))

(defun fn-rhl-limit-admittedp (d)
  ; What admissibility asks of a delta's limit value and nothing else does:
  ; a `:set-limit' value is a uint32 within its slot's ceiling.
  (declare (xargs :guard t))
  (or (not (equal (fn-cfg-delta-kind d) :set-limit))
      (not (fn-cfg-delta-shapep d))
      (and (fn-record-uint32p (fn-cfg-delta-n d))
           (<= (fn-cfg-delta-n d) (fn-cfg-limit-ceiling (fn-cfg-delta-a d))))))

(defun fn-rhl-limits-admittedp (ds)
  (declare (xargs :guard t))
  (if (consp ds)
      (and (fn-rhl-limit-admittedp (car ds)) (fn-rhl-limits-admittedp (cdr ds)))
    t))

(defun fn-rhl-record-variantp (r1 r2)
  ; R2 is R1 with other `:set-limit' values, decoded, fitting and within the
  ; ceilings exactly when R1 is.
  (declare (xargs :guard t))
  (and (equal (fn-rhl-blank-record r1) (fn-rhl-blank-record r2))
       (iff (fn-cfg-recordp r1) (fn-cfg-recordp r2))
       (iff (fn-cfg-record-fitsp r1) (fn-cfg-record-fitsp r2))
       (iff (fn-rhl-limits-admittedp (fn-cfg-record-change r1))
            (fn-rhl-limits-admittedp (fn-cfg-record-change r2)))))

(defun fn-rhl-configs-variantp (c1 c2)
  (declare (xargs :guard t))
  (if (consp c1)
      (and (consp c2)
           (fn-rhl-record-variantp (car c1) (car c2))
           (fn-rhl-configs-variantp (cdr c1) (cdr c2)))
    (equal c1 c2)))

; -----------------------------------------------------------------------------
; The limits slot is written by :set-limit and read by nothing

(defthm fn-rhl-blank-value-of-apply-delta
  (equal (fn-rhl-blank-value (fn-cfg-apply-delta (fn-rhl-blank-value v) gen stamp (fn-rhl-blank-delta d)))
         (fn-rhl-blank-value (fn-cfg-apply-delta v gen stamp d)))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-set-groups))))
(defthm fn-rhl-blank-value-idempotent
  (equal (fn-rhl-blank-value (fn-rhl-blank-value v)) (fn-rhl-blank-value v)))
(defthm fn-rhl-blank-delta-idempotent
  (equal (fn-rhl-blank-delta (fn-rhl-blank-delta d)) (fn-rhl-blank-delta d)))
(defthm fn-rhl-blank-deltas-idempotent
  (equal (fn-rhl-blank-deltas (fn-rhl-blank-deltas ds)) (fn-rhl-blank-deltas ds)))
(defun fn-rhl-veq (v1 v2)
  (declare (xargs :guard t))
  (equal (fn-rhl-blank-value v1) (fn-rhl-blank-value v2)))
(defequiv fn-rhl-veq)
(defun fn-rhl-deq (d1 d2)
  (declare (xargs :guard t))
  (equal (fn-rhl-blank-delta d1) (fn-rhl-blank-delta d2)))
(defequiv fn-rhl-deq)
(defun fn-rhl-dseq (ds1 ds2)
  (declare (xargs :guard t))
  (equal (fn-rhl-blank-deltas ds1) (fn-rhl-blank-deltas ds2)))
(defequiv fn-rhl-dseq)
(defthm fn-rhl-veq-blank-value (fn-rhl-veq (fn-rhl-blank-value v) v))
(defthm fn-rhl-deq-blank-delta (fn-rhl-deq (fn-rhl-blank-delta d) d))
(defthm fn-rhl-dseq-blank-deltas (fn-rhl-dseq (fn-rhl-blank-deltas ds) ds))
(defcong fn-rhl-veq fn-rhl-veq (fn-cfg-apply-delta v gen stamp d) 1
  :hints (("Goal" :use ((:instance fn-rhl-blank-value-of-apply-delta (v v))
                        (:instance fn-rhl-blank-value-of-apply-delta (v v-equiv)))
           :in-theory (disable fn-rhl-blank-value-of-apply-delta fn-rhl-blank-value fn-rhl-blank-delta fn-cfg-apply-delta))))
(defcong fn-rhl-deq fn-rhl-veq (fn-cfg-apply-delta v gen stamp d) 4
  :hints (("Goal" :use ((:instance fn-rhl-blank-value-of-apply-delta (d d))
                        (:instance fn-rhl-blank-value-of-apply-delta (d d-equiv)))
           :in-theory (disable fn-rhl-blank-value-of-apply-delta fn-rhl-blank-value fn-rhl-blank-delta fn-cfg-apply-delta))))
(defthm fn-rhl-subscription-rowsp-of-blank-value
  (equal (fn-cfg-subscription-rowsp (fn-rhl-blank-value v) gen rows)
         (fn-cfg-subscription-rowsp v gen rows))
  :hints (("Goal" :in-theory (enable fn-cfg-subscription-rowsp fn-cfg-group-livep))))
(defthm fn-rhl-groups-of-blank-value (equal (fn-cfg-groups (fn-rhl-blank-value v)) (fn-cfg-groups v)))
(defthm fn-rhl-capacity-of-blank-value (equal (fn-cfg-capacity (fn-rhl-blank-value v)) (fn-cfg-capacity v)))
(defthm fn-rhl-quotas-of-blank-value (equal (fn-cfg-quotas (fn-rhl-blank-value v)) (fn-cfg-quotas v)))
(defthm fn-rhl-policies-of-blank-value (equal (fn-cfg-policies (fn-rhl-blank-value v)) (fn-cfg-policies v)))
(defthm fn-rhl-listeners-of-blank-value (equal (fn-cfg-listeners (fn-rhl-blank-value v)) (fn-cfg-listeners v)))
(defthm fn-rhl-peers-of-blank-value (equal (fn-cfg-peers (fn-rhl-blank-value v)) (fn-cfg-peers v)))
(defthm fn-rhl-authorities-of-blank-value (equal (fn-cfg-authorities (fn-rhl-blank-value v)) (fn-cfg-authorities v)))
(defthm fn-rhl-invitations-of-blank-value (equal (fn-cfg-invitations (fn-rhl-blank-value v)) (fn-cfg-invitations v)))
(defthm fn-rhl-accounts-of-blank-value (equal (fn-cfg-accounts (fn-rhl-blank-value v)) (fn-cfg-accounts v)))
(defthm fn-rhl-descriptions-of-blank-value (equal (fn-cfg-descriptions (fn-rhl-blank-value v)) (fn-cfg-descriptions v)))
(defthm fn-rhl-limits-of-blank-value (equal (fn-cfg-limits (fn-rhl-blank-value v)) nil))
(in-theory (disable fn-rhl-blank-value))
(defthm fn-rhl-delta-reason-of-blank-value
  (equal (fn-cfg-delta-reason (fn-rhl-blank-value v) gen stamp reserved ceiling d)
         (fn-cfg-delta-reason v gen stamp reserved ceiling d))
  :hints (("Goal" :in-theory (enable fn-cfg-delta-reason fn-cfg-group-livep fn-cfg-group-names
                                     fn-cfg-account-delete-reason fn-cfg-set-default-subscriptions-reason
                                     fn-cfg-set-group-description-reason fn-cfg-set-group-moderation-reason
                                     fn-cfg-withdraw-article-reason))))

(defcong fn-rhl-veq equal (fn-cfg-delta-reason v gen stamp reserved ceiling d) 1
  :hints (("Goal" :use ((:instance fn-rhl-delta-reason-of-blank-value (v v))
                        (:instance fn-rhl-delta-reason-of-blank-value (v v-equiv)))
           :in-theory (disable fn-rhl-delta-reason-of-blank-value fn-cfg-delta-reason))))
(defthm fn-rhl-delta-reason-of-blank-delta
  (iff (fn-cfg-delta-reason v gen stamp reserved ceiling d)
       (or (fn-cfg-delta-reason v gen stamp reserved ceiling (fn-rhl-blank-delta d))
           (not (fn-rhl-limit-admittedp d))))
  :hints (("Goal" :in-theory (enable fn-cfg-delta-reason fn-cfg-deltap fn-rhl-blank-delta))))
(in-theory (disable fn-rhl-delta-reason-of-blank-delta fn-rhl-blank-delta fn-rhl-veq fn-rhl-deq))
(defun fn-rhl-apply2-induct (v1 v2 gen stamp ds1 ds2)
  (declare (xargs :measure (len ds1)))
  (if (consp ds1)
      (fn-rhl-apply2-induct (fn-cfg-apply-delta v1 gen stamp (car ds1))
                            (fn-cfg-apply-delta v2 gen stamp (car ds2))
                            gen stamp (cdr ds1) (cdr ds2))
    (list v1 v2 ds2)))
(defthm fn-rhl-apply-limit-variant
  (implies (and (fn-rhl-veq v1 v2) (fn-rhl-dseq ds1 ds2))
           (fn-rhl-veq (fn-cfg-apply v1 gen stamp ds1) (fn-cfg-apply v2 gen stamp ds2)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-rhl-apply2-induct v1 v2 gen stamp ds1 ds2)
           :in-theory (e/d (fn-cfg-apply fn-rhl-dseq) (fn-cfg-apply-delta)))
          ("Subgoal *1/1" :use ((:instance fn-rhl-deq-blank-delta (d (car ds1)))
                                (:instance fn-rhl-deq-blank-delta (d (car ds2))))
           :in-theory (e/d (fn-cfg-apply fn-rhl-dseq) (fn-cfg-apply-delta fn-rhl-deq-blank-delta)))))
(defun fn-rhl-reason2-induct (v1 v2 gen stamp reserved ceiling ds)
  (declare (xargs :measure (len ds)))
  (if (consp ds)
      (fn-rhl-reason2-induct (fn-cfg-apply-delta v1 gen stamp (car ds))
                             (fn-cfg-apply-delta v2 gen stamp (car ds))
                             gen stamp reserved ceiling (cdr ds))
    (list v1 v2 reserved ceiling)))
(defcong fn-rhl-veq equal (fn-cfg-admissible-reason v gen stamp reserved ceiling ds) 1
  :hints (("Goal" :induct (fn-rhl-reason2-induct v v-equiv gen stamp reserved ceiling ds)
           :in-theory (e/d (fn-cfg-admissible-reason) (fn-cfg-apply-delta fn-cfg-delta-reason)))))
(defcong fn-rhl-veq equal (fn-cfg-admissiblep v gen stamp reserved ceiling ds) 1
  :hints (("Goal" :in-theory (e/d (fn-cfg-admissiblep) (fn-cfg-admissible-reason)))))
(defthm fn-rhl-admissiblep-is-blank-and-admitted
  (equal (fn-cfg-admissiblep v gen stamp reserved ceiling ds)
         (and (fn-cfg-admissiblep v gen stamp reserved ceiling (fn-rhl-blank-deltas ds))
              (fn-rhl-limits-admittedp ds)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-cfg-admissible-reason v gen stamp reserved ceiling ds)
           :in-theory (e/d (fn-cfg-admissiblep fn-cfg-admissible-reason)
                           (fn-cfg-apply-delta fn-cfg-delta-reason)))
          ("Subgoal *1/2" :use ((:instance fn-rhl-delta-reason-of-blank-delta (d (car ds)))))
          ("Subgoal *1/1" :use ((:instance fn-rhl-delta-reason-of-blank-delta (d (car ds)))))))

; -----------------------------------------------------------------------------
; One configuration record, one store event

(defthm fn-rhl-cfg-make-equal
  (equal (equal (fn-cfg-make g1 v1) (fn-cfg-make g2 v2))
         (and (equal g1 g2) (equal v1 v2)))
  :hints (("Goal" :in-theory (enable fn-cfg-make))))
(defthm fn-rhl-cnode-make-equal
  (equal (equal (fn-cnode-make n1 c1) (fn-cnode-make n2 c2))
         (and (equal n1 n2) (equal c1 c2)))
  :hints (("Goal" :in-theory (enable fn-cnode-make))))
(defthm fn-rhl-record-make-equal
  (equal (equal (fn-cfg-record-make s1 t1 g1 c1 st1) (fn-cfg-record-make s2 t2 g2 c2 st2))
         (and (equal s1 s2) (equal t1 t2) (equal g1 g2) (equal c1 c2) (equal st1 st2)))
  :hints (("Goal" :in-theory (enable fn-cfg-record-make))))
(defthm fn-rhl-blank-cfg-accessors
  (and (equal (fn-cfg-generation (fn-rhl-blank-cfg c)) (fn-cfg-generation c))
       (equal (fn-cfg-value (fn-rhl-blank-cfg c)) (fn-rhl-blank-value (fn-cfg-value c)))))
(defthm fn-rhl-blank-cnode-accessors
  (and (equal (fn-cnode-node (fn-rhl-blank-cnode cn)) (fn-cnode-node cn))
       (equal (fn-cnode-config (fn-rhl-blank-cnode cn)) (fn-rhl-blank-cfg (fn-cnode-config cn)))))
(defthm fn-rhl-blank-record-accessors
  (and (equal (fn-cfg-record-sequence (fn-rhl-blank-record r)) (fn-cfg-record-sequence r))
       (equal (fn-cfg-record-txid (fn-rhl-blank-record r)) (fn-cfg-record-txid r))
       (equal (fn-cfg-record-generation (fn-rhl-blank-record r)) (fn-cfg-record-generation r))
       (equal (fn-cfg-record-change (fn-rhl-blank-record r)) (fn-rhl-blank-deltas (fn-cfg-record-change r)))
       (equal (fn-cfg-record-stamp (fn-rhl-blank-record r)) (fn-cfg-record-stamp r))))
(in-theory (disable fn-rhl-blank-cfg fn-rhl-blank-cnode fn-rhl-blank-record))
(defthm fn-rhl-apply-record-limit-variant
  (implies (and (equal (fn-rhl-blank-cfg c1) (fn-rhl-blank-cfg c2))
                (equal (fn-rhl-blank-record r1) (fn-rhl-blank-record r2)))
           (equal (fn-rhl-blank-cfg (fn-cfg-apply-record c1 r1))
                  (fn-rhl-blank-cfg (fn-cfg-apply-record c2 r2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cfg-apply-record fn-rhl-blank-cfg fn-rhl-blank-record fn-rhl-veq fn-rhl-dseq)
                                  (fn-cfg-apply))
           :use ((:instance fn-rhl-apply-limit-variant
                            (v1 (fn-cfg-value c1)) (v2 (fn-cfg-value c2))
                            (gen (fn-cfg-record-generation r1)) (stamp (fn-cfg-record-stamp r1))
                            (ds1 (fn-cfg-record-change r1)) (ds2 (fn-cfg-record-change r2)))))))
(defthm fn-rhl-blank-cfg-equal-parts
  (implies (equal (fn-rhl-blank-cfg c1) (fn-rhl-blank-cfg c2))
           (and (equal (fn-cfg-generation c1) (fn-cfg-generation c2))
                (fn-rhl-veq (fn-cfg-value c1) (fn-cfg-value c2))
                (equal (fn-cfg-groups (fn-cfg-value c1)) (fn-cfg-groups (fn-cfg-value c2)))
                (equal (fn-cfg-capacity (fn-cfg-value c1)) (fn-cfg-capacity (fn-cfg-value c2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rhl-blank-cfg fn-rhl-veq)
                                  (fn-rhl-groups-of-blank-value fn-rhl-capacity-of-blank-value))
           :use ((:instance fn-rhl-groups-of-blank-value (v (fn-cfg-value c1)))
                 (:instance fn-rhl-groups-of-blank-value (v (fn-cfg-value c2)))
                 (:instance fn-rhl-capacity-of-blank-value (v (fn-cfg-value c1)))
                 (:instance fn-rhl-capacity-of-blank-value (v (fn-cfg-value c2)))))))
(defthm fn-rhl-statep-of-make-limit-variant
  (implies (and (equal (fn-rhl-blank-cfg c1) (fn-rhl-blank-cfg c2))
                (fn-cfgp c1) (fn-cfgp c2))
           (equal (fn-cnode-statep (fn-cnode-make n c1))
                  (fn-cnode-statep (fn-cnode-make n c2))))
  :rule-classes nil
  :hints (("Goal" :use fn-rhl-blank-cfg-equal-parts
           :in-theory (e/d (fn-cnode-statep fn-cnode-domain fn-cnode-domain-of)
                           (fn-cfgp fn-node-statep)))))
(defthm fn-rhl-record-acceptablep-limit-variant
  (implies (and (equal (fn-rhl-blank-cnode cn1) (fn-rhl-blank-cnode cn2))
                (fn-cfgp (fn-cnode-config cn1)) (fn-cfgp (fn-cnode-config cn2))
                (fn-rhl-record-variantp r1 r2))
           (equal (fn-cnode-record-acceptablep cn1 r1 ceiling)
                  (fn-cnode-record-acceptablep cn2 r2 ceiling)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rhl-blank-cfg-equal-parts
                                   (c1 (fn-cnode-config cn1)) (c2 (fn-cnode-config cn2)))
                        (:instance fn-rhl-blank-cnode-accessors (cn cn1))
                        (:instance fn-rhl-blank-cnode-accessors (cn cn2))
                        (:instance fn-rhl-blank-record-accessors (r r1))
                        (:instance fn-rhl-blank-record-accessors (r r2))
                        (:instance fn-rhl-admissiblep-is-blank-and-admitted
                                   (v (fn-cfg-value (fn-cnode-config cn1)))
                                   (gen (fn-cfg-record-generation r1)) (stamp (fn-cfg-record-stamp r1))
                                   (reserved (fn-retain-reserved (fn-node-retention (fn-cnode-node cn1))))
                                   (ds (fn-cfg-record-change r1)))
                        (:instance fn-rhl-admissiblep-is-blank-and-admitted
                                   (v (fn-cfg-value (fn-cnode-config cn2)))
                                   (gen (fn-cfg-record-generation r2)) (stamp (fn-cfg-record-stamp r2))
                                   (reserved (fn-retain-reserved (fn-node-retention (fn-cnode-node cn2))))
                                   (ds (fn-cfg-record-change r2))))
           :in-theory (e/d (fn-cnode-record-acceptablep fn-cfg-record-acceptablep fn-rhl-record-variantp)
                           (fn-cfgp fn-cfg-recordp fn-cfg-record-fitsp fn-cfg-admissiblep
                            fn-rhl-blank-cnode-accessors fn-rhl-blank-record-accessors
                            fn-rhl-limits-admittedp)))))
(defthm fn-rhl-apply-config-limit-variant
  (implies (and (equal (fn-rhl-blank-cnode cn1) (fn-rhl-blank-cnode cn2))
                (fn-cnode-statep cn1) (fn-cnode-statep cn2)
                (fn-rhl-record-variantp r1 r2))
           (equal (fn-rhl-blank-cnode (fn-cnode-apply-config cn1 r1 ceiling))
                  (fn-rhl-blank-cnode (fn-cnode-apply-config cn2 r2 ceiling))))
  :rule-classes nil
  :hints (("Goal" :use (fn-rhl-record-acceptablep-limit-variant
                        (:instance fn-rhl-blank-cnode-accessors (cn cn1))
                        (:instance fn-rhl-blank-cnode-accessors (cn cn2))
                        (:instance fn-rhl-apply-record-limit-variant
                                   (c1 (fn-cnode-config cn1)) (c2 (fn-cnode-config cn2)))
                        (:instance fn-rhl-blank-cfg-equal-parts
                                   (c1 (fn-cfg-apply-record (fn-cnode-config cn1) r1))
                                   (c2 (fn-cfg-apply-record (fn-cnode-config cn2) r2))))
           :in-theory (e/d (fn-cnode-apply-config fn-cnode-domain-of fn-rhl-record-variantp)
                           (fn-cnode-statep fn-cnode-record-acceptablep fn-cfg-apply-record
                            fn-rhl-blank-cnode-accessors fn-cnode-extend-nexts)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-cnode-apply-config fn-cnode-domain-of fn-rhl-record-variantp
                                  fn-rhl-blank-cnode)
                                 (fn-cnode-statep fn-cnode-record-acceptablep fn-cfg-apply-record
                                  fn-cnode-extend-nexts))))))
(defthm fn-rhl-apply-event-limit-variant
  (implies (and (equal (fn-rhl-blank-cnode cn1) (fn-rhl-blank-cnode cn2))
                (fn-cnode-statep cn1) (fn-cnode-statep cn2))
           (and (equal (fn-cnode-statep (fn-cpr-apply-event cn1 event))
                       (fn-cnode-statep (fn-cpr-apply-event cn2 event)))
                (equal (consp (fn-cpr-apply-event cn1 event))
                       (consp (fn-cpr-apply-event cn2 event)))
                (equal (fn-rhl-blank-cnode (fn-cpr-apply-event cn1 event))
                       (fn-rhl-blank-cnode (fn-cpr-apply-event cn2 event)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rhl-blank-cnode-accessors (cn cn1))
                        (:instance fn-rhl-blank-cnode-accessors (cn cn2))
                        (:instance fn-rhl-blank-cfg-equal-parts
                                   (c1 (fn-cnode-config cn1)) (c2 (fn-cnode-config cn2)))
                        (:instance fn-rhl-statep-of-make-limit-variant
                                   (c1 (fn-cnode-config cn1)) (c2 (fn-cnode-config cn2))
                                   (n (fn-replay-apply-record (fn-cnode-node cn1) event))))
           :in-theory (e/d (fn-cpr-apply-event fn-cpr-event-servedp fn-cnode-selection-servedp
                            fn-cnode-served-of fn-cfg-group-names fn-rhl-blank-cnode)
                           (fn-cnode-statep fn-replay-apply-record fn-rhl-blank-cnode-accessors
                            fn-node-statep fn-store-event-p)))))

; -----------------------------------------------------------------------------
; The fold

(defthm fn-rhl-blank-cnode-of-make
  (equal (fn-rhl-blank-cnode (fn-cnode-make n c))
         (fn-cnode-make n (fn-rhl-blank-cfg c)))
  :hints (("Goal" :in-theory (enable fn-rhl-blank-cnode))))
(defthm fn-rhl-blank-result-of-ok
  (equal (fn-rhl-blank-result (fn-replay-ok cn position))
         (fn-replay-ok (fn-rhl-blank-cnode cn) position))
  :hints (("Goal" :in-theory (enable fn-replay-ok))))
(defthm fn-rhl-blank-result-of-fault
  (equal (fn-rhl-blank-result (fn-replay-fault cn position reason))
         (fn-replay-fault (fn-rhl-blank-cnode cn) position reason))
  :hints (("Goal" :in-theory (enable fn-replay-fault))))
(in-theory (disable fn-rhl-blank-result))
(defthm fn-rhl-configs-variantp-parts
  (implies (fn-rhl-configs-variantp c1 c2)
           (and (iff (consp c1) (consp c2))
                (equal (fn-cfg-record-txid (car c1)) (fn-cfg-record-txid (car c2)))
                (equal (fn-cfg-record-sequence (car c1)) (fn-cfg-record-sequence (car c2)))
                (iff (fn-cfg-recordp (car c1)) (fn-cfg-recordp (car c2)))
                (fn-rhl-configs-variantp (cdr c1) (cdr c2))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rhl-blank-record-accessors (r (car c1)))
                        (:instance fn-rhl-blank-record-accessors (r (car c2))))
           :in-theory (disable fn-rhl-blank-record-accessors fn-cfg-recordp))))
(defthm fn-rhl-config-firstp-limit-variant
  (implies (fn-rhl-configs-variantp c1 c2)
           (equal (fn-cpr-config-firstp c2 events) (fn-cpr-config-firstp c1 events)))
  :hints (("Goal" :use fn-rhl-configs-variantp-parts
           :in-theory (e/d (fn-cpr-config-firstp) (fn-rhl-configs-variantp)))))
(defun fn-rhl-loop2-induct (cn1 cn2 c1 c2 events cs es)
  (declare (xargs :measure (+ (len c1) (len events))
                  :hints (("Goal" :in-theory (enable fn-cpr-config-firstp)))))
  (if (fn-cpr-config-firstp c1 events)
      (fn-rhl-loop2-induct
       (fn-cnode-apply-config
        (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn1) (fn-cfg-record-txid (car c1)))
                       (fn-cnode-config cn1))
        (car c1) (fn-cnode-line-ceiling))
       (fn-cnode-apply-config
        (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn2) (fn-cfg-record-txid (car c2)))
                       (fn-cnode-config cn2))
        (car c2) (fn-cnode-line-ceiling))
       (cdr c1) (cdr c2) events (+ 1 (nfix cs)) es)
    (if (consp events)
        (fn-rhl-loop2-induct (fn-cpr-apply-event cn1 (car events))
                             (fn-cpr-apply-event cn2 (car events))
                             c1 c2 (cdr events) cs (+ 1 (nfix es)))
      (list cn1 cn2 c2 cs es))))
(defthm fn-rhl-configs-variantp-atom
  (implies (and (fn-rhl-configs-variantp c1 c2) (not (consp c1)))
           (equal c2 c1))
  :rule-classes nil)
(defthm fn-rhl-cpr-loop-limit-variant
  (implies (and (equal (fn-rhl-blank-cnode cn1) (fn-rhl-blank-cnode cn2))
                (fn-cnode-statep cn1) (fn-cnode-statep cn2)
                (fn-rhl-configs-variantp c1 c2))
           (equal (fn-rhl-blank-result (fn-cpr-loop cn1 c1 events cs es))
                  (fn-rhl-blank-result (fn-cpr-loop cn2 c2 events cs es))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-rhl-loop2-induct cn1 cn2 c1 c2 events cs es)
           :expand ((:free (cn c) (fn-cpr-loop cn c events cs es)))
           :in-theory (e/d (fn-rhl-blank-cnode-accessors)
                           (fn-cnode-statep fn-cnode-apply-config fn-cpr-apply-event
                               fn-cnode-record-acceptablep fn-rhl-configs-variantp
                               fn-cfg-recordp fn-replay-advance-okp fn-replay-advance-txid
                               fn-store-event-p fn-cpr-loop)))
          ("Subgoal *1/3" :expand ((:free (cn c) (fn-cpr-loop cn c events cs es)))
           :use ((:instance fn-rhl-configs-variantp-parts)
                                (:instance fn-rhl-configs-variantp-atom)
                                (:instance fn-rhl-config-firstp-limit-variant))
           :in-theory (e/d (fn-rhl-blank-cnode-accessors)
                           (fn-cnode-statep fn-cnode-apply-config fn-cpr-apply-event
                               fn-cnode-record-acceptablep fn-rhl-configs-variantp
                               fn-cfg-recordp fn-replay-advance-okp fn-replay-advance-txid
                               fn-store-event-p fn-cpr-loop fn-rhl-config-firstp-limit-variant)))
          ("Subgoal *1/2" :expand ((:free (cn c) (fn-cpr-loop cn c events cs es)))
           :use ((:instance fn-rhl-apply-event-limit-variant (event (car events)))
                                (:instance fn-rhl-configs-variantp-parts)
                                (:instance fn-rhl-blank-cnode-accessors (cn cn1))
                                (:instance fn-rhl-blank-cnode-accessors (cn cn2)))
           :in-theory (e/d () (fn-cnode-statep fn-cnode-apply-config fn-cpr-apply-event
                               fn-cnode-record-acceptablep fn-rhl-configs-variantp
                               fn-cfg-recordp fn-replay-advance-okp fn-replay-advance-txid
                               fn-store-event-p fn-cpr-loop fn-rhl-blank-cnode-accessors)))
          ("Subgoal *1/1"
           :use ((:instance fn-rhl-configs-variantp-parts)
                 (:instance fn-rhl-config-firstp-limit-variant)
                 (:instance fn-rhl-blank-cnode-accessors (cn cn1))
                 (:instance fn-rhl-blank-cnode-accessors (cn cn2))
                 (:instance fn-rhl-statep-of-make-limit-variant
                            (c1 (fn-cnode-config cn1)) (c2 (fn-cnode-config cn2))
                            (n (fn-replay-advance-txid (fn-cnode-node cn1) (fn-cfg-record-txid (car c1)))))
                 (:instance fn-rhl-record-acceptablep-limit-variant
                            (cn1 (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn1) (fn-cfg-record-txid (car c1)))
                                                (fn-cnode-config cn1)))
                            (cn2 (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn2) (fn-cfg-record-txid (car c2)))
                                                (fn-cnode-config cn2)))
                            (r1 (car c1)) (r2 (car c2)) (ceiling (fn-cnode-line-ceiling)))
                 (:instance fn-rhl-apply-config-limit-variant
                            (cn1 (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn1) (fn-cfg-record-txid (car c1)))
                                                (fn-cnode-config cn1)))
                            (cn2 (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn2) (fn-cfg-record-txid (car c2)))
                                                (fn-cnode-config cn2)))
                            (r1 (car c1)) (r2 (car c2)) (ceiling (fn-cnode-line-ceiling)))
                 (:instance fn-cnode-apply-config-preserves-state
                            (cn (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn1) (fn-cfg-record-txid (car c1)))
                                               (fn-cnode-config cn1)))
                            (record (car c1)) (ceiling (fn-cnode-line-ceiling)))
                 (:instance fn-cnode-apply-config-preserves-state
                            (cn (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn2) (fn-cfg-record-txid (car c2)))
                                               (fn-cnode-config cn2)))
                            (record (car c2)) (ceiling (fn-cnode-line-ceiling))))
           :expand ((fn-rhl-configs-variantp c1 c2) (:free (cn c) (fn-cpr-loop cn c events cs es)))
           :in-theory (e/d () (fn-cnode-statep fn-cnode-apply-config fn-cpr-apply-event
                               fn-cnode-record-acceptablep fn-rhl-record-variantp
                               fn-cfg-recordp fn-replay-advance-okp fn-replay-advance-txid
                               fn-store-event-p fn-cpr-loop fn-rhl-blank-cnode-accessors
                               fn-cnode-apply-config-preserves-state
                               fn-rhl-config-firstp-limit-variant)))))

; -----------------------------------------------------------------------------
; The host's open

(defthm fn-rhl-cpr-replay-limit-variant
  (implies (fn-rhl-configs-variantp configs1 configs2)
           (equal (fn-rhl-blank-result (fn-cpr-replay configs1 events))
                  (fn-rhl-blank-result (fn-cpr-replay configs2 events))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rhl-cpr-loop-limit-variant
                                   (cn1 (fn-cnode-initial (fn-cfg-initial)))
                                   (cn2 (fn-cnode-initial (fn-cfg-initial)))
                                   (c1 configs1) (c2 configs2) (cs 0) (es 0))
                        (:instance fn-cnode-initial-is-state (config (fn-cfg-initial))))
           :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop fn-cnode-initial fn-cnode-statep
                                            fn-cnode-initial-is-state)))))

; KEYSTONE (PRF-1026).  The host's open, host/store-node-host.lisp
; fn-store-sn-recover-rows -> fn-rii-sco-extend-open, over the capture of an
; admitted history's prefix P extended by its suffix Q: the configuration
; fold its store open returns first (fn-rii-sco-store-open's REPLAYED) is,
; up to the limit values carried in the configuration, the same for two
; configuration histories that differ only in their :set-limit values.  No
; limit value in force at any position -- the one when a record was
; accepted, a later lowering, or the current profile's -- decides a
; record's replay.
(defthm fn-rhl-extend-open-is-limit-free
  (implies (and (fn-sn-observed-historyp frontier (append prefix suffix))
                (fn-rhl-configs-variantp configs1 configs2))
           (equal (fn-rhl-blank-result
                   (fn-sco-cpr-finish
                    (fn-sco-cpr (car (fn-rii-sco-extend-open (fn-sco-capture configs1 prefix)
                                                             configs1 suffix frontier)))
                    configs1))
                  (fn-rhl-blank-result
                   (fn-sco-cpr-finish
                    (fn-sco-cpr (car (fn-rii-sco-extend-open (fn-sco-capture configs2 prefix)
                                                             configs2 suffix frontier)))
                    configs2))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-sco-extend-of-capture-when-history (configs configs1))
                        (:instance fn-sco-extend-of-capture-when-history (configs configs2))
                        (:instance fn-rhl-cpr-replay-limit-variant
                                   (events (append prefix suffix))))
           :in-theory (union-theories
                       '(fn-rii-sco-extend-open-is-extend-then-open
                         fn-rii-sco-extend-is-sco-extend car-cons)
                       (theory 'minimal-theory)))))
