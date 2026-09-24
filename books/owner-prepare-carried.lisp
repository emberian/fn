;; fn: the owner's prepare the host calls, without the history's txid fold.
;
; host/owner-host.lisp fn-owner-prepare installs fn-sbud-prepare
; (books/owner-store-budget.lisp), which is fn-opc-prepare -> fn-opc-owner-
; prepare -> fn-spc-prepare -> fn-spc-stage-record -> fn-sf-candidatep
; (books/store-files.lisp).  The candidate test compares the record's txid
; with (fn-sf-next-lower records 0): a fold over the whole durable history
; that computes fn-store-event-txid of every record, and that accessor
; dispatches on the event kind through fn-record-p, which walks the record's
; octets.  O(N * L) per POST, 23 to 26 percent of POST CPU at N = 120 after
; the commit lane (planning/evidence/commit-path-cost-2026-09-24.md).
;
; The fold's value is fixed by its last step: each step discards the
; accumulator, so on a non-empty history it is 1 + the txid of the LAST
; record, and on the empty history it is the initial 0.  No invariant is
; needed for that (fn-pcar-next-lower-is-next-lower has no hypothesis);
; fn-sf-record-listp is what makes the value meaningful (the txids are
; increasing), not what makes it equal.  fn-pcar-next-lower steps to the last
; cons without looking at the records and computes one txid: O(N + L).
;
; Every definition below is its reference with fn-sf-candidatep replaced by
; fn-pcar-candidatep, keeps the reference's guard, is guard-verified, and is
; proved EQUAL to the reference with no hypothesis.  host/owner-host.lisp
; fn-owner-prepare calls fn-pcar-sbud-prepare.

(in-package "ACL2")
(include-book "owner-store-budget")

(defun fn-pcar-next-lower (records)
  (declare (xargs :guard (fn-sf-record-valuesp records) :verify-guards nil))
  (if (consp records)
      (if (consp (cdr records))
          (fn-pcar-next-lower (cdr records))
        (1+ (fn-store-event-txid (car records))))
    0))

(local
 (defthm fn-pcar-next-lower-of-cons-step
   (implies (consp records)
            (equal (fn-sf-next-lower records lower)
                   (fn-pcar-next-lower records)))
   :hints (("Goal" :induct (fn-sf-next-lower records lower)
            :in-theory (disable fn-store-event-txid)))))

; KEYSTONE (the fold).  The history's txid fold from 0 is 1 + the txid of
; its last record, or 0 on the empty history.  For every value: no
; hypothesis.
(defthm fn-pcar-next-lower-is-next-lower
  (equal (fn-pcar-next-lower records)
         (fn-sf-next-lower records 0))
  :hints (("Goal" :cases ((consp records))
           :in-theory (disable fn-store-event-txid))))

(local
 (defthm fn-pcar-next-lower-natp
   (implies (fn-sf-record-valuesp records)
            (natp (fn-pcar-next-lower records)))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (fn-pcar-next-lower records)
            :in-theory (e/d (fn-pcar-next-lower)
                            (fn-pcar-next-lower-is-next-lower))))))

(in-theory (disable fn-pcar-next-lower))

(defun fn-pcar-candidatep (record records frontier)
  (declare (xargs :guard (and (fn-sf-record-valuesp records)
                              (natp frontier))
                  :verify-guards nil))
  (and (fn-store-event-p record)
       (equal (fn-store-event-sequence record) (len records))
       (equal (1+ (fn-store-event-txid record)) frontier)
       (<= (fn-pcar-next-lower records) (fn-store-event-txid record))
       (equal (fn-store-event-generation record) (fn-store-event-txid record))))

(defthm fn-pcar-candidatep-is-candidatep
  (equal (fn-pcar-candidatep record records frontier)
         (fn-sf-candidatep record records frontier))
  :hints (("Goal" :in-theory (e/d (fn-pcar-candidatep fn-sf-candidatep)
                                  (fn-sf-next-lower fn-store-event-p
                                   fn-store-event-sequence fn-store-event-txid
                                   fn-store-event-generation)))))

(verify-guards fn-pcar-next-lower)

(verify-guards fn-pcar-candidatep
  :hints (("Goal" :in-theory (disable fn-pcar-next-lower-is-next-lower
                                      fn-store-event-p fn-store-event-sequence
                                      fn-store-event-txid
                                      fn-store-event-generation))))

(in-theory (disable fn-pcar-candidatep))

; fn-spc-stage-record (books/store-prepare-correspondence.lisp), carried.
(defun fn-pcar-stage-record (files record)
  (declare (xargs :guard (fn-sf-statep files) :verify-guards nil))
  (if (and (equal (fn-sf-phase files) :reserved)
           (fn-pcar-candidatep record (fn-sf-records files)
                               (fn-sf-frontier files)))
      (fn-sf-make :record-staged (fn-sf-frontier files) nil
                  (fn-sf-records files) record nil
                  (fn-sf-successes files) (fn-sf-barriers files))
    files))

(defthm fn-pcar-stage-record-is-stage-record
  (equal (fn-pcar-stage-record files record)
         (fn-spc-stage-record files record))
  :hints (("Goal" :in-theory (e/d (fn-pcar-stage-record fn-spc-stage-record)
                                  (fn-sf-statep fn-sf-candidatep)))))

(local
 (defthm fn-pcar-record-list-implies-values
   (implies (fn-sf-record-listp records sequence lower frontier)
            (fn-sf-record-valuesp records))
   :hints (("Goal" :induct (fn-sf-record-listp
                             records sequence lower frontier)))))

(local
 (defthm fn-pcar-state-has-candidate-guard-domain
   (implies (fn-sf-statep files)
            (and (fn-sf-record-valuesp (fn-sf-records files))
                 (natp (fn-sf-frontier files))))
   :hints (("Goal" :in-theory (enable fn-sf-statep)
            :use ((:instance fn-pcar-record-list-implies-values
                             (records (fn-sf-records files))
                             (sequence 0) (lower 0)
                             (frontier (fn-sf-frontier files))))))))

(verify-guards fn-pcar-stage-record
  :hints (("Goal" :use fn-pcar-state-has-candidate-guard-domain
           :in-theory (disable fn-sf-statep fn-pcar-candidatep-is-candidatep))))

(in-theory (disable fn-pcar-stage-record))

; fn-spc-prepare, carried.  The body is the reference's.
(defun fn-pcar-spc-prepare (s record)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (null (fn-node-stage (fn-sn-node s)))
           (fn-record-p record)
           (not (equal (fn-record-stamp record) :legacy))
           (eq (car (fn-cpe-projection-step
                     (fn-sn-consumer s) record (fn-sn-identity-next s))) :ok))
      (let* ((node (fn-sn-prepare-node (fn-sn-node s) record))
             (files (fn-pcar-stage-record (fn-sn-files s) record)))
        (if (and (fn-sn-record-bindsp node record)
                 (equal (fn-sf-phase files) :record-staged))
            (fn-sn-update s files node)
          s))
    s))

(defthm fn-pcar-spc-prepare-is-spc-prepare
  (equal (fn-pcar-spc-prepare s record) (fn-spc-prepare s record))
  :hints (("Goal" :in-theory (e/d (fn-pcar-spc-prepare fn-spc-prepare)
                                  (fn-sn-statep fn-spc-stage-record
                                   fn-sn-prepare-node fn-sn-record-bindsp
                                   fn-record-p fn-cpe-projection-step)))))

(verify-guards fn-pcar-spc-prepare
  :hints (("Goal" :in-theory
           (e/d (fn-sn-statep)
                (fn-sf-statep fn-node-statep fn-node-pending-matchesp
                 fn-sn-pending-record fn-sn-prepare-node)))))

(in-theory (disable fn-pcar-spc-prepare))

; fn-opc-owner-prepare and fn-opc-prepare
; (books/owner-prepare-correspondence.lisp), carried.
(defun fn-pcar-opc-owner-prepare (o record)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))))
  (fn-own-refresh
   (fn-own-make (fn-pcar-spc-prepare (fn-own-store o) record)
                (fn-own-view o) (fn-own-conns o)
                (fn-own-next-id o) (fn-own-max-conns o)
                (fn-own-pending o) (fn-own-ledger o)
                (fn-own-clock o) (fn-own-facts o)
                (fn-own-config o) (fn-own-queue o)
                (fn-own-inflight o) (fn-own-feeds o))))

(defthm fn-pcar-opc-owner-prepare-is-opc-owner-prepare
  (equal (fn-pcar-opc-owner-prepare o record)
         (fn-opc-owner-prepare o record))
  :hints (("Goal" :in-theory (e/d (fn-pcar-opc-owner-prepare
                                   fn-opc-owner-prepare)
                                  (fn-own-refresh fn-spc-prepare)))))

(in-theory (disable fn-pcar-opc-owner-prepare))

(defun fn-pcar-opc-prepare (oc record)
  (declare (xargs :guard (fn-sn-statep
                          (fn-own-store (fn-ocfg-owner oc)))))
  (fn-ocfg-with-owner
   oc (fn-pcar-opc-owner-prepare (fn-ocfg-owner oc) record)))

(defthm fn-pcar-opc-prepare-is-opc-prepare
  (equal (fn-pcar-opc-prepare oc record) (fn-opc-prepare oc record))
  :hints (("Goal" :in-theory (e/d (fn-pcar-opc-prepare fn-opc-prepare)
                                  (fn-opc-owner-prepare)))))

(in-theory (disable fn-pcar-opc-prepare))

; The function host/owner-host.lisp fn-owner-prepare installs.
(defun fn-pcar-sbud-prepare (oc record budget)
  (declare (xargs :guard (fn-sn-statep (fn-sbud-oc-store oc))))
  (if (fn-sbud-admitp budget (fn-sbud-used (fn-sbud-oc-store oc)))
      (fn-pcar-opc-prepare oc record)
    oc))

; KEYSTONE for the host line: the carried prepare is the called prepare, for
; every configured owner, record and budget.  No hypothesis.  Every theorem
; about fn-sbud-prepare (fn-sbud-prepare-refuses-at-budget,
; fn-sbud-prepare-below-budget-is-the-owner-prepare, and through it
; fn-opc-prepare-equals-owner-event-under-relation) is a theorem about the
; host's call.
(defthm fn-pcar-sbud-prepare-is-sbud-prepare
  (equal (fn-pcar-sbud-prepare oc record budget)
         (fn-sbud-prepare oc record budget))
  :hints (("Goal" :in-theory (e/d (fn-pcar-sbud-prepare fn-sbud-prepare)
                                  (fn-opc-prepare fn-sbud-admitp
                                   fn-sbud-used)))))

; The guard is carried, not evaluated: the owner relation keeps it across the
; prepare (fn-opc-prepare-preserves-owner-relation over the reference; the
; budget's identity arm leaves the owner as it was).
(defthm fn-pcar-sbud-prepare-preserves-owner-relation
  (implies (fn-own-relation (fn-ocfg-owner oc))
           (fn-own-relation (fn-ocfg-owner
                             (fn-pcar-sbud-prepare oc record budget))))
  :hints (("Goal" :in-theory (e/d (fn-sbud-prepare)
                                  (fn-opc-prepare fn-own-relation
                                   fn-sbud-admitp fn-sbud-used)))))

(in-theory (disable fn-pcar-sbud-prepare))
