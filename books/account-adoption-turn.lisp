; INTERNAL typed account-turn counter/custody transitions. Public owner
; wrappers derive all arguments from actual installed BODY/source + CURRENT.
; Passing these pure model arguments is never an allocating capability.
(in-package "ACL2")
(include-book "account-adoption-input-source")
(include-book "index-query-resources")

(defun fn-act-token (nonce epoch generation)
 (declare (xargs :guard t))
 (list :account-preparation-turn nonce epoch generation))

; Fixed10 retains old request/job before any producer can escape. OUTPUT is
; the actual saved request/job/action packet, not an external authority reply.
(defun fn-act-row (token phase demand operation source request job output intent)
 (declare (xargs :guard t))
 (list :account-turn token phase demand operation source request job output intent))

(defun fn-act-livep (token current)
 (declare (xargs :guard t))
 (and (fn-cado-widthp 10 current)
      (eq (fn-cp-nth 0 current) :account-turn)
      (fn-cado-receipt-coordinatep token)
      (fn-cado-receipt-coordinatep (fn-cp-nth 1 current))
      (equal token (fn-cp-nth 1 current))
      (member-eq (fn-cp-nth 2 current)
                 '(:reserved :produced :promoting :promoted :suspended :uncertain))))

(defun fn-act-reserve (epoch generation operation source request job
                            demand rescue current ledger)
 (declare (xargs :guard t))
 (cond
  (current (mv :account-turn-busy current ledger))
  ((not (and (natp epoch) (natp generation)
              (member-eq operation '(:begin :candidate-step :operation-select))
              (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)))
   (mv :invalid-account-turn-census current ledger))
  (t
   (mv-let (word next charged)
    (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) rescue
                  (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
                  (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
    (if (not (eq word :admitted)) (mv word current ledger)
      (mv :account-turn-reserved
          (fn-act-row (fn-act-token (fn-prl-nth 2 ledger) epoch generation)
                      :reserved demand operation source request job nil nil)
          (fn-prl-build (fn-prl-nth 0 ledger) charged next
                        (fn-prl-nth 3 ledger) (fn-prl-baseline ledger))))))))

(defun fn-act-produced (token output current)
 (declare (xargs :guard t))
 (if (not (and (fn-act-livep token current)
                (eq (fn-cp-nth 2 current) :reserved)))
     (mv :stale current)
   (mv :account-turn-produced
       (fn-act-row token :produced (fn-cp-nth 3 current)
                   (fn-cp-nth 4 current) (fn-cp-nth 5 current)
                   (fn-cp-nth 6 current) (fn-cp-nth 7 current) output nil))))

(defun fn-act-uncertain (token current)
 (declare (xargs :guard t))
 (if (not (fn-act-livep token current)) (mv :stale current)
   (mv :account-turn-uncertain
       (fn-act-row token :uncertain (fn-cp-nth 3 current)
                   (fn-cp-nth 4 current) (fn-cp-nth 5 current)
                   (fn-cp-nth 6 current) (fn-cp-nth 7 current)
                   (fn-cp-nth 8 current) (fn-cp-nth 9 current)))))

; This prepares the exact fenced intent BEFORE any pool store. RETAINED is
; an actual qualified old/new graph projection selected inside the owner;
; it is not a request count, allocation epoch charge or native supplied price.
(defun fn-act-promotion-intent (token retained current ledger)
 (declare (xargs :guard t))
 (let ((demand (fn-cp-nth 3 current)) (charged (fn-prl-nth 1 ledger)))
  (if (not (and (fn-act-livep token current)
                 (eq (fn-cp-nth 2 current) :produced)
                 (fn-prs-vectorp demand) (fn-prs-vectorp charged)
                 (fn-prs-vectorp retained)
                 (true-listp charged) (true-listp retained)
                 (equal (fn-prl-nth 4 retained) 0)
                 (fn-prs-below retained demand)
                 (fn-prs-below retained charged)))
      (mv :invalid-account-turn-promotion current)
    (mv :account-turn-promoting
        (fn-act-row token :promoting demand (fn-cp-nth 4 current)
                    (fn-cp-nth 5 current) (fn-cp-nth 6 current)
                    (fn-cp-nth 7 current) (fn-cp-nth 8 current)
                    (list :account-turn-promotion ledger
                          (fn-iqr-promoted-ledger ledger retained) retained))))))

; Internal finalize follows ONLY actual successful counter-only pool publish.
; It retains original graphs. Neither this phase nor an ordinary return is
; a last-alias receipt, and no reusable refund/clear helper exists here.
(defun fn-act-promotion-published (token current)
 (declare (xargs :guard t))
 (let* ((intent (fn-cp-nth 9 current)) (retained (fn-cp-nth 3 intent))
        (demand (fn-cp-nth 3 current)))
  (if (not (and (fn-act-livep token current)
                 (eq (fn-cp-nth 2 current) :promoting)
                 (eq (fn-cp-nth 0 intent) :account-turn-promotion)
                 (fn-prs-vectorp retained) (fn-prs-vectorp demand)
                 (true-listp retained) (true-listp demand)
                 (equal (fn-prl-nth 4 retained) 0)
                 (fn-prs-below retained demand)))
      (mv :stale current)
    (mv :account-turn-promoted
        (fn-act-row token :promoted (fn-prs-release-reusable demand retained)
                    (fn-cp-nth 4 current) (fn-cp-nth 5 current)
                    (fn-cp-nth 6 current) (fn-cp-nth 7 current)
                    (fn-cp-nth 8 current) intent)))))

(in-theory (disable fn-act-token fn-act-row fn-act-livep fn-act-reserve
                    fn-act-produced fn-act-uncertain fn-act-promotion-intent
                    fn-act-promotion-published))
