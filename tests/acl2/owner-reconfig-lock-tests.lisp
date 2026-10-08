; Ground witnesses and hypothesis-removal teeth for the staged lock.
(in-package "ACL2")
(include-book "../../books/owner-reconfig-lock")

; These events read no payload bytes. Seal each call in a fresh local arena.
(defun orlt-own-step (o event)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (mv (fn-own-step o event fn-arena) fn-arena)
      result)))
(defun orlt-ocfg-step (oc event)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (mv (fn-ocfg-step oc event fn-arena) fn-arena)
      result)))
(defconst *orlt-empty* (fn-own-start (fn-sn-initial nil 0) 2))
(defconst *orlt-open* (cdr (fn-own-open *orlt-empty* nil)))
(defconst *orlt-staged*
  (fn-ocfg-make *orlt-open* (fn-cfg-initial) nil *fn-cfg-default-record*))
(defconst *orlt-queued*
  (fn-own-make (fn-own-store *orlt-empty*) (fn-own-view *orlt-empty*)
               nil 0 2 nil nil nil nil nil
               (list (fn-psub-pack-sub (fn-own-sub-make 0 0 0 nil nil)))
               nil nil nil nil))

; The round-1 staged fixture has no connection. The close-NIL tooth below
; deliberately supplies an invalid connection id, not a host-generated id.
(defconst *orlt-staged-empty*
  (fn-ocfg-make *orlt-empty* (fn-cfg-initial) nil *fn-cfg-default-record*))

; L1 positive: closing an existing connection does not open a transaction.
(assert-event
 (let ((o *orlt-open*) (event '(:close 0)))
   (and (fn-own-find-conn 0 (fn-own-conns o))
        (not (fn-own-pending o))
        (not (member-equal (car event) '(:begin :take)))
        (not (fn-own-pending (orlt-own-step o event))))))

; L1 exclusion, :begin: a connected owner can acquire a pending transaction.
(assert-event
 (let ((o *orlt-open*) (event '(:begin 0)))
   (and (fn-own-find-conn 0 (fn-own-conns o))
        (not (fn-own-pending o))
        (equal (car event) :begin)
        (not (equal (car event) :take))
        (member-equal (car event) '(:begin :take))
        (fn-own-pending (orlt-own-step o event)))))

; L1 exclusion, :take: round-1 counterexample. This is a synthetic queued
; owner, not a claim that its submission satisfies the full owner invariant.
(assert-event
 (let ((o *orlt-queued*) (event '(:take)))
   (and (not (fn-own-pending o))
        (not (equal (car event) :begin))
        (equal (car event) :take)
        (member-equal (car event) '(:begin :take))
        (fn-own-pending (orlt-own-step o event)))))

; L2 positive: the configured owner refuses precisely the :begin that the
; underlying connected owner would accept. Every L2 hypothesis is checked.
(assert-event
 (let* ((oc *orlt-staged*) (event '(:begin 0))
        (next (orlt-ocfg-step oc event)))
   (and (fn-ocfg-staged oc)
        (not (fn-own-pending (fn-ocfg-owner oc)))
        (not (equal (car event) :complete))
        (implies (equal (car event) :close) (natp (cadr event)))
        (fn-own-pending (orlt-own-step (fn-ocfg-owner oc) event))
        (equal (fn-ocfg-config next) (fn-ocfg-config oc))
        (equal (fn-ocfg-staged next) (fn-ocfg-staged oc))
        (not (fn-own-pending (fn-ocfg-owner next))))))

; L2 :complete exclusion: retained hypotheses hold and the conjunction fails
; because completion clears the staged record (and publishes the config).
(assert-event
 (let* ((oc *orlt-staged*) (event '(:complete))
        (next (orlt-ocfg-step oc event)))
   (and (fn-ocfg-staged oc)
        (not (fn-own-pending (fn-ocfg-owner oc)))
        (equal (car event) :complete)
        (implies (equal (car event) :close) (natp (cadr event)))
        (not (equal (fn-ocfg-staged next) (fn-ocfg-staged oc)))
        (not (and (equal (fn-ocfg-config next) (fn-ocfg-config oc))
                  (equal (fn-ocfg-staged next) (fn-ocfg-staged oc))
                  (not (fn-own-pending (fn-ocfg-owner next))))))))

; L2 close-id hypothesis: round-1 counterexample, malformed :close NIL.
(assert-event
 (let* ((oc *orlt-staged-empty*) (event '(:close nil))
        (next (orlt-ocfg-step oc event)))
   (and (fn-ocfg-staged oc)
        (not (fn-own-pending (fn-ocfg-owner oc)))
        (not (equal (car event) :complete))
        (not (implies (equal (car event) :close) (natp (cadr event))))
        (not (and (equal (fn-ocfg-config next) (fn-ocfg-config oc))
                  (equal (fn-ocfg-staged next) (fn-ocfg-staged oc))
                  (not (fn-own-pending (fn-ocfg-owner next))))))))

; L3 positive: an authorized default record stays authorized when a real
; connection closes. Check the complete antecedent and conclusion.
(assert-event
 (let* ((oc *orlt-staged*) (event '(:close 0))
        (next (orlt-ocfg-step oc event)))
   (and (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner oc)))
        (fn-ocfg-staged oc)
        (not (fn-own-pending (fn-ocfg-owner oc)))
        (member-equal (car event) '(:open :close :read :octets :fault))
        (implies (equal (car event) :close) (natp (cadr event)))
        (fn-oclc-live-authorizep oc)
        (fn-oclc-live-authorizep next)
        (not (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner next)))))))

; L3 close-id hypothesis: the same round-1 malformed event destroys the
; staged authorization even though every retained hypothesis holds.
(assert-event
 (let* ((oc *orlt-staged-empty*) (event '(:close nil))
        (next (orlt-ocfg-step oc event)))
   (and (fn-ocfg-staged oc)
        (not (fn-own-pending (fn-ocfg-owner oc)))
        (member-equal (car event) '(:open :close :read :octets :fault))
        (not (implies (equal (car event) :close) (natp (cadr event))))
        (fn-oclc-live-authorizep oc)
        (not (fn-oclc-live-authorizep next)))))
