; Context field9 vocabulary; existing query context fields0..8 are unchanged.
; The row owns references to actual actor holder roots, never category bits or
; an asserted joined flag. This book creates no terminal disposition.
(in-package "ACL2")
(include-book "receiver-turn-controller")

(defun fn-rxt-recipient-jobp (job)
 (declare (xargs :guard t))
 (and (consp job) (eq (car job) :receiver-recipient)
      (consp (cdr job)) (cadr job)
      (consp (cddr job)) (fn-rxt-pending-rangep (caddr job))
      (consp (cdddr job)) (natp (cadddr job))
      (consp (cddddr job)) (natp (car (cddddr job)))
      (<= (cadddr job) (car (cddddr job)))
      (equal (car (cddddr job)) (caddr (caddr job)))
      (consp (cdr (cddddr job)))
      (let ((roots (cadr (cddddr job))))
       (and (fn-rxt-fixed-widthp roots 3)
            (eq (fn-prl-nth 0 roots) :reader-response-roots)
            (fn-rxt-parser-jobp (fn-prl-nth 1 roots))
            (fn-rxt-fixed-widthp (fn-prl-nth 2 roots) 6)
            (eq (fn-prl-nth 0 (fn-prl-nth 2 roots)) :reader-actor)
            (equal (fn-prl-nth 1 (fn-prl-nth 2 roots)) (cadr job))
            (eq (fn-prl-nth 3 (fn-prl-nth 2 roots)) :response-owned)))
      (null (cddr (cddddr job)))))

(defun fn-owner-rx-turn-custody-row
 (ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (let ((job (fn-rxt-job fn-receiver-turn)))
  (if (not (and (eq (fn-rxt-phase fn-receiver-turn) :transferred)
                (fn-rxt-owned-claim-p ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
                (null (fn-rxp-capacity fn-rx-provider))
                (fn-rxt-recipient-jobp job)))
      (mv :unavailable-custody nil)
   ; Initial query holder is the exact recipient. Remaining actor roots can
   ; only be populated by their actual registered acquisition transitions.
   (mv :retained-custody
       (list :receiver-custody (fn-rxt-source fn-receiver-turn)
             (cadr job) (caddr job) (cadddr job) (car (cddddr job))
             :retained (cadr job) nil (cadr (cddddr job)) nil nil)))))

(defthm fn-owner-rx-turn-custody-row-preserves-stored-suffix
 (let ((answer (fn-owner-rx-turn-custody-row ticket fn-rx-provider
                                           fn-receiver-turn fn-page-read-pool)))
  (implies (equal (mv-nth 0 answer) :retained-custody)
   (and (equal (fn-prl-nth 1 (mv-nth 1 answer)) (fn-rxt-source fn-receiver-turn))
        (equal (fn-prl-nth 2 (mv-nth 1 answer)) (cadr (fn-rxt-job fn-receiver-turn)))
        (natp (fn-prl-nth 4 (mv-nth 1 answer)))
        (<= (fn-prl-nth 4 (mv-nth 1 answer)) (fn-prl-nth 5 (mv-nth 1 answer)))
        (<= (fn-prl-nth 5 (mv-nth 1 answer)) 4096))))
 :hints (("Goal" :in-theory (enable fn-owner-rx-turn-custody-row
                                   fn-rxt-recipient-jobp fn-rxt-pending-rangep fn-prl-nth)))
 :rule-classes nil)
