; owner-outcome-pinned.lisp -- the served outcomes over the CONFIGURED owner
; (fn-oop-, lane owner-relation-2, PKT-889).
;
; host/owner-host.lisp fn-owner-outcome and fn-owner-transit-outcome called
; fn-apc-own-outcome and fn-own-transit-outcome on the raw owner and
; installed the result with fn-owner-replace-core, which keeps the pin table
; as it was.  A :durable completion advances the connection to the committed
; view (fn-own-advance: the session is rebuilt over the current archive at
; the view's version and frontier) and the pin table did not follow: the
; connection's pin still named the configuration it was opened under, so
; after a reconfiguration published while it was open, the configured
; owner's relation (books/config-owner-live-complete.lisp fn-ocl-relation:
; fn-ocl-conn-historyp asks the pinned generation to replay to the
; connection's version) was false after the first durable POST.  ADVANCE
; and a GROUP that re-pins (NNT-042) move the pin through fn-ocfg-advance /
; fn-ocfg-with-read-owner's REPINNED; the outcome had no configured form.
;
; These are the two outcomes with the advance routed through the configured
; owner: the owner the host installs is exactly the raw outcome's owner
; (fn-oop-outcome-is-apc-own-outcome, fn-oop-transit-outcome-is-own-transit-
; outcome: no hypothesis), the effects are the same, and the pin of a
; connection the advance admitted is set to the live configuration, as
; fn-ocfg-advance sets it.  books/owner-host-relation.lisp proves both keep
; fn-ocl-relation and the carried fn-lgoc-invariantp.
;
; fn-oop-advance is fn-ocfg-advance with the carried advance
; (books/owner-advance-carried.lisp fn-acar-own-advance-result: the rebuilt
; session tested at the node the held session carries), equal to it under
; the relation (fn-oop-advance-is-ocfg-advance-under-ocl-relation).  The
; transit outcome keeps the reference advance it had (fn-own-advance, hence
; fn-ocfg-advance), so its equality carries no hypothesis.

(in-package "ACL2")

(include-book "owner-parse-carried")

; -----------------------------------------------------------------------------
; The configured advance with the carried rebuild.

(defun fn-oop-advance (oc id)
  (declare (xargs :guard t))
  (let* ((advanced (fn-acar-own-advance-result (fn-ocfg-owner oc) id))
         (o (cdr advanced)))
    (fn-ocfg-make o (fn-ocfg-config oc)
                  (if (equal (car advanced) :advanced)
                      (fn-ocfg-pin-set id (fn-ocfg-config oc) (fn-ocfg-pins oc))
                    (fn-ocfg-pins oc))
                  (fn-ocfg-staged oc))))

(defthm fn-oop-advance-is-ocfg-advance-under-ocl-relation
  (implies (fn-ocl-relation oc)
           (equal (fn-oop-advance oc id) (fn-ocfg-advance oc id)))
  :hints (("Goal" :in-theory (e/d (fn-oop-advance fn-ocfg-advance)
                                  (fn-acar-own-advance-result fn-own-advance-result
                                   fn-ocl-relation fn-acar-conn-sessionp
                                   fn-acar-view-statep)))))

; -----------------------------------------------------------------------------
; The served POST outcome (host/owner-host.lisp fn-owner-outcome).  NEXT is
; fn-apc-own-outcome's owner before its advance, named so the frame lemmas
; of books/owner-host-relation.lisp state it once.

(defun fn-oop-outcome-next (o id sub completion icar carry)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
               (fn-own-next-id o) (fn-own-max-conns o)
               (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
               (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
               (fn-own-config o) (fn-own-queue o) nil
               (if (equal completion :durable)
                   (fn-own-feed-enqueue-all
                    (fn-apc-submission-targets o icar carry)
                    (fn-own-feeds o)
                    (fn-own-sub-msgid sub) (fn-own-feed-stamp o))
                 (fn-own-feeds o))
               (fn-own-node-secret o) (fn-own-refused o)))

(defun fn-oop-outcome (oc id word icar carry)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (sub (fn-own-inflight o)))
    (if (and conn sub (equal (fn-own-sub-id sub) id))
        (let* ((completion (fn-own-outcome-completion o word))
               (oc2 (fn-ocfg-with-owner
                     oc (fn-oop-outcome-next o id sub completion icar carry))))
          (cons (fn-served-result-effects
                 (fn-served-post-outcome
                  (fn-served-make-conn-group-indexed (fn-own-conn-wire conn)
                                       (fn-own-conn-session conn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-own-clock o)
                                       (fn-own-conn-verdicts conn)
                                       (fn-own-conn-index conn)
                                       (fn-own-conn-group-index conn)
                                       (fn-own-conn-control conn))
                  (fn-own-post-rendering o word)))
                (if (equal completion :durable)
                    (fn-oop-advance oc2 id)
                  oc2)))
      (cons nil oc))))

; KEYSTONE for the host line: the effects and the owner are
; fn-apc-own-outcome's (hence fn-acar-own-outcome's and fn-own-outcome's
; under their carries and the relation), with no hypothesis.
(defthm fn-oop-outcome-is-apc-own-outcome
  (and (equal (car (fn-oop-outcome oc id word icar carry))
              (car (fn-apc-own-outcome (fn-ocfg-owner oc) id word icar carry)))
       (equal (fn-ocfg-owner (cdr (fn-oop-outcome oc id word icar carry)))
              (cdr (fn-apc-own-outcome (fn-ocfg-owner oc) id word icar carry))))
  :hints (("Goal" :in-theory (e/d (fn-oop-outcome fn-oop-outcome-next
                                   fn-apc-own-outcome fn-oop-advance
                                   fn-ocfg-with-owner)
                                  (fn-acar-own-advance-result fn-served-post-outcome
                                   fn-own-outcome-completion fn-own-feed-enqueue-all
                                   fn-apc-submission-targets fn-own-post-rendering
                                   fn-served-make-conn-group-indexed
                                   fn-own-feed-stamp)))))

(defthm fn-oop-outcome-keeps-config-and-staged
  (and (equal (fn-ocfg-config (cdr (fn-oop-outcome oc id word icar carry)))
              (fn-ocfg-config oc))
       (equal (fn-ocfg-staged (cdr (fn-oop-outcome oc id word icar carry)))
              (fn-ocfg-staged oc)))
  :hints (("Goal" :in-theory (e/d (fn-oop-outcome fn-oop-advance fn-ocfg-with-owner)
                                  (fn-acar-own-advance-result fn-served-post-outcome
                                   fn-own-outcome-completion fn-oop-outcome-next
                                   fn-own-post-rendering
                                   fn-served-make-conn-group-indexed)))))

; -----------------------------------------------------------------------------
; The transit outcome (host/owner-host.lisp fn-owner-transit-outcome).

(defun fn-oop-transit-next (o id conn sub completion kind reason)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
               (fn-own-next-id o) (fn-own-max-conns o)
               (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
               (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
               (fn-own-config o) (fn-own-queue o) nil
               (if (equal completion :durable)
                   (fn-own-feed-durable o sub)
                 (fn-own-feeds o))
               (fn-own-node-secret o)
               (fn-own-transit-refused o conn sub kind reason)))

(defun fn-oop-transit-outcome (oc id kind reason word)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (sub (fn-own-inflight o)))
    (if (and conn sub (equal (fn-own-sub-id sub) id) (fn-own-transit-subp sub))
        (let* ((d (fn-peer-decision kind reason))
               (completion (if (equal kind :want)
                               (fn-own-outcome-completion o word)
                             nil))
               (oc2 (fn-ocfg-with-owner
                     oc (fn-oop-transit-next o id conn sub completion kind reason))))
          (cons (fn-served-result-effects
                 (fn-served-transit-outcome
                  (fn-served-make-conn-group-indexed (fn-own-conn-wire conn)
                                       (fn-own-conn-session conn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-own-clock o)
                                       (fn-own-conn-verdicts conn)
                                       (fn-own-conn-index conn)
                                       (fn-own-conn-group-index conn)
                                       (fn-own-conn-control conn))
                  (fn-own-sub-decision sub) d
                  (if (equal kind :want) (fn-own-outcome-rendering o word) nil)))
                (if (equal completion :durable)
                    (fn-ocfg-advance oc2 id)
                  oc2)))
      (cons nil oc))))

; KEYSTONE for the host line: the effects and the owner are
; fn-own-transit-outcome's, with no hypothesis.
(defthm fn-oop-transit-outcome-is-own-transit-outcome
  (and (equal (car (fn-oop-transit-outcome oc id kind reason word))
              (car (fn-own-transit-outcome (fn-ocfg-owner oc) id kind reason word)))
       (equal (fn-ocfg-owner (cdr (fn-oop-transit-outcome oc id kind reason word)))
              (cdr (fn-own-transit-outcome (fn-ocfg-owner oc) id kind reason word))))
  :hints (("Goal" :in-theory (e/d (fn-oop-transit-outcome fn-oop-transit-next
                                   fn-own-transit-outcome fn-ocfg-advance
                                   fn-own-advance fn-ocfg-with-owner)
                                  (fn-own-advance-result fn-served-transit-outcome
                                   fn-own-outcome-completion fn-own-outcome-rendering
                                   fn-own-feed-durable fn-own-transit-refused
                                   fn-peer-decision fn-served-make-conn-group-indexed
                                   fn-own-transit-subp)))))

(defthm fn-oop-transit-outcome-keeps-config-and-staged
  (and (equal (fn-ocfg-config (cdr (fn-oop-transit-outcome oc id kind reason word)))
              (fn-ocfg-config oc))
       (equal (fn-ocfg-staged (cdr (fn-oop-transit-outcome oc id kind reason word)))
              (fn-ocfg-staged oc)))
  :hints (("Goal" :in-theory (e/d (fn-oop-transit-outcome fn-ocfg-advance fn-ocfg-with-owner)
                                  (fn-own-advance-result fn-served-transit-outcome
                                   fn-own-outcome-completion fn-oop-transit-next
                                   fn-own-outcome-rendering fn-peer-decision
                                   fn-served-make-conn-group-indexed)))))
