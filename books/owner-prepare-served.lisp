; fn: the owner's prepares decide what the configured replay will refuse
; (lane prepare-served, 2026-09-27; PKT-827 (d) and its follow-ons).
;
; Three entries host/owner-host.lisp calls, and the un-stage of a refused
; configuration request.  Before this lane the served-group test of an
; article was host code (fn-owner-prepare-buffer tested
; fn-cnode-selection-servedp, then called fn-prc-sbud-prepare, which staged
; an article whatever its groups); the signed composite's identity prepare
; had no served test at all; the topic prepare staged an event its
; completion's consumer projection could refuse; and nothing un-staged a
; configuration record whose publication was refused before it was written,
; so the owner kept the configuration lock and refused every later POST
; (:begin and :take refuse while a record is staged) until a restart.
; books/owner-prepare-served-ocl.lisp proves the carried owner invariant
; across each.
;
; This book shares the prefix `fn-psrv-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "post-retain-carried")
(include-book "owner-commit-carried")
(include-book "owner-identity-intern")

; -----------------------------------------------------------------------------
; The served decision.  An event that creates an article (a held row, or the
; signed composite's held row) names groups; the configured replay
; (books/config-physical-replay.lisp fn-cpr-event-servedp) refuses one whose
; groups the configuration does not serve.  Every other event names no group.
(defun fn-psrv-event-servedp (config event)
  (declare (xargs :guard t))
  (cond ((fn-held-p event)
         (fn-cnode-selection-servedp config (fn-record-groups event)))
        ((fn-hstxa-p event)
         (fn-cnode-selection-servedp
          config (fn-record-groups (fn-replay-composite-held event))))
        (t t)))

; THE ARTICLE PREPARE THE HOST CALLS (host/owner-host.lisp
; fn-owner-prepare-buffer).  An article whose groups the live configuration
; does not serve -- a retired group, still in the Store's allocation domain
; -- leaves the owner unchanged; otherwise it is fn-prc-sbud-prepare.
(defun fn-psrv-prepare (oc record budget carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-pidx-view-okp
                               (fn-own-view (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry))))
  (if (fn-psrv-event-servedp (fn-ocfg-config oc) record)
      (fn-prc-sbud-prepare oc record budget carry)
    oc))

; The word the host reports when the prepare left the owner unchanged: an
; unserved group is :refused whatever the budget; otherwise the budget's
; word (fn-sbud-refusal-kind).
(defun fn-psrv-refusal-kind (oc record budget)
  (declare (xargs :guard t))
  (if (fn-psrv-event-servedp (fn-ocfg-config oc) record)
      (fn-sbud-refusal-kind oc budget)
    :refused))

; THE IDENTITY PREPARE THE HOST CALLS (host/owner-host.lisp
; fn-owner-prepare-identity): a signed composite whose article's groups the
; live configuration does not serve leaves the owner unchanged; otherwise
; fn-ccar-ocfg-prepare-identity (PRF-144, PRF-193).
(defun fn-psrv-prepare-identity (oc event)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
  (if (fn-psrv-event-servedp (fn-ocfg-config oc) event)
      (fn-ccar-ocfg-prepare-identity oc event)
    oc))

; THE TOPIC PREPARE THE HOST CALLS (host/owner-host.lisp
; fn-owner-prepare-topic): the configured owner's (:store (:prepare-topic E))
; when the carried consumer projection accepts E at the Store's next
; sequence, which the completion requires (fn-sn-completion-enabledp) and
; fn-sn-prepare-topic does not test; otherwise the owner unchanged.
(defun fn-psrv-prepare-topic (oc event)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o)))
    (if (and (fn-store-event-p event)
             (eq (car (fn-ccar-cpe-projection-step
                       (fn-sn-consumer s) event (fn-sn-identity-next s)))
                 :ok))
        (fn-ocfg-with-owner
         oc
         (fn-own-refresh
          (fn-own-make (fn-sn-prepare-topic s event)
                       (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
                       (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
                       (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                       (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
                       (fn-own-node-secret o) (fn-own-refused o))))
      oc)))

; THE UN-STAGE (host/owner-host.lisp fn-owner-reconfigure-unstage; called by
; host/native/admin.lisp fnn-owner-live-reconfigure-locked when the staged
; record's publication is refused BEFORE anything was written: the
; authorization, the candidate open, or the immutable publisher's :refused).
; The staged record is the configuration transaction lock; it lives in no
; durable file, so dropping it is the whole transition and a process death on
; either side of it recovers the same durable history.  An uncertain
; publication never reaches it (the host fences and recovers instead).
(defun fn-psrv-unstage (oc)
  (declare (xargs :guard t))
  (if (fn-ocfg-staged oc)
      (fn-ocfg-make (fn-ocfg-owner oc) (fn-ocfg-config oc) (fn-ocfg-pins oc) nil)
    oc))

(defthm fn-psrv-prepare-refuses-unserved
  (implies (not (fn-psrv-event-servedp (fn-ocfg-config oc) record))
           (and (equal (fn-psrv-prepare oc record budget carry) oc)
                (equal (fn-psrv-refusal-kind oc record budget) :refused)
                (equal (fn-psrv-prepare-identity oc record) oc))))

(defthm fn-psrv-prepare-when-served
  (implies (fn-psrv-event-servedp (fn-ocfg-config oc) record)
           (and (equal (fn-psrv-prepare oc record budget carry)
                       (fn-prc-sbud-prepare oc record budget carry))
                (equal (fn-psrv-refusal-kind oc record budget)
                       (fn-sbud-refusal-kind oc budget))
                (equal (fn-psrv-prepare-identity oc record)
                       (fn-ccar-ocfg-prepare-identity oc record)))))

;; The bridge to the budget gate (planning/current-view.json P9): where the
;; groups are served, the host's prepare is fn-sbud-prepare under the carry's
;; recognizer and the carried view premises PRF-191/PRF-242 name
;; (fn-prc-sbud-prepare-is-pidx-sbud-prepare,
;; fn-pidx-sbud-prepare-is-pcar-sbud-prepare,
;; fn-pcar-sbud-prepare-is-sbud-prepare); where they are not, the owner is
;; unchanged at every budget.
(defthm fn-psrv-prepare-is-sbud-prepare-when-served
  (implies (and (fn-psrv-event-servedp (fn-ocfg-config oc) record)
                (fn-prc-carryp carry)
                (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner oc)))
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-ceis-indexedp (fn-sbud-oc-store oc)))
           (equal (fn-psrv-prepare oc record budget carry)
                  (fn-sbud-prepare oc record budget)))
  :hints (("Goal" :use (fn-psrv-prepare-when-served
                        fn-prc-sbud-prepare-is-pidx-sbud-prepare
                        fn-pidx-sbud-prepare-is-pcar-sbud-prepare
                        fn-pcar-sbud-prepare-is-sbud-prepare)
           :in-theory nil)))

(in-theory (disable fn-psrv-prepare fn-psrv-refusal-kind fn-psrv-prepare-identity
                    fn-psrv-prepare-topic))
