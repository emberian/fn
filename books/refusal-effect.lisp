; refusal-effect.lisp -- a refused request has no effect on the state, stated
; per host refusal entry, and the one refusal that does (fn-rfx-, lane
; closure-theorems, 2026-09-29).
;
; B10 (operability review): on a transaction-full store, refused POSTs
; consumed transaction ids without records; a configuration record accepted
; later carried an id above every stored article; the open computed its
; frontier from the article records and refused every later open as
; checkpoint-damaged.  No theorem had said what a refusal leaves behind, so
; nothing named the id the readers had to account for.  This book says it:
;
; COVERAGE: host refusal entry -> the ACL2 function -> the theorem.
;   fn-owner-prepare-buffer (host/owner-host.lisp): an article whose groups
;     the live configuration does not serve
;                        fn-psrv-prepare      fn-rfx-unserved-prepare-is-unchanged-by-definition
;   fn-owner-prepare-buffer: the budget refuses (:unaffordable)
;                        fn-prc-sbud-prepare  fn-rfx-unaffordable-prepare-is-unchanged-by-definition
;   fn-owner-reconfigure (host/owner-host.lisp): a configuration request the
;     owner does not admit
;                        fn-ocfg-reconfigure  fn-rfx-refused-reconfigure-is-unchanged-by-definition
;   fn-store-sn-io :log-reserve then fn-owner-refuse-reservation
;     (host/store-node-host.lisp, host/owner-host.lisp): THE FULL-STORE POST
;     REFUSAL.  NOT effect-free, by design (books/store-node-resolution.lisp:
;     "a semantic refusal consumes the durable file reservation and advances
;     the actual idle node over the same txid").  What it consumes, exactly:
;     one transaction id -- the files' frontier and the node's next txid are
;     both one higher; the records, the groups and the capacity are what
;     they were.
;                        fn-olr-sn-reserve, fn-sn-refuse-reservation
;                                             fn-rfx-refused-post-keeps-records
;                                             fn-rfx-refused-post-keeps-configuration
;                                             fn-rfx-refused-post-consumes-one-txid
;   The readers of ids that must account for the consumed one:
;     the configuration record's txid is the node's next txid at staging (so
;     it stands above every burned id):
;                        fn-ocfg-reconfig-record  fn-rfx-config-record-txid-is-the-node-next-by-definition
;     the open's frontier over the records and the configuration records:
;                        lane limits-live-2, books/open-frontier.lisp
;                        fn-ofr-loop-ok-within-frontier [landing]
;     the export carries the frontier: books/store-export.lisp
;                        fn-sxp-import-of-export-replays-the-same-history (PRF-205)
;   Refusals whose entry is a decision with no state (TLS, auth): the
;     decision's word is the whole effect; the connection state is the
;     caller's -- books/nntp-auth.lisp fn-auth-step-protected-only-refuses-
;     authinfo-before-tls, books/tls-reload.lisp fn-tlsr-decide-carries-the-
;     facts-or-a-named-refusal.  A limits refusal (fn-lim-decide :refused,
;     lane limits-live-2) publishes nothing [landing].

(in-package "ACL2")

(include-book "store-log-route-phases")
(include-book "store-node-resolution")
(include-book "owner-prepare-served")

; -----------------------------------------------------------------------------
; The effect-free refusals, by definition: the else branches with their
; tests negated.

(defthm fn-rfx-unserved-prepare-is-unchanged-by-definition
  (implies (not (fn-psrv-event-servedp (fn-ocfg-config oc) record))
           (equal (fn-psrv-prepare oc record budget carry) oc))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-psrv-prepare))))

(defthm fn-rfx-unaffordable-prepare-is-unchanged-by-definition
  (implies (not (fn-sbud-admitp budget (fn-sbud-count (fn-sbud-oc-store oc))))
           (equal (fn-prc-sbud-prepare oc record budget carry) oc))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prc-sbud-prepare))))

(defthm fn-rfx-refused-reconfigure-is-unchanged-by-definition
  (implies (not (fn-ocfg-reconfig-okp oc id deltas))
           (equal (fn-ocfg-reconfigure oc id deltas) oc))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ocfg-reconfigure))))

; The configuration record's txid is the node's next txid when it is staged:
; after a burned reservation the node stands one past the burned id
; (fn-rfx-refused-post-consumes-one-txid), so the record's id does too.
(defthm fn-rfx-config-record-txid-is-the-node-next-by-definition
  (equal (fn-cfg-record-txid (fn-ocfg-reconfig-record oc deltas))
         (fn-state-next-txid
          (fn-node-acceptance
           (fn-sn-node (fn-own-store (fn-ocfg-owner oc))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ocfg-reconfig-record))))

; -----------------------------------------------------------------------------
; THE FULL-STORE POST REFUSAL, as the host composes it: the reservation
; (fn-store-sn-io :log-reserve = fn-olr-sn-reserve, books/store-log-route)
; then the semantic refusal at the reserved txid (fn-owner-refuse-reservation
; -> (:store (:refuse-reservation TXID)) -> fn-sn-refuse-reservation).  The
; reservation's own effects are books/store-log-route-phases
; fn-olr-sn-reserve-reaches-reserved (phase :reserved, frontier one higher,
; records kept); the refusal's are books/store-node-resolution
; fn-sn-refuse-reservation-is-exact-advance and fn-snrt-refuse-keeps-records.

(defthm fn-rfx-reserve-keeps-the-node
  (equal (fn-sn-node (fn-olr-sn-reserve s)) (fn-sn-node s))
  :hints (("Goal" :in-theory (enable fn-olr-sn-reserve fn-sn-io fn-sn-update))))

(defthm fn-rfx-reserve-keeps-the-configuration
  (and (equal (fn-sn-groups (fn-olr-sn-reserve s)) (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-olr-sn-reserve s)) (fn-sn-capacity s)))
  :hints (("Goal" :in-theory (enable fn-olr-sn-reserve fn-sn-io fn-sn-update))))

(defthm fn-rfx-reserve-preserves-state
  (implies (fn-sn-statep s) (fn-sn-statep (fn-olr-sn-reserve s)))
  :hints (("Goal" :in-theory (e/d (fn-olr-sn-reserve-is-the-file-route-by-definition)
                                  (fn-olr-sn-reserve fn-sn-io)))))

(defthm fn-rfx-refuse-keeps-the-frontier
  (implies (fn-sn-refuse-reservation-enabledp s txid)
           (equal (fn-sf-frontier (fn-sn-files (fn-sn-refuse-reservation s txid)))
                  (fn-sf-frontier (fn-sn-files s))))
  :hints (("Goal" :in-theory (enable fn-sn-refuse-reservation fn-sn-update
                                     fn-sf-refuse-reservation
                                     fn-sn-refuse-reservation-enabledp))))

; What the refusal leaves: the records it found.
(defthm fn-rfx-refused-post-keeps-records
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready)
                (< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*))
           (equal (fn-sf-records
                   (fn-sn-files (fn-sn-refuse-reservation (fn-olr-sn-reserve s) txid)))
                  (fn-sf-records (fn-sn-files s))))
  :hints (("Goal" :in-theory (disable fn-olr-sn-reserve fn-sn-refuse-reservation
                                      fn-olr-sn-reserve-is-the-file-route-by-definition))))

; ... the groups and the capacity it found ...
(defthm fn-rfx-refused-post-keeps-configuration
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready)
                (< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*))
           (and (equal (fn-sn-groups (fn-sn-refuse-reservation (fn-olr-sn-reserve s) txid))
                       (fn-sn-groups s))
                (equal (fn-sn-capacity (fn-sn-refuse-reservation (fn-olr-sn-reserve s) txid))
                       (fn-sn-capacity s))))
  :hints (("Goal" :in-theory (disable fn-olr-sn-reserve fn-sn-refuse-reservation
                                      fn-olr-sn-reserve-is-the-file-route-by-definition))))

; ... and what it consumes: exactly one transaction id.  With the
; reservation's txid (the frontier the store stood at) and a node that can
; advance over it, the files are :ready again one past where they were and
; the node's next txid is that same number.  Every reader of ids accounts
; for this one: the configuration record takes the node's next txid
; (fn-rfx-config-record-txid-is-the-node-next-by-definition), the open joins
; the records' and the configuration records' next ids (lane limits-live-2,
; books/open-frontier.lisp), the export carries the frontier
; (books/store-export.lisp).
(defthm fn-rfx-refused-post-consumes-one-txid
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready)
                (< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*)
                (equal txid (fn-sf-frontier (fn-sn-files s)))
                (fn-replay-advance-okp (fn-sn-node s) (+ 1 (fn-sf-frontier (fn-sn-files s)))))
           (and (equal (fn-sf-phase
                        (fn-sn-files (fn-sn-refuse-reservation (fn-olr-sn-reserve s) txid)))
                       :ready)
                (equal (fn-sf-frontier
                        (fn-sn-files (fn-sn-refuse-reservation (fn-olr-sn-reserve s) txid)))
                       (+ 1 (fn-sf-frontier (fn-sn-files s))))
                (equal (fn-state-next-txid
                        (fn-node-acceptance
                         (fn-sn-node (fn-sn-refuse-reservation (fn-olr-sn-reserve s) txid))))
                       (+ 1 (fn-sf-frontier (fn-sn-files s))))))
  :hints (("Goal" :use (fn-rfx-reserve-preserves-state
                        (:instance fn-sn-refuse-reservation-is-exact-advance
                                   (s (fn-olr-sn-reserve s)))
                        (:instance fn-rfx-refuse-keeps-the-frontier
                                   (s (fn-olr-sn-reserve s))))
           :in-theory (e/d (fn-sn-refuse-reservation-enabledp)
                           (fn-olr-sn-reserve fn-sn-refuse-reservation
                            fn-olr-sn-reserve-is-the-file-route-by-definition
                            fn-sn-refuse-reservation-is-exact-advance
                            fn-rfx-refuse-keeps-the-frontier
                            fn-rfx-reserve-preserves-state)))))
