; Per-destination forwarding of held transit (PKT-261; specs/bp-node-machine.md
; 4.8, 9.5).
;
; A relay's :progress event carries the configuration's route table as
; (:table TABLE) (`fn-bpnp-route-peer'), so each held row is dispatched to
; the neighbour `fn-bprt-outbound-choice' names for its own destination, and
; the kind-6 record makes that neighbour's EID the row's next hop (slot 11).
; After each pass the host asks `fn-bpnp-forward-plan' which outbound
; sessions to open: one per next hop that has forward-pending held transit,
; each with the boundary, EID and contact port the route table names for
; the oldest such row.  Each session offers only rows whose next hop is its
; peer (`fn-bpnp-forward-candidatep'), so one pass offers a held row on at
; most one session.
(in-package "ACL2")
(include-book "bp-node-progress-guards")
(set-verify-guards-eagerness 0)

(defun fn-bpnp-forward-plan-rows (ordered table seen)
  (declare (xargs :guard t :measure (acl2-count ordered)))
  (if (atom ordered) nil
    (let* ((h (car ordered))
           (peer (fn-bpn-nth 11 h))
           (choice (fn-bprt-outbound-choice (fn-bpnp-held-dest h) table)))
      (if (and (equal (fn-bpn-nth 12 h) '(:forward-pending))
               (null (fn-bpn-nth 14 h))
               (fn-bpp-eidp peer)
               (not (member-equal peer (fix-true-list seen)))
               (equal (fn-bprt-nth 0 choice) :hop))
          (cons (list peer (fn-bprt-nth 1 choice) (fn-bprt-nth 2 choice)
                      (fn-bprt-nth 3 choice))
                (fn-bpnp-forward-plan-rows (cdr ordered) table
                                           (cons peer (fix-true-list seen))))
        (fn-bpnp-forward-plan-rows (cdr ordered) table seen)))))

; The host's question after each pass (host/native/bp-node.lisp
; `fnn-bpnode-forward-contact'): a list of (PEER BOUNDARY EID PORT), oldest
; held row first.
(defun fn-bpnp-forward-plan (held table)
  (declare (xargs :guard (true-listp held)))
  (fn-bpnp-forward-plan-rows (reverse held) table nil))

(defun fn-bpnp-plan-peers (plan)
  (declare (xargs :guard t))
  (if (consp plan)
      (cons (fn-bprt-nth 0 (car plan)) (fn-bpnp-plan-peers (cdr plan)))
    nil))

; ---------------------------------------------------------------------------
; The next hop over the table is the routed hop.

(defthm fn-bpnp-table-route-peer-is-the-routed-hop
  (let ((peer (fn-bpnp-route-peer dest (list :table table)))
        (choice (fn-bprt-outbound-choice (fn-bpaj-eid-text dest) table)))
    (implies (and peer (fn-bprt-tablep table))
             (and (fn-bpp-eidp peer)
                  (equal (car choice) :hop)
                  (equal (fn-bpaj-eid-text peer) (fn-bprt-nth 2 choice)))))
  :hints (("Goal" :in-theory (disable fn-bprt-next-hop fn-bprt-hop-route
                                      fn-bprt-contactable fn-bpaj-eid-text
                                      fn-bpp-eidp fn-bprt-tablep
                                      fn-bprt-next-hop-names-a-live-matching-route))))

; ---------------------------------------------------------------------------
; One session per peer per pass, and a held row offered on at most one.

(local (defthm plan-peers-not-seen
  (implies (member-equal p (fix-true-list seen))
           (not (member-equal p (fn-bpnp-plan-peers
                                 (fn-bpnp-forward-plan-rows ordered table seen)))))
  :hints (("Goal" :in-theory (disable fn-bprt-outbound-choice fn-bpnp-held-dest
                                      fn-bpp-eidp)))))

(local (defthm plan-peers-distinct
  (no-duplicatesp-equal
   (fn-bpnp-plan-peers (fn-bpnp-forward-plan-rows ordered table seen)))
  :hints (("Goal" :in-theory (disable fn-bprt-outbound-choice fn-bpnp-held-dest
                                      fn-bpp-eidp)))))

(defthm fn-bpnp-forward-plan-has-one-session-per-peer
  (no-duplicatesp-equal (fn-bpnp-plan-peers (fn-bpnp-forward-plan held table))))

(local (defthm member-plan-peer
  (implies (member-equal e plan)
           (member-equal (fn-bprt-nth 0 e) (fn-bpnp-plan-peers plan)))))

(local (defthm distinct-peers-name-one-entry
  (implies (and (no-duplicatesp-equal (fn-bpnp-plan-peers plan))
                (member-equal e1 plan) (member-equal e2 plan)
                (equal (fn-bprt-nth 0 e1) (fn-bprt-nth 0 e2)))
           (equal e1 e2))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bprt-nth)
           :induct (fn-bpnp-plan-peers plan)))))

(local (defthm forward-scan-ready-is-a-candidate
  (implies (equal (car (fn-bpnp-forward-scan ordered peer mru node obs waits
                                             free epoch budget))
                  :ready)
           (fn-bpnp-forward-candidatep
            (fn-bpn-nth 1 (fn-bpnp-forward-scan ordered peer mru node obs waits
                                                free epoch budget))
            peer obs epoch budget))
  :hints (("Goal" :induct (fn-bpnp-forward-scan ordered peer mru node obs waits
                                                free epoch budget)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-bpnp-forward-scan car-cons cdr-cons
                                        fn-bpn-nth fn-cbor-ag-car
                                        (:executable-counterpart natp)
                                        (:executable-counterpart not)
                                        (:executable-counterpart zp)
                                        (:executable-counterpart binary-+)
                                        (:executable-counterpart equal)))))))

(local (defthm candidate-names-its-next-hop
  (implies (fn-bpnp-forward-candidatep h peer obs epoch budget)
           (equal (fn-bpn-nth 11 h) peer))
  :rule-classes :forward-chaining))

; KEYSTONE.  The sessions of one pass are the plan's entries; a session to
; peer P offers the row its scan selects (`fn-bpnp-forward-scan', which the
; routed :session event runs, fn-bpnp-routed-start).  A held row selected
; on the sessions of two plan entries was selected on one entry's session:
; one pass offers each held row at most once.
(defthm fn-bpnp-forward-plan-offers-a-row-on-one-session
  (let ((plan (fn-bpnp-forward-plan held table))
        (s1 (fn-bpnp-forward-scan o1 (fn-bprt-nth 0 e1) mru1 node obs w1 f1
                                  epoch budget))
        (s2 (fn-bpnp-forward-scan o2 (fn-bprt-nth 0 e2) mru2 node obs w2 f2
                                  epoch budget)))
    (implies (and (member-equal e1 plan) (member-equal e2 plan)
                  (equal (car s1) :ready) (equal (car s2) :ready)
                  (equal (fn-bpn-nth 1 s1) (fn-bpn-nth 1 s2)))
             (equal e1 e2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bpnp-forward-scan fn-bpnp-forward-plan
                                      fn-bpnp-forward-candidatep
                                      forward-scan-ready-is-a-candidate)
           :use ((:instance forward-scan-ready-is-a-candidate
                  (ordered o1) (peer (fn-bprt-nth 0 e1)) (mru mru1)
                  (waits w1) (free f1))
                 (:instance forward-scan-ready-is-a-candidate
                  (ordered o2) (peer (fn-bprt-nth 0 e2)) (mru mru2)
                  (waits w2) (free f2))
                 (:instance distinct-peers-name-one-entry
                  (plan (fn-bpnp-forward-plan held table)))))))

; ---------------------------------------------------------------------------
; The dispatch names the routed hop.  The :progress event under (:table
; TABLE) proposes a kind-6 record whose peer field is the EID of the
; boundary `fn-bprt-outbound-choice' routes the record's own row to; the
; durable apply (`fn-bpnp-dispatch-apply', `fn-bpnp-dispatched-held') writes
; that field into the row's next-hop slot 11.

(local (defthm arrival-count-of-member
  (implies (member-equal h held)
           (<= 1 (fn-bpnf-arrival-count (fn-bpn-nth 3 h) held)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-bpn-nth)))))

(local (defthm find-arrival-of-unique-member
  (implies (and (member-equal h held)
                (equal (fn-bpnf-arrival-count (fn-bpn-nth 3 h) held) 1))
           (equal (fn-bpnf-find-arrival (fn-bpn-nth 3 h) held) h))
  :hints (("Goal" :in-theory (disable fn-bpn-nth)))))

(local (defthm oldest-eligible-with-credit-is-a-member
  (let ((sel (fn-bpnp-oldest-eligible-with-credit
              held node obs routes generation waits free budget selected)))
    (implies (and sel (not (equal sel selected)))
             (member-equal sel held)))
  :hints (("Goal" :induct (fn-bpnp-oldest-eligible-with-credit
                            held node obs routes generation waits free budget
                            selected)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-bpnp-oldest-eligible-with-credit
                                        member-equal car-cons cdr-cons))))))

(local (defthm with-waits-keeps-held-epoch-op
  (and (equal (fn-bpnf-held-list (fn-bpnp-with-waits st waits))
              (fn-bpnf-held-list st))
       (equal (fn-bpnf-epoch (fn-bpnp-with-waits st waits))
              (fn-bpnf-epoch st))
       (equal (fn-bpnf-next-op (fn-bpnp-with-waits st waits))
              (fn-bpnf-next-op st)))
  :hints (("Goal" :in-theory (e/d (fn-bpnp-with-waits)
                                  (fn-bpnf-state-with-arrival))))))

(local (defthm answer-effects-of-answer
  (equal (fn-bpnf-answer-effects (fn-bpnf-answer st effects)) effects)))

(local (defthm busy-stranded-effects-propose-no-dispatch
  (not (equal (car (car (fn-bpnp-busy-stranded-effects held budget)))
              :persist-dispatch))
  :hints (("Goal" :in-theory (disable fn-bpnp-first-busy-stranded
                                      fn-bpnp-wait-key fn-bpnp-busy-count)))))

(local (defthm deliver-step-proposes-no-dispatch
  (not (equal (car (car (fn-bpnf-answer-effects
                         (fn-bpah-deliver-step st key node))))
              :persist-dispatch))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                            '(fn-bpah-deliver-step
                                              answer-effects-of-answer
                                              car-cons cdr-cons
                                              (:executable-counterpart equal)))))))

(local (defthm fn-bpn-nth-3-of-a-four-list
  (equal (fn-bpn-nth 3 (list a b c d)) d)))

(local (defthm transit-dispatch-record
  (let ((eff (car (fn-bpnf-answer-effects
                   (fn-bpnp-transit-dispatch-step st h peer node)))))
    (implies (equal (car eff) :persist-dispatch)
             (and (equal (fn-bpn-nth 3 eff)
                         (fn-bpnp-dispatch-record
                          (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                          (fn-bpn-nth 3 h) (fn-bpah-held-primary-identity h)
                          peer))
                  (equal (car (fn-bpnp-dispatch-apply
                               (fn-bpn-nth 3 eff) (fn-bpnf-held-list st)))
                         :ready))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                            '(fn-bpnp-transit-dispatch-step
                                              answer-effects-of-answer
                                              fn-bpn-nth-3-of-a-four-list
                                              car-cons cdr-cons
                                              (:executable-counterpart not)
                                              (:executable-counterpart equal)))))))

(local (defthm progress-dispatch-is-the-transit-step
  (let* ((waits (fn-bpnp-prune-waits (fn-bpnp-waits st) (fn-bpnf-held-list st)))
         (st2 (fn-bpnp-with-waits st waits))
         (h (fn-bpnp-oldest-eligible-with-credit
             (fn-bpnf-held-list st2) node obs routes generation waits
             (fn-bpnd-free (fn-bpnp-used st2) (fn-bpnp-debt st2)
                           *fn-bpnp-control-margin*)
             budget nil))
         (peer (fn-bpnp-route-peer (fn-bpn-nth 3 (fn-bpnp-primary h)) routes))
         (ans (fn-bpnp-progress-step st node obs routes generation budget)))
    (implies (equal (car (car (fn-bpnf-answer-effects ans))) :persist-dispatch)
             (and (member-equal h (fn-bpnf-held-list st))
                  peer
                  (fn-bpnp-routesp routes)
                  (equal ans (fn-bpnp-transit-dispatch-step st2 h peer node)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                            '(fn-bpnp-progress-step
                                              answer-effects-of-answer
                                              busy-stranded-effects-propose-no-dispatch
                                              deliver-step-proposes-no-dispatch
                                              oldest-eligible-with-credit-is-a-member
                                              with-waits-keeps-held-epoch-op
                                              car-cons cdr-cons
                                              (:executable-counterpart equal)
                                              (:executable-counterpart car)))))))

(local (defthm dispatch-apply-ready-is-unique
  (implies (equal (car (fn-bpnp-dispatch-apply record held)) :ready)
           (and (equal (fn-bpnf-arrival-count (fn-bpn-nth 3 record) held) 1)
                (equal (fn-bpn-nth 2 (fn-bpnp-dispatch-apply record held))
                       (fn-bpnp-dispatched-held
                        (fn-bpnf-find-arrival (fn-bpn-nth 3 record) held)
                        (fn-bpn-nth 5 record)))))
  :hints (("Goal" :in-theory (e/d (fn-bpnp-dispatch-apply)
                                  (fn-bpnf-arrival-count fn-bpnf-find-arrival
                                   fn-bpnp-dispatch-matches-heldp
                                   fn-bpnp-replace-dispatched
                                   fn-bpnp-dispatched-held))))))

(local (defthm route-list-of-table-form
  (not (fn-bpnp-route-listp (list :table table)))))

(local (defthm progress-dispatch-record
  (let* ((waits (fn-bpnp-prune-waits (fn-bpnp-waits st) (fn-bpnf-held-list st)))
         (st2 (fn-bpnp-with-waits st waits))
         (h (fn-bpnp-oldest-eligible-with-credit
             (fn-bpnf-held-list st2) node obs routes generation waits
             (fn-bpnd-free (fn-bpnp-used st2) (fn-bpnp-debt st2)
                           *fn-bpnp-control-margin*)
             budget nil))
         (peer (fn-bpnp-route-peer (fn-bpn-nth 3 (fn-bpnp-primary h)) routes))
         (ans (fn-bpnp-progress-step st node obs routes generation budget))
         (eff (car (fn-bpnf-answer-effects ans))))
    (implies (equal (car eff) :persist-dispatch)
             (and (member-equal h (fn-bpnf-held-list st))
                  peer
                  (fn-bpnp-routesp routes)
                  (equal (fn-bpn-nth 3 eff)
                         (fn-bpnp-dispatch-record
                          (fn-bpnf-epoch st2) (fn-bpnf-next-op st2)
                          (fn-bpn-nth 3 h) (fn-bpah-held-primary-identity h)
                          peer))
                  (equal (car (fn-bpnp-dispatch-apply
                               (fn-bpn-nth 3 eff) (fn-bpnf-held-list st)))
                         :ready))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                            '(with-waits-keeps-held-epoch-op))
           :use (progress-dispatch-is-the-transit-step
                 (:instance transit-dispatch-record
                  (st (fn-bpnp-with-waits st
                       (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                            (fn-bpnf-held-list st))))
                  (h (fn-bpnp-oldest-eligible-with-credit
                      (fn-bpnf-held-list (fn-bpnp-with-waits st
                       (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                            (fn-bpnf-held-list st))))
                      node obs routes generation
                      (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                           (fn-bpnf-held-list st))
                      (fn-bpnd-free
                       (fn-bpnp-used (fn-bpnp-with-waits st
                         (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                              (fn-bpnf-held-list st))))
                       (fn-bpnp-debt (fn-bpnp-with-waits st
                         (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                              (fn-bpnf-held-list st))))
                       *fn-bpnp-control-margin*)
                      budget nil))
                  (peer (fn-bpnp-route-peer
                         (fn-bpn-nth 3 (fn-bpnp-primary
                          (fn-bpnp-oldest-eligible-with-credit
                           (fn-bpnf-held-list (fn-bpnp-with-waits st
                            (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                                 (fn-bpnf-held-list st))))
                           node obs routes generation
                           (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                                (fn-bpnf-held-list st))
                           (fn-bpnd-free
                            (fn-bpnp-used (fn-bpnp-with-waits st
                              (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                                   (fn-bpnf-held-list st))))
                            (fn-bpnp-debt (fn-bpnp-with-waits st
                              (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                                   (fn-bpnf-held-list st))))
                            *fn-bpnp-control-margin*)
                           budget nil)))
                         routes))
                  (node node)))))))

; The record-level fact, over variables: a dispatch record for a unique
; member row names that row, and its peer is the table's routed hop.
(local (defthm dispatch-record-names-the-routed-hop
  (implies (and (equal record (fn-bpnp-dispatch-record e o (fn-bpn-nth 3 h) i peer))
                (equal (car (fn-bpnp-dispatch-apply record held)) :ready)
                (member-equal h held)
                (equal peer (fn-bpnp-route-peer (fn-bpn-nth 3 (fn-bpnp-primary h))
                                                (list :table table)))
                peer
                (fn-bprt-tablep table))
           (let ((choice (fn-bprt-outbound-choice
                          (fn-bpnp-held-dest
                           (fn-bpnf-find-arrival (fn-bpn-nth 3 record) held))
                          table)))
             (and (fn-bpp-eidp (fn-bpn-nth 5 record))
                  (equal (car choice) :hop)
                  (equal (fn-bpaj-eid-text (fn-bpn-nth 5 record))
                         (fn-bprt-nth 2 choice)))))
  :hints (("Goal" :in-theory (e/d (fn-bpnp-held-dest fn-bpnp-dispatch-record)
                                  (fn-bpnp-dispatch-apply fn-bpnf-arrival-count
                                   fn-bpnf-find-arrival fn-bprt-outbound-choice
                                   fn-bpaj-eid-text fn-bpp-eidp fn-bpnp-primary
                                   fn-bpnp-route-peer fn-bprt-tablep
                                   fn-bpnp-table-route-peer-is-the-routed-hop))
           :use ((:instance fn-bpnp-table-route-peer-is-the-routed-hop
                  (dest (fn-bpn-nth 3 (fn-bpnp-primary h))))
                 (:instance dispatch-apply-ready-is-unique))))))

; KEYSTONE.  Under the route table, the :progress event's dispatch names the
; routed hop: its kind-6 record applies (the row it names is unique), the
; record's peer, which the durable apply writes into that row's next-hop
; slot 11 (`fn-bpnp-dispatched-held'), is an EID, and it is the EID of the
; route `fn-bprt-outbound-choice' selects for the row's own destination
; among the boundaries with a contact (and that route is a live matching one:
; fn-bprt-next-hop-names-a-live-matching-route).  The host's call:
; host/native/bp-node.lisp `fnn-bpnode-dispatch-one', (:progress NODE OBS
; (:table TABLE) 0) through `fn-bpnj-step' (fn-bpnj-step-delegates-every-
; other-event) to `fn-bpnp-step' and this step.
(defthm fn-bpnp-progress-dispatch-names-the-routed-hop
  (let* ((ans (fn-bpnp-progress-step st node obs (list :table table)
                                     generation budget))
         (eff (car (fn-bpnf-answer-effects ans)))
         (record (fn-bpn-nth 3 eff))
         (row (fn-bpnf-find-arrival (fn-bpn-nth 3 record)
                                    (fn-bpnf-held-list st)))
         (choice (fn-bprt-outbound-choice (fn-bpnp-held-dest row) table)))
    (implies (equal (car eff) :persist-dispatch)
             (and (equal (car (fn-bpnp-dispatch-apply
                               record (fn-bpnf-held-list st)))
                         :ready)
                  (fn-bpp-eidp (fn-bpn-nth 5 record))
                  (equal (car choice) :hop)
                  (equal (fn-bpaj-eid-text (fn-bpn-nth 5 record))
                         (fn-bprt-nth 2 choice)))))
  :hints (("Goal"
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-bpnp-routesp fn-bpnp-table-routingp
                                        route-list-of-table-form
                                        car-cons cdr-cons len true-listp
                                        (:executable-counterpart len)
                                        (:executable-counterpart true-listp)
                                        (:executable-counterpart binary-+)
                                        (:executable-counterpart equal)))
           :use ((:instance progress-dispatch-record (routes (list :table table)))
                 (:instance dispatch-record-names-the-routed-hop
                  (record (fn-bpn-nth 3 (car (fn-bpnf-answer-effects
                           (fn-bpnp-progress-step st node obs (list :table table)
                                                  generation budget)))))
                  (held (fn-bpnf-held-list st))
                  (e (fn-bpnf-epoch (fn-bpnp-with-waits st
                       (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                            (fn-bpnf-held-list st)))))
                  (o (fn-bpnf-next-op (fn-bpnp-with-waits st
                       (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                            (fn-bpnf-held-list st)))))
                  (h (fn-bpnp-oldest-eligible-with-credit
                      (fn-bpnf-held-list (fn-bpnp-with-waits st
                       (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                            (fn-bpnf-held-list st))))
                      node obs (list :table table) generation
                      (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                           (fn-bpnf-held-list st))
                      (fn-bpnd-free
                       (fn-bpnp-used (fn-bpnp-with-waits st
                         (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                              (fn-bpnf-held-list st))))
                       (fn-bpnp-debt (fn-bpnp-with-waits st
                         (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                              (fn-bpnf-held-list st))))
                       *fn-bpnp-control-margin*)
                      budget nil))
                  (i (fn-bpah-held-primary-identity
                      (fn-bpnp-oldest-eligible-with-credit
                       (fn-bpnf-held-list (fn-bpnp-with-waits st
                        (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                             (fn-bpnf-held-list st))))
                       node obs (list :table table) generation
                       (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                            (fn-bpnf-held-list st))
                       (fn-bpnd-free
                        (fn-bpnp-used (fn-bpnp-with-waits st
                          (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                               (fn-bpnf-held-list st))))
                        (fn-bpnp-debt (fn-bpnp-with-waits st
                          (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                               (fn-bpnf-held-list st))))
                        *fn-bpnp-control-margin*)
                       budget nil)))
                  (peer (fn-bpnp-route-peer
                         (fn-bpn-nth 3 (fn-bpnp-primary
                          (fn-bpnp-oldest-eligible-with-credit
                           (fn-bpnf-held-list (fn-bpnp-with-waits st
                            (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                                 (fn-bpnf-held-list st))))
                           node obs (list :table table) generation
                           (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                                (fn-bpnf-held-list st))
                           (fn-bpnd-free
                            (fn-bpnp-used (fn-bpnp-with-waits st
                              (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                                   (fn-bpnf-held-list st))))
                            (fn-bpnp-debt (fn-bpnp-with-waits st
                              (fn-bpnp-prune-waits (fn-bpnp-waits st)
                                                   (fn-bpnf-held-list st))))
                            *fn-bpnp-control-margin*)
                           budget nil)))
                         (list :table table))))))))

; ---------------------------------------------------------------------------
; The host's two other questions.

; The :progress event's routes: the configuration's route table when it has
; one, else the single-peer instance (the node's PEER-ID routes only
; itself), which a node with no route rows keeps.
(defun fn-bpnp-host-routes (table peer)
  (declare (xargs :guard t))
  (if (and (consp table) (fn-bprt-tablep table))
      (list :table table)
    (fn-bpnp-single-peer-routes peer)))

; The report of held transit no route reaches: one (DESTINATION-TEXT
; DECISION) per destination whose forward-pending row has no :hop, oldest
; first.  A report only; the rows stay held with their obligations.
(defun fn-bpnp-forward-unrouted-rows (ordered table seen)
  (declare (xargs :guard t :measure (acl2-count ordered)))
  (if (atom ordered) nil
    (let* ((h (car ordered))
           (dest (fn-bpnp-held-dest h))
           (choice (fn-bprt-outbound-choice dest table)))
      (if (and (equal (fn-bpn-nth 12 h) '(:forward-pending))
               (null (fn-bpn-nth 14 h))
               (not (equal (fn-bprt-nth 0 choice) :hop))
               (not (member-equal dest (fix-true-list seen))))
          (cons (list dest (fn-bprt-nth 0 choice))
                (fn-bpnp-forward-unrouted-rows (cdr ordered) table
                                               (cons dest (fix-true-list seen))))
        (fn-bpnp-forward-unrouted-rows (cdr ordered) table seen)))))

(defun fn-bpnp-forward-unrouted (held table)
  (declare (xargs :guard (true-listp held)))
  (fn-bpnp-forward-unrouted-rows (reverse held) table nil))

(verify-guards fn-bpnp-forward-plan-rows)
(verify-guards fn-bpnp-forward-plan)
(verify-guards fn-bpnp-plan-peers)
(verify-guards fn-bpnp-host-routes)
(verify-guards fn-bpnp-forward-unrouted-rows)
(verify-guards fn-bpnp-forward-unrouted)
