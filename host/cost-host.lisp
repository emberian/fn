; Cost rows checked in the actual image world, after interface declarations.
; Partial means unknown, never an admission tariff or a completed allocation
; claim.  FN-READER-INSTALL-RESULT is itself unaccounted: its installer is
; too large/has unresolved dependencies for this derivation's inliner.
(in-package "ACL2")
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/payload-arena-attach")
(include-book "../books/def-cost")
(include-book "../books/string-line-cursor-cost")
(include-book "reader-host")
(include-book "interfaces")
(include-book "page-window-executor-host")
(include-book "../books/output-tariff-families")
(include-book "page-decoded-window-host")

(def-cost fn-reader-chunk
  :visits (+ 1 request-octets)
  :sizes ((request-octets (len octets)))
  :unaccounted (fn-served-step fn-reader-install-result)
  ;; len and the unaccounted leaves as naturals, which minimal-theory lacks:
  ;; the bound then holds whatever the derived route charges below it (with
  ;; host/interfaces.lisp unloaded the route derives :internal, 0).
  :hints (("Goal" :in-theory
           (union-theories '(fn-reader-chunk-visits fn-reader-chunk-route-visits
                             (:type-prescription len)
                             (:type-prescription fn-cost-unaccounted-natp))
                           (theory 'minimal-theory)))))
(def-cost-check fn-reader-chunk)

; Pin the actual route and unresolved dependency set.  This does not pretend
; to execute a defun-nx cost twin or the constrained unknown leaf costs.
(assert-event
 (let ((row (cdr (assoc-eq 'fn-reader-chunk (table-alist 'fn-cost (w state))))))
   (and (eq (fn-cost-get :route row) :served)
        (equal (fn-cost-get :route-cost row) '(binary-+ '1 (len octets)))
        (equal (fn-cost-get :unaccounted row) '(fn-served-step fn-reader-install-result)))))

; Real owner syncer entry: derive the same function the native actor calls.
; No supplied bound means no qualifying tariff; custody is already enforced
; for the charged worker projection while total entry work remains owed.
(def-cost create-fn-resource-ledger :unaccounted (make-list-ac))
(def-cost fn-ros-install-syncer :unaccounted (fn-ros-install))
(def-cost fn-ros-issue :unaccounted (fn-rl-wfp fn-rl-draw mv-nth))
(def-operation-check fn-ros-issue)
(def-cost fn-ros-physical
  :unaccounted (fn-ros-livep member-eq-exec fn-ros-settle-ready))
(def-cost fn-ros-outcome :unaccounted (fn-ros-livep fn-ros-settle-ready))
(def-cost fn-ros-drainedp :unaccounted (fn-rl-wfp))

; The output admission gate and the family tariffs' arithmetic (lanes
; tariff2, tariff3; planning/design/tariff-2026-10-04.md Q6): derived,
; nothing unaccounted, no host visit, and the logical conses a descriptor or
; a refusal word holds.  The generated producer fn-tariff-family-preview and
; its catalog/arena reads are not costed here; the program wrapper
; fn-owner-output-tariff-preview carries no row (a :program entry cannot).
(def-cost fn-ocap-at :visits 0 :conses 0)
(def-cost fn-ocap-admit-preview :visits 0 :conses 3)
(def-cost fn-tariff-article-octets :visits 0 :conses 0)
(def-cost fn-tariff-stat-octets :visits 0 :conses 0)
(def-cost fn-tariff-line-octets :visits 0 :conses 0)
(def-cost fn-tariff-group-reply-octets :visits 0 :conses 0)
(def-cost fn-tariff-descriptor :visits 0 :conses 3)

; The ratchet's backlog (lane cost-ratchet): every guard-verified dispatched
; entry carries a def-cost.  The two constants and the config's reclaim flag
; are bounded outright; the figure arithmetic and the owner page borrows are
; derived, nothing bounded, because their callees (the heap figures and the
; span borrows of books/page-window-span.lisp, books/decoded-window-span.lisp)
; have no row of their own and a bound over a name list would restate the body.
(def-cost fn-asto-quantum :visits 0 :conses 0)
(def-cost fn-heap-reclaim-chunk-rows :visits 0 :conses 0)
(def-cost fn-ncfg-nth :visits (+ 1 m) :sizes ((m (nfix n))))
(def-cost fn-native-config-reclaim-livep :visits 32)
(def-cost fn-mca-figure-octets :unaccounted (fn-mca-base-octets fn-heap-with-nursery))
(def-cost fn-rrv-extend-reservation
  :unaccounted (fn-rrv-extra-octets fn-heap-grow-runtime-dynamic fn-heap-machine-octets fn-crv-nth))
(def-cost fn-owner-page-window-span-at :unaccounted (fn-owner-page-read-ledger fn-pwr-span-at))
(def-cost fn-owner-page-window-cache-span-at :unaccounted (fn-owner-page-read-ledger fn-pwc-span-at))
(def-cost fn-owner-page-decoded-job-span-at :unaccounted (fn-owner-page-read-ledger fn-dwj-span-at))
(def-cost fn-owner-page-decoded-window-cache-span-at
  :unaccounted (fn-owner-page-read-ledger fn-pwz-cache-span-at))
; The BP serve loop's inbound admission (books/bp-session-scheduler), asked
; once per pass that finds a listener readable: two boolean steps, no size.
(def-cost fn-bpsched-admit-p :visits 0)

; Dispatched entries (FILL-COST-OBLIGATIONS-5): each cost DERIVED from its
; body in this world, partial over exactly the callees the derivation cannot
; cost (no bound is claimed; a bound is a theorem a later row adds).
; In the order they were admitted: a row's derivation counts the rows above it.
(def-cost fn-asto-resume-ms :unaccounted (fn-asto-preflight-planp fn-qplan-lst-cursorp))
(def-cost fn-bpnf-mixed-recovery-plan-from :unaccounted (fn-bpnf-namespace-plan fn-ag-append fn-bpn-lifecycle-namespace-plan-from fn-bpn-lifecycle-namespace-planp))
(def-cost fn-bpnr-plan-start-token :unaccounted (fn-bpnr-plan-checkpoint fn-bpnr-checkpointp fn-bpnr-checkpoint-next-token))
(def-cost fn-bpnr-seed-state :unaccounted (fn-bpnr-plan-checkpoint fn-bpnr-checkpointp fn-bpnf-base fn-bpnr-replay-base fn-bpn-machine-statep fn-bpnf-with-base))
(def-cost fn-cwq-new)
(def-cost fn-ews-span-effect :unaccounted (fn-ews-effect update-nth))
(def-cost fn-ews-tick-to-io :unaccounted (fn-ews-tick-run))
(def-cost fn-feed-journal-scan :unaccounted (fn-feed-journal-open-frame fn-feed-record-peer fn-frame-result-kind fn-frame-result-payload))
(def-cost fn-lim-decision-appliedp)
(def-cost fn-lim-funded-after)
(def-cost fn-lpf-reply-bound)
(def-cost fn-lpf-reply-read :unaccounted (fn-wg-decode fn-bs-profile-validp))
(def-cost fn-lpf-request-size-p)
(def-cost fn-native-control-profile-observes-p)
(def-cost fn-native-control-profile-source)
(def-cost fn-nco-at)
(def-cost fn-nco-client-follow :unaccounted (fn-nco-work-class fn-nctrl-reason-word))
(def-cost fn-nco-client-heldp :unaccounted (fn-nctrl-reason-word))
(def-cost fn-nco-client-observed-status :unaccounted (fn-nctrl-reason-word fn-nco-client-status))
(def-cost fn-nco-client-releasep :unaccounted (member-eq-exec))
(def-cost fn-nco-client-status :unaccounted (fn-nctrl-reason-word))
(def-cost fn-nco-client-waitp :unaccounted (fn-nctrl-reason-word))
(def-cost fn-nco-epoch-octets)
(def-cost fn-nco-initial)
(def-cost fn-nco-owner-step :unaccounted (fn-nco-work-class fn-nco-terminalp))
(def-cost fn-nco-pending-job)
(def-cost fn-nco-receipt-command)
(def-cost fn-nco-status-argv)
(def-cost fn-nco-wait-seconds)
(def-cost fn-nco-work-class)
(def-cost fn-och-caller-answer :unaccounted (member-eq-exec))
(def-cost fn-och-frames-event)
(def-cost fn-och-held-event)
(def-cost fn-oclc-live-authorizep :unaccounted (fn-oclc-configure mv-nth))
(def-cost fn-olau-authorize-observed :unaccounted (fn-cfg-decode-exact fn-olau-authorize-carried))
(def-cost fn-olau-next-name :unaccounted (fn-native-admin-config-name))
(def-cost fn-orp-convert-event)
(def-cost fn-otm-committer-may-start)
(def-cost fn-otm-held-caller-wake)
(def-cost fn-otm-held-committer-wake :unaccounted (fn-ocp-excluded-waits-p))
(def-cost fn-otm-hold-begin)
(def-cost fn-otm-hold-end)
(def-cost fn-owner-page-read-growth-convert :unaccounted (fn-owner-page-read-default-installedp fn-owner-page-read-ledger fn-prl-convert-growth mv-nth fn-owner-page-read-keep-ledger))
(def-cost fn-owner-page-read-growth-release :unaccounted (fn-owner-page-read-default-installedp fn-owner-page-read-ledger fn-prl-evict mv-nth fn-owner-page-read-keep-ledger))
(def-cost fn-owner-page-read-growth-reserve :unaccounted (fn-owner-page-read-default-installedp fn-owner-page-read-ledger fn-prl-reserve-growth mv-nth fn-owner-page-read-keep-ledger))
(def-cost fn-send-window-octets)
(def-cost fn-send-window-render-p)
(def-cost fn-cwq-arrive :unaccounted (fn-cwq-p))
(def-cost fn-cwq-drop :unaccounted (fn-cwq-p remove1-equal))
(def-cost fn-cwq-step :unaccounted (fn-cwq-pos fn-cwq-p remove1-equal))
(def-cost fn-cwq-waiting :unaccounted (fn-cwq-p))
(def-cost fn-ews-read-span :unaccounted (fn-ews-effect update-nth ceiling fn-ews-span-loop fn-ews-read))
(def-cost fn-lpf-reply :unaccounted (fn-bs-profile-validp fn-wg-encode))
(def-cost fn-lpf-request :unaccounted (fn-wg-encode))
(def-cost fn-lpf-request-p :unaccounted (fn-wg-decode))
(def-cost fn-nco-wire-step :unaccounted (fn-record-string-octets fn-nco-work-class fn-nco-terminalp fn-nco-token-text))
(def-cost fn-orp-step :unaccounted (fn-orp-refused-in-q2 fn-orp-replay-peers true-list-fix fn-orp-label))
(def-cost fn-otm-held-plan :unaccounted (fn-otm-held-event mv-nth fn-och-action-effects))
(def-cost fn-otm-hold-next :unaccounted (mv-nth fn-otm-next))
(def-cost fn-nco-owner-publication-word)
(def-cost fn-owner-cfg-capture)
(def-cost fn-owner-held-verdicts)
(def-cost fn-owner-sco-count :unaccounted (fn-sf-records-count))
