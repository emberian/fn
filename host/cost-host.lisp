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
