; Visits derived from the executed shared launch composition, no declared bound.
(in-package "ACL2")
(include-book "image-world")
(include-book "memory-entry-cost")
(include-book "../host/cost-host")
(include-book "def-cost")
(include-book "heap-command")
(include-book "peer-flight-startup")
; Callee rows precede their compositions, in the same final world.
(def-cost fn-mo-serve-pool-threads :unaccounted (true-list-fix))
(def-cost fn-bpsp-node-capacity
  :unaccounted (fn-bpsp-node-wire-span fn-bpnpf-held-octets fn-bpnpf-rows fn-bpnpf-adu-octets
                fn-bpsp-capacity-octets))
(def-cost fn-mo-serve-pools :unaccounted (fn-crv-pool-budget fn-prstartup-launch-extra true-list-fix))

(def-cost fn-mo-serve-decide
  :unaccounted (fn-mo-serve-limit fn-mo-serve-dynamic fn-mo-serve-cfg fn-mm-least-observation
                fn-mm-reopen-need fn-heap-profile-word))

(def-cost fn-mo-serve-bp-store-need
 :unaccounted (fn-mo-serve-run-limit fn-mm-launch-dynamic fn-crv-pool-budget
               fn-prstartup-launch-extra true-list-fix))
(def-cost fn-mo-serve-run-decide
 :unaccounted (fn-mo-serve-total-pools fn-mo-serve-limit fn-mo-serve-dynamic fn-mo-serve-cfg
               fn-mm-least-observation fn-mm-reopen-need fn-heap-profile-word true-list-fix))
(def-cost fn-prstartup-run-default-plan
 :unaccounted (fn-prstartup-default-plan-with-peer fn-mo-serve-bp-need fn-mo-serve-run-limit
 fn-pfr-policy-p fn-prstartup-plan fn-prstartup-serve-protected fn-pfr-at
 fn-prstartup-launch-extra fn-prstartup-read-reserve fn-prstartup-read-extent))
(def-cost fn-prstartup-run-peer-native-grant
 :unaccounted (fn-prstartup-peer-native-grant fn-mo-serve-bp-need fn-mo-serve-run-limit
 fn-prstartup-peer-protected fn-prstartup-planp fn-pfr-startup-grant fn-mm-least-observation
 fn-pfr-at))
(def-cost fn-prstartup-run-store-need
 :unaccounted (fn-prstartup-serve-protected fn-mo-serve-run-limit))
