; Visits derived from the executed shared launch composition, no declared bound.
(in-package "ACL2")
(include-book "def-cost")
(include-book "heap-command")
(include-book "peer-flight-startup")
(def-cost fn-mo-serve-bp-store-need
 :unaccounted (fn-mo-serve-run-limit fn-mm-launch-dynamic fn-mo-serve-pools))
(def-cost fn-mo-serve-run-decide
 :unaccounted (fn-mo-serve-total-pools fn-mo-serve-decide fn-mo-serve-pool-threads))
(def-cost fn-prstartup-run-default-plan
 :unaccounted (fn-prstartup-default-plan-with-peer fn-mo-serve-bp-need fn-mo-serve-run-limit
 fn-pfr-policy-p fn-orv-policy-p fn-prstartup-plan fn-prstartup-serve-protected fn-pfr-at
 fn-prstartup-launch-extra fn-prstartup-read-reserve fn-prstartup-read-extent))
(def-cost fn-prstartup-run-peer-native-grant
 :unaccounted (fn-prstartup-peer-native-grant fn-mo-serve-bp-need fn-mo-serve-run-limit
 fn-prstartup-peer-protected fn-prstartup-planp fn-pfr-startup-grant fn-mm-least-observation
 fn-pfr-at))
(def-cost fn-prstartup-run-store-need
 :unaccounted (fn-prstartup-serve-protected fn-mo-serve-run-limit))
