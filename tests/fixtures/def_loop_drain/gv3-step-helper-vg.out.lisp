(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-bpn-ready-peers (jobs)
  :shape :foldr :over jobs :elt j
  :combine (if (and (equal (fn-bpn-job-status j) :queued)
                    (not (fn-bpn-member (fn-bpn-job-peer j) acc)))
               (cons (fn-bpn-job-peer j) acc)
               acc)
  :init nil
  :rev fn-ag-rev-onto)

