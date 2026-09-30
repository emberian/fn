; Explicitly unfunded logical storage fixture; no allocator permission.
(in-package "ACL2")
(include-book "../../books/bp-checkpoint-close-registered")
(defconst *bpclose-token* '(:bp-job 7 (:bp-controller 2 0) 0 5))
(defconst *bpclose-job*
 (fn-bpck-stage-observation
  (fn-bpck-begin *bpclose-token* 0 5 (fn-bpnr-depth-budget 8)
                 nil nil 8 0 1048576) :ambiguous))
(defconst *bpclose-payload*
 (fn-bpck-control-make *bpclose-job* '(:close :uncertain) :unfunded-binding nil))
(defconst *bpclose-prepared* (fn-bpck-close-prepare *bpclose-payload* 5))
(assert-event
 (let* ((payload (fn-bpn-nth 1 *bpclose-prepared*))
        (ok (fn-bpck-close-observe payload *bpclose-token* 6 :ok))
        (unknown (fn-bpck-close-observe payload *bpclose-token* 6 :unknown))
        (stale (fn-bpck-close-observe payload *bpclose-token* 5 :ok)))
  (and (fn-bpcc-job-tokenp *bpclose-token*)
       (equal (fn-bpn-nth 0 *bpclose-prepared*) :action-prepared)
       (equal (fn-bpn-nth 2 *bpclose-prepared*)
              (list :bp-checkpoint-io-action *bpclose-token* 6 :close 0 nil))
       (equal (fn-bpn-nth 0 ok) :close-observed)
       (equal (fn-bpck-control-job (fn-bpn-nth 1 ok)) *bpclose-job*)
       (equal (fn-bpck-control-io (fn-bpn-nth 1 ok)) '(:done :uncertain))
       (equal (fn-bpn-nth 0 unknown) :close-uncertain)
       (equal (fn-bpck-control-job (fn-bpn-nth 1 unknown)) *bpclose-job*)
       (equal (fn-bpck-control-io (fn-bpn-nth 1 unknown)) '(:fenced :uncertain))
       (equal (fn-bpn-nth 0 stale) :stale-checkpoint-observation)
       (equal (fn-bpn-nth 1 stale) payload)
       (equal (fn-bpck-cleanup-word *bpclose-job* :returned :relinquished
                                   :closed :transferred) :uncertain))))
