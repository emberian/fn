; Executed source model over SAME actual local stobjs. The installed receiver
; capacity/anchor and parsed RC are explicit synthetic seeds, not factory or
; serialized STATE authority. Wrapper guards are deliberately unverified.
; No intermediate committed receipt, response phase or actor is injected.
(in-package "ACL2")
(include-book "../../books/index-connection-issuer")

(include-book "../../books/served-step")
(defun fn-icr-test-setup (children fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard t))
 (let* ((fn-page-read-pool
          (fn-owner-page-read-keep-ledger
           (fn-prl-build '(1000 1000 5 5 99) '(0 0 0 0 0) 0 '(:legacy) '(100 0 0 0 0))
           fn-page-read-pool))
        (fn-index-backing (update-fn-ibp-pool-capacity 1 fn-index-backing)))
  (if (not children) (mv fn-index-backing fn-page-read-pool)
   (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
    (fn-ibp-node)
    (stobj-let ((fn-ibp-generation-segment
                (fn-ibp-node-children-get 'fn-ibp-generation-segment fn-ibp-node
                                         (create-fn-ibp-generation-segment))))
     (fn-ibp-generation-segment)
     (let ((fn-ibp-generation-segment (update-fn-ibp-gs-id 1 fn-ibp-generation-segment)))
      (mv-let (a fn-ibp-generation-segment)
       (fn-ibp-generation-begin '(:index-generation 9 1 0) :gen-grant fn-ibp-generation-segment)
       (declare (ignore a))
       (mv-let (b fn-ibp-generation-segment)
        (fn-ibp-generation-capture-arena '(:index-generation 9 1 0) 7 22 fn-ibp-generation-segment)
        (declare (ignore b))
        (mv-let (c fn-ibp-generation-segment)
         (fn-ibp-generation-install-publication '(:index-generation 9 1 0)
          (fn-ipub-make 9 :key nil 0 3 2 nil 0 1 nil 0 2 nil 3 :complete :selected-view 7 22)
          fn-ibp-generation-segment)
         (declare (ignore c)) fn-ibp-generation-segment))))
     (stobj-let ((fn-ibp-connection-segment
                 (fn-ibp-node-children-get 'fn-ibp-connection-segment fn-ibp-node
                                          (create-fn-ibp-connection-segment))))
      (fn-ibp-connection-segment)
      (update-fn-ich-segment-id 1 fn-ibp-connection-segment)
      fn-ibp-node))
    (let ((fn-index-backing
           (update-fn-ibp-current
            (list :installed-publication '(:index-generation 9 1 0)
             (fn-ipub-make 9 :key nil 0 3 2 nil 0 1 nil 0 2 nil 3 :complete :selected-view 7 22))
            fn-index-backing)))
     (mv fn-index-backing fn-page-read-pool))))))
(defun fn-rxtl-seed-provider (fn-rx-provider)
 (declare (xargs :stobjs fn-rx-provider :guard t))
 (stobj-let ((fn-rx-carry (fn-rxp-carry fn-rx-provider)))
  (fn-rx-carry)
  (let* ((fn-rx-carry (update-fn-rxc-token '(:rx-capacity 0 0 4096) fn-rx-carry))
         (fn-rx-carry (update-fn-rxc-instance 0 fn-rx-carry)))
   (update-fn-rxc-capacity 4096 fn-rx-carry)) fn-rx-provider))
(defun fn-rxtl-fixture-copy (fn-rx-provider)
 (declare (xargs :stobjs fn-rx-provider :guard t))
 (stobj-let ((fn-octets-rx (fn-rxp-octets fn-rx-provider)))
  (fn-octets-rx) (fn-octets-rx-from-list '(1 2 3 4 5 6) fn-octets-rx) fn-rx-provider))

