; The forwarding image is an ACL2-authored byte image of one admitted held row.
(in-package "ACL2")
(include-book "../../books/bp-forward-image")

(defconst *bpnfi-local* (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47)))
(defconst *bpnfi-peer* (cons :dtn '(47 47 98 112 45 112 101 101 114 47)))
(defconst *bpnfi-config*
  (fn-bpn-config *bpnfi-local* 3600000 2 32 1048576))
(defconst *bpnfi-arrival* (fn-clock-observation 1000 0 0 nil))
(defconst *bpnfi-forward* (fn-clock-observation 1005 0 0 nil))
(defconst *bpnfi-bundle*
  (let ((sent (fn-bpn-send-bundle *bpnfi-config* *bpnfi-peer*
                                  '(1 2 3 4) 1 *bpnfi-arrival*)))
    (fn-bpb-make-bundle
     (fn-bpb-bundle-primary sent)
     (append (fn-bpb-bundle-blocks sent)
             (list (fn-bpb-previous-node-block 4 0 2 *bpnfi-peer*)))
     (fn-bpb-bundle-payload sent))))
(defconst *bpnfi-held*
  (fn-bpnf-held nil (fn-bpb-bundle-id *bpnfi-bundle*) 0 nil nil nil
                *bpnfi-bundle* (fn-bpb-encode *bpnfi-bundle*)
                '(:observed-age 0 1000) nil nil nil nil nil nil))
(defconst *bpnfi-image*
  (fn-bpnp-forward-image *bpnfi-held* *bpnfi-local* *bpnfi-forward*))

(assert-event (equal (car *bpnfi-image*) :ready))
(assert-event (fn-bpb-bundlep (caddr *bpnfi-image*)))
(assert-event (equal (fn-bpb-bundle-age (caddr *bpnfi-image*)) 5))
(assert-event
 (equal (fn-bpb-bundle-hop-count (caddr *bpnfi-image*))
        (fn-bpp-make-hop-count 32 1)))
(assert-event
 (equal (fn-bpb-bundle-previous-node (caddr *bpnfi-image*))
        *bpnfi-local*))
(assert-event
 (equal (cadr *bpnfi-image*) (fn-bpb-encode (caddr *bpnfi-image*))))
(assert-event
 (equal (fn-bpb-bundle-primary (caddr *bpnfi-image*))
        (fn-bpb-bundle-primary *bpnfi-bundle*)))
(assert-event
 (equal (fn-bpb-bundle-payload (caddr *bpnfi-image*))
        (fn-bpb-bundle-payload *bpnfi-bundle*)))
(assert-event
 (equal (car (fn-bpnp-forward-image
              (update-nth 9 nil *bpnfi-held*)
              *bpnfi-local* *bpnfi-forward*))
        :fault))
