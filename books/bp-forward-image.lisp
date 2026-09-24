; The exact BPv7 image proposed for a received held forwarding attempt.
; Canonical block replacement happens in ACL2 at the attempt observation;
; native TCPCL receives only the resulting octets after kind 8 is durable.
(in-package "ACL2")
(include-book "bp-node-progress")
(set-verify-guards-eagerness 0)

(defun fn-bpnp-forward-anchor (h)
  (declare (xargs :guard t))
  (let ((tag (fn-bpn-nth 9 h)))
    (if (and (true-listp tag) (equal (len tag) 3)
             (equal (car tag) :observed-age)
             (fn-clock-timep (cadr tag))
             (fn-clock-timep (caddr tag)))
        (cons (cadr tag) (caddr tag))
      nil)))

(defun fn-bpnp-forward-one-block (block node anchor observation)
  (declare (xargs :guard t))
  (let ((type (fn-bpb-block-type block)))
    (cond
     ((equal type *fn-bpp-block-type-previous-node*)
      (list :ready
            (fn-bpb-previous-node-block
             (fn-bpb-block-number block) (fn-bpb-block-flags block)
             (fn-bpb-block-crc-type block) node)))
     ((equal type *fn-bpp-block-type-bundle-age*)
      (if (not (fn-clock-age-anchorp anchor))
          (list :fault :age-anchor)
        (let ((age (fn-clock-age-estimate anchor observation)))
          (if (not (fn-bpp-bundle-agep age))
              (list :fault :age-overflow)
            (list :ready
                  (fn-bpb-bundle-age-block
                   (fn-bpb-block-number block)
                   (fn-bpb-block-flags block)
                   (fn-bpb-block-crc-type block) age))))))
     ((equal type *fn-bpp-block-type-hop-count*)
      (let* ((hop (fn-bpp-data-hop-count (fn-bpb-block-data block)))
             (next (and (fn-bpp-hop-countp hop)
                        (fn-bpn-next-hop-count hop))))
        (if (not (and (fn-bpp-hop-countp next)
                      (not (fn-bpp-hop-limit-exceededp next))))
            (list :fault :hop-limit)
          (list :ready
                (fn-bpb-hop-count-block
                 (fn-bpb-block-number block) (fn-bpb-block-flags block)
                 (fn-bpb-block-crc-type block) next)))))
     (t (list :ready block)))))

(defun fn-bpnp-forward-blocks (blocks node anchor observation)
  (declare (xargs :guard t :measure (acl2-count blocks)))
  (if (atom blocks)
      (if (null blocks) (list :ready nil)
        (list :fault :blocks))
    (let ((one (fn-bpnp-forward-one-block
                (car blocks) node anchor observation)))
      (if (not (equal (car one) :ready)) one
        (let ((rest (fn-bpnp-forward-blocks
                     (cdr blocks) node anchor observation)))
          (if (not (equal (car rest) :ready)) rest
            (list :ready (cons (cadr one) (cadr rest)))))))))

(defun fn-bpnp-forward-image (h node observation)
  (declare (xargs :guard t))
  (let* ((bundle (fn-bpnf-held-bundle h))
         (anchor (fn-bpnp-forward-anchor h)))
    (if (not (and (fn-bpb-bundlep bundle)
                  (fn-bpp-previous-nodep node)
                  (fn-clock-observationp observation)
                  (equal (fn-bpnp-held-expiry h observation) :live)))
        (list :fault :forward-eligibility)
      (let ((blocks
             (fn-bpnp-forward-blocks
              (fn-bpb-bundle-blocks bundle) node anchor observation)))
        (if (not (equal (car blocks) :ready)) blocks
          (let ((forwarded
                 (fn-bpb-make-bundle
                  (fn-bpb-bundle-primary bundle) (cadr blocks)
                  (fn-bpb-bundle-payload bundle))))
            (if (not (fn-bpb-bundlep forwarded))
                (list :fault :forward-bundle)
              (let ((wire (fn-bpb-encode forwarded)))
                (if (and (fn-cbor-octet-listp wire)
                         (<= (len wire) *fn-bpb-max-input*))
                    (list :ready wire forwarded)
                  (list :fault :forward-image))))))))))
