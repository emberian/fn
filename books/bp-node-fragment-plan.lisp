; A bounded, read-only family replacement proposal over the one FNBS held list.
; The later kind-18 publication is the only event allowed to install this
; whole bundle or retire the source rows.  No Store dispatch follows :ready.
(in-package "ACL2")
(include-book "bp-node-fragment-family")

(defun fn-bpnf-family-consumed-ids (rows)
  (declare (xargs :guard t :measure (acl2-count rows)))
  (if (consp rows)
      (cons (list (fn-bpnf-held-principal (car rows))
                  (fn-bpnf-held-id (car rows))
                  (fn-bpn-nth 3 (car rows)))
            (fn-bpnf-family-consumed-ids (cdr rows)))
    nil))

(defun fn-bpnf-family-whole-bundle (zero bytes)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-bpnf-heldp zero)
                (fn-cbor-octet-listp bytes)
                (consp bytes)
                (fn-bpp-fragmentp
                 (fn-bpp-flags
                  (fn-bpb-bundle-primary (fn-bpnf-held-bundle zero))))))
      nil
    (let* ((source (fn-bpnf-held-bundle zero))
           (payload (fn-bpb-bundle-payload source)))
      (fn-bpb-make-bundle
       (fn-bpf-unfragment-block (fn-bpb-bundle-primary source))
       (fn-bpb-bundle-blocks source)
       (fn-bpb-make-block
        (fn-bpb-block-type payload) (fn-bpb-block-number payload)
        (fn-bpb-block-flags payload) (fn-bpb-block-crc-type payload)
        bytes)))))

(defun fn-bpnf-family-plan (st anchor)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
  (let* ((rows (fn-bpnf-active-set st anchor))
         (query (fn-bpnf-fragment-query st anchor)))
    (if (not (equal (car query) :ok))
        query
      (let* ((zero (fn-bpnf-offset-zero-source rows))
             (whole (fn-bpnf-family-whole-bundle zero (cadr query))))
        (if (not (and zero (fn-bpb-bundlep whole)))
            (list :invalid :whole)
          (let* ((wire (fn-bpb-encode whole))
                 (held (fn-bpnf-held-list st))
                 (new-slots (+ (- (len held) (len rows)) 1))
                 (new-octets (+ (- (fn-bpnf-held-octets held)
                                   (fn-bpnf-held-octets rows))
                                (len wire))))
            (if (or (not (fn-cbor-octet-listp wire))
                    (> (len wire) *fn-bpnf-max-held-image*)
                    (< new-slots 0)
                    (< new-octets 0)
                    (> new-slots (fn-bpn-machine-state-max-jobs
                                  (fn-bpnf-base st)))
                    (> new-octets (fn-bpn-machine-state-max-octets
                                   (fn-bpnf-base st))))
                (list :capacity)
              (list :ready whole wire
                    (fn-bpnf-family-consumed-ids rows) zero))))))))

;; The plan returns the query unchanged when its tag is not :ok, so the
;; theorem needs only that a query never carries the :ready tag.  Stating that
;; keeps the reassembly reference closed in the main proof.
(local
 (defthm fn-bpnf-reassemble-is-not-ready
   (not (equal (car (fn-bpf-reassemble fs total)) :ready))
   :hints (("Goal" :in-theory (e/d (fn-bpf-reassemble)
                                   (fn-bpf-inputsp fn-bpf-canvas
                                    fn-bpf-first-index))))))

(local
 (defthm fn-bpnf-fragment-query-is-not-ready
   (not (equal (car (fn-bpnf-fragment-query st anchor)) :ready))
   :hints (("Goal" :in-theory (disable fn-bpf-reassemble
                                       fn-bpnf-active-fragmentp
                                       fn-bpnf-active-set
                                       fn-bpnf-fragment-cells
                                       fn-bpnf-held-list
                                       fn-bpp-total-adu-length
                                       fn-bpnf-held-bundle)))))

(defthm fn-bpnf-family-ready-has-valid-whole
  (implies (equal (car (fn-bpnf-family-plan st anchor)) :ready)
           (and (fn-bpb-bundlep (cadr (fn-bpnf-family-plan st anchor)))
                (fn-cbor-octet-listp (caddr (fn-bpnf-family-plan st anchor)))
                (<= (len (caddr (fn-bpnf-family-plan st anchor)))
                    *fn-bpnf-max-held-image*)
                (equal (car (fn-bpnf-fragment-query st anchor)) :ok)
                (fn-bpnf-offset-zero-source
                 (fn-bpnf-active-set st anchor))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpnf-active-set fn-bpnf-fragment-query
                               fn-bpnf-fragment-query-is-reference
                               fn-bpnf-offset-zero-source
                               fn-bpnf-family-whole-bundle
                               fn-bpnf-family-consumed-ids
                               fn-bpnf-held-list
                               fn-bpb-bundlep fn-bpb-encode
                               fn-bpnf-held-octets)))
  :rule-classes nil)
