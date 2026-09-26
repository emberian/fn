; Read-only fragment-family query over the finite BP foundation's held rows.
; A2/A3 will connect this query to a journalled replacement transition.
(in-package "ACL2")

(include-book "bp-node-foundation")
(include-book "bp-fragment-fast")
(include-book "bp-fragment-invariants")
(include-book "bp-fragment-sweep")
(set-verify-guards-eagerness 0)

(defun fn-bpnf-family-member (x xs)
  (declare (xargs :guard t))
  (mbe :logic (member-equal x xs)
       :exec (if (consp xs)
                 (if (equal x (car xs)) xs
                   (fn-bpnf-family-member x (cdr xs)))
               nil)))

; An ADU key alone is not sufficient: fragments with incompatible primary
; headers must not share a reassembly canvas.  The fragment flag itself is
; removed; all candidates here are fragments, so the remaining flags agree.
(defun fn-bpnf-fragment-coherence-key (primary)
  (declare (xargs :guard (fn-bpp-blockp primary) :verify-guards nil))
  (list (fn-bpp-total-adu-length primary)
        (fn-bpp-destination primary)
        (fn-bpp-report-to primary)
        (fn-bpp-lifetime primary)
        (fn-bpp-crc-type primary)
        (- (fn-bpp-flags primary) *fn-bpp-flag-fragment*)))

; The consumed marker is this query's convention until A2 has a durable
; family replacement event.  Deleted rows are already explicit in the A1
; held schema; a completed family will eventually remove its members.
(defun fn-bpnf-active-fragmentp (h)
  (declare (xargs :guard t))
  (and (fn-bpnf-heldp h)
       (fn-bpp-fragmentp
        (fn-bpp-flags (fn-bpb-bundle-primary (fn-bpnf-held-bundle h))))
       (not (nth 14 h))
       (not (equal (nth 12 h) :reassembly-consumed))))

(defun fn-bpnf-same-fragment-family-p (h anchor)
  (declare (xargs :guard t))
  (and (fn-bpnf-active-fragmentp h)
       (fn-bpnf-active-fragmentp anchor)
       (equal (fn-bpnf-held-principal h)
              (fn-bpnf-held-principal anchor))
       (equal (fn-bpp-adu-key
               (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
              (fn-bpp-adu-key
               (fn-bpb-bundle-primary (fn-bpnf-held-bundle anchor))))
       (equal (fn-bpnf-fragment-coherence-key
               (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
              (fn-bpnf-fragment-coherence-key
               (fn-bpb-bundle-primary (fn-bpnf-held-bundle anchor))))))

(defun fn-bpnf-active-set-rows (held anchor)
  (declare (xargs :guard t))
  (if (consp held)
      (if (fn-bpnf-same-fragment-family-p (car held) anchor)
          (cons (car held) (fn-bpnf-active-set-rows (cdr held) anchor))
        (fn-bpnf-active-set-rows (cdr held) anchor))
    nil))

; The anchor must be a current held row.  Thus an arbitrary caller-supplied
; header cannot make a phantom family out of rows with a matching key.
(defun fn-bpnf-active-set (st anchor)
  (declare (xargs :guard t))
  (if (and (fn-bpnf-active-fragmentp anchor)
           (fn-bpnf-family-member anchor (fn-bpnf-held-list st)))
      (fn-bpnf-active-set-rows (fn-bpnf-held-list st) anchor)
    nil))

(defun fn-bpnf-fragment-cells (held)
  (declare (xargs :guard t :verify-guards nil))
  (mbe
   :logic
   (if (consp held)
       (let* ((primary (fn-bpb-bundle-primary
                        (fn-bpnf-held-bundle (car held))))
              (payload (fn-bpb-payload (fn-bpnf-held-bundle (car held)))))
         (cons (fn-bpf-make (fn-bpp-fragment-offset primary)
                            payload (fn-bpp-total-adu-length primary))
               (fn-bpnf-fragment-cells (cdr held))))
     nil)
   :exec
   (if (consp held)
       ; The total field selectors are logically identical to the record
       ; projections above and avoid a duplicate record scan on this path.
       (let* ((bundle (fn-bpnf-held-bundle (car held)))
              (primary (fn-bpb-bundle-primary bundle))
              (payload (fn-bpb-block-data
                        (fn-bpb-bundle-payload bundle))))
         (cons (fn-bpf-make (fn-bpn-nth 9 primary)
                            payload (fn-bpn-nth 10 primary))
               (fn-bpnf-fragment-cells (cdr held))))
     nil)))

; This is the actual foundation-state query: the reassembler consumes the
; held bundles selected from the machine's own list, not a parallel family
; representation.  An invalid anchor is a bounded invalid result.  The
; reassembler is bp-fragment-sweep's: no family-size ceiling, work linear in
; the octets the family holds (PRF-121).
(defun fn-bpnf-fragment-query (st anchor)
  (declare (xargs :guard t))
  (if (not (and (fn-bpnf-active-fragmentp anchor)
                (fn-bpnf-family-member anchor (fn-bpnf-held-list st))))
      (list :invalid :bounds)
    (fn-bpfw-reassemble
     (fn-bpnf-fragment-cells (fn-bpnf-active-set st anchor))
     (fn-bpp-total-adu-length
      (fn-bpb-bundle-primary (fn-bpnf-held-bundle anchor))))))

; The source for reconstructing the whole primary and extension blocks is
; the offset-zero row, regardless of which selected row arrived first.
(defun fn-bpnf-offset-zero-source (held)
  (declare (xargs :guard t :verify-guards nil))
  (mbe
   :logic
   (if (consp held)
       (if (equal (fn-bpp-fragment-offset
                   (fn-bpb-bundle-primary
                    (fn-bpnf-held-bundle (car held))))
                  0)
           (car held)
         (fn-bpnf-offset-zero-source (cdr held)))
     nil)
   :exec
   (if (consp held)
       (if (equal (fn-bpn-nth
                   9 (fn-bpb-bundle-primary
                      (fn-bpnf-held-bundle (car held))))
                  0)
           (car held)
         (fn-bpnf-offset-zero-source (cdr held)))
     nil)))

(defthm fn-bpnf-active-set-rows-members-share-family
  (implies (member-equal h (fn-bpnf-active-set-rows held anchor))
           (fn-bpnf-same-fragment-family-p h anchor))
  :hints (("Goal" :induct (fn-bpnf-active-set-rows held anchor)
           :in-theory (disable fn-bpnf-same-fragment-family-p))))

(defthm fn-bpnf-active-set-members-share-family
  (implies (member-equal h (fn-bpnf-active-set st anchor))
           (fn-bpnf-same-fragment-family-p h anchor))
  :hints (("Goal" :use ((:instance fn-bpnf-active-set-rows-members-share-family
                                  (held (fn-bpnf-held-list st))))
           :in-theory (disable fn-bpnf-active-set-rows-members-share-family
                               fn-bpnf-active-set-rows
                               fn-bpnf-same-fragment-family-p))))

(defthm fn-bpnf-fragment-query-is-reference
  (equal (fn-bpnf-fragment-query st anchor)
         (if (not (and (fn-bpnf-active-fragmentp anchor)
                       (member-equal anchor (fn-bpnf-held-list st))))
             (list :invalid :bounds)
           (fn-bpfw-spec
            (fn-bpnf-fragment-cells (fn-bpnf-active-set st anchor))
            (fn-bpp-total-adu-length
             (fn-bpb-bundle-primary (fn-bpnf-held-bundle anchor))))))
  :hints (("Goal" :use ((:instance fn-bpfw-reassemble-is-spec
                                  (fs (fn-bpnf-fragment-cells
                                       (fn-bpnf-active-set st anchor)))
                                  (total (fn-bpp-total-adu-length
                                          (fn-bpb-bundle-primary
                                           (fn-bpnf-held-bundle anchor))))))
           :in-theory (e/d (fn-bpnf-fragment-query fn-bpnf-family-member)
                           (fn-bpfw-reassemble-is-spec
                            fn-bpfw-reassemble fn-bpfw-spec
                            fn-bpnf-active-fragmentp fn-bpnf-active-set
                            fn-bpnf-fragment-cells fn-bpnf-held-list
                            fn-bpp-total-adu-length fn-bpnf-held-bundle
                            fn-bpb-bundle-primary fn-bpf-fragment-listp)))))

(defthm fn-bpnf-offset-zero-source-is-a-member
  (implies (fn-bpnf-offset-zero-source held)
           (and (member-equal (fn-bpnf-offset-zero-source held) held)
                (equal (fn-bpp-fragment-offset
                        (fn-bpb-bundle-primary
                         (fn-bpnf-held-bundle
                          (fn-bpnf-offset-zero-source held))))
                       0)))
  :hints (("Goal" :induct (fn-bpnf-offset-zero-source held))))

; A covered index zero has to come from an offset-zero extent.  This is a
; list argument over the exact cells projected from held rows; no arrival
; order or header choice enters the premise.
(defthm fn-bpnf-covered-zero-has-source
  (implies (and (fn-bpfw-fragment-listp (fn-bpnf-fragment-cells rows))
                (fn-bpf-coveredp (fn-bpnf-fragment-cells rows) 0))
           (fn-bpnf-offset-zero-source rows))
  :hints (("Goal" :induct (fn-bpnf-fragment-cells rows)
           :in-theory (disable fn-bpb-bundlep fn-bpp-blockp
                               fn-cbor-octet-listp))))

(defthm fn-bpnf-reassemble-ok-covers-zero
  (implies (equal (fn-bpf-result-tag (fn-bpfw-spec fs total)) :ok)
           (and (fn-bpfw-fragment-listp fs)
                (fn-bpf-coveredp fs 0)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpfw-spec-ok-covers-zero))
           :in-theory (disable fn-bpfw-spec-ok-covers-zero
                               fn-bpfw-spec fn-bpf-canvas))))

(defthm fn-bpnf-reference-success-has-offset-zero-source
  (implies (equal (fn-bpf-result-tag
                   (fn-bpfw-spec (fn-bpnf-fragment-cells rows) total))
                  :ok)
           (fn-bpnf-offset-zero-source rows))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-reassemble-ok-covers-zero
                            (fs (fn-bpnf-fragment-cells rows)))
                 (:instance fn-bpnf-covered-zero-has-source))
           :in-theory (disable fn-bpnf-reassemble-ok-covers-zero
                               fn-bpnf-covered-zero-has-source
                               fn-bpnf-fragment-cells
                               fn-bpnf-offset-zero-source
                               fn-bpfw-spec))))

(defthm fn-bpnf-success-has-offset-zero-source
  (implies (equal (fn-bpf-result-tag (fn-bpnf-fragment-query st anchor)) :ok)
           (fn-bpnf-offset-zero-source (fn-bpnf-active-set st anchor)))
  :hints (("Goal" :do-not-induct t
           :cases ((and (fn-bpnf-active-fragmentp anchor)
                        (member-equal anchor (fn-bpnf-held-list st))))
           :use ((:instance fn-bpnf-reference-success-has-offset-zero-source
                            (rows (fn-bpnf-active-set st anchor))
                            (total (fn-bpp-total-adu-length
                                    (fn-bpb-bundle-primary
                                     (fn-bpnf-held-bundle anchor))))))
           :in-theory (disable
                       fn-bpnf-reference-success-has-offset-zero-source
                       fn-bpnf-active-fragmentp fn-bpnf-heldp
                       fn-bpnf-active-set fn-bpnf-fragment-cells
                       fn-bpnf-offset-zero-source fn-bpfw-reassemble
                       fn-bpfw-spec fn-bpf-canvas))))

; Receiving proposes publication; it does not change the selected family
; until the matching durable callback installs the held row.
(defthm fn-bpnf-receive-proposal-preserves-fragment-query
  (equal (fn-bpnf-fragment-query
          (fn-bpnf-answer-state
           (fn-bpnf-step st (list :receive-bundle bundle wire ingress)))
          anchor)
         (fn-bpnf-fragment-query st anchor))
  :hints (("Goal"
           :in-theory '(fn-bpnf-fragment-query fn-bpnf-active-set
                        fn-bpnf-receive-proposal-does-not-install-held))))
