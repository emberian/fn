; Additive BP exact-byte integrity seam. The abstract frame digest remains
; abstract: only a joint attachment relates its executable to this cursor.
; PREFIX and INVARIANT are proof-only vocabulary; no served path encodes a
; complete checkpoint or scans the capture to check them.
(in-package "ACL2")
(include-book "bp-node-checkpoint-emission")
(include-book "pagestore-digest-cursor-semantics")
(include-book "frame-digest-buffer")
(set-verify-guards-eagerness 0)

(defun fn-bpck-frame-prefix (job)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpcke-prefix job))

(local
 (defthm fn-bpck-b3-octets-are-cbor-octets
  (implies (fn-b3-octet-listp octets) (fn-cbor-octet-listp octets))
  :hints (("Goal" :induct (len octets)
   :in-theory (enable fn-b3-octet-listp
                      fn-cbor-octet-listp fn-cbor-octetp)))))

(defun fn-bpck-frame-digest-invariantp (job pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
  (and (equal (fn-bpn-nth 6 job) :digest-finish)
       (posp (fn-bpn-nth 8 job))
       (<= (fn-bpn-nth 8 job) *fn-bpc-max-uint*)
       (equal (fn-bpn-nth 10 job) (+ 14 (fn-bpn-nth 8 job)))
       (equal (pgs-dc-capture pgs-digest-state)
              (list :bp-checkpoint-stage (fn-bpn-nth 1 job) (fn-bpn-nth 3 job)))
       (equal (pgs-dc-lease pgs-digest-state) (fn-bpn-nth 1 job))
       (pgs-dcs-invariantp 63 (+ 14 (fn-bpn-nth 8 job))
                           (fn-bpck-frame-prefix job) pgs-digest-state)))

(encapsulate
 (((fn-bpck-frame-result * pgs-digest-state) => *))
 (local
  (defun fn-bpck-frame-result (job pgs-digest-state)
    (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
    (declare (ignore pgs-digest-state))
    (fn-frame-digest (fn-bpck-frame-prefix job))))
 (defthm fn-bpck-frame-result-is-exact-frame-digest
   (implies (and (fn-bpck-frame-digest-invariantp job pgs-digest-state)
                 (equal (pgs-dc-mode pgs-digest-state) :done))
            (equal (fn-bpck-frame-result job pgs-digest-state)
                   (fn-frame-digest (fn-bpck-frame-prefix job))))
   :hints (("Goal" :in-theory (enable fn-bpck-frame-digest-invariantp
                                     pgs-dcs-invariantp fn-frame-trailer
                                     fn-b3-octet-listp fn-cbor-octet-listp)))
   :rule-classes nil))

(defthm fn-bpck-frame-result-is-exact-frame-trailer
  (implies (and (fn-bpck-frame-digest-invariantp job pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :done))
           (equal (fn-bpck-frame-result job pgs-digest-state)
                  (fn-frame-trailer (fn-bpck-frame-prefix job))))
  :hints (("Goal" :use fn-bpck-frame-result-is-exact-frame-digest
                  :in-theory (e/d (fn-bpck-frame-digest-invariantp
                                   pgs-dcs-invariantp fn-frame-trailer)
                                  (fn-bpck-frame-prefix))))
  :rule-classes nil)

; The actual terminal implementation reads only the bounded digest state.
; Invalid phase returns NIL; it has no full-source fallback.
(defun fn-bpck-frame-result-impl (job pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t))
  (declare (ignore job))
  (if (equal (pgs-dc-mode pgs-digest-state) :done)
      (pgs-dcb-result-octets pgs-digest-state) nil))
(verify-guards fn-bpck-frame-result-impl)

(defthm fn-bpck-frame-result-impl-is-exact-blake3
  (implies (and (fn-bpck-frame-digest-invariantp job pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :done))
           (equal (fn-bpck-frame-result-impl job pgs-digest-state)
                  (fn-blake3-stobj (fn-bpck-frame-prefix job))))
  :hints (("Goal" :use ((:instance pgs-dcs-done-result-is-blake3
                                   (limit 63)
                                   (byte-total (+ 14 (fn-bpn-nth 8 job)))
                                   (msg (fn-bpck-frame-prefix job))))
           :in-theory (e/d (fn-bpck-frame-result-impl fn-bpck-frame-digest-invariantp
                                                    fn-blake3-stobj-is-blake3)
                           (fn-bpck-frame-prefix pgs-dcs-invariantp
                            pgs-dcb-result-octets fn-blake3 fn-blake3-stobj))))
  :rule-classes nil)

; Preserve every existing frame digest/buffer/range attachment as one group.
; This discharges the new constraint with the exact-byte terminal theorem;
; it adds no assumption that the abstract digest is BLAKE3 in the logic.
(defattach (fn-frame-digest fn-blake3-stobj)
           (fn-frame-digest-buffer fn-blake3-of-prefixed-buffer-any)
           (fn-frame-digest-range fn-blake3-of-prefixed-range-any)
           (fn-bpck-frame-result fn-bpck-frame-result-impl)
 :hints (("Goal" :use fn-bpck-frame-result-impl-is-exact-blake3
                   :in-theory (disable fn-bpck-frame-result-impl
                                       fn-bpck-frame-digest-invariantp
                                       fn-bpck-frame-prefix))))

(in-theory (disable fn-bpck-frame-result-impl))
