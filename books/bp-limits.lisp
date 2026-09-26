; fn: composition of the BP codec widths (PRF-134; D27, the codec half of P5).
;
; The ADU, bundle and held-image constants are codec widths: each is the
; ceiling every BP node profile field has (`fn-bpn-machine-limitp', 2^24), and
; the bounds a node applies are the profile's ADU octets, bundle octets and
; held octets (books/bp-node-profile, books/bp-node-profile-admission).  This
; book states how the widths nest.
;
; Before P5, `fn-bpn-limits-compose' stated the old finite machine: an ADU of
; 65,538 octets with 65,534 octets of header fitted one sender job image
; (`*fn-bpn-machine-max-job-octets*', the plain frame `:blob', 131,072).  That
; composition is what P5 removes, and it is false at the ADU's width: the
; sender machine's job image is still the plain `:blob' (PKT-294), so a
; sender cannot yet hold an ADU above about 64 KiB as one job.  The receiving
; side (kind 5, kind 18, reassembly, the ADU decoder) is at the widths below.
; The planned family stage slots, stage octets, and explicit header bound are
; not yet machine fields.  This book does not claim their composition.

(in-package "ACL2")

(include-book "bp-adu")
(include-book "bp-fragment")
(include-book "frame-octets")
(include-book "bp-node-machine-codec")
(include-book "bp-node-foundation")

(defthm fn-bpn-limits-compose-at-the-codec-widths
  (and
   ;; An ADU of the ADU width is one bundle's payload data.
   (<= *fn-bpa-max-octets* *fn-bpb-max-data*)
   ;; The held image width is the decoder's input width, and a lifecycle
   ;; record carries an image of that width with 3,072 octets of fields.
   (equal *fn-bpnf-max-held-image* *fn-bpb-max-input*)
   (<= (+ *fn-bpnf-max-held-image* 3072) *fn-bpn-lifecycle-max-payload*)
   ;; The capped reference reassembler is below the ADU width; the served
   ;; reassembler (fn-bpfw-reassemble) has no cap.
   (<= *fn-bpf-max-length* *fn-bpa-max-octets*)
   ;; Every width is the profile ceiling, 2^24.
   (fn-bpn-machine-limitp *fn-bpa-max-octets*)
   (fn-bpn-machine-limitp *fn-bpb-max-input*)
   (fn-bpn-machine-limitp *fn-bpnf-max-held-image*)
   (not (fn-bpn-machine-limitp (+ 1 *fn-bpnf-max-held-image*)))
   ;; The sender machine's job image, unchanged (PKT-294).
   (equal *fn-bpn-machine-max-job-octets* *fn-frame-max-blob*)
   (<= (+ *fn-bpn-machine-max-job-octets* 3072)
       *fn-bpn-lifecycle-max-payload*)
   (<= (* *fn-bpf-max-fragments*
          *fn-bpn-machine-max-job-octets*)
       *fn-bpn-machine-max-octets*))
  :rule-classes nil)
