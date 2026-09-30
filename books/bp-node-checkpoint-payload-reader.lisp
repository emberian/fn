; Internal cold-reopen payload turn. Integrity/workspace authority must be
; established by the registered caller before entry; this function grants none.
; Input is one bounded read, not a complete checkpoint or trailer slice.
(in-package "ACL2")
(include-book "bp-node-checkpoint-reader")
(include-book "bp-node-checkpoint-job")
(set-verify-guards-eagerness 2)

(defun fn-bpfr-payload-run (decoder payload-count input quantum)
 (declare (xargs :guard (and (fn-cbor-octet-listp input) (natp quantum))
  :guard-hints (("Goal" :in-theory (disable fn-bpcr-run)))))
 (let ((offset (fn-bpn-nth 10 decoder)))
  (if (not (and (posp payload-count) (<= payload-count *fn-bpc-max-uint*)
                (natp offset) (<= offset payload-count)
                (fn-bpck-small-octet-listp input 64)
                (<= (len input) (- payload-count offset))))
   (list :refused decoder input 0 0)
   (let* ((answer (fn-bpcr-run decoder input quantum))
          (next (fn-bpn-nth 0 answer))
          (status (fn-bpn-nth 1 next))
          (next-offset (fn-bpn-nth 10 next)))
    (list
     (cond ((equal status :refused) :refused)
           ((equal status :done)
            (if (and (equal next-offset payload-count)
                     (null (fn-bpn-nth 1 answer))) :decoded :refused))
           (t :yield))
     next (fn-bpn-nth 1 answer) (fn-bpn-nth 2 answer)
     (fn-bpn-nth 3 answer))))))

; The actual wrapper bounds both byte consumption and all decoder/reversal
; constructor actions, including refusals before the underlying runner.
(defthm fn-bpfr-payload-run-bounds-work
 (implies (natp quantum)
  (let ((answer (fn-bpfr-payload-run decoder payload-count input quantum)))
   (and (natp (fn-bpn-nth 3 answer)) (natp (fn-bpn-nth 4 answer))
        (<= (fn-bpn-nth 4 answer) (fn-bpn-nth 3 answer))
        (<= (fn-bpn-nth 3 answer) quantum))))
 :hints (("Goal" :use ((:instance fn-bpcr-run-bounds-read-and-constructor-turns
                          (job decoder)))
  :in-theory (e/d (fn-bpfr-payload-run) (fn-bpcr-run))))
 :rule-classes nil)
