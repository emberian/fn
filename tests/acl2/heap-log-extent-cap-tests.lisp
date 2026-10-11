; Teeth for books/heap-log-extent-cap (Builder A, the read's extent cap):
; KEYSTONE fn-lxc-admitted-segment-entries-within-the-decided-log over
; tests/acl2/store-log-stream-tests's segment (three workload records chained
; from genesis, zero padded to 8,192 octets; heap-command-entry-scratch-tests).
;   WITNESS: empty header and suffix totals observed at the segment's own
;     extent, that extent the cap: the first entry the stream and the damage
;     probe read is within the observation's LOG.
;   BREAKS: no cap (:uncapped, the caller's own heap) gives no observation;
;     a segment longer than the cap is refused, and its first entry is past
;     the LOG a decision at that cap holds.
;   MUTATION: a decision over a smaller extent than the cap does not hold
;     the segment's first entry.
; KEYSTONE fn-lxc-cap-of-the-probes-extent: the probe's extent read back is
; the extent (WITNESS 8192); BREAKS: a non-natural renders as 0; MUTATION: a
; digit past the word read with it is another figure.
(in-package "ACL2")
(include-book "heap-command-entry-scratch-tests")
(include-book "../../books/heap-log-extent-cap")

(defun lxct-ps () (declare (xargs :guard t :verify-guards nil)) (fn-lgdm-start (hcest-st)))

; The words and the round trip, executed.
(assert-event (equal (fn-lxc-words :reads (hcest-tot0) '(1 2 3) 0 4096 8192) " extent=8192"))
(assert-event (equal (fn-lxc-words :reads nil '(1 2 3) 0 4096 8192) ""))
(assert-event (equal (fn-lxc-words :header (hcest-tot0) '(1 2 3) 0 4096 8192) ""))
(assert-event (equal (fn-lxc-cap-of-text (fn-decimal-text 8192)) 8192))
(assert-event (equal (fn-lxc-cap-of-text nil) :uncapped))
(assert-event (equal (fn-lxc-cap-of-text "") :unreadable))
(assert-event (equal (fn-lxc-cap-of-text "81x2") :unreadable))
(assert-event (equal (fn-lxc-verdict 8192 8192) :read))
(assert-event (equal (fn-lxc-verdict 8193 8192) :refused))
(assert-event (equal (fn-lxc-verdict 8193 :uncapped) :read))
(assert-event (equal (fn-lxc-refusal-text "000002.log" 8193 8192)
                     "log segment 000002.log is 8193 octets, past the extent 8192 the heap probe decided this read's memory over (log-segment-past-decided-extent)"))

(defteeth fn-lxc-admitted-segment-entries-within-the-decided-log
  :claim (((observed (fn-mo-observed-totals hdr suffix cap))
           (admitted (equal (fn-lxc-verdict size cap) :read)))
          (and (<= (nfix (fn-lgw-entry-len-bounded h st size max))
                   (fn-mm-tot-log (fn-mo-observed-totals hdr suffix cap)))
               (<= (nfix (fn-lgdm-entry-len-bounded h ps size max))
                   (fn-mm-tot-log (fn-mo-observed-totals hdr suffix cap)))))
  :subject fn-lxc-verdict
  :witness ((hdr (hcest-tot0)) (suffix (hcest-tot0)) (cap (sleb-extent)) (size (sleb-extent))
            (h (hcest-h)) (st (hcest-st)) (ps (lxct-ps)) (max (slw-max)))
  :breaks ((observed ((hdr (hcest-tot0)) (suffix (hcest-tot0)) (cap :uncapped) (size (sleb-extent))
                      (h (hcest-h)) (st (hcest-st)) (ps (lxct-ps)) (max (slw-max))))
           (admitted ((hdr (hcest-tot0)) (suffix (hcest-tot0)) (cap 1) (size (sleb-extent))
                      (h (hcest-h)) (st (hcest-st)) (ps (lxct-ps)) (max (slw-max)))))
  :mutations ((decided-below-the-cap
               (:conclusion (<= (nfix (fn-lgw-entry-len-bounded h st size max))
                                (fn-mm-tot-log (fn-mo-observed-totals hdr suffix 1))))
               ((hdr (hcest-tot0)) (suffix (hcest-tot0)) (cap (sleb-extent)) (size (sleb-extent))
                (h (hcest-h)) (st (hcest-st)) (ps (lxct-ps)) (max (slw-max)))
               :fault "the cap past the extent the heap was decided over: an admitted segment's entry is read past the decision's LOG")))

(defteeth fn-lxc-cap-of-the-probes-extent
  :claim (((nat (natp extent)))
          (equal (fn-lxc-cap-of-text (fn-decimal-text extent)) extent))
  :subject fn-lxc-cap-of-text
  :witness ((extent 8192))
  :breaks ((nat ((extent -1))))
  :mutations ((a-digit-past-the-word
               (:conclusion (equal (fn-lxc-cap-of-text (concatenate 'string (fn-decimal-text extent) "0"))
                                   extent))
               ((extent 8192))
               :fault "the launcher's cap read past the probe's extent word")))
