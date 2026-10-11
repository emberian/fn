; Teeth for books/heap-command-entry-scratch (Builder M, memory landing 4b):
; KEYSTONE fn-mo-observed-log-holds-every-entry-read over
; tests/acl2/store-log-stream-tests's segment (three workload records chained
; from genesis, zero padded to 8,192 octets; store-log-entry-bound-tests).
;   WITNESS: empty header and suffix totals, the segment's own extent
;     observed: the first entry the open reads is within the observation's LOG.
;   BREAKS: an observation whose extent is no natural is NIL (the offline
;     adapter's case), and a
;     segment longer than the observed extent yields an entry past LOG.
;   MUTATION: the records' LOG alone, without the extent, does not hold the
;     first entry of a store whose totals carry no LOG.
(in-package "ACL2")
(include-book "store-log-entry-bound-tests")
(include-book "../../books/heap-command-entry-scratch")

(defun hcest-tot0 ()
  (declare (xargs :guard t))
  (fn-mm-make-tot 0 0 0 0 0 0 0 0 :resident))
(defun hcest-h () (declare (xargs :guard t :verify-guards nil)) (fn-bs-take 10 (sleb-seg)))
(defun hcest-st () (declare (xargs :guard t :verify-guards nil)) (fn-lgw-start *fn-lg-genesis* 1))

(assert-event (fn-mm-tot-p (hcest-tot0)))
(assert-event (natp (fn-lgw-entry-len-bounded (hcest-h) (hcest-st) (sleb-extent) (slw-max))))
(assert-event (< 0 (fn-lgw-entry-len-bounded (hcest-h) (hcest-st) (sleb-extent) (slw-max))))

(defteeth fn-mo-observed-log-holds-every-entry-read
  :claim (((observed (fn-mo-observed-totals hdr suffix extent))
           (within (<= (nfix segment-extent) extent)))
          (<= (nfix (fn-lgw-entry-len-bounded h st segment-extent max))
              (fn-mm-tot-log (fn-mo-observed-totals hdr suffix extent))))
  :subject fn-mo-observed-totals
  :witness ((hdr (hcest-tot0)) (suffix (hcest-tot0)) (extent (sleb-extent))
            (segment-extent (sleb-extent)) (h (hcest-h)) (st (hcest-st)) (max (slw-max)))
  :breaks ((observed ((hdr (hcest-tot0)) (suffix (hcest-tot0)) (extent 16385/2)
                      (segment-extent (sleb-extent)) (h (hcest-h)) (st (hcest-st)) (max (slw-max))))
           (within ((hdr (hcest-tot0)) (suffix (hcest-tot0)) (extent 1)
                    (segment-extent (sleb-extent)) (h (hcest-h)) (st (hcest-st)) (max (slw-max)))))
  :mutations ((entry-charged-by-the-records-log
               (:conclusion (<= (nfix (fn-lgw-entry-len-bounded h st segment-extent max))
                                (fn-mm-tot-log (fn-mm-observed-tot hdr suffix))))
               ((hdr (hcest-tot0)) (suffix (hcest-tot0)) (extent (sleb-extent))
                (segment-extent (sleb-extent)) (h (hcest-h)) (st (hcest-st)) (max (slw-max)))
               :fault "the read's entry scratch charged by the records' LOG alone: a damaged segment's entry is read past it")))
