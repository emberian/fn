; Fixed-arity lifetime callbacks for a funded native custody record.
; These adapters allocate no native record and establish no runtime authority.
; STATE is threaded unchanged; the same MIO provider and pool carry effects.
(in-package "ACL2")
(include-book "../books/index-connection-repin")

; Definite pre-open/repin refusal only. :released is the sole permission to
; discard the pending holder token. Unknown intent remains recovery-required.
(defun fn-owner-index-connection-abort
 (token fuel fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool state) :guard t))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word left fn-index-backing fn-page-read-pool)
  (fn-icr-abort token (nfix fuel) fn-index-backing fn-page-read-pool)
  (mv nil word left fn-mio$c fn-page-read-pool state)))

; A closing holder may still own aliases. :held keeps its token and charge;
; socket/logical close and native worker return cannot substitute for release.
(defun fn-owner-index-connection-settle
 (token fuel fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool state) :guard t))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word left fn-index-backing fn-page-read-pool)
  (fn-icr-settle token (nfix fuel) fn-index-backing fn-page-read-pool)
  (mv nil word left fn-mio$c fn-page-read-pool state)))

; INTERNAL continuation of the actual accepted RC/view-change result, not an
; independent native operation accepting an assertion of acceptance. The
; composed reader preflights before that result and retains both tokens on
; uncertainty. :repinned-held keeps OLD-TOKEN as charged retirement custody.
(defun fn-owner-index-connection-repin-accept
 (id old-token new-token fuel fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool state) :guard t))
 (mv-let (word left fn-mio$c fn-page-read-pool)
  (fn-mio-connection-repin-accept id old-token new-token (nfix fuel)
                                  fn-mio$c fn-page-read-pool)
  (mv nil word left fn-mio$c fn-page-read-pool state)))
