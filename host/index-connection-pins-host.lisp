; Actual source selection is ACL2-owned. The registered holder, not the
; current working publication, supplies an existing connection's source.
(in-package "ACL2")
(include-book "../books/index-connection-issuer")

; Pool/STATE participate in the composed owner admission ABI, but this readonly
; projection does not inspect a different live source or synthesize authority.
; The producer/transition invariant must associate the registered holder with
; this same owner/connection and resource pool. No such proof follows from
; equal scalar coordinates or from this adapter's guard.
(defun fn-owner-index-reader-source
  (id holder-token fuel fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool state) :guard (natp fuel))
          (ignore fn-page-read-pool state))
 (mv-let (word pin left) (fn-mio-connection-source id holder-token fuel fn-mio$c)
  (cond ((not (eq word :current)) (mv word nil nil left))
        ((not (and (fn-omk-widthp pin 3)
                   (eq (fn-omk-at 0 pin) :publication-pin)
                   (fn-ibp-generation-tokenp (fn-omk-at 1 pin))
                   (fn-ipub-shapep (fn-omk-at 2 pin))))
         (mv :recovery-required nil nil left))
        (t (mv :current pin (fn-omk-at 2 pin) left)))))

; For fn-owner-open only: mirrors its actual fn-owner-at-reader-view selector.
; A batch capture's D
; must have its corresponding retained registry pin. Missing D is unavailable,
; never permission to read the working/current publication instead.
(defun fn-owner-index-connection-capture (token fuel fn-mio$c state)
 (declare (xargs :stobjs (fn-mio$c state) :guard (natp fuel)))
 (let ((kind (if (and (f-boundp-global 'fn-owner-reader-views state)
                      (consp (f-get-global 'fn-owner-reader-views state)))
                 :d :current)))
  (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
   (status pin left fn-index-backing)
   (fn-icr-capture token kind fuel fn-index-backing)
   (mv status pin left fn-mio$c))))

; Exposure and peer opens currently execute on the working owner directly;
; unlike fn-owner-open, they do not call fn-owner-at-reader-view. Their
; capture must therefore select current even while a D batch pin exists.
(defun fn-owner-index-working-connection-capture (token fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (status pin left fn-index-backing)
  (fn-icr-capture token :current fuel fn-index-backing)
  (mv status pin left fn-mio$c)))
