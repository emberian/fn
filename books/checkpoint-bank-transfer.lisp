; The only discharge of a displaced physical cold-anchor obligation. Existing
; candidate ownership must already contain every common and slot-specific word.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-teardown-cold-evidence")
(fn2-book-layer :b)
(defun fn2-checkpoint-bank-obligations-transfer (physicalslot fn2-checkpoint-teardown-debt fn2-checkpoint-publication)
 (declare (xargs :stobjs (fn2-checkpoint-teardown-debt fn2-checkpoint-publication)
 :guard (and (fn2-checkpoint-teardown-debt-wfp fn2-checkpoint-teardown-debt) (fn2-checkpoint-publication-wfp fn2-checkpoint-publication))))
 (b* (((unless (fn2-checkpoint-teardown-cold-retainedp physicalslot fn2-checkpoint-teardown-debt fn2-checkpoint-publication))
       (mv :retained fn2-checkpoint-publication))
      (bit (fn2-checkpoint-bank-obligation-bit physicalslot))
      (fn2-checkpoint-publication (fn2-checkpoint-publication-put 0
       (cold-pending-mask (logand (fn2-checkpoint-publication-cold-pending-mask 0 fn2-checkpoint-publication) (logxor 15 bit)))
       (cold-retired-mask (logior (fn2-checkpoint-publication-cold-retired-mask 0 fn2-checkpoint-publication) bit)))))
  (mv :transferred fn2-checkpoint-publication)))
(fn2-checkpoint-publication-preserves fn2-checkpoint-bank-obligations-transfer
 (physicalslot fn2-checkpoint-teardown-debt fn2-checkpoint-publication)
 :hyps ((fn2-checkpoint-teardown-debtp fn2-checkpoint-teardown-debt) (fn2-checkpoint-teardown-debt-wfp fn2-checkpoint-teardown-debt)
        (fn2-checkpoint-publicationp fn2-checkpoint-publication) (fn2-checkpoint-publication-wfp fn2-checkpoint-publication)) :position 1)
(defcost fn2-checkpoint-teardown-cold-ack-op :child fn2-checkpoint-bank-obligations-transfer :answers t
 :tables (fn2-core-checkpoint-teardown-debt fn2-core-checkpoint-publication)
 :doc "Discharge one overwritten physical anchor only after exact48-word evidence is retained by actual candidate debt; no physical edge is dropped.")
(defcost fn2-checkpoint-teardown-cold-next-op :child fn2-checkpoint-bank-obligations-pending-next :answers t
 :tables (fn2-core-checkpoint-publication)
 :doc "Inspect one of the four actual displaced physical anchor obligations; no caller selects a victim candidate.")
