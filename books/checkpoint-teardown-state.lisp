; Candidate-scoped volatile retention: evidence is copied before the one
; publication in-flight slot can be reused. No row grants retirement or FREE.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-teardown-debt
 ((phase (:enum fn2-checkpoint-teardown-debt-phase (:empty :copying :held :waiting :drop :uncertain)))
  (generation :u60) (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (checkpoint :u60) (history :u60) (incarnation :u60)
  (cut-commit :u60) (cut-event :u60) (installation-commit :u60) (installation-event :u60)
  (word-cursor :u8) (anchor-mask :u8)
  (cold-copy :bool) (cold-slot :u8) (cold-pos :u8) (cold-new :bool)
  ; Disposal is a separate retained continuation; accepted retirement tuple
  ; fields below remain immutable until their actual DROP finishes.
  (dispose-phase (:enum fn2-checkpoint-dispose-phase (:idle :sources :roots :refs :bytes :finish :cold)))
  (dispose-cursor :u32)
  (cold-token :u60) (cold-owner-kind :u8) (cold-owner-slot :u32) (cold-owner-gen :u60)
  (extent :u32) (epoch :u60) (allocation :u60) (batch :u60) (event :u60))
 :init-name fn2-checkpoint-teardown-debt-columns-init
 :extra-fields
 ((fn2-checkpoint-teardown-debt-last-generation :type (unsigned-byte 60) :initially 0
   :why "Nonwrapping retained-debt lifetime identity, minted only for a new actual evidence-copy subject; candidate reuse never recycles it.")
  (fn2-checkpoint-teardown-debt-words :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t
   :why "Five exact eight-word physical/semantic installation evidence identities per configured candidate, copied from actual completed bank evidence.")
  (fn2-checkpoint-teardown-debt-count :type (unsigned-byte 32) :initially 0
   :why "Number of immutable retained candidate debts; no scan is needed by the wait predicate.")
  (fn2-checkpoint-teardown-debt-notified :type (unsigned-byte 1) :initially 0
   :why "Actual completed transfer requests a complete bounded sweep; this is notification, never eligibility.")
  (fn2-checkpoint-teardown-debt-observed :type (array (unsigned-byte 60) (32)) :initially 0
   :why "Exact exclusion fingerprint: binding phase/mask plus six protocol roles times state/candidate/checkpoint/history/incarnation; no hash or wrapping counter.")
  (fn2-checkpoint-teardown-debt-anchors :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t
   :why "Four distinct physical-slot anchor hashes per candidate. Duplicate semantic checkpoint copies do not overwrite the slot-bound hash of another physical obligation.")))

(defun fn2-checkpoint-teardown-debt-init (rows fn2-checkpoint-teardown-debt)
 (declare (xargs :stobjs fn2-checkpoint-teardown-debt :verify-guards nil
  :guard (and (unsigned-byte-p 32 rows) (fn2-checkpoint-teardown-debt-wfp fn2-checkpoint-teardown-debt))))
 (let* ((fn2-checkpoint-teardown-debt (fn2-checkpoint-teardown-debt-columns-init rows fn2-checkpoint-teardown-debt))
        (fn2-checkpoint-teardown-debt (resize-fn2-checkpoint-teardown-debt-words (* 40 rows) fn2-checkpoint-teardown-debt))
        (fn2-checkpoint-teardown-debt (resize-fn2-checkpoint-teardown-debt-anchors (* 32 rows) fn2-checkpoint-teardown-debt)))
  fn2-checkpoint-teardown-debt))
(defun fn2-checkpoint-teardown-debt-heldp (c fn2-checkpoint-teardown-debt)
 (declare (xargs :stobjs fn2-checkpoint-teardown-debt :guard (fn2-checkpoint-teardown-debt-wfp fn2-checkpoint-teardown-debt)))
 (and (natp c) (< c (fn2-checkpoint-teardown-debt-rows fn2-checkpoint-teardown-debt))
      (not (equal (fn2-checkpoint-teardown-debt-phase c fn2-checkpoint-teardown-debt) *fn2-checkpoint-teardown-debt-phase-empty*))))
