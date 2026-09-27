; Atomic logical publication of a durable configuration into the served owner.
; The physical record has already passed the host's immutable publication
; barrier.  This function is administrative, never a per-command served path.
(in-package "ACL2")
;
; Split 2026-09-27 (lane owner-books-split; D26: every book certifies under
; 10 s at two jobs) into three chained parts along its structure, in this order.
; Statements and names are the ones this book always had; each part replays
; the local prelude of the first.  This book includes the parts and keeps the
; export theory, so every includer is unchanged.
(include-book "config-owner-live-complete")
(include-book "config-owner-live-open")
(include-book "config-owner-live-read")


(deftheory fn-ocl-vocabulary
  '(fn-ocl-owner-with-store fn-ocl-store-config fn-ocl-complete fn-ocl-conn-historyp
    fn-ocl-conns-historyp fn-ocl-view-historyp fn-ocl-config-historyp
    fn-ocl-view-configp fn-ocl-relation))
(in-theory (disable fn-ocl-vocabulary))

; These large read-composition facts are applied explicitly by the historical
; reader proof.  Leaving them as global rewrite rules makes unrelated TLS and
; pin proofs expand a second read path while simplifying their own one.
(deftheory fn-ocl-read-proof-lemmas
  '(fn-ocl-replace-preserves-conns-pinned
    fn-ocl-find-survives-connection-replacement
    fn-ocl-replace-preserves-pins-point-to-conns
    fn-ocl-own-read-survivor-is-replacement
    fn-ocl-own-read-nonsurvivor-is-removal
    fn-ocl-own-read-keeps-store
    fn-ocl-own-read-preserves-owner-shape
    fn-ocl-own-read-keeps-owner-control
    fn-ocl-own-read-does-not-increase-connections
    fn-ocl-related-found-connection-has-history
    fn-ocl-own-read-survivor-had-original
    fn-ocl-config-shape-reconstructs
    fn-ocl-related-config-shaped
    fn-ocl-missing-read-keeps-configured-owner
    fn-ocl-own-read-survivor-has-history
    fn-ocl-relation-under-same-control-and-valid-connections
    fn-ocl-relation-read-input-facts
    fn-ocl-read-preserves-capacity-bound))
(in-theory (disable fn-ocl-read-proof-lemmas))
