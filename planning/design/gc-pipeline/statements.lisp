; PHASE-1 DRAFT: proof scripts omitted. Do not include this file in witnesses.
; These are composition contracts over current host-called entries (and
; their named concrete refinements), not certified claims about native I/O.
; contracts.lisp spells out EVERY hypothesis and conclusion. TRACE.md names
; the remaining invariant/renderer/effect bridges and the append-behind work.
(in-package "ACL2")
(include-book "contracts")

; All four dependency prefixes (reader, feed resolution, log, reply) consist
; byte-for-byte of records below the durable record frontier. Renderer
; refinement must establish that all record-derived observations use them.
(defthm fn-ocp-gc-reveals-are-durable
  (implies (fn-ocp-gc-linkedp h m ks s event phase word)
           (fn-ocp-gc-reveals-okp h ks (fn-ocp-gc-cuts m s event phase word)))
  :rule-classes nil)

; Both batches' outcomes, including refusals dependent on attempted writes,
; become uncertain; arbitrary later acknowledgement attempts cannot cross D.
(defthm fn-ocp-gc-failure-fences-both-batches
  (implies (fn-ocp-gc-failure-hyp s ks a b)
           (fn-ocp-gc-failure-okp s ks a b n))
  :rule-classes nil)

; Exact ordered suffix membership and BOTH profile bounds. This needs the
; proposed encoded-octet preflight: it is false of unqualified current TAKE.
(defthm fn-olr-gc-membership-and-profile-bounds
  (implies (fn-olr-gc-membership-hyp h ks record txid count octets bmax omax unit)
           (fn-olr-gc-membership-okp h ks record txid count octets bmax omax unit))
  :rule-classes nil)
