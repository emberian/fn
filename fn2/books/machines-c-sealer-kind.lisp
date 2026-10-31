; Layer C1c: the sealer machine kind (C-ENGINE-OWNER as built). Declared
; here, after machines-b's fn2-commit and before C's successor books, so its
; position in the machine registry is fixed before the engine's owner
; constant is taken from it (machines-c-successor.lisp). One row: :sealing
; drives the engine's seal step (books/sealer.lisp) through the core wrapper
; fn2-sealer-step and parks on the :sealable wait kind when nothing is
; sealable (genesis parks it there first); the grant service's fifth source wakes it (machines-a-access,
; C's attachment in machines-c-sealer.lisp). :stopped is terminal. The
; callbacks are fn2-sealer-core-events (machines-c-sealer.lisp),
; materialized in assembly-callbacks-c.lisp.
(in-package "ACL2")
;; A's kinds first, as in the assembly (assembly-index includes machines-all
;; before machines-b), so the position taken for the owner constant is the
;; one the index assigns.
(include-book "machines-all")
(include-book "machines-c")
(fn2-book-layer :c)

(defconst *fn2-sealer-tables*
 '(fn2-core-seals fn2-core-overlays fn2-core-overlay-index fn2-core-run-installed fn2-core-run-builds
   fn2-core-run-writers fn2-core-run-restarts fn2-core-run-cache fn2-core-ribbon-builds fn2-core-ribbon-band
   fn2-core-fields fn2-core-pool fn2-core-fc fn2-core-fc-context fn2-core-b3 fn2-core-digests))
(defcost fn2-sealer-step :bytes 4096
 :tables (fn2-core-seals fn2-core-overlays fn2-core-overlay-index fn2-core-run-installed fn2-core-run-builds
          fn2-core-run-writers fn2-core-run-restarts fn2-core-run-cache fn2-core-ribbon-builds fn2-core-ribbon-band
          fn2-core-fields fn2-core-pool fn2-core-fc fn2-core-fc-context fn2-core-b3 fn2-core-digests)
 :doc "One bounded seal step: at most 4,096 bytes of page or filter work, one entry added, or one install.")
(defcost fn2-sealer-refuse :tables (fn2-core-control)
 :doc "Stop the core by name: a seal step refused for want of a pool slot (:sealer-full), a cache row (:sealer-cache), or as an invariant (:sealer).")

(defmachine fn2-sealer
 :states (:sealing :stopped)
 ;; stopped: 1 once the row is :stopped. The budget's descriptor cap is the
 ;; other kinds' (4), though the sealer issues nothing: the run's charge
 ;; check (fn2-machine-charge) is proved over every kind's caps, and a kind
 ;; whose cap is below another's charge breaks A's callers' guard proofs,
 ;; which cannot show a row's kind is kept across an issue.
 :fields ((stopped :bool))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 1
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :continuations
 ((:sealing fn2-sealer-seal :cost (:bytes (:cost fn2-sealer-step :bytes) :steps *fn2-work-transition*)
   :writes (wait-reason stopped)
   :tables (fn2-core-seals fn2-core-overlays fn2-core-overlay-index fn2-core-run-installed fn2-core-run-builds
            fn2-core-run-writers fn2-core-run-restarts fn2-core-run-cache fn2-core-ribbon-builds fn2-core-ribbon-band
            fn2-core-fields fn2-core-pool fn2-core-fc fn2-core-fc-context fn2-core-b3 fn2-core-digests)
   :next (:sealing :stopped) :uses (fn2-sealer-step fn2-sealer-refuse))
  (:stopped fn2-sealer-idle :cost (:steps (:cost fn2-machine-idle :steps)) :writes () :next (:stopped)
   :uses (fn2-machine-idle))))
