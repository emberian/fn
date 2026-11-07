; The measure's own probe kind (LEAN-METATHEORY §6): the step-language constructs no served kind
; takes on the recorded scenarios: (:park :pool C), a declared wait without a parker
; (:sealable), (:park :admission ID), (:do ... :when E :else (V)), a (:case ...) step, (:halt)
; and a handler's (:nowake). Not here, for want of a child-form word: a declared wait with a
; parker (the only one, :principal-reservation, parks through fn2-account-request-park, whose
; defcost names no :child) and (:park :taken K) (fn2-machine-park-taken-K is the assembly's,
; over fn2-core).
; A kind is declared below the assembly (reference's index section seals the machine
; declarations), so this book includes the owners' books that declare the wait kinds and leaves
; reference to the drivers, which include it after this book (print-probe.lsp, record-probe.lsp).
; machine-arms-unit's probe kinds (kind stops, :wake-row + :goto with an :issue, :repeat,
; accept-hand) come in with it. Test-only: nothing served includes this book.
(in-package "ACL2")
(include-book "../../books/accounts-core")
(include-book "../../books/machines-c-sealer-kind")
(include-book "../../tests/machine-arms-unit")

(defmachine fn2-meta-probe
 :phases (:free :pool :seal :admit :skip :casing :halting :done)
 :fields ((count :u32) (class :u32) (waiter :link) (cursor :u32) (stopped :bool))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*) (waiter *fn2-none*))
 :arms ((:free (:idle))
        (:pool (:set (count 1)) (:park :pool row-class :steps *fn2-work-small*))
        (:seal (:next :done) (:park :sealable))
        (:admit (:park :admission row-waiter))
        (:skip (:do (code) (fn2-arms-t-peek row-count) :accept (:found) :when (equal row-class 0) :else (:found)
                :case (((:end) (:next :done) (:charge :steps *fn2-work-small*))))
               (:set (count 0)) (:charge :steps *fn2-work-small*))
        (:casing (:case row-count ((0) (:set (count 1)) (:charge :steps *fn2-work-small*))
                   (:otherwise (:idle))))
        (:halting (:halt))
        (:done (:idle)))
 :observes ((:receive-result (:nowake))))
(defmachine-arms fn2-meta-probe :children)
