; Retained source cursor for the real event directory and frontier pages.
; Physical page I/O is delegated to the shared owned-buffer worker.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)
(defcolumns fn2-event-build
 ((phase (:enum fn2-event-build-phase
    (:idle :auth-zero :auth-open :auth :auth-ready :claim-zero :claims :reserve :zero :entries :directory-header :frontier-header
           :peaks :physical-header :page :bound :done :uncertain)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (candidate :u32) (cut-commit :u60) (cut-event :u60)
  (slot :u32) (gen :u60) (scratch :u32) (scratch-gen :u60)
  (read-slot :u32) (read-gen :u60)
  (role :u8) (ordinal :u60) (pages :u60) (first :u60) (end :u60) (entry :u60)
  (claimed :u60) (zero :u32) (peak :u8) (payload :u32)
  (extent :u32) (epoch :u60) (allocation :u60) (child :u32) (has-child :bool)
  (directory-completed :u60) (frontier-completed :u60)
  ; Physical identity captured from the owner-bound configured origin.
  (history :u60) (history-incarnation :u60)))
