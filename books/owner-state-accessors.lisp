; Exact owner state accessors shared by host transitions and their proofs.
; Definitions moved unchanged from host/owner-host.lisp. No state effects,
; new decision, or invariant revalidation is introduced.
(in-package "ACL2")
(include-book "owner-config")

(defun fn-owner-ocfg (state)
  ; Internal, single-valued accessor for host wrappers.
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
  (f-get-global 'fn-owner state))

(defun fn-owner-core (state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
  (fn-ocfg-owner (f-get-global 'fn-owner state)))

(defun fn-owner-store (state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
  (fn-own-store (fn-owner-core state)))

; Definitional aliases, not cited keystones. They preserve the projection
; rewriting the host guard proofs used before these definitions moved.
(defthm fn-owner-core-is-configured-owner-by-definition
  (equal (fn-owner-core state) (fn-ocfg-owner (fn-owner-ocfg state)))
  :hints (("Goal" :in-theory (enable fn-owner-core fn-owner-ocfg))))

(defthm fn-owner-store-is-configured-store-by-definition
  (equal (fn-owner-store state)
         (fn-own-store (fn-ocfg-owner (fn-owner-ocfg state))))
  :hints (("Goal" :in-theory (enable fn-owner-store))))

(in-theory (disable fn-owner-ocfg fn-owner-core fn-owner-store))

;; The owner's publication globals (moved unchanged from host/owner-host.lisp
;; so host/web-host.lisp, which includes only this book, certifies).
(defun fn-owner-sco-global (name state)
  (declare (xargs :stobjs state :guard (symbolp name)))
  (if (boundp-global name state) (f-get-global name state) nil))

; The publication the owner deferred by name, (:deferred REASON ESTIMATE
; BUDGET) as fn-ock-publication-stream answered it, or nil; the status
; report carries it (host/native-live-status-host.lisp).
(defun fn-owner-sco-deferred (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-owner-sco-global 'fn-owner-sco-deferred state))
