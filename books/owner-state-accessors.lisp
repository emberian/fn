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

;; The owner's process record (books/owner-process.lisp), read from the owner
;; value.  Total: an owner that was never installed answers the initial record
;; (no live-reclaim opt-in, no capture yet), so a guard-t host reader needs no
;; premise about the global.
(defun fn-owner-proc (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner state)
      (fn-own-proc (fn-owner-core state))
    (fn-oproc-initial)))

;; The recovered owner OC with the PRIOR owner's process record: the install
;; of a recovery (host/owner-host.lisp fn-owner-recover-*, through
;; books/owner-recovery-retain.lisp fn-owner-install-extended) builds a fresh
;; owner whose record is the initial one; the serial the publication
;; identifies its captures by must stay monotone for the life of the process
;; and the operator's live-reclaim opt-in is a property of the run, so the
;; record the process already carries moves to the recovered owner.  With no
;; prior owner the fresh owner's record (the initial one) stands, and the
;; recovery's refusal (:fault) is passed through untouched.
(defun fn-owner-carry-proc (oc state)
  (declare (xargs :stobjs state :guard t))
  (if (and (boundp-global 'fn-owner state) (not (equal oc :fault)))
      (fn-ocfg-with-owner
       oc (fn-own-with-proc (fn-ocfg-owner oc) (fn-own-proc (fn-owner-core state))))
    oc))

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
