; host/spike-storage-host.lisp -- spike/storage (D28): ACL2 :program wrappers
; for the storage-at-scale spike.  Every function here is a SPIKE deferral:
; it is :program code, not a certified book, and each block names the proof
; or ACL2 owner a dev re-implementation owes.  Record:
; planning/evidence/spike-storage-2026-09-25.md.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; A. The owner opens from the open the store already made.
;
;; SPIKE: defers the theorem that the stashed state equals what
;; fn-owner-recover computes: both are fn-cpo-open-observed over the same
;; config records, frontier and history under the store lock (full path), or
;; fn-sco-open of the checkpoint (P3 keystone
;; fn-sn-recover-from-checkpoint-equals-full-recover).

(defun fn-spk-stash-opened (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-spk-opened
                             (cons (f-get-global 'fn-store-sn state)
                                   (f-get-global 'fn-store-cfg state))
                             state)))
    (value :stashed)))

(defun fn-spk-clear-opened (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-spk-opened nil state)))
    (value :cleared)))

(defun fn-spk-owner-recover-opened (max-conns state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((stash (and (boundp-global 'fn-spk-opened state)
                     (f-get-global 'fn-spk-opened state)))
         (s (car stash))
         (cfg (cdr stash)))
    (if (or (not (consp stash)) (null s) (not (natp max-conns))
            (not (equal (fn-sf-phase (fn-sn-files s)) :recovering)))
        (value :fault)
      (let* ((state (fn-owner-install-ocfg
                     (fn-ocfg-make
                      (fn-own-configure (fn-own-start s max-conns)
                                        (fn-owner-post-config cfg))
                      cfg nil nil)
                     state))
             (state (f-put-global 'fn-owner-feed-intents nil state))
             (state (f-put-global 'fn-owner-store-profile nil state))
             (state (f-put-global 'fn-owner-feed-inputs
                                  (fn-fc-table-initial-state) state))
             (state (f-put-global 'fn-spk-opened nil state)))
        (value :recovering)))))

