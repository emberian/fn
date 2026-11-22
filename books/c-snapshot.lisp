; The resident cut shared by C and retained journal readers. Already
; admitted publication and materialization drain before the cut is held.
(in-package "ACL2")
(include-book "c-snapshot-state")
(include-book "declare")
(fn2-book-layer :c)

(defun fn2-csnapshot-current-phase (fn2-csnapshot)
 (declare (xargs :stobjs fn2-csnapshot :guard (fn2-csnapshot-wfp fn2-csnapshot)))
 (if (< 0 (fn2-csnapshot-rows fn2-csnapshot))
     (fn2-csnapshot-phase 0 fn2-csnapshot)
   *fn2-csnapshot-phase-idle*))

(defcost fn2-csnapshot-state :tables (fn2-core-csnapshot)
 :doc "Read resident snapshot exclusion state.")
(defcost fn2-csnapshot-begin :answers (:ok :busy :bounds :exhausted :stopped) :tables (fn2-core-csnapshot fn2-core-extents)
 :doc "Close new C staging while admitted work drains.")
(defcost fn2-csnapshot-poll :answers (:owner :bounds :more :held :stopped)
 :tables (fn2-core-csnapshot fn2-core-succ-txns fn2-core-commit-root fn2-core-seals fn2-core-extents)
 :doc "Inspect one draining transaction, then retain the actual settled commit/event cut.")
(defcost fn2-csnapshot-release :answers (:owner :frozen :ok :stopped) :tables (fn2-core-csnapshot fn2-core-extents)
 :doc "Release an exact owner/token resident cut; ambiguous persistence must retain it.")

(defmacro fn2-csnapshot-op (name args position body)
 `(progn
   (defun ,name (,@args fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    ,body)
   (fn2-core-preserves ,name (,@args fn2-core) :position ,position :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))))

; Core operations are materialized with C's successor wrappers, after the
; assembled core and C's transaction phase constants exist.
(defmacro fn2-csnapshot-core-events ()
 '(progn
 (defun fn2-csnapshot-state (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core))) (phase)
   (fn2-csnapshot-current-phase fn2-csnapshot) phase))

 (fn2-csnapshot-op fn2-csnapshot-begin (okind oslot ogen) 2
  (if (fn2-core-stopped-p fn2-core) (mv :stopped 0 fn2-core)
  (stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core))
              (fn2-extents (fn2-core-extents fn2-core)))
   (code token fn2-csnapshot fn2-extents)
   (b* (((unless (and (< 0 (fn2-csnapshot-rows fn2-csnapshot))
                      (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
         (mv :bounds 0 fn2-csnapshot fn2-extents))
        ((unless (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-idle*))
         (mv :busy 0 fn2-csnapshot fn2-extents))
        (token (+ 1 (fn2-csnapshot-token 0 fn2-csnapshot)))
        ((unless (unsigned-byte-p 60 token)) (mv :exhausted 0 fn2-csnapshot fn2-extents))
        ((mv code fn2-extents) (fn2-alloc-snapshot-prepare token okind oslot ogen fn2-extents))
        ((unless (eq code :ok)) (mv code 0 fn2-csnapshot fn2-extents))
        (fn2-csnapshot (fn2-csnapshot-put 0 (phase *fn2-csnapshot-phase-closing*)
         (token token) (owner-kind okind) (owner-slot oslot) (owner-gen ogen)
         (scan 0) (blocked 0) (source 0) (row 0) (complete 0))))
    (mv :ok token fn2-csnapshot fn2-extents))
   (mv code token fn2-core))))

 ; One transaction per poll. No new OPEN transaction may stage after BEGIN;
 ; STAGED/BOUND ones still finish through the ordinary B writer. PUBLISHED
 ; owners must finish their accepted-result materialization and release too:
 ; txn :batched commits payload reservations before :reply releases its C row.
 ; OPEN rows are unadmitted work and cannot alter the held visible view.
 ; A disconnected upload retains/wakes its child txn until that drain ends.
 ; A stopped owner/core is recovery work, never a valid acquired snapshot.
 (fn2-csnapshot-op fn2-csnapshot-poll (token okind oslot ogen) 3
  (if (fn2-core-stopped-p fn2-core) (mv :stopped 0 0 fn2-core)
  (stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core))
              (fn2-succ-txns (fn2-core-succ-txns fn2-core))
              (fn2-commit-root (fn2-core-commit-root fn2-core))
              (fn2-seals (fn2-core-seals fn2-core))
              (fn2-extents (fn2-core-extents fn2-core)))
   (code cut event fn2-csnapshot)
   (cond ((not (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot))
          (mv :owner 0 0 fn2-csnapshot))
         ((= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
          (mv :held (fn2-csnapshot-cut-commit 0 fn2-csnapshot)
                    (fn2-csnapshot-cut-event 0 fn2-csnapshot) fn2-csnapshot))
         ((< (fn2-csnapshot-scan 0 fn2-csnapshot) (fn2-succ-txns-rows fn2-succ-txns))
          (if (not (unsigned-byte-p 32 (+ 1 (fn2-csnapshot-scan 0 fn2-csnapshot))))
              (mv :bounds 0 0 fn2-csnapshot)
          (let* ((r (fn2-csnapshot-scan 0 fn2-csnapshot))
                 (phase (fn2-succ-txns-phase r fn2-succ-txns))
                 (blocked (or (= (fn2-csnapshot-blocked 0 fn2-csnapshot) 1)
                              (= phase *fn2-succ-phase-staged*) (= phase *fn2-succ-phase-bound*)
                              (= phase *fn2-succ-phase-published*)))
                 (fn2-csnapshot (fn2-csnapshot-put 0 (scan (+ 1 r)) (blocked (if blocked 1 0)))))
           (mv :more 0 0 fn2-csnapshot))))
         ((or (= (fn2-csnapshot-blocked 0 fn2-csnapshot) 1)
              (not (zp (fn2-alloc-retirement-intent-batch fn2-extents)))
              (and (< 0 (fn2-seals-rows fn2-seals))
                   (not (= (fn2-seals-phase 0 fn2-seals) *fn2-seal-phase-idle*)))
              (not (< 0 (fn2-commit-root-rows fn2-commit-root)))
              (not (zp (fn2-commit-root-aborting 0 fn2-commit-root)))
              (not (= (fn2-commit-root-installed 0 fn2-commit-root)
                      (fn2-commit-root-published 0 fn2-commit-root)))
              (not (= (fn2-commit-root-proposed 0 fn2-commit-root)
                      (fn2-commit-root-published 0 fn2-commit-root))))
          (let ((fn2-csnapshot (fn2-csnapshot-put 0 (scan 0) (blocked 0))))
           (mv :more 0 0 fn2-csnapshot)))
         (t (let* ((cut (fn2-commit-root-published 0 fn2-commit-root))
                   (event (if (zp (fn2-commit-root-first-key 0 fn2-commit-root)) 0
                            (- (fn2-commit-root-first-key 0 fn2-commit-root) 1)))
                   (fn2-csnapshot (fn2-csnapshot-put 0 (phase *fn2-csnapshot-phase-held*)
                                    (cut-commit cut) (cut-event event) (source 0) (row 0) (complete 0))))
              (mv :held cut event fn2-csnapshot))))
   (mv code cut event fn2-core))))

 ; Release never implies persistence or checkpoint completion. The coordinator
 ; must retain this ownership on an ambiguous write/install outcome.
 (fn2-csnapshot-op fn2-csnapshot-release (token okind oslot ogen) 1
  (if (fn2-core-stopped-p fn2-core) (mv :stopped fn2-core)
  (stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core))
              (fn2-extents (fn2-core-extents fn2-core))) (code fn2-csnapshot fn2-extents)
   (if (not (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot))
       (mv :owner fn2-csnapshot fn2-extents)
     (mv-let (code fn2-extents) (fn2-alloc-snapshot-release token okind oslot ogen fn2-extents)
      (let ((fn2-csnapshot (if (eq code :ok)
             (fn2-csnapshot-set-phase 0 *fn2-csnapshot-phase-idle* fn2-csnapshot) fn2-csnapshot)))
       (mv code fn2-csnapshot fn2-extents))))
   (mv code fn2-core))))))
