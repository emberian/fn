; host/spike-storage-bp-host.lisp -- spike/storage (D28): the BP journal
; generation cleanup plan, ld'ed by both host/native/build.lisp and
; host/native/build-dtn.lisp.  :program code; see the SPIKE line below.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; E. BP journal generation cleanup (rotation retires generations).
;
;; SPIKE: defers an ACL2 plan book with the preservation theorem: after the
;; selection naming generation G is durable (the open read it), no open reads
;; a generation directory other than G's (fn-bpnr-plan-directory), so
;; removing every other generation directory changes no recovery; and a
;; staged selection file `.bp-generation-*' is never authority.  Directories
;; above G are removed only when empty (a killed rotation's unselected
;; directory), so no evidence is dropped.

(defun fn-spk-bp-cleanup-plan-aux (names selected old later strays)
  (declare (xargs :mode :program))
  (if (atom names)
      (list (reverse old) (reverse later) (reverse strays))
    (let* ((name (car names))
           (g (cond ((equal name "lifecycle") 0)
                    (t (fn-bpnr-generation-of-name name)))))
      (cond ((and (stringp name) (<= 15 (length name))
                  (equal (subseq name 0 15) ".bp-generation-"))
             (fn-spk-bp-cleanup-plan-aux (cdr names) selected old later
                                         (cons name strays)))
            ((and (natp g) (< g selected))
             (fn-spk-bp-cleanup-plan-aux (cdr names) selected (cons name old)
                                         later strays))
            ((and (natp g) (> g selected))
             (fn-spk-bp-cleanup-plan-aux (cdr names) selected old
                                         (cons name later) strays))
            (t (fn-spk-bp-cleanup-plan-aux (cdr names) selected old later
                                           strays))))))

; (OLD LATER STRAYS) for the observed root names under selection PLAN.
(defun fn-spk-bp-cleanup-plan (names plan)
  (declare (xargs :mode :program))
  (fn-spk-bp-cleanup-plan-aux names (nfix (fn-bpnr-plan-generation plan))
                              nil nil nil))
