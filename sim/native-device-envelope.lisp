; Bind the physical file-device capture to actual envelope replay.
; Selected-host premise: one executor submits, one FIFO worker performs;
; direct seed/setup performs are outside this existing-image replay entry.
(in-package "ACL2")
(include-book "check-envelope")
(include-book "native-device-bindings")

(defun fn2-nde-submit-join-p (e records unbound rest backend)
 (declare (xargs :verify-guards nil))
 (let ((job (fn2-nde-job (nth 1 e) (nth 2 e) records)))
  (if job (and (consp unbound) (equal (nth 1 job) (car unbound)))
   (if (eq (fn2-device-request (fn2-nde-kind (nth 3 e)) (nth 11 e) backend) :perform)
       ; The selected executor records Take, then Ack, then submits inline.
       ; A missing supported submit can only be this terminal cut, with no
       ; later physical jobs or later control actions skipped over the gap.
       (and (not unbound) (or (null rest) (equal rest '((:ack 1)))))
     t))))
(defun fn2-nde-bind-take (e records unbound rest backend fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (let* ((job (fn2-nde-job (nth 1 e) (nth 2 e) records)) (d (nth 2 job)))
  (cond ((not (fn2-nde-submit-join-p e records unbound rest backend))
         (mv :physical-submit-order unbound))
        ((not job) (mv nil unbound))
        ((and (eq (car job) :submit)
              (fn2-nde-take-descriptor-p e d backend)
              (or (not (eq (nth 3 d) :write))
                  (equal (nth 6 d)
                   (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (bytes)
                    (fn2-envelope-read-range (nth 8 e) (+ (nth 8 e) (nth 9 e)) (nth 6 e) fn2-pool)
                    bytes))))
         (mv nil (cdr unbound)))
        (t (mv :physical-take-mismatch unbound)))))

; Reuse the actual replay step rather than copying its transition semantics.
; The take comparison runs after that step has validated the complete logical
; descriptor. Take itself does not release or mutate its borrowed range.
(defun fn2-native-device-envelope-steps (rest trace records taken caps unbound backend fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (acl2-count rest)))
 (if (atom rest)
     (mv (if (or rest unbound) :unbound-physical-job :pass) caps fn2-core)
  (let ((e (car rest)))
   (mv-let (failure taken caps fn2-core) (fn2-envelope-step e t taken caps fn2-core)
    (if failure (mv failure caps fn2-core)
     (mv-let (binding unbound)
      (if (eq (car e) :take) (fn2-nde-bind-take e records unbound (cdr rest) backend fn2-core)
       (mv (and (eq (car e) :post) (not (fn2-nde-post-p e trace records backend)) :physical-post-mismatch) unbound))
      (if binding (mv binding caps fn2-core)
       (fn2-native-device-envelope-steps (cdr rest) trace records taken caps unbound backend fn2-core))))))))

(defun fn2-native-device-control-replay (profile boot trace records fd backend)
 (declare (xargs :verify-guards nil))
 (mv-let (physical-code effects) (fn2-native-device-effects records fd)
  (declare (ignore effects))
  (if (not (and (eq physical-code :ok) (member-eq backend '(:fdatasync :fullfsync)))) (list :malformed-physical nil)
   (with-local-stobj fn2-core
    (mv-let (verdict caps fn2-core)
     (let ((fn2-core (fn2-init-executor profile :echo nil fn2-core)))
      (mv-let (code fn2-core) (fn2-boot-start (nth 1 boot) (nth 2 boot) fn2-core)
       (if (and (equal (car boot) :boot-start) (equal (len boot) 4)
                (equal code :ok) (equal code (nth 3 boot)))
           (fn2-native-device-envelope-steps trace trace records nil nil (fn2-nde-submitted-ids records) backend fn2-core)
         (mv :boot-start-mismatch nil fn2-core))))
     (list verdict caps))))))
