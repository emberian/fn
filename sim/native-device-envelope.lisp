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
              (mv-let (code address length)
               (fn2-host-op-span (nth 1 e) (nth 2 e) fn2-core)
               (fn2-nde-loan-span-p d code address length))
              (or (not (eq (nth 3 d) :write))
                  (equal (nth 6 d)
                   (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (bytes)
                    (fn2-envelope-read-range (nth 8 e) (+ (nth 8 e) (nth 9 e)) (nth 6 e) fn2-pool)
                    bytes))))
         (mv nil (cdr unbound)))
        (t (mv :physical-take-mismatch unbound)))))

; Physical returns enter the selected worker's done FIFO, then the host's
; completion FIFO. A terminal crash may leave a suffix unposted, but cannot
; justify posting a later physical completion before an earlier one.
(defun fn2-nde-returned-ids (records)
 (if (atom records) nil
  (if (eq (caar records) :return)
      (cons (nth 1 (car records)) (fn2-nde-returned-ids (cdr records)))
    (fn2-nde-returned-ids (cdr records)))))
(defun fn2-nde-post-join-p (e records unposted)
 (declare (xargs :verify-guards nil))
 (let ((job (fn2-nde-job (nth 2 e) (nth 3 e) records)))
  (or (not job) (and (consp unposted) (equal (nth 1 job) (car unposted))))))

; Shapes are the actual adapter constructors. Validate before positional
; reads in the replay; a dotted/truncated capture must fail without taking a
; logical transition. Payload authorization remains the actual envelope step.
(defun fn2-nde-control-shape-p (e)
 (and (true-listp e)
      (case (car e)
       (:clock (equal (len e) 4))
       ((:signal :turn :ack) (equal (len e) 2))
       (:take (equal (len e) 17))
       (:finish (equal (len e) 3))
       (:post (equal (len e) 13))
       (otherwise nil))))

; Reuse the actual replay step rather than copying its transition semantics.
; The take comparison runs after that step has validated the complete logical
; descriptor. Take itself does not release or mutate its borrowed range.
(defun fn2-native-device-envelope-steps (rest trace records taken caps unbound unposted backend fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (acl2-count rest)))
 (if (atom rest)
     (mv (if (or rest unbound) :unbound-physical-job :pass) caps fn2-core)
  (let ((e (car rest)))
   (if (not (fn2-nde-control-shape-p e))
       (mv :malformed-control caps fn2-core)
   (mv-let (failure taken caps fn2-core) (fn2-envelope-step e t taken caps fn2-core)
    (if failure (mv failure caps fn2-core)
     (mv-let (binding unbound unposted)
      (cond ((eq (car e) :take)
             (mv-let (binding unbound) (fn2-nde-bind-take e records unbound (cdr rest) backend fn2-core)
              (mv binding unbound unposted)))
            ((eq (car e) :post)
             (mv (cond ((not (fn2-nde-post-p e trace records backend)) :physical-post-mismatch)
                       ((not (fn2-nde-post-join-p e records unposted)) :physical-post-order)
                       (t nil))
                 unbound
                 (if (fn2-nde-job (nth 2 e) (nth 3 e) records) (cdr unposted) unposted)))
            (t (mv nil unbound unposted)))
      (if binding (mv binding caps fn2-core)
       (fn2-native-device-envelope-steps (cdr rest) trace records taken caps unbound unposted backend fn2-core)))))))))

(defun fn2-native-device-control-replay (profile boot trace records fd backend)
 (declare (xargs :verify-guards nil))
 (if (not (and (true-listp boot) (equal (len boot) 4) (eq (car boot) :boot-start)))
     (list :malformed-boot nil)
 (mv-let (physical-code effects) (fn2-native-device-effects records fd)
  (declare (ignore effects))
  (if (not (and (eq physical-code :ok) (member-eq backend '(:fdatasync :fullfsync)))) (list :malformed-physical nil)
   (with-local-stobj fn2-core
    (mv-let (verdict caps fn2-core)
     (let ((fn2-core (fn2-init-executor profile :echo nil fn2-core)))
      (mv-let (code fn2-core) (fn2-boot-start (nth 1 boot) (nth 2 boot) fn2-core)
       (if (and (equal (car boot) :boot-start) (equal (len boot) 4)
                (equal code :ok) (equal code (nth 3 boot)))
           (fn2-native-device-envelope-steps trace trace records nil nil (fn2-nde-submitted-ids records) (fn2-nde-returned-ids records) backend fn2-core)
         (mv :boot-start-mismatch nil fn2-core))))
     (list verdict caps)))))))
