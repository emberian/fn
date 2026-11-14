; Issuance accounting for the actual common action pipeline.
(in-package "ACL2")
(include-book "ops-issued-count")

(defthm fn2-issue-children-issued-total
 (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
  (equal
   (fn2-ops-issued-count
    (fn2-ops-rows (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)))
    (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)))
   (+ (fn2-ops-issued-count (fn2-ops-rows fn2-ops) fn2-ops)
      (if (eq (car (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)) :ok) 1 0))))
 :hints (("Goal" :use (:instance fn2-env-op-reserve-ok-facts (o fn2-ops))
 :in-theory (e/d (fn2-issue-children)
  (fn2-ops-issued-count fn2-op-issued-weight fn2-op-enqueue fn2-opsp fn2-ops-wfp fn2-ops-rows)))))

(defthm fn2-issue-children-keeps-issued-rows
 (equal (fn2-ops-rows (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)))
        (fn2-ops-rows fn2-ops))
 :hints (("Goal" :in-theory (e/d (fn2-issue-children)
   (fn2-op-reserve fn2-op-unreserve fn2-op-enqueue fn2-op-set-range
    fn2-op-set-capability fn2-op-set-storage fn2-op-set-cancel-target fn2-ops-rows)))))

(defthm fn2-issue-children-issued-count-of-rows
 (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
  (equal (fn2-ops-issued-count (fn2-ops-rows fn2-ops) (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)))
   (+ (fn2-ops-issued-count (fn2-ops-rows fn2-ops) fn2-ops)
      (if (eq (car (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)) :ok) 1 0))))
 :hints (("Goal" :use fn2-issue-children-issued-total
  :in-theory (disable fn2-issue-children-issued-total fn2-ops-issued-count fn2-ops-rows))))

; Each action face uses the same actual issue pipeline, including its refusal
; and rollback branches. This relation counts incarnations, not queue length.
(defun fn2-issued-wrapper-events (names world)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (let* ((fn (car names)) (call (cons fn (getpropc fn 'formals nil world))))
   (append `((defthm ,(fn2-columns-sym fn "-ISSUED-ROWS")
     (equal (fn2-ops-rows (mv-nth 4 ,call)) (fn2-ops-rows fn2-ops))
     :hints (("Goal" :in-theory (e/d (,fn) (fn2-ops-rows)))))
    (defthm ,(fn2-columns-sym fn "-ISSUED-TOTAL")
     (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
      (equal (fn2-ops-issued-count (fn2-ops-rows fn2-ops) (mv-nth 4 ,call))
       (+ (fn2-ops-issued-count (fn2-ops-rows fn2-ops) fn2-ops)
          (if (eq (car ,call) :ok) 1 0))))
     :hints (("Goal" :in-theory (e/d (,fn)
       (fn2-ops-issued-count fn2-op-issued-weight fn2-ops-rows fn2-opsp fn2-ops-wfp))))))
    (fn2-issued-wrapper-events (cdr names) world)))))
(make-event (value (cons 'progn (fn2-issued-wrapper-events
 '(fn2-issue-receive-children fn2-issue-send-children fn2-issue-read-children
   fn2-issue-write-children fn2-issue-fence-children fn2-issue-accept-children
   fn2-issue-close-children fn2-issue-cancel-children fn2-issue-entropy-children)
 (w state)))))
