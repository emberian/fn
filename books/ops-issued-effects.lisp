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
; Issue faces return (code slot generation . children). Bind the operation
; carrier to the actual admitted ABI rather than assuming output position 4.
(defun fn2-issued-wrapper-ops-position (fn world)
 (declare (xargs :verify-guards nil))
 (let* ((ins (getpropc fn 'stobjs-in nil world))
        (outs (getpropc fn 'stobjs-out nil world))
        (pos (position-eq 'fn2-ops outs)))
  (and (function-symbolp fn world)
       (member-eq 'fn2-ops ins)
       (equal (take 3 outs) '(nil nil nil))
       (<= 4 (len outs))
       (natp pos) (<= 3 pos)
       (not (member-eq 'fn2-ops (cdr (member-eq 'fn2-ops outs))))
       pos)))
(defun fn2-issued-wrapper-events (names world)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (let* ((fn (car names)) (call (cons fn (getpropc fn 'formals nil world)))
         (pos (fn2-issued-wrapper-ops-position fn world)))
   (if (not pos)
       `((make-event (er soft 'fn2-issued-wrapper-events
            "Unsupported issue result ABI for ~x0." ',fn)))
   (append `((defthm ,(fn2-columns-sym fn "-ISSUED-ROWS")
     (equal (fn2-ops-rows (mv-nth ,pos ,call)) (fn2-ops-rows fn2-ops))
     :hints (("Goal" :in-theory (e/d (,fn) (fn2-ops-rows)))))
    (defthm ,(fn2-columns-sym fn "-ISSUED-TOTAL")
     (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
      (equal (fn2-ops-issued-count (fn2-ops-rows fn2-ops) (mv-nth ,pos ,call))
       (+ (fn2-ops-issued-count (fn2-ops-rows fn2-ops) fn2-ops)
          (if (eq (car ,call) :ok) 1 0))))
     :hints (("Goal" :in-theory (e/d (,fn)
       (fn2-ops-issued-count fn2-op-issued-weight fn2-ops-rows fn2-opsp fn2-ops-wfp))))))
    (fn2-issued-wrapper-events (cdr names) world))))))
(make-event (value (cons 'progn (fn2-issued-wrapper-events
 (strip-cars (table-alist 'fn2-issue-child-wrappers (w state)))
 (w state)))))
