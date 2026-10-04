; Teeth for books/store-log-recover-copy (RL-01, option A2; lane m1-durable-3,
; 2026-10-04): the adversarial witness of K2 (a failed journal/ fence, an
; exit with the cache kept, a second attempt that reads the visible but not
; durable replacement and copies it again, a power loss; and the variant
; where the second attempt's journal/ fence fails too), RL-01 red on the
; old in-place program and green under A2 on the same restart, and option
; A's in-place rewrite violating the side condition and losing A.
(in-package "ACL2")
(include-book "../../books/store-log-recover-copy")
(include-book "../../books/frame-trailer")
(include-book "../../books/codec-attach")

(defun lgrct-unit () (declare (xargs :guard t)) 4)
(defun lgrct-max () (declare (xargs :guard t)) 4096)
(defun lgrct-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun lgrct-r (i) (declare (xargs :guard t)) (list i (+ 1 (nfix i)) 7))
; A: two records, acknowledged.  B: a third, its batch's barrier fails.
; C: a fourth, appended and acknowledged after the restart.
(defun lgrct-a () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (list (lgrct-r 1) (lgrct-r 2)) (lgrct-genesis) (lgrct-unit)))
(defun lgrct-b () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (list (lgrct-r 3))
             (fn-lg-scan-last (lgrct-a) (lgrct-genesis) (lgrct-unit) (lgrct-max)) (lgrct-unit)))
(defun lgrct-c () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (list (lgrct-r 4))
             (fn-lg-scan-last (append (lgrct-a) (lgrct-b)) (lgrct-genesis) (lgrct-unit) (lgrct-max))
             (lgrct-unit)))
(defun lgrct-extent () (declare (xargs :guard t)) 512)
(defun lgrct-records (c) (declare (xargs :guard t :verify-guards nil))
  (car (fn-lg-scan c (lgrct-genesis) (lgrct-unit) (lgrct-max))))
(assert-event
 (let ((a (lgrct-a)) (ab (append (lgrct-a) (lgrct-b))) (abc (append (lgrct-a) (lgrct-b) (lgrct-c))))
   (and (fn-lgrc-completep a (lgrct-genesis) (lgrct-unit) (lgrct-max))
        (fn-lgrc-completep ab (lgrct-genesis) (lgrct-unit) (lgrct-max))
        (fn-lgrc-completep abc (lgrct-genesis) (lgrct-unit) (lgrct-max))
        (equal (lgrct-records abc) (list (lgrct-r 1) (lgrct-r 2) (lgrct-r 3) (lgrct-r 4)))
        (< (len abc) (lgrct-extent)))))

; The store at the restart: journal/K names inode 0, which durably holds A
; and zeros to the extent; nothing pending.
(defun lgrct-s0 () (declare (xargs :guard t :verify-guards nil))
  (fn-bsc-of (fn-bs-make (lgrct-unit)
                         (list (cons 0 (append (lgrct-a) (fn-bs-zeros (- (lgrct-extent) (len (lgrct-a)))))))
                         (list (list :journal (cons "K" 0)) (list :staging))
                         nil 1)))
; The world's events, from the failed barrier on.
(defun lgrct-events (outs2) (declare (xargs :guard t :verify-guards nil))
  (list (list :write 0 (len (lgrct-a)) (lgrct-b) :ok)          ; B appended, never acknowledged
        (list :fsync-file 0 (cons :eio nil))                    ; its barrier fails: B clean, not durable
        (list :exit)                                            ; restart with the cache kept
        (list :attempt :staging "stage" (list :ok :ok :ok :ok (cons :eio nil) :ok)) ; journal/ fence fails
        (list :exit)
        (list :attempt :staging "stage" outs2)                  ; re-recovery
        (list :lose-cache nil)))                                ; power loss
(defun lgrct-world (outs2) (declare (xargs :guard t :verify-guards nil))
  (fn-lgrc-world (lgrct-s0) (lgrct-events outs2) :journal "K" (lgrct-genesis) (lgrct-max) 0))
(defun lgrct-bound-records (s) (declare (xargs :guard t :verify-guards nil))
  (let ((bs (fn-bsc-bs s)))
    (lgrct-records (fn-bs-durable-content bs (fn-bs-durable-entry bs :journal "K")))))

; The keystone's hypotheses are inhabited, and every state keeps the invariant.
(assert-event
 (and (fn-lgrc-invp (lgrct-s0) :journal "K" (lgrct-a))
      (fn-lgrc-world-okp (lgrct-s0) (lgrct-events nil) :journal "K" (lgrct-a) (lgrct-genesis) (lgrct-max) 0)
      (fn-lgrc-all-invp (lgrct-world nil) :journal "K" (lgrct-a))
      (fn-lgrc-world-okp (lgrct-s0) (lgrct-events (list :ok :ok :ok :ok (cons :eio nil)))
                         :journal "K" (lgrct-a) (lgrct-genesis) (lgrct-max) 0)
      (fn-lgrc-all-invp (lgrct-world (list :ok :ok :ok :ok (cons :eio nil))) :journal "K" (lgrct-a))))

; After the first attempt's failed journal/ fence the replacement is
; VISIBLE (inode 1) and not durable (journal/K still durably names 0): the
; second attempt reads it, does not trust it, and copies it again (inode 2).
(assert-event
 (let* ((w (lgrct-world nil)) (after1 (nth 7 w)))
   (and (equal (fn-bsc-lookup after1 :journal "K") 1)
        (equal (fn-bs-durable-entry (fn-bsc-bs after1) :journal "K") 0)
        (equal (len w) 16)
        (equal (fn-bs-durable-entry (fn-bsc-bs (car (last w))) :journal "K") 2)
        ;; the power loss leaves inode 2 bound: A and B's records
        (equal (lgrct-bound-records (car (last w)))
               (list (lgrct-r 1) (lgrct-r 2) (lgrct-r 3))))))

; Variant: the second attempt's journal/ fence fails too.  The durable
; binding is still inode 0, never written: A's records.
(assert-event
 (let ((w (lgrct-world (list :ok :ok :ok :ok (cons :eio nil)))))
   (and (equal (fn-bs-durable-entry (fn-bsc-bs (car (last w))) :journal "K") 0)
        (equal (lgrct-bound-records (car (last w))) (list (lgrct-r 1) (lgrct-r 2))))))

; The restart's state: B readable (clean cache), not durable.
(defun lgrct-restarted () (declare (xargs :guard t :verify-guards nil))
  (nth 2 (lgrct-world nil)))
(defun lgrct-ab () (declare (xargs :guard t :verify-guards nil)) (append (lgrct-a) (lgrct-b)))
(defun lgrct-steps (s ops) (declare (xargs :guard t :verify-guards nil))
  (if (consp ops) (mv-let (r s1) (fn-bsc-step s (car ops)) (declare (ignore r)) (lgrct-steps s1 (cdr ops))) s))
; Serve C after recovery into whatever journal/K visibly names: the append
; and its barrier, both :ok (C is acknowledged), then a power loss.
(defun lgrct-serve-c-then-lose (s) (declare (xargs :guard t :verify-guards nil))
  (let ((ino (fn-bsc-lookup s :journal "K")))
    (lgrct-steps s (list (list :write ino (len (lgrct-ab)) (lgrct-c) :ok)
                         (list :fsync-file ino :ok)
                         (list :lose-cache nil)))))

(assert-event
 (let ((s (lgrct-restarted)))
   (and (equal (fn-bs-take (len (lgrct-ab)) (fn-bsc-content s 0)) (lgrct-ab))   ; read: A and B
        (equal (lgrct-records (fn-bs-durable-content (fn-bsc-bs s) 0))            ; durable: A only
               (list (lgrct-r 1) (lgrct-r 2))))))

; RL-01 RED on the OLD program (P-LOG-RECOVER: zero [F, end) in place, fence):
; the open's kernel counts B as history; C is appended after it and
; acknowledged; the power loss leaves a hole where B was read from cache,
; and the open recovers 2 of the 4 records acknowledged.  The old program
; keeps the invariant over A, but never establishes it over what it read.
(defun lgrct-old-recovered () (declare (xargs :guard t :verify-guards nil))
  (let ((s (lgrct-restarted)))
    (lgrct-steps s (list (list :write 0 (len (lgrct-ab))
                               (fn-bs-zeros (- (lgrct-extent) (len (lgrct-ab)))) :ok)
                         (list :fsync-file 0 :ok)))))
(assert-event
 (let ((final (lgrct-serve-c-then-lose (lgrct-old-recovered))))
   (and (fn-lgrc-invp (lgrct-old-recovered) :journal "K" (lgrct-a))
        (not (fn-lgrc-invp (lgrct-old-recovered) :journal "K" (lgrct-ab)))
        (equal (lgrct-bound-records final) (list (lgrct-r 1) (lgrct-r 2))))))

; GREEN under A2: one attempt from the same restart establishes the
; invariant over what it read (A and B), and the same service and power
; loss recover all four records.
(defun lgrct-a2-recovered () (declare (xargs :guard t :verify-guards nil))
  (car (last (fn-lgrc-attempt (lgrct-restarted) :journal "K" :staging "stage"
                              (lgrct-genesis) (lgrct-max) 0 nil))))
(assert-event
 (let ((final (lgrct-serve-c-then-lose (lgrct-a2-recovered))))
   (and (fn-lgrc-invp (lgrct-a2-recovered) :journal "K" (lgrct-ab))
        (equal (lgrct-bound-records final)
               (list (lgrct-r 1) (lgrct-r 2) (lgrct-r 3) (lgrct-r 4))))))

; A (rewrite the read prefix in place) violates the side condition, and its
; crash image with the first unit landed as zeros recovers nothing: the
; acknowledged A is lost.
(assert-event
 (let* ((s (lgrct-restarted))
        (op (list :write 0 0 (fn-bs-take (len (lgrct-ab)) (fn-bsc-content s 0)) :ok))
        (s1 (lgrct-steps s (list op)))
        (s2 (lgrct-steps s1 (list (list :lose-cache (list (list :zero)))))))
   (and (not (fn-lgrc-op-okp s op :journal "K" (lgrct-a)))
        (fn-bs-crash-choicesp (list (list :zero)) (fn-bs-pending (fn-bsc-bs s1)) (lgrct-unit))
        (equal (lgrct-bound-records s2) nil))))
