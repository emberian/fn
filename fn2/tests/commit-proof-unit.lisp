; Evaluated teeth use actual initialized machines, issued actions, routed
; completions, simulated death and durable-image recovery. No synthetic flags.
(in-package "ACL2")
(include-book "../books/commit-proof")

(defun fn2-commit-proof-positive (mode)
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-commit-proof-run (make-list 600 :initial-element '(:auto 26)) p mode 2 1)))
  (and (fn2-commit-ack-hyps p r) (equal (fn2-commit-proof-acks r) '(2 2))
       (fn2-commit-ack-evidencep r) (fn2-commit-proof-stable r))))

(defun fn2-commit-proof-fence-removal ()
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :lying nil t nil 0 0))
        (r (fn2-commit-proof-run (make-list 600 :initial-element '(:auto 10)) p 0 2 1)))
  (and (fn2-cm-profilep p) (not (fn2-cm-persistence-fence p))
       (fn2-commit-proof-admitted r) (equal (fn2-commit-proof-acks r) '(2 2))
       (not (fn2-commit-ack-evidencep r)))))

(defun fn2-commit-proof-timeout-positive (mode)
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-commit-proof-run (make-list 600 :initial-element '(:auto-timeout)) p mode 2 1)))
  (and (fn2-commit-proof-admitted r) (fn2-commit-proof-saw-uncertain r)
       (fn2-commit-proof-stable r) (equal (fn2-commit-proof-acks r) '(0 0)))))

(defun fn2-commit-proof-dispatch-removal ()
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-commit-proof-run
            (append (make-list 600 :initial-element '(:auto 24)) '((:bypass-notify 0))) p 0 2 1)))
  (and (fn2-cm-profilep p) (fn2-cm-persistence-fence p)
       (not (fn2-commit-proof-admitted r)) (fn2-commit-proof-saw-uncertain r)
       (not (fn2-commit-proof-stable r))
       (equal (car (fn2-commit-proof-acks r)) 1)
       (not (fn2-commit-ack-evidencep r)))))

(defun fn2-commit-proof-first-write (events)
 (declare (xargs :verify-guards nil))
 (if (atom events) nil
  (if (eq (fn2-lm-event-tag (car events)) :write)
      (fn2-history-write-event-batch (car events))
   (fn2-commit-proof-first-write (cdr events)))))
(defun fn2-commit-proof-follower-first ()
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-commit-proof-run
             (make-list 600 :initial-element '(:auto-follower-first 26)) p 0 2 1)))
  (and (fn2-commit-ack-hyps p r) (equal (fn2-commit-proof-acks r) '(2 2))
       ; b54 M3: a follower may not issue its first journal write before its
       ; leader has, so a follower-first schedule still writes batch 1 first.
       (equal (fn2-commit-proof-first-write (fn2-commit-proof-events r)) 1)
       (fn2-commit-ack-evidencep r))))

(defun fn2-commit-proof-reuse-positive (mode)
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-commit-proof-run
             (append (make-list 600 :initial-element '(:auto 26))
                     (list (list :start 0 2 5 mode) (list :start 1 2 7 mode))
                     (make-list 600 :initial-element '(:auto 26))) p mode 2 1))
        (replies (fn2-commit-proof-replies r)))
  (and (fn2-commit-ack-hyps p r) (fn2-commit-ack-evidencep r)
       (fn2-commit-proof-stable r) (equal (len replies) 4)
       (equal (cdr (assoc-equal 1 replies)) 2) (equal (cdr (assoc-equal 2 replies)) 2)
       (equal (cdr (assoc-equal 3 replies)) 2) (equal (cdr (assoc-equal 4 replies)) 2)
       (equal (len (fn2-commit-proof-recovered r)) 4))))

(defun fn2-commit-proof-uncertain-rearm ()
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-commit-proof-run
             (append (make-list 600 :initial-element '(:auto-timeout))
                     '((:start 0 2 5 0) (:start 1 2 7 0))
                     (make-list 100 :initial-element '(:auto 26))) p 0 2 1)))
  (and (fn2-commit-proof-admitted r) (fn2-commit-proof-saw-uncertain r)
       (fn2-commit-proof-stable r) (not (fn2-commit-proof-replies r))
       (equal (fn2-commit-proof-acks r) '(0 0)))))

(defun fn2-commit-proof-duplicate-start ()
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-commit-proof-run
             (append (make-list 600 :initial-element '(:auto 26))
                     '((:start 0 2 1 0) (:start 1 2 3 0))) p 0 2 1)))
  (and (fn2-commit-ack-hyps p r) (fn2-commit-ack-evidencep r)
       (equal (fn2-commit-proof-acks r) '(2 2))
       (equal (len (fn2-commit-proof-replies r)) 2)
       (equal (len (fn2-commit-proof-recovered r)) 2))))

; This contract counterexample retains all three durable batches. It exposes
; client refusal consistency, not a physical durability hypothesis removal.
(defun fn2-commit-proof-refused-retry-contract ()
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-commit-proof-run
             (append '((:start 0 2 5 0))
                     (make-list 600 :initial-element '(:auto 26))
                     '((:start 0 2 5 0))
                     (make-list 600 :initial-element '(:auto 26))) p 0 2 1)))
  (and (fn2-cm-profilep p) (fn2-cm-persistence-fence p) (fn2-commit-proof-admitted r)
       (not (fn2-commit-proof-fresh r)) (fn2-commit-ack-hyps p r)
       (equal (cdr (assoc-equal 3 (fn2-commit-proof-replies r))) 2)
       (equal (len (fn2-commit-proof-recovered r)) 3)
       (fn2-commit-ack-evidencep r)
       (not (fn2-check-history (fn2-commit-proof-events r) p
              (fn2-commit-proof-classification r) (fn2-commit-proof-recovered r))))))

; Compact diagnostic for a real replay; never print full frame bytes.
(defun fn2-commit-proof-summary (result)
 (declare (xargs :verify-guards nil))
 (mv-let (code trace) (fn2-history-translate (fn2-commit-proof-events result))
  (list (fn2-commit-proof-admitted result) (fn2-commit-proof-acks result)
        (fn2-commit-proof-stable result) (fn2-commit-proof-saw-uncertain result)
        code (len trace) (len (fn2-commit-proof-recovered result))
        (fn2-commit-proof-classification result) (fn2-commit-proof-replies result) (fn2-commit-proof-fresh result))))

; The registry resolves zero-argument evaluators; these wrappers keep each
; existing whole-premise fixture and its barrier mode unchanged.
(defun fn2-commit-proof-ack-baseline ()
 (declare (xargs :verify-guards nil))
 (fn2-commit-proof-positive 0))
(defun fn2-commit-proof-ack-fua ()
 (declare (xargs :verify-guards nil))
 (fn2-commit-proof-positive 1))
(defun fn2-commit-proof-timeout-baseline ()
 (declare (xargs :verify-guards nil))
 (fn2-commit-proof-timeout-positive 0))
(defun fn2-commit-proof-timeout-fua ()
 (declare (xargs :verify-guards nil))
 (fn2-commit-proof-timeout-positive 1))
(defun fn2-commit-proof-reuse-baseline ()
 (declare (xargs :verify-guards nil))
 (fn2-commit-proof-reuse-positive 0))
(defun fn2-commit-proof-reuse-fua ()
 (declare (xargs :verify-guards nil))
 (fn2-commit-proof-reuse-positive 1))

(defun fn2-commit-proof-teeth ()
 (declare (xargs :verify-guards nil))
 (list (fn2-commit-proof-ack-baseline) (fn2-commit-proof-ack-fua)
       (fn2-commit-proof-fence-removal)
       (fn2-commit-proof-timeout-baseline) (fn2-commit-proof-timeout-fua)
       (fn2-commit-proof-dispatch-removal) (fn2-commit-proof-follower-first)
       (fn2-commit-proof-reuse-baseline) (fn2-commit-proof-reuse-fua)
       (fn2-commit-proof-uncertain-rearm) (fn2-commit-proof-duplicate-start) (fn2-commit-proof-refused-retry-contract)))
(fn2-assert-owed-teeth fn2-commit-ack-implies-durable fn2-commit-uncertain-persists)
