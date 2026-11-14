; Source probe: physical prefixes and real commit uncertainty are separate
; controls of the same simulator fault. This is not a whole-host ACK theorem.
(in-package "ACL2")
(include-book "../books/commit-proof")

(defun fn2-see-bytes (n address durable fn2-sim-storage)
 (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (nfix n)))
 (if (zp n) nil
  (cons (if durable (fn2-sim-storage-durable address fn2-sim-storage)
          (fn2-sim-storage-pending address fn2-sim-storage))
        (fn2-see-bytes (- n 1) (+ 1 (nfix address)) durable fn2-sim-storage))))

(defun fn2-see-physical (prefix fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
      (fn2-own (fn2-own-init *fn2-profile-tiny* fn2-own))
      (fn2-sim (fn2-sim-init 1 :none "effectful-error" *fn2-profile-tiny* fn2-sim))
      ((mv rc slot gen fn2-core) (fn2-core-reserve 0 1 0 1 fn2-core))
      ((mv w0 fn2-core) (fn2-core-write slot gen 0 21 1 0 1 fn2-core))
      (fn2-own (fn2-own-observe-core-write slot gen 0 w0 21 fn2-core fn2-own))
      ((mv w1 fn2-core) (fn2-core-write slot gen 1 22 1 0 1 fn2-core))
      (fn2-own (fn2-own-observe-core-write slot gen 1 w1 22 fn2-core fn2-own))
      ((mv w2 fn2-core) (fn2-core-write slot gen 2 23 1 0 1 fn2-core))
      (fn2-own (fn2-own-observe-core-write slot gen 2 w2 23 fn2-core fn2-own))
      ((mv w3 fn2-core) (fn2-core-write slot gen 3 24 1 0 1 fn2-core))
      (fn2-own (fn2-own-observe-core-write slot gen 3 w3 24 fn2-core fn2-own))
      ; Prior fenced bytes occupy a separate address. Their expected value
      ; is specified here, not obtained by running the write handler twice.
      ((mv prior fn2-sim)
       (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim))) (ok fn2-sim-storage)
        (b* (((mv wc fn2-sim-storage) (fn2-storage-write-byte 4096 4096 91 1 nil nil fn2-sim-storage))
             ((mv fc fn2-sim-storage) (fn2-storage-fence-capture 0 fn2-sim-storage))
             ((mv dc fn2-sim-storage) (fn2-storage-fence-complete 0 nil nil fn2-sim-storage)))
         (mv (and (eq wc :ok) (eq fc :ok) (eq dc :ok)) fn2-sim-storage))
        (mv ok fn2-sim)))
      ((mv ic op & fn2-core) (fn2-issue-write 0 slot gen 0 4 0 1 0 1 0 fn2-core))
      (fn2-own (fn2-own-observe-issue op fn2-core fn2-own))
      ((mv taken fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own))
      ((mv & fn2-core fn2-sim fn2-own) (fn2-sim-complete op *fn2-fault-no-space* prefix fn2-core fn2-sim fn2-own))
      (physical
       (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim))) (ok)
        (and (equal (fn2-see-bytes 4 0 nil fn2-sim-storage)
                    (append (take prefix '(21 22 23 24)) (make-list (- 4 prefix) :initial-element 0)))
             (equal (fn2-see-bytes 4 0 t fn2-sim-storage) '(0 0 0 0))
             (equal (fn2-see-bytes 1 4096 t fn2-sim-storage) '(91))) ok)))
  (mv (and (equal (list rc w0 w1 w2 w3 ic) '(:ok :ok :ok :ok :ok :ok))
           prior (equal taken 1) physical
           (equal (fn2-sim-terminal-outcome op fn2-sim) *fn2-outcome-failed*)
           (equal (fn2-sim-terminal-reason op fn2-sim) *fn2-reason-no-space*)
           (equal (fn2-sim-terminal-count op fn2-sim) 0))
      fn2-core fn2-sim fn2-own)))

(defun fn2-see-prefix (prefix)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (ok fn2-core)
   (with-local-stobj fn2-sim
    (mv-let (ok fn2-core fn2-sim)
     (with-local-stobj fn2-own
      (mv-let (ok fn2-core fn2-sim fn2-own)
       (fn2-see-physical prefix fn2-core fn2-sim fn2-own)
       (mv ok fn2-core fn2-sim)))
     (mv ok fn2-core))) ok)))

; The same effectful error then traverses the actual issued commit writes,
; completion normalization, harvester and generated commit decision. Two
; earlier accepted batches must still recover after the later uncertainty.
(defun fn2-see-commit ()
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-commit-proof-run
            (append (make-list 600 :initial-element '(:auto 26))
                    '((:start 0 2 5 0) (:start 1 2 7 0))
                    (make-list 600 :initial-element '(:auto 12))) p 0 2 1))
        (replies (fn2-commit-proof-replies r)))
  (and (fn2-commit-proof-admitted r) (fn2-commit-proof-saw-uncertain r)
       (fn2-commit-proof-stable r) (fn2-commit-ack-evidencep r)
       (equal (len replies) 2)
       (equal (cdr (assoc-equal 1 replies)) 2)
       (equal (cdr (assoc-equal 2 replies)) 2)
       (equal (len (fn2-commit-proof-recovered r)) 2))))

(assert-event (and (fn2-see-prefix 0) (fn2-see-prefix 2) (fn2-see-prefix 4)))
(assert-event (fn2-see-commit))
