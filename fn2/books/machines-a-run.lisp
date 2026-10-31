; Layer A's operations for its kinds' arms (the arms are machines-a.lisp's
; declarations; each run emits at most one descriptor).
(in-package "ACL2")
(include-book "machines-a-access")
(include-book "machines-a-scribe")
(include-book "machines-a")
(include-book "machine-arms")

; MACHINE-FORM 6.5 P3: echo's and scribe's arms in child form, over their
; tables and the core children their operations take, defined here before
; any core exists; their core faces are made in the callbacks section.
(defmachine-arms fn2-echo :children)
(defmachine-arms fn2-scribe :children)

(defmacro fn2-machine-a-events ()
 '(progn
; One credit per unretired row, held from successful Accept issue through
; admission and echo reclamation. Failed Accept/admission returns its credit.
; Thus free rows = credits + outstanding admission reservations. Only listener
; admission removes a free row; retirement never returns a credit.
(fn2-defoperation (:operation-set fn2-machine-resources) :callbacks :infer
(defun fn2-listener-return-credit (ord fn2-core)
  ; ORD is a listener's target ordinal; one outside the admitted kinds stops.
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (and (natp ord) (< ord *fn2-machine-admitted-max*))) (fn2-machine-refuse-write fn2-core)
    (fn2-machine-set-admission-credits ord
      (+ 1 (fn2-machine-admission-credits ord fn2-core)) fn2-core))))
(fn2-core-preserves fn2-listener-return-credit (ord fn2-core) :rows nil :prefix "")
(fn2-defoperation (:operation-set fn2-machine-resources) :callbacks :infer
(defun fn2-listener-take-credit (ord fn2-core)
  ; ORD is a listener's target ordinal; one outside the admitted kinds stops.
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  ; Taking a credit the partition does not hold is a caller's bug: stop
  ; before the field changes, never a count clamped at zero.
  (if (or (not (and (natp ord) (< ord *fn2-machine-admitted-max*)))
          (zp (fn2-machine-admission-credits ord fn2-core)))
      (fn2-machine-refuse-write fn2-core)
    (fn2-machine-set-admission-credits ord
      (- (fn2-machine-admission-credits ord fn2-core) 1) fn2-core))))
(fn2-core-preserves fn2-listener-take-credit (ord fn2-core) :rows nil :prefix "")

(defun fn2-machine-observe-terminal (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  ; A terminal for a row with nothing pending is a caller's bug: stop.
  (if (and (eq (fn2-machine-pending-read-code id fn2-core) :ok)
           (not (zp (fn2-machine-pending id fn2-core))))
      (fn2-machine-write-pending id (- (fn2-machine-pending id fn2-core) 1) fn2-core)
    (fn2-machine-refuse-write fn2-core)))
(fn2-core-preserves fn2-machine-observe-terminal (id fn2-core) :rows nil :prefix "")

(defun fn2-machine-refuse-observation (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((fn2-core (fn2-core-stop *fn2-stop-reason-machine-observation* fn2-core)))
    (mv *fn2-none* fn2-core)))
(fn2-core-preserves fn2-machine-refuse-observation (fn2-core) :position 1 :rows nil)


(defun fn2-machine-issue-result (id code bytes fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp bytes) (<= bytes *fn2-echo-run-bytes*))))
  (if (eq code :ok)
      (let ((fn2-core (fn2-machine-put id (pending 1) (wait-reason *fn2-wait-completion*))))
        (fn2-machine-result bytes *fn2-work-mailbox* 1 nil fn2-core))
    (if (eq code :exhausted)
        (let ((fn2-core (fn2-machine-park id fn2-core)))
          (fn2-machine-result 0 *fn2-work-mailbox* 0 nil fn2-core))
      ; TODO R6-NONEXHAUSTION-REFUSAL: replace this retained stop with the
      ; named close/release or evidence posture chosen by R6.
      (let ((fn2-core (fn2-machine-put id (stopped 1) (wait-reason *fn2-wait-none*))))
        (fn2-machine-result 0 *fn2-work-mailbox* 0 nil fn2-core)))))
(fn2-core-preserves fn2-machine-issue-result (id code bytes fn2-core) :position 4 :rows nil)

; The kinds' arms, generated from their declarations (machine-arms.lisp),
; then their run entries and certificates.
(defmachine-arms fn2-listener)
(defmachine-run fn2-listener)
(defmachine-arms fn2-echo :wrappers)
(defmachine-run fn2-echo)

))
