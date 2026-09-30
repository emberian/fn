; PRF-1090: actual FNBS row, checkpoint, and recovery admission subjects.
(in-package "ACL2")
(include-book "../../books/bp-recovery-profile")
(include-book "bp-held-projection-tests")

(defconst *bprpft-profile* '(8 1048576 8 1048576))
(defconst *bprpft-small* '(8 1048576 7 1048576))
(defun bprpft-row () (declare (xargs :guard t :verify-guards nil)) (cadr (car (bpnfr-replay-rows))))
(defun bprpft-event () (declare (xargs :guard t :verify-guards nil))
  (fn-bphp-recover-auto-event *bphpt-st* nil :ready (bpnfr-replay-rows) '(:none)))
(defun bprpft-held () (declare (xargs :guard t :verify-guards nil)) (car (fn-bpn-nth 1 (fn-bpn-nth 4 (bprpft-event)))))
(defun bprpft-plan () (declare (xargs :guard t :verify-guards nil))
  (list :selected (fn-bpnr-checkpoint-of-event (bprpft-event) 1)))

; Positive: fragment payload is only five octets; the bound reads total eight.
; fn-bprpf-admitted-row-has-bounded-adu, full antecedent and conclusion.
(assert-event
 (and (fn-bpnpf-profilep *bprpft-profile*)
      (equal (fn-bprpf-row-admit (bprpft-row) *bprpft-profile*) '(:ready))
      (equal (len (fn-bpb-payload (fn-bpnf-held-bundle *bpnff-p3*))) 5)
      (equal (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle *bpnff-p3*)) 8)
      (<= (fn-bpnpf-bundle-adu-length
           (fn-bpnf-held-bundle
            (fn-bpn-nth 3 (fn-bpnf-stored-record-unframe (bprpft-row)))))
          (fn-bpnpf-adu-octets *bprpft-profile*))))

; Hypothesis removal: row admission is not ready, and the claimed bound fails.
(assert-event
 (and (not (equal (fn-bprpf-row-admit (bprpft-row) *bprpft-small*) '(:ready)))
      (equal (fn-bprpf-row-admit (bprpft-row) *bprpft-small*) '(:fault :adu-beyond-profile))
      (not (<= (fn-bpnpf-bundle-adu-length
                (fn-bpnf-held-bundle
                 (fn-bpn-nth 3 (fn-bpnf-stored-record-unframe (bprpft-row)))))
               (fn-bpnpf-adu-octets *bprpft-small*)))))

; Positive: the actual complete family replay returns a nonfragment payload.
; fn-bprpf-ready-recovery-bounds-every-held-adu, full antecedent and conclusion.
(assert-event
 (let ((r (fn-bpn-nth 4 (fn-bprpf-admit-recovery (bprpft-event) *bprpft-profile*))))
  (and (equal (fn-bpn-nth 0 r) :ready)
       (member-equal (bprpft-held) (fn-bpn-nth 1 r))
       (not (fn-bpp-fragmentp (fn-bpp-flags (fn-bpb-bundle-primary (fn-bpnf-held-bundle (bprpft-held))))))
       (equal (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle (bprpft-held)))
              (len (fn-bpb-payload (fn-bpnf-held-bundle (bprpft-held)))))
       (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle (bprpft-held)))
           (fn-bpnpf-adu-octets *bprpft-profile*)))))

; Positive: the exact checkpoint of that event is admitted before replay.
; fn-bprpf-admitted-checkpoint-bounds-every-held-adu, full antecedent/conclusion.
(assert-event
 (and (equal (fn-bprpf-selection-admit (bprpft-plan) *bprpft-profile*) '(:ready))
      (member-equal (bprpft-held) (fn-bpnr-checkpoint-held (fn-bpnr-plan-checkpoint (bprpft-plan))))
      (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle (bprpft-held)))
          (fn-bpnpf-adu-octets *bprpft-profile*))))

; Hypothesis removal: checkpoint admission is not ready, member retained.
(assert-event
 (and (not (equal (fn-bprpf-selection-admit (bprpft-plan) *bprpft-small*) '(:ready)))
      (member-equal (bprpft-held) (fn-bpnr-checkpoint-held (fn-bpnr-plan-checkpoint (bprpft-plan))))
      (not (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle (bprpft-held)))
               (fn-bpnpf-adu-octets *bprpft-small*)))))

; Hypothesis removal: member omitted, every retained readiness hypothesis true.
; Empty ready recovery/checkpoint need not bound an unrelated held row.
(defun bprpft-empty-event () (declare (xargs :guard t :verify-guards nil))
  (fn-bphp-recover-auto-event *bphpt-st* nil :ready nil '(:none)))
(assert-event
 (let ((r (fn-bpn-nth 4 (fn-bprpf-admit-recovery (bprpft-empty-event) *bprpft-small*))))
  (and (equal (fn-bpn-nth 0 r) :ready)
       (not (member-equal (bprpft-held) (fn-bpn-nth 1 r)))
       (not (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle (bprpft-held)))
                (fn-bpnpf-adu-octets *bprpft-small*))))))
(assert-event
 (and (equal (fn-bprpf-selection-admit '(:none) *bprpft-small*) '(:ready))
      (not (member-equal (bprpft-held) (fn-bpnr-checkpoint-held (fn-bpnr-plan-checkpoint '(:none)))))
      (not (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle (bprpft-held)))
               (fn-bpnpf-adu-octets *bprpft-small*)))))

; Corrupted-state hypothesis removal: non-ready input is preserved, so a
; non-ready event can contain an over-limit member without claiming admission.
(defun bprpft-fault-event () (declare (xargs :guard t :verify-guards nil))
  (update-nth 4 (list :fault (list (bprpft-held))) (bprpft-event)))
(assert-event
 (let ((r (fn-bpn-nth 4 (fn-bprpf-admit-recovery (bprpft-fault-event) *bprpft-small*))))
  (and (not (equal (fn-bpn-nth 0 r) :ready))
       (member-equal (bprpft-held) (fn-bpn-nth 1 r))
       (not (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle (bprpft-held)))
                (fn-bpnpf-adu-octets *bprpft-small*))))))

; Mutation: a later kind-10 deletion does not bypass pre-fold row admission.
(assert-event
 (let* ((row (cadr (car (bpnfr-delete-rows))))
        (h (fn-bpn-nth 3 (fn-bpnf-stored-record-unframe row)))
        (adu (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle h)))
        (profile (list 8 1048576 (1- adu) 1048576)))
  (and (< 1 adu) (fn-bpnpf-profilep profile)
       (equal (car (bpnfr-delete-answer)) :ready)
       (fn-bpn-nth 14 (car (nth 1 (bpnfr-delete-answer))))
       (equal (fn-bprpf-row-admit row profile) '(:fault :adu-beyond-profile)))))

; Invalid profile and already-faulted replay stay named and non-ready.
(assert-event (equal (fn-bprpf-row-admit (bprpft-row) nil) '(:fault :profile)))
(assert-event (equal (fn-bprpf-selection-admit (bprpft-plan) nil) '(:fault :profile)))
(assert-event (equal (fn-bpn-nth 4 (fn-bprpf-admit-recovery (bprpft-event) nil)) '(:fault :profile)))
(assert-event (equal (fn-bprpf-admit-recovery (bprpft-fault-event) nil) (bprpft-fault-event)))
