; PRF-1143 bounded input setup schedule. Source-only until operational backing
; carry, source identity observations and actual native range-copy refinement
; are installed. No host range arithmetic; no implicit backing capacity.
(in-package "ACL2")
(include-book "incoming-octet-holder")
(include-book "connection-read-quantum")

; Plan=(token total installed-capacity quantum offset pending phase).
; Pending is a fixed four-field grant (:incoming-copy token start count).
(defun fn-isr-plan (token total capacity quantum offset pending phase)
  (declare (xargs :guard t))
  (list token total capacity quantum offset pending phase))
(defun fn-isr-begin (token total capacity limits)
  (declare (xargs :guard t))
  (if (not (and (fn-ioh-tokenp token) (natp total) (natp capacity)
                (<= total capacity)))
      (mv :setup-unavailable nil)
    (mv :setup-started
        (fn-isr-plan token total capacity (fn-cbud-step-read-octets limits)
                     0 nil (if (zp total) :complete :copying)))))
(defun fn-isr-next (plan)
  (declare (xargs :guard t))
  (let* ((phase (fn-prl-nth 6 plan)) (pending (fn-prl-nth 5 plan))
         (total (nfix (fn-prl-nth 1 plan)))
         (offset (nfix (fn-prl-nth 4 plan)))
         (quantum (nfix (fn-prl-nth 3 plan))))
    (cond ((equal phase :complete) (mv :complete nil plan))
          ((not (equal phase :copying)) (mv :setup-unavailable nil plan))
          (pending (mv :copy pending plan))
          ((or (not (posp quantum)) (>= offset total))
           (mv :setup-unavailable nil plan))
          (t (let ((grant (list :incoming-copy (fn-prl-nth 0 plan) offset
                               (min quantum (- total offset)))))
               (mv :copy grant
                   (fn-isr-plan (fn-prl-nth 0 plan) total
                                (fn-prl-nth 2 plan) quantum offset grant :copying)))))))
(defun fn-isr-grantp (grant)
  (declare (xargs :guard t))
  (and (consp grant) (equal (car grant) :incoming-copy)
       (consp (cdr grant)) (fn-ioh-tokenp (cadr grant))
       (consp (cddr grant)) (natp (caddr grant))
       (consp (cdddr grant)) (posp (cadddr grant))
       (null (cddddr grant))))
(defun fn-isr-ack (plan grant outcome)
  (declare (xargs :guard t))
  (let ((pending (fn-prl-nth 5 plan)))
    (cond ((not (and (equal (fn-prl-nth 6 plan) :copying)
                     (fn-isr-grantp grant) (fn-isr-grantp pending)
                     (equal grant pending)))
           (mv :stale-copy plan))
          ((equal outcome :copied)
           (let* ((offset (+ (nfix (fn-prl-nth 2 grant))
                             (nfix (fn-prl-nth 3 grant))))
                  (total (nfix (fn-prl-nth 1 plan))))
             (if (> offset total) (mv :stale-copy plan)
               (mv :copy-recorded
                   (fn-isr-plan (fn-prl-nth 0 plan) total (fn-prl-nth 2 plan)
                                (fn-prl-nth 3 plan) offset nil
                                (if (equal offset total) :complete :copying))))))
          ((member-eq outcome '(:uncertain :failed))
           (mv :copy-cancelled
               (fn-isr-plan (fn-prl-nth 0 plan) (fn-prl-nth 1 plan)
                            (fn-prl-nth 2 plan) (fn-prl-nth 3 plan)
                            (fn-prl-nth 4 plan) pending :cancelled)))
          (t (mv :invalid-copy-outcome plan)))))

(defthm fn-isr-new-range-bounded-by-quantum-and-source
  (implies (and (equal (fn-prl-nth 6 plan) :copying)
                (not (fn-prl-nth 5 plan))
                (equal (mv-nth 0 (fn-isr-next plan)) :copy))
           (let ((grant (mv-nth 1 (fn-isr-next plan))))
             (and (posp (fn-prl-nth 3 grant))
                  (<= (fn-prl-nth 3 grant) (nfix (fn-prl-nth 3 plan)))
                  (<= (+ (fn-prl-nth 2 grant) (fn-prl-nth 3 grant))
                      (nfix (fn-prl-nth 1 plan))))))
  :hints (("Goal" :in-theory (enable fn-isr-next fn-isr-plan fn-prl-nth))))
(defthm fn-isr-unacknowledged-next-keeps-plan
  (implies (and (equal (fn-prl-nth 6 plan) :copying) (fn-prl-nth 5 plan))
           (equal (mv-nth 2 (fn-isr-next plan)) plan))
  :hints (("Goal" :in-theory (enable fn-isr-next))))
(defthm fn-isr-stale-copy-keeps-plan
  (implies (equal (mv-nth 0 (fn-isr-ack plan grant outcome)) :stale-copy)
           (equal (mv-nth 1 (fn-isr-ack plan grant outcome)) plan))
  :hints (("Goal" :in-theory (enable fn-isr-ack))))

; This fixed record invariant is established at capture and preserved by the
; core transitions; it is not a whole owner/buffer revalidation at each step.
(defun fn-isr-tail (n x)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) x (fn-isr-tail (- n 1) (if (consp x) (cdr x) nil))))
(defun fn-isr-planp (plan)
  (declare (xargs :guard t))
  (let ((token (fn-prl-nth 0 plan)) (total (fn-prl-nth 1 plan))
        (capacity (fn-prl-nth 2 plan)) (quantum (fn-prl-nth 3 plan))
        (offset (fn-prl-nth 4 plan)) (pending (fn-prl-nth 5 plan))
        (phase (fn-prl-nth 6 plan)))
    (and (consp (fn-isr-tail 6 plan)) (null (fn-isr-tail 7 plan))
         (fn-ioh-tokenp token) (natp total) (natp capacity) (<= total capacity)
         (posp quantum) (<= quantum *fn-cbud-read-quantum*)
         (natp offset) (<= offset total)
         (member-eq phase '(:copying :complete :cancelled))
         (if (equal phase :complete) (and (equal offset total) (not pending))
           (and (if (equal phase :copying) (< offset total) t)
                (or (not pending)
                    (and (fn-isr-grantp pending)
                         (equal (fn-prl-nth 1 pending) token)
                         (equal (fn-prl-nth 2 pending) offset)
                         (equal (fn-prl-nth 3 pending)
                                (min quantum (- total offset))))))))))
(defun fn-isr-sealablep (plan)
  (declare (xargs :guard t))
  (and (equal (fn-prl-nth 6 plan) :complete) (not (fn-prl-nth 5 plan))))

(defthm fn-isr-begin-establishes-plan
  (implies (equal (mv-nth 0 (fn-isr-begin token total capacity limits)) :setup-started)
           (fn-isr-planp (mv-nth 1 (fn-isr-begin token total capacity limits))))
  :hints (("Goal" :in-theory (enable fn-isr-begin fn-isr-plan fn-isr-planp fn-isr-tail fn-prl-nth))))
(defthm fn-isr-next-preserves-plan
  (implies (fn-isr-planp plan)
           (fn-isr-planp (mv-nth 2 (fn-isr-next plan))))
  :hints (("Goal" :in-theory (enable fn-isr-next fn-isr-plan fn-isr-planp
                                    fn-isr-grantp fn-isr-tail fn-prl-nth))))
(defthm fn-isr-ack-preserves-plan
  (implies (fn-isr-planp plan)
           (fn-isr-planp (mv-nth 1 (fn-isr-ack plan grant outcome))))
  :hints (("Goal" :in-theory (enable fn-isr-ack fn-isr-plan fn-isr-planp
                                    fn-isr-grantp fn-isr-tail fn-prl-nth))))
(defthm fn-isr-sealable-plan-is-completely-copied
  (implies (and (fn-isr-planp plan) (fn-isr-sealablep plan))
           (and (equal (fn-prl-nth 4 plan) (fn-prl-nth 1 plan))
                (not (fn-prl-nth 5 plan))))
  :hints (("Goal" :in-theory (enable fn-isr-planp fn-isr-sealablep))))
(defthm fn-isr-every-issued-range-within-captured-bounds
  (implies (and (fn-isr-planp plan)
                (equal (mv-nth 0 (fn-isr-next plan)) :copy))
           (let ((grant (mv-nth 1 (fn-isr-next plan))))
             (and (fn-isr-grantp grant)
                  (equal (fn-prl-nth 1 grant) (fn-prl-nth 0 plan))
                  (<= (fn-prl-nth 3 grant) *fn-cbud-read-quantum*)
                  (<= (+ (fn-prl-nth 2 grant) (fn-prl-nth 3 grant))
                      (fn-prl-nth 1 plan)))))
  :hints (("Goal" :in-theory (enable fn-isr-planp fn-isr-next fn-isr-plan
                                    fn-isr-grantp fn-isr-tail fn-prl-nth))))
