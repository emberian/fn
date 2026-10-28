; Independent accounting over emitted transition records, never over executor
; loop counters alone. Decoded records and certificates are test-only lists.
(in-package "ACL2")
(include-book "../books/profile")

(defun fn2-check-field (i xs)
  (declare (xargs :guard (natp i)))
  (if (consp xs)
      (if (zp i) (car xs) (fn2-check-field (1- i) (cdr xs)))
    nil))

(defun fn2-work-recordp (record profile)
  (declare (xargs :guard t))
  (let ((kind (fn2-check-field 0 record))
        (bytes (fn2-check-field 4 record))
        (steps (fn2-check-field 5 record))
        (actions (fn2-check-field 6 record)))
    (and (true-listp record) (= (len record) 19)
         (member-equal kind '(0 1 2 3 4))
         (natp bytes) (natp steps) (natp actions)
         (<= bytes (nfix (fn2-profile-run-bytes profile)))
         (<= steps (nfix (fn2-profile-run-steps profile)))
         (<= actions (nfix (fn2-profile-run-descriptors profile)))
         ; Payload work belongs to scheduled continuations, never ingress.
         (or (member-equal kind '(1 2)) (and (= bytes 0) (= actions 0))))))

(defun fn2-work-certificate (records)
  (declare (xargs :guard t))
  (if (atom records) (list 0 0 0 0 0)
    (let* ((record (car records))
           (kind (fn2-check-field 0 record))
           (rest (fn2-work-certificate (cdr records))))
      (list (+ (if (member-equal kind '(0 3 4)) 1 0)
               (nfix (fn2-check-field 0 rest)))
            (+ (if (member-equal kind '(1 2)) 1 0)
               (nfix (fn2-check-field 1 rest)))
            (+ (nfix (fn2-check-field 6 record)) (nfix (fn2-check-field 2 rest)))
            (+ (nfix (fn2-check-field 4 record)) (nfix (fn2-check-field 3 rest)))
            (+ (nfix (fn2-check-field 5 record)) (nfix (fn2-check-field 4 rest)))))))

; Scalar scheduler/return overhead is explicit rather than silently omitted
; from the reported work sum. CSCHED and CRETURN are declared abstract costs;
; this arithmetic is not a measured CPU-cost theorem. Each payload byte and
; structural step contributes one unit, matching fn2-turn-cost when CSCHED
; and CRETURN are 1. Descriptor counts remain a separate certificate component.
(defun fn2-work-cost-certificate (records csched creturn)
  (declare (xargs :guard (and (natp csched) (natp creturn))))
  (let* ((observed (fn2-work-certificate records))
         (calendar (* csched (nfix (fn2-check-field 1 observed))))
         (bytes (nfix (fn2-check-field 3 observed)))
         (structural (nfix (fn2-check-field 4 observed))))
    (list observed calendar creturn (+ bytes structural calendar creturn))))

(defun fn2-work-records-p (records profile)
  (declare (xargs :guard t))
  (if (atom records) (null records)
    (and (fn2-work-recordp (car records) profile)
         (fn2-work-records-p (cdr records) profile))))

(defun fn2-check-work (records lost nobs nvisits nactions profile)
  (declare (xargs :guard t))
  (let ((certificate (fn2-work-certificate records)))
    (cond ((not (equal lost 0)) '(:fail :work-trace-lost))
          ((not (fn2-profilep profile)) '(:fail :work-profile))
          ((not (fn2-work-records-p records profile)) '(:fail :run-work-cap))
          ((not (and (natp nobs) (natp nvisits) (natp nactions)))
           '(:fail :turn-work-count-type))
          ((not (and (equal nobs (fn2-check-field 0 certificate))
                     (equal nvisits (fn2-check-field 1 certificate))
                     (equal nactions (fn2-check-field 2 certificate))))
           '(:fail :turn-work-certificate))
          ((or (> nobs (nfix (fn2-profile-h profile)))
               (> nvisits (nfix (fn2-profile-k profile)))
               (> nactions (nfix (fn2-profile-aturn profile))))
           '(:fail :turn-work-cap))
          (t :pass))))

(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-check-field fn2-work-recordp fn2-work-certificate
    fn2-work-cost-certificate fn2-work-records-p fn2-check-work) (w state)))
(assert-event
 (let ((r '(1 0 0 0 4096 32 4 0 4294967295 0 0 0 1 1 1 2 1 3 1)))
   (and (equal (fn2-check-work (list r) 0 0 1 4 *fn2-profile-tiny*) :pass)
        (equal (fn2-check-work (list r) 1 0 1 4 *fn2-profile-tiny*)
               '(:fail :work-trace-lost))
        (equal (fn2-check-work (list (update-nth 4 4097 r)) 0 0 1 4 *fn2-profile-tiny*)
               '(:fail :run-work-cap))
        (equal (fn2-check-work (list (update-nth 5 33 r)) 0 0 1 4 *fn2-profile-tiny*)
               '(:fail :run-work-cap))
        (equal (fn2-check-work (list (update-nth 6 5 r)) 0 0 1 5 *fn2-profile-tiny*)
               '(:fail :run-work-cap))
        (equal (fn2-check-work (list r) 0 1 1 4 *fn2-profile-tiny*)
               '(:fail :turn-work-certificate)))))
(assert-event
 (let ((run '(1 0 0 0 7 1 4 0 4294967295 0 0 0 1 1 1 2 1 3 1))
       (empty '(1 4294967295 0 0 0 1 0 0 4294967295 0 0 0 0 0 0 0 0 0 0))
       (event '(0 0 0 0 0 1 0 0 4294967295 0 0 0 0 0 0 0 0 0 0)))
   (and (equal (fn2-check-work (list run run run) 0 0 3 12 *fn2-profile-tiny*)
               '(:fail :turn-work-cap))
        (equal (fn2-check-work (list event event event event event) 0 5 0 0
                               *fn2-profile-tiny*) '(:fail :turn-work-cap))
        (equal (fn2-check-work (list empty empty empty empty empty empty empty empty empty)
                               0 0 9 0 *fn2-profile-tiny*) '(:fail :turn-work-cap))
        (equal (fn2-work-cost-certificate (list run event) 3 2)
               '((1 1 4 7 2) 3 2 14))
        (equal (fn2-work-cost-certificate (list run event) 1 1)
               '((1 1 4 7 2) 1 1 11)))))
