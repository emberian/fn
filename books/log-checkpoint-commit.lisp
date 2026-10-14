; LC admission and segment effect. A prepared record is (ROW FRAME ENTRY):
; FRAME is the sealed writer output, ENTRY its directory observation. ROW is
; the new catalog row, or nil for a maintenance entry whose caller applies
; the locator/reclaim effect. Each packet decodes to exactly one logical event.
; The producer/directory/column correspondence lands after LB's restack.
(in-package "ACL2")
(include-book "log-checkpoint-tail")
(include-book "catalog-columns")

(defun fn-lc-prepared-recordsp (records prev unit max)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (let* ((record (mbe :logic (car records) :exec (fn-lc-head records))) (frame (mbe :logic (nth 1 record) :exec (fn-lc-at 1 record)))
             (scan (fn-lc-scan-bytes frame prev unit max (len frame))))
        (and (true-listp record) (equal (len record) 3)
             (or (null (mbe :logic (car record) :exec (fn-lc-head record))) (fn-held-p (mbe :logic (car record) :exec (fn-lc-head record))))
             (consp frame) (equal (mbe :logic (car scan) :exec (fn-lc-head scan)) :ok)
             (equal (len (mbe :logic (nth 2 scan) :exec (fn-lc-at 2 scan))) 1)
             (equal (len (fn-lc-decode-tail-records (mbe :logic (nth 1 scan) :exec (fn-lc-at 1 scan)))) 1)
             (not (equal (fn-lc-decode-tail-records (mbe :logic (nth 1 scan) :exec (fn-lc-at 1 scan))) :bad))
             (fn-lc-prepared-recordsp (mbe :logic (cdr records) :exec (fn-lc-rest records)) (mbe :logic (nth 3 scan) :exec (fn-lc-at 3 scan)) unit max)))
    (null records)))

(defun fn-lc-last-segment-id (segs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp (mbe :logic (cdr segs) :exec (fn-lc-rest segs))) (fn-lc-last-segment-id (mbe :logic (cdr segs) :exec (fn-lc-rest segs))) (mbe :logic (caar segs) :exec (fn-lc-head (fn-lc-head segs)))))

(defun fn-lc-append-prepared (record id unit segs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp segs)
      (if (equal (mbe :logic (caar segs) :exec (fn-lc-head (fn-lc-head segs))) id)
          (cons (list id
                  (mbe :logic (append (cadar segs) (nth 1 record)
                          (fn-bs-zeros (fn-lg-pad-len (len (nth 1 record)) unit))) :exec (fn-lc-join (fn-lc-head (fn-lc-rest (fn-lc-head segs))) (fn-lc-join (fn-lc-at 1 record) (fn-bs-zeros (fn-lg-pad-len (len (fn-lc-at 1 record)) unit)))))
                  (mbe :logic (append (caddar segs) (if (nth 2 record) (list (nth 2 record)) nil)) :exec (fn-lc-join (fn-lc-head (fn-lc-rest (fn-lc-rest (fn-lc-head segs)))) (if (fn-lc-at 2 record) (list (fn-lc-at 2 record)) nil))))
                (mbe :logic (cdr segs) :exec (fn-lc-rest segs)))
        (cons (mbe :logic (car segs) :exec (fn-lc-head segs)) (fn-lc-append-prepared record id unit (mbe :logic (cdr segs) :exec (fn-lc-rest segs)))))
    segs))

; This single export call is the dependent seam. No local column layout or
; replacement correspondence is introduced. Maintenance packets pass through.
(defun fn-lc-append-prepared-columns (row segs fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
  (if row (fn-lbc-append-row row segs fn-lbc) fn-lbc))

(defun fn-lc-prepare-tail (records id unit segs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (fn-lc-prepare-tail (mbe :logic (cdr records) :exec (fn-lc-rest records)) id unit
                          (fn-lc-append-prepared (mbe :logic (car records) :exec (fn-lc-head records)) id unit segs))
    segs))

(defun fn-lc-commit-prepared (records segs fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
  (if (consp records)
      (let ((fn-lbc (fn-lc-append-prepared-columns (mbe :logic (caar records) :exec (fn-lc-head (fn-lc-head records))) segs fn-lbc)))
        (fn-lc-commit-prepared (mbe :logic (cdr records) :exec (fn-lc-rest records)) segs fn-lbc))
    (mv :ok fn-lbc segs)))

(defun fn-lc-commit (records segs header k fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (fn-lbc-p fn-lbc) (natp k))
                  :verify-guards nil))
  (cond ((and (natp k)
              (< k (+ (len (fn-lc-tail-history segs header)) (len records))))
         (mv :publication-behind fn-lbc segs))
        ((not (natp k)) (mv :invalid-tail-bound fn-lbc segs))
        ((or (not (fn-lc-segs-retain segs header))
             (not (equal (mbe :logic (car (fn-lc-tail-scan segs header)) :exec (fn-lc-head (fn-lc-tail-scan segs header))) :ok)))
         (mv :checkpoint-tail fn-lbc segs))
        ((not (fn-lc-prepared-recordsp records (mbe :logic (nth 3 (fn-lc-tail-scan segs header)) :exec (fn-lc-at 3 (fn-lc-tail-scan segs header)))
                                      (fn-lc-tail-unit header) (fn-lc-tail-max header)))
         (mv :invalid-prepared-record fn-lbc segs))
        (t (let ((proposed (fn-lc-prepare-tail records
                           (fn-lc-last-segment-id (fn-lc-ordered-segments segs))
                           (fn-lc-tail-unit header) segs)))
             ; Decide before any column effect. The entry decoder is the
             ; count of record events; maintenance events are included.
             (if (< k (len (fn-lc-tail-history proposed header)))
                 (mv :publication-behind fn-lbc segs)
               (fn-lc-commit-prepared records proposed fn-lbc))))))
