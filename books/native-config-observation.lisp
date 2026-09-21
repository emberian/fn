; fn: bounded, ACL2-owned configuration-history namespace observation.
;
; The raw adapter supplies a bounded list of (basename, octets) observations.
; This book decodes each record before using its generation, derives the only
; acceptable basename through the native-admin writer codec, and returns the
; canonical contiguous generation plan.  It does not choose a policy from
; names or bytes in raw Lisp.
(in-package "ACL2")
(include-book "native-admin")

; A recovery-time resource limit.  Exceeding it is a fault before the host
; retains a larger directory listing or treats a prefix as a usable history.
(defconst *fn-nco-max-config-observations* 8192)

(defun fn-nco-result (status reason entries)
  (declare (xargs :guard t))
  (list status reason entries))
(defun fn-nco-result-status (result)
  (declare (xargs :guard t)) (fn-ag-car result))
(defun fn-nco-result-reason (result)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr result)))
(defun fn-nco-result-entries (result)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr (fn-ag-cdr result))))

(defun fn-nco-observed-entryp (entry)
  (declare (xargs :guard t))
  (and (true-listp entry) (equal (len entry) 2)
       (stringp (car entry)) (fn-cbor-octet-listp (cadr entry))))

; A decoded entry is (generation basename octets).  A malformed input is NIL;
; generation is read only after the exact codec established fn-cfg-recordp.
(defun fn-nco-decode-entry (entry)
  (declare (xargs :guard t))
  (if (not (fn-nco-observed-entryp entry))
      nil
    (let ((parsed (fn-cfg-decode-exact (cadr entry))))
      (if (and (fn-record-parse-okp parsed)
               (fn-cfg-recordp (fn-record-parse-value parsed)))
          (list (fn-cfg-record-generation (fn-record-parse-value parsed))
                (car entry) (cadr entry))
        nil))))

(defun fn-nco-decode-entries (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (let ((entry (fn-nco-decode-entry (car entries))))
        (if (null entry)
            :bad
          (let ((rest (fn-nco-decode-entries (cdr entries))))
            (if (equal rest :bad) :bad (cons entry rest)))))
    (if (null entries) nil :bad)))

(defun fn-nco-entry-generation (entry)
  (declare (xargs :guard t)) (fn-ag-car entry))
(defun fn-nco-entry-name (entry)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr entry)))
(defun fn-nco-entry-octets (entry)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr (fn-ag-cdr entry))))

(defun fn-nco-insert-by-generation (entry entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (if (<= (fn-nco-entry-generation entry)
              (fn-nco-entry-generation (car entries)))
          (cons entry entries)
        (cons (car entries)
              (fn-nco-insert-by-generation entry (cdr entries))))
    entries))

(defun fn-nco-sort-by-generation (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (fn-nco-insert-by-generation (car entries)
                                   (fn-nco-sort-by-generation (cdr entries)))
    nil))

(defun fn-nco-canonical-contiguousp (entries expected-generation)
  (declare (xargs :guard t))
  (if (consp entries)
      (let* ((entry (car entries))
             (generation (fn-nco-entry-generation entry)))
        (and (equal generation expected-generation)
             (equal (fn-nco-entry-name entry)
                    (fn-native-admin-config-name generation))
             (fn-nco-canonical-contiguousp (cdr entries) (+ 1 expected-generation))))
    (null entries)))

(defun fn-nco-output-entries (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (cons (list (fn-nco-entry-name (car entries))
                  (fn-nco-entry-octets (car entries)))
            (fn-nco-output-entries (cdr entries)))
    nil))

(defun fn-nco-observe (entries)
  "Return :ok only for the exact bounded 1..n filename/generation history."
  (declare (xargs :guard t))
  (if (or (not (true-listp entries))
          (< *fn-nco-max-config-observations* (len entries)))
      (fn-nco-result :fault :budget nil)
    (let ((decoded (fn-nco-decode-entries entries)))
      (if (equal decoded :bad)
          (fn-nco-result :fault :decode nil)
        (let ((ordered (fn-nco-sort-by-generation decoded)))
          (if (fn-nco-canonical-contiguousp ordered 1)
              (fn-nco-result :ok nil (fn-nco-output-entries ordered))
            (fn-nco-result :fault :namespace nil))))))
)
