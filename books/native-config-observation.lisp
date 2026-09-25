; fn: bounded, ACL2-owned configuration-history namespace observation.
;
; The raw adapter supplies a bounded list of (basename, octets) observations.
; This book decodes each record before using its generation, derives the only
; acceptable basename through the native-admin writer codec, and returns the
; canonical contiguous generation plan.  It does not choose a policy from
; names or bytes in raw Lisp.
(in-package "ACL2")
(include-book "native-admin-shape")
; The configuration record codec (fn-cfg-decode-exact); reached through
; books/native-admin.lisp until this book included only its shape (audit
; 2026-09-25, packet 4).
(include-book "config")

; The listing bound is the operator's: the profile's `max-config-generations'
; (books/byte-store-frame.lisp field 11, `fn-bs-profile-max-config-generations'),
; which the host reads once from the profile it opened and passes as
; MAX-GENERATIONS.  Exceeding it is a fault before the host retains a larger
; directory listing or treats a prefix as a usable history.  The writer
; refuses a generation above the same field
; (`fn-native-admin-publication-authorize', `:max-config-generations'), and
; the profile never shrinks (`fn-profile-upgradep'), so a store the node wrote
; never exceeds its own listing bound.  (D27, PRF-102; the pre-D27 constant
; was 8192.)

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
  "A total natural projection.  Decoded records already supply a natural
generation; NFIX keeps sorting and validation inside arithmetic guards when a
program-mode caller supplies a malformed logical entry."
  (declare (xargs :guard t)) (nfix (fn-ag-car entry)))
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
    (list entry)))

(defun fn-nco-sort-by-generation (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (fn-nco-insert-by-generation (car entries)
                                   (fn-nco-sort-by-generation (cdr entries)))
    nil))

(defthm fn-nco-entry-generation-is-a-natural
  (natp (fn-nco-entry-generation entry))
  :rule-classes :type-prescription)

(verify-guards fn-nco-entry-generation)
(verify-guards fn-nco-insert-by-generation)

; These are the preservation keystones for the recovery sorter.  A directory
; can contain conflicting decoded generations, so preserving only a set of
; generations would be too weak: every observed decoded entry must remain in
; the result until the namespace validator rejects the conflict.
(defun fn-nco-occurrences (target entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (+ (if (equal target (car entries)) 1 0)
         (fn-nco-occurrences target (cdr entries)))
    0))

(defthm fn-nco-insert-by-generation-preserves-occurrences
  (equal (fn-nco-occurrences target
                             (fn-nco-insert-by-generation entry entries))
         (+ (if (equal target entry) 1 0)
            (fn-nco-occurrences target entries)))
  :hints (("Goal" :induct (fn-nco-insert-by-generation entry entries))))

(defthm fn-nco-sort-by-generation-preserves-occurrences
  (equal (fn-nco-occurrences target (fn-nco-sort-by-generation entries))
         (fn-nco-occurrences target entries))
  :hints (("Goal" :induct (fn-nco-sort-by-generation entries))))

(defthm fn-nco-sort-by-generation-preserves-cardinality
  (equal (len (fn-nco-sort-by-generation entries))
         (len entries))
  :hints (("Goal" :induct (fn-nco-sort-by-generation entries))))

(defthm fn-nco-sort-by-generation-preserves-membership
  (iff (member-equal entry (fn-nco-sort-by-generation entries))
       (member-equal entry entries)))

(defun fn-nco-canonical-contiguousp (entries expected-generation)
  (declare (xargs :guard t))
  (if (consp entries)
      (let* ((entry (car entries))
             (expected (nfix expected-generation))
             (generation (fn-nco-entry-generation entry)))
        (and (equal generation expected)
             (equal (fn-nco-entry-name entry)
                    (fn-native-admin-config-name generation))
             (fn-nco-canonical-contiguousp (cdr entries) (+ 1 expected))))
    (null entries)))

(verify-guards fn-nco-canonical-contiguousp)

(defun fn-nco-output-entries (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (cons (list (fn-nco-entry-name (car entries))
                  (fn-nco-entry-octets (car entries)))
            (fn-nco-output-entries (cdr entries)))
    nil))

(defun fn-nco-observe (entries max-generations)
  "Return :ok only for the exact bounded 1..n filename/generation history."
  (declare (xargs :guard t))
  (if (or (not (true-listp entries))
          (< (nfix max-generations) (len entries)))
      (fn-nco-result :fault :budget nil)
    (let ((decoded (fn-nco-decode-entries entries)))
      (if (equal decoded :bad)
          (fn-nco-result :fault :decode nil)
        (let ((ordered (fn-nco-sort-by-generation decoded)))
          (if (and (consp ordered)
                   (fn-nco-canonical-contiguousp ordered 1))
            (fn-nco-result :ok nil (fn-nco-output-entries ordered))
            (fn-nco-result :fault :namespace nil)))))))

; Initialization has not published generation 1 yet.  Only this entry accepts
; an exactly empty namespace; recovery continues to require a durable history.
(defun fn-nco-observe-initial (entries max-generations)
  (declare (xargs :guard t))
  (if (null entries) (fn-nco-result :ok nil nil)
    (fn-nco-observe entries max-generations)))

; KEYSTONE (D27, PRF-102: the listing refuses exactly past the operator's
; bound).  For a proper observation list, the budget fault occurs iff the
; namespace holds more entries than MAX-GENERATIONS, the profile's
; `max-config-generations' the host passes (host/native/io.lisp
; `fnn-config-record-observation' -> host/store-node-host.lisp
; `fn-store-config-observation' -> this function).  No other arm reports
; :budget, so a namespace within the bound is never refused for its size,
; however far above the pre-D27 8192 the operator set the field.
(defthm fn-nco-observe-refuses-exactly-past-the-operator-bound
  (implies (true-listp entries)
           (iff (equal (fn-nco-result-reason
                        (fn-nco-observe entries max-generations))
                       :budget)
                (< (nfix max-generations) (len entries))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-nco-observe fn-nco-result
                                   fn-nco-result-reason)
                                  (fn-nco-decode-entries
                                   fn-nco-sort-by-generation
                                   fn-nco-canonical-contiguousp
                                   fn-nco-output-entries)))))
