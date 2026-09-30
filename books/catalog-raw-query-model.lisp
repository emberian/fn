; Raw query's reference selection over its captured oldest-first catalog rows.
; This list walk is a logical reference; the served implementation must use
; the retained provider/iterator and prove its terminal answer equals this.
; Reader visibility is intentionally not an input: withdrawn acceptance
; still belongs to duplicate history. Catalog ordinal and Store sequence are
; different types, bounded by captured count and committed frontier separately.
(in-package "ACL2")
(include-book "records-shape")

(defun fn-craw-first-from (msgid rows frontier ordinal)
  (declare (xargs :guard t))
  (if (consp rows)
      (let ((sequence (fn-record-sequence (car rows))))
        (if (and (natp sequence) (< sequence (nfix frontier))
                 (equal (fn-record-msgid (car rows)) msgid))
            (nfix ordinal)
          (fn-craw-first-from msgid (cdr rows) frontier (+ 1 (nfix ordinal)))))
    nil))

(defun fn-craw-first-accepted-row (msgid captured-rows frontier)
  (declare (xargs :guard t))
  (fn-craw-first-from msgid captured-rows frontier 0))

; No theorem about this reference alone closes the actual served lookup.
; Capture O must relate its oldest-first rows to raw Store acceptance and
; exclude pending/noncommitted rows; the iterator's coverage/no-hole and
; retained-root lifetime relation must justify its completed answer.
