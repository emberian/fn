; Runtime NNTP number projection over materialized membership entries.
; Kept below books/nntp.lisp so the served pinned dispatcher can use it.
(in-package "ACL2")
(include-book "nntp-projection")
(include-book "index")

(defun fn-nntp-index-msgid-okp (text)
  (declare (xargs :guard t :verify-guards nil))
  (and (stringp text)
       (<= (length text) *fn-nntp-max-message-id-octets*)
       (fn-nntp-message-id-tokenp (fn-nntp-string-octets text))))

(defun fn-nntp-index-entry-available (entry)
  (declare (xargs :guard t :verify-guards nil))
  (let ((number (fn-index-entry-number entry)))
    (if (and (posp number)
             (<= number *fn-nntp-max-article-number*)
             (fn-nntp-index-msgid-okp (fn-index-entry-msgid entry)))
        number
      0)))

(defun fn-nntp-index-numbers (entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (let ((number (fn-nntp-index-entry-available (fn-ag-car entries))))
        (if (posp number)
            (cons number (fn-nntp-index-numbers (fn-ag-cdr entries)))
          (fn-nntp-index-numbers (fn-ag-cdr entries))))
    nil))

(defun fn-nntp-numbers-count (numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (+ 1 (fn-nntp-numbers-count (fn-ag-cdr numbers)))
    0))

(defun fn-nntp-numbers-min (numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (let ((number (fn-ag-car numbers))
            (rest (fn-nntp-numbers-min (fn-ag-cdr numbers))))
        (if (and (posp number)
                 (or (not (posp rest)) (< number rest)))
            number
          rest))
    0))

(defun fn-nntp-numbers-max (numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (let ((number (fn-ag-car numbers))
            (rest (fn-nntp-numbers-max (fn-ag-cdr numbers))))
        (if (and (posp number) (< rest number)) number rest))
    0))

(defthm fn-nntp-numbers-max-natp
  (natp (fn-nntp-numbers-max numbers))
  :rule-classes (:type-prescription :rewrite))

(defun fn-nntp-numbers-min-above (current numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (let ((number (fn-ag-car numbers))
            (rest (fn-nntp-numbers-min-above current (fn-ag-cdr numbers))))
        (if (and (posp number)
                 (fn-ag-less current number)
                 (or (not (posp rest)) (< number rest)))
            number
          rest))
    0))

(defun fn-nntp-numbers-max-below (current numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (let ((number (fn-ag-car numbers))
            (rest (fn-nntp-numbers-max-below current (fn-ag-cdr numbers))))
        (if (and (posp number)
                 (fn-ag-less number current)
                 (< rest number))
            number
          rest))
    0))

(defthm fn-nntp-numbers-max-below-natp
  (natp (fn-nntp-numbers-max-below current numbers))
  :rule-classes (:type-prescription :rewrite))

(defun fn-nntp-numbers-sort (numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (fn-nntp-insert-number (fn-ag-car numbers)
                             (fn-nntp-numbers-sort (fn-ag-cdr numbers)))
    nil))

(defconst *fn-nntp-index-all-low* 1)

(defconst *fn-nntp-index-all-high* 2147483647)

(defun fn-nntp-index-group-numbers (index group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-index-numbers
   (fn-index-query-range index group
                         *fn-nntp-index-all-low* *fn-nntp-index-all-high*)))

(defun fn-nntp-index-group-count (index group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-count (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-low (index group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-min (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-high (index group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-max (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-next-number (index group current)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-min-above current (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-last-number (index group current)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-max-below current (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-range-numbers (index group low high)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-sort
   (fn-nntp-index-numbers (fn-index-query-range index group low high))))

(verify-guards fn-nntp-index-msgid-okp)
(verify-guards fn-nntp-index-entry-available)
(verify-guards fn-nntp-index-numbers)
(verify-guards fn-nntp-numbers-count)
(verify-guards fn-nntp-numbers-min)
(verify-guards fn-nntp-numbers-max)
(verify-guards fn-nntp-numbers-min-above)
(verify-guards fn-nntp-numbers-max-below)
(verify-guards fn-nntp-numbers-sort)
(verify-guards fn-nntp-index-group-numbers)
(verify-guards fn-nntp-index-group-count)
(verify-guards fn-nntp-index-group-low)
(verify-guards fn-nntp-index-group-high)
(verify-guards fn-nntp-index-group-next-number)
(verify-guards fn-nntp-index-group-last-number)
(verify-guards fn-nntp-index-group-range-numbers)
