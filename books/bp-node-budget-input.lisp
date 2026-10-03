; Operator text grammar; host performs only a bounded regular-file read.
; fn-bpnp-configured-budgets owns numeric policy/defaults, as before.
(in-package "ACL2")

(defun fn-bpnb-decimal (xs value digits)
  (declare (xargs :guard (and (natp value) (natp digits))))
  (if (consp xs)
      (if (and (integerp (car xs)) (<= 48 (car xs)) (<= (car xs) 57)
               (< digits 20))
          (fn-bpnb-decimal (cdr xs) (+ (* 10 value) (- (car xs) 48))
                           (1+ digits))
        nil)
    (and (null xs) (< 0 digits) value)))

(defun fn-bpnb-row (line key)
  (declare (xargs :guard (true-listp key)))
  (if (consp line)
      (if (equal (car line) 32)
          (let ((value (fn-bpnb-decimal (cdr line) 0 0)))
            (and value (list (reverse key) value)))
        (fn-bpnb-row (cdr line) (cons (car line) key)))
    nil))

(defun fn-bpnb-install-row (line rows)
  (declare (xargs :guard (true-listp rows)))
  (if (null line) rows
    (let ((row (fn-bpnb-row line nil)))
      (cond
       ((and row (equal (car row) '(111 119 110 101 114 45 98 97 99 107 111 102 102)))
        (if (second rows) nil (list :rows (second row) (third rows))))
       ((and row (equal (car row) '(114 101 116 114 121 45 98 117 100 103 101 116)))
        (if (third rows) nil (list :rows (second rows) (second row))))
       (t nil)))))

(defun fn-bpnb-lines (xs reverse-line rows)
  (declare (xargs :guard (and (true-listp reverse-line) (true-listp rows))))
  (if (consp xs)
      (if (equal (car xs) 10)
          (let ((next (fn-bpnb-install-row (reverse reverse-line) rows)))
            (and next (fn-bpnb-lines (cdr xs) nil next)))
        (fn-bpnb-lines (cdr xs) (cons (car xs) reverse-line) rows))
    (and (null xs) (fn-bpnb-install-row (reverse reverse-line) rows))))

(defun fn-bpnb-read (octets)
  (declare (xargs :guard t))
  (if (<= (len octets) 256)
      (fn-bpnb-lines octets nil '(:rows nil nil))
    nil))

; Once either row is installed, another row under that same name is refused
; regardless of its value. Empty lines do not count as rows.
(defthm fn-bpnb-installed-backoff-refuses-another-backoff
  (implies (and (second rows)
                (equal (car (fn-bpnb-row line nil))
                       '(111 119 110 101 114 45 98 97 99 107 111 102 102)))
           (not (fn-bpnb-install-row line rows)))
  :hints (("Goal" :in-theory (enable fn-bpnb-install-row))))

(defthm fn-bpnb-installed-retries-refuses-another-retries
  (implies (and (third rows)
                (equal (car (fn-bpnb-row line nil))
                       '(114 101 116 114 121 45 98 117 100 103 101 116)))
           (not (fn-bpnb-install-row line rows)))
  :hints (("Goal" :in-theory (enable fn-bpnb-install-row))))

(defthm fn-bpnb-input-past-read-bound-is-refused
  (implies (< 256 (len octets)) (not (fn-bpnb-read octets))))
