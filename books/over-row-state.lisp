; Exact shared six-field row continuation constructors. PRF-1066.
(in-package "ACL2")
(include-book "over-cursor-shape")

; (range origin-pin phase parser pieces string-position). The six original
; range fields keep their meanings; the pin is a separate coordinate.
(defun fn-obc-make (range pin phase parser pieces pos)
  (declare (xargs :guard t))
  (list range pin phase parser pieces pos))

(defun fn-obc-begin (range pin)
  (declare (xargs :guard t))
  (fn-obc-make range pin :seek nil nil 0))

(defun fn-obc-next-range (range owed)
  (declare (xargs :guard (true-listp range)))
  (fn-ovw-cursor (nth 0 range) (+ 1 (nfix (nth 1 range)))
                 (nth 2 range) (nth 3 range) (nth 4 range) owed))

(defun fn-obc-row-ready (range pin pieces)
  (declare (xargs :guard (true-listp range)))
  (fn-obc-make (fn-obc-next-range range nil) pin :emit nil
              (if (nth 5 range)
                  (cons (fn-ovw-status (fn-proto-text * :overview)) pieces)
                pieces)
              0))

