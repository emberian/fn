(in-package "ACL2")
(include-book "../../books/list-row-cursor")
(include-book "../../books/list-metadata-cursor")

; Test fuel detects a failure to settle; it never limits a served response.
(defun lsr-test-drain (cur fuel)
  (declare (xargs :mode :program :guard (natp fuel)))
  (if (not cur) (list :done nil)
    (if (zp fuel) (list :limit nil)
      (mv-let (octets next) (fn-lsr-one cur)
        (let ((answer (lsr-test-drain next (1- fuel))))
          (list (car answer) (append octets (cadr answer))))))))

(defun lsr-test-row (group summary countsp status)
  (declare (xargs :mode :program :guard t))
  (let ((actual (lsr-test-drain (fn-lsr-start group summary countsp status) 10000)))
    (and (equal (car actual) :done)
         (equal (cadr actual)
                (fn-nntp-stuff-lines (list (fn-lst-line group summary countsp status)))))))

(assert-event
 (and (lsr-test-row "fn.test" '(2 1 34) nil "y")
      (lsr-test-row "fn.test" '(2 1 34) t "m")
      (lsr-test-row ".dot" '(0 35 34) nil "n")
      (lsr-test-row "" '(0 0 0) t "y")
      (lsr-test-row nil '(0 0 0) t "y")
      (lsr-test-row "fn.test" '(9999999999 9999999999 9999999999) t "y")
      (lsr-test-row "fn.test" '(10000000000 10000000000 10000000000) t "y")
      (lsr-test-row "fn.test" '(1000000000000000000000000000000 -1 nope) t "m")))

; No whole string conversion is needed even when most of a row remains.
(defun lsr-test-long-reference ()
  (declare (xargs :mode :program :guard t))
  (let* ((text (coerce (make-list 20000 :initial-element #\a) 'string))
         (cur (fn-lsr-start text '(1 1 1) nil "y")))
    (mv-let (first next) (fn-lsr-one cur)
      (declare (ignore first))
      (mv-let (octets tail) (fn-lsr-one next)
        (and (eq (fn-cur-at 1 next) :text)
             (equal octets '(97))
             (equal (fn-cur-at 2 tail) 1))))))

(assert-event (lsr-test-long-reference))

(defun lsr-test-shape-teeth (cur)
  (declare (xargs :mode :program :guard t))
  (mv-let (octets next) (fn-lsr-one cur)
    (and (fn-lsr-statep cur) (fn-lsr-statep next)
         (<= (len octets) 1)
         (or (not next) (equal (len next) 7)))))

(defun lsr-test-corrupted-shape ()
  (declare (xargs :mode :program :guard t))
  (let ((cur (fn-lsr-make nil :digits 0 0 nil
                          (make-list 12 :initial-element 48) nil)))
    (mv-let (octets next) (fn-lsr-one cur)
      (declare (ignore octets))
      ; Removal witness for the sole carried-shape hypothesis. This corrupt
      ; state is not asserted reachable from the factory.
      (and (not (fn-lsr-statep cur)) (not (fn-lsr-statep next))))))

(assert-event
 (and (lsr-test-shape-teeth (fn-lsr-start ".dot" '(2 1 34) t "m"))
      (lsr-test-shape-teeth (fn-lsr-make '((:number 34)) :build 0 34 nil nil nil))
      (lsr-test-shape-teeth (fn-lsr-make nil :digits 0 0 nil '(51 52) nil))
      (lsr-test-corrupted-shape)))
