(in-package "ACL2")
(include-book "../../books/history-decode-stream")

; PRF-1102 reachable positive: every literal residual antecedent and its
; conclusion, with nonempty consumed digit and nonempty remaining suffix.
(assert-event
 (let ((c (fn-hdc-number-begin 2)) (byte 37) (suffix '(129)))
   (and (fn-hdc-numberp c) (posp (car c)) (natp byte)
        (equal (fn-hdc-number-value (fn-hdc-number-feed byte c) suffix)
               (fn-hdc-number-value c (cons byte suffix)))
        (equal (fn-hdc-number-value c (cons byte suffix)) 33061))))

; Literal hypothesis removal: zero remaining is a valid completed cursor;
; byte remains an octet; consuming it would change the represented value.
(assert-event
 (let ((c (fn-hdc-number-begin 0)) (byte 37) (suffix '(129)))
   (and (fn-hdc-numberp c) (not (posp (car c))) (natp byte)
        (not (equal (fn-hdc-number-value (ec-call (fn-hdc-number-feed byte c)) suffix)
                    (fn-hdc-number-value c (cons byte suffix)))))))

; Literal hypothesis removal: non-octet digit, valid live cursor. Negative
; input is fixed to zero by the old logical codec, not by the new arithmetic.
(assert-event
 (with-guard-checking :none
 (let ((c (fn-hdc-number-begin 2)) (byte -1) (suffix '(129)))
   (and (fn-hdc-numberp c) (posp (car c)) (not (natp byte))
        (not (equal (fn-hdc-number-value (ec-call (fn-hdc-number-feed byte c)) suffix)
                    (fn-hdc-number-value c (cons byte suffix))))))))

; Existing codec refinement, including nonminimal zero digits.
(assert-event
 (let ((bytes '(37 129 0)))
   (and (fn-scc-octet-listp bytes) (< (len bytes) 256)
        (equal (cadr (fn-hdc-number-run bytes (fn-hdc-number-begin (len bytes))))
               (car (fn-scc-read-nat (cons (len bytes) bytes)))))))

(defun fn-hdc-test-run (bytes s)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp bytes)
      (fn-hdc-test-run (cdr bytes) (fn-hdc-feed (car bytes) s))
    s))

(defun fn-hdc-test-trace (bytes s)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp bytes)
      (let ((next (fn-hdc-feed (car bytes) s)))
        (and (fn-hdc-statep s) (fn-scc-octetp (car bytes))
             (not (member-eq (nth 0 s) '(:done :refused)))
             (< (nth 7 s) (nth 8 s))
             (fn-hdc-statep next)
             (equal (nth 7 next) (+ 1 (nth 7 s)))
             (equal (nth 8 next) (nth 8 s))
             (equal (nth 10 next) (nth 10 s))
             (equal (nth 11 next) (nth 11 s))
             (fn-hdc-test-trace (cdr bytes) next)))
    (eq (nth 0 s) :done)))

; Two nonempty strings and a cons instruction cross opcode, length, payload
; and stack phases. Offsets are absolute in the borrowed immutable pool.
(defconst *fn-hdc-two-strings* '(3 1 3 65 66 67 3 1 2 68 69 5))
(assert-event
 (fn-hdc-test-trace *fn-hdc-two-strings* (fn-hdc-begin 100 12 9 17)))
(assert-event
 (let ((r (fn-hdc-test-run *fn-hdc-two-strings* (fn-hdc-begin 100 12 9 17))))
   (and (eq (nth 0 r) :done)
        (equal (nth 9 r)
               (list (fn-hdc-pair (fn-hdc-span 3 0 103 3)
                                  (fn-hdc-span 3 0 109 2)))))))

; Yield at an arbitrary payload cut and resume from exactly the saved state.
(assert-event
 (equal (fn-hdc-test-run (nthcdr 5 *fn-hdc-two-strings*)
                         (fn-hdc-test-run (take 5 *fn-hdc-two-strings*)
                                          (fn-hdc-begin 100 12 9 17)))
        (fn-hdc-test-run *fn-hdc-two-strings* (fn-hdc-begin 100 12 9 17))))

(assert-event
 (let ((r (fn-hdc-test-run '(4 0 1 3 70 79 79) (fn-hdc-begin 0 7 9 17))))
   (and (eq (nth 0 r) :done)
        (equal (nth 9 r) (list (fn-hdc-span 4 0 4 3))))))

; Malformed source refuses without a partial row: invalid package, truncated
; number/string and stack underflow. Empty opcode6 is valid current format.
(assert-event (eq (nth 0 (fn-hdc-test-run '(4 3 0) (fn-hdc-begin 0 3 9 17))) :refused))
(assert-event (eq (nth 0 (fn-hdc-test-run '(1 2 7) (fn-hdc-begin 0 3 9 17))) :refused))
(assert-event (eq (nth 0 (fn-hdc-test-run '(3 1 9 65) (fn-hdc-begin 0 4 9 17))) :refused))
(assert-event (eq (nth 0 (fn-hdc-test-run '(5) (fn-hdc-begin 0 1 9 17))) :refused))
(assert-event (eq (nth 0 (fn-hdc-test-run '(6 0) (fn-hdc-begin 0 2 9 17))) :done))

; Known tag recognition is a byte-wise equality with an existing keyword,
; never general interning. One mutation must preserve an opaque symbol span.
(assert-event
 (let ((r (fn-hdc-test-run '(4 0 1 5 72 83 84 88 65) (fn-hdc-begin 0 9 9 '(17 2)))))
   (and (eq (nth 0 r) :done)
        (equal (nth 9 r) (list (fn-hdc-atom :hstxa))))))
(assert-event
 (let ((r (fn-hdc-test-run '(4 0 1 5 72 83 85 88 65) (fn-hdc-begin 0 9 9 '(17 2)))))
   (and (eq (nth 0 r) :done)
        (equal (nth 9 r) (list (fn-hdc-span 4 0 4 5))))))

; Non-executable abstraction is evaluated by proof rewriting, never by a
; runtime materializer. Ground complete current-codec value compatibility.
(defthm fn-hdc-test-two-strings-refinement
  (let* ((bytes *fn-hdc-two-strings*)
         (s (fn-hdc-test-run bytes (fn-hdc-begin 0 (len bytes) 9 '(17 2)))))
    (and (eq (car (fn-scc-decode-tree bytes)) :ok)
         (fn-hdc-statep s) (eq (nth 0 s) :done)
         (equal (fn-hdc-abstract (car (nth 9 s)) bytes)
                (cadr (fn-scc-decode-tree bytes)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdc-abstract))))
