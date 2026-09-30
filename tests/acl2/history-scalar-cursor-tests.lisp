(in-package "ACL2")
(include-book "../../books/history-scalar-cursor")

(defun fn-hrsc-test-run (fuel c)
  (declare (xargs :guard (natp fuel)))
  (if (zp fuel) (list :yield nil c)
    (mv-let (v b next) (fn-hrsc-tick c)
      (cond ((eq v :emit)
             (let ((r (fn-hrsc-test-run (1- fuel) next)))
               (list (car r) (cons b (cadr r)) (caddr r))))
            ((eq v :continue) (fn-hrsc-test-run (1- fuel) next))
            (t (list v nil next))))))

; At every actually reached phase this checks every literal antecedent and
; complete conclusion of preservation, residual, octet and progress theorems.
(defun fn-hrsc-test-tracep (fuel c)
  (declare (xargs :guard (natp fuel) :verify-guards nil))
  (if (zp fuel) nil
    (mv-let (v b next) (fn-hrsc-tick c)
      (and (fn-hrsc-invariantp c) (fn-hrsc-invariantp next)
           (equal (fn-hrsc-field 8 next) (fn-hrsc-field 8 c))
           (equal (fn-hrsc-field 9 next) (fn-hrsc-field 9 c))
           (member-eq v '(:continue :emit :prepared))
           (equal (fn-hrsc-rest c)
                  (if (eq v :emit) (cons b (fn-hrsc-rest next)) (fn-hrsc-rest next)))
           (or (not (eq v :emit)) (fn-scc-octetp b))
           (or (not (eq v :prepared)) (equal (fn-hrsc-rest next) nil))
           (or (eq (fn-hrsc-field 0 c) :done)
               (< (fn-hrsc-work next) (fn-hrsc-work c)))
           (if (eq v :prepared) t (fn-hrsc-test-tracep (1- fuel) next))))))

(defun fn-hrsc-test-positive (x fuel)
  (declare (xargs :guard (natp fuel) :verify-guards nil))
  (let* ((c (fn-hrsc-begin x '(:capture 31 5) '(:maintenance 19)))
         (r (fn-hrsc-test-run fuel c)))
    (and (fn-hrsc-domainp x)
         (fn-hrsc-invariantp c)
         (equal (fn-hrsc-rest c) (fn-scc-atom-octets x))
         (fn-hrsc-test-tracep fuel c)
         (equal (car r) :prepared)
         (equal (cadr r) (fn-scc-atom-octets x))
         (equal (fn-hrsc-field 8 (caddr r)) '(:capture 31 5))
         (equal (fn-hrsc-field 9 (caddr r)) '(:maintenance 19)))))

(assert-event (fn-hrsc-test-positive "captured string" 40))
(assert-event (fn-hrsc-test-positive :snapshot 40))
(assert-event (fn-hrsc-test-positive 'fn-scc-atom-octets 50))
(assert-event (fn-hrsc-test-positive 'car 30))
(assert-event (fn-hrsc-test-positive #\Z 12))
(assert-event (fn-hrsc-test-positive nil 12))
(assert-event (fn-hrsc-test-positive "" 12))
(assert-event (fn-hrsc-test-positive 0 12))
(assert-event (fn-hrsc-test-positive 255 15))
(assert-event (fn-hrsc-test-positive 256 15))
(assert-event (fn-hrsc-test-positive -1 12))
(assert-event (fn-hrsc-test-positive -257 15))
; Current codec maximum: 255 digits, not a newly introduced narrower cap.
(assert-event (fn-hrsc-test-positive (- (expt 256 255) 1) 530))
(assert-event (fn-hrsc-test-positive (- (expt 256 255)) 530))

; Scheduling exhaustion preserves a cursor and all emitted bytes.
(assert-event
 (let* ((c (fn-hrsc-begin "a string across a yield" :capture :lease))
        (a (fn-hrsc-test-run 10 c))
        (b (fn-hrsc-test-run 40 (caddr a))))
   (and (equal (car a) :yield) (equal (car b) :prepared)
        (equal (append (cadr a) (cadr b))
               (fn-scc-atom-octets "a string across a yield")))))

; Initial-refinement hypothesis removal: unsupported rational, no remaining
; hypotheses. The invariant conjunct of the literal conclusion fails.
(assert-event
 (let* ((x 1/2) (c (fn-hrsc-begin x :capture :lease)))
   (and (not (fn-hrsc-domainp x))
        (not (and (fn-hrsc-invariantp c)
                  (equal (fn-hrsc-rest c) (fn-scc-atom-octets x)))))))

; Invariant-preservation hypothesis removal, corrupted initial source.
(assert-event
 (let ((c (fn-hrsc-begin '(1 . 2) :capture :lease)))
   (mv-let (v b next) (fn-hrsc-tick c)
     (declare (ignore v b))
     (and (not (fn-hrsc-invariantp c)) (not (fn-hrsc-invariantp next))))))

; Residual hypothesis removal: width field is corrupted. All outer shape
; checks pass; emitting a wrong prefix fails the literal residual equation.
(assert-event
 (let ((c '(:width 1 nil 1 0 2 "" 0 :capture :lease)))
   (mv-let (v b next) (fn-hrsc-tick c)
     (and (fn-hrsc-shapep c) (not (fn-hrsc-invariantp c))
          (not (equal (fn-hrsc-rest c)
                      (if (eq v :emit) (cons b (fn-hrsc-rest next))
                        (fn-hrsc-rest next))))))))

; Progress hypothesis removal: invariant omitted, non-done retained.
(assert-event
 (let ((c '(:refused nil nil 0 0 0 "" 0 :capture :lease)))
   (mv-let (v b next) (fn-hrsc-tick c)
     (declare (ignore v b))
     (and (not (fn-hrsc-invariantp c))
          (not (eq (fn-hrsc-field 0 c) :done))
          (not (< (fn-hrsc-work next) (fn-hrsc-work c)))))))
; Non-done omitted, invariant retained: terminal idempotence has no decrease.
(assert-event
 (let ((c '(:done nil nil 0 0 0 "" 0 :capture :lease)))
   (mv-let (v b next) (fn-hrsc-tick c)
     (declare (ignore v b))
     (and (fn-hrsc-invariantp c) (eq (fn-hrsc-field 0 c) :done)
          (not (< (fn-hrsc-work next) (fn-hrsc-work c)))))))
; Octet theorem hypothesis removal: terminal calls have no emitted byte.
(assert-event
 (let ((c '(:done nil nil 0 0 0 "" 0 :capture :lease)))
   (mv-let (v b next) (fn-hrsc-tick c)
     (declare (ignore next))
     (and (not (eq v :emit)) (not (fn-scc-octetp b))))))

; Explicit current-format refusal, never accepted truncation.
(assert-event
 (let ((r (fn-hrsc-test-run 270 (fn-hrsc-begin (expt 256 255) :capture :lease))))
   (and (equal (car r) '(:refused :codec-width)) (equal (cadr r) nil)
        (equal (fn-hrsc-field 8 (caddr r)) :capture)
        (equal (fn-hrsc-field 9 (caddr r)) :lease))))
; Unconditional identity theorem also covers a malformed cursor.
(assert-event
 (let ((c '(:unknown nil nil 0 0 0 "" 0 (:capture 5) (:lease 7))))
   (mv-let (v b next) (fn-hrsc-tick c)
     (declare (ignore b))
     (and (equal v '(:refused :cursor))
          (equal (fn-hrsc-field 8 next) (fn-hrsc-field 8 c))
          (equal (fn-hrsc-field 9 next) (fn-hrsc-field 9 c))))))
