(in-package "ACL2")
(include-book "../../books/history-record-cursor")

(defun fn-hrcur-test-run (fuel c)
  (declare (xargs :guard (natp fuel)))
  (if (zp fuel) (list :yield c nil)
    (mv-let (verdict octet next) (fn-hrcur-leaf-tick c)
      (cond ((eq verdict :prepared) (list :prepared next nil))
            ((eq verdict :emit)
             (let ((rest (fn-hrcur-test-run (1- fuel) next)))
               (list (car rest) (cadr rest) (cons octet (caddr rest)))))
            ((eq verdict :continue) (fn-hrcur-test-run (1- fuel) next))
            (t (list verdict next nil))))))

(defconst *fn-hrcur-test-leaf* '(0 127 255))
(defconst *fn-hrcur-test-begin*
  (fn-hrcur-leaf-begin *fn-hrcur-test-leaf* '(:captured 31 7) '(:lease 19)))

; PRF-1088 reachable-positive: all literal initial-refinement hypotheses.
(assert-event
 (and (consp *fn-hrcur-test-leaf*)
      (fn-scc-octet-listp *fn-hrcur-test-leaf*)
      (< (+ (len *fn-hrcur-test-leaf*) 2
            (len (fn-scc-le-digits (len *fn-hrcur-test-leaf*))))
         *fn-hrcur-u64-bound*)
      (fn-hrcur-leaf-invariantp *fn-hrcur-test-begin*)
      (equal (fn-hrcur-leaf-rest *fn-hrcur-test-begin*)
             (fn-scc-encode *fn-hrcur-test-leaf*))))

; Every reached count/prefix/body/done state checks the complete invariant,
; byte/refusal verdict and literal exact residual theorem.
(defun fn-hrcur-test-tracep (fuel c)
  (declare (xargs :guard (natp fuel) :verify-guards nil))
  (if (zp fuel) t
    (mv-let (verdict octet next) (fn-hrcur-leaf-tick c)
      (and (fn-hrcur-leaf-invariantp c)
           (fn-hrcur-leaf-invariantp next)
           (member-eq verdict '(:continue :emit :prepared))
           (implies (eq verdict :emit) (fn-scc-octetp octet))
           (equal (fn-hrcur-leaf-rest c)
                  (if (eq verdict :emit)
                      (cons octet (fn-hrcur-leaf-rest next))
                    (fn-hrcur-leaf-rest next)))
           (equal (fn-hrcur-field 5 next) (fn-hrcur-field 5 c))
           (equal (fn-hrcur-field 6 next) (fn-hrcur-field 6 c))
           (fn-hrcur-test-tracep (1- fuel) next)))))

(assert-event (fn-hrcur-test-tracep 15 *fn-hrcur-test-begin*))
(assert-event
 (let ((result (fn-hrcur-test-run 12 *fn-hrcur-test-begin*)))
   (and (equal (car result) :prepared)
        (equal (caddr result) (fn-scc-encode *fn-hrcur-test-leaf*))
        (equal (fn-hrcur-field 5 (cadr result)) '(:captured 31 7))
        (equal (fn-hrcur-field 6 (cadr result)) '(:lease 19)))))

; Yield is resumable; it does not silently truncate the record.
(assert-event
 (let* ((first (fn-hrcur-test-run 7 *fn-hrcur-test-begin*))
        (second (fn-hrcur-test-run 7 (cadr first))))
   (and (equal (car first) :yield) (equal (car second) :prepared)
        (equal (append (caddr first) (caddr second))
               (fn-scc-encode *fn-hrcur-test-leaf*)))))

; Literal hypothesis-removal: sole tick-invariant hypothesis fails,
; as do preservation and its permitted-verdict conjunct. Corrupted state,
; never asserted producer-reachable.
(assert-event
 (let ((bad '(:prefix nil (3) 1 (300) :capture :lease)))
   (mv-let (verdict octet next) (fn-hrcur-leaf-tick bad)
     (declare (ignore octet))
     (and (not (fn-hrcur-leaf-invariantp bad))
          (not (fn-hrcur-leaf-invariantp next))
          (not (member-eq verdict '(:continue :emit :prepared)))))))

; Literal hypothesis-removal for residual refinement: invalid count relation
; reaches the zero-length refusal, losing the nonempty residual.
(assert-event
 (let ((bad '(:count nil (8 9) 0 nil :capture :lease)))
   (mv-let (verdict octet next) (fn-hrcur-leaf-tick bad)
     (and (not (fn-hrcur-leaf-invariantp bad))
          (not (equal (fn-hrcur-leaf-rest bad)
                      (if (eq verdict :emit)
                          (cons octet (fn-hrcur-leaf-rest next))
                        (fn-hrcur-leaf-rest next))))))))

; Existing tree codec treats NIL and a non-octet list differently from an
; opaque leaf. Their positive retained bound hypothesis holds; the omitted
; nonempty / octet hypothesis and the exact encode conclusion fail.
(assert-event
 (let ((x nil))
   (and (fn-scc-octet-listp x) (not (consp x))
        (< (+ (len x) 2 (len (fn-scc-le-digits (len x)))) *fn-hrcur-u64-bound*)
        (not (equal (fn-hrcur-leaf-rest (fn-hrcur-leaf-begin x :c :l))
                    (fn-scc-encode x))))))
(assert-event
 (let ((x '(300)))
   (and (consp x) (not (fn-scc-octet-listp x))
        (< (+ (len x) 2 (len (fn-scc-le-digits (len x)))) *fn-hrcur-u64-bound*)
        (not (equal (fn-hrcur-leaf-rest (fn-hrcur-leaf-begin x :c :l))
                    (fn-scc-encode x))))))
