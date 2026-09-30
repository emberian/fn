(in-package "ACL2")
(include-book "../../books/history-symbol-normalize")

; Test-only source supplies use strings. The actual cursor receives a byte
; from its pinned authenticated span provider, never a materialized name.
(defun fn-hdsn-test-run (fuel name c ticks reads)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp fuel) (list :yield ticks reads c)
    (mv-let (verdict next) (fn-hdsn-tick c)
      (cond
       ((eq verdict :continue)
        (fn-hdsn-test-run (1- fuel) name next (+ 1 ticks) reads))
       ((and (consp verdict) (eq (car verdict) :need-byte))
        (mv-let (v supplied)
          (fn-hdsn-supply (cadr verdict) (caddr verdict)
                          (char-code (char name (nth 4 c))) next)
          (if (eq v :continue)
              (fn-hdsn-test-run (1- fuel) name supplied (+ 1 ticks) (+ 1 reads))
            (list v (+ 1 ticks) (+ 1 reads) supplied))))
       (t (list verdict (+ 1 ticks) reads next))))))

(defun fn-hdsn-test-case (pkg name)
  (declare (xargs :guard t :verify-guards nil))
  (fn-hdsn-test-run 100000 name (fn-hdsn-begin pkg 100 (length name)) 0 0))

; Accepted import spelling must canonicalize to the home package.
(assert-event (equal (car (fn-hdsn-test-case 1 "CAR")) '(:done (4 2))))
(assert-event (equal (car (fn-hdsn-test-case 1 "T")) '(:done (4 2))))
(assert-event (equal (car (fn-hdsn-test-case 2 "T")) '(:done (4 2))))
(assert-event (equal (car (fn-hdsn-test-case 0 "T")) '(:done (4 0))))

; NIL aliases become opcode0. Keyword NIL remains a non-NIL symbol.
(assert-event (equal (car (fn-hdsn-test-case 1 "NIL")) '(:done (0 0))))
(assert-event (equal (car (fn-hdsn-test-case 2 "NIL")) '(:done (0 0))))
(assert-event (equal (car (fn-hdsn-test-case 0 "NIL")) '(:done (4 0))))

; Unknown, empty and case-distinct names retain their borrowed spelling.
(assert-event (equal (car (fn-hdsn-test-case 1 "fn-private-name")) '(:done (4 1))))
(assert-event (equal (car (fn-hdsn-test-case 1 "nil")) '(:done (4 1))))
(assert-event (equal (car (fn-hdsn-test-case 2 "nil")) '(:done (4 2))))
(assert-event (equal (car (fn-hdsn-test-case 1 "")) '(:done (4 1))))

; Literal stale-reply antecedent and conclusion; a valid current request
; exists, but the offset or serial is not its issued coordinate.
(assert-event
 (let ((c (fn-hdsn-begin 2 100 3)))
   (and (fn-hdsn-statep c)
        (equal (nth 0 (mv-list 2 (fn-hdsn-tick c))) '(:need-byte 100 0))
        (not (equal 101 (+ (nth 1 c) (nth 4 c))))
        (equal (mv-list 2 (fn-hdsn-supply 101 0 78 c)) (list :refused c)))))
(assert-event
 (let ((c (fn-hdsn-begin 2 100 3)))
   (and (fn-hdsn-statep c)
        (not (equal 1 (nth 5 c)))
        (equal (mv-list 2 (fn-hdsn-supply 100 1 78 c)) (list :refused c)))))

; Removing the stale-coordinate hypothesis changes the complete outcome.
(assert-event
 (let ((c (fn-hdsn-begin 2 100 3)))
   (and (fn-hdsn-statep c)
        (equal 100 (+ (nth 1 c) (nth 4 c))) (equal 0 (nth 5 c))
        (not (equal (mv-list 2 (fn-hdsn-supply 100 0 78 c)) (list :refused c)))
        (equal (nth 0 (mv-list 2 (fn-hdsn-supply 100 0 78 c))) :continue)
        (equal (nth 4 (nth 1 (mv-list 2 (fn-hdsn-supply 100 0 78 c)))) 1))))

; Duplicate completion is stale after its first successful use.
(assert-event
 (let* ((c (fn-hdsn-begin 2 100 3))
        (next (nth 1 (mv-list 2 (fn-hdsn-supply 100 0 78 c)))))
   (and (fn-hdsn-statep next) (equal (nth 5 next) 1)
        (equal (mv-list 2 (fn-hdsn-supply 100 0 78 next)) (list :refused next)))))

; Yield/resume reuses the same immutable source identity, offset and serial.
(assert-event
 (let* ((c (fn-hdsn-begin 2 100 3))
        (cut (fn-hdsn-test-run 2 "NIL" c 0 0)))
   (and (eq (car cut) :yield)
        (equal (fn-hdsn-test-run 10 "NIL" (cadddr cut) (cadr cut) (caddr cut))
               (fn-hdsn-test-run 12 "NIL" c 0 0)))))

; Corrupted-state witness is distinct from accepted-source mutation.
(assert-event
 (let ((c (fn-hdsn-state 1 100 3 '(19) 0 0 nil)))
   (and (fn-hdsn-statep c) (equal (mv-list 2 (fn-hdsn-tick c)) (list :refused c)))))
(assert-event (equal (car (fn-hdsn-test-case 2 "NIM")) '(:done (4 2))))

; Non-executable denotation vocabulary is checked by ground proofs.
; This is a literal positive witness for every supply-refinement hypothesis.
(defthm fn-hdsn-test-supply-semantic-positive
  (let ((c (fn-hdsn-begin 2 100 3)) (name "NIL") (byte 78))
    (and (fn-hdsn-statep c) (stringp name) (equal (length name) (nth 2 c))
         (< (nth 4 c) (nth 2 c))
         (equal byte (char-code (char name (nth 4 c))))
         (equal (fn-hdsn-denote (nth 1 (mv-list 2 (fn-hdsn-supply 100 0 byte c))) name)
                (fn-hdsn-denote c name))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdsn-denote fn-hdsn-find))))

; Literal hypothesis removal: wrong source byte changes NIL into an ordinary
; symbol descriptor; all other supply-refinement hypotheses remain true.
(defthm fn-hdsn-test-supply-semantic-source-removal
  (let ((c (fn-hdsn-begin 2 100 3)) (name "NIL") (byte 77))
    (and (fn-hdsn-statep c) (stringp name) (equal (length name) (nth 2 c))
         (< (nth 4 c) (nth 2 c))
         (not (equal byte (char-code (char name (nth 4 c)))))
         (not (equal (fn-hdsn-denote (nth 1 (mv-list 2 (fn-hdsn-supply 100 0 byte c))) name)
                     (fn-hdsn-denote c name)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdsn-denote fn-hdsn-find))))

(defun fn-hdsn-test-table-cost (candidates)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp candidates)
      (+ 1 (length (symbol-name (car candidates)))
         (fn-hdsn-test-table-cost (cdr candidates)))
    0))

(assert-event
 (and (equal (len *fn-hdsn-acl2-imports*) 978)
      (equal (fn-hdsn-test-table-cost *fn-hdsn-acl2-imports*) 12249)
      (equal (take 3 (fn-hdsn-test-case 1 "CAR")) '((:done (4 2)) 160 9))
      (equal (take 3 (fn-hdsn-test-case 1 "NIL")) '((:done (0 0)) 611 29))
      (equal (take 3 (fn-hdsn-test-case 1 "fn-private-name")) '((:done (4 1)) 979 41))))

(defthm fn-hdsn-test-current-intern-positive
  (let ((pkg 1) (name "CAR"))
    (and (member-equal pkg '(0 1 2)) (stringp name)
         (equal (fn-hdsn-classify-name pkg name)
                (if (equal (fn-scc-intern pkg name) nil) '(0 0)
                  (list 4 (fn-scc-package-index
                           (symbol-package-name (fn-scc-intern pkg name))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdsn-classify-name))))

; Literal package hypothesis removal. The name remains a valid string;
; index3 is outside the exact current codec's three packages.
(defthm fn-hdsn-test-current-intern-package-removal
  (let ((pkg 3) (name "CAR"))
    (and (not (member-equal pkg '(0 1 2))) (stringp name)
         (not (equal (fn-hdsn-classify-name pkg name)
                     (if (equal (fn-scc-intern pkg name) nil) '(0 0)
                       (list 4 (fn-scc-package-index
                                (symbol-package-name (fn-scc-intern pkg name)))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdsn-classify-name))))
