(in-package "ACL2")
(include-book "../../books/history-normalized-span")

(defun fn-hrcur-test-ns-run (fuel c pool)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (list :yield nil c)
    (mv-let (verdict byte next) (fn-hrcur-span-tick c)
      (cond ((eq verdict :prepared) (list :prepared nil next))
            ((eq verdict :emit)
             (let ((rest (fn-hrcur-test-ns-run (1- fuel) next pool)))
               (list (car rest) (cons byte (cadr rest)) (caddr rest))))
            ((eq verdict :continue) (fn-hrcur-test-ns-run (1- fuel) next pool))
            ((and (consp verdict) (eq (car verdict) :need-byte))
             (mv-let (sv sb sn)
               (fn-hrcur-span-supply next (cadr verdict) (nth (cadr verdict) pool))
               (if (eq sv :emit)
                   (let ((rest (fn-hrcur-test-ns-run (1- fuel) sn pool)))
                     (list (car rest) (cons sb (cadr rest)) (caddr rest)))
                 (list sv nil sn))))
            (t (list verdict nil next))))))

(defthm fn-hrcur-test-ns-imported-car
  (and (member-equal 1 '(0 1 2)) (fn-scc-octet-listp '(9 67 65 82 9)) (natp 1) (natp 3) (< (+ 1 3) *fn-hrcur-u64-bound*) (<= (+ 1 3) (len '(9 67 65 82 9))) (equal '(4 2) (fn-hdsn-classify-name 1 (coerce (fn-scc-octets-chars (take 3 (nthcdr 1 '(9 67 65 82 9)))) 'string)))
       (and (fn-hrcur-span-invariantp (fn-hrcur-ns-begin '(4 2) 1 3 :capture :lease) '(9 67 65 82 9))
                (equal (fn-hrcur-span-rest (fn-hrcur-ns-begin '(4 2) 1 3 :capture :lease) '(9 67 65 82 9))
                       (fn-scc-encode (fn-hdc-abstract (fn-hdc-span 4 1 1 3) '(9 67 65 82 9))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hdsn-classify-name fn-hdc-abstract fn-hdc-span fn-scc-intern)
                                   (fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire)))))

(defthm fn-hrcur-test-ns-nil-alias
  (and (member-equal 1 '(0 1 2)) (fn-scc-octet-listp '(78 73 76)) (natp 0) (natp 3) (< (+ 0 3) *fn-hrcur-u64-bound*) (<= (+ 0 3) (len '(78 73 76))) (equal '(0 0) (fn-hdsn-classify-name 1 (coerce (fn-scc-octets-chars (take 3 (nthcdr 0 '(78 73 76)))) 'string)))
       (and (fn-hrcur-span-invariantp (fn-hrcur-ns-begin '(0 0) 0 3 :capture :lease) '(78 73 76))
                (equal (fn-hrcur-span-rest (fn-hrcur-ns-begin '(0 0) 0 3 :capture :lease) '(78 73 76))
                       (fn-scc-encode (fn-hdc-abstract (fn-hdc-span 4 1 0 3) '(78 73 76))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hdsn-classify-name fn-hdc-abstract fn-hdc-span fn-scc-intern)
                                   (fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire)))))

(defthm fn-hrcur-test-ns-keyword-nil
  (and (member-equal 0 '(0 1 2)) (fn-scc-octet-listp '(78 73 76)) (natp 0) (natp 3) (< (+ 0 3) *fn-hrcur-u64-bound*) (<= (+ 0 3) (len '(78 73 76))) (equal '(4 0) (fn-hdsn-classify-name 0 (coerce (fn-scc-octets-chars (take 3 (nthcdr 0 '(78 73 76)))) 'string)))
       (and (fn-hrcur-span-invariantp (fn-hrcur-ns-begin '(4 0) 0 3 :capture :lease) '(78 73 76))
                (equal (fn-hrcur-span-rest (fn-hrcur-ns-begin '(4 0) 0 3 :capture :lease) '(78 73 76))
                       (fn-scc-encode (fn-hdc-abstract (fn-hdc-span 4 0 0 3) '(78 73 76))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hdsn-classify-name fn-hdc-abstract fn-hdc-span fn-scc-intern)
                                   (fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire)))))

(defthm fn-hrcur-test-ns-unmatched-acl2
  (and (member-equal 1 '(0 1 2)) (fn-scc-octet-listp '(90 90 90 90)) (natp 0) (natp 4) (< (+ 0 4) *fn-hrcur-u64-bound*) (<= (+ 0 4) (len '(90 90 90 90))) (equal '(4 1) (fn-hdsn-classify-name 1 (coerce (fn-scc-octets-chars (take 4 (nthcdr 0 '(90 90 90 90)))) 'string)))
       (and (fn-hrcur-span-invariantp (fn-hrcur-ns-begin '(4 1) 0 4 :capture :lease) '(90 90 90 90))
                (equal (fn-hrcur-span-rest (fn-hrcur-ns-begin '(4 1) 0 4 :capture :lease) '(90 90 90 90))
                       (fn-scc-encode (fn-hdc-abstract (fn-hdc-span 4 1 0 4) '(90 90 90 90))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hdsn-classify-name fn-hdc-abstract fn-hdc-span fn-scc-intern)
                                   (fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire)))))

(defthm fn-hrcur-test-ns-wrong-descriptor
  (and (member-equal 1 '(0 1 2)) (fn-scc-octet-listp '(67 65 82)) (natp 0) (natp 3) (< (+ 0 3) *fn-hrcur-u64-bound*) (<= (+ 0 3) (len '(67 65 82))) (not (equal '(4 1) (fn-hdsn-classify-name 1 (coerce (fn-scc-octets-chars (take 3 (nthcdr 0 '(67 65 82)))) 'string))))
       (not (and (fn-hrcur-span-invariantp (fn-hrcur-ns-begin '(4 1) 0 3 :capture :lease) '(67 65 82))
                (equal (fn-hrcur-span-rest (fn-hrcur-ns-begin '(4 1) 0 3 :capture :lease) '(67 65 82))
                       (fn-scc-encode (fn-hdc-abstract (fn-hdc-span 4 1 0 3) '(67 65 82)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hdsn-classify-name fn-hdc-abstract fn-hdc-span fn-scc-intern)
                                   (fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire)))))

(defthm fn-hrcur-test-ns-package-removal
  (and (not (member-equal 3 '(0 1 2))) (fn-scc-octet-listp '(67 65 82)) (natp 0) (natp 3) (< (+ 0 3) *fn-hrcur-u64-bound*) (<= (+ 0 3) (len '(67 65 82))) (equal '(4 3) (fn-hdsn-classify-name 3 (coerce (fn-scc-octets-chars (take 3 (nthcdr 0 '(67 65 82)))) 'string)))
       (not (and (fn-hrcur-span-invariantp (fn-hrcur-ns-begin '(4 3) 0 3 :capture :lease) '(67 65 82))
                (equal (fn-hrcur-span-rest (fn-hrcur-ns-begin '(4 3) 0 3 :capture :lease) '(67 65 82))
                       (fn-scc-encode (fn-hdc-abstract (fn-hdc-span 4 3 0 3) '(67 65 82)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hdsn-classify-name fn-hdc-abstract fn-hdc-span fn-scc-intern)
                                   (fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire)))))

(defthm fn-hrcur-test-ns-pool-removal
  (and (member-equal 0 '(0 1 2)) (not (fn-scc-octet-listp '(300))) (natp 0) (natp 1) (< (+ 0 1) *fn-hrcur-u64-bound*) (<= (+ 0 1) (len '(300))) (equal '(4 0) (fn-hdsn-classify-name 0 (coerce (fn-scc-octets-chars (take 1 (nthcdr 0 '(300)))) 'string)))
       (not (and (fn-hrcur-span-invariantp (fn-hrcur-ns-begin '(4 0) 0 1 :capture :lease) '(300))
                (equal (fn-hrcur-span-rest (fn-hrcur-ns-begin '(4 0) 0 1 :capture :lease) '(300))
                       (fn-scc-encode (fn-hdc-abstract (fn-hdc-span 4 0 0 1) '(300)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hdsn-classify-name fn-hdc-abstract fn-hdc-span fn-scc-intern)
                                   (fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire)))))

(defthm fn-hrcur-test-ns-offset-removal
  (and (member-equal 1 '(0 1 2)) (fn-scc-octet-listp '(67 65 82)) (not (natp -1)) (natp 3) (< (+ -1 3) *fn-hrcur-u64-bound*) (<= (+ -1 3) (len '(67 65 82))) (equal '(4 2) (fn-hdsn-classify-name 1 (coerce (fn-scc-octets-chars (take 3 (nthcdr -1 '(67 65 82)))) 'string)))
       (not (and (fn-hrcur-span-invariantp (fn-hrcur-ns-begin '(4 2) -1 3 :capture :lease) '(67 65 82))
                (equal (fn-hrcur-span-rest (fn-hrcur-ns-begin '(4 2) -1 3 :capture :lease) '(67 65 82))
                       (fn-scc-encode (fn-hdc-abstract (fn-hdc-span 4 1 -1 3) '(67 65 82)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hdsn-classify-name fn-hdc-abstract fn-hdc-span fn-scc-intern)
                                   (fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire)))))

(defthm fn-hrcur-test-ns-count-removal
  (and (member-equal 0 '(0 1 2)) (fn-scc-octet-listp '(67 65 82)) (natp 0) (not (natp -1)) (< (+ 0 -1) *fn-hrcur-u64-bound*) (<= (+ 0 -1) (len '(67 65 82))) (equal '(4 0) (fn-hdsn-classify-name 0 (coerce (fn-scc-octets-chars (take -1 (nthcdr 0 '(67 65 82)))) 'string)))
       (not (and (fn-hrcur-span-invariantp (fn-hrcur-ns-begin '(4 0) 0 -1 :capture :lease) '(67 65 82))
                (equal (fn-hrcur-span-rest (fn-hrcur-ns-begin '(4 0) 0 -1 :capture :lease) '(67 65 82))
                       (fn-scc-encode (fn-hdc-abstract (fn-hdc-span 4 0 0 -1) '(67 65 82)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hdsn-classify-name fn-hdc-abstract fn-hdc-span fn-scc-intern)
                                   (fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire)))))

(defthm fn-hrcur-test-ns-fits-removal
  (and (member-equal 0 '(0 1 2)) (fn-scc-octet-listp '(67 65 82)) (natp 0) (natp 4) (< (+ 0 4) *fn-hrcur-u64-bound*) (not (<= (+ 0 4) (len '(67 65 82)))) (equal '(4 0) (fn-hdsn-classify-name 0 (coerce (fn-scc-octets-chars (take 4 (nthcdr 0 '(67 65 82)))) 'string)))
       (not (and (fn-hrcur-span-invariantp (fn-hrcur-ns-begin '(4 0) 0 4 :capture :lease) '(67 65 82))
                (equal (fn-hrcur-span-rest (fn-hrcur-ns-begin '(4 0) 0 4 :capture :lease) '(67 65 82))
                       (fn-scc-encode (fn-hdc-abstract (fn-hdc-span 4 0 0 4) '(67 65 82)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hdsn-classify-name fn-hdc-abstract fn-hdc-span fn-scc-intern)
                                   (fn-hrcur-span-tick-refines-wire fn-hrcur-span-supply-refines-wire)))))

; Yield/resume drives the actual span child, not a new byte emitter.
(assert-event
 (let* ((pool '(9 67 65 82 9))
        (c (fn-hrcur-ns-begin '(4 2) 1 3 '(:epoch :pass :row) :lease))
        (first (fn-hrcur-test-ns-run 5 c pool))
        (second (fn-hrcur-test-ns-run 10 (caddr first) pool)))
   (and (eq (car first) :yield) (eq (car second) :prepared)
        (equal (append (cadr first) (cadr second)) (fn-scc-encode 'car))
        (fn-hrcur-span-invariantp (caddr second) pool)
        (equal (fn-hrcur-field 4 (caddr second)) '(:epoch :pass :row))
        (equal (fn-hrcur-field 5 (caddr second)) :lease))))
(assert-event
 (let* ((c (fn-hrcur-ns-begin '(0 0) 0 3 :capture :lease))
        (run (fn-hrcur-test-ns-run 3 c '(78 73 76))))
   (and (equal (fn-hrcur-field 3 c) 0)
        (eq (car run) :prepared) (equal (cadr run) '(0))
        (equal (fn-hrcur-field 2 (caddr run)) 0))))
; The initial u64 sum removal needs a pool of at least 2^64 octets and has
; no practical fixture. Auxiliary wire/domain teeth remain separately open.

(assert-event
 (let ((capture '(:epoch :pass :row)) (lease '(:capture-ticket :count)))
   (and (equal (fn-hrcur-field 4 (fn-hrcur-ns-begin '(0 0) 0 3 capture lease)) capture)
        (equal (fn-hrcur-field 5 (fn-hrcur-ns-begin '(0 0) 0 3 capture lease)) lease)
        (equal (fn-hrcur-field 4 (fn-hrcur-ns-begin '(:invalid) -1 3 capture lease)) capture)
        (equal (fn-hrcur-field 5 (fn-hrcur-ns-begin '(:invalid) -1 3 capture lease)) lease))))
