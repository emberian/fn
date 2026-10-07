(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-pb-upto-semicolon-loop (rev acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rev)
      (fn-pb-upto-semicolon-loop (cdr rev)
                                 (if (equal (car rev) 59)
                                     nil
                                   (let ((rest acc))
                                     (if (equal rest :no) :no (cons (car rev) rest)))))
    acc))

(defun fn-pb-upto-semicolon (r)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp r)
           (if (equal (car r) 59)
               nil
             (let ((rest (fn-pb-upto-semicolon (cdr r))))
               (if (equal rest :no) :no (cons (car r) rest))))
         :no)
       :exec (fn-pb-upto-semicolon-loop (fn-ag-rev-onto r nil) :no)))

(local
 (defthm fn-pb-upto-semicolon-loop-of-rev-onto
   (equal (fn-pb-upto-semicolon-loop (fn-ag-rev-onto r zs) :no)
          (fn-pb-upto-semicolon-loop zs (fn-pb-upto-semicolon r)))
   :hints (("Goal" :induct (fn-ag-rev-onto r zs)
                   :in-theory (union-theories '(fn-pb-upto-semicolon-loop fn-pb-upto-semicolon fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-pb-upto-semicolon-loop)

(verify-guards fn-pb-upto-semicolon
  :hints (("Goal" :in-theory (union-theories '(fn-pb-upto-semicolon fn-pb-upto-semicolon-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-pb-upto-semicolon-loop-of-rev-onto (zs nil))))))
