(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-lg-fit-count-loop (records used acc)
  (declare (xargs :guard (and (natp used) (acl2-numberp acc)) :verify-guards nil))
  (if (and (consp records)
           (<= (+ (nfix used) 4 (len (car records))) *fn-frame-max-payload*))
      (fn-lg-fit-count-loop (cdr records)
                            (+ (nfix used) 4 (len (car records)))
                            (+ 1 acc))
    (+ acc 0)))

(defun fn-lg-fit-count (records used)
  (declare (xargs :verify-guards nil :guard (natp used)))
  (mbe :logic
       (if (and (consp records)
                (<= (+ (nfix used) 4 (len (car records))) *fn-frame-max-payload*))
           (1+ (fn-lg-fit-count (cdr records) (+ (nfix used) 4 (len (car records)))))
         0)
       :exec (fn-lg-fit-count-loop records used 0)))

(local
 (defthm fn-lg-fit-count-loop-is-plus
   (implies (acl2-numberp acc)
            (equal (fn-lg-fit-count-loop records used acc)
                   (+ acc (fn-lg-fit-count records used))))
   :hints (("Goal" :induct (fn-lg-fit-count-loop records used acc)))))

(verify-guards fn-lg-fit-count-loop)

(verify-guards fn-lg-fit-count
  :hints (("Goal"
           :in-theory
           (disable fn-lg-fit-count-loop)
           :use
           ((:instance fn-lg-fit-count-loop-is-plus (acc 0))))))
