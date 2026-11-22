; Capacity of owner-activated client rows and their private format slots.
(in-package "ACL2")
(include-book "profile")
(include-book "article-limit-text")

(defun fn2-peer-pull-capacity (profile)
 (declare (xargs :guard t))
 (let ((n (fn2-profile-get :peer-pull-slots profile)))
   (if (unsigned-byte-p 32 n) n 0)))
(defthm fn2-peer-pull-capacity-natp
 (natp (fn2-peer-pull-capacity profile)) :rule-classes :type-prescription)

(defun fn2-peer-pull-profile-from-text (profile slots)
 (declare (xargs :guard t))
 (if slots (put-assoc-equal :peer-pull-slots (fn2-article-limit-decimal slots)
                            (if (alistp profile) profile nil))
   profile))

(defun fn2-peer-pull-profilep (profile)
 (declare (xargs :guard t))
 (or (not (alistp profile)) (not (assoc-equal :peer-pull-slots profile))
     (let ((n (fn2-profile-get :peer-pull-slots profile))
           (classes (fn2-profile-pool-classes profile)))
       (and (unsigned-byte-p 32 n)
            (or (zp n)
                (and (<= (+ n (nfix (fn2-profile-get :authority profile))
                              (nfix (fn2-profile-get :cns profile)))
                         (nfix (fn2-profile-t profile)))
                     (consp classes) (consp (car classes))
                     (<= 3 (nfix (caar classes))) (<= 512 (nfix (cdar classes)))))))))

(assert-event
 (let ((p '((:peer-pull-slots . 1) (:authority . 1) (:cns . 1) (:t . 3)
            (:pool-classes . ((3 . 512))))))
   (and (fn2-peer-pull-profilep p)
        (not (fn2-peer-pull-profilep (put-assoc-equal :t 2 p)))
        (not (fn2-peer-pull-profilep (put-assoc-equal :peer-pull-slots :invalid p)))
        (fn2-peer-pull-profilep (put-assoc-equal :peer-pull-slots 0 p)))))
