; fn: the article-record stamp derived solely from an owner observation.
(in-package "ACL2")
(include-book "records-shape")
(include-book "clock")

(defun fn-record-stamp-of-observation (obs)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-clock-observationp
                                                           fn-clock-timep)))))
  (if (and (fn-clock-observationp obs)
           (fn-clock-has-wall obs)
           (< (floor (fn-clock-wall obs) 1000) 4294967296))
      (floor (fn-clock-wall obs) 1000)
    :clock-unusable))

(defthm fn-record-stamp-of-observation-is-a-stamp
  (implies (natp (fn-record-stamp-of-observation obs))
           (fn-record-stampp (fn-record-stamp-of-observation obs)))
  :hints (("Goal" :in-theory (enable fn-record-stamp-of-observation
                                     fn-record-stampp fn-record-uint32p))))

(defthm fn-record-stamp-of-observation-is-natural-or-unusable
  (or (natp (fn-record-stamp-of-observation obs))
      (equal (fn-record-stamp-of-observation obs) :clock-unusable))
  :hints (("Goal" :in-theory (enable fn-record-stamp-of-observation
                                     fn-clock-observationp fn-clock-timep))))
