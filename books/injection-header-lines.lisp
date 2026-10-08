; Injection-generated date lines satisfy the shared exact-line predicate.
(in-package "ACL2")
(include-book "injection")
(include-book "post-header-line")
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-pb-weekday-line-textp
   (and (not (equal (fn-inj-dow-c1 n) 10))
        (not (equal (fn-inj-dow-c1 n) 13))
        (not (equal (fn-inj-dow-c2 n) 10))
        (not (equal (fn-inj-dow-c2 n) 13))
        (not (equal (fn-inj-dow-c3 n) 10))
        (not (equal (fn-inj-dow-c3 n) 13)))
   :hints (("Goal" :in-theory (enable fn-inj-dow-c1 fn-inj-dow-c2 fn-inj-dow-c3)))))

(local
 (defthm fn-pb-month-line-textp
   (and (not (equal (fn-inj-month-c1 n) 10))
        (not (equal (fn-inj-month-c1 n) 13))
        (not (equal (fn-inj-month-c2 n) 10))
        (not (equal (fn-inj-month-c2 n) 13))
        (not (equal (fn-inj-month-c3 n) 10))
        (not (equal (fn-inj-month-c3 n) 13)))
   :hints (("Goal" :in-theory (enable fn-inj-month-c1 fn-inj-month-c2 fn-inj-month-c3)))))

(local
 (defthm fn-pb-date-digit-line-textp
   (and (not (equal (fn-inj-hi2 n) 10))
        (not (equal (fn-inj-hi2 n) 13))
        (not (equal (fn-inj-lo2 n) 10))
        (not (equal (fn-inj-lo2 n) 13))
        (not (equal (fn-inj-y-th n) 10))
        (not (equal (fn-inj-y-th n) 13))
        (not (equal (fn-inj-y-hu n) 10))
        (not (equal (fn-inj-y-hu n) 13))
        (not (equal (fn-inj-y-te n) 10))
        (not (equal (fn-inj-y-te n) 13))
        (not (equal (fn-inj-y-un n) 10))
        (not (equal (fn-inj-y-un n) 13)))
   :hints (("Goal" :in-theory (enable fn-inj-hi2 fn-inj-lo2 fn-inj-y-th fn-inj-y-hu fn-inj-y-te fn-inj-y-un fn-inj-r1 fn-inj-r2)))))

(defthm fn-pb-date-octets-line-textp
  (fn-pb-line-textp (fn-inj-date-octets inst))
  :hints (("Goal" :in-theory (enable fn-pb-line-textp fn-inj-date-octets))))
