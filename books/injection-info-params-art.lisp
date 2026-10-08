; fn: Injection-Info parameters over ART; only HEAD is rebuilt.
(in-package "ACL2")
(include-book "post-header-local")

(defun fn-art-decision-payload (d)
  (declare (xargs :guard t))
  (fn-inj-decision-octets d))

; Logical lowering changes just the payload slot, preserving every other cons
; and any trailing fields. It is not called by the served ART writer.
(defun fn-art-decision-down-aux (n d)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (consp d)
      (if (zp n)
          (cons (fn-art-octets (car d)) (cdr d))
        (cons (car d) (fn-art-decision-down-aux (- n 1) (cdr d))))
    d))

(defun fn-art-decision-down (d)
  (declare (xargs :guard t))
  (fn-art-decision-down-aux 4 d))

(defun fn-ipp-with-params-art (a msgid params)
  (declare (xargs :guard t))
  (cons (fn-ipp-with-params (fn-art-head a) msgid params) (fn-art-body a)))

(defun fn-ipp-injected-art (d secret login cfg)
  (declare (xargs :guard t))
  (fn-ipp-with-params-art
   (fn-art-decision-payload d) (fn-inj-decision-msgid d)
   (fn-ipp-params secret login (fn-ipp-complaints cfg))))

(local
 (defthm fn-art-decision-down-octets
   (equal (fn-inj-decision-octets (fn-art-decision-down d))
          (fn-art-octets (fn-art-decision-payload d)))
   :hints (("Goal" :do-not-induct t
            :expand ((:free (d) (fn-art-decision-down-aux 0 d))
                     (:free (d) (fn-art-decision-down-aux 1 d))
                     (:free (d) (fn-art-decision-down-aux 2 d))
                     (:free (d) (fn-art-decision-down-aux 3 d))
                     (:free (d) (fn-art-decision-down-aux 4 d))
                     (:free (xs) (fn-inj-nth 0 xs))
                     (:free (xs) (fn-inj-nth 1 xs))
                     (:free (xs) (fn-inj-nth 2 xs))
                     (:free (xs) (fn-inj-nth 3 xs))
                     (:free (xs) (fn-inj-nth 4 xs)))
            :in-theory
            (union-theories '(fn-art-decision-down fn-art-decision-down-aux
                              fn-art-decision-payload fn-inj-decision-octets
                              fn-inj-nth fn-inj-car fn-inj-cdr nfix zp
                              (:executable-counterpart fn-bch-unpack) fn-art-octets
                              fn-art-head fn-art-body true-list-fix binary-append
                              car-cons cdr-cons default-car default-cdr)
                            (theory 'minimal-theory))))))

(local
 (defthm fn-art-decision-down-msgid
   (equal (fn-inj-decision-msgid (fn-art-decision-down d))
          (fn-inj-decision-msgid d))
   :hints (("Goal" :do-not-induct t
            :expand ((:free (d) (fn-art-decision-down-aux 0 d))
                     (:free (d) (fn-art-decision-down-aux 1 d))
                     (:free (d) (fn-art-decision-down-aux 2 d))
                     (:free (d) (fn-art-decision-down-aux 3 d))
                     (:free (d) (fn-art-decision-down-aux 4 d))
                     (:free (xs) (fn-inj-nth 0 xs))
                     (:free (xs) (fn-inj-nth 1 xs))
                     (:free (xs) (fn-inj-nth 2 xs))
                     (:free (xs) (fn-inj-nth 3 xs))
                     (:free (xs) (fn-inj-nth 4 xs)))
            :in-theory
            (union-theories '(fn-art-decision-down fn-art-decision-down-aux
                              fn-inj-decision-msgid fn-inj-nth fn-inj-car fn-inj-cdr nfix zp
                              car-cons cdr-cons default-car default-cdr)
                            (theory 'minimal-theory))))))

(local
 (defthm fn-art-append-fix
   (equal (append (true-list-fix x) y) (append x y))
   :hints (("Goal" :in-theory
            (union-theories '(true-list-fix binary-append car-cons cdr-cons)
                            (theory 'minimal-theory))
            :induct (binary-append x y)))))

(local
 (defthm fn-art-octets-listp
   (implies (fn-bch-octetsp h) (true-listp h))
   :hints (("Goal" :in-theory (enable fn-bch-octetsp)))))

(local
 (defthm fn-art-true-listp-inj-append
   (implies (true-listp y) (true-listp (fn-inj-append x y)))
   :hints (("Goal" :in-theory
            (union-theories '(fn-inj-append true-listp car-cons cdr-cons)
                            (theory 'minimal-theory))))))
(local
 (defthm fn-art-true-listp-strip
   (implies (and (true-listp h) (not (equal (fn-inj-strip line h) :no)))
            (true-listp (fn-inj-strip line h)))
   :hints (("Goal" :in-theory
            (union-theories '(fn-inj-strip true-listp car-cons cdr-cons)
                            (theory 'minimal-theory))
            :induct (fn-inj-strip line h)))))
(local
 (defthm fn-art-true-listp-drop
   (implies (true-listp h) (true-listp (fn-inj-drop n h)))
   :hints (("Goal" :in-theory
            (union-theories '(fn-inj-drop nfix zp true-listp car-cons cdr-cons)
                            (theory 'minimal-theory))
            :induct (fn-inj-drop n h)))))

(local
 (defthm fn-art-ipp-info-listp
   (implies (true-listp h) (true-listp (fn-ipp-at-info h agent params)))
   :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ipp-at-info fn-pb-strip-header-line fn-art-true-listp-inj-append fn-art-true-listp-strip fn-art-true-listp-drop) (theory 'minimal-theory))))))

(local
 (defthm fn-art-ipp-date-listp
   (implies (true-listp h) (true-listp (fn-ipp-at-date h agent params)))
   :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ipp-at-date fn-pb-strip-header-line fn-art-true-listp-inj-append fn-art-true-listp-strip fn-art-true-listp-drop fn-art-ipp-info-listp) (theory 'minimal-theory))))))

(local
 (defthm fn-art-ipp-msgid-listp
   (implies (true-listp h) (true-listp (fn-ipp-at-msgid h agent msgid params)))
   :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ipp-at-msgid fn-pb-strip-header-line fn-art-true-listp-inj-append fn-art-true-listp-strip fn-art-true-listp-drop fn-art-ipp-info-listp fn-art-ipp-date-listp) (theory 'minimal-theory))))))

(local
 (defthm fn-art-ipp-stamp-listp
   (implies (true-listp h) (true-listp (fn-ipp-at-stamp h agent msgid params)))
   :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ipp-at-stamp fn-pb-strip-header-line fn-art-true-listp-inj-append fn-art-true-listp-strip fn-art-true-listp-drop fn-art-ipp-info-listp fn-art-ipp-date-listp fn-art-ipp-msgid-listp) (theory 'minimal-theory))))))

(local
 (defthm fn-art-ipp-with-params-listp
   (implies (true-listp h) (true-listp (fn-ipp-with-params h msgid params)))
   :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ipp-with-params fn-pb-strip-header-line fn-art-true-listp-inj-append fn-art-true-listp-strip fn-art-true-listp-drop fn-art-ipp-info-listp fn-art-ipp-date-listp fn-art-ipp-msgid-listp fn-art-ipp-stamp-listp) (theory 'minimal-theory))))))

(defthm fn-ipp-with-params-art-refines
  (implies (fn-art-headp a)
           (and (equal (fn-art-octets (fn-ipp-with-params-art a msgid params))
                       (fn-ipp-with-params (fn-art-octets a) msgid params))
                (equal (fn-art-body (fn-ipp-with-params-art a msgid params))
                       (fn-art-body a))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ipp-with-params-art fn-art-octets fn-art-headp
                             fn-art-separated-headp fn-art-head fn-art-body)
                            (fn-ipp-with-params fn-bch-unpack
                             fn-art-first-separator-headp fn-art-no-separatorp))
           :use ((:instance fn-ipp-with-params-head-local
                            (head (fn-art-head a))
                            (body (fn-bch-unpack (fn-art-body a))))))))

; Statement 3, injection member: the only premise is the carried ART invariant.
(defthm fn-ipp-injected-art-refines
  (implies (fn-art-headp (fn-art-decision-payload d))
           (let ((r (fn-ipp-injected-art d secret login cfg)))
             (and (equal (fn-art-octets r)
                         (fn-ipp-injected-octets
                          (fn-art-decision-down d) secret login cfg))
                  (equal (fn-art-body r)
                         (fn-art-body (fn-art-decision-payload d))))))
  :hints (("Goal" :in-theory
           (e/d (fn-ipp-injected-art fn-ipp-injected-octets)
                (fn-ipp-with-params-art fn-art-decision-down
                 fn-art-decision-payload fn-art-octets fn-art-body
                 fn-art-headp fn-ipp-with-params)))))
