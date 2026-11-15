(in-package "ACL2")
(include-book "../books/article-limit-config")
(include-book "article-limit-text-unit")

(assert-event (equal (fn2-article-limit-profile-from-text *fn2-profile-tiny* nil) *fn2-profile-tiny*))
(assert-event
 (let ((profile (fn2-article-limit-profile-from-text *fn2-profile-tiny* "98304")))
  (and (equal (fn2-profile-get :article-max profile) 98304)
       (fn2-input-config-profilep profile))))
(assert-event
 (let ((profile (fn2-article-limit-profile-from-text *fn2-profile-tiny* "4294967295")))
  (and (equal (fn2-profile-get :article-max profile) -1)
       (not (fn2-input-config-profilep profile)))))
(assert-event
 (let ((profile (fn2-article-limit-profile-from-text *fn2-profile-tiny* "no")))
  (and (equal (fn2-profile-get :article-max profile) -1)
       (not (fn2-input-config-profilep profile)))))
(assert-event
 (let ((profile (put-assoc-equal :article-max 98304 *fn2-profile-tiny*)))
  (equal (fn2-article-limit-profile-from-text profile nil) profile)))
(assert-event
 (equal (fn2-profile-get :article-max
         (fn2-article-limit-profile-from-text *fn2-profile-tiny* "")) -1))
