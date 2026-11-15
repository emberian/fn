(in-package "ACL2")
(include-book "../books/article-limit-config")

(assert-event (equal (fn2-article-limit-profile-from-text *fn2-profile-tiny* nil) *fn2-profile-tiny*))
(assert-event (equal (fn2-article-limit-decimal "00098304") 98304))
(assert-event (equal (fn2-article-limit-decimal "4294967295") 4294967295))
(assert-event (equal (fn2-article-limit-decimal "0") 0))
(assert-event (not (fn2-article-limit-decimal "4294967296")))
(assert-event (not (fn2-article-limit-decimal "00000098304")))
(assert-event (not (fn2-article-limit-decimal "98 304")))
(assert-event (not (fn2-article-limit-decimal "")))
(assert-event (not (fn2-article-limit-decimal "#.(anything)")))
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
