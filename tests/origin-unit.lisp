; Explicit deployment origin; fixture names are not a uniqueness theorem.
(in-package "ACL2")
(include-book "../books/origin")
(assert-event
 (and (equal (fn2-origin-decimal "1") 1)
      (equal (fn2-origin-decimal "1152921504606846975") *fn2-u60-max*)
      (not (fn2-origin-decimal "1152921504606846976"))
      (not (fn2-origin-decimal "00000000000000000001"))
      (not (fn2-origin-decimal "0")) (not (fn2-origin-decimal "-1"))
      (not (fn2-origin-decimal "+1")) (not (fn2-origin-decimal "1 "))
      (not (fn2-origin-decimal "#.(error x)"))
      (not (fn2-origin-decimal nil))))
(assert-event
 (and (fn2-origin-profilep
        (fn2-origin-profile-from-text *fn2-profile-tiny* "17" "23" "5" "101" "7"))
      (not (fn2-origin-profilep
             (fn2-origin-profile-from-text *fn2-profile-tiny* nil "23" "5" "101" "7")))
      (not (fn2-origin-profilep
             (fn2-origin-profile-from-text *fn2-profile-tiny* "17" "bad" "5" "101" "7")))))
(defun fn2-origin-unit-run (fn2-origin)
 (declare (xargs :stobjs fn2-origin :verify-guards nil))
 (let* ((profile (fn2-origin-profile-from-text *fn2-profile-tiny* "17" "23" "5" "101" "7"))
        (fn2-origin (fn2-origin-prepare profile fn2-origin)))
  (mv (and (= (fn2-origin-lineage fn2-origin) 17)
           (= (fn2-origin-domain fn2-origin) 23)
           (= (fn2-origin-incarnation fn2-origin) 5)
           (= (fn2-origin-history fn2-origin) 101)
           (= (fn2-origin-history-incarnation fn2-origin) 7)) fn2-origin)))
(defun fn2-origin-unit-check ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-origin
  (mv-let (ok fn2-origin) (fn2-origin-unit-run fn2-origin) ok)))
(assert-event (fn2-origin-unit-check))

(assert-event
 (let ((profile (fn2-history-revision-profile-from-text *fn2-profile-tiny* "3")))
  (and (equal (fn2-history-revision-profile-from-text *fn2-profile-tiny* nil) *fn2-profile-tiny*)
       (equal (fn2-profile-get :history-revision profile) 3)
       (fn2-origin-profilep profile)
       (not (fn2-origin-profilep (fn2-history-revision-profile-from-text profile "0")))
       (not (fn2-origin-profilep (fn2-history-revision-profile-from-text profile "+3"))))))
