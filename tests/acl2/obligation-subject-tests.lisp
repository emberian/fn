; Full query and frame behavior, including independent holds and absent keys.
(in-package "ACL2")
(include-book "../../books/obligation-subject-report")
(include-book "../../books/native-operator")
(include-book "../../books/control-evidence")
(include-book "../../books/codec-attach")
(in-theory (disable (:executable-counterpart fn-rov-correspondp)
                    (:executable-counterpart fn-vdc-correspondp)))
(defconst *oqt-l0* (fn-retain-initial-state 100))
(defconst *oqt-l1* (fn-retain-admit *oqt-l0* "a" "subject-a" :archive "a" 7))
(defconst *oqt-l2* (fn-retain-admit *oqt-l1* "b" "subject-a" :forward "b" 11))
(defconst *oqt-view* (fn-rov-build (fn-retain-pins *oqt-l2*)))
(defthm oqt-report-complete-positive
  (and (stringp "subject-a")
       (fn-rov-correspondp *oqt-view* (fn-retain-pins *oqt-l2*))
       (equal (fn-oqr-live-report "subject-a" *oqt-view*)
              (fn-oqr-oracle-report "subject-a" (fn-retain-pins *oqt-l2*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rov-build-corresponds
                         (pins (fn-retain-pins *oqt-l2*)))
                        (:instance fn-oqr-live-is-reconstruction
                         (subject "subject-a") (view *oqt-view*)
                         (pins (fn-retain-pins *oqt-l2*)))))))
(assert-event
 (and (equal (fn-oqr-live-report "subject-a" *oqt-view*)
             (fn-nls-text "subject-hex=7375626a6563742d61 obligations=2 charge=18
"))
      (equal (fn-oqr-live-report "absent" *oqt-view*)
             (fn-oqr-oracle-report "absent" (fn-retain-pins *oqt-l2*)))
      (equal (fn-rov-subject "absent" *oqt-view*) '(0 . 0))))
; Mutation witness: erasing the per-subject trie violates exact report equality.
(assert-event
 (and (stringp "subject-a")
      (not (equal (fn-oqr-live-report "subject-a" (cons 2 nil))
                  (fn-oqr-oracle-report "subject-a" (fn-retain-pins *oqt-l2*))))))
(assert-event (equal (fn-oqg-parse '("subject" "subject-a"))
                     '(:kind (:obligation-subject . "subject-a"))))
(assert-event (equal (fn-oqg-parse '("subject" "")) '(:usage :obligation-subject)))
(assert-event (equal (fn-oqg-parse '("subject" "x" "extra"))
                     '(:usage :obligation-subject)))
; The existing metadata type admits 256 octets; no accidental old 250 cap.
(defconst *oqt-subject256* (coerce (make-list 256 :initial-element #\a) 'string))
(assert-event
 (and (fn-oqg-kindp (cons :obligation-subject *oqt-subject256*))
      (equal (fn-cev-any-request-decode
               (fn-cev-any-request-encode
                 (cons :obligation-subject *oqt-subject256*) 4294967295))
             (list :live-status (cons :obligation-subject *oqt-subject256*)
                   4294967295))))
(defconst *oqt-config*
  (append (fn-record-string-octets "[store]") '(10)
          (fn-record-string-octets "path = \"/srv/fn\"") '(10)))
(defconst *oqt-plan*
  (fn-native-operator-run *oqt-config*
     (list (fn-record-string-octets "obligations")
           (fn-record-string-octets "subject")
           (fn-record-string-octets "subject-a"))))
(assert-event
 (and (fn-native-operator-result-status-planp *oqt-plan*)
      (equal (fn-native-operator-result-status-kind *oqt-plan*)
             '(:obligation-subject . "subject-a"))))

; Full actual answered reply and cache effect; repeated keys grow no cache.
(assert-event
 (and (equal (fn-oqr-live-answer "subject-a" *oqt-view* 0 'existing-cache)
             (list (fn-nls-page (fn-nls-buffer
                     (fn-oqr-oracle-report "subject-a" (fn-retain-pins *oqt-l2*))) 0)
                   'existing-cache))
      (equal (cadr (fn-oqr-live-answer "absent" *oqt-view* 0 'existing-cache))
             'existing-cache)
      (equal (cadr (fn-nls-reply-decode
                    (car (fn-oqr-live-answer "subject-a" *oqt-view* 1 nil))))
             :refused)))

(defthm oqt-answer-complete-positive
 (and (stringp "subject-a")
      (fn-rov-correspondp *oqt-view* (fn-retain-pins *oqt-l2*))
      (<= (len (fn-oqr-oracle-report "subject-a" (fn-retain-pins *oqt-l2*)))
          *fn-nls-chunk-octets*)
      (equal (fn-oqr-live-answer "subject-a" *oqt-view* 0 'existing-cache)
             (list (fn-nls-page (fn-nls-buffer
                     (fn-oqr-oracle-report "subject-a" (fn-retain-pins *oqt-l2*))) 0)
                   'existing-cache)))
 :rule-classes nil
 :hints (("Goal" :use (oqt-report-complete-positive
                       (:instance fn-oqr-live-answer-is-reconstruction
                        (subject "subject-a") (view *oqt-view*)
                        (pins (fn-retain-pins *oqt-l2*)) (cached 'existing-cache))))))
