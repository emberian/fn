(in-package "ACL2")
(include-book "../../books/obligation-view-growth")

(defconst *rovg-key* (coerce (make-list 256 :initial-element #\a) 'string))
(defconst *rovg-empty* (fn-retain-initial-state 100))
(defconst *rovg-held* (fn-retain-admit *rovg-empty* "hold" *rovg-key* :forward "receipt" 7))
(defconst *rovg-released* (fn-retain-release *rovg-held* "hold" *rovg-key* :forward "receipt"))
(defconst *rovg-view* (fn-rov-update *rovg-empty* *rovg-held* (fn-rov-build nil)))
(defconst *rovg-zero* (fn-rov-update *rovg-held* *rovg-released* *rovg-view*))

; Literal updater bound, reachable arrival, largest metadata path, exact shape.
(assert-event
 (and (equal (fn-rov-update-arm *rovg-empty* *rovg-held*) :arrival)
      (equal (fn-rov-update-subject *rovg-empty* *rovg-held*) *rovg-key*)
      (equal (fn-rov-count *rovg-view*) 1)
      (equal (fn-rov-subject *rovg-key* *rovg-view*) '(1 . 7))
      (equal (fn-vcs-conses (cdr *rovg-view*)) 515)
      (<= (fn-vcs-conses (cdr *rovg-view*))
          (+ (fn-vcs-conses (cdr (fn-rov-build nil))) 3
             (* 2 (length (if (stringp (fn-rov-update-subject *rovg-empty* *rovg-held*))
                              (fn-rov-update-subject *rovg-empty* *rovg-held*) "")))))))
; Reachable release preserves its zero path. Funding only live count fails.
(assert-event
 (and (equal (fn-rov-update-arm *rovg-held* *rovg-released*) :release)
      (equal (fn-rov-update-subject *rovg-held* *rovg-released*) *rovg-key*)
      (equal (fn-rov-count *rovg-zero*) 0)
      (equal (fn-rov-subject *rovg-key* *rovg-zero*) '(0 . 0))
      (equal (fn-vcs-conses (cdr *rovg-zero*)) 515)
      (<= (fn-vcs-conses (cdr *rovg-zero*))
          (+ (fn-vcs-conses (cdr *rovg-view*)) 3
             (* 2 (length (if (stringp (fn-rov-update-subject *rovg-held* *rovg-released*))
                              (fn-rov-update-subject *rovg-held* *rovg-released*) "")))))
      (not (<= (fn-vcs-conses (cdr *rovg-zero*)) (* 515 (fn-rov-count *rovg-zero*))))))
; Duplicate release stays the same, including the funded zero terminal.
(assert-event
 (let ((duplicate (fn-retain-release *rovg-released* "hold" *rovg-key* :forward "receipt")))
   (and (equal (fn-rov-update-arm *rovg-released* duplicate) :same)
        (equal (fn-rov-update *rovg-released* duplicate *rovg-zero*) *rovg-zero*)
        (<= (fn-vcs-conses (cdr (fn-rov-update *rovg-released* duplicate *rovg-zero*)))
            (+ (fn-vcs-conses (cdr *rovg-zero*)) 3
               (* 2 (length (if (stringp (fn-rov-update-subject *rovg-released* duplicate))
                                (fn-rov-update-subject *rovg-released* duplicate) ""))))))))
; Mutation witness: claiming a successful first arrival allocates no retained
; conses would pass an empty-only test and fails at this actual updater call.
(assert-event
 (not (<= (fn-vcs-conses (cdr *rovg-view*)) (fn-vcs-conses (cdr (fn-rov-build nil))))))

; Literal retraction lemma over the concrete trie used by the updater.
(assert-event
 (let ((trie (cdr *rovg-view*)) (key *rovg-key*) (weight 7))
   (and (equal (fn-vdc-get key trie) '(1 . 7))
        (equal (fn-vdc-get key (fn-vdc-unbump key weight trie)) '(0 . 0))
        (<= (fn-vcs-conses (fn-vdc-unbump key weight trie))
            (+ (* 2 (length (if (stringp key) key ""))) 3
               (fn-vcs-conses trie))))))
