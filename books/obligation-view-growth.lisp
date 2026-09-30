; W9 retained tree growth at its exact delta updater. This counts cons cells,
; not physical allocations, and charges releases as well as arrivals.
(in-package "ACL2")
(include-book "retention-obligation-view")
(include-book "view-delta-space")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-vdc-unbump-cons-growth
  (<= (fn-vcs-conses (fn-vdc-unbump key weight trie))
      (+ (* 2 (length (if (stringp key) key ""))) 3 (fn-vcs-conses trie)))
  :hints (("Goal" :in-theory (e/d (fn-vdc-unbump fn-vd-pairp)
                                  (fn-vdc-put fn-vdc-get))
           :use ((:instance fn-vdc-put-cons-growth
                   (pair (if (<= (car (fn-vdc-get key trie)) 1) *fn-vd-zero*
                           (cons (- (car (fn-vdc-get key trie)) 1)
                                 (nfix (- (cdr (fn-vdc-get key trie)) (nfix weight)))))))))))

; The exact subject that fn-rov-update visits. Invalid/no-change transitions
; visit no path; defining their subject as NIL gives a conservative zero size.
(defun fn-rov-update-subject (old new)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-rov-update-arm)))))
  (case (fn-rov-update-arm old new)
    (:arrival (fn-retain-obligation-subject (car (fn-retain-pins new))))
    (:release (fn-retain-release-subject (car (fn-retain-releases new))))
    (otherwise nil)))

(defthm fn-rov-update-retained-cons-growth
  (<= (fn-vcs-conses (cdr (fn-rov-update old new view)))
      (+ (fn-vcs-conses (cdr view)) 3
         (* 2 (length (if (stringp (fn-rov-update-subject old new))
                         (fn-rov-update-subject old new) "")))))
  :hints (("Goal"
           :in-theory (e/d (fn-rov-update fn-rov-update-subject fn-rov-arrive
                             fn-vcs-conses fn-rov-count)
                           (fn-rov-update-arm fn-vdc-bump fn-vdc-unbump
                            fn-vdc-bump-cons-growth fn-vdc-unbump-cons-growth))
           :use ((:instance fn-vdc-bump-cons-growth
                   (key (fn-retain-obligation-subject (car (fn-retain-pins new))))
                   (weight (fn-retain-obligation-charge (car (fn-retain-pins new))))
                   (trie (cdr view)))
                 (:instance fn-vdc-unbump-cons-growth
                   (key (fn-retain-release-subject (car (fn-retain-releases new))))
                   (weight (nfix (+ 1 (- (nfix (fn-retain-reserved old))
                                         (nfix (fn-retain-reserved new))))))
                   (trie (cdr view)))))))
