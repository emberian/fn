; Shared fixture profile recipe; no simulator or core instance.
(in-package "ACL2")
(include-book "../books/profile")
(include-book "../books/commit-geometry")
(defun fn2-b-four-k-classp (classes)
  (declare (xargs :verify-guards nil))
  (if (atom classes) nil
    (or (equal (cdar classes) 4096) (fn2-b-four-k-classp (cdr classes)))))
(defun fn2-b-test-profile (profile mode)
  (declare (xargs :verify-guards nil))
  (let* ((sectors (if (assoc-equal :sim-sectors profile)
                      (fn2-profile-get :sim-sectors profile) (* 5 *fn2-storage-extent-units*)))
         (profile (put-assoc-equal :sim-sectors sectors profile))
         (profile (if (assoc-equal :extent-slots profile) profile
                    (put-assoc-equal :extent-slots (floor (nfix sectors) *fn2-storage-extent-units*) profile))))
    (put-assoc-equal :commit-barrier-mode mode
      (if (fn2-b-four-k-classp (fn2-profile-pool-classes profile)) profile
        (put-assoc-equal :pool-classes
          (append (fn2-profile-pool-classes profile) '((8 . 4096))) profile)))))
