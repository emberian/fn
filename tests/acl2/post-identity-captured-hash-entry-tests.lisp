(in-package "ACL2")
(include-book "../../books/post-identity-captured-hash-entry")
(include-book "post-identity-captured-tests")

; Ground reachability starts at the real binding-gated begin and uses the
; existing fixture driver for one actual feedback transition per iteration.
(defun pic-het-until (c incoming held branch fuel)
  (declare (xargs :measure (nfix fuel) :verify-guards nil))
  (let ((phase (fn-pic-get phase c)) (d (fn-pic-demand c)))
    (if (or (zp fuel) (equal phase :done)
            (and (equal branch :whole) (equal phase :tomb-flag))
            (and (equal branch :source) (equal phase :tomb-agent-held) (equal d :control))
            (and (equal branch :fallback) (equal phase :tomb-agent-incoming)
                 (not (equal (nth (fn-pic-at 1 d) incoming) (fn-pic-get cached c)))))
        c
      (pic-het-until (pic-test-drive c incoming held 1) incoming held branch (1- fuel)))))
(defun pic-het-input (branch)
  (if (equal branch :whole) '(97 98 99) *pic-test-stamped*))
(defun pic-het-c (branch)
  (declare (xargs :verify-guards nil))
  (let* ((incoming (pic-het-input branch))
         (held (pic-test-tomb (if (equal branch :whole) 0 1)
                 *pic-test-abc-hash* *pic-test-abc-hash*
                 (case branch (:source *pic-test-source-agent*) (:fallback '(97 98 100)) (otherwise nil))))
         (c (fn-pic-begin *pic-test-selected* *pic-test-grant*
               (pic-test-held "<m>" nil *pic-test-binding*) *pic-test-incoming*
               (len incoming) "<m>" *pic-test-binding* nil)))
    (pic-het-until c incoming held branch 2000)))

(defthm pic-het-feedback-whole-positive
 (let* ((incoming (pic-het-input :whole)) (c (pic-het-c :whole))
        (observation (list :payload-byte *pic-test-selected* *pic-test-grant* 0 8 0))
        (next (mv-nth 1 (fn-pic-feed-funded c observation 1))))
  (and (fn-pic-hash-entryp 0 c incoming)
       (member-eq (fn-pic-get phase c) '(:tomb-flag :tomb-agent-held :tomb-agent-incoming))
       (equal (fn-pic-get phase next) :digest-begin)
       (fn-pic-digest-trajectoryp 0 next incoming (create-pgs-digest-state))
       (equal (fn-pic-get digest-base next) 9)
       (equal (fn-pic-get digest-desc next) '(0 0 0))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-hash-entryp fn-pic-digest-trajectoryp))))
(defthm pic-het-feedback-source-positive
 (let* ((incoming (pic-het-input :source)) (c (pic-het-c :source))
        (next (mv-nth 1 (fn-pic-feed-funded c :control 1))))
  (and (fn-pic-hash-entryp 0 c incoming)
       (member-eq (fn-pic-get phase c) '(:tomb-flag :tomb-agent-held :tomb-agent-incoming))
       (equal (fn-pic-demand c) :control)
       (equal (fn-pic-get phase next) :digest-begin)
       (fn-pic-digest-trajectoryp 0 next incoming (create-pgs-digest-state))
       (equal (fn-pic-get digest-base next) 41)
       (equal (fn-pic-span-value (fn-pic-get digest-desc next) incoming) *pic-test-source*)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-hash-entryp fn-pic-digest-trajectoryp))))
(defthm pic-het-read-source-positive
 (let* ((incoming (pic-het-input :source)) (c (pic-het-c :source))
        (next (mv-nth 1 (fn-pic-next c 1 incoming))))
  (and (fn-pic-hash-entryp 0 c incoming)
       (member-eq (fn-pic-get phase c) '(:tomb-flag :tomb-agent-held :tomb-agent-incoming))
       (equal (fn-pic-get phase next) :digest-begin)
       (fn-pic-digest-trajectoryp 0 next incoming (create-pgs-digest-state))
       (equal (fn-pic-get digest-base next) 41)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-hash-entryp fn-pic-digest-trajectoryp))))
(defthm pic-het-read-mismatched-agent-fallback-positive
 (let* ((incoming (pic-het-input :fallback)) (c (pic-het-c :fallback))
        (next (mv-nth 1 (fn-pic-next c 2 incoming))))
  (and (fn-pic-hash-entryp 0 c incoming)
       (member-eq (fn-pic-get phase c) '(:tomb-flag :tomb-agent-held :tomb-agent-incoming))
       (equal (fn-pic-get phase c) :tomb-agent-incoming)
       (equal (fn-pic-get phase next) :digest-begin)
       (fn-pic-digest-trajectoryp 0 next incoming (create-pgs-digest-state))
       (equal (fn-pic-get digest-base next) 9)
       (equal (fn-pic-get digest-desc next) '(0 0 0))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-hash-entryp fn-pic-digest-trajectoryp))))
; Corrupted-state removal: both actual subjects falsely enter a source hash
; if the carried source descriptor is removed from a source-ready state.
(defthm pic-het-carried-entry-removal-corrupted-source
 (let* ((incoming (pic-het-input :source))
        (c (fn-pic-set incoming-desc nil (pic-het-c :source)))
        (a (mv-nth 1 (fn-pic-feed-funded c :control 1)))
        (b (mv-nth 1 (fn-pic-next c 1 incoming))))
  (and (not (fn-pic-hash-entryp 0 c incoming))
       (member-eq (fn-pic-get phase c) '(:tomb-flag :tomb-agent-held :tomb-agent-incoming))
       (equal (fn-pic-get phase a) :digest-begin) (equal (fn-pic-get phase b) :digest-begin)
       (not (fn-pic-digest-trajectoryp 0 a incoming (create-pgs-digest-state)))
       (not (fn-pic-digest-trajectoryp 0 b incoming (create-pgs-digest-state)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-hash-entryp fn-pic-digest-trajectoryp))))
; Corrupted-state phase removal: an existing invalid hash continuation is
; preserved at zero fuel, and the new-entry theorem does not apply to it.
(defthm pic-het-phase-removal-corrupted-existing-hash
 (let* ((incoming (pic-het-input :whole))
        (c (fn-pic-set digest-desc '(0 4 2) (fn-pic-hash-start nil (pic-het-c :whole))))
        (a (mv-nth 1 (fn-pic-feed-funded c nil 0)))
        (b (mv-nth 1 (fn-pic-next c 0 incoming))))
  (and (fn-pic-hash-entryp 0 c incoming)
       (not (member-eq (fn-pic-get phase c) '(:tomb-flag :tomb-agent-held :tomb-agent-incoming)))
       (equal (fn-pic-get phase a) :digest-begin) (equal (fn-pic-get phase b) :digest-begin)
       (not (fn-pic-digest-trajectoryp 0 a incoming (create-pgs-digest-state)))
       (not (fn-pic-digest-trajectoryp 0 b incoming (create-pgs-digest-state)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-hash-entryp fn-pic-digest-trajectoryp))))
