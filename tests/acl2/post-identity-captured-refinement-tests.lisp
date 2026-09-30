(in-package "ACL2")
(include-book "../../books/post-identity-captured-refinement")

; Literal logical fixtures only. No fixture runs on the served path.
(defun-nx pic-prft-c (phase pos block)
  (fn-pic-set phase phase (fn-pic-set incoming-n 3
    (fn-pic-set digest-desc '(0 0 0) (fn-pic-set pos pos
      (fn-pic-set block-start 0 (fn-pic-set block-count 3
        (fn-pic-set block block (make-list 23 :initial-element nil)))))))))
(defun-nx pic-prft-chunk ()
  (declare (xargs :stobjs nil :verify-guards nil))
  (mv-nth 1 (pgs-dcb-step 3 nil
    (pgs-dcb-begin 0 0 3 nil nil (create-pgs-digest-state)))))
(defun-nx pic-prft-done ()
  (declare (xargs :stobjs nil :verify-guards nil))
  (let* ((a (mv-nth 1 (pgs-dcb-step 3 (fn-b3-words 16 '(65 66 67)) (pic-prft-chunk))))
         (b (mv-nth 1 (pgs-dcb-step 3 nil a))))
    (mv-nth 1 (pgs-dcb-step 3 nil b))))

(defthm pic-prft-digest-positive-commit
  (let* ((incoming '(65 66 67))
         (c (pic-prft-c :digest-commit 3 '(67 66 65)))
         (cursor (pic-prft-chunk))
         (next (mv-nth 1 (fn-pic-digest-next c 2 cursor)))
         (state (mv-nth 3 (fn-pic-digest-next c 2 cursor))))
    (and (fn-pic-digest-trajectoryp 0 c incoming cursor)
         (fn-pic-digest-trajectoryp 0 next incoming state)
         (equal (fn-pic-get phase next) :digest-next)
         (equal (pgs-dc-mode state) :return)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pic-prft-c pic-prft-chunk fn-pic-digest-trajectoryp
    fn-pic-block-prefixp pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
    pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
    pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span pgs-dcb-next-byte-offset
    pgs-dcb-read-demand pgs-dc-needs-block pgs-dcb-word-count)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))))

(defthm pic-prft-digest-positive-terminal-hash
  (let* ((incoming '(65 66 67)) (c (pic-prft-c :digest-next 0 nil))
         (cursor (pic-prft-done))
         (next (mv-nth 1 (fn-pic-digest-next c 2 cursor)))
         (state (mv-nth 3 (fn-pic-digest-next c 2 cursor))))
    (and (fn-pic-digest-trajectoryp 0 c incoming cursor)
         (fn-pic-digest-trajectoryp 0 next incoming state)
         (equal (fn-pic-get phase next) :digest-compare)
         (equal (fn-pic-get digest next) (fn-blake3 incoming))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pic-prft-c pic-prft-chunk pic-prft-done fn-pic-digest-trajectoryp
    pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
    pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
    pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span pgs-dcb-word-count)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))))

(defthm pic-prft-digest-invariant-removal-corrupted-descriptor
  (let* ((incoming '(65 66 67))
         (c (fn-pic-set digest-desc '(0 4 2) (pic-prft-c :digest-begin 0 nil)))
         (cursor (create-pgs-digest-state))
         (next (mv-nth 1 (fn-pic-digest-next c 2 cursor)))
         (state (mv-nth 3 (fn-pic-digest-next c 2 cursor))))
    (and (not (fn-pic-digest-trajectoryp 0 c incoming cursor))
         (not (fn-pic-digest-trajectoryp 0 next incoming state))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pic-prft-c fn-pic-digest-trajectoryp))))

; Non-natural fuel yields before any digest effect, preserving the product.
; This is a logical totality witness; the served guard still requires NATP.
(defthm pic-prft-digest-rational-fuel-yields-unchanged
  (let* ((incoming '(65 66 67))
         (c (pic-prft-c :digest-commit 3 '(67 66 65)))
         (cursor (pic-prft-chunk))
         (next (mv-nth 1 (fn-pic-digest-next c 5/2 cursor)))
         (state (mv-nth 3 (fn-pic-digest-next c 5/2 cursor))))
    (and (fn-pic-digest-trajectoryp 0 c incoming cursor) (not (natp 5/2))
         (equal next c) (equal state cursor)
         (fn-pic-digest-trajectoryp 0 next incoming state)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-prft-c pic-prft-chunk fn-pic-digest-trajectoryp
    fn-pic-digest-next fn-pic-digest-effect fn-pic-block-prefixp
    pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
    pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
    pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span pgs-dcb-next-byte-offset
    pgs-dcb-read-demand pgs-dc-needs-block pgs-dcb-word-count)
    ((:executable-counterpart fn-pic-digest-next)
     (:executable-counterpart fn-pic-digest-effect)))
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))))

(defthm pic-prft-read-positive
  (let* ((incoming '(65 66 67)) (c (pic-prft-c :digest-read 0 nil))
         (cursor (pic-prft-chunk)) (next (mv-nth 1 (fn-pic-next c 2 incoming))))
    (and (fn-pic-digest-trajectoryp 0 c incoming cursor)
         (fn-pic-digest-trajectoryp 0 next incoming cursor)
         (equal (fn-pic-get block next) '(65))
         (equal (fn-pic-get pos next) 1)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pic-prft-c pic-prft-chunk fn-pic-digest-trajectoryp
    fn-pic-block-prefixp pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
    pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
    pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span pgs-dcb-next-byte-offset
    pgs-dcb-read-demand pgs-dc-needs-block pgs-dcb-word-count)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))))

(defthm pic-prft-read-invariant-removal-corrupted-buffer
  (let* ((incoming '(65 66 67)) (c (pic-prft-c :digest-read 1 nil))
         (cursor (pic-prft-chunk)) (next (mv-nth 1 (fn-pic-next c 2 incoming))))
    (and (not (fn-pic-digest-trajectoryp 0 c incoming cursor))
         (not (fn-pic-digest-trajectoryp 0 next incoming cursor))
         (equal (fn-pic-get block next) '(66))
         (equal (fn-pic-get pos next) 2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pic-prft-c pic-prft-chunk fn-pic-digest-trajectoryp
    fn-pic-block-prefixp pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
    pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
    pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span pgs-dcb-next-byte-offset
    pgs-dcb-read-demand pgs-dc-needs-block pgs-dcb-word-count)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))))
