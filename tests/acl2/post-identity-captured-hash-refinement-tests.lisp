(in-package "ACL2")
(include-book "../../books/post-identity-captured-hash-refinement")
(include-book "post-identity-captured-tests")

; Ground trace stops immediately before the actual terminal digest effect.
(defun pic-hrt-until-entry (c incoming held fuel pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil :measure (nfix fuel)))
 (if (or (zp fuel) (equal (fn-pic-get phase c) :done)
         (and (equal (fn-pic-get phase c) :digest-next)
              (equal (pgs-dc-mode pgs-digest-state) :done)))
  (mv c pgs-digest-state)
  (if (member-eq (fn-pic-get phase c) '(:digest-begin :digest-next :digest-commit))
   (mv-let (status next left pgs-digest-state) (fn-pic-digest-next c 2 pgs-digest-state)
    (declare (ignore status left))
    (pic-hrt-until-entry next incoming held (1- fuel) pgs-digest-state))
   (pic-hrt-until-entry (pic-test-drive c incoming held 1) incoming held (1- fuel) pgs-digest-state))))
(defun-nx pic-hrt-before (incoming held)
 (declare (xargs :stobjs nil :verify-guards nil))
 (mv-list 2 (pic-hrt-until-entry
  (fn-pic-begin *pic-test-selected* *pic-test-grant*
   (pic-test-held "<m>" nil *pic-test-binding*) *pic-test-incoming*
   (len incoming) "<m>" *pic-test-binding* nil)
  incoming held 1000 (create-pgs-digest-state))))
(defconst *pic-hrt-held*
 (pic-test-tomb 0 *pic-test-abc-hash* (make-list 32 :initial-element 0) nil))
(defun-nx pic-hrt-before-whole () (pic-hrt-before '(97 98 99) *pic-hrt-held*))
(defun-nx pic-hrt-start ()
 (declare (xargs :stobjs nil :verify-guards nil))
 (mv-nth 1 (fn-pic-digest-next (car (pic-hrt-before-whole)) 2 (cadr (pic-hrt-before-whole)))))
(defun pic-hrt-observation (c byte)
 (list :payload-byte (fn-pic-get selected c) (fn-pic-get grant c) 0
       (fn-pic-at 1 (fn-pic-demand c)) byte))

(defthm pic-hrt-digest-entry-positive
 (let* ((c (car (pic-hrt-before-whole))) (cursor (cadr (pic-hrt-before-whole)))
        (next (mv-nth 1 (fn-pic-digest-next c 2 cursor))))
  (and (fn-pic-digest-trajectoryp 0 c '(97 98 99) cursor)
       (fn-pic-hash-entry-layoutp c *pic-hrt-held*)
       (equal (fn-pic-get phase c) :digest-next)
       (equal (fn-pic-get phase next) :digest-compare)
       (fn-pic-hash-productp next '(97 98 99) *pic-hrt-held*)
       (equal (fn-pic-get digest next) (fn-blake3 '(97 98 99)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-digest-trajectoryp
    pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
    pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
    pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span pgs-dcb-word-count)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))))
(defthm pic-hrt-feedback-positive-resumption
 (let* ((c (pic-hrt-start)) (observation (pic-hrt-observation c 100))
        (next (mv-nth 1 (fn-pic-feed-funded c observation 1))))
  (and (fn-pic-hash-productp c '(97 98 99) *pic-hrt-held*)
       (fn-pic-hash-observationp c observation *pic-hrt-held*)
       (fn-pic-hash-outcomep next '(97 98 99) *pic-hrt-held*)
       (fn-pic-hash-productp next '(97 98 99) *pic-hrt-held*)
       (equal (fn-pic-get pos next) 1)))
 :rule-classes nil)
(defthm pic-hrt-feedback-positive-conflict
 (let* ((held (update-nth 9 101 *pic-hrt-held*))
        (c (pic-hrt-start)) (observation (pic-hrt-observation c 101))
        (next (mv-nth 1 (fn-pic-feed-funded c observation 1))))
  (and (fn-pic-hash-productp c '(97 98 99) held)
       (fn-pic-hash-observationp c observation held)
       (fn-pic-hash-outcomep next '(97 98 99) held)
       (equal (fn-pic-get phase next) :done) (equal (fn-pic-get result next) :conflict)))
 :rule-classes nil)
(defun pic-hrt-until-complete (c held fuel)
 (declare (xargs :measure (nfix fuel) :verify-guards nil))
 (if (or (zp fuel) (equal (fn-pic-get phase c) :done) (equal (fn-pic-demand c) :control)) c
  (pic-hrt-until-complete (pic-test-drive c '(97 98 99) held 1) held (1- fuel))))
(defthm pic-hrt-read-positive-equality
 (let* ((c (pic-hrt-until-complete (pic-hrt-start) *pic-hrt-held* 32))
        (next (mv-nth 1 (fn-pic-next c 1 '(97 98 99)))))
  (and (fn-pic-hash-productp c '(97 98 99) *pic-hrt-held*)
       (fn-pic-hash-observationp c :control *pic-hrt-held*)
       (fn-pic-hash-outcomep next '(97 98 99) *pic-hrt-held*)
       (equal (fn-pic-get phase next) :groups)
       (equal (fn-pic-get digest next) (take 32 (nthcdr 9 *pic-hrt-held*)))
       (equal (fn-pic-get digest next) (fn-blake3 '(97 98 99)))))
 :rule-classes nil)

; Corrupted prefix skips a wrong stored digest; exact control and the entire
; input extent remain. Both actual continuations falsely confirm equality.
(defthm pic-hrt-product-removal-corrupted-prefix
 (let* ((held (update-nth 9 101 *pic-hrt-held*)) (c (fn-pic-set pos 32 (pic-hrt-start)))
        (a (mv-nth 1 (fn-pic-feed-funded c :control 1)))
        (b (mv-nth 1 (fn-pic-next c 1 '(97 98 99)))))
  (and (not (fn-pic-hash-productp c '(97 98 99) held))
       (fn-pic-hash-observationp c :control held)
       (not (fn-pic-hash-outcomep a '(97 98 99) held))
       (not (fn-pic-hash-outcomep b '(97 98 99) held))
       (equal (fn-pic-get phase a) :groups) (equal (fn-pic-get phase b) :groups)))
 :rule-classes nil)
; Mutated byte passes the typed gate but disagrees with the leased source.
(defthm pic-hrt-observation-removal-mutated-byte
 (let* ((c (pic-hrt-start)) (observation (pic-hrt-observation c 101))
        (next (mv-nth 1 (fn-pic-feed-funded c observation 1))))
  (and (fn-pic-hash-productp c '(97 98 99) *pic-hrt-held*)
       (fn-pic-observation-okp c (fn-pic-demand c) observation)
       (not (fn-pic-hash-observationp c observation *pic-hrt-held*))
       (not (fn-pic-hash-outcomep next '(97 98 99) *pic-hrt-held*))
       (equal (fn-pic-get result next) :conflict)))
 :rule-classes nil)
; Corrupted digest semantics: scalar completion is genuine for different
; bytes, but the retained virtual message is changed after computation.
(defthm pic-hrt-entry-trajectory-removal-mutated-message
 (let* ((c (car (pic-hrt-before-whole))) (cursor (cadr (pic-hrt-before-whole)))
        (next (mv-nth 1 (fn-pic-digest-next c 2 cursor))))
  (and (not (fn-pic-digest-trajectoryp 0 c '(97 98 100) cursor))
       (fn-pic-hash-entry-layoutp c *pic-hrt-held*)
       (equal (fn-pic-get phase c) :digest-next)
       (equal (fn-pic-get phase next) :digest-compare)
       (not (fn-pic-hash-productp next '(97 98 100) *pic-hrt-held*))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-digest-trajectoryp
    pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
    pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
    pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span pgs-dcb-word-count)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))))
; Corrupted retained held extent leaves the full digest trajectory and phase.
(defthm pic-hrt-entry-layout-removal-corrupted-held-extent
 (let* ((c (fn-pic-set held-n 146 (car (pic-hrt-before-whole)))) (cursor (cadr (pic-hrt-before-whole)))
        (next (mv-nth 1 (fn-pic-digest-next c 2 cursor))))
  (and (fn-pic-digest-trajectoryp 0 c '(97 98 99) cursor)
       (not (fn-pic-hash-entry-layoutp c *pic-hrt-held*))
       (equal (fn-pic-get phase c) :digest-next)
       (equal (fn-pic-get phase next) :digest-compare)
       (not (fn-pic-hash-productp next '(97 98 99) *pic-hrt-held*))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-digest-trajectoryp
    pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
    pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
    pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span pgs-dcb-word-count)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))))
; Existing corrupt prefix survives a zero-fuel call; completed hash semantics
; and held layout remain, but the entry phase is false.
(defthm pic-hrt-entry-phase-removal-corrupted-existing-prefix
 (let* ((held (update-nth 9 101 *pic-hrt-held*)) (c (fn-pic-set pos 32 (pic-hrt-start)))
        (cursor (cadr (pic-hrt-before-whole))) (next (mv-nth 1 (fn-pic-digest-next c 0 cursor))))
  (and (fn-pic-digest-trajectoryp 0 c '(97 98 99) cursor)
       (fn-pic-hash-entry-layoutp c held)
       (not (equal (fn-pic-get phase c) :digest-next))
       (equal (fn-pic-get phase next) :digest-compare)
       (not (fn-pic-hash-productp next '(97 98 99) held))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-digest-trajectoryp
    pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
    pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
    pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span pgs-dcb-word-count)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))))

; The source-hash branch reaches base41 through the actual incoming-agent
; comparison and hashes the retained virtual source, not the stamped bytes.
(defthm pic-hrt-source-digest-entry-positive
 (let* ((held (pic-test-tomb 1 (make-list 32 :initial-element 0)
                 (fn-blake3 *pic-test-source*) *pic-test-source-agent*))
        (trace (pic-hrt-before *pic-test-stamped* held)) (c (car trace)) (cursor (cadr trace))
        (next (mv-nth 1 (fn-pic-digest-next c 2 cursor))))
  (and (fn-pic-digest-trajectoryp 0 c *pic-test-stamped* cursor)
       (fn-pic-hash-entry-layoutp c held)
       (equal (fn-pic-get phase c) :digest-next)
       (equal (fn-pic-get phase next) :digest-compare)
       (fn-pic-hash-productp next *pic-test-stamped* held)
       (equal (fn-pic-get digest-base next) 41)
       (equal (fn-pic-span-value (fn-pic-get digest-desc next) *pic-test-stamped*) *pic-test-source*)
       (equal (fn-pic-get digest next) (fn-blake3 *pic-test-source*))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-digest-trajectoryp
    pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
    pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
    pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span pgs-dcb-word-count)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor))))))
