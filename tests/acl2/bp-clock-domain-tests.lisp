; Physical boot domain is an ACL2-owned recovery gate for persisted BP age.
(in-package "ACL2")
(include-book "../../books/bp-clock-domain")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpcdt-boot-a*
  '(48 49 50 51 52 53 54 55 45 56 57 97 98 45 99 100 101 102 45
    48 49 50 51 45 52 53 54 55 56 57 97 98 99 100 101 102))
(defconst *bpcdt-boot-b*
  '(49 49 50 51 52 53 54 55 45 56 57 97 98 45 99 100 101 102 45
    48 49 50 51 45 52 53 54 55 56 57 97 98 99 100 101 102))

(defun bpcdt-observed (id)
  (append id '(10)))
(defun bpcdt-saved ()
  (fn-bpcd-frame *bpcdt-boot-a*))
(defun bpcdt-plan (saved present observed legacy lock-owned absent)
  (fn-bpnf-clock-domain-plan
   saved present observed legacy lock-owned absent))

(assert-event (fn-bpcd-boot-idp *bpcdt-boot-a*))
(assert-event (fn-bpcd-boot-idp *bpcdt-boot-b*))
(assert-event (equal (fn-bpcd-frame-limit) 82))
(assert-event (equal (len (bpcdt-saved)) 82))
(assert-event (equal (fn-bpcd-unframe (bpcdt-saved)) *bpcdt-boot-a*))
(must-fail
 (assert-event
  (equal (fn-bpcd-unframe
          (fn-bpcd-frame (cons 65 (cdr *bpcdt-boot-a*))))
         (cons 65 (cdr *bpcdt-boot-a*)))))
(assert-event (equal (fn-bpcd-observed-id (bpcdt-observed *bpcdt-boot-a*))
                     *bpcdt-boot-a*))
(assert-event (not (fn-bpcd-observed-id *bpcdt-boot-a*)))
(assert-event (not (fn-bpcd-observed-id
                    (append *bpcdt-boot-a* '(13 10)))))
(assert-event (not (fn-bpcd-boot-idp
                    (cons 65 (cdr *bpcdt-boot-a*)))))

; Fresh empty directory, then same-boot restart.  The publisher state is
; staging and is not durable until the directory barrier succeeds.
(assert-event
 (equal (bpcdt-plan nil nil (bpcdt-observed *bpcdt-boot-a*) nil t t)
        (list :initialize (bpcdt-saved) (fn-jpub-initial t))))
(assert-event
 (equal (bpcdt-plan (bpcdt-saved) t
                    (bpcdt-observed *bpcdt-boot-a*) nil t nil)
        (list :same *bpcdt-boot-a*)))
(assert-event
 (equal (fn-jpub-crash-outcome
         (fn-jpub-step
          (fn-jpub-step
           (fn-jpub-step (fn-jpub-initial t) '(:stage-result :ok))
           '(:file-barrier-result :ok))
          '(:link-begin)))
        :uncertain))

; Different boot fences independently of the clock counter.  A previously
; anchored age (0 . 20000) and a new-boot reading 1000 would spuriously look
; live; a new-boot reading 30000 would spuriously look expired.  Neither
; incomparable counter is passed to the expiry decision after this fence.
(assert-event
 (equal (fn-clock-expiry-decision
         0 1500 '(0 . 20000) (fn-clock-observation 1000 0 0 nil))
        :live))
(assert-event
 (equal (fn-clock-expiry-decision
         0 1500 '(0 . 20000) (fn-clock-observation 30000 0 0 nil))
        :expired))
(assert-event
 (equal (bpcdt-plan (bpcdt-saved) t
                    (bpcdt-observed *bpcdt-boot-b*) nil t nil)
        '(:fence :different-boot)))
(assert-event
 (equal (bpcdt-plan (bpcdt-saved) t
                    (bpcdt-observed *bpcdt-boot-b*) nil t t)
        '(:fence :different-boot)))
(must-fail
 (assert-event
  (equal (bpcdt-plan (bpcdt-saved) t
                     (bpcdt-observed *bpcdt-boot-b*) nil t nil)
         (list :same *bpcdt-boot-b*))))

; Missing marker with either legacy outbound or received FNBS obligation is
; never silently initialized.  A malformed mixed plan also counts as evidence.
(assert-event
 (fn-bpnf-clock-domain-legacy-evidence
  (list :ready (list (fn-bpn-lifecycle-record-name 0)) nil nil 1) nil))
(assert-event
 (fn-bpnf-clock-domain-legacy-evidence
  (list :ready nil (list (fn-bpnf-stored-record-name 0 0)) nil 0) nil))
(assert-event
 (fn-bpnf-clock-domain-legacy-evidence '(:fault :fnbs-namespace) nil))
(assert-event
 (fn-bpnf-clock-domain-legacy-evidence '(:ready nil nil nil 0) t))
(assert-event
 (equal (bpcdt-plan nil nil (bpcdt-observed *bpcdt-boot-a*) t t t)
        '(:fence :legacy-without-domain)))
(assert-event
 (equal (bpcdt-plan nil nil (bpcdt-observed *bpcdt-boot-a*) nil nil t)
        '(:fence :lock-authority)))
(assert-event
 (equal (bpcdt-plan nil nil (bpcdt-observed *bpcdt-boot-a*) nil t nil)
        '(:fence :name-observation)))
(must-fail
 (assert-event
  (equal (bpcdt-plan nil nil (bpcdt-observed *bpcdt-boot-a*) t t t)
         (list :initialize (bpcdt-saved) (fn-jpub-initial t)))))

; A visible but malformed marker remains a fault, including a short frame.
(assert-event
 (equal (bpcdt-plan '(70 78 66 83) t
                    (bpcdt-observed *bpcdt-boot-a*) nil t nil)
        '(:fence :domain-frame)))
(assert-event
 (equal (bpcdt-plan (cdr (bpcdt-saved)) t
                    (bpcdt-observed *bpcdt-boot-a*) nil t nil)
        '(:fence :domain-frame)))
(assert-event
 (equal (bpcdt-plan (bpcdt-saved) t *bpcdt-boot-a* nil t nil)
        '(:fence :boot-observation)))
