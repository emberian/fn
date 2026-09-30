(in-package "ACL2")
(include-book "../../books/consumer-config-metadata")
(local (include-book "consumer-account-metadata-tests"))

(defun fn-ccamt-hypotheses (cp metadata)
 (declare (xargs :guard t :verify-guards nil))
 (list (integerp (fn-cp-nth 3 cp))
       (fn-caam-authority-sizep (fn-cp-nth 6 cp))
       (equal metadata (fn-caam-annotation cp))
       (equal (car (fn-cca-preflight cp metadata)) :ok)))
(defun fn-ccamt-conclusion (cp metadata)
 (declare (xargs :guard t :verify-guards nil))
 (let ((approved (fn-cca-preflight cp metadata)))
  (fn-caam-correspondsp (fn-cp-nth 1 approved) (fn-cp-nth 2 approved))))

;@positive fn-ccam-actual-config-preflight-maintains-full-metadata
(assert-event
 (let* ((cp (fn-caammt-cp *caammt-fence*)) (metadata (cadr *caammt-fence*))
        (approved (fn-cca-preflight cp metadata))
        (next (fn-cp-nth 1 approved)))
  (and (equal (fn-ccamt-hypotheses cp metadata) '(t t t t))
       (fn-ccamt-conclusion cp metadata)
       (equal (fn-cp-nth 1 (fn-cp-nth 6 next))
              (1+ (fn-cp-nth 1 (fn-cp-nth 6 cp))))
       (equal (fn-cp-nth 4 (fn-cp-nth 6 next))
              (fn-cp-nth 4 (fn-cp-nth 6 cp)))
       (not (fn-cp-nth 5 (fn-cp-nth 6 next))))))

;@mutation-witness fn-ccam-config-discards-pending-without-adopting-it
(assert-event
 (let* ((cp (fn-caammt-cp *caammt-begin*)) (metadata (cadr *caammt-begin*))
        (approved (fn-cca-preflight cp metadata))
        (next (fn-cp-nth 1 approved)) (nm (fn-cp-nth 2 approved)))
  (and (equal (fn-ccamt-hypotheses cp metadata) '(t t t t))
       (fn-ccamt-conclusion cp metadata)
       (fn-cp-nth 5 (fn-cp-nth 6 cp))
       (not (fn-cp-nth 5 (fn-cp-nth 6 next)))
       (not (fn-cp-nth 3 nm))
       (equal (fn-cp-nth 4 (fn-cp-nth 6 next))
              (fn-cp-nth 4 (fn-cp-nth 6 cp))))))

; All removals are deliberately corrupted maintained state/input. Each
; affirmatively retains every other literal premise and falsifies conclusion.
;@hypothesis-removal fn-ccam-actual-config-preflight-maintains-full-metadata frontier-scalar
(assert-event
 (let* ((cp (update-nth 3 '(7) (fn-caammt-cp *caammt-fence*)))
        (m (fn-caam-annotation cp)))
  (and (equal (fn-ccamt-hypotheses cp m) '(nil t t t))
       (not (fn-ccamt-conclusion cp m)))))
;@hypothesis-removal fn-ccam-actual-config-preflight-maintains-full-metadata authority-size
(assert-event
 (let* ((original (fn-caammt-cp *caammt-fence*))
        (cp (update-nth 6 (update-nth 2 '(bad) (fn-cp-nth 6 original)) original))
        (m (fn-caam-annotation cp)))
  (and (equal (fn-ccamt-hypotheses cp m) '(t nil t t))
       (not (fn-ccamt-conclusion cp m)))))
;@hypothesis-removal fn-ccam-actual-config-preflight-maintains-full-metadata old-metadata
(assert-event
 (let* ((cp (fn-caammt-cp *caammt-fence*))
        (m (update-nth 1 nil (cadr *caammt-fence*))))
  (and (equal (fn-ccamt-hypotheses cp m) '(t t nil t))
       (not (fn-ccamt-conclusion cp m)))))
;@hypothesis-removal fn-ccam-actual-config-preflight-maintains-full-metadata approved
(assert-event
 (let* ((original (fn-caammt-cp *caammt-fence*))
        (cp (update-nth 6 (update-nth 1 *fn-cbor-max-uint* (fn-cp-nth 6 original)) original))
        (m (fn-caam-annotation cp)))
  (and (equal (fn-ccamt-hypotheses cp m) '(t t t nil))
       (not (fn-ccamt-conclusion cp m))
       (equal (fn-cca-preflight cp m) '(:refused :authority-revision-exhausted)))))
