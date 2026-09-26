; Witnesses and teeth for books/store-capacity-config (PRF-138, STO-020):
; the configuration namespace keeps its last generation for the retention
; rule.  Fixtures after tests/acl2/native-admin-tests.lisp: the default
; configuration record at generation 1 and a second record at generation 2.
(in-package "ACL2")
(include-book "../../books/store-capacity-config")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *cvc-stamp* (fn-clock-observation 7 9 0 t))
; An ordinary second record (a capacity change) and the retention rule's
; (`retention set released-by-all-holders': two :set-limit rows).
(defconst *cvc-other*
  (fn-cfg-record-make 1 0 2 (list (fn-cfg-set-capacity 1048576)) *cvc-stamp*))
(defconst *cvc-release*
  (fn-cfg-record-make 1 0 2 (fn-rcl-rule-deltas '(:released-by-all-holders))
                      *cvc-stamp*))
(assert-event (and (fn-cvec-retention-recordp *cvc-release*)
                   (not (fn-cvec-retention-recordp *cvc-other*))))
; A profile whose max-config-generations is 2: generation 2 is the last.
(defconst *cvc-profile*
  (fn-bs-profile-set-fields *fn-bs-profile-defaults* '((11 . 2))))
(assert-event (and (equal (fn-bs-profile-max-config-generations *cvc-profile*) 2)
                   (equal (fn-cvec-config-generations *cvc-profile* *cvc-other*) 1)
                   (equal (fn-cvec-config-generations *cvc-profile* *cvc-release*) 2)))

(defun cvc-authorize (record)
  (fn-native-admin-publication-authorize
   nil 0 (list *fn-cfg-default-record*) record t nil
   (fn-cvec-config-generations *cvc-profile* record)))

; Reachable witness: the retention rule takes the last generation (2).
(assert-event
 (and (equal (fn-native-admin-publication-status (cvc-authorize *cvc-release*))
             :accepted)
      (equal (fn-native-admin-publication-generation (cvc-authorize *cvc-release*))
             2)))
; The keystone's subject: the ordinary record is refused the last generation
; by name, so it never reaches generation 2.
(assert-event
 (and (equal (fn-native-admin-publication-status (cvc-authorize *cvc-other*))
             :refused)
      (equal (fn-native-admin-publication-reason (cvc-authorize *cvc-other*))
             :max-config-generations)))
; Below the last generation the ordinary record is accepted (bound 3).
(assert-event
 (let ((p (fn-bs-profile-set-fields *fn-bs-profile-defaults* '((11 . 3)))))
   (and (equal (fn-native-admin-publication-status
                (fn-native-admin-publication-authorize
                 nil 0 (list *fn-cfg-default-record*) *cvc-other* t nil
                 (fn-cvec-config-generations p *cvc-other*)))
               :accepted)
        (< 2 (fn-bs-profile-max-config-generations p)))))
; Tooth, the retention hypothesis: the retention rule's accepted generation
; is the last one, not below it.
(assert-event
 (not (< (fn-native-admin-publication-generation (cvc-authorize *cvc-release*))
         (fn-bs-profile-max-config-generations *cvc-profile*))))
; Tooth, acceptance: the refused value carries no generation below the bound.
(assert-event
 (not (natp (fn-native-admin-publication-generation (cvc-authorize *cvc-other*)))))
; Tooth, the reservation itself: the profile's own bound (what the host
; passed before PRF-138) accepts the ordinary record at the last generation.
(assert-event
 (equal (fn-native-admin-publication-generation
         (fn-native-admin-publication-authorize
          nil 0 (list *fn-cfg-default-record*) *cvc-other* t nil
          (fn-bs-profile-max-config-generations *cvc-profile*)))
        2))
