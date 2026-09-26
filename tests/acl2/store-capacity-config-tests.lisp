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

; -----------------------------------------------------------------------------
; PRF-171 (PKT-451 (C)): field 7, max-group-name-octets, governs a created
; group's name (fn-cvec-native-admin-authorize, called by
; host/store-node-host.lisp fn-store-cfg-native-admin-authorize).

(defconst *cvc-p100*
  (fn-bs-profile-set-fields *fn-bs-profile-defaults* '((7 . 100))))
(defconst *cvc-name-100*
  (coerce (append (coerce "fn." 'list) (make-list 97 :initial-element #\a))
          'string))
(defconst *cvc-name-101*
  (coerce (append (coerce "fn." 'list) (make-list 98 :initial-element #\a))
          'string))
(defconst *cvc-create-100*
  (fn-cfg-record-make 1 0 2 (list (fn-cfg-create-group *cvc-name-100* ""))
                      *cvc-stamp*))
(defconst *cvc-create-101*
  (fn-cfg-record-make 1 0 2 (list (fn-cfg-create-group *cvc-name-101* ""))
                      *cvc-stamp*))
(defun cvc-group-authorize (record profile)
  (fn-cvec-native-admin-authorize nil 0 (list *fn-cfg-default-record*) record
                                  t nil profile))
(assert-event (and (equal (fn-bs-profile-max-group-name-octets *cvc-p100*) 100)
                   (equal (len (fn-record-string-octets *cvc-name-100*)) 100)
                   (equal (len (fn-record-string-octets *cvc-name-101*)) 101)
                   (fn-record-group-namep *cvc-name-101*)))
; Reachable witness at the bound: a 100-octet name under field 7 = 100 is
; within and accepted at generation 2, the publication it always was.
(assert-event
 (let ((r (cvc-group-authorize *cvc-create-100* *cvc-p100*)))
   (and (fn-cvec-group-names-within (fn-cfg-record-change *cvc-create-100*) 100)
        (equal (fn-native-admin-publication-status r) :accepted)
        (equal (fn-native-admin-publication-generation r) 2)
        (equal r (fn-native-admin-publication-authorize
                  nil 0 (list *fn-cfg-default-record*) *cvc-create-100* t nil
                  (fn-cvec-config-generations *cvc-p100* *cvc-create-100*))))))
; Past the bound: 101 octets is refused by name, and the refusal is not the
; publication (which would have accepted it): the conclusion of the second
; conjunct fails without its hypothesis.
(assert-event
 (let ((r (cvc-group-authorize *cvc-create-101* *cvc-p100*)))
   (and (not (fn-cvec-group-names-within
              (fn-cfg-record-change *cvc-create-101*) 100))
        (equal (fn-native-admin-publication-status r) :refused)
        (equal (fn-native-admin-publication-reason r) :max-group-name-octets)
        (equal (fn-native-admin-publication-status
                (fn-native-admin-publication-authorize
                 nil 0 (list *fn-cfg-default-record*) *cvc-create-101* t nil
                 (fn-cvec-config-generations *cvc-p100* *cvc-create-101*)))
               :accepted))))
; Field 7 is what refuses: the default profile (field 7 = 256) accepts the
; same 101-octet name.
(assert-event
 (and (equal (fn-bs-profile-max-group-name-octets *fn-bs-profile-defaults*) 256)
      (equal (fn-native-admin-publication-status
              (cvc-group-authorize *cvc-create-101* *fn-bs-profile-defaults*))
             :accepted)))
; A record creating no group is untouched by field 7 (even at 1).
(defconst *cvc-p1* (fn-bs-profile-set-fields *fn-bs-profile-defaults* '((7 . 1))))
(assert-event
 (and (equal (fn-bs-profile-max-group-name-octets *cvc-p1*) 1)
      (equal (fn-native-admin-publication-status
              (cvc-group-authorize *cvc-other* *cvc-p1*))
             :accepted)
      (equal (cvc-group-authorize *cvc-other* *cvc-p1*)
             (fn-native-admin-publication-authorize
              nil 0 (list *fn-cfg-default-record*) *cvc-other* t nil
              (fn-cvec-config-generations *cvc-p1* *cvc-other*)))))
; fn-cvec-accepted-group-names-are-within-the-profile: its hypothesis
; (acceptance) removed, the 101-octet record is not within field 7.
(must-fail
 (defthm cvc-group-names-within-without-acceptance
   (fn-cvec-group-names-within
    (fn-cfg-record-change *cvc-create-101*)
    (fn-bs-profile-max-group-name-octets *cvc-p100*))))
(assert-event
 (and (not (equal (fn-native-admin-publication-status
                   (cvc-group-authorize *cvc-create-101* *cvc-p100*))
                  :accepted))
      (not (fn-cvec-group-names-within
            (fn-cfg-record-change *cvc-create-101*)
            (fn-bs-profile-max-group-name-octets *cvc-p100*)))))
