; Teeth for the bounded native administrative command plan.
(in-package "ACL2")
(include-book "../../books/native-admin")

(defun fn-na-test-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words))
            (fn-na-test-argv (cdr words)))
    nil))

(defconst *fn-na-create*
  (fn-native-admin-plan (fn-na-test-argv '("group" "create" "fn.admin"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-create*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-create*) :create-group))
(assert-event (equal (fn-native-admin-result-name *fn-na-create*)
                     (fn-record-string-octets "fn.admin")))

(defconst *fn-na-retire*
  (fn-native-admin-plan (fn-na-test-argv '("group" "retire" "fn.admin"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-retire*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-retire*) :remove-group))

(defconst *fn-na-capacity*
  (fn-native-admin-plan (fn-na-test-argv '("capacity" "1048576"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-capacity*) :accepted))
(assert-event (equal (fn-native-admin-result-capacity *fn-na-capacity*) 1048576))

(defconst *fn-na-peer-add*
  (fn-native-admin-plan
   (list (fn-record-string-octets "peer")
         (fn-record-string-octets "add")
         (fn-record-string-octets "far")
         (fn-record-string-octets "far.example")
         (fn-record-string-octets "192.0.2.44")
         (fn-record-string-octets "1119")
         (fn-record-string-octets "fn.*")
         (fn-record-string-octets "fn.*")
         (fn-record-string-octets "192.0.2.44")
         (fn-record-string-octets "true"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-peer-add*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-peer-add*) :set-peer))
(assert-event (fn-cfg-peerp (fn-native-admin-result-peer *fn-na-peer-add*)))
(assert-event
 (equal (fn-cfg-peer-transport (fn-native-admin-result-peer *fn-na-peer-add*))
        '(:nntp "192.0.2.44" 1119)))
(assert-event
 (equal (fn-cfg-peer-auth (fn-native-admin-result-peer *fn-na-peer-add*))
        '(:source-address "192.0.2.44")))
(assert-event
 (equal (fn-native-admin-result-status
         (fn-native-admin-plan
          (list (fn-record-string-octets "peer")
                (fn-record-string-octets "add")
                (fn-record-string-octets "far")
                (fn-record-string-octets "far.example")
                (fn-record-string-octets "192.0.2.44")
                (fn-record-string-octets "70000")
                (fn-record-string-octets "fn.*")
                (fn-record-string-octets "fn.*")
                (fn-record-string-octets "192.0.2.44")
                (fn-record-string-octets "true"))))
        :refused))
(assert-event
 (equal (fn-native-admin-result-status
         (fn-native-admin-plan
          (list (fn-record-string-octets "peer")
                (fn-record-string-octets "add")
                (fn-record-string-octets "far")
                (fn-record-string-octets "far.example")
                (fn-record-string-octets "192.0.2.44")
                (fn-record-string-octets "1119")
                (fn-record-string-octets "fn.*")
                (fn-record-string-octets "fn.*")
                (fn-record-string-octets "192.000.2.44")
                (fn-record-string-octets "true"))))
        :refused))
(defconst *fn-na-peer-remove*
  (fn-native-admin-plan
   (list (fn-record-string-octets "peer")
         (fn-record-string-octets "remove")
         (fn-record-string-octets "far"))))
(assert-event (equal (fn-native-admin-result-kind *fn-na-peer-remove*) :remove-peer))

; Leading zeroes, signs, overflow, malformed verbs, and non-group labels are
; all refusals before the physical adapter acquires a writable store.
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("capacity" "01"))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("capacity" "+1"))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("capacity" "4294967296"))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("group" "create" ""))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("group" "remove" "fn.admin"))))
                     :refused))

; The persistent generation namespace uses byte-store's ACL2 digit renderer;
; a raw `format' implementation cannot pass these fixed-name witnesses.
(assert-event (equal (fn-native-admin-config-name 1) "00000001.cfg"))
(assert-event (equal (fn-native-admin-config-name 99999999) "99999999.cfg"))
(assert-event (equal (fn-native-admin-config-name 100000000) nil))

; Candidate validation is the logical replay/open predicate the host wrapper
; calls after byte decoding.  The default durable record opens an empty image;
; an out-of-range frontier is a reachable differing observation and refuses.
(assert-event (fn-native-admin-candidate-openp nil 0 (list *fn-cfg-default-record*)))
(assert-event (not (fn-native-admin-candidate-openp nil 4294967296
                                                 (list *fn-cfg-default-record*))))

; Raw clocks are observations only.  ACL2 accepts a schema-representable pair
; and refuses an out-of-domain value without wrapping it.
(assert-event (equal (fn-native-admin-clock-status
                      (fn-native-admin-clock-observation 7 9)) :accepted))
(assert-event (equal (fn-native-admin-clock-status
                      (fn-native-admin-clock-observation -1 9)) :refused))

; Publication authorization cannot be reached without the observed exclusive
; lock.  This separates the raw lock observation from the ACL2 authority it
; must satisfy before a fn-jpub state is returned.
(assert-event (equal (fn-native-admin-publication-status
                      (fn-native-admin-publication-authorize nil 0 nil nil nil nil))
                     :refused))

; A second, admissible configuration record is authorized only for the exact
; next ACL2-rendered name.  An observed collision for that name refuses before
; any shared immutable-publisher state is exposed to the raw adapter.
(defconst *fn-na-second-record*
  (fn-cfg-record-make
   1 0 2 (list (fn-cfg-set-capacity 1048576))
   (fn-clock-observation 7 9 0 t)))
(defconst *fn-na-publication*
  (fn-native-admin-publication-authorize
   nil 0 (list *fn-cfg-default-record*) *fn-na-second-record* t nil))
(assert-event (equal (fn-native-admin-publication-status *fn-na-publication*)
                     :accepted))
(assert-event (equal (fn-native-admin-publication-generation *fn-na-publication*) 2))
(assert-event (equal (fn-native-admin-publication-name *fn-na-publication*)
                     "00000002.cfg"))
(assert-event (equal (fn-jpub-phase
                      (fn-native-admin-publication-jpub *fn-na-publication*))
                     :staging))
(assert-event
 (equal (fn-native-admin-publication-status
         (fn-native-admin-publication-authorize
          nil 0 (list *fn-cfg-default-record*) *fn-na-second-record* t
          '("00000002.cfg")))
        :refused))
