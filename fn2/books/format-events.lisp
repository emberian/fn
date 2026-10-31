; Independent declaration family; format.lisp exports the complete catalog.
(in-package "ACL2")
(include-book "format-base")
(fn2-book-layer :b)

; Maintenance has a kind/version but no semantic event number.
(deflayout fn2-format-maintenance-header
  `((record-kind ,*fn2-format-record-kind*) (schema-version :u8)))
(assert-event (fn2-layoutp *fn2-format-maintenance-header*))
(assert-event (equal (fn2-layout-max-size *fn2-format-maintenance-header*) 2))

; One record is one event; its header is the event envelope (WIDEST-ROLE §3
; decision 2, IDENTITY-ACROSS-PEERS ruling 2). The event is its commit
; position. The other fields carry no behaviour yet:
; - revision: the revision the event was decided under.
; - occurrence: the event's occurrence identity, distinct from content identity.
; - lineage, domain, incarnation: the origin of an acceptance.
; - author, payer, grant: the author key, the payer principal, the grant acted under.
; A field with nothing to name is 0, one octet.
(deflayout fn2-format-record-header
  (append *fn2-format-maintenance-header*
          '((event (:id event)) (revision (:id revision)) (occurrence (:id occurrence))
            (lineage (:id lineage)) (domain (:id domain)) (incarnation (:id incarnation))
            (author (:id key)) (payer (:id principal)) (grant (:id grant)))))
(assert-event (fn2-layoutp *fn2-format-record-header*))
(assert-event (equal (fn2-layout-max-size *fn2-format-record-header*) 83))

(deflayout fn2-format-operation-header
  `((principal (:id principal)) (operation (:id operation))))
(assert-event (fn2-layoutp *fn2-format-operation-header*))
(assert-event (equal (fn2-layout-max-size *fn2-format-operation-header*) 18))

(deflayout fn2-format-article-acceptance
  (append
    `((article (:id article)) (message-id (:octets ,*fn2-format-message-id-max*)) (source-identity :digest) (source-length :varint))
    (fn2-format-prefix "SOURCE-" *fn2-format-ref*)
    (fn2-format-prefix "PROJECTION-" *fn2-format-ref*)
    (fn2-format-prefix "MEMBERSHIPS-" *fn2-format-ref*)
    `((membership-count :varint))
    (fn2-format-prefix "ACCEPTANCE-" *fn2-format-ref*)
    (fn2-format-prefix "CONFIGURATION-" *fn2-format-ref*)
    (fn2-format-prefix "CHARGES-" *fn2-format-ref*)
    (fn2-format-prefix "CREATED-OBLIGATIONS-" *fn2-format-ref*)
    '((outcome :varint))))
(assert-event (fn2-layoutp *fn2-format-article-acceptance*))
(assert-event (equal (fn2-layout-max-size *fn2-format-article-acceptance*) 874))

(deflayout fn2-format-cursor-advance
  (append
    `((registration (:id registration)) (previous-event (:id event)) (next-event (:id event)))
    (fn2-format-prefix "SELECTION-" *fn2-format-ref*)
    '((outcome :varint))))
(assert-event (fn2-layoutp *fn2-format-cursor-advance*))
(assert-event (equal (fn2-layout-max-size *fn2-format-cursor-advance*) 115))

(deflayout fn2-format-registration-change
  (append
    `((registration (:id registration)) (previous-version (:id event)))
    (fn2-format-prefix "CONTRACT-" *fn2-format-ref*)
    '((outcome :varint))))
(assert-event (fn2-layoutp *fn2-format-registration-change*))
(assert-event (equal (fn2-layout-max-size *fn2-format-registration-change*) 106))

(deflayout fn2-format-configuration-change
  (append
    `((configuration (:id configuration)) (previous-generation (:id configuration)))
    (fn2-format-prefix "VALUE-" *fn2-format-ref*)
    '((outcome :varint))))
(assert-event (fn2-layoutp *fn2-format-configuration-change*))
(assert-event (equal (fn2-layout-max-size *fn2-format-configuration-change*) 106))

(deflayout fn2-format-withdrawal
  (append
    `((article (:id article)))
    (fn2-format-prefix "AUTHORIZATION-" *fn2-format-ref*)
    '((outcome :varint))))
(assert-event (fn2-layoutp *fn2-format-withdrawal*))
(assert-event (equal (fn2-layout-max-size *fn2-format-withdrawal*) 97))

(deflayout fn2-format-obligation-create
  (append
    `((obligation (:id obligation)) (owner (:id principal)) (article (:id article)))
    (fn2-format-prefix "TERMS-" *fn2-format-ref*)
    (fn2-format-prefix "CHARGES-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-obligation-create*))
(assert-event (equal (fn2-layout-max-size *fn2-format-obligation-create*) 185))

(deflayout fn2-format-obligation-release
  (append
    `((obligation (:id obligation)))
    (fn2-format-prefix "RELEASE-EVIDENCE-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-obligation-release*))
(assert-event (equal (fn2-layout-max-size *fn2-format-obligation-release*) 88))

(deflayout fn2-format-keyed-mutation
  (append
    `((table (:id table)) (object (:id object)) (principal (:id principal)) (operation (:id operation)) (binding :digest) (expected-prior-version (:id event)))
    (fn2-format-prefix "NEW-VALUE-" *fn2-format-ref*)
    '((outcome :varint))))
(assert-event (fn2-layoutp *fn2-format-keyed-mutation*))
(assert-event (equal (fn2-layout-max-size *fn2-format-keyed-mutation*) 166))

(deflayout fn2-format-allocation
  `((extent (:id extent)) (owner-kind :u8) (owner (:id owner)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation))))
(assert-event (fn2-layoutp *fn2-format-allocation*))
(assert-event (equal (fn2-layout-max-size *fn2-format-allocation*) 37))

(deflayout fn2-format-relocation
  (append
    `((object (:id object)))
    (fn2-format-prefix "OLD-" *fn2-format-ref*)
    (fn2-format-prefix "NEW-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-relocation*))
(assert-event (equal (fn2-layout-max-size *fn2-format-relocation*) 167))

(deflayout fn2-format-run-replacement
  (append
    `((schema (:id schema)))
    (fn2-format-prefix "OLD-RUNS-" *fn2-format-ref*)
    (fn2-format-prefix "NEW-RUNS-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-run-replacement*))
(assert-event (equal (fn2-layout-max-size *fn2-format-run-replacement*) 167))

(deflayout fn2-format-retirement
  `((extent (:id extent)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation)) (retirement-commit (:id commit))))
(assert-event (fn2-layoutp *fn2-format-retirement*))
(assert-event (equal (fn2-layout-max-size *fn2-format-retirement*) 36))

(deflayout fn2-format-release-allocation
  (append
    `((extent (:id extent)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation)) (retirement-commit (:id commit)) (promoted-checkpoint (:id checkpoint)))
    (fn2-format-prefix "RELEASE-EVIDENCE-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-release-allocation*))
(assert-event (equal (fn2-layout-max-size *fn2-format-release-allocation*) 124))

(deflayout fn2-format-checkpoint-installation
  (append
    `((checkpoint (:id checkpoint)))
    (fn2-format-prefix "DESCRIPTOR-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-checkpoint-installation*))
(assert-event (equal (fn2-layout-max-size *fn2-format-checkpoint-installation*) 88))

(deflayout fn2-format-begin-writer-epoch
  `((history (:id history)) (incarnation (:id incarnation)) (previous-writer-epoch (:id writer-epoch)) (writer-epoch (:id writer-epoch))))
(assert-event (fn2-layoutp *fn2-format-begin-writer-epoch*))
(assert-event (equal (fn2-layout-max-size *fn2-format-begin-writer-epoch*) 36))

(deflayout fn2-format-checkpoint-statement
  (append
    `((history (:id history)) (incarnation (:id incarnation)) (event-cut (:id event)) (event-root :digest) (fold-schema (:id schema)) (summary-commitment :digest) (exact-identity-commitment :digest))
    (fn2-format-prefix "DESCRIPTOR-" *fn2-format-ref*)
    (fn2-format-prefix "AUTHORIZED-KEYS-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-checkpoint-statement*))
(assert-event (equal (fn2-layout-max-size *fn2-format-checkpoint-statement*) 293))

