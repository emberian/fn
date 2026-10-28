; The storage format is data interpreted by layout.lisp. No integrity checker.
; Operation outcomes are inline canonical codes (the stable outcome of a keyed
; mutation or acceptance is a small closed vocabulary owned by the layer that
; defines the operation), never an external page: one isolated ack must not
; cost a Ref (seat review of B2c).
(in-package "ACL2")
(include-book "layout")
(defconst *fn2-format-version* 1)
(defconst *fn2-format-bootstrap-magic* #x44473246) ; F2GD
(defconst *fn2-format-page-magic* #x47503246) ; F2PG
(defconst *fn2-format-frame-magic* #x524a3246) ; F2JR
(defconst *fn2-format-sector-size* 4096)
(defconst *fn2-format-page-size* 65536)
; ENVELOPE-AND-HOST section 1.6: exact Message-ID octets, maximum 250.
(defconst *fn2-format-message-id-max* 250)
(defconst *fn2-format-page-kind* '(:enum page-kind (:run-data :run-index :partitioned-filter :manifest :allocation-map :source-manifest :range-proof :checkpoint-descriptor :merkle-node :raw-source :key-list :recovery-arena :dependency-manifest :membership-list :obligation-list)))
(defconst *fn2-format-record-kind* '(:enum record-kind (:article-acceptance :cursor-advance :registration-change :configuration-change :withdrawal :obligation-create :obligation-release :keyed-mutation :allocation :relocation :run-replacement :retirement :release-allocation :checkpoint-installation :begin-writer-epoch :checkpoint-statement)))
; Defconst-time composition only, never called by the served codec.
(defun fn2-format-prefix (prefix fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (list (intern-in-package-of-symbol
                  (concatenate 'string prefix (symbol-name (caar fields))) 'fn2-format-prefix)
                (cadar fields))
          (fn2-format-prefix prefix (cdr fields)))))

(defconst *fn2-format-ref*
  `((storage-domain (:id storage-domain)) (physical-unit (:id physical-unit)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation)) (page-kind ,*fn2-format-page-kind*) (encoded-length :varint) (expected-hash :digest)))
(assert-event (fn2-layoutp *fn2-format-ref*))
(assert-event (equal (fn2-layout-max-size *fn2-format-ref*) 79))

(defconst *fn2-format-bootstrap*
  `((magic :u32) (version :u8) (sector-size :varint) (page-size :varint) (anchor-0 (:id physical-unit)) (anchor-1 (:id physical-unit)) (anchor-2 (:id physical-unit)) (anchor-3 (:id physical-unit)) (storage-domain (:id storage-domain)) (geometry-hash :digest)))
(assert-event (fn2-layoutp *fn2-format-bootstrap*))
(assert-event (equal (fn2-layout-max-size *fn2-format-bootstrap*) 101))

(defconst *fn2-format-anchor*
  (append
    `((slot (:id anchor-slot)) (history (:id history)) (incarnation (:id incarnation)) (checkpoint (:id checkpoint)) (checkpoint-batch :digest))
    (fn2-format-prefix "DESCRIPTOR-" *fn2-format-ref*)
    `((previous-checkpoint :digest) (geometry :digest) (anchor-hash :digest))))
(assert-event (fn2-layoutp *fn2-format-anchor*))
(assert-event (equal (fn2-layout-max-size *fn2-format-anchor*) 247))

(defconst *fn2-format-page-header*
  `((magic :u32) (version :u8) (page-kind ,*fn2-format-page-kind*) (history (:id history)) (incarnation (:id incarnation)) (physical-unit (:id physical-unit)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation)) (header-length :varint) (payload-length :varint)))
(assert-event (fn2-layoutp *fn2-format-page-header*))
(assert-event (equal (fn2-layout-max-size *fn2-format-page-header*) 69))

(defconst *fn2-format-raw-source-context*
  `((storage-domain (:id storage-domain)) (history (:id history)) (incarnation (:id incarnation)) (physical-unit (:id physical-unit)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation)) (actual-length :varint) (logical-source-offset :varint)))
(assert-event (fn2-layoutp *fn2-format-raw-source-context*))
(assert-event (equal (fn2-layout-max-size *fn2-format-raw-source-context*) 72))

(defconst *fn2-format-frame-header*
  `((magic :u32) (frame-kind (:enum frame-kind (:records :seal :continuation))) (history (:id history)) (incarnation (:id incarnation)) (writer-epoch (:id writer-epoch)) (commit (:id commit)) (extent (:id extent)) (extent-writer-epoch (:id writer-epoch)) (extent-allocation (:id allocation)) (ordinal :varint) (fragment-offset :varint) (payload-length :varint)))
(assert-event (fn2-layoutp *fn2-format-frame-header*))
(assert-event (equal (fn2-layout-max-size *fn2-format-frame-header*) 95))

(defconst *fn2-format-frame-trailer*
  `((frame-hash :digest)))
(assert-event (fn2-layoutp *fn2-format-frame-trailer*))
(assert-event (equal (fn2-layout-max-size *fn2-format-frame-trailer*) 33))

; Maintenance has a kind/version but no semantic event number.
(defconst *fn2-format-maintenance-header*
  `((record-kind ,*fn2-format-record-kind*) (schema-version :u8)))
(assert-event (fn2-layoutp *fn2-format-maintenance-header*))
(assert-event (equal (fn2-layout-max-size *fn2-format-maintenance-header*) 2))

(defconst *fn2-format-record-header*
  (append *fn2-format-maintenance-header* '((event (:id event)))))
(assert-event (fn2-layoutp *fn2-format-record-header*))
(assert-event (equal (fn2-layout-max-size *fn2-format-record-header*) 11))

(defconst *fn2-format-operation-header*
  `((principal (:id principal)) (operation (:id operation))))
(assert-event (fn2-layoutp *fn2-format-operation-header*))
(assert-event (equal (fn2-layout-max-size *fn2-format-operation-header*) 18))

(defconst *fn2-format-article-acceptance*
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

(defconst *fn2-format-cursor-advance*
  (append
    `((registration (:id registration)) (previous-event (:id event)) (next-event (:id event)))
    (fn2-format-prefix "SELECTION-" *fn2-format-ref*)
    '((outcome :varint))))
(assert-event (fn2-layoutp *fn2-format-cursor-advance*))
(assert-event (equal (fn2-layout-max-size *fn2-format-cursor-advance*) 115))

(defconst *fn2-format-registration-change*
  (append
    `((registration (:id registration)) (previous-version (:id event)))
    (fn2-format-prefix "CONTRACT-" *fn2-format-ref*)
    '((outcome :varint))))
(assert-event (fn2-layoutp *fn2-format-registration-change*))
(assert-event (equal (fn2-layout-max-size *fn2-format-registration-change*) 106))

(defconst *fn2-format-configuration-change*
  (append
    `((configuration (:id configuration)) (previous-generation (:id configuration)))
    (fn2-format-prefix "VALUE-" *fn2-format-ref*)
    '((outcome :varint))))
(assert-event (fn2-layoutp *fn2-format-configuration-change*))
(assert-event (equal (fn2-layout-max-size *fn2-format-configuration-change*) 106))

(defconst *fn2-format-withdrawal*
  (append
    `((article (:id article)))
    (fn2-format-prefix "AUTHORIZATION-" *fn2-format-ref*)
    '((outcome :varint))))
(assert-event (fn2-layoutp *fn2-format-withdrawal*))
(assert-event (equal (fn2-layout-max-size *fn2-format-withdrawal*) 97))

(defconst *fn2-format-obligation-create*
  (append
    `((obligation (:id obligation)) (owner (:id principal)) (article (:id article)))
    (fn2-format-prefix "TERMS-" *fn2-format-ref*)
    (fn2-format-prefix "CHARGES-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-obligation-create*))
(assert-event (equal (fn2-layout-max-size *fn2-format-obligation-create*) 185))

(defconst *fn2-format-obligation-release*
  (append
    `((obligation (:id obligation)))
    (fn2-format-prefix "RELEASE-EVIDENCE-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-obligation-release*))
(assert-event (equal (fn2-layout-max-size *fn2-format-obligation-release*) 88))

(defconst *fn2-format-keyed-mutation*
  (append
    `((table (:id table)) (object (:id object)) (principal (:id principal)) (operation (:id operation)) (binding :digest) (expected-prior-version (:id event)))
    (fn2-format-prefix "NEW-VALUE-" *fn2-format-ref*)
    '((outcome :varint))))
(assert-event (fn2-layoutp *fn2-format-keyed-mutation*))
(assert-event (equal (fn2-layout-max-size *fn2-format-keyed-mutation*) 166))

(defconst *fn2-format-allocation*
  `((extent (:id extent)) (owner-kind :u8) (owner (:id owner)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation))))
(assert-event (fn2-layoutp *fn2-format-allocation*))
(assert-event (equal (fn2-layout-max-size *fn2-format-allocation*) 37))

(defconst *fn2-format-relocation*
  (append
    `((object (:id object)))
    (fn2-format-prefix "OLD-" *fn2-format-ref*)
    (fn2-format-prefix "NEW-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-relocation*))
(assert-event (equal (fn2-layout-max-size *fn2-format-relocation*) 167))

(defconst *fn2-format-run-replacement*
  (append
    `((schema (:id schema)))
    (fn2-format-prefix "OLD-RUNS-" *fn2-format-ref*)
    (fn2-format-prefix "NEW-RUNS-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-run-replacement*))
(assert-event (equal (fn2-layout-max-size *fn2-format-run-replacement*) 167))

(defconst *fn2-format-retirement*
  `((extent (:id extent)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation)) (retirement-commit (:id commit))))
(assert-event (fn2-layoutp *fn2-format-retirement*))
(assert-event (equal (fn2-layout-max-size *fn2-format-retirement*) 36))

(defconst *fn2-format-release-allocation*
  (append
    `((extent (:id extent)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation)) (retirement-commit (:id commit)) (promoted-checkpoint (:id checkpoint)))
    (fn2-format-prefix "RELEASE-EVIDENCE-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-release-allocation*))
(assert-event (equal (fn2-layout-max-size *fn2-format-release-allocation*) 124))

(defconst *fn2-format-checkpoint-installation*
  (append
    `((checkpoint (:id checkpoint)))
    (fn2-format-prefix "DESCRIPTOR-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-checkpoint-installation*))
(assert-event (equal (fn2-layout-max-size *fn2-format-checkpoint-installation*) 88))

(defconst *fn2-format-begin-writer-epoch*
  `((history (:id history)) (incarnation (:id incarnation)) (previous-writer-epoch (:id writer-epoch)) (writer-epoch (:id writer-epoch))))
(assert-event (fn2-layoutp *fn2-format-begin-writer-epoch*))
(assert-event (equal (fn2-layout-max-size *fn2-format-begin-writer-epoch*) 36))

(defconst *fn2-format-checkpoint-statement*
  (append
    `((history (:id history)) (incarnation (:id incarnation)) (event-cut (:id event)) (event-root :digest) (fold-schema (:id schema)) (summary-commitment :digest) (exact-identity-commitment :digest))
    (fn2-format-prefix "DESCRIPTOR-" *fn2-format-ref*)
    (fn2-format-prefix "AUTHORIZED-KEYS-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-checkpoint-statement*))
(assert-event (equal (fn2-layout-max-size *fn2-format-checkpoint-statement*) 293))

(defconst *fn2-format-root-recipe*
  (append
    (fn2-format-prefix "CHECKPOINT-BASE-" *fn2-format-ref*)
    `((suffix-first (:id commit)) (suffix-last (:id commit)))
    (fn2-format-prefix "PHYSICAL-MANIFEST-" *fn2-format-ref*)
    (fn2-format-prefix "ALLOCATION-CHANGES-" *fn2-format-ref*)
    (fn2-format-prefix "EVENT-FRONTIER-" *fn2-format-ref*)
    (fn2-format-prefix "CONFIGURATION-GENERATIONS-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-root-recipe*))
(assert-event (equal (fn2-layout-max-size *fn2-format-root-recipe*) 413))

(defconst *fn2-format-sealed-batch*
  (append
    `((commit (:id commit)) (previous-commit (:id commit)) (previous-seal :digest) (input-root :digest) (event-first (:id event)) (event-last (:id event)) (record-stream :digest))
    (fn2-format-prefix "DEPENDENCIES-" *fn2-format-ref*)
    (fn2-format-prefix "ALLOCATION-RETIREMENT-" *fn2-format-ref*)
    (fn2-format-prefix "METADATA-EDITS-" *fn2-format-ref*)
    (fn2-format-prefix "OUTPUT-" *fn2-format-root-recipe*)
    (fn2-format-prefix "EVENT-FRONTIER-" *fn2-format-ref*)
    `((final-seal :digest))))
(assert-event (fn2-layoutp *fn2-format-sealed-batch*))
(assert-event (equal (fn2-layout-max-size *fn2-format-sealed-batch*) 897))

(defconst *fn2-format-dependency-entry*
  (append
    (fn2-format-prefix "TARGET-" *fn2-format-ref*)
    `((length :varint) (digest :digest))))
(assert-event (fn2-layoutp *fn2-format-dependency-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-dependency-entry*) 121))

(defconst *fn2-format-source-manifest-header*
  `((source-length :varint) (block-size :varint) (source-identity :digest)))
(assert-event (fn2-layoutp *fn2-format-source-manifest-header*))
(assert-event (equal (fn2-layout-max-size *fn2-format-source-manifest-header*) 51))

(defconst *fn2-format-source-manifest-entry*
  (append
    `((logical-offset :varint) (length :varint))
    (fn2-format-prefix "BLOCK-" *fn2-format-ref*)
    `((subtree-cv :digest))))
(assert-event (fn2-layoutp *fn2-format-source-manifest-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-source-manifest-entry*) 130))

(defconst *fn2-format-allocation-map-entry*
  `((extent (:id extent)) (state (:enum allocation-state (:free :reserved :allocated :retire-pending))) (owner-kind :u8) (owner (:id owner)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation)) (retirement-commit (:id commit))))
(assert-event (fn2-layoutp *fn2-format-allocation-map-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-allocation-map-entry*) 47))

(defconst *fn2-format-checkpoint-descriptor*
  (append
    `((checkpoint (:id checkpoint)) (cut-commit (:id commit)) (cut-event (:id event)))
    (fn2-format-prefix "METADATA-MANIFEST-" *fn2-format-ref*)
    (fn2-format-prefix "ALLOCATION-STATE-" *fn2-format-ref*)
    (fn2-format-prefix "EVENT-PROOF-DIRECTORY-" *fn2-format-ref*)
    (fn2-format-prefix "EVENT-FRONTIER-" *fn2-format-ref*)
    (fn2-format-prefix "RECOVERY-ARENA-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-checkpoint-descriptor*))
(assert-event (equal (fn2-layout-max-size *fn2-format-checkpoint-descriptor*) 422))

(defconst *fn2-format-recovery-arena-entry*
  `((extent-physical-unit (:id physical-unit)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation))))
(assert-event (fn2-layoutp *fn2-format-recovery-arena-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-recovery-arena-entry*) 27))

(defconst *fn2-format-membership-entry*
  `((group (:id group)) (group-number (:id group-number)) (article (:id article))))
(assert-event (fn2-layoutp *fn2-format-membership-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-membership-entry*) 27))

(defconst *fn2-format-key-entry*
  `((key (:id key))))
(assert-event (fn2-layoutp *fn2-format-key-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-key-entry*) 9))

(defconst *fn2-format-configuration-generation-entry*
  `((configuration (:id configuration))))
(assert-event (fn2-layoutp *fn2-format-configuration-generation-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-configuration-generation-entry*) 9))

(defconst *fn2-format-layouts*
  (list
    (list 'ref *fn2-format-ref*)
    (list 'bootstrap *fn2-format-bootstrap*)
    (list 'anchor *fn2-format-anchor*)
    (list 'page-header *fn2-format-page-header*)
    (list 'raw-source-context *fn2-format-raw-source-context*)
    (list 'frame-header *fn2-format-frame-header*)
    (list 'frame-trailer *fn2-format-frame-trailer*)
    (list 'maintenance-header *fn2-format-maintenance-header*)
    (list 'record-header *fn2-format-record-header*)
    (list 'operation-header *fn2-format-operation-header*)
    (list 'article-acceptance *fn2-format-article-acceptance*)
    (list 'cursor-advance *fn2-format-cursor-advance*)
    (list 'registration-change *fn2-format-registration-change*)
    (list 'configuration-change *fn2-format-configuration-change*)
    (list 'withdrawal *fn2-format-withdrawal*)
    (list 'obligation-create *fn2-format-obligation-create*)
    (list 'obligation-release *fn2-format-obligation-release*)
    (list 'keyed-mutation *fn2-format-keyed-mutation*)
    (list 'allocation *fn2-format-allocation*)
    (list 'relocation *fn2-format-relocation*)
    (list 'run-replacement *fn2-format-run-replacement*)
    (list 'retirement *fn2-format-retirement*)
    (list 'release-allocation *fn2-format-release-allocation*)
    (list 'checkpoint-installation *fn2-format-checkpoint-installation*)
    (list 'begin-writer-epoch *fn2-format-begin-writer-epoch*)
    (list 'checkpoint-statement *fn2-format-checkpoint-statement*)
    (list 'root-recipe *fn2-format-root-recipe*)
    (list 'sealed-batch *fn2-format-sealed-batch*)
    (list 'dependency-entry *fn2-format-dependency-entry*)
    (list 'source-manifest-header *fn2-format-source-manifest-header*)
    (list 'source-manifest-entry *fn2-format-source-manifest-entry*)
    (list 'allocation-map-entry *fn2-format-allocation-map-entry*)
    (list 'checkpoint-descriptor *fn2-format-checkpoint-descriptor*)
    (list 'recovery-arena-entry *fn2-format-recovery-arena-entry*)
    (list 'membership-entry *fn2-format-membership-entry*)
    (list 'key-entry *fn2-format-key-entry*)
    (list 'configuration-generation-entry *fn2-format-configuration-generation-entry*)))
