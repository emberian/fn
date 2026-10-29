; Independent declaration family; format.lisp exports the complete catalog.
; Storage declarations compile their codecs through DEFLAYOUT. Integrity lives in format-check.
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

(deflayout fn2-format-ref
  `((storage-domain (:id storage-domain)) (physical-unit (:id physical-unit)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation)) (page-kind ,*fn2-format-page-kind*) (encoded-length :varint) (expected-hash :digest)))
(assert-event (fn2-layoutp *fn2-format-ref*))
(assert-event (equal (fn2-layout-max-size *fn2-format-ref*) 79))

