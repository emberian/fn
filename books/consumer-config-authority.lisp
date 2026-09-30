; Saved ACL2 configuration authority preflight. The actual owner captures its
; staged record and consumes this proposal once after durable completion.
; Coordinates are a bounded binding under the exact staged-record invariant,
; never a substitute for payload correspondence or admission funding.
(in-package "ACL2")
(include-book "consumer-authority-revision")
(include-book "consumer-account-carried")
(include-book "config-record-order")

(defun fn-cca-preflight (cp metadata)
  (declare (xargs :guard t))
  (let ((one (fn-carv-semantic-step cp)))
    (if (eq (fn-cp-nth 0 one) :ok)
        (let ((next (fn-cp-nth 1 one)))
          (list :ok next
                (if (and next metadata)
                    (fn-caac-metadata next (fn-cp-nth 1 metadata)
                                       (fn-cp-nth 2 metadata) nil)
                  nil)))
      one)))

(defun fn-cca-coordinates (record)
  (declare (xargs :guard t))
  (list (fn-cfg-record-sequence record) (fn-cfg-record-txid record)
        (fn-cfg-record-generation record) (fn-cfg-record-stamp record)))

; Fixed11: tag epoch coordinates history incarnation frontier namespace
; old-revision approvedCP approvedMetadata exact-borrowed-staged-record.
; The last field is retained for the actual producer relation; matching does
; not execute equality or a recognizer over the record's arbitrary delta list.
(defun fn-cca-proposal (epoch cp record approved)
  (declare (xargs :guard t))
  (if (and (natp epoch) record (eq (fn-cp-nth 0 approved) :ok))
      (let ((a (fn-cp-nth 6 cp)))
        (list :config-authority epoch (fn-cca-coordinates record)
              (fn-cp-nth 1 cp) (fn-cp-nth 2 cp) (fn-cp-nth 3 cp)
              (fn-cp-nth 3 a) (fn-cp-nth 1 a)
              (fn-cp-nth 1 approved) (fn-cp-nth 2 approved) record))
    nil))

(defun fn-cca-matchesp (proposal epoch cp record)
  (declare (xargs :guard t))
  (let ((a (fn-cp-nth 6 cp)))
    (and (eq (fn-cp-nth 0 proposal) :config-authority)
         (natp epoch) (equal (fn-cp-nth 1 proposal) epoch) record
         (equal (fn-cp-nth 2 proposal) (fn-cca-coordinates record))
         (equal (fn-cp-nth 3 proposal) (fn-cp-nth 1 cp))
         (equal (fn-cp-nth 4 proposal) (fn-cp-nth 2 cp))
         (equal (fn-cp-nth 5 proposal) (fn-cp-nth 3 cp))
         (equal (fn-cp-nth 6 proposal) (fn-cp-nth 3 a))
         (equal (fn-cp-nth 7 proposal) (fn-cp-nth 1 a)))))

(defun fn-cca-consume (proposal epoch cp record)
  (declare (xargs :guard t))
  (if (fn-cca-matchesp proposal epoch cp record)
      (list :ok (fn-cp-nth 8 proposal) (fn-cp-nth 9 proposal))
    (list :recovery-required :authority-proposal)))

; This is the actual saved-result boundary. The proposal must be constructed
; by the same stage producer; no assertion about arbitrary forged descriptors.
(defthm fn-cca-consume-keeps-approved-result
  (implies (and (natp epoch) record (eq (fn-cp-nth 0 approved) :ok))
           (equal (fn-cca-consume (fn-cca-proposal epoch cp record approved)
                                  epoch cp record)
                  (list :ok (fn-cp-nth 1 approved) (fn-cp-nth 2 approved))))
  :hints (("Goal" :in-theory
           (e/d (fn-cca-consume fn-cca-proposal fn-cca-matchesp fn-cp-nth)
                (fn-cca-coordinates)))))

(defthm fn-cca-consume-epoch-mismatch-requires-recovery
  (implies (not (equal (fn-cp-nth 1 proposal) current-epoch))
           (equal (fn-cca-consume proposal current-epoch cp record)
                  '(:recovery-required :authority-proposal)))
  :hints (("Goal" :in-theory
           (e/d (fn-cca-consume fn-cca-matchesp)
                (fn-cca-coordinates fn-cp-nth)))))
