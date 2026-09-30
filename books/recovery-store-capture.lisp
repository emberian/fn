; Literal Store-backed descriptor constructor used by the actual startup
; getter. Maintained invariants are proof premises, never served validators.
(in-package "ACL2")
(include-book "store-node")

(defun fn-rsc-descriptor (token epoch generation store)
 (declare (xargs :guard t :verify-guards nil))
 (let ((files (fn-sn-files store)))
  (list :recovery-census token epoch generation store
        (fn-sf-records-field files) (fn-sf-records-count files)
        (fn-sf-frontier files) (fn-sn-consumer store))))

; Proposed source theorems: admission and guards remain open at this packet.
(defthm fn-rsc-record-list-member-is-an-actual-store-event
 (implies (and (fn-sf-record-listp records sequence lower frontier)
               (member-equal row records))
          (fn-store-event-p row))
 :hints (("Goal" :induct (fn-sf-record-listp records sequence lower frontier)
          :in-theory (enable fn-sf-record-listp member-equal))))

(defthm fn-rsc-captured-store-field-is-canonical
 (implies (fn-sn-statep store)
          (fn-sfr-canonp (fn-sf-records-field (fn-sn-files store))))
 :hints (("Goal" :in-theory (enable fn-sn-statep fn-sf-statep fn-sf-shapep
                                   fn-sf-records-field))))

(defthm fn-rsc-captured-store-row-is-an-actual-store-event
 (implies (and (fn-sn-statep store)
               (member-equal row (fn-sfr-list
                                  (fn-sf-records-field (fn-sn-files store)))))
          (fn-store-event-p row))
 :hints (("Goal" :use ((:instance fn-rsc-record-list-member-is-an-actual-store-event
                        (records (fn-sf-records (fn-sn-files store)))
                        (sequence 0) (lower 0)
                        (frontier (fn-sf-frontier (fn-sn-files store)))))
          :in-theory (enable fn-sn-statep fn-sf-statep fn-sf-records))))

; Full literal constructor equality is a helper, not a completion keystone.
(defthm fn-rsc-descriptor-is-the-original-getter-result-by-definition
 (equal (fn-rsc-descriptor token epoch generation store)
        (list :recovery-census token epoch generation store
              (fn-sf-records-field (fn-sn-files store))
              (fn-sf-records-count (fn-sn-files store))
              (fn-sf-frontier (fn-sn-files store)) (fn-sn-consumer store)))
 :hints (("Goal" :in-theory (enable fn-rsc-descriptor))))
