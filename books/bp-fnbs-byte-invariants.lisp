; A-2 physical FNBS publication: a file-fenced inode cannot turn into a
; different received bundle in any admissible crash image.  The directory
; choice is deliberately separate: before its barrier a final name can be
; absent or point to this inode.
(in-package "ACL2")
(include-book "bp-fnbs-byte-publisher")
(include-book "bp-fnbs-codec-invariants")

(defthm fn-bpnf-byte-crash-keeps-fenced-record
  (implies (and (fn-bs-crash-imagep state image)
                (fn-bs-fencedp state ino)
                (equal (fn-bs-durable-content state ino) frame)
                (fn-bpnf-stored-recordp record)
                (equal (fn-bpnf-stored-record-unframe frame) record)
                (equal (nth 1 record) epoch)
                (equal (nth 2 record) operation-id)
                (equal (fn-bs-durable-entry
                        image :fnbs
                        (fn-bpnf-stored-record-name epoch operation-id))
                       ino)
                (natp ino))
           (equal (fn-bpnf-byte-slot image epoch operation-id)
                  (list :record record)))
  :hints (("Goal"
           :use ((:instance fn-bs-crash-keeps-fenced-content
                            (s state) (image image) (ino ino)))
           :in-theory (e/d (fn-bpnf-byte-slot)
                           (fn-bpnf-stored-record-unframe
                            fn-bpnf-stored-record-name
                            fn-bpnf-stored-record-name-chars)))))

(defthm fn-bpnf-byte-crash-keeps-canonical-kind-five
  (implies
   (and (fn-bs-crash-imagep state image)
        (fn-bs-fencedp state ino)
        (natp ino)
        (fn-bpnf-stored-recordp record)
        (equal (nth 1 record) epoch)
        (equal (nth 2 record) operation-id)
        (fn-frame-values-okp *fn-bpnf-stored-fields*
                             (fn-bpnf-stored-record-values record))
        (fn-frame-inputp
         *fn-frame-magic-bundle-store* *fn-frame-version*
         *fn-bpnf-stored-code*
         (fn-frame-fields-octets *fn-bpnf-stored-fields*
                                 (fn-bpnf-stored-record-values record))
         *fn-bpn-lifecycle-max-payload*)
        (equal (fn-bpnf-stored-from-values
                (fn-bpnf-stored-record-values record)) record)
        (equal (fn-bpnf-stored-record-frame record)
               (fn-frame-seal
                *fn-frame-magic-bundle-store* *fn-frame-version*
                *fn-bpnf-stored-code*
                (fn-frame-fields-octets *fn-bpnf-stored-fields*
                                        (fn-bpnf-stored-record-values record))))
        (equal (fn-bs-durable-content state ino)
               (fn-bpnf-stored-record-frame record))
        (equal (fn-bs-durable-entry
                image :fnbs
                (fn-bpnf-stored-record-name epoch operation-id)) ino))
   (equal (fn-bpnf-byte-slot image epoch operation-id)
          (list :record record)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-stored-unframe-of-canonical-frame)
                 (:instance fn-bpnf-byte-crash-keeps-fenced-record
                            (frame (fn-bpnf-stored-record-frame record))))
           :in-theory (disable fn-bpnf-stored-record-frame
                               fn-bpnf-stored-record-unframe
                               fn-bpnf-stored-recordp
                               fn-bs-crash-imagep fn-bs-fencedp
                               fn-bpnf-byte-slot))))
