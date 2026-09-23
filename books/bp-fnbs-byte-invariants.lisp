; A-2 physical FNBS publication: a file-fenced inode cannot turn into a
; different received bundle in any admissible crash image.  The directory
; choice is deliberately separate: before its barrier a final name can be
; absent or point to this inode.
(in-package "ACL2")
(include-book "bp-fnbs-byte-publisher")
(include-book "bp-fnbs-codec-invariants")

(defthm fn-bpnf-ops-for-name-of-append
  (equal (fn-bs-ops-for-name (append a b) dir name)
         (append (fn-bs-ops-for-name a dir name)
                 (fn-bs-ops-for-name b dir name)))
  :hints (("Goal" :induct (append a b)
           :in-theory (enable fn-bs-ops-for-name))))

(defthm fn-bpnf-ops-for-ino-of-append
  (equal (fn-bs-ops-for-ino (append a b) ino)
         (append (fn-bs-ops-for-ino a ino)
                 (fn-bs-ops-for-ino b ino)))
  :hints (("Goal" :induct (append a b)
           :in-theory (enable fn-bs-ops-for-ino))))

(defthm fn-bpnf-link-issues-one-final-entry
  (implies
   (and (fn-bs-inop ino)
        (equal (fn-bs-lookup state :fnbs stage) ino)
        (not (fn-bs-lookup state :fnbs final))
        (equal (fn-bs-ops-for-name (fn-bs-pending state) :fnbs final)
               nil))
   (equal
    (fn-bs-ops-for-name
     (fn-bs-pending (fn-bpnf-byte-after-link state stage final :ok))
     :fnbs final)
    (list (list :set-entry :fnbs final ino))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-bpnf-byte-after-link fn-bs-link
                              fn-bs-ops-for-name))))

(defthm fn-bpnf-link-keeps-fenced-inode-and-durable-bytes
  (implies (and (fn-bs-inop ino)
                (equal (fn-bs-lookup state :fnbs stage) ino)
                (not (fn-bs-lookup state :fnbs final)))
           (let ((linked (fn-bpnf-byte-after-link state stage final :ok)))
             (and (equal (fn-bs-durable-entry linked :fnbs final)
                         (fn-bs-durable-entry state :fnbs final))
                  (equal (fn-bs-durable-content linked ino)
                         (fn-bs-durable-content state ino))
                  (equal (fn-bs-fencedp linked ino)
                         (fn-bs-fencedp state ino)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-bpnf-byte-after-link fn-bs-link
                              fn-bs-fencedp fn-bs-ops-for-ino
                              fn-bs-durable-entry fn-bs-durable-content))))

(defthm fn-bpnf-byte-one-pending-link-has-two-crash-names
  (implies
   (and (fn-bs-crash-imagep state image)
        (equal (fn-bs-durable-entry state :fnbs name) nil)
        (equal (fn-bs-ops-for-name (fn-bs-pending state) :fnbs name)
               (list (list :set-entry :fnbs name ino)))
        (stringp name))
   (member-equal (fn-bs-durable-entry image :fnbs name)
                 (list nil ino)))
  :hints (("Goal"
           :use ((:instance fn-bs-crash-entry-is-old-or-a-pending-target
                            (s state) (image image) (dir :fnbs)))
           :in-theory (e/d (fn-bs-entry-outcomes fn-bs-dir-idp fn-bs-namep)
                           (fn-bs-crash-entry-is-old-or-a-pending-target)))))

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

(defthm fn-bpnf-byte-link-cut-is-absent-or-exact
  (implies
   (and (fn-bs-crash-imagep state image)
        (natp ino)
        (fn-bs-fencedp state ino)
        (fn-bpnf-stored-recordp record)
        (equal (nth 1 record) epoch)
        (equal (nth 2 record) operation-id)
        (equal (fn-bs-durable-content state ino) frame)
        (equal (fn-bpnf-stored-record-unframe frame) record)
        (equal (fn-bs-durable-entry
                state :fnbs (fn-bpnf-stored-record-name epoch operation-id))
               nil)
        (equal
         (fn-bs-ops-for-name
          (fn-bs-pending state) :fnbs
          (fn-bpnf-stored-record-name epoch operation-id))
         (list (list :set-entry :fnbs
                     (fn-bpnf-stored-record-name epoch operation-id) ino))))
   (member-equal (fn-bpnf-byte-slot image epoch operation-id)
                 (list :absent (list :record record))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-byte-one-pending-link-has-two-crash-names
                            (name (fn-bpnf-stored-record-name
                                   epoch operation-id)))
                 (:instance fn-bpnf-byte-crash-keeps-fenced-record))
           :in-theory (e/d (fn-bpnf-byte-slot)
                           (fn-bpnf-byte-one-pending-link-has-two-crash-names
                            fn-bpnf-byte-crash-keeps-fenced-record
                            fn-bpnf-stored-record-name
                            fn-bpnf-stored-record-unframe)))))

(defthm fn-bpnf-actual-link-crash-is-absent-or-exact
  (implies
   (and (fn-bs-inop ino)
        (equal (fn-bs-lookup state :fnbs stage) ino)
        (not (fn-bs-lookup state :fnbs
                           (fn-bpnf-stored-record-name epoch operation-id)))
        (equal (fn-bs-durable-entry
                state :fnbs (fn-bpnf-stored-record-name epoch operation-id))
               nil)
        (equal (fn-bs-ops-for-name
                (fn-bs-pending state) :fnbs
                (fn-bpnf-stored-record-name epoch operation-id)) nil)
        (fn-bs-fencedp state ino)
        (fn-bpnf-stored-recordp record)
        (equal (nth 1 record) epoch)
        (equal (nth 2 record) operation-id)
        (equal (fn-bs-durable-content state ino) frame)
        (equal (fn-bpnf-stored-record-unframe frame) record)
        (fn-bs-crash-imagep
         (fn-bpnf-byte-after-link
          state stage (fn-bpnf-stored-record-name epoch operation-id) :ok)
         image))
   (member-equal (fn-bpnf-byte-slot image epoch operation-id)
                 (list :absent (list :record record))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-link-issues-one-final-entry
                            (final (fn-bpnf-stored-record-name
                                    epoch operation-id)))
                 (:instance fn-bpnf-link-keeps-fenced-inode-and-durable-bytes
                            (final (fn-bpnf-stored-record-name
                                    epoch operation-id)))
                 (:instance fn-bpnf-byte-link-cut-is-absent-or-exact
                            (state (fn-bpnf-byte-after-link
                                    state stage
                                    (fn-bpnf-stored-record-name
                                     epoch operation-id) :ok))))
           :in-theory (disable fn-bpnf-link-issues-one-final-entry
                               fn-bpnf-link-keeps-fenced-inode-and-durable-bytes
                               fn-bpnf-byte-slot fn-bpnf-stored-recordp
                               fn-bpnf-stored-record-name
                               fn-bs-crash-imagep fn-bs-fencedp
                               fn-bs-ops-for-name fn-bs-lookup
                               fn-bpnf-stored-record-unframe
                               fn-bpnf-byte-after-link))))

(defthm fn-bpnf-directory-barrier-quiet
  (fn-bs-dir-quietp (fn-bpnf-byte-after-dir-barrier state) :fnbs)
  :hints (("Goal" :use ((:instance fn-bs-fence-dir-drains-exactly-its-directory
                                   (s state) (dir :fnbs)))
           :in-theory (enable fn-bpnf-byte-after-dir-barrier
                              fn-bs-fsync-dir fn-bs-dir-quietp))))

(defthm fn-bpnf-quiet-final-name-survives-crash
  (implies (and (fn-bs-crash-imagep state image)
                (fn-bs-dir-quietp state :fnbs))
           (equal (fn-bs-durable-entry image :fnbs name)
                  (fn-bs-durable-entry state :fnbs name)))
  :hints (("Goal" :use ((:instance fn-bs-crash-keeps-quiet-directory
                                   (s state) (dir :fnbs)))
           :in-theory (e/d (fn-bs-durable-entry)
                           (fn-bs-crash-keeps-quiet-directory)))))

(defthm fn-bpnf-durable-cut-recovers-exact-record
  (implies
   (and (fn-bs-crash-imagep state image)
        (fn-bs-dir-quietp state :fnbs)
        (natp ino)
        (fn-bs-fencedp state ino)
        (equal (fn-bs-durable-entry
                state :fnbs (fn-bpnf-stored-record-name epoch operation-id))
               ino)
        (equal (fn-bs-durable-content state ino) frame)
        (fn-bpnf-stored-recordp record)
        (equal (nth 1 record) epoch)
        (equal (nth 2 record) operation-id)
        (equal (fn-bpnf-stored-record-unframe frame) record))
   (equal (fn-bpnf-byte-slot image epoch operation-id)
          (list :record record)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-quiet-final-name-survives-crash
                            (name (fn-bpnf-stored-record-name
                                   epoch operation-id)))
                 (:instance fn-bpnf-byte-crash-keeps-fenced-record))
           :in-theory (disable fn-bpnf-quiet-final-name-survives-crash
                               fn-bpnf-byte-slot fn-bpnf-stored-recordp
                               fn-bpnf-stored-record-unframe
                               fn-bpnf-stored-record-name))))

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
