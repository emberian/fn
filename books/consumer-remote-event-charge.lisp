; Exact scalar FNCE4 charge from the same-pass definition count/wire carry.
; This bounded decision never scans a served query to reconstruct its charge.
(in-package "ACL2")
(include-book "consumer-remote-event-codec")

(defun fn-crc-event-charge (event count wire)
 (declare (xargs :guard t))
 (if (and (fn-crev-headp event) (posp count) (fn-cp-uintp count) (natp wire))
     (+ (fn-crev-header-charge event count) wire) 0))

(local
 (defthm fn-crc-u16-length
  (equal (len (fn-cbor-u16-bytes n)) 2)
  :hints (("Goal" :in-theory (e/d (fn-cbor-u16-bytes) (floor mod))))))

(local
 (defthm fn-crc-name-is-proper
  (implies (fn-crs-namep name) (true-listp name))
  :hints (("Goal" :in-theory
           (e/d (fn-crs-namep fn-cbor-octet-listp)
                (fn-record-group-name-octetsp fn-cbor-at-mostp))))))

(defthm fn-crc-groups-charge-is-reference-encoded-length
 (implies (fn-crev-groupsp groups previous)
          (equal (fn-crw-groups-charge groups) (len (fn-crev-groups-encode groups))))
 :hints (("Goal" :induct (fn-crev-groupsp groups previous)
          :in-theory (e/d (fn-crev-groupsp fn-crev-groups-encode fn-crw-groups-charge)
                          (fn-cbor-u16-bytes fn-crs-namep lexorder)))))

(local
 (defthm fn-crc-nonempty-count-positive
  (implies (consp xs) (< 0 (len xs)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable len)))))

(defthm fn-crc-carried-charge-is-reference-encoded-length
 (implies (and (fn-crev-eventp event)
               (posp count) (fn-cp-uintp count)
               (equal wire (fn-crw-groups-charge (fn-cp-nth 7 (fn-cp-nth 4 event)))))
          (equal (fn-crc-event-charge event count wire)
                 (len (fn-crev-encode-reference event))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-crev-header-charge-is-encoded-length
                   (count (len (fn-cp-nth 7 (fn-cp-nth 4 event))))))
          :in-theory
           (e/d (fn-crc-event-charge fn-crev-eventp fn-crev-encode-reference fn-crev-header-charge)
                (fn-crev-header-charge-is-encoded-length fn-crev-headp fn-crev-header fn-crev-groups-encode
                 fn-crw-groups-charge fn-crev-groupsp fn-cp-nth fn-cp-uintp)))))

(in-theory (disable fn-crc-event-charge))
