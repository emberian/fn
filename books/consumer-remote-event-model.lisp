; Proof-only residual observation for the bounded FNCE4 chunk producer.
(in-package "ACL2")
(include-book "consumer-remote-event-codec")

(defun fn-crevm-residual (s)
 (declare (xargs :guard t))
 (append (if (eq (fn-cp-nth 7 s) :header) (true-list-fix (fn-cp-nth 6 s)) nil)
         (fn-crev-groups-encode (fn-cp-nth 2 s))))

(defun fn-crevm-measurep (s)
 (declare (xargs :guard t))
 (and (natp (fn-cp-nth 3 s)) (natp (fn-cp-nth 4 s))
      (equal (fn-cp-nth 3 s) (len (fn-cp-nth 2 s)))
      (equal (fn-cp-nth 4 s) (fn-crw-groups-charge (fn-cp-nth 2 s)))))

(local
 (defthm fn-crevm-append-ignores-improper-prefix-tail
  (equal (append xs ys) (append (true-list-fix xs) ys))
  :rule-classes nil
  :hints (("Goal" :induct (true-list-fix xs)
                   :in-theory (enable true-list-fix binary-append)))))

(defthm fn-crev-chunk-is-exact-residual-encoding
 (implies (eq (fn-cp-nth 0 (fn-crev-tick s key)) :chunk)
  (equal (append (fn-cp-nth 1 (fn-crev-tick s key))
                 (fn-crevm-residual (fn-cp-nth 2 (fn-crev-tick s key))))
         (fn-crevm-residual s)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-crevm-append-ignores-improper-prefix-tail
                   (xs (fn-cp-nth 6 s)) (ys (fn-crev-groups-encode (fn-cp-nth 2 s)))))
          :in-theory (e/d (fn-crev-tick fn-crev-state fn-crevm-residual
                          fn-crev-groups-encode fn-crs-namep fn-cp-nth)
                         (fn-cbor-u16-bytes fn-record-group-name-octetsp lexorder len floor mod)))))

(defthm fn-crev-tick-preserves-exact-remaining-measures
 (implies (and (fn-crevm-measurep s)
                (eq (fn-cp-nth 0 (fn-crev-tick s key)) :chunk))
          (fn-crevm-measurep (fn-cp-nth 2 (fn-crev-tick s key))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-crev-tick fn-crev-state fn-crevm-measurep fn-crw-groups-charge fn-cp-nth len)
                         (fn-crs-namep fn-cbor-u16-bytes lexorder)))))

(defthm fn-crev-encoded-has-no-residual-octets
 (implies (eq (fn-cp-nth 0 (fn-crev-tick s key)) :encoded)
          (equal (fn-crevm-residual s) nil))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-crev-tick fn-crevm-residual fn-crev-groups-encode fn-cp-nth)
                         (fn-crev-state fn-cbor-u16-bytes fn-crs-namep lexorder len)))))

(in-theory (disable fn-crevm-residual fn-crevm-measurep))
