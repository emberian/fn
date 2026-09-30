(in-package "ACL2")
(include-book "cbor")
(defun fn-cbor-decode-bytes-sized-bounded (additional tail max-bytes)
  (declare (xargs :guard (and (natp additional)
                              (fn-cbor-octet-listp tail)
                              (natp max-bytes))
                  :guard-hints (("Goal" :in-theory (enable fn-cbor-codec-vocabulary)))))
  (let ((argument (fn-cbor-decode-argument additional tail)))
    (if (not (fn-cbor-result-okp argument))
        (mv argument nil)
      (let ((length (fn-cbor-result-value argument))
            (content (fn-cbor-result-rest argument)))
        (if (not (fn-cbor-canonical-argumentp additional length))
            (mv (fn-cbor-error :noncanonical) nil)
          ; This check precedes TAKE, so a declared length outside the caller's
          ; profile cannot drive allocation.  The legacy entry point below
          ; supplies *fn-cbor-max-bytes* and therefore keeps its exact domain.
          (if (< max-bytes length)
              (mv (fn-cbor-error :limit) nil)
            (if (fn-cbor-at-leastp content length)
                (mv (fn-cbor-ok (cons :bytes (take length content))
                                (nthcdr length content)) length)
              (mv (fn-cbor-error :truncated) nil))))))))

(verify-guards fn-cbor-decode-bytes-sized-bounded)

(local
 (defthm fn-cbor-sized-len-take
   (equal (len (take n xs)) (nfix n))
   :hints (("Goal" :induct (take n xs) :in-theory (enable take)))))

(local
 (defthm fn-cbor-sized-argument-natural
   (implies (and (natp additional) (fn-cbor-octet-listp tail)
                 (fn-cbor-result-okp (fn-cbor-decode-argument additional tail)))
            (natp (fn-cbor-result-value (fn-cbor-decode-argument additional tail))))
   :hints (("Goal" :in-theory (enable fn-cbor-decode-argument
                                     fn-cbor-u16-from fn-cbor-u32-from
                                     fn-cbor-octet-listp fn-cbor-octetp)))))

(defthm fn-cbor-byte-size-is-allocated-length
  (implies (and (natp additional) (fn-cbor-octet-listp tail)
                (fn-cbor-result-okp
                 (mv-nth 0 (fn-cbor-decode-bytes-sized-bounded
                            additional tail max-bytes))))
           (and (natp (mv-nth 1 (fn-cbor-decode-bytes-sized-bounded
                                additional tail max-bytes)))
                (equal (mv-nth 1 (fn-cbor-decode-bytes-sized-bounded
                                  additional tail max-bytes))
                       (len (cdr (fn-cbor-result-value
                                   (mv-nth 0 (fn-cbor-decode-bytes-sized-bounded
                                              additional tail max-bytes))))))))
  :hints (("Goal" :use fn-cbor-sized-argument-natural
           :in-theory (e/d (fn-cbor-decode-bytes-sized-bounded)
                           (fn-cbor-sized-argument-natural fn-cbor-decode-argument fn-cbor-at-leastp
                            fn-cbor-canonical-argumentp take nthcdr)))))

(defun fn-cbor-decode-sized-prechecked (octets item-budget)
  (declare (xargs :guard (and (fn-cbor-octet-listp octets)
                              (natp item-budget))
                  :guard-hints (("Goal" :in-theory (enable fn-cbor-codec-vocabulary)))))
  (if (not (consp octets))
      (mv (fn-cbor-error :truncated) nil)
    (let ((head (car octets)))
      (if (< head 32)
          (mv (fn-cbor-decode-unsigned head (cdr octets)) nil)
        (if (and (< 63 head) (< head 96))
            (fn-cbor-decode-bytes-sized-bounded (- head 64) (cdr octets)
                                          item-budget)
          (mv (fn-cbor-error :unsupported) nil))))))

(verify-guards fn-cbor-decode-sized-prechecked)

(local
 (defthm fn-cbor-sized-bytes-tag-by-definition
   (implies (fn-cbor-result-okp
             (mv-nth 0 (fn-cbor-decode-bytes-sized-bounded additional tail max-bytes)))
            (equal (car (fn-cbor-result-value
                         (mv-nth 0 (fn-cbor-decode-bytes-sized-bounded
                                    additional tail max-bytes)))) :bytes))
   :hints (("Goal" :in-theory
            (e/d (fn-cbor-decode-bytes-sized-bounded)
                 (fn-cbor-decode-argument fn-cbor-at-leastp
                  fn-cbor-canonical-argumentp take nthcdr))))))

(defthm fn-cbor-sized-item-length-corresponds
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp
                 (mv-nth 0 (fn-cbor-decode-sized-prechecked octets item-budget))))
           (if (equal (car (fn-cbor-result-value
                            (mv-nth 0 (fn-cbor-decode-sized-prechecked
                                       octets item-budget)))) :bytes)
               (and (natp (mv-nth 1 (fn-cbor-decode-sized-prechecked
                                     octets item-budget)))
                    (equal (mv-nth 1 (fn-cbor-decode-sized-prechecked
                                       octets item-budget))
                           (len (cdr (fn-cbor-result-value
                                      (mv-nth 0 (fn-cbor-decode-sized-prechecked
                                                 octets item-budget)))))))
             (equal (mv-nth 1 (fn-cbor-decode-sized-prechecked
                               octets item-budget)) nil)))
  :hints (("Goal"
           :use ((:instance fn-cbor-sized-bytes-tag-by-definition
                            (additional (- (car octets) 64))
                            (tail (cdr octets)) (max-bytes item-budget))
                 (:instance fn-cbor-byte-size-is-allocated-length
                            (additional (- (car octets) 64))
                            (tail (cdr octets)) (max-bytes item-budget)))
           :in-theory
           (e/d (fn-cbor-decode-sized-prechecked fn-cbor-decode-unsigned)
                (fn-cbor-sized-bytes-tag-by-definition
                 fn-cbor-byte-size-is-allocated-length
                 fn-cbor-decode-bytes-sized-bounded fn-cbor-decode-argument
                 fn-cbor-canonical-argumentp)))))

(defthm fn-cbor-sized-projection-by-definition
  (equal (mv-nth 0 (fn-cbor-decode-sized-prechecked octets item-budget))
         (fn-cbor-decode-prechecked octets item-budget))
  :hints (("Goal" :in-theory (e/d (fn-cbor-decode-prechecked fn-cbor-decode-sized-prechecked
                 fn-cbor-decode-bytes-bounded fn-cbor-decode-bytes-sized-bounded)
                (fn-cbor-decode-argument fn-cbor-decode-unsigned
                 fn-cbor-at-leastp fn-cbor-canonical-argumentp take nthcdr)))))
