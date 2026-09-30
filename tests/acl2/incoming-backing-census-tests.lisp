(in-package "ACL2")
(include-book "../../books/incoming-backing-census")
(defun ibct-step (requested old-capacity fn-octets$c)
  (declare (xargs :stobjs fn-octets$c :verify-guards nil))
  (let* ((fn-octets$c (resize-fn-octets$c-buf old-capacity fn-octets$c))
         (fn-octets$c (ec-call (fn-octets$c-reserve requested fn-octets$c))))
    (mv (fn-octets$c-buf-length fn-octets$c) fn-octets$c)))
(defun ibct (requested old-capacity)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets$c
    (mv-let (capacity fn-octets$c) (ibct-step requested old-capacity fn-octets$c)
      capacity)))
(assert-event (and (natp 8) (equal (ibct 8 4) (fn-ibc-next-capacity 8 4))))
(assert-event (and (natp 2) (equal (ibct 2 4) (fn-ibc-next-capacity 2 4))))
 ; Hypothesis removal is a malformed logical-state witness, not executable
; guarded native input. Prove the complete literal using actual reserve.
(defthm ibct-nonnatural-request-removal
  (and (not (natp 3/2))
       (not (equal (fn-octets$c-buf-length
                    (fn-octets$c-reserve 3/2 '((0) 0)))
                   (fn-ibc-next-capacity 3/2 1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-octets$c-reserve
                                    fn-octets$c-buf-length
                                    fn-ibc-next-capacity))))
(assert-event
 (and (equal (car (fn-ibc-backing-components 1 8192 1))
             (* 2 (fn-crl-array-octets 8192 1)))
      (< (* 2 (fn-crl-array-octets 1 1))
         (car (fn-ibc-backing-components 1 8192 1)))))
