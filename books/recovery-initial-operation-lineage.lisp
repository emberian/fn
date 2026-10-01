; Custody lineage for an ALREADY issued INITIAL operation. This predicate
; cannot issue/refresh INITIAL or reopen the cold recovery source.
(in-package "ACL2")
(include-book "snapshot-source-token")
(include-book "recovery-source-authority")
(defun fn-rsa-installed-source-matchp (source ticket count frontier)
 (declare (xargs :guard t))
 (and (fn-omk-widthp source 4) (fn-omk-widthp (fn-omk-at 1 source) 2)
      (equal (fn-omk-at 0 source) frontier)
      (equal (fn-omk-at 0 (fn-omk-at 1 source)) ticket)
      (equal (fn-omk-at 1 (fn-omk-at 1 source)) count)
      (equal (fn-omk-at 2 source) 0) (equal (fn-omk-at 3 source) 0)))
(defun fn-rsa-initial-operation-lineagep
    (issuer token epoch generation actual-count actual-frontier canonical)
 (declare (xargs :guard t))
 (and (fn-omk-widthp issuer 9) (fn-omk-widthp token 4)
      (eq (fn-omk-at 0 token) :recovery-source)
      (natp (fn-omk-at 1 issuer)) (natp (fn-omk-at 2 issuer))
      (natp (fn-omk-at 4 issuer)) (natp (fn-omk-at 5 issuer))
      (natp (fn-omk-at 7 issuer)) (natp (fn-omk-at 8 issuer))
      (natp (fn-omk-at 3 token))
      (<= (fn-omk-at 3 token) (fn-omk-at 7 issuer))
      (equal (fn-omk-at 1 token) (fn-omk-at 1 issuer))
      (equal (fn-omk-at 2 token) epoch)
      (equal epoch (fn-omk-at 2 issuer))
      (equal generation (fn-omk-at 8 issuer))
      (natp actual-count) (natp actual-frontier)
      (equal actual-count (fn-omk-at 4 issuer))
      (cond
       ((eq (fn-omk-at 0 issuer) :recovering)
        (and (null canonical)
             (<= (fn-omk-at 5 issuer) actual-frontier)))
       ((eq (fn-omk-at 0 issuer) :sealed)
        (and (equal actual-frontier (fn-omk-at 5 issuer))
             (fn-omk-widthp canonical 10)
             (eq (fn-omk-at 0 canonical) :ready)
             (equal (fn-omk-at 1 canonical) epoch)
             (equal (fn-omk-at 2 canonical) actual-count)
             (fn-rsa-installed-source-matchp
              (fn-omk-at 9 canonical) (fn-omk-at 1 issuer)
              actual-count actual-frontier)))
       (t nil))))

(defthm fn-rsa-seal-preserves-initial-operation-lineage
 (implies
  (and (fn-rsa-initial-operation-lineagep
        issuer token epoch generation count frontier nil)
       (equal frontier (fn-omk-at 5 issuer)))
  (mv-let (word source sealed)
    (fn-rsa-seal issuer (fn-rsa-token issuer) epoch generation count frontier)
    (and (eq word :sealed)
         (fn-rsa-initial-operation-lineagep
          sealed token epoch generation count frontier
          (list :ready epoch count ctx fields cp cpfields pool rows source)))))
 :hints (("Goal" :in-theory
          (enable fn-rsa-seal fn-rsa-token fn-rsa-currentp
                  fn-rsa-initial-operation-lineagep
                  fn-rsa-installed-source-matchp fn-omk-widthp fn-omk-at))))
