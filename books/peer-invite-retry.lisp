; PKT497: crash retry of the SAME authenticated current-inviter adoption.
; Receipt identity is the authored-source ID; equality of arbitrary source
; bytes from equal IDs requires the named A-CRYPTO collision premise.
; This book does not claim collision resistance or native durability.
(in-package "ACL2")
(include-book "peer-invite")
(include-book "peer-adoption-receipt-rows")

(defun fn-par-local-contextp (ident generation)
  (declare (xargs :guard t))
  (and (true-listp ident) (equal (len ident) 2)
       (fn-hsig-exact-octets-p (fn-pinv-at 0 ident) 32)
       (fn-record-uint32p (fn-pinv-at 1 ident))
       (fn-record-uint32p generation)))

(defun fn-par-receipt-rows (received ident adoption snapshots)
  (declare (xargs :guard t))
  (let* ((source (fn-pinv-received-source received))
         (principal (fn-pinv-received-principal received))
         (peer (fn-pinv-inviter-peer source principal))
         (name (fn-cfg-peer-name peer)))
    (list (fn-cfg-row-make name "internal-invite-source"
                           (fn-pinv-hex-string (fn-pinv-source-id source)) adoption)
          (fn-cfg-row-make name "internal-invite-store"
                           (fn-pinv-hex-string (fn-pinv-at 0 ident))
                           (fn-pinv-at 1 ident))
          (fn-cfg-row-make name "internal-invite-key-generation" ""
                           (fn-stxk-keyring-generation
                            (fn-hl-current-for-principal principal snapshots))))))

(defun fn-par-adoption-generation (rows)
  (declare (xargs :guard t))
  (fn-cfg-row-n (fn-cfg-peer-slot rows "internal-invite-source")))

(defun fn-par-retry-authorizedp (received observed-ml ed ml snapshots peers ident generation)
  (declare (xargs :guard t))
  (let* ((source (fn-pinv-received-source received))
         (principal (fn-pinv-received-principal received))
         (peer (fn-pinv-inviter-peer source principal))
         (rows (fn-cfg-rows-with-key peers (fn-cfg-peer-name peer)))
         (adoption (fn-par-adoption-generation rows)))
    (and (fn-par-local-contextp ident generation)
         (equal (car (fn-pinv-accept-plan received observed-ml ed ml snapshots)) :enrol)
         (fn-pinv-enrolled-withp principal (fn-pinv-received-keys received) snapshots)
         (fn-pinv-inviter-addressedp source)
         (fn-cfg-peerp peer)
         (fn-record-uint32p adoption) (< 0 adoption) (<= adoption generation)
         (equal rows (append (fn-cfg-peer-rows peer)
                             (fn-par-receipt-rows received ident adoption snapshots))))))

; The actual owner entry: :resume is already-committed adoption, not a new
; configure or enrollment.  Generic peer mutations must invalidate receipt
; rows in config's fold before this entry is activated.
(defun fn-par-accept-record-plan (received observed-ml ed ml snapshots peers ident generation)
  (declare (xargs :guard t))
  (let* ((source (fn-pinv-received-source received))
         (principal (fn-pinv-received-principal received))
         (peer (fn-pinv-inviter-peer source principal))
         (rows (fn-cfg-rows-with-key peers (fn-cfg-peer-name peer)))
         (plan (fn-pinv-accept-record-plan received observed-ml ed ml snapshots peers)))
    (cond ((fn-par-retry-authorizedp received observed-ml ed ml snapshots peers ident generation)
           (list :resume))
          ((not (fn-par-receipt-freep rows)) (list :refused :stale-invitation-receipt))
          ((and (equal (car plan) :configure)
                (fn-pinv-enrolled-withp principal (fn-pinv-received-keys received) snapshots))
           (if (and (fn-par-local-contextp ident generation)
                    (fn-record-uint32p (1+ generation)))
               (list :configure
                     (list (fn-cfg-delta-make
                            :accept-peer (fn-cfg-peer-name peer) "" (1+ generation)
                            (append (fn-cfg-peer-rows peer)
                                    (fn-par-receipt-rows received ident (1+ generation) snapshots)))))
             (list :refused :adoption-context)))
          (t (if (member-equal (car plan) '(:configure :enrol :refused)) plan
               (list :refused :invitation-plan))))))

(defthm fn-par-resume-requires-current-verified-adoption
  (implies (equal (car (fn-par-accept-record-plan received observed-ml ed ml snapshots
                                                peers ident generation)) :resume)
           (and (fn-par-retry-authorizedp received observed-ml ed ml snapshots
                                          peers ident generation)
                (fn-pinv-bound-document-p received observed-ml ed ml
                                          *fn-pinv-invitation-kind* snapshots)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-par-accept-record-plan fn-par-retry-authorizedp)
                (fn-pinv-accept-record-plan fn-pinv-accept-plan
                 fn-par-local-contextp fn-par-adoption-generation
                 fn-pinv-inviter-peer fn-pinv-inviter-addressedp
                 fn-par-receipt-rows fn-cfg-peerp fn-pinv-enrolled-withp))
           :use ((:instance fn-pinv-accept-plan-enrols-only-a-bound-invitation)))))

; The internal producer never elevates an unverified or stale inviter.
(defthm fn-par-internal-adoption-requires-current-bound-inviter
  (let* ((plan (fn-par-accept-record-plan received observed-ml ed ml snapshots
                                          peers ident generation))
         (delta (fn-cfg-ag-car (fn-pinv-at 1 plan))))
    (implies (equal (list (car plan) (fn-cfg-delta-kind delta))
                    '(:configure :accept-peer))
             (and (fn-pinv-bound-document-p received observed-ml ed ml
                                            *fn-pinv-invitation-kind* snapshots)
                  (fn-pinv-enrolled-withp (fn-pinv-received-principal received)
                                           (fn-pinv-received-keys received) snapshots)
                  (fn-par-local-contextp ident generation)
                  (equal (fn-cfg-delta-n delta) (1+ generation)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-par-accept-record-plan fn-cfg-set-peer-delta fn-cfg-set-peer fn-cfg-ag-car)
                (fn-pinv-accept-record-plan fn-pinv-inviter-addressedp fn-par-local-contextp
                 fn-par-retry-authorizedp fn-par-receipt-freep
                 fn-par-receipt-rows fn-pinv-inviter-peer
                 fn-pinv-enrolled-withp))
           :use ((:instance fn-pinv-accept-record-configures-the-verified-inviter)))))

(local
 (defthm fn-par-retry-with-key-of-append
   (equal (fn-cfg-rows-with-key (append a b) key)
          (append (fn-cfg-rows-with-key a key) (fn-cfg-rows-with-key b key)))
   :hints (("Goal" :induct (append a b)
            :in-theory (enable fn-cfg-rows-with-key)))))
(local
 (defthm fn-par-retry-with-key-of-without-key
   (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows key) key) nil)
   :hints (("Goal" :induct (fn-cfg-rows-without-key rows key)
            :in-theory (enable fn-cfg-rows-with-key fn-cfg-rows-without-key)))))
(local
 (defthm fn-par-receipt-rows-have-inviter-key
   (equal (fn-cfg-rows-with-key
           (fn-par-receipt-rows received ident adoption snapshots)
           (fn-cfg-peer-name (fn-pinv-inviter-peer
                             (fn-pinv-received-source received)
                             (fn-pinv-received-principal received))))
          (fn-par-receipt-rows received ident adoption snapshots))
   :hints (("Goal" :in-theory
            (e/d (fn-par-receipt-rows fn-cfg-rows-with-key fn-cfg-row-make
                  fn-cfg-row-a fn-cfg-ag-car)
                 (fn-pinv-inviter-peer fn-pinv-hex-string
                  fn-pinv-source-id fn-stxk-keyring-generation))))))
(local
 (defthm fn-par-retry-keyed-cons
   (equal (fn-cfg-rows-with-key (cons row rows) key)
          (if (equal (fn-cfg-row-a row) key)
              (cons row (fn-cfg-rows-with-key rows key))
            (fn-cfg-rows-with-key rows key)))
   :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key)))))
(local
 (defthm fn-par-retry-keyed-nil
   (equal (fn-cfg-rows-with-key nil key) nil)
   :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key)))))
(local
 (defthm fn-par-peer-rows-have-peer-key
   (equal (fn-cfg-rows-with-key (fn-cfg-peer-rows peer) (fn-cfg-peer-name peer))
          (fn-cfg-peer-rows peer))
   :hints (("Goal" :in-theory
            (union-theories
             '(fn-cfg-peer-rows fn-cfg-peer-trust-row
               fn-par-retry-keyed-cons fn-par-retry-keyed-nil
               fn-par-retry-with-key-of-append
               fn-cfg-row-a-of-row-make car-cons cdr-cons)
             (union-theories (theory 'minimal-theory)
                            (executable-counterpart-theory :here)))))))

(local
 (defthm fn-par-local-context-at-next-generation
   (implies (and (fn-par-local-contextp ident generation)
                 (fn-record-uint32p (1+ generation)))
            (fn-par-local-contextp ident (1+ generation)))
   :hints (("Goal" :in-theory (enable fn-par-local-contextp)))))

(local
 (defthm fn-par-source-slot-of-append
   (equal (fn-cfg-peer-slot (append a b) "internal-invite-source")
          (or (fn-cfg-peer-slot a "internal-invite-source")
              (fn-cfg-peer-slot b "internal-invite-source")))
   :hints (("Goal" :induct (append a b)
            :in-theory (enable fn-cfg-peer-slot)))))
(local
 (defthm fn-par-source-slot-cons
   (equal (fn-cfg-peer-slot (cons row rows) "internal-invite-source")
          (if (equal (fn-cfg-row-b row) "internal-invite-source") row
            (fn-cfg-peer-slot rows "internal-invite-source")))
   :hints (("Goal" :in-theory (enable fn-cfg-peer-slot)))))
(local
 (defthm fn-par-source-slot-nil
   (equal (fn-cfg-peer-slot nil "internal-invite-source") nil)
   :hints (("Goal" :in-theory (enable fn-cfg-peer-slot)))))
(local
 (defthm fn-par-peer-rows-have-no-source-slot
   (equal (fn-cfg-peer-slot (fn-cfg-peer-rows peer) "internal-invite-source") nil)
   :hints (("Goal" :in-theory
            (union-theories
             '(fn-cfg-peer-rows fn-cfg-peer-trust-row fn-par-source-slot-cons
               fn-par-source-slot-nil fn-par-source-slot-of-append
               fn-cfg-row-b-of-row-make car-cons cdr-cons)
             (union-theories (theory 'minimal-theory)
                            (executable-counterpart-theory :here)))))))
(local
 (defthm fn-par-receipt-adoption-generation
   (equal (fn-cfg-row-n (fn-cfg-peer-slot
                       (fn-par-receipt-rows received ident adoption snapshots)
                       "internal-invite-source")) adoption)
   :hints (("Goal" :in-theory
            (e/d (fn-par-receipt-rows fn-cfg-peer-slot fn-cfg-row-make
                  fn-cfg-row-b fn-cfg-row-n fn-cfg-ag-car fn-cfg-ag-cdr)
                 (fn-pinv-inviter-peer fn-pinv-hex-string fn-pinv-source-id
                  fn-stxk-keyring-generation))))))

(local
 (defthm fn-par-local-context-generation-nonnegative
   (implies (fn-par-local-contextp ident generation)
            (and (integerp generation) (<= 0 generation)))
   :hints (("Goal" :in-theory (enable fn-par-local-contextp fn-record-uint32p)))))

(local
 (defthm fn-par-local-context-next-positive
   (implies (fn-par-local-contextp ident generation)
            (< 0 (+ 1 generation)))
   :hints (("Goal" :in-theory (enable fn-par-local-contextp fn-record-uint32p)))))

; The actual durable fold produces the retryable state, for every admitted
; current-inviter adoption.  Restart supplies the same store/key context;
; unrelated later generations leave the peer-specific receipt intact.
(defthm fn-par-current-adoption-fold-resumes-without-another-record
  (let* ((plan (fn-par-accept-record-plan received observed-ml ed ml snapshots
                                          (fn-cfg-peers value) ident generation))
         (delta (fn-cfg-ag-car (fn-pinv-at 1 plan)))
         (next (fn-cfg-apply-delta value (1+ generation) stamp delta)))
    (implies (equal (list (car plan) (fn-cfg-delta-kind delta))
                    '(:configure :accept-peer))
             (equal (fn-par-accept-record-plan received observed-ml ed ml snapshots
                                               (fn-cfg-peers next) ident (1+ generation))
                    '(:resume))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-par-accept-record-plan fn-par-retry-authorizedp
                 fn-par-adoption-generation fn-cfg-apply-delta
                 fn-cfg-set-peer-delta fn-cfg-set-peer fn-cfg-ag-car)
                (fn-pinv-accept-record-plan fn-pinv-accept-plan
                 fn-par-local-contextp fn-par-receipt-freep
                 fn-par-without-receipts fn-par-receipt-rows
                 fn-pinv-inviter-peer fn-pinv-inviter-addressedp
                 fn-pinv-enrolled-withp fn-cfg-peerp fn-cfg-rows-with-key
                 fn-cfg-rows-without-key))
           :use ((:instance fn-par-local-context-generation-nonnegative) (:instance fn-pinv-accept-record-configures-the-verified-inviter (peers (fn-cfg-peers value)))))))
