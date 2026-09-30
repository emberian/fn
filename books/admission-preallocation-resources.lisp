; Internal canonical admission charge transition over the ONE shared PRL.
; The public producer derives identity and demand from actual owner/census.
; Supplied demand or a returned old ROW is not an allocation capability.
(in-package "ACL2")
(include-book "page-read-ledger")

(local (defthm fn-apr-natural-vector-true-listp
 (implies (fn-prs-nats-p x) (true-listp x))
 :hints (("Goal" :induct (fn-prs-nats-p x)
          :in-theory (enable fn-prs-nats-p)))))
(local (defthm fn-apr-resource-vector-true-listp
 (implies (fn-prs-vectorp x) (true-listp x))
 :hints (("Goal" :in-theory (enable fn-prs-vectorp)))))

(defun fn-apr-naturals (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (null x)
  (and (consp x) (natp (car x)) (fn-apr-naturals (1- n) (cdr x)))))
; (process epoch, actual SF predecessor count, prepared sequence, txid, operation)
(defun fn-apr-identityp (x)
 (declare (xargs :guard t))
 (and (fn-apr-naturals 4 (list (fn-prl-nth 0 x) (fn-prl-nth 1 x)
                            (fn-prl-nth 2 x) (fn-prl-nth 3 x)))
      (member-eq (fn-prl-nth 4 x) '(:article :identity :retention :consumer :topic :config))
      (consp x) (consp (cdr x)) (consp (cddr x))
      (consp (cdddr x)) (consp (cddddr x)) (null (cdr (cddddr x)))))
(defun fn-apr-token (nonce identity)
 (declare (xargs :guard t))
 (list :admission-grant nonce (fn-prl-nth 0 identity) (fn-prl-nth 1 identity)
       (fn-prl-nth 2 identity) (fn-prl-nth 3 identity) (fn-prl-nth 4 identity)))
(defun fn-apr-widthp (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (null x)
  (and (consp x) (fn-apr-widthp (1- n) (cdr x)))))
(defun fn-apr-tokenp (token)
 (declare (xargs :guard t))
 (and (fn-apr-widthp 7 token) (eq (fn-prl-nth 0 token) :admission-grant)
      (natp (fn-prl-nth 1 token)) (natp (fn-prl-nth 2 token))
      (natp (fn-prl-nth 3 token)) (natp (fn-prl-nth 4 token))
      (natp (fn-prl-nth 5 token))
      (member-eq (fn-prl-nth 6 token) '(:article :identity :retention :consumer :topic :config))))
(defun fn-apr-livep (token row)
 (declare (xargs :guard t))
 (and (fn-apr-widthp 5 row) (fn-apr-tokenp token)
      (fn-apr-tokenp (fn-prl-nth 0 row))
      (equal token (fn-prl-nth 0 row))
      (member-eq (fn-prl-nth 2 row) '(:reserved :produced :uncertain))))

; Internal algebra only: CURRENT is fetched from the actual exclusive owner
; pending slot in the atomic STATE+pool wrapper, never accepted from its caller.
; Current row stores (token charged phase borrowed-base next-ready10). C includes this row
; under the joint pool+owner-slot relation; PRL bindings remain untouched.
(defun fn-apr-issue (identity demand rescue base current ledger)
 (declare (xargs :guard t))
 (if current (mv :admission-busy current ledger)
  (if (not (and (fn-apr-identityp identity) (fn-prs-vectorp demand)
                (equal (fn-prl-nth 4 demand) 1)))
   (mv :invalid-admission-census current ledger)
   (mv-let (word next charged)
    (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) rescue
                 (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
                 (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
    (if (not (eq word :admitted)) (mv word current ledger)
     (mv :reserved
         (list (fn-apr-token (fn-prl-nth 2 ledger) identity) demand :reserved base nil)
         (fn-prl-build (fn-prl-nth 0 ledger) charged next
                       (fn-prl-nth 3 ledger) (fn-prl-baseline ledger))))))))

(defun fn-apr-produced (token next-ready current)
 (declare (xargs :guard t))
 (if (not (and (fn-apr-livep token current)
                (eq (fn-prl-nth 2 current) :reserved)))
  (mv :stale current)
  (mv :produced (list token (fn-prl-nth 1 current) :produced (fn-prl-nth 3 current) next-ready))))
(defun fn-apr-uncertain (token current)
 (declare (xargs :guard t))
 (if (not (fn-apr-livep token current)) (mv :stale current)
  (if (eq (fn-prl-nth 2 current) :uncertain) (mv :uncertain current)
  (mv :uncertain (list token (fn-prl-nth 1 current) :uncertain
                      (fn-prl-nth 3 current) (fn-prl-nth 4 current))))))

; Neither cancellation nor ambiguous completion relinquishes old/new graphs.
; Settlement is permitted only after the actual owner has joined publication
; and relinquished private references. Spent nonce coordinate is never refunded.
(defun fn-apr-release (token joined current ledger)
 (declare (xargs :guard t))
 (cond ((not (fn-apr-livep token current)) (mv :stale current ledger))
       ((not (eq joined :joined)) (mv :not-joined current ledger))
       ((not (and (fn-prs-vectorp (fn-prl-nth 1 ledger))
                   (fn-prs-vectorp (fn-prl-nth 1 current))
                   (fn-prs-below (list (fn-prl-nth 0 (fn-prl-nth 1 current))
                                        (fn-prl-nth 1 (fn-prl-nth 1 current))
                                        (fn-prl-nth 2 (fn-prl-nth 1 current))
                                        (fn-prl-nth 3 (fn-prl-nth 1 current)) 0)
                                 (fn-prl-nth 1 ledger))))
        (mv :invalid-resource-state current ledger))
       (t (mv :released nil
           (fn-prl-build (fn-prl-nth 0 ledger)
              (fn-prs-release-reusable (fn-prl-nth 1 ledger) (fn-prl-nth 1 current))
              (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger) (fn-prl-baseline ledger))))))

(defthm fn-apr-busy-preserves-shared-authority
 (implies current
  (and (equal (mv-nth 1 (fn-apr-issue identity demand rescue base current ledger)) current)
       (equal (mv-nth 2 (fn-apr-issue identity demand rescue base current ledger)) ledger))))
(defthm fn-apr-stale-callback-cannot-refund
 (implies (not (fn-apr-livep token current))
  (and (equal (mv-nth 1 (fn-apr-release token joined current ledger)) current)
       (equal (mv-nth 2 (fn-apr-release token joined current ledger)) ledger))))
(defthm fn-apr-unjoined-keeps-charge
 (implies (not (eq joined :joined))
  (equal (mv-nth 2 (fn-apr-release token joined current ledger)) ledger)))
(in-theory (disable fn-apr-identityp fn-apr-token fn-apr-livep fn-apr-issue
                    fn-apr-produced fn-apr-uncertain fn-apr-release))
