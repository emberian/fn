; Recovery-only namespace. Actual source and INITIAL custody are checked by
; the production host boundary before this token or arena holder escapes.
(in-package "ACL2")
(include-book "snapshot-source-token")
(defun fn-rpv-seed () (declare (xargs :guard t))
  (list :recovery-payload-view-ledger 0 nil nil))
(defun fn-rpv-tokenp (x) (declare (xargs :guard t))
  (and (fn-omk-widthp x 4) (eq (fn-omk-at 0 x) :recovery-payload-view)
       (natp (fn-omk-at 1 x)) (natp (fn-omk-at 2 x)) (natp (fn-omk-at 3 x))))
(defun fn-rpv-token-matchp (a b) (declare (xargs :guard t))
  (and (fn-rpv-tokenp a) (fn-rpv-tokenp b)
       (equal (fn-omk-at 1 a) (fn-omk-at 1 b))
       (equal (fn-omk-at 2 a) (fn-omk-at 2 b))
       (equal (fn-omk-at 3 a) (fn-omk-at 3 b))))
(defun fn-rpv-ledgerp (s) (declare (xargs :guard t))
  (let ((a (fn-omk-at 3 s)))
    (and (fn-omk-widthp s 4)
         (eq (fn-omk-at 0 s) :recovery-payload-view-ledger)
         (natp (fn-omk-at 1 s))
         (or (null (fn-omk-at 2 s)) (natp (fn-omk-at 2 s)))
         (or (null a)
             (and (fn-omk-widthp a 3) (fn-rpv-tokenp (fn-omk-at 0 a))
                  (equal (fn-omk-at 1 (fn-omk-at 0 a)) (fn-omk-at 1 s))
                  (equal (fn-omk-at 3 (fn-omk-at 0 a)) (fn-omk-at 2 s)))))))
(defun fn-rpv-ownedp (s) (declare (xargs :guard t))
  (if (fn-omk-at 3 s) t nil))
(defun fn-rpv-livep (s token) (declare (xargs :guard t))
  (and (fn-rpv-ledgerp s) (fn-rpv-token-matchp token (fn-omk-at 0 (fn-omk-at 3 s)))))
(defun fn-rpv-acquire (s prefix source maintenance) (declare (xargs :guard t))
  ; RSA token is (:recovery-source ticket process-epoch ack-serial).
  (let ((ticket (fn-omk-at 1 source)))
    (cond ((not (and (fn-rpv-ledgerp s) (natp prefix)
                     (fn-omk-widthp source 4)
                     (eq (fn-omk-at 0 source) :recovery-source)
                     (natp ticket) maintenance)) (list :refused :recovery-view-domain s))
          ((fn-rpv-ownedp s) (list :refused :recovery-view-busy s))
          ((and (natp (fn-omk-at 2 s)) (<= ticket (fn-omk-at 2 s)))
           (list :refused :recovery-view-spent s))
          (t (let ((token (list :recovery-payload-view (fn-omk-at 1 s) prefix ticket)))
               (list :acquired token
                     (list :recovery-payload-view-ledger (fn-omk-at 1 s) ticket
                           (list token source maintenance))))))))
; Only the host's atomic same-row RoleReleasableP/RoleReturn composition
; invokes this transition. There is no supplied joined argument.
(defun fn-rpv-release (s token) (declare (xargs :guard t))
  (if (not (fn-rpv-livep s token)) (list :retained :recovery-view-stale s)
    (list :released token
          (list :recovery-payload-view-ledger (fn-omk-at 1 s) (fn-omk-at 2 s) nil))))
(defun fn-rpv-reset (s) (declare (xargs :guard t))
  (cond ((not (fn-rpv-ledgerp s)) (list :refused :recovery-view-domain s))
        ((fn-rpv-ownedp s) (list :retained :recovery-view-owned s))
        (t (list :reset nil
                 (list :recovery-payload-view-ledger (+ 1 (fn-omk-at 1 s))
                       (fn-omk-at 2 s) nil)))))
(in-theory (disable fn-rpv-seed fn-rpv-tokenp fn-rpv-token-matchp
                    fn-rpv-ledgerp fn-rpv-ownedp fn-rpv-livep
                    fn-rpv-acquire fn-rpv-release fn-rpv-reset))
