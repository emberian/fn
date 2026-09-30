; Receiver-only descriptor matching and logical retirement.
; Frozen 6b42c2a93 section 5.1, RFC 9172/9173 security boundary.
; A shaped reference or test-supplied :verified completion proves no crypto,
; registry binding, current policy lease, physical return or application grant.
(in-package "ACL2")
(include-book "bpsec-model")

; Stop after N cells even on untrusted longer/malformed records. Never LEN
; or TRUE-LISTP the complete caller-supplied object on this boundary.
(defun fn-bps-fixed-recordp (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n) (null x)
    (and (consp x) (fn-bps-fixed-recordp (1- n) (cdr x)))))

(defun fn-bps-refp (x)
  (declare (xargs :guard t))
  (and (fn-bps-fixed-recordp 3 x) (eq (fn-bps-field 0 x) :bps-ref)
       (fn-bps-uintp (fn-bps-field 1 x))
       (fn-bps-uintp (fn-bps-field 2 x))))

(defun fn-bps-op-byte-spanp (x)
  (declare (xargs :guard t))
  (and (fn-bps-fixed-recordp 4 x) (eq (fn-bps-field 0 x) :bytes-span)
       (fn-bps-uintp (fn-bps-field 1 x))
       (fn-bps-uintp (fn-bps-field 2 x))
       (fn-bps-uintp (fn-bps-field 3 x))
       (<= (+ (fn-bps-field 2 x) (fn-bps-field 3 x)) *fn-bpc-max-uint*)))

(defun fn-bps-op-wrappedp (x)
  (declare (xargs :guard t))
  (or (null x) (fn-bps-op-byte-spanp x)))

(defun fn-bps-bib-paramsp (x)
  (declare (xargs :guard t))
  (and (fn-bps-fixed-recordp 4 x) (eq (fn-bps-field 0 x) :bps-bib-params)
       (or (equal (fn-bps-field 1 x) 5) (equal (fn-bps-field 1 x) 6)
           (equal (fn-bps-field 1 x) 7))
       (natp (fn-bps-field 2 x)) (<= (fn-bps-field 2 x) 7)
       (fn-bps-op-wrappedp (fn-bps-field 3 x))))

(defun fn-bps-bcb-paramsp (x)
  (declare (xargs :guard t))
  (and (fn-bps-fixed-recordp 6 x) (eq (fn-bps-field 0 x) :bps-bcb-params)
       (or (equal (fn-bps-field 1 x) 1) (equal (fn-bps-field 1 x) 3))
       (natp (fn-bps-field 2 x)) (<= (fn-bps-field 2 x) 7)
       (fn-bps-op-byte-spanp (fn-bps-field 3 x))
       (<= 8 (fn-bps-field 3 (fn-bps-field 3 x)))
       (<= (fn-bps-field 3 (fn-bps-field 3 x)) 16)
       (fn-bps-op-wrappedp (fn-bps-field 4 x))
       (or (eq (fn-bps-field 5 x) :separate-tag)
           (eq (fn-bps-field 5 x) :tag-in-ciphertext))))

(defun fn-bps-op-make (action token held policy key security target context params input expected)
  (declare (xargs :guard t))
  (list :bps-op action token held policy key security target context params input expected))

(defun fn-bps-opp (x)
  (declare (xargs :guard t))
  (and (fn-bps-fixed-recordp 12 x) (eq (fn-bps-field 0 x) :bps-op)
       (fn-bps-refp (fn-bps-field 2 x)) (fn-bps-refp (fn-bps-field 3 x))
       (fn-bps-refp (fn-bps-field 4 x)) (fn-bps-refp (fn-bps-field 5 x))
       (fn-bps-uintp (fn-bps-field 6 x)) (fn-bps-uintp (fn-bps-field 7 x))
       (fn-bps-refp (fn-bps-field 10 x))
       (if (eq (fn-bps-field 1 x) :verify-bib)
           (and (equal (fn-bps-field 8 x) 1)
                (fn-bps-bib-paramsp (fn-bps-field 9 x))
                (fn-bps-op-byte-spanp (fn-bps-field 11 x))
                (equal (fn-bps-field 3 (fn-bps-field 11 x))
                       (case (fn-bps-field 1 (fn-bps-field 9 x)) (5 32) (6 48) (otherwise 64))))
         (and (eq (fn-bps-field 1 x) :decrypt-bcb)
              (equal (fn-bps-field 8 x) 2)
              (fn-bps-bcb-paramsp (fn-bps-field 9 x))
              (if (eq (fn-bps-field 5 (fn-bps-field 9 x)) :separate-tag)
                  (and (fn-bps-op-byte-spanp (fn-bps-field 11 x))
                       (equal (fn-bps-field 3 (fn-bps-field 11 x)) 16))
                (null (fn-bps-field 11 x)))))))

(defun fn-bps-currentp (x)
  (declare (xargs :guard t))
  (and (fn-bps-fixed-recordp 5 x) (eq (fn-bps-field 0 x) :bps-current)
       (fn-bps-refp (fn-bps-field 1 x)) (fn-bps-refp (fn-bps-field 2 x))
       (fn-bps-refp (fn-bps-field 3 x)) (fn-bps-refp (fn-bps-field 4 x))))

(defun fn-bps-op-current (descriptor)
  (declare (xargs :guard t))
  (list :bps-current (fn-bps-field 3 descriptor) (fn-bps-field 4 descriptor)
        (fn-bps-field 5 descriptor) (fn-bps-field 10 descriptor)))

(defun fn-bps-operationp (x)
  (declare (xargs :guard t))
  (and (fn-bps-fixed-recordp 3 x) (eq (fn-bps-field 0 x) :bps-operation)
       (or (eq (fn-bps-field 1 x) :issued) (eq (fn-bps-field 1 x) :cancelled)
           (eq (fn-bps-field 1 x) :settled))
       (fn-bps-opp (fn-bps-field 2 x))))

(defun fn-bps-completionp (x)
  (declare (xargs :guard t))
  (and (fn-bps-fixed-recordp 5 x) (eq (fn-bps-field 0 x) :bps-completion)
       (fn-bps-opp (fn-bps-field 1 x))
       (case (fn-bps-field 2 x)
         (:verified (and (eq (fn-bps-field 4 x) :ok)
                         (if (eq (fn-bps-field 1 (fn-bps-field 1 x)) :verify-bib)
                             (null (fn-bps-field 3 x))
                           (fn-bps-refp (fn-bps-field 3 x)))))
         (:failed (and (eq (fn-bps-field 4 x) :authentication-failed) (null (fn-bps-field 3 x))))
         (:unsupported (and (eq (fn-bps-field 4 x) :unsupported-profile) (null (fn-bps-field 3 x))))
         (:uncertain (and (or (eq (fn-bps-field 4 x) :primitive-unavailable)
                              (eq (fn-bps-field 4 x) :primitive-fault))
                          (null (fn-bps-field 3 x))))
         (otherwise nil))))

(defun fn-bps-op-cancel (opstate)
  (declare (xargs :guard t))
  (if (and (fn-bps-operationp opstate) (eq (fn-bps-field 1 opstate) :issued))
      (list :bps-operation :cancelled (fn-bps-field 2 opstate)) opstate))

(defun fn-bps-op-complete (opstate current completion)
  (declare (xargs :guard t))
  (let ((descriptor (fn-bps-field 2 opstate)))
    (cond
     ((or (not (fn-bps-operationp opstate)) (not (fn-bps-completionp completion)))
      (list :bps-completed :ignored :malformed-completion opstate nil))
     ((not (equal (fn-bps-field 1 completion) descriptor))
      (list :bps-completed :ignored :foreign-completion opstate nil))
     ((eq (fn-bps-field 1 opstate) :settled)
      (list :bps-completed :ignored :duplicate opstate nil))
     ((eq (fn-bps-field 1 opstate) :cancelled)
      (list :bps-completed :ignored :cancelled (list :bps-operation :settled descriptor) nil))
     ((or (not (fn-bps-currentp current)) (not (equal current (fn-bps-op-current descriptor))))
      (list :bps-completed :ignored :stale-current (list :bps-operation :settled descriptor) nil))
     (t (list :bps-completed (fn-bps-field 2 completion) (fn-bps-field 4 completion)
              (list :bps-operation :settled descriptor)
              (if (eq (fn-bps-field 2 completion) :verified)
                  (list :bps-evidence descriptor (fn-bps-field 3 completion)) nil))))))

; The evidence is about exact fixed metadata and current snapshot only.
; It is not an authenticated primitive observation or application capability.
(defthm fn-bps-op-evidence-requires-issued-current-verified
  (implies (fn-bps-field 4 (fn-bps-op-complete opstate current completion))
           (and (fn-bps-operationp opstate)
                (eq (fn-bps-field 1 opstate) :issued)
                (fn-bps-currentp current)
                (equal current (fn-bps-op-current (fn-bps-field 2 opstate)))
                (fn-bps-completionp completion)
                (equal (fn-bps-field 1 completion) (fn-bps-field 2 opstate))
                (eq (fn-bps-field 2 completion) :verified)
                (equal (fn-bps-field 4 (fn-bps-op-complete opstate current completion))
                       (list :bps-evidence (fn-bps-field 2 opstate) (fn-bps-field 3 completion)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bps-opp fn-bps-fixed-recordp fn-bps-currentp fn-bps-completionp fn-bps-op-current))))

(defthm fn-bps-op-complete-preserves-operation
  (implies (fn-bps-operationp opstate)
           (fn-bps-operationp (fn-bps-field 3 (fn-bps-op-complete opstate current completion))))
  :hints (("Goal" :in-theory (disable fn-bps-opp fn-bps-completionp fn-bps-currentp fn-bps-op-current))))

(defthm fn-bps-op-cancel-preserves-operation
  (implies (fn-bps-operationp opstate) (fn-bps-operationp (fn-bps-op-cancel opstate)))
  :hints (("Goal" :in-theory (disable fn-bps-opp))))

(defthm fn-bps-op-foreign-completion-preserves-rightful-state-by-definition
  (implies (and (fn-bps-operationp opstate) (fn-bps-completionp completion)
                (not (equal (fn-bps-field 1 completion) (fn-bps-field 2 opstate))))
           (equal (fn-bps-op-complete opstate current completion)
                  (list :bps-completed :ignored :foreign-completion opstate nil)))
  :hints (("Goal" :in-theory (disable fn-bps-operationp fn-bps-completionp fn-bps-currentp fn-bps-op-current))))

(defthm fn-bps-op-completion-never-reopens-retired-operation
  (implies (not (eq (fn-bps-field 1 opstate) :issued))
           (and (not (eq (fn-bps-field 1 (fn-bps-op-cancel opstate)) :issued))
                (not (eq (fn-bps-field 1 (fn-bps-field 3 (fn-bps-op-complete opstate current completion))) :issued))
                (not (fn-bps-field 4 (fn-bps-op-complete opstate current completion)))))
  :hints (("Goal" :in-theory (disable fn-bps-opp fn-bps-fixed-recordp fn-bps-completionp fn-bps-currentp fn-bps-op-current))))
