; fn: durable keyring-snapshot event and ordered identity evidence replay.
;
; Keyring snapshots are fn-e version 0 kind 3.  They occupy the same ordered
; Store history as kind-2 statement verdicts.  The snapshot payload and its
; profile tag are retained byte-exact.  D09 has not selected a production
; keyring/signature profile, so this book deliberately provides no conversion
; from those bytes to fn-prin-keyringp and no authorization predicate.

(in-package "ACL2")
(include-book "stx-evidence-records")

(defconst *fn-stxk-magic* '(102 110 45 101)) ; "fn-e"
(defconst *fn-stxk-version* 0)
(defconst *fn-stxk-kind* 3)
(defconst *fn-stxk-max-octets* 131072)
(defconst *fn-stxk-max-profile* 64)
(defconst *fn-stxk-max-snapshot* 65536)

(fn-defrecord fn-stxk
  :constructor (fn-stxk-make sequence txid generation keyring-generation
                             profile snapshot)
  :fields ((fn-stxk-sequence fn-record-uint32p)
           (fn-stxk-txid fn-record-uint32p)
           (fn-stxk-generation fn-record-uint32p)
           (fn-stxk-keyring-generation fn-record-uint32p)
           (fn-stxk-profile
            (fn-stxe-bounded-octetsp (fn-stxk-profile x)
                                     *fn-stxk-max-profile*))
           (fn-stxk-snapshot
            (fn-stxe-bounded-octetsp (fn-stxk-snapshot x)
                                     *fn-stxk-max-snapshot*)))
  :recognizer fn-stxk-p)

(defun fn-stxk-items (e)
  (declare (xargs :guard (fn-stxk-p e)))
  (list (cons :bytes *fn-stxk-magic*)
        (cons :uint *fn-stxk-version*)
        (cons :uint *fn-stxk-kind*)
        (cons :uint (fn-stxk-sequence e))
        (cons :uint (fn-stxk-txid e))
        (cons :uint (fn-stxk-generation e))
        (cons :uint (fn-stxk-keyring-generation e))
        (cons :bytes (fn-stxk-profile e))
        (cons :bytes (fn-stxk-snapshot e))))

(defun fn-stxk-encode (e)
  (declare (xargs :guard t))
  (if (fn-stxk-p e)
      (fn-stxe-encode-items-bounded (fn-stxk-items e)
                                    *fn-stxk-max-snapshot*)
    nil))

(defun fn-stxk-items-p (items)
  (declare (xargs :guard t))
  (and (true-listp items) (equal (len items) 9)
       (fn-stmt-bytes-item-p (nth 0 items))
       (equal (fn-cbor-ag-cdr (nth 0 items)) *fn-stxk-magic*)
       (fn-stmt-uint-item-p (nth 1 items))
       (equal (fn-cbor-ag-cdr (nth 1 items)) *fn-stxk-version*)
       (fn-stmt-uint-item-p (nth 2 items))
       (equal (fn-cbor-ag-cdr (nth 2 items)) *fn-stxk-kind*)
       (fn-stmt-uint-item-p (nth 3 items))
       (fn-stmt-uint-item-p (nth 4 items))
       (fn-stmt-uint-item-p (nth 5 items))
       (fn-stmt-uint-item-p (nth 6 items))
       (fn-stmt-bytes-item-p (nth 7 items))
       (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 7 items))
                                *fn-stxk-max-profile*)
       (fn-stmt-bytes-item-p (nth 8 items))
       (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 8 items))
                                *fn-stxk-max-snapshot*)))

(defun fn-stxk-of-items (items)
  (declare (xargs :guard t))
  (if (not (fn-stxk-items-p items))
      (fn-stmt-error :keyring-snapshot)
    (fn-stmt-ok
     (fn-stxk-make (fn-cbor-ag-cdr (nth 3 items))
                   (fn-cbor-ag-cdr (nth 4 items))
                   (fn-cbor-ag-cdr (nth 5 items))
                   (fn-cbor-ag-cdr (nth 6 items))
                   (fn-cbor-ag-cdr (nth 7 items))
                   (fn-cbor-ag-cdr (nth 8 items))))))

(defun fn-stxk-decode-exact (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stxk-max-octets*))
      (fn-stmt-error :limit)
    (let ((decoded (fn-stmt-decode-items-bounded
                    9 octets *fn-stxk-max-octets* *fn-stxk-max-snapshot*)))
      (if (not (fn-stmt-okp decoded))
          decoded
        (fn-stxk-of-items (fn-stmt-value decoded))))))

; Snapshot identity excludes Store ordering coordinates.  Repeating a
; generation with the same profile and payload is idempotent; changing either
; is conflicting evidence and faults replay.
(defun fn-stxk-same-snapshotp (a b)
  (declare (xargs :guard t))
  (and (fn-stxk-p a) (fn-stxk-p b)
       (equal (fn-stxk-keyring-generation a)
              (fn-stxk-keyring-generation b))
       (equal (fn-stxk-profile a) (fn-stxk-profile b))
       (equal (fn-stxk-snapshot a) (fn-stxk-snapshot b))))

(defun fn-stxk-find (generation snapshots)
  (declare (xargs :guard t))
  (if (consp snapshots)
      (if (and (fn-stxk-p (car snapshots))
               (equal generation
                      (fn-stxk-keyring-generation (car snapshots))))
          (car snapshots)
        (fn-stxk-find generation (cdr snapshots)))
    nil))

; Ordered identity replay context:
;   (:ok next-sequence snapshots verdicts current-generation current-trust)
;   (:fault expected-sequence snapshots verdicts current-generation reason)
; `current-trust' remains NIL until a supported D09 profile owns decoding.
(defun fn-stxk-context (kind next snapshots verdicts current-generation tail)
  (declare (xargs :guard t))
  (list kind next snapshots verdicts current-generation tail))

(defun fn-stxk-context-kind (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(verify-guards fn-stxk-context-kind)
(defun fn-stxk-context-next (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadr x) :exec (fn-ag-car (fn-ag-cdr x))))
(verify-guards fn-stxk-context-next)
(defun fn-stxk-context-snapshots (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (caddr x)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(verify-guards fn-stxk-context-snapshots)
(defun fn-stxk-context-verdicts (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadddr x)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(verify-guards fn-stxk-context-verdicts)
(defun fn-stxk-context-current-generation (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cddddr x))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(verify-guards fn-stxk-context-current-generation)
(defun fn-stxk-context-tail (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadr (cddddr x))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
              (fn-ag-cdr x))))))))
(verify-guards fn-stxk-context-tail)

(defun fn-stxk-initial-context (next)
  (declare (xargs :guard t))
  (fn-stxk-context :ok next nil nil nil nil))

(defun fn-stxk-fault (ctx reason)
  (declare (xargs :guard t))
  (fn-stxk-context :fault (fn-stxk-context-next ctx)
                   (fn-stxk-context-snapshots ctx)
                   (fn-stxk-context-verdicts ctx)
                   (fn-stxk-context-current-generation ctx) reason))

(defun fn-stxk-apply-snapshot (ctx e)
  (declare (xargs :guard t))
  (cond
   ((not (equal (fn-stxk-context-kind ctx) :ok)) ctx)
   ((not (fn-stxk-p e)) (fn-stxk-fault ctx :malformed-snapshot))
   ((not (equal (fn-stxk-sequence e) (fn-stxk-context-next ctx)))
    (fn-stxk-fault ctx :sequence))
   (t
    (let ((old (fn-stxk-find (fn-stxk-keyring-generation e)
                             (fn-stxk-context-snapshots ctx))))
      (cond
       ((and old (not (fn-stxk-same-snapshotp old e)))
        (fn-stxk-fault ctx :conflicting-keyring-generation))
       (old
        (fn-stxk-context :ok (1+ (fn-stxk-context-next ctx))
                         (fn-stxk-context-snapshots ctx)
                         (fn-stxk-context-verdicts ctx)
                         (fn-stxk-context-current-generation ctx) nil))
       ((and (natp (fn-stxk-context-current-generation ctx))
             (not (equal (fn-stxk-keyring-generation e)
                         (1+ (fn-stxk-context-current-generation ctx)))))
        (fn-stxk-fault ctx :keyring-generation-order))
       (t
        (fn-stxk-context :ok (1+ (fn-stxk-context-next ctx))
                         (cons e (fn-stxk-context-snapshots ctx))
                         (fn-stxk-context-verdicts ctx)
                         (fn-stxk-keyring-generation e) nil)))))))

(defun fn-stxk-apply-verdict (ctx e)
  (declare (xargs :guard t))
  (cond
   ((not (equal (fn-stxk-context-kind ctx) :ok)) ctx)
   ((not (fn-stxe-p e)) (fn-stxk-fault ctx :malformed-verdict))
   ((not (equal (fn-stxe-sequence e) (fn-stxk-context-next ctx)))
    (fn-stxk-fault ctx :sequence))
   (t
    (let ((snapshot
           (fn-stxk-find (fn-stxe-keyring-generation e)
                         (fn-stxk-context-snapshots ctx))))
      (cond
       ((not snapshot)
        (fn-stxk-fault ctx :missing-keyring-generation))
       ((not (equal (fn-stxe-profile e) (fn-stxk-profile snapshot)))
        (fn-stxk-fault ctx :keyring-profile-mismatch))
       (t
        (fn-stxk-context :ok (1+ (fn-stxk-context-next ctx))
                         (fn-stxk-context-snapshots ctx)
                         (cons e (fn-stxk-context-verdicts ctx))
                         (fn-stxk-context-current-generation ctx) nil)))))))

; Keystone for rotation order.  A successful snapshot step either repeats
; exact bytes and preserves the current generation, or installs its immediate
; successor.  The theorem's hypotheses are the carried replay context shape;
; tests remove each material condition with reachable counterexamples.
(defthm fn-stxk-apply-snapshot-does-not-regress-current-generation
  (implies (natp (fn-stxk-context-current-generation ctx))
           (<= (fn-stxk-context-current-generation ctx)
               (fn-stxk-context-current-generation
                (fn-stxk-apply-snapshot ctx e))))
  :hints (("Goal" :in-theory (enable fn-stxk-apply-snapshot
                                      fn-stxk-fault
                                      fn-stxk-context
                                      fn-stxk-same-snapshotp))))

(defun fn-stxk-current-trust (ctx)
  (declare (xargs :guard t) (ignore ctx))
  nil)

(in-theory (disable (:d fn-stxk-items) (:d fn-stxk-encode)
                    (:d fn-stxk-items-p) (:d fn-stxk-of-items)
                    (:d fn-stxk-decode-exact) (:d fn-stxk-same-snapshotp)
                    (:d fn-stxk-find) (:d fn-stxk-context)
                    (:d fn-stxk-initial-context) (:d fn-stxk-fault)
                    (:d fn-stxk-apply-snapshot) (:d fn-stxk-apply-verdict)
                    (:d fn-stxk-current-trust)))
