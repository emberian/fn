; Durable FNBS records for the outbound BP lifecycle machine.
;
; Kind 1 belongs to books/bp-node-records.lisp's sequence frontier.  This
; append-only extension owns kinds 2 through 4.  The host never serializes a
; lifecycle decision: it asks this book for a complete frame and gives this
; book the complete frame during recovery.

(in-package "ACL2")
(include-book "bp-node-machine")
(include-book "frame-trailer")
(include-book "byte-store-txn-name")

(set-verify-guards-eagerness 0)

(defconst *fn-bpn-lifecycle-queued-code* 2)
(defconst *fn-bpn-lifecycle-attempting-code* 3)
(defconst *fn-bpn-lifecycle-result-code* 4)

; Eight-byte token, two bounded identifiers, generation, creation sequence,
; the durable Bundle Age/monotonic anchor, exact route, encoded peer EID and
; exact encoded bundle.  The maximum is below the generic frame layer's cap
; and is the only whole-payload bound the host uses.
(defconst *fn-bpn-lifecycle-max-payload* 134144)
(defconst *fn-bpn-lifecycle-max-hidden-stages* 16)
(defconst *fn-bpn-lifecycle-max-stage-name-chars* 128)
(defconst *fn-bpn-lifecycle-name-suffix* '(#\. #\f #\n #\b))

(defun fn-bpn-lifecycle-max-namespace-entries ()
  (declare (xargs :guard t))
  (+ *fn-bpn-machine-max-records* *fn-bpn-lifecycle-max-hidden-stages*))

; Reuse the Store transaction codec's proved decimal digit renderer.  Only the
; namespace suffix differs; there is no second natural-number printer here.
(defun fn-bpn-lifecycle-record-name-chars (token)
  (declare (xargs :guard t))
  (append (fn-bs-txn-digits token) *fn-bpn-lifecycle-name-suffix*))

(defun fn-bpn-lifecycle-record-name (token)
  (declare (xargs :guard t :verify-guards nil))
  (coerce (fn-bpn-lifecycle-record-name-chars token) 'string))

(defthm fn-bpn-lifecycle-record-name-chars-character-listp
  (character-listp (fn-bpn-lifecycle-record-name-chars token))
  :hints (("Goal"
           :use ((:instance fn-bs-txn-name-chars-characters (n token)))
           :in-theory (enable fn-bpn-lifecycle-record-name-chars
                              fn-bs-txn-name-chars))))

; This renderer is on every persist path.  Its executable guard is checked
; here rather than relying on the recovery-only functions' guard T contracts.
(verify-guards fn-bpn-lifecycle-record-name-chars)
(verify-guards fn-bpn-lifecycle-record-name
  :hints (("Goal"
           :use ((:instance
                  fn-bpn-lifecycle-record-name-chars-character-listp)))))

(defun fn-bpn-lifecycle-hidden-stage-namep (name)
  (declare (xargs :guard t))
  (and (stringp name)
       (let ((chars (coerce name 'list)))
         (and (consp chars)
              (equal (car chars) #\.)
              (<= (len chars) *fn-bpn-lifecycle-max-stage-name-chars*)))))

(defun fn-bpn-lifecycle-reverse-onto (xs acc)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (if (consp xs)
      (fn-bpn-lifecycle-reverse-onto (cdr xs) (cons (car xs) acc))
    acc))

(defun fn-bpn-lifecycle-reverse (xs)
  (declare (xargs :guard t))
  (fn-bpn-lifecycle-reverse-onto xs nil))

; This is a recovery plan, not an admission machine.  Raw Lisp supplies the
; sorted directory observations.  ACL2 classifies hidden stages, compares each
; final name with the exact name generated for the contiguous token, and
; returns both lists plus the observed next-token frontier.
(defun fn-bpn-lifecycle-namespace-plan-aux (names token records stages)
  (declare (xargs :guard t :measure (acl2-count names)))
  (if (atom names)
      (if (null names)
          (list :ready (fn-bpn-lifecycle-reverse records)
                (fn-bpn-lifecycle-reverse stages) token)
        (list :fault :improper-namespace))
    (let ((name (car names)))
      (cond
       ((fn-bpn-lifecycle-hidden-stage-namep name)
        (if (< (len stages) *fn-bpn-lifecycle-max-hidden-stages*)
            (fn-bpn-lifecycle-namespace-plan-aux
             (cdr names) token records (cons name stages))
          (list :fault :hidden-stage-bound)))
       ((and (< token *fn-bpn-machine-max-records*)
             (stringp name)
             (equal name (fn-bpn-lifecycle-record-name token)))
        (fn-bpn-lifecycle-namespace-plan-aux
         (cdr names) (+ 1 token) (cons name records) stages))
       (t (list :fault :lifecycle-namespace))))))

(defun fn-bpn-lifecycle-namespace-plan (names)
  (declare (xargs :guard t))
  (if (and (true-listp names)
           (<= (len names) (fn-bpn-lifecycle-max-namespace-entries)))
      (fn-bpn-lifecycle-namespace-plan-aux names 0 nil nil)
    (list :fault :namespace-entry-bound)))

(defun fn-bpn-lifecycle-namespace-planp (plan)
  (declare (xargs :guard t))
  (and (true-listp plan) (equal (len plan) 4)
       (equal (car plan) :ready)
       (fn-string-listp (nth 1 plan))
       (fn-string-listp (nth 2 plan))
       (natp (nth 3 plan))
       (<= (nth 3 plan) *fn-bpn-machine-max-records*)))

(defun fn-bpn-lifecycle-plan-record-names (plan)
  (declare (xargs :guard (fn-bpn-lifecycle-namespace-planp plan)))
  (nth 1 plan))

(defun fn-bpn-lifecycle-plan-hidden-stages (plan)
  (declare (xargs :guard (fn-bpn-lifecycle-namespace-planp plan)))
  (nth 2 plan))

(defun fn-bpn-lifecycle-plan-next-token (plan)
  (declare (xargs :guard (fn-bpn-lifecycle-namespace-planp plan)))
  (nth 3 plan))

(defun fn-bpn-lifecycle-record-bindingsp (names records token)
  (declare (xargs :guard t :measure (acl2-count names)))
  (if (atom names)
      (and (null names) (null records))
    (and (consp records)
         (stringp (car names))
         (fn-bpn-lifecycle-recordp (car records))
         (equal (fn-bpn-record-token (car records)) token)
         (equal (car names) (fn-bpn-lifecycle-record-name token))
         (fn-bpn-lifecycle-record-bindingsp
          (cdr names) (cdr records) (+ 1 token)))))

(defun fn-bpn-lifecycle-recovery (observed-names decoded-records)
  (declare (xargs :guard t))
  (let ((plan (fn-bpn-lifecycle-namespace-plan observed-names)))
    (if (and (fn-bpn-lifecycle-namespace-planp plan)
             (fn-bpn-lifecycle-record-bindingsp
              (fn-bpn-lifecycle-plan-record-names plan) decoded-records 0))
        (list :ready decoded-records
              (fn-bpn-lifecycle-plan-hidden-stages plan)
              (fn-bpn-lifecycle-plan-next-token plan))
      (list :fault :lifecycle-namespace-record-binding))))

; The native host needs only these flat projections.  RESTART itself remains
; fn-bpn-step; this predicate checks that its carried machine frontier is the
; frontier established by namespace recovery.
(defun fn-bpn-lifecycle-recovery-records (answer)
  (declare (xargs :guard t))
  (if (and (true-listp answer) (equal (car answer) :ready))
      (nth 1 answer) nil))

(defun fn-bpn-lifecycle-recovery-stages (answer)
  (declare (xargs :guard t))
  (if (and (true-listp answer) (equal (car answer) :ready))
      (nth 2 answer) nil))

(defun fn-bpn-lifecycle-recovery-next-token (answer)
  (declare (xargs :guard t))
  (if (and (true-listp answer) (equal (car answer) :ready))
      (nth 3 answer) 0))

(defun fn-bpn-lifecycle-recovery-agrees-with-statep (answer st)
  (declare (xargs :guard t))
  (and (equal (car answer) :ready)
       (fn-bpn-machine-statep st)
       (equal (fn-bpn-lifecycle-recovery-next-token answer)
              (fn-bpn-machine-state-next-token st))))

(defconst *fn-bpn-lifecycle-queued-spec*
  '(:nat :text :text :nat :nat :nat :nat
    :text :nat :text :nat :nat :nat :blob :blob))
(defconst *fn-bpn-lifecycle-attempting-spec*
  '(:nat :text :text :nat))
(defconst *fn-bpn-lifecycle-result-statuses*
  '(:requeued :finished :expired))
(defconst *fn-bpn-lifecycle-result-reasons*
  '(:none :refused :failed :uncertain))
(defconst *fn-bpn-lifecycle-result-spec*
  (list :nat :text :text :nat
        (cons :enum *fn-bpn-lifecycle-result-statuses*)
        (cons :enum *fn-bpn-lifecycle-result-reasons*)))

(defun fn-bpn-lifecycle-kind-code (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :queued) *fn-bpn-lifecycle-queued-code*)
        ((equal kind :attempting) *fn-bpn-lifecycle-attempting-code*)
        ((fn-bpn-member kind '(:requeued :finished :expired))
         *fn-bpn-lifecycle-result-code*)
        (t 0)))

(defun fn-bpn-lifecycle-code-kind (code)
  (declare (xargs :guard t))
  (cond ((equal code *fn-bpn-lifecycle-queued-code*) :queued)
        ((equal code *fn-bpn-lifecycle-attempting-code*) :attempting)
        ((equal code *fn-bpn-lifecycle-result-code*) :result)
        (t nil)))

(defun fn-bpn-lifecycle-spec (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :queued) *fn-bpn-lifecycle-queued-spec*)
        ((equal kind :attempting) *fn-bpn-lifecycle-attempting-spec*)
        ((equal kind :result) *fn-bpn-lifecycle-result-spec*)
        (t nil)))

(defun fn-bpn-peer-octets (peer)
  (declare (xargs :guard (fn-bpp-eidp peer)))
  (fn-bpc-enc :item (fn-bpp-eid-value peer)))

(defun fn-bpn-peer-from-octets (octets)
  (declare (xargs :guard t))
  (let ((decoded (fn-bpc-decode-exact octets)))
    (if (not (fn-cbor-result-okp decoded))
        nil
      (let ((peer (fn-bpp-value-eid (fn-cbor-result-value decoded))))
        (if (fn-bpp-eidp peer) peer nil)))))

(defun fn-bpn-lifecycle-record-values (record)
  (declare (xargs :guard (fn-bpn-lifecycle-recordp record)))
  (let ((kind (fn-cbor-ag-car record)))
    (if (equal kind :queued)
        (let ((job (fn-bpn-nth 2 record)))
          (let ((route (fn-bpn-job-route job)))
            (list (fn-bpn-record-token record)
                  (fn-bpn-job-work-id job)
                  (fn-bpn-job-attempt-id job)
                  (fn-bpn-job-generation job)
                  (fn-bpn-job-sequence job)
                  (car (fn-bpn-job-age-anchor job))
                  (cdr (fn-bpn-job-age-anchor job))
                  (fn-bpn-nth 1 route) (fn-bpn-nth 2 route)
                  (fn-bpn-nth 3 route) (fn-bpn-nth 4 route)
                  (fn-bpn-nth 5 route) (fn-bpn-nth 6 route)
                  (fn-bpn-peer-octets (fn-bpn-job-peer job))
                  (fn-bpn-job-wire job))))
      (if (equal kind :attempting)
          (list (fn-bpn-record-token record)
                (fn-bpn-nth 2 record) (fn-bpn-nth 3 record)
                (fn-bpn-nth 4 record))
        (list (fn-bpn-record-token record)
              (fn-bpn-nth 2 record) (fn-bpn-nth 3 record)
              (fn-bpn-nth 4 record) (fn-bpn-nth 6 record)
              (fn-bpn-nth 5 record))))))

(defun fn-bpn-lifecycle-record-protected (record)
  (declare (xargs :guard (fn-bpn-lifecycle-recordp record)))
  (let* ((kind (fn-cbor-ag-car record))
         (code (fn-bpn-lifecycle-kind-code kind))
         (spec (fn-bpn-lifecycle-spec
                (if (equal code *fn-bpn-lifecycle-result-code*) :result kind)))
         (values (fn-bpn-lifecycle-record-values record))
         (payload (fn-frame-fields-octets spec values)))
    (if (and (not (equal code 0))
             (fn-frame-values-okp spec values)
             (fn-cbor-at-mostp payload *fn-bpn-lifecycle-max-payload*))
        (fn-frame-protected *fn-frame-magic-bundle-store*
                            *fn-frame-version* code payload)
      :bad)))

(defun fn-bpn-lifecycle-record-frame (record)
  (declare (xargs :guard (fn-bpn-lifecycle-recordp record)))
  (let ((protected (fn-bpn-lifecycle-record-protected record)))
    (if (equal protected :bad)
        :bad
      (fn-bpn-append protected (fn-frame-trailer protected)))))

(defun fn-bpn-lifecycle-queued-from-values (values)
  (declare (xargs :guard t))
  (let* ((wire (fn-bpn-nth 14 values))
         (peer (fn-bpn-peer-from-octets (fn-bpn-nth 13 values)))
         (route (list :route (fn-bpn-nth 7 values) (fn-bpn-nth 8 values)
                      (fn-bpn-nth 9 values) (fn-bpn-nth 10 values)
                      (fn-bpn-nth 11 values) (fn-bpn-nth 12 values)))
         (age-anchor (cons (fn-bpn-nth 5 values) (fn-bpn-nth 6 values)))
         (decoded (if (fn-cbor-octet-listp wire)
                      (fn-bpb-decode wire *fn-bpn-machine-max-job-octets*)
                    (fn-cbor-error :malformed)))
         (bundle (if (fn-cbor-result-okp decoded)
                     (fn-cbor-result-value decoded) nil))
         (job (fn-bpn-make-job
               (fn-bpn-nth 1 values) (fn-bpn-nth 2 values)
               (fn-bpn-nth 3 values) (fn-bpn-nth 4 values)
               age-anchor peer route bundle wire :queued (fn-bpn-nth 0 values)))
         (record (list :queued (fn-bpn-nth 0 values) job)))
    (if (fn-bpn-lifecycle-recordp record) record nil)))

(defun fn-bpn-lifecycle-record-from-values (kind values)
  (declare (xargs :guard t))
  (let ((record
         (cond ((equal kind :queued)
                (fn-bpn-lifecycle-queued-from-values values))
               ((equal kind :attempting)
                (list :attempting (fn-bpn-nth 0 values)
                      (fn-bpn-nth 1 values) (fn-bpn-nth 2 values)
                      (fn-bpn-nth 3 values)))
               ((equal kind :result)
                (list (fn-bpn-nth 4 values) (fn-bpn-nth 0 values)
                      (fn-bpn-nth 1 values) (fn-bpn-nth 2 values)
                      (fn-bpn-nth 3 values) (fn-bpn-nth 5 values)
                      (fn-bpn-nth 4 values)))
               (t nil))))
    (if (fn-bpn-lifecycle-recordp record) record nil)))

(defun fn-bpn-lifecycle-record-unframe (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((answer (fn-frame-decode
                 octets
                 (fn-frame-trailer (fn-frame-protected-prefix octets))
                 *fn-bpn-lifecycle-max-payload*)))
    (if (not (and (fn-frame-result-okp answer)
                  (equal (fn-frame-result-magic answer)
                         *fn-frame-magic-bundle-store*)
                  (equal (fn-frame-result-version answer) *fn-frame-version*)))
        nil
      (let* ((kind (fn-bpn-lifecycle-code-kind
                    (fn-frame-result-kind answer)))
             (spec (fn-bpn-lifecycle-spec kind)))
        (if (null kind)
            nil
          (let ((parsed (fn-frame-fields-parse
                         spec (fn-frame-result-payload answer))))
            (if (not (fn-frame-parse-okp parsed))
                nil
              (fn-bpn-lifecycle-record-from-values
               kind (fn-frame-parse-value parsed)))))))))

(defun fn-bpn-lifecycle-frame-limit ()
  (declare (xargs :guard t))
  (+ *fn-frame-header-octets* *fn-bpn-lifecycle-max-payload*
     *fn-frame-trailer-octets*))

(deftheory fn-bpn-machine-codec-vocabulary nil)
