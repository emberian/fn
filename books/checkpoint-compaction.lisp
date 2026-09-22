; Lossless transaction-prefix summaries for authoritative checkpoint compaction.
; A node checkpoint alone is insufficient: newer Store transaction kinds carry
; retention and identity history.  This summary retains the exact canonical
; bytes of every compacted transaction for the one Store decoder to replay.
(in-package "ACL2")
(include-book "store-events")
(include-book "frame-journal")

(defconst *fn-cc-magic* '(102 110 45 120)) ; "fn-x"
(defconst *fn-cc-version* 0)
(defconst *fn-cc-max-events* 4096)
(defconst *fn-cc-max-octets* 4194304)

; `zp' carries the guard (natp n); every caller in this book passes a
; literal index.  Declared `:guard t' until 2026-09-22, which no ACL2 run
; had ever been asked to verify at this digest.
(defun fn-cc-nth (n x)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) (if (consp x) (car x) nil)
    (fn-cc-nth (1- n) (if (consp x) (cdr x) nil))))

; (:fn-compaction-summary 0 next-sequence allocator-frontier event-octets)
(defun fn-cc-make (sequence frontier event-octets)
  (declare (xargs :guard t :verify-guards nil))
  (list :fn-compaction-summary 0 sequence frontier event-octets))
(defun fn-cc-sequence (summary) (declare (xargs :guard t)) (fn-cc-nth 2 summary))
(defun fn-cc-frontier (summary) (declare (xargs :guard t)) (fn-cc-nth 3 summary))
(defun fn-cc-events (summary) (declare (xargs :guard t)) (fn-cc-nth 4 summary))

(defun fn-cc-event-octets-size (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (+ (len (car events)) 5 (fn-cc-event-octets-size (cdr events)))
    32))

(defun fn-cc-octet-event-listp (octet-events sequence lower-frontier upper-frontier)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp octet-events)
      (let ((decoded (fn-store-event-decode-exact (car octet-events))))
        (and (fn-cbor-octet-listp (car octet-events))
             (equal (car decoded) :ok)
             (fn-store-event-p (fn-cc-nth 1 decoded))
             (equal (fn-store-event-sequence (fn-cc-nth 1 decoded)) sequence)
             (equal (fn-store-event-txid (fn-cc-nth 1 decoded))
                    (fn-store-event-generation (fn-cc-nth 1 decoded)))
             (<= lower-frontier (fn-store-event-txid (fn-cc-nth 1 decoded)))
             (< (fn-store-event-txid (fn-cc-nth 1 decoded)) upper-frontier)
             (fn-cc-octet-event-listp
              (cdr octet-events) (+ 1 sequence)
              (+ 1 (fn-store-event-txid (fn-cc-nth 1 decoded))) upper-frontier)))
    (null octet-events)))

(defun fn-cc-summaryp (summary)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp summary) (equal (len summary) 5)
       (equal (fn-cc-nth 0 summary) :fn-compaction-summary)
       (equal (fn-cc-nth 1 summary) 0)
       (fn-record-uint32p (fn-cc-sequence summary))
       (fn-record-uint32p (fn-cc-frontier summary))
       (<= (fn-cc-sequence summary) (fn-cc-frontier summary))
       (equal (len (fn-cc-events summary)) (fn-cc-sequence summary))
       (<= (fn-cc-sequence summary) *fn-cc-max-events*)
       (fn-cc-octet-event-listp (fn-cc-events summary) 0 0
                                (fn-cc-frontier summary))))

(defun fn-cc-capture (octet-events frontier)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-record-uint32p frontier)
           (<= (len octet-events) frontier)
           (fn-record-uint32p (len octet-events))
           (<= (len octet-events) *fn-cc-max-events*)
           (<= (fn-cc-event-octets-size octet-events) *fn-cc-max-octets*)
           (fn-cc-octet-event-listp octet-events 0 0 frontier))
      (list :ok (fn-cc-make (len octet-events) frontier octet-events))
    (list :error :history)))

(defun fn-cc-expand (summary suffix final-frontier)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((not (fn-cc-summaryp summary)) (list :error :summary))
        ((or (not (fn-record-uint32p final-frontier))
             (< final-frontier (fn-cc-frontier summary)))
         (list :error :frontier))
        ((not (fn-cc-octet-event-listp suffix (fn-cc-sequence summary)
                                       (fn-cc-frontier summary) final-frontier))
         (list :error :suffix))
        (t (list :ok (append (fn-cc-events summary) suffix) final-frontier))))

; Guard verification is deferred for this whole book, as its author left it
; (twelve functions above and below carry :verify-guards nil, and the
; generated ledger counts them).  The three observation functions below were
; declared verifiable with `:guard t' and are not: `<=' needs a rational
; boundary and `nth' a true list, which their (unverified) callers do not
; establish.  They now say so like their siblings.  Verifying this book's
; guards is the compaction lane's open item, not a claim this book makes.
; Every surviving physical record inside the packed interval must be the exact
; packed byte string.  Missing covered records are allowed after an interrupted
; reclaim; no missing record at or above the boundary is accepted by the
; namespace observation.
(defun fn-cc-observation-agrees (pairs events boundary)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (let ((pair (car pairs)))
        (and (true-listp pair) (equal (len pair) 2)
             (natp (car pair))
             (or (<= boundary (car pair))
                 (and (< (car pair) (len events))
                      (equal (cadr pair) (nth (car pair) events))))
             (fn-cc-observation-agrees (cdr pairs) events boundary)))
    (null pairs)))

(defun fn-cc-observation-suffix (pairs boundary)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (if (< (caar pairs) boundary)
          (fn-cc-observation-suffix (cdr pairs) boundary)
        (cons (cadar pairs) (fn-cc-observation-suffix (cdr pairs) boundary)))
    nil))

(defun fn-cc-recover-observation (summary observed frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let ((boundary (fn-cc-sequence summary)))
    (if (not (fn-cc-observation-agrees
              observed (fn-cc-events summary) boundary))
        (list :error :conflict)
      (fn-cc-expand summary
                    (fn-cc-observation-suffix observed boundary)
                    frontier))))

(defun fn-cc-partial-observationp (observed prefix suffix boundary)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal boundary (len prefix))
       (fn-cc-observation-agrees observed prefix boundary)
       (equal (fn-cc-observation-suffix observed boundary) suffix)))

(defun fn-cc-valid-suffixp (summary suffix final-frontier)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-record-uint32p final-frontier)
       (<= (fn-cc-frontier summary) final-frontier)
       (fn-cc-octet-event-listp suffix (fn-cc-sequence summary)
                                (fn-cc-frontier summary) final-frontier)))

(defthm fn-cc-partial-deletion-preserves-exact-history
  (implies (and (fn-cc-summaryp summary)
                (fn-cc-valid-suffixp summary suffix final-frontier)
                (fn-cc-partial-observationp
                 observed (fn-cc-events summary) suffix
                 (fn-cc-sequence summary)))
           (equal (fn-cc-recover-observation summary observed final-frontier)
                  (list :ok (append (fn-cc-events summary) suffix)
                        final-frontier)))
  :hints (("Goal" :in-theory (enable fn-cc-recover-observation
                                     fn-cc-partial-observationp
                                     fn-cc-valid-suffixp
                                     fn-cc-expand fn-cc-summaryp fn-cc-make
                                     fn-cc-sequence fn-cc-frontier fn-cc-events))))

(defun fn-cc-encode-events (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (append (fn-cbor-encode-bounded (cons :bytes (car events))
                                      *fn-frame-max-store-payload*)
              (fn-cc-encode-events (cdr events)))
    nil))

; Canonical summary bytes.  Each already-canonical transaction is carried as
; one definite CBOR byte string, so boundaries do not depend on host filenames.
(defun fn-cc-encode (summary)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cc-summaryp summary)) nil
    (append (fn-cbor-encode (cons :bytes *fn-cc-magic*))
            (fn-cbor-encode (cons :uint *fn-cc-version*))
            (fn-cbor-encode (cons :uint (fn-cc-sequence summary)))
            (fn-cbor-encode (cons :uint (fn-cc-frontier summary)))
            (fn-cbor-encode (cons :uint (len (fn-cc-events summary))))
            (fn-cc-encode-events (fn-cc-events summary)))))

(defun fn-cc-values-event-octets (values)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp values)
      (let ((item (car values)))
        (if (and (consp item) (equal (car item) :bytes))
            (cons (cdr item) (fn-cc-values-event-octets (cdr values)))
          :bad))
    (if (null values) nil :bad)))

(defun fn-cc-decode-exact (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-cbor-octet-listp octets))
          (< *fn-cc-max-octets* (len octets)))
      (list :error :octets)
    (let ((header (fn-stmt-decode-prefix-items-bounded
                   5 octets *fn-cc-max-octets*
                   *fn-frame-max-store-payload*)))
      (if (or (not (equal (car header) :ok))
              (not (equal (fn-cc-nth 0 (fn-cc-nth 1 header))
                          (cons :bytes *fn-cc-magic*)))
              (not (equal (fn-cc-nth 1 (fn-cc-nth 1 header))
                          (cons :uint *fn-cc-version*))))
          (list :error :header)
        (let* ((values (fn-cc-nth 1 header))
               (sequence-item (fn-cc-nth 2 values))
               (frontier-item (fn-cc-nth 3 values))
               (count-item (fn-cc-nth 4 values)))
          (if (or (not (and (consp sequence-item) (equal (car sequence-item) :uint)))
                  (not (and (consp frontier-item) (equal (car frontier-item) :uint)))
                  (not (and (consp count-item) (equal (car count-item) :uint)))
                  (< *fn-cc-max-events* (cdr count-item)))
              (list :error :header)
            (let* ((body (fn-stmt-decode-prefix-items-bounded
                          (cdr count-item) (fn-cc-nth 2 header)
                          *fn-cc-max-octets* *fn-frame-max-store-payload*))
                   (events (if (equal (car body) :ok)
                               (fn-cc-values-event-octets (fn-cc-nth 1 body)) :bad))
                   (summary (fn-cc-make (cdr sequence-item) (cdr frontier-item) events)))
              (if (or (not (equal (car body) :ok))
                      (consp (fn-cc-nth 2 body))
                      (equal events :bad)
                      (not (fn-cc-summaryp summary)))
                  (list :error :summary)
                (list :ok summary)))))))))

(defthm fn-cc-decode-rejects-over-aggregate-bound-before-header
  (implies (< *fn-cc-max-octets* (len octets))
           (equal (fn-cc-decode-exact octets) (list :error :octets)))
  :hints (("Goal" :in-theory (enable fn-cc-decode-exact))))

(defthm fn-cc-capture-produces-summary
  (implies (equal (car (fn-cc-capture prefix frontier)) :ok)
           (fn-cc-summaryp (fn-cc-nth 1 (fn-cc-capture prefix frontier))))
  :hints (("Goal" :in-theory (enable fn-cc-capture fn-cc-summaryp fn-cc-make
                                     fn-cc-sequence fn-cc-frontier fn-cc-events))))

; Definition unfolding: the summary stores the exact prefix bytes and expand
; appends the validated suffix.  This is not a recovery correspondence proof.
(defthm fn-cc-capture-plus-suffix-is-full-history-by-definition
  (implies (and (fn-record-uint32p checkpoint-frontier)
                (fn-record-uint32p final-frontier)
                (<= (len prefix) checkpoint-frontier)
                (<= checkpoint-frontier final-frontier)
                (fn-record-uint32p (len prefix))
                (<= (len prefix) *fn-cc-max-events*)
                (fn-cc-octet-event-listp prefix 0 0 checkpoint-frontier)
                (fn-cc-octet-event-listp suffix (len prefix)
                                         checkpoint-frontier final-frontier))
           (equal (fn-cc-expand
                   (fn-cc-make (len prefix) checkpoint-frontier prefix)
                   suffix final-frontier)
                  (list :ok (append prefix suffix) final-frontier)))
  :hints (("Goal" :in-theory (enable fn-cc-expand fn-cc-summaryp fn-cc-make
                                     fn-cc-sequence fn-cc-frontier fn-cc-events))))

(defthm fn-cc-capture-preserves-prefix-member
  (implies (and (member-equal event-octets prefix)
                (equal (car (fn-cc-capture prefix frontier)) :ok))
           (member-equal event-octets
                         (fn-cc-events
                          (fn-cc-nth 1 (fn-cc-capture prefix frontier)))))
  :hints (("Goal" :in-theory (enable fn-cc-capture fn-cc-events fn-cc-make))))

(deftheory fn-checkpoint-compaction-vocabulary
  '(fn-cc-nth fn-cc-make fn-cc-sequence fn-cc-frontier fn-cc-events
    fn-cc-octet-event-listp fn-cc-summaryp fn-cc-capture fn-cc-expand))
(in-theory (disable fn-checkpoint-compaction-vocabulary))
