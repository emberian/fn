; FNCE version4: remote registration/rebase, distinct from local version1,
; account adoption version2 and signing binding version3. The full encoder
; is a logical/recovery reference. Served preparation emits bounded chunks.
(in-package "ACL2")
(include-book "consumer-remote-fields")
(include-book "consumer-store-events")

(defun fn-crev-code (kind)
 (declare (xargs :guard t))
 (case kind (:remote-register 6) (:remote-rebase 7) (otherwise nil)))

; Only fixed-spine and admitted bounded-field checks, never a group walk.
(defun fn-crev-headp (event)
 (declare (xargs :guard t))
 (let ((op (fn-cp-nth 4 event)))
  (and (fn-cbor-at-mostp event 5) (true-listp event) (equal (len event) 5)
       (eq (fn-cp-nth 0 event) :consumer)
       (fn-cp-uintp (fn-cp-nth 1 event)) (fn-cp-uintp (fn-cp-nth 2 event))
       (fn-cp-uintp (fn-cp-nth 3 event))
       (fn-cbor-at-mostp op 9) (true-listp op) (equal (len op) 9)
       (fn-crev-code (fn-cp-nth 0 op))
       (fn-cp-idp (fn-cp-nth 1 op)) (fn-cp-idp (fn-cp-nth 2 op))
       (fn-cp-idp (fn-cp-nth 3 op))
       (fn-cp-uintp (fn-cp-nth 4 op)) (fn-cp-uintp (fn-cp-nth 5 op))
       (fn-cp-uintp (fn-cp-nth 6 op)) (posp (fn-cp-nth 6 op))
       (fn-cp-idp (fn-cp-nth 8 op)))))

(defun fn-crev-id (value)
 (declare (xargs :guard t))
 (if (true-listp value) (cons (len value) value) nil))

; Fixed header, three bounded IDs, three uint32 coordinates, bounded account
; creation token, uint32 query count. Each query name uses uint16+octets.
(defun fn-crev-header (event count)
 (declare (xargs :guard t))
 (if (not (and (fn-crev-headp event) (fn-cp-uintp count) (posp count))) nil
  (let ((op (fn-cp-nth 4 event)))
   (append '(102 110 99 101) (list 4 (fn-crev-code (fn-cp-nth 0 op)))
     (fn-cbor-u32-bytes (fn-cp-nth 1 event))
     (fn-cbor-u32-bytes (fn-cp-nth 2 event))
     (fn-cbor-u32-bytes (fn-cp-nth 3 event))
     (fn-crev-id (fn-cp-nth 1 op)) (fn-crev-id (fn-cp-nth 2 op))
     (fn-crev-id (fn-cp-nth 3 op))
     (fn-cbor-u32-bytes (fn-cp-nth 4 op))
     (fn-cbor-u32-bytes (fn-cp-nth 5 op))
     (fn-cbor-u32-bytes (fn-cp-nth 6 op))
     (fn-crev-id (fn-cp-nth 8 op)) (fn-cbor-u32-bytes count)))))

(defun fn-crev-groups-encode (groups)
 (declare (xargs :guard t))
 (if (not (consp groups)) nil
  (append (ec-call (fn-cbor-u16-bytes (len (car groups))))
          (if (true-listp (car groups)) (car groups) nil)
          (fn-crev-groups-encode (cdr groups)))))

(defun fn-crev-encode-reference (event)
 (declare (xargs :guard t))
 (let ((groups (fn-cp-nth 7 (fn-cp-nth 4 event))))
  (append (fn-crev-header event (len groups)) (fn-crev-groups-encode groups))))

(defun fn-crev-header-charge (event count)
 (declare (xargs :guard t))
 (if (not (and (fn-crev-headp event) (fn-cp-uintp count) (posp count))) 0
  (let ((op (fn-cp-nth 4 event)))
   (+ 38 (len (fn-cp-nth 1 op)) (len (fn-cp-nth 2 op))
          (len (fn-cp-nth 3 op)) (len (fn-cp-nth 8 op))))))

; Fixed8 chunk cursor: tag, source key, borrowed query tail, remaining count,
; remaining wire octets, previous group, header, phase. A current source
; issuer must retain the event/definition and fund each bounded chunk.
(defun fn-crev-state (key groups count wire previous header phase)
 (declare (xargs :guard t))
 (list :remote-event key groups count wire previous header phase))

(defun fn-crev-begin (event count wire key record-budget)
 (declare (xargs :guard t))
 (cond ((not (and (fn-crev-headp event) (fn-cp-uintp count) (posp count) (natp wire)))
        '(:refused :remote-event))
       ((< (nfix record-budget) (+ (fn-crev-header-charge event count) wire))
        '(:refused :record-budget))
       (t (list :yield (fn-crev-state key (fn-cp-nth 7 (fn-cp-nth 4 event))
                         count wire nil (fn-crev-header event count) :header)))))

(local
 (defthm fn-crev-bounded-name-length
  (implies (fn-cbor-at-mostp xs bound) (<= (len xs) (nfix bound)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-cbor-at-mostp xs bound)
                  :in-theory (enable fn-cbor-at-mostp len)))))

(defun fn-crev-tick (s current-key)
 (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-crs-namep)))))
 (let ((key (fn-cp-nth 1 s)) (groups (fn-cp-nth 2 s))
       (count (nfix (fn-cp-nth 3 s))) (wire (nfix (fn-cp-nth 4 s)))
       (previous (fn-cp-nth 5 s)) (header (fn-cp-nth 6 s)) (phase (fn-cp-nth 7 s)))
  (cond ((not (equal key current-key)) '(:refused :consumer-source-changed))
        ((eq phase :header)
         (list :chunk header (fn-crev-state key groups count wire previous nil :groups)))
        ((not (eq phase :groups)) '(:refused :remote-event-phase))
        ((zp count)
         (if (and (null groups) (zp wire)) '(:encoded) '(:refused :remote-event-charge)))
        ((or (not (consp groups)) (not (fn-crs-namep (car groups)))
              (and previous (or (not (lexorder previous (car groups))) (equal previous (car groups)))))
         '(:refused :remote-event-query))
        ((< wire (+ 2 (len (car groups)))) '(:refused :remote-event-charge))
        (t (list :chunk (append (fn-cbor-u16-bytes (len (car groups))) (car groups))
                (fn-crev-state key (cdr groups) (1- count) (- wire (+ 2 (len (car groups))))
                                (car groups) nil :groups))))))

(local
 (defthm fn-crev-u32-length
  (equal (len (fn-cbor-u32-bytes n)) 4)
  :hints (("Goal" :in-theory (e/d (fn-cbor-u32-bytes) (floor mod))))))

(local
 (defthm fn-crev-id-length
  (implies (true-listp value) (equal (len (fn-crev-id value)) (+ 1 (len value))))
  :hints (("Goal" :in-theory (enable fn-crev-id)))))

(local
 (defthm fn-crev-header-proper-id-fields
  (implies (fn-crev-headp event)
   (let ((op (fn-cp-nth 4 event)))
    (and (true-listp (fn-cp-nth 1 op)) (true-listp (fn-cp-nth 2 op))
         (true-listp (fn-cp-nth 3 op)) (true-listp (fn-cp-nth 8 op)))))
  :hints (("Goal" :in-theory (e/d (fn-crev-headp fn-cp-idp fn-cbor-octet-listp)
                                      (fn-cp-nth fn-cbor-at-mostp len))))))

(defthm fn-crev-header-charge-is-encoded-length
 (equal (fn-crev-header-charge event count) (len (fn-crev-header event count)))
 :hints (("Goal" :in-theory (e/d (fn-crev-header-charge fn-crev-header)
                                   (fn-crev-headp fn-crev-id fn-cp-nth fn-cp-uintp
                                    fn-crev-code fn-cbor-u32-bytes floor mod)))))

(defun fn-crev-kind (code)
 (declare (xargs :guard t))
 (case code (6 :remote-register) (7 :remote-rebase) (otherwise nil)))

; Logical recovery parser. The served located-buffer parser must retain its
; admitted record and resume one name per tick; it never calls this walker.
(defun fn-crev-read-groups (count bytes previous)
 (declare (xargs :guard t :measure (nfix count)))
 (if (zp (nfix count)) (list :ok nil bytes)
  (if (not (fn-cbor-at-leastp bytes 2)) '(:error :remote-query)
   (let* ((n (ec-call (fn-cbor-u16-from bytes)))
          (body (if (consp bytes) (cdr (if (consp (cdr bytes)) (cdr bytes) nil)) nil)))
    (if (or (not (posp n)) (< *fn-record-max-group-name* n)
             (not (fn-cbor-at-leastp body n))) '(:error :remote-query)
     (let ((name (ec-call (take n body))))
      (if (or (not (fn-crs-namep name))
               (and previous (or (not (lexorder previous name)) (equal previous name))))
          '(:error :remote-query)
       (let ((rest (fn-crev-read-groups (1- (nfix count)) (ec-call (nthcdr n body)) name)))
        (if (eq (fn-cp-nth 0 rest) :ok)
            (list :ok (cons name (fn-cp-nth 1 rest)) (fn-cp-nth 2 rest)) rest)))))))))

(defun fn-crev-decode-exact (bytes)
 (declare (xargs :guard t))
 (if (or (not (equal (ec-call (take 4 bytes)) '(102 110 99 101)))
          (not (equal (fn-cp-nth 4 bytes) 4))) '(:error :remote-version)
  (let* ((kind (fn-crev-kind (fn-cp-nth 5 bytes)))
         (coords (ec-call (fn-cp-read-fields (ec-call (nthcdr 6 bytes)) '(:uint :uint :uint)))))
   (if (or (not kind) (not (eq (fn-cp-nth 0 coords) :ok))) '(:error :remote-envelope)
    (let ((fields (ec-call (fn-cp-read-fields (fn-cp-nth 2 coords)
                                     '(:id :id :id :uint :uint :uint :id :uint)))))
     (if (not (eq (fn-cp-nth 0 fields) :ok)) '(:error :remote-fields)
      (let* ((v (fn-cp-nth 1 coords)) (f (fn-cp-nth 1 fields))
             (count (fn-cp-nth 7 f))
             (groups (fn-crev-read-groups count (fn-cp-nth 2 fields) nil))
             (event (list :consumer (fn-cp-nth 0 v) (fn-cp-nth 1 v) (fn-cp-nth 2 v)
               (list kind (fn-cp-nth 0 f) (fn-cp-nth 1 f) (fn-cp-nth 2 f)
                          (fn-cp-nth 3 f) (fn-cp-nth 4 f) (fn-cp-nth 5 f)
                          (fn-cp-nth 1 groups) (fn-cp-nth 6 f)))))
       (if (and (posp count) (eq (fn-cp-nth 0 groups) :ok) (null (fn-cp-nth 2 groups))
                (fn-crev-headp event)) (list :ok event) '(:error :remote-event)))))))))

(in-theory (disable fn-crev-code fn-crev-headp fn-crev-id fn-crev-header
                    fn-crev-groups-encode fn-crev-encode-reference
                    fn-crev-header-charge fn-crev-state fn-crev-begin fn-crev-tick
                    fn-crev-kind fn-crev-read-groups fn-crev-decode-exact))
