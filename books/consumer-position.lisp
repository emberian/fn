; E2 v1 finite consumer-position decision kernel.  No host calls this book yet.
; A :write result is a proposed Store event, not durable acceptance.  The
; authoritative Store record/replay/finish join remains open.
(in-package "ACL2")

(defconst *fn-cp-max-id* 64)
(defconst *fn-cp-max-token* 512)
(defconst *fn-cp-max-consumers* 256)
(defconst *fn-cp-max-uint* 4294967295)
(defconst *fn-cp-magic* '(102 110 99 117)) ; "fncu"
(defconst *fn-cp-version* 1)

(defun fn-cp-octetp (x)
  (and (integerp x) (<= 0 x) (<= x 255)))

(defun fn-cp-at-mostp (xs n)
  (declare (xargs :measure (nfix n)))
  (if (consp xs)
      (and (posp n) (fn-cp-at-mostp (cdr xs) (1- n)))
    (null xs)))

(defun fn-cp-octet-listp (xs)
  (if (consp xs)
      (and (fn-cp-octetp (car xs)) (fn-cp-octet-listp (cdr xs)))
    (null xs)))

(defun fn-cp-idp (x)
  (and (consp x) (fn-cp-at-mostp x *fn-cp-max-id*)
       (fn-cp-octet-listp x)))

(defun fn-cp-uintp (x)
  (and (natp x) (<= x *fn-cp-max-uint*)))

; A decoded cursor: (:cursor history incarnation consumer principal query
;                    query-version view-version registration-epoch position).
(defun fn-cp-cursor (history incarnation consumer principal query qver view epoch pos)
  (list :cursor history incarnation consumer principal query qver view epoch pos))

(defun fn-cp-cursorp (x)
  (and (true-listp x) (equal (len x) 10) (equal (nth 0 x) :cursor)
       (fn-cp-idp (nth 1 x)) (fn-cp-idp (nth 2 x))
       (fn-cp-idp (nth 3 x)) (fn-cp-idp (nth 4 x))
       (fn-cp-idp (nth 5 x)) (fn-cp-uintp (nth 6 x))
       (fn-cp-uintp (nth 7 x)) (fn-cp-uintp (nth 8 x))
       (fn-cp-uintp (nth 9 x)) (posp (nth 8 x))))

(defun fn-cp-u32-bytes (n)
  (list (mod (floor n 16777216) 256)
        (mod (floor n 65536) 256)
        (mod (floor n 256) 256)
        (mod n 256)))

(defun fn-cp-u32-value (xs)
  (+ (* 16777216 (nth 0 xs)) (* 65536 (nth 1 xs))
     (* 256 (nth 2 xs)) (nth 3 xs)))

(defun fn-cp-id-bytes (x)
  (cons (len x) x))

; Five nonempty length-prefixed octet IDs and four uint32 values.  The
; recognizer is run on a caller-supplied cursor only, not on the Store.
(defun fn-cp-cursor-encode (cursor)
  (if (not (fn-cp-cursorp cursor)) nil
    (append *fn-cp-magic* (list *fn-cp-version*)
            (fn-cp-id-bytes (nth 1 cursor))
            (fn-cp-id-bytes (nth 2 cursor))
            (fn-cp-id-bytes (nth 3 cursor))
            (fn-cp-id-bytes (nth 4 cursor))
            (fn-cp-id-bytes (nth 5 cursor))
            (fn-cp-u32-bytes (nth 6 cursor))
            (fn-cp-u32-bytes (nth 7 cursor))
            (fn-cp-u32-bytes (nth 8 cursor))
            (fn-cp-u32-bytes (nth 9 cursor)))))

; Each step is bounded by the 512-octet preflight in the public decoder.
; Result is (:ok value rest) or (:error reason).
(defun fn-cp-read-id (xs)
  (if (and (consp xs) (posp (car xs))
           (<= (car xs) *fn-cp-max-id*)
           (<= (car xs) (len (cdr xs))))
      (list :ok (take (car xs) (cdr xs)) (nthcdr (car xs) (cdr xs)))
    (list :error :id)))

(defun fn-cp-read-u32 (xs)
  (if (<= 4 (len xs))
      (list :ok (fn-cp-u32-value xs) (nthcdr 4 xs))
    (list :error :uint)))

(defun fn-cp-read-fields (xs kinds)
  (declare (xargs :measure (len kinds)))
  (if (endp kinds) (list :ok nil xs)
    (let ((field (if (eq (car kinds) :id)
                     (fn-cp-read-id xs) (fn-cp-read-u32 xs))))
      (if (not (eq (car field) :ok)) field
        (let ((rest (fn-cp-read-fields (nth 2 field) (cdr kinds))))
          (if (not (eq (car rest) :ok)) rest
            (list :ok (cons (nth 1 field) (nth 1 rest))
                  (nth 2 rest))))))))

(defun fn-cp-cursor-decode (octets)
  (if (or (not (fn-cp-at-mostp octets *fn-cp-max-token*))
          (not (fn-cp-octet-listp octets)))
      (list :refused :octets)
    (if (or (not (equal (take 4 octets) *fn-cp-magic*))
            (not (equal (nth 4 octets) *fn-cp-version*)))
        (list :refused :version)
      (let ((fields (fn-cp-read-fields
                     (nthcdr 5 octets)
                     '(:id :id :id :id :id :uint :uint :uint :uint))))
        (if (or (not (eq (car fields) :ok)) (consp (nth 2 fields)))
            (list :refused :grammar)
          (let* ((v (nth 1 fields))
                 (cursor (fn-cp-cursor
                          (nth 0 v) (nth 1 v) (nth 2 v) (nth 3 v)
                          (nth 4 v) (nth 5 v) (nth 6 v) (nth 7 v)
                          (nth 8 v))))
            (if (fn-cp-cursorp cursor) (list :ok cursor)
              (list :refused :grammar))))))))

; Entry: (:entry consumer principal query qver view epoch ack).
(defun fn-cp-entry (consumer principal query qver view epoch ack)
  (list :entry consumer principal query qver view epoch ack))

(defun fn-cp-find (consumer entries)
  (if (endp entries) nil
    (if (equal consumer (nth 1 (car entries))) (car entries)
      (fn-cp-find consumer (cdr entries)))))

(defun fn-cp-remove (consumer entries)
  (if (endp entries) nil
    (if (equal consumer (nth 1 (car entries))) (cdr entries)
      (cons (car entries) (fn-cp-remove consumer (cdr entries))))))

; State: (:consumer-state history incarnation committed-frontier next-epoch
;         entries).  next-epoch is one scalar, so unregister does not need an
; unbounded tombstone table.  Epoch exhaustion refuses a new registration.
(defun fn-cp-state (history incarnation frontier next-epoch entries)
  (list :consumer-state history incarnation frontier next-epoch entries))

(defun fn-cp-initial (history incarnation frontier)
  (fn-cp-state history incarnation frontier 1 nil))

(defun fn-cp-scope-cursor (s entry)
  (fn-cp-cursor (nth 1 s) (nth 2 s) (nth 1 entry) (nth 2 entry)
                (nth 3 entry) (nth 4 entry) (nth 5 entry)
                (nth 6 entry) (nth 7 entry)))

(defun fn-cp-scope-matchp (s caller qver view cursor entry)
  (and (fn-cp-cursorp cursor) (consp entry)
       (equal (nth 1 cursor) (nth 1 s))
       (equal (nth 2 cursor) (nth 2 s))
       (equal (nth 3 cursor) (nth 1 entry))
       (equal (nth 4 cursor) caller)
       (equal (nth 4 cursor) (nth 2 entry))
       (equal (nth 5 cursor) (nth 3 entry))
       (equal (nth 6 cursor) qver)
       (equal (nth 6 cursor) (nth 4 entry))
       (equal (nth 7 cursor) view)
       (equal (nth 7 cursor) (nth 5 entry))
       (equal (nth 8 cursor) (nth 6 entry))))

; Decision results: (:write event), (:no-op cursor), (:refused reason).
; The owner must choose qver/view from its current ACL2 policy projection,
; rather than accepting those two values from the consumer request.
(defun fn-cp-register (s caller consumer query qver view)
  (let ((old (fn-cp-find consumer (nth 5 s))))
    (cond ((or (not (fn-cp-idp caller)) (not (fn-cp-idp consumer))
               (not (fn-cp-idp query)) (not (fn-cp-uintp qver))
               (not (fn-cp-uintp view))) (list :refused :input))
          (old (if (and (equal caller (nth 2 old))
                        (equal query (nth 3 old))
                        (equal qver (nth 4 old))
                        (equal view (nth 5 old)))
                   (list :no-op (fn-cp-scope-cursor s old))
                 (list :refused :rebase-required)))
          ((>= (len (nth 5 s)) *fn-cp-max-consumers*)
           (list :refused :capacity))
          ((or (not (posp (nth 4 s)))
               (not (fn-cp-uintp (nth 4 s)))
               (equal (nth 4 s) *fn-cp-max-uint*))
           (list :refused :epoch-exhausted))
          (t (list :write (list :register consumer caller query qver view
                                (nth 4 s)))))))

(defun fn-cp-ack (s caller qver view cursor)
  (let ((entry (fn-cp-find (nth 3 cursor) (nth 5 s))))
    (cond ((not (fn-cp-scope-matchp s caller qver view cursor entry))
           (list :refused :scope))
          ((> (nth 9 cursor) (nth 3 s)) (list :refused :future))
          ((< (nth 9 cursor) (nth 7 entry)) (list :refused :backwards))
          ((equal (nth 9 cursor) (nth 7 entry))
           (list :no-op (fn-cp-scope-cursor s entry)))
          (t (list :write (list :ack cursor))))))

(defun fn-cp-rebase (s caller consumer query qver view)
  (let ((entry (fn-cp-find consumer (nth 5 s))))
    (cond ((or (not (fn-cp-idp caller)) (not (fn-cp-idp query))
               (not (fn-cp-uintp qver)) (not (fn-cp-uintp view)))
           (list :refused :input))
          ((or (not entry) (not (equal caller (nth 2 entry))))
           (list :refused :scope))
          ((and (equal query (nth 3 entry))
                (equal qver (nth 4 entry))
                (equal view (nth 5 entry)))
           (list :no-op (fn-cp-scope-cursor s entry)))
          ((or (not (posp (nth 4 s)))
               (not (fn-cp-uintp (nth 4 s)))
               (equal (nth 4 s) *fn-cp-max-uint*))
           (list :refused :epoch-exhausted))
          (t (list :write (list :rebase consumer caller query qver view
                                (nth 4 s)))))))

(defun fn-cp-unregister (s caller consumer)
  (let ((entry (fn-cp-find consumer (nth 5 s))))
    (if (and entry (equal caller (nth 2 entry)))
        (list :write (list :unregister consumer (nth 6 entry)))
      (list :refused :scope))))

; The event applier is the model of a committed proposal, not a second
; journal.  Its shape checks make malformed/replayed events inert.  Durable
; acceptance needs the Store record for exactly this event and replay step.
(defun fn-cp-apply (s event)
  (let* ((kind (car event))
         (consumer (nth 1 event))
         (entries (nth 5 s))
         (old (fn-cp-find consumer entries)))
    (cond
     ((and (eq kind :register) (equal (len event) 7)
           (not old) (< (len entries) *fn-cp-max-consumers*)
           (equal (nth 6 event) (nth 4 s))
           (posp (nth 6 event))
           (fn-cp-uintp (nth 6 event))
           (< (nth 6 event) *fn-cp-max-uint*)
           (fn-cp-idp consumer) (fn-cp-idp (nth 2 event))
           (fn-cp-idp (nth 3 event))
           (fn-cp-uintp (nth 4 event)) (fn-cp-uintp (nth 5 event)))
      (fn-cp-state (nth 1 s) (nth 2 s) (nth 3 s)
                   (1+ (nth 4 s))
                   (cons (fn-cp-entry consumer (nth 2 event)
                                      (nth 3 event) (nth 4 event)
                                      (nth 5 event) (nth 6 event) 0)
                         entries)))
     ((and (eq kind :rebase) (equal (len event) 7)
           old (equal (nth 2 event) (nth 2 old))
           (equal (nth 6 event) (nth 4 s))
           (posp (nth 6 event))
           (fn-cp-uintp (nth 6 event))
           (< (nth 6 event) *fn-cp-max-uint*)
           (fn-cp-idp (nth 3 event))
           (fn-cp-uintp (nth 4 event)) (fn-cp-uintp (nth 5 event)))
      (fn-cp-state (nth 1 s) (nth 2 s) (nth 3 s)
                   (1+ (nth 4 s))
                   (cons (fn-cp-entry consumer (nth 2 old)
                                      (nth 3 event) (nth 4 event)
                                      (nth 5 event) (nth 6 event) 0)
                         (fn-cp-remove consumer entries))))
     ((and (eq kind :ack) (equal (len event) 2)
           (fn-cp-scope-matchp s (nth 4 (nth 1 event))
                                (nth 6 (nth 1 event))
                                (nth 7 (nth 1 event))
                                (nth 1 event)
                                (fn-cp-find (nth 3 (nth 1 event)) entries))
           (<= (nth 9 (nth 1 event)) (nth 3 s))
           (<= (nth 7 (fn-cp-find (nth 3 (nth 1 event)) entries))
               (nth 9 (nth 1 event))))
      (let* ((cursor (nth 1 event))
             (entry (fn-cp-find (nth 3 cursor) entries)))
        (fn-cp-state (nth 1 s) (nth 2 s) (nth 3 s) (nth 4 s)
                     (cons (fn-cp-entry (nth 3 cursor) (nth 2 entry)
                                        (nth 3 entry) (nth 4 entry)
                                        (nth 5 entry) (nth 6 entry)
                                        (nth 9 cursor))
                           (fn-cp-remove (nth 3 cursor) entries)))))
     ((and (eq kind :unregister) (equal (len event) 3)
           old (equal (nth 2 event) (nth 6 old)))
      (fn-cp-state (nth 1 s) (nth 2 s) (nth 3 s) (nth 4 s)
                   (fn-cp-remove consumer entries)))
     (t s))))

; These are about the decision the future owner must call before a Store
; publication.  They do not assert publication, replay or physical durability.
(defthm fn-cp-ack-write-never-passes-committed-frontier
  (implies (equal (car (fn-cp-ack s caller qver view cursor)) :write)
           (<= (nth 9 cursor) (nth 3 s))))

(defthm fn-cp-ack-write-binds-current-registration-epoch
  (implies (equal (car (fn-cp-ack s caller qver view cursor)) :write)
           (equal (nth 8 cursor)
                  (nth 6 (fn-cp-find (nth 3 cursor) (nth 5 s))))))

(defthm fn-cp-ack-stale-epoch-is-refused
  (implies (not (equal (nth 8 cursor)
                       (nth 6 (fn-cp-find (nth 3 cursor) (nth 5 s)))))
           (equal (fn-cp-ack s caller qver view cursor)
                  (list :refused :scope))))

(defthm fn-cp-apply-preserves-committed-frontier
  (equal (nth 3 (fn-cp-apply s event)) (nth 3 s)))

(defthm fn-cp-apply-epoch-changes-only-by-one
  (or (equal (nth 4 (fn-cp-apply s event)) (nth 4 s))
      (equal (nth 4 (fn-cp-apply s event)) (1+ (nth 4 s)))))

(defthm fn-cp-remove-never-increases-length
  (<= (len (fn-cp-remove consumer entries)) (len entries)))

(defthm fn-cp-remove-length-linear
  (<= (len (fn-cp-remove consumer entries)) (len entries))
  :rule-classes :linear)

(defthm fn-cp-remove-found-decreases-length
  (implies (fn-cp-find consumer entries)
           (< (len (fn-cp-remove consumer entries)) (len entries)))
  :rule-classes :linear)

(defthm fn-cp-apply-preserves-consumer-capacity
  (implies (<= (len (nth 5 s)) *fn-cp-max-consumers*)
           (<= (len (nth 5 (fn-cp-apply s event)))
               *fn-cp-max-consumers*)))

; The codec and decision internals are opened only by a caller's focused
; proof.  Importing this leaf must not expand its parser in every later goal.
(in-theory (disable (:d fn-cp-cursor-encode) (:d fn-cp-cursor-decode)
                    (:d fn-cp-register) (:d fn-cp-ack)
                    (:d fn-cp-rebase) (:d fn-cp-unregister)
                    (:d fn-cp-apply) (:d fn-cp-scope-matchp)))
