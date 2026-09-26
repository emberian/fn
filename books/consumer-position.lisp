; E2 v1 finite consumer-position decision kernel.  No host calls this book yet.
; A :write result is a proposed Store event, not durable acceptance.  The
; authoritative Store record/replay/finish join remains open.
(in-package "ACL2")
(include-book "cbor-invariants")

(defconst *fn-cp-max-id* 64)
(defconst *fn-cp-max-token* 512)
; The consumer count is the operator's (D27; store profile field 9,
; `fn-bs-profile-max-consumers', books/store-profile-namespace): the served
; decision `fn-cp-register-within' takes it as MAX.  Pre-D27 this book held a
; constant 256 here, checked by the decision and again by replay.
(defconst *fn-cp-magic* '(102 110 99 117)) ; "fncu"
(defconst *fn-cp-version* 1)

(defun fn-cp-idp (x)
  (and (consp x) (fn-cbor-at-mostp x *fn-cp-max-id*)
       (fn-cbor-octet-listp x)))

(defun fn-cp-uintp (x)
  (and (natp x) (<= x *fn-cbor-max-uint*)))

; Total fixed-field access.  It never walks the Store or a retained article;
; callers use only small record indices, and no whole-record recognizer runs
; on a served decision path.
(defun fn-cp-nth (n x)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n)
      (if (consp x) (car x) nil)
    (fn-cp-nth (1- n) (if (consp x) (cdr x) nil))))

; A decoded cursor: (:cursor history incarnation consumer principal query
;                    query-version view-version registration-epoch position).
(defun fn-cp-cursor (history incarnation consumer principal query qver view epoch pos)
  (list :cursor history incarnation consumer principal query qver view epoch pos))

(defun fn-cp-cursorp (x)
  (and (true-listp x) (equal (len x) 10) (equal (fn-cp-nth 0 x) :cursor)
       (fn-cp-idp (fn-cp-nth 1 x)) (fn-cp-idp (fn-cp-nth 2 x))
       (fn-cp-idp (fn-cp-nth 3 x)) (fn-cp-idp (fn-cp-nth 4 x))
       (fn-cp-idp (fn-cp-nth 5 x)) (fn-cp-uintp (fn-cp-nth 6 x))
       (fn-cp-uintp (fn-cp-nth 7 x)) (fn-cp-uintp (fn-cp-nth 8 x))
       (fn-cp-uintp (fn-cp-nth 9 x)) (posp (fn-cp-nth 8 x))))

(defun fn-cp-id-bytes (x)
  (cons (len x) x))

; Five nonempty length-prefixed octet IDs and four uint32 values.  The
; recognizer is run on a caller-supplied cursor only, not on the Store.
(defun fn-cp-cursor-encode (cursor)
  (if (not (fn-cp-cursorp cursor)) nil
    (append *fn-cp-magic* (list *fn-cp-version*)
            (fn-cp-id-bytes (fn-cp-nth 1 cursor))
            (fn-cp-id-bytes (fn-cp-nth 2 cursor))
            (fn-cp-id-bytes (fn-cp-nth 3 cursor))
            (fn-cp-id-bytes (fn-cp-nth 4 cursor))
            (fn-cp-id-bytes (fn-cp-nth 5 cursor))
            (fn-cbor-u32-bytes (fn-cp-nth 6 cursor))
            (fn-cbor-u32-bytes (fn-cp-nth 7 cursor))
            (fn-cbor-u32-bytes (fn-cp-nth 8 cursor))
            (fn-cbor-u32-bytes (fn-cp-nth 9 cursor)))))

; Each step is bounded by the 512-octet preflight in the public decoder.
; Result is (:ok value rest) or (:error reason).
(defun fn-cp-read-id (xs)
  (declare (xargs :guard (fn-cbor-octet-listp xs) :verify-guards nil))
  (if (and (consp xs) (posp (car xs))
           (<= (car xs) *fn-cp-max-id*)
           (<= (car xs) (len (cdr xs))))
      (list :ok (take (car xs) (cdr xs)) (nthcdr (car xs) (cdr xs)))
    (list :error :id)))

(defun fn-cp-read-u32 (xs)
  (declare (xargs :guard (fn-cbor-octet-listp xs) :verify-guards nil))
  (if (<= 4 (len xs))
      (list :ok (fn-cbor-u32-from xs) (nthcdr 4 xs))
    (list :error :uint)))

(defun fn-cp-read-fields (xs kinds)
  (declare (xargs :guard (and (fn-cbor-octet-listp xs)
                              (true-listp kinds))
                  :measure (len kinds) :verify-guards nil))
  (if (endp kinds) (list :ok nil xs)
    (let ((field (if (eq (car kinds) :id)
                     (fn-cp-read-id xs) (fn-cp-read-u32 xs))))
      (if (not (eq (car field) :ok)) field
        (let ((rest (fn-cp-read-fields (fn-cp-nth 2 field) (cdr kinds))))
          (if (not (eq (car rest) :ok)) rest
            (list :ok (cons (fn-cp-nth 1 field) (fn-cp-nth 1 rest))
                  (fn-cp-nth 2 rest))))))))

; A proof-side field representation of the public fixed grammar.  The
; equality theorem below connects it to the actual cursor encoder.
(defun fn-cp-fields-validp (vals kinds)
  (declare (xargs :guard (true-listp kinds) :verify-guards nil))
  (if (endp kinds) (null vals)
    (and (consp vals)
         (if (eq (car kinds) :id)
             (fn-cp-idp (car vals)) (fn-cp-uintp (car vals)))
         (fn-cp-fields-validp (cdr vals) (cdr kinds)))))

(defun fn-cp-fields-encode (vals kinds)
  (declare (xargs :guard (and (true-listp kinds)
                              (fn-cp-fields-validp vals kinds))
                  :verify-guards nil))
  (if (endp kinds) nil
    (append (if (eq (car kinds) :id)
                (fn-cp-id-bytes (car vals))
              (fn-cbor-u32-bytes (car vals)))
            (fn-cp-fields-encode (cdr vals) (cdr kinds)))))

(defun fn-cp-cursor-decode (octets)
  (if (or (not (fn-cbor-at-mostp octets *fn-cp-max-token*))
          (not (fn-cbor-octet-listp octets)))
      (list :refused :octets)
    (if (or (not (equal (take 4 octets) *fn-cp-magic*))
            (not (equal (fn-cp-nth 4 octets) *fn-cp-version*)))
        (list :refused :version)
      (let ((fields (fn-cp-read-fields
                     (nthcdr 5 octets)
                     '(:id :id :id :id :id :uint :uint :uint :uint))))
        (if (or (not (eq (car fields) :ok)) (consp (fn-cp-nth 2 fields)))
            (list :refused :grammar)
          (let* ((v (fn-cp-nth 1 fields))
                 (cursor (fn-cp-cursor
                          (fn-cp-nth 0 v) (fn-cp-nth 1 v) (fn-cp-nth 2 v) (fn-cp-nth 3 v)
                          (fn-cp-nth 4 v) (fn-cp-nth 5 v) (fn-cp-nth 6 v) (fn-cp-nth 7 v)
                          (fn-cp-nth 8 v))))
            (if (fn-cp-cursorp cursor) (list :ok cursor)
              (list :refused :grammar))))))))

; Entry: (:entry consumer principal query qver view epoch ack).
(defun fn-cp-entry (consumer principal query qver view epoch ack)
  (list :entry consumer principal query qver view epoch ack))

(defun fn-cp-find (consumer entries)
  (if (not (consp entries)) nil
    (if (equal consumer (fn-cp-nth 1 (car entries))) (car entries)
      (fn-cp-find consumer (cdr entries)))))

(defun fn-cp-remove (consumer entries)
  (if (not (consp entries)) nil
    (if (equal consumer (fn-cp-nth 1 (car entries))) (cdr entries)
      (cons (car entries) (fn-cp-remove consumer (cdr entries))))))

; State: (:consumer-state history incarnation committed-frontier next-epoch
;         entries).  next-epoch is one scalar, so unregister does not need an
; unbounded tombstone table.  Epoch exhaustion refuses a new registration.
(defun fn-cp-state (history incarnation frontier next-epoch entries)
  (list :consumer-state history incarnation frontier next-epoch entries))

; Whole-state recognition is for initialization/reopen and proof boundaries.
; None of the served decision functions below calls it per request.
(defun fn-cp-entryp (entry frontier next-epoch)
  (and (true-listp entry) (equal (len entry) 8)
       (equal (fn-cp-nth 0 entry) :entry)
       (fn-cp-idp (fn-cp-nth 1 entry))
       (fn-cp-idp (fn-cp-nth 2 entry))
       (fn-cp-idp (fn-cp-nth 3 entry))
       (fn-cp-uintp (fn-cp-nth 4 entry))
       (fn-cp-uintp (fn-cp-nth 5 entry))
       (posp (fn-cp-nth 6 entry))
       (< (fn-cp-nth 6 entry) (nfix next-epoch))
       (fn-cp-uintp (fn-cp-nth 7 entry))
       (<= (fn-cp-nth 7 entry) (nfix frontier))))

(defun fn-cp-entriesp (entries frontier next-epoch)
  (if (consp entries)
      (and (fn-cp-entryp (car entries) frontier next-epoch)
           (not (fn-cp-find (fn-cp-nth 1 (car entries)) (cdr entries)))
           (fn-cp-entriesp (cdr entries) frontier next-epoch))
    (null entries)))

(defun fn-cp-statep (s)
  (and (true-listp s) (equal (len s) 6)
       (equal (fn-cp-nth 0 s) :consumer-state)
       (fn-cp-idp (fn-cp-nth 1 s))
       (fn-cp-idp (fn-cp-nth 2 s))
       (fn-cp-uintp (fn-cp-nth 3 s))
       (posp (fn-cp-nth 4 s))
       (fn-cp-uintp (fn-cp-nth 4 s))
       (fn-cp-entriesp (fn-cp-nth 5 s)
                       (fn-cp-nth 3 s) (fn-cp-nth 4 s))))

(defun fn-cp-initial (history incarnation frontier)
  (fn-cp-state history incarnation frontier 1 nil))

(defun fn-cp-scope-cursor (s entry)
  (fn-cp-cursor (fn-cp-nth 1 s) (fn-cp-nth 2 s) (fn-cp-nth 1 entry) (fn-cp-nth 2 entry)
                (fn-cp-nth 3 entry) (fn-cp-nth 4 entry) (fn-cp-nth 5 entry)
                (fn-cp-nth 6 entry) (fn-cp-nth 7 entry)))

(defun fn-cp-scope-matchp (s caller qver view cursor entry)
  (and (fn-cp-cursorp cursor) (consp entry)
       (equal (fn-cp-nth 1 cursor) (fn-cp-nth 1 s))
       (equal (fn-cp-nth 2 cursor) (fn-cp-nth 2 s))
       (equal (fn-cp-nth 3 cursor) (fn-cp-nth 1 entry))
       (equal (fn-cp-nth 4 cursor) caller)
       (equal (fn-cp-nth 4 cursor) (fn-cp-nth 2 entry))
       (equal (fn-cp-nth 5 cursor) (fn-cp-nth 3 entry))
       (equal (fn-cp-nth 6 cursor) qver)
       (equal (fn-cp-nth 6 cursor) (fn-cp-nth 4 entry))
       (equal (fn-cp-nth 7 cursor) view)
       (equal (fn-cp-nth 7 cursor) (fn-cp-nth 5 entry))
       (equal (fn-cp-nth 8 cursor) (fn-cp-nth 6 entry))))

; Decision results: (:write event), (:no-op cursor), (:refused reason).
; The owner must choose qver/view from its current ACL2 policy projection,
; rather than accepting those two values from the consumer request.
(defun fn-cp-register (s caller consumer query qver view)
  (let ((old (fn-cp-find consumer (fn-cp-nth 5 s))))
    (cond ((or (not (fn-cp-idp caller)) (not (fn-cp-idp consumer))
               (not (fn-cp-idp query)) (not (fn-cp-uintp qver))
               (not (fn-cp-uintp view))) (list :refused :input))
          (old (if (and (equal caller (fn-cp-nth 2 old))
                        (equal query (fn-cp-nth 3 old))
                        (equal qver (fn-cp-nth 4 old))
                        (equal view (fn-cp-nth 5 old)))
                   (list :no-op (fn-cp-scope-cursor s old))
                 (list :refused :rebase-required)))
          ((or (not (posp (fn-cp-nth 4 s)))
               (not (fn-cp-uintp (fn-cp-nth 4 s)))
               (equal (fn-cp-nth 4 s) *fn-cbor-max-uint*))
           (list :refused :epoch-exhausted))
          (t (list :write (list :register consumer caller query qver view
                                (fn-cp-nth 4 s)))))))

;   The served registration: `fn-cp-register' under the operator's consumer
; count MAX (profile field 9).  A register write that would hold more than
; MAX entries is refused `:max-consumers'; every other answer is
; `fn-cp-register''s.  Replay re-runs `fn-cp-register' only (the committed
; event's validity, books/consumer-store-projection), not this admission
; bound: the profile only rises (`fn-profile-upgrade-keeps-namespace-counts'),
; so a register the node committed under an older bound is within the
; current one, and a replay that refused it would be whole-state
; revalidation of what the served decision already decided.
(defun fn-cp-register-within (s max caller consumer query qver view)
  (let ((d (fn-cp-register s caller consumer query qver view)))
    (if (and (eq (fn-cp-nth 0 d) :write)
             (<= (nfix max) (len (fn-cp-nth 5 s))))
        (list :refused :max-consumers)
      d)))

(defun fn-cp-ack (s caller qver view cursor)
  (let ((entry (fn-cp-find (fn-cp-nth 3 cursor) (fn-cp-nth 5 s))))
    (cond ((not (fn-cp-scope-matchp s caller qver view cursor entry))
           (list :refused :scope))
          ((> (fn-cp-nth 9 cursor) (nfix (fn-cp-nth 3 s)))
           (list :refused :future))
          ((< (fn-cp-nth 9 cursor) (nfix (fn-cp-nth 7 entry)))
           (list :refused :backwards))
          ((equal (fn-cp-nth 9 cursor) (fn-cp-nth 7 entry))
           (list :no-op (fn-cp-scope-cursor s entry)))
          (t (list :write (list :ack cursor))))))

(defun fn-cp-rebase (s caller consumer query qver view)
  (let ((entry (fn-cp-find consumer (fn-cp-nth 5 s))))
    (cond ((or (not (fn-cp-idp caller)) (not (fn-cp-idp query))
               (not (fn-cp-uintp qver)) (not (fn-cp-uintp view)))
           (list :refused :input))
          ((or (not entry) (not (equal caller (fn-cp-nth 2 entry))))
           (list :refused :scope))
          ((and (equal query (fn-cp-nth 3 entry))
                (equal qver (fn-cp-nth 4 entry))
                (equal view (fn-cp-nth 5 entry)))
           (list :no-op (fn-cp-scope-cursor s entry)))
          ((or (not (posp (fn-cp-nth 4 s)))
               (not (fn-cp-uintp (fn-cp-nth 4 s)))
               (equal (fn-cp-nth 4 s) *fn-cbor-max-uint*))
           (list :refused :epoch-exhausted))
          (t (list :write (list :rebase consumer caller query qver view
                                (fn-cp-nth 4 s)))))))

(defun fn-cp-unregister (s caller consumer)
  (let ((entry (fn-cp-find consumer (fn-cp-nth 5 s))))
    (if (and entry (equal caller (fn-cp-nth 2 entry)))
        (list :write (list :unregister consumer (fn-cp-nth 6 entry)))
      (list :refused :scope))))

; The event applier is the model of a committed proposal, not a second
; journal.  Its shape checks make malformed/replayed events inert.  Durable
; acceptance needs the Store record for exactly this event and replay step.
(defun fn-cp-apply (s event)
  (let* ((kind (fn-cp-nth 0 event))
         (consumer (fn-cp-nth 1 event))
         (entries (fn-cp-nth 5 s))
         (old (fn-cp-find consumer entries)))
    (cond
     ((and (eq kind :register) (equal (len event) 7)
           (not old)
           (equal (fn-cp-nth 6 event) (fn-cp-nth 4 s))
           (posp (fn-cp-nth 6 event))
           (fn-cp-uintp (fn-cp-nth 6 event))
           (< (fn-cp-nth 6 event) *fn-cbor-max-uint*)
           (fn-cp-idp consumer) (fn-cp-idp (fn-cp-nth 2 event))
           (fn-cp-idp (fn-cp-nth 3 event))
           (fn-cp-uintp (fn-cp-nth 4 event)) (fn-cp-uintp (fn-cp-nth 5 event)))
      (fn-cp-state (fn-cp-nth 1 s) (fn-cp-nth 2 s) (fn-cp-nth 3 s)
                   (1+ (fn-cp-nth 4 s))
                   (cons (fn-cp-entry consumer (fn-cp-nth 2 event)
                                      (fn-cp-nth 3 event) (fn-cp-nth 4 event)
                                      (fn-cp-nth 5 event) (fn-cp-nth 6 event) 0)
                         entries)))
     ((and (eq kind :rebase) (equal (len event) 7)
           old (equal (fn-cp-nth 2 event) (fn-cp-nth 2 old))
           (equal (fn-cp-nth 6 event) (fn-cp-nth 4 s))
           (posp (fn-cp-nth 6 event))
           (fn-cp-uintp (fn-cp-nth 6 event))
           (< (fn-cp-nth 6 event) *fn-cbor-max-uint*)
           (fn-cp-idp (fn-cp-nth 3 event))
           (fn-cp-uintp (fn-cp-nth 4 event)) (fn-cp-uintp (fn-cp-nth 5 event)))
      (fn-cp-state (fn-cp-nth 1 s) (fn-cp-nth 2 s) (fn-cp-nth 3 s)
                   (1+ (fn-cp-nth 4 s))
                   (cons (fn-cp-entry consumer (fn-cp-nth 2 old)
                                      (fn-cp-nth 3 event) (fn-cp-nth 4 event)
                                      (fn-cp-nth 5 event) (fn-cp-nth 6 event) 0)
                         (fn-cp-remove consumer entries))))
     ((and (eq kind :ack) (equal (len event) 2)
           (fn-cp-scope-matchp s (fn-cp-nth 4 (fn-cp-nth 1 event))
                                (fn-cp-nth 6 (fn-cp-nth 1 event))
                                (fn-cp-nth 7 (fn-cp-nth 1 event))
                                (fn-cp-nth 1 event)
                                (fn-cp-find (fn-cp-nth 3 (fn-cp-nth 1 event)) entries))
           (<= (fn-cp-nth 9 (fn-cp-nth 1 event)) (nfix (fn-cp-nth 3 s)))
           (<= (nfix (fn-cp-nth 7 (fn-cp-find (fn-cp-nth 3 (fn-cp-nth 1 event)) entries)))
               (fn-cp-nth 9 (fn-cp-nth 1 event))))
      (let* ((cursor (fn-cp-nth 1 event))
             (entry (fn-cp-find (fn-cp-nth 3 cursor) entries)))
        (fn-cp-state (fn-cp-nth 1 s) (fn-cp-nth 2 s) (fn-cp-nth 3 s) (fn-cp-nth 4 s)
                     (cons (fn-cp-entry (fn-cp-nth 3 cursor) (fn-cp-nth 2 entry)
                                        (fn-cp-nth 3 entry) (fn-cp-nth 4 entry)
                                        (fn-cp-nth 5 entry) (fn-cp-nth 6 entry)
                                        (fn-cp-nth 9 cursor))
                           (fn-cp-remove (fn-cp-nth 3 cursor) entries)))))
     ((and (eq kind :unregister) (equal (len event) 3)
           old (equal (fn-cp-nth 2 event) (fn-cp-nth 6 old)))
      (fn-cp-state (fn-cp-nth 1 s) (fn-cp-nth 2 s) (fn-cp-nth 3 s) (fn-cp-nth 4 s)
                   (fn-cp-remove consumer entries)))
     (t s))))

; A finite replay of already committed consumer events.  Store replay will
; eventually supply this ordered sequence; this function performs no I/O.
(defun fn-cp-apply-trace (s events)
  (if (consp events)
      (fn-cp-apply-trace (fn-cp-apply s (car events)) (cdr events))
    s))

; Guard facts are local shape facts, not consumer-processing claims.  They
; keep the decoder's recursive parser closed during its guard proof.
(defthm fn-cp-nthcdr-preserves-octets
  (implies (and (natp n) (fn-cbor-octet-listp xs))
           (fn-cbor-octet-listp (nthcdr n xs))))

(defthm fn-cp-read-fields-ok-values-true-listp
  (implies (equal (car (fn-cp-read-fields xs kinds)) :ok)
           (true-listp (fn-cp-nth 1 (fn-cp-read-fields xs kinds)))))

(defthm fn-cp-scope-match-implies-cursorp
  (implies (fn-cp-scope-matchp s caller qver view cursor entry)
           (fn-cp-cursorp cursor))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cp-scope-matchp))))

(defthm fn-cp-cursorp-position-natural
  (implies (fn-cp-cursorp cursor)
           (natp (fn-cp-nth 9 cursor)))
  :rule-classes :forward-chaining)

(verify-guards fn-cp-idp)
(verify-guards fn-cp-uintp)
(verify-guards fn-cp-cursor)
(verify-guards fn-cp-cursorp)
(verify-guards fn-cp-id-bytes)
(verify-guards fn-cp-cursor-encode)
(verify-guards fn-cp-read-id)
(verify-guards fn-cp-read-u32)
(verify-guards fn-cp-read-fields)
(verify-guards fn-cp-fields-validp)
(verify-guards fn-cp-fields-encode)
(verify-guards fn-cp-cursor-decode
  :hints (("Goal" :in-theory (disable fn-cp-read-fields))))
(verify-guards fn-cp-entry)
(verify-guards fn-cp-find)
(verify-guards fn-cp-remove)
(verify-guards fn-cp-state)
(verify-guards fn-cp-entryp)
(verify-guards fn-cp-entriesp)
(verify-guards fn-cp-statep)
(verify-guards fn-cp-initial)
(verify-guards fn-cp-scope-cursor)
(verify-guards fn-cp-scope-matchp)
(verify-guards fn-cp-register)
(verify-guards fn-cp-register-within)
(verify-guards fn-cp-ack)
(verify-guards fn-cp-rebase)
(verify-guards fn-cp-unregister)
(verify-guards fn-cp-apply)
(verify-guards fn-cp-apply-trace)

; These are about the decision the future owner must call before a Store
; publication.  They do not assert publication, replay or physical durability.
(defthm fn-cp-ack-write-frontier-by-definition
  (implies (equal (car (fn-cp-ack s caller qver view cursor)) :write)
           (<= (fn-cp-nth 9 cursor) (nfix (fn-cp-nth 3 s)))))

(defthm fn-cp-ack-write-epoch-by-definition
  (implies (equal (car (fn-cp-ack s caller qver view cursor)) :write)
           (equal (fn-cp-nth 8 cursor)
                  (fn-cp-nth 6 (fn-cp-find (fn-cp-nth 3 cursor) (fn-cp-nth 5 s))))))

(defthm fn-cp-ack-stale-epoch-refusal-by-definition
  (implies (not (equal (fn-cp-nth 8 cursor)
                       (fn-cp-nth 6 (fn-cp-find (fn-cp-nth 3 cursor) (fn-cp-nth 5 s)))))
           (equal (fn-cp-ack s caller qver view cursor)
                  (list :refused :scope))))

(defthm fn-cp-apply-preserves-committed-frontier
  (equal (fn-cp-nth 3 (fn-cp-apply s event)) (fn-cp-nth 3 s)))

(defthm fn-cp-apply-epoch-changes-only-by-one
  (or (equal (fn-cp-nth 4 (fn-cp-apply s event)) (fn-cp-nth 4 s))
      (equal (fn-cp-nth 4 (fn-cp-apply s event)) (1+ (fn-cp-nth 4 s)))))

(defthm fn-cp-remove-never-increases-length
  (<= (len (fn-cp-remove consumer entries)) (len entries)))

(defthm fn-cp-remove-length-linear
  (<= (len (fn-cp-remove consumer entries)) (len entries))
  :rule-classes :linear)

(defthm fn-cp-remove-found-decreases-length
  (implies (fn-cp-find consumer entries)
           (< (len (fn-cp-remove consumer entries)) (len entries)))
  :rule-classes :linear)

; Only a register grows the table, and by one entry.
(defthm fn-cp-apply-grows-only-by-a-register
  (<= (len (fn-cp-nth 5 (fn-cp-apply s event)))
      (if (eq (fn-cp-nth 0 event) :register)
          (1+ (len (fn-cp-nth 5 s)))
        (len (fn-cp-nth 5 s))))
  :rule-classes nil)

; KEYSTONE (the served registration refuses exactly past the operator's
; bound).  Of the answers `fn-cp-register' gives, the served decision
; changes only a register write, and refuses it `:max-consumers' exactly when
; the table already holds MAX entries, so after the write it would hold more
; than MAX.  Every other answer, and every write within the bound, is
; `fn-cp-register''s, which replay re-runs.  The host calls the subject
; through `fn-col-register' (books/consumer-owner-local), from
; host/owner-host.lisp `fn-owner-consumer-local-register', with MAX the
; opened profile's field 9 (host/store-host.lisp
; `fn-store-profile-max-consumers').
(defthm fn-cp-register-within-refuses-exactly-past-the-operator-bound
  (let ((d (fn-cp-register s caller consumer query qver view))
        (w (fn-cp-register-within s max caller consumer query qver view)))
    (and (iff (equal w '(:refused :max-consumers))
              (and (equal (car d) :write)
                   (<= (nfix max) (len (fn-cp-nth 5 s)))))
         (implies (not (equal w '(:refused :max-consumers)))
                  (equal w d))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cp-register fn-cp-nth))))

; KEYSTONE (the table stays within the operator's bound).  From a table of
; at most MAX entries, applying the write the served decision proposed --
; or any event that is not a register -- leaves at most MAX.  With the
; upgrade keystone (a profile never lowers field 9) this carries the bound
; across reopen: a table within the old profile's count is within the new.
(defthm fn-cp-apply-preserves-consumer-capacity
  (implies (and (<= (len (fn-cp-nth 5 s)) (nfix max))
                (or (not (eq (fn-cp-nth 0 event) :register))
                    (equal (fn-cp-register-within s max caller consumer
                                                  query qver view)
                           (list :write event))))
           (<= (len (fn-cp-nth 5 (fn-cp-apply s event))) (nfix max)))
  :hints (("Goal" :use ((:instance fn-cp-apply-grows-only-by-a-register)
                        (:instance
                         fn-cp-register-within-refuses-exactly-past-the-operator-bound))
           :in-theory (disable fn-cp-apply fn-cp-register-within
                               fn-cp-register)))
  :rule-classes nil)

(defthm fn-cp-find-remove-absent-id
  (implies (and (fn-cp-idp key) (not (fn-cp-find key entries)))
           (not (fn-cp-find key (fn-cp-remove consumer entries))))
  :hints (("Goal" :induct (fn-cp-remove consumer entries)
           :in-theory (enable fn-cp-remove))))

(defthm fn-cp-entriesp-remove
  (implies (fn-cp-entriesp entries frontier next-epoch)
           (fn-cp-entriesp (fn-cp-remove consumer entries)
                           frontier next-epoch))
  :hints (("Goal" :induct (fn-cp-remove consumer entries)
           :in-theory (enable fn-cp-remove))))

(defthm fn-cp-entriesp-larger-next
  (implies (and (fn-cp-entriesp entries frontier next-epoch)
                (natp next-epoch))
           (fn-cp-entriesp entries frontier (+ 1 next-epoch)))
  :hints (("Goal" :induct (fn-cp-entriesp entries frontier next-epoch))))

(defthm fn-cp-find-after-remove-same
  (implies (fn-cp-entriesp entries frontier next-epoch)
           (not (fn-cp-find consumer (fn-cp-remove consumer entries))))
  :hints (("Goal" :induct (fn-cp-remove consumer entries)
           :in-theory (enable fn-cp-remove))))

(defthm fn-cp-find-consumer-idp
  (implies (and (fn-cp-entriesp entries frontier next-epoch)
                (fn-cp-find consumer entries))
           (fn-cp-idp consumer))
  :hints (("Goal" :induct (fn-cp-find consumer entries))))

(defthm fn-cp-find-principal-idp
  (implies (and (fn-cp-entriesp entries frontier next-epoch)
                (fn-cp-find consumer entries))
           (fn-cp-idp (fn-cp-nth 2 (fn-cp-find consumer entries))))
  :hints (("Goal" :induct (fn-cp-find consumer entries))))

(defthm fn-cp-find-query-idp
  (implies (and (fn-cp-entriesp entries frontier next-epoch)
                (fn-cp-find consumer entries))
           (fn-cp-idp (fn-cp-nth 3 (fn-cp-find consumer entries))))
  :hints (("Goal" :induct (fn-cp-find consumer entries))))

(defthm fn-cp-find-qver-uintp
  (implies (and (fn-cp-entriesp entries frontier next-epoch)
                (fn-cp-find consumer entries))
           (fn-cp-uintp (fn-cp-nth 4 (fn-cp-find consumer entries))))
  :hints (("Goal" :induct (fn-cp-find consumer entries))))

(defthm fn-cp-find-view-uintp
  (implies (and (fn-cp-entriesp entries frontier next-epoch)
                (fn-cp-find consumer entries))
           (fn-cp-uintp (fn-cp-nth 5 (fn-cp-find consumer entries))))
  :hints (("Goal" :induct (fn-cp-find consumer entries))))

(defthm fn-cp-find-epoch-posp
  (implies (and (fn-cp-entriesp entries frontier next-epoch)
                (fn-cp-find consumer entries))
           (posp (fn-cp-nth 6 (fn-cp-find consumer entries))))
  :hints (("Goal" :induct (fn-cp-find consumer entries))))

(defthm fn-cp-find-epoch-less-next
  (implies (and (fn-cp-entriesp entries frontier next-epoch)
                (fn-cp-find consumer entries))
           (< (fn-cp-nth 6 (fn-cp-find consumer entries))
              (nfix next-epoch)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-cp-find consumer entries))))

(defthm fn-cp-find-ack-nonnegative-linear
  (implies (and (fn-cp-entriesp entries frontier next-epoch)
                (fn-cp-find consumer entries))
           (<= 0 (fn-cp-nth 7 (fn-cp-find consumer entries))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-cp-find consumer entries))))

(defthm fn-cp-statep-find-ack-nonnegative
  (implies (and (fn-cp-statep s)
                (fn-cp-find consumer (fn-cp-nth 5 s)))
           (<= 0 (fn-cp-nth 7
                            (fn-cp-find consumer (fn-cp-nth 5 s)))))
  :rule-classes :linear)

(defthm fn-cp-scope-match-implies-entry
  (implies (fn-cp-scope-matchp s caller qver view cursor entry)
           (consp entry))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cp-scope-matchp))))

; This is the invariant over arbitrary committed consumer event traces.
; It says nothing about which events a physical Store has persisted.
(defthm fn-cp-apply-preserves-statep
  (implies (fn-cp-statep s)
           (fn-cp-statep (fn-cp-apply s event)))
  :hints (("Goal" :in-theory (e/d (fn-cp-apply) (fn-cp-idp)))))

(defthm fn-cp-apply-trace-preserves-statep
  (implies (fn-cp-statep s)
           (fn-cp-statep (fn-cp-apply-trace s events)))
  :hints (("Goal" :induct (fn-cp-apply-trace s events)
           :in-theory (disable fn-cp-statep fn-cp-apply))))

; The encoder has a sharper 346-octet bound than the 512-octet decoder
; preflight.  Both bounds are independent of any untrusted list tail.
(defthm fn-cp-u32-bytes-four
  (equal (len (fn-cbor-u32-bytes n)) 4)
  :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes))))

(defthm fn-cp-at-most-length
  (implies (fn-cbor-at-mostp xs bound)
           (<= (len xs) (nfix bound)))
  :hints (("Goal" :induct (fn-cbor-at-mostp xs bound))))

(defthm fn-cp-id-length-bound
  (implies (fn-cp-idp x) (<= (len x) 64))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-cp-at-most-length
                                 (xs x) (bound 64))))))

(defthm fn-cp-len-append
  (equal (len (append x y)) (+ (len x) (len y))))

(defthm fn-cp-cursor-encode-length-bound
  (<= (len (fn-cp-cursor-encode cursor)) 346)
  :hints (("Goal" :cases ((fn-cp-cursorp cursor))
           :in-theory (enable fn-cp-cursor-encode))))

(defthm fn-cp-cursor-decode-overlong-by-definition
  (implies (not (fn-cbor-at-mostp octets *fn-cp-max-token*))
           (equal (fn-cp-cursor-decode octets) (list :refused :octets)))
  :hints (("Goal" :in-theory (enable fn-cp-cursor-decode))))

; Decode-after-encode is proved through one field at a time so the parser
; and its byte codec stay closed in later Store proofs.
(defthm fn-cp-take-append-prefix
  (implies (true-listp x)
           (equal (take (len x) (append x y)) x))
  :hints (("Goal" :induct (len x))))

(defthm fn-cp-nthcdr-append-prefix
  (implies (true-listp x)
           (equal (nthcdr (len x) (append x y)) y))
  :hints (("Goal" :induct (len x))))

(defthm fn-cp-idp-true-listp
  (implies (fn-cp-idp x) (true-listp x)))

(defthm fn-cp-read-id-roundtrip
  (implies (fn-cp-idp id)
           (equal (fn-cp-read-id (append (fn-cp-id-bytes id) rest))
                  (list :ok id rest)))
  :hints (("Goal" :in-theory (enable fn-cp-read-id fn-cp-id-bytes))))

(defthm fn-cp-u32-from-append-prefix
  (implies (fn-cp-uintp n)
           (equal (fn-cbor-u32-from
                   (append (fn-cbor-u32-bytes n) rest)) n))
  :hints (("Goal" :in-theory (enable fn-cbor-u32-from fn-cbor-u32-bytes)
           :use ((:instance fn-cbor-u32-from-u32-bytes (n n))))))

(defthm fn-cp-u32-bytes-true-listp
  (true-listp (fn-cbor-u32-bytes n))
  :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes))))

(defthm fn-cp-u32-nthcdr-append-prefix
  (equal (nthcdr 4 (append (fn-cbor-u32-bytes n) rest)) rest)
  :hints (("Goal" :use ((:instance fn-cp-nthcdr-append-prefix
                                  (x (fn-cbor-u32-bytes n)) (y rest))))))

(defthm fn-cp-read-u32-roundtrip
  (implies (fn-cp-uintp n)
           (equal (fn-cp-read-u32
                   (append (fn-cbor-u32-bytes n) rest))
                  (list :ok n rest)))
  :hints (("Goal" :in-theory (enable fn-cp-read-u32))))

(defthm fn-cp-append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defthm fn-cp-append-nil-left
  (equal (append nil x) x))

(defthm fn-cp-fields-roundtrip
  (implies (fn-cp-fields-validp vals kinds)
           (equal (fn-cp-read-fields
                   (append (fn-cp-fields-encode vals kinds) rest) kinds)
                  (list :ok vals rest)))
  :hints (("Goal" :induct (fn-cp-fields-encode vals kinds)
           :in-theory (e/d (fn-cp-fields-encode fn-cp-fields-validp
                            fn-cp-read-fields)
                           (binary-append fn-cp-id-bytes fn-cp-read-id
                            fn-cp-read-u32 fn-cp-idp fn-cp-uintp)))))

(defthm fn-cp-cursor-encode-fields
  (equal (fn-cp-cursor-encode c)
         (if (fn-cp-cursorp c)
             (append *fn-cp-magic* (list *fn-cp-version*)
                     (fn-cp-fields-encode
                      (list (fn-cp-nth 1 c) (fn-cp-nth 2 c)
                            (fn-cp-nth 3 c) (fn-cp-nth 4 c)
                            (fn-cp-nth 5 c) (fn-cp-nth 6 c)
                            (fn-cp-nth 7 c) (fn-cp-nth 8 c)
                            (fn-cp-nth 9 c))
                      '(:id :id :id :id :id :uint :uint :uint :uint)))
           nil))
  :hints (("Goal" :in-theory (e/d (fn-cp-cursor-encode
                                   fn-cp-fields-encode)
                                  (binary-append)))))

(defthm fn-cp-cursor-fields-valid
  (implies (fn-cp-cursorp c)
           (fn-cp-fields-validp
            (list (fn-cp-nth 1 c) (fn-cp-nth 2 c)
                  (fn-cp-nth 3 c) (fn-cp-nth 4 c)
                  (fn-cp-nth 5 c) (fn-cp-nth 6 c)
                  (fn-cp-nth 7 c) (fn-cp-nth 8 c)
                  (fn-cp-nth 9 c))
            '(:id :id :id :id :id :uint :uint :uint :uint))))

(defthm fn-cp-id-bytes-octets
  (implies (fn-cp-idp id)
           (fn-cbor-octet-listp (fn-cp-id-bytes id)))
  :hints (("Goal" :in-theory (enable fn-cp-id-bytes
                                     fn-cbor-octet-listp
                                     fn-cbor-octetp))))

(defthm fn-cp-cursor-encode-octets
  (implies (fn-cp-cursorp c)
           (fn-cbor-octet-listp (fn-cp-cursor-encode c)))
  :hints (("Goal" :in-theory
           (e/d (fn-cp-cursor-encode fn-cbor-octet-listp-append
                 fn-cbor-octet-listp-implies-true-listp
                 fn-cbor-u32-bytes-are-octets)
                (fn-cbor-octet-listp binary-append fn-cp-id-bytes)))))

(defthm fn-cp-cursor-encode-passes-preflight
  (implies (fn-cp-cursorp c)
           (fn-cbor-at-mostp (fn-cp-cursor-encode c)
                             *fn-cp-max-token*))
  :hints (("Goal" :use ((:instance fn-cbor-at-mostp-from-length
                                  (xs (fn-cp-cursor-encode c))
                                  (bound *fn-cp-max-token*)))
           :in-theory (enable fn-cbor-octet-listp-implies-true-listp))))

(defthm fn-cp-cursor-encode-header
  (implies (fn-cp-cursorp c)
           (and (equal (take 4 (fn-cp-cursor-encode c)) *fn-cp-magic*)
                (equal (fn-cp-nth 4 (fn-cp-cursor-encode c))
                       *fn-cp-version*)))
  :hints (("Goal" :in-theory (enable fn-cp-cursor-encode))))

(defthm fn-cp-cursor-encode-fields-read
  (implies (fn-cp-cursorp c)
           (equal (fn-cp-read-fields
                   (nthcdr 5 (fn-cp-cursor-encode c))
                   '(:id :id :id :id :id :uint :uint :uint :uint))
                  (list :ok
                        (list (fn-cp-nth 1 c) (fn-cp-nth 2 c)
                              (fn-cp-nth 3 c) (fn-cp-nth 4 c)
                              (fn-cp-nth 5 c) (fn-cp-nth 6 c)
                              (fn-cp-nth 7 c) (fn-cp-nth 8 c)
                              (fn-cp-nth 9 c))
                        nil)))
  :hints (("Goal" :in-theory
           (disable fn-cp-cursorp fn-cp-read-fields fn-cp-fields-encode
                    fn-cp-idp fn-cp-uintp)
           :use ((:instance fn-cp-fields-roundtrip
                            (vals (list (fn-cp-nth 1 c) (fn-cp-nth 2 c)
                                        (fn-cp-nth 3 c) (fn-cp-nth 4 c)
                                        (fn-cp-nth 5 c) (fn-cp-nth 6 c)
                                        (fn-cp-nth 7 c) (fn-cp-nth 8 c)
                                        (fn-cp-nth 9 c)))
                            (kinds '(:id :id :id :id :id
                                     :uint :uint :uint :uint))
                            (rest nil))))))

(defthm fn-cp-nths-ten-equal-take
  (equal (list (fn-cp-nth 0 x) (fn-cp-nth 1 x)
               (fn-cp-nth 2 x) (fn-cp-nth 3 x)
               (fn-cp-nth 4 x) (fn-cp-nth 5 x)
               (fn-cp-nth 6 x) (fn-cp-nth 7 x)
               (fn-cp-nth 8 x) (fn-cp-nth 9 x))
         (take 10 x))
  :hints (("Goal" :in-theory (enable fn-cp-nth)
           :expand ((take 10 x) (take 9 (cdr x))
                    (take 8 (cddr x)) (take 7 (cdddr x))
                    (take 6 (cddddr x))
                    (take 5 (cdr (cddddr x)))
                    (take 4 (cddr (cddddr x)))
                    (take 3 (cdddr (cddddr x)))
                    (take 2 (cddddr (cddddr x)))
                    (take 1 (cdr (cddddr (cddddr x))))))))

(defthm fn-cp-cursor-rebuild
  (implies (fn-cp-cursorp c)
           (equal (fn-cp-cursor
                   (fn-cp-nth 1 c) (fn-cp-nth 2 c) (fn-cp-nth 3 c)
                   (fn-cp-nth 4 c) (fn-cp-nth 5 c) (fn-cp-nth 6 c)
                   (fn-cp-nth 7 c) (fn-cp-nth 8 c) (fn-cp-nth 9 c))
                  c))
  :hints (("Goal" :in-theory
           (disable fn-cp-nth fn-cp-idp fn-cp-uintp
                    fn-cp-nths-ten-equal-take)
           :use ((:instance fn-cp-nths-ten-equal-take (x c))
                 (:instance fn-cbor-take-whole-list (xs c))))))

(defthm fn-cp-cursor-decode-encode-roundtrip
  (implies (fn-cp-cursorp c)
           (equal (fn-cp-cursor-decode (fn-cp-cursor-encode c))
                  (list :ok c)))
  :hints (("Goal" :in-theory
           (e/d (fn-cp-cursor-decode)
                (fn-cp-cursorp fn-cp-cursor-encode
                 fn-cp-cursor-encode-fields
                 fn-cp-read-fields fn-cp-fields-encode
                 fn-cp-idp fn-cp-uintp fn-cp-cursor binary-append
                 nthcdr take fn-cbor-at-mostp
                 fn-cbor-octet-listp)))))

; The codec and decision internals are opened only by a caller's focused
; proof.  Importing this leaf must not expand its parser in every later goal.
(in-theory (disable (:d fn-cp-cursor-encode) (:d fn-cp-cursor-decode)
                    (:d fn-cp-register) (:d fn-cp-ack)
                    (:d fn-cp-rebase) (:d fn-cp-unregister)
                    (:d fn-cp-apply) (:d fn-cp-scope-matchp)))
