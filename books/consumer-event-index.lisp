; Rebuildable sequence index for the Store's exact committed event list.
; The index contains references to the authoritative event objects, not a
; second journal or an admission decision.  Four octets of the uint32 Store
; sequence choose a fixed-depth radix path.  Every branch has at most 256
; octet keys plus one terminal key, so lookup and extension have a constant
; bound independent of the acknowledged prefix length.
;
; Since 2026-09-26 (lane signed-history-index, PRF-144 part 1) the index is a
; pair: the sequence trie above, and a Message-ID trie from each Message-ID
; to the article records the history commits under it, in history order --
; a plain article record, and the record a signed kind-4 composite carries,
; decoded once when the event is added (`fn-cei-event-article').  Both halves
; are extended by the same `fn-cei-put', so the index the Store carries in
; its derived field (`fn-sn-event-index', extended at `fn-sn-io''s record
; directory append and built by every open) answers a Message-ID with the
; exact fold over the history, `fn-cei-article-records-for', under the
; correspondence the Store already maintains (`fn-cei-correspondencep';
; `fn-cei-msgid-records-of-correspondence').  A lookup walks the Message-ID
; by string index down a character trie: its work is bounded by the
; Message-ID and the per-node branching, not by the history.
;
; Since 2026-09-26 (lane hot-path-scans-2, PRF-180) the index also carries
; the number of events put into it, so it is a triple
; (SEQUENCE-TRIE MSGID-TRIE . COUNT).  `fn-cei-put' adds one; the built index
; of a history holds that history's length (`fn-cei-count-of-build'), so
; under the correspondence the Store maintains the count is the committed
; record count (`fn-cei-count-of-correspondence') and the served owner reads
; it in constant time instead of taking `len' of the history.
(in-package "ACL2")
(include-book "consumer-position")
(include-book "replay")
(include-book "msgid-index-concrete")

(defconst *fn-cei-value-key* :fn-cei-value)

(defun fn-cei-branch-get (key branches)
  (declare (xargs :guard t))
  (if (consp branches)
      (if (equal key (fn-cbor-ag-car (fn-cbor-ag-car branches)))
          (fn-cbor-ag-cdr (fn-cbor-ag-car branches))
        (fn-cei-branch-get key (fn-cbor-ag-cdr branches)))
    nil))

(defun fn-cei-branch-put (key value branches)
  (declare (xargs :guard t))
  (if (consp branches)
      (if (equal key (fn-cbor-ag-car (fn-cbor-ag-car branches)))
          (cons (cons key value) (fn-cbor-ag-cdr branches))
        (cons (fn-cbor-ag-car branches)
              (fn-cei-branch-put key value (fn-cbor-ag-cdr branches))))
    (list (cons key value))))

(defun fn-cei-put-digits (digits event trie)
  (declare (xargs :guard t))
  (if (consp digits)
      (fn-cei-branch-put
       (car digits)
       (fn-cei-put-digits
        (cdr digits) event (fn-cei-branch-get (car digits) trie))
       trie)
    (fn-cei-branch-put *fn-cei-value-key* event trie)))

(defun fn-cei-get-digits (digits trie)
  (declare (xargs :guard t))
  (if (consp digits)
      (fn-cei-get-digits
       (cdr digits) (fn-cei-branch-get (car digits) trie))
    (fn-cei-branch-get *fn-cei-value-key* trie)))

; The article record a Store event commits: a plain article record is its
; own; a signed acceptance composite (kind 4) commits the record it carries,
; decoded as replay decodes it (`fn-replay-composite-record').  Every other
; event maps to itself, which is never `fn-record-p'.  The same body as
; books/bp-receipt.lisp's `fn-bpr-event-article' (equal by
; `fn-bpaj-event-article-is-cei', books/bp-native-app.lisp).
(defun fn-cei-event-article (event)
  (declare (xargs :guard t))
  (if (fn-stxa-p event) (fn-replay-composite-record event) event))

; The specification of the Message-ID half: the article records of EVENTS
; whose Message-ID is MSGID, in history order.
(defun fn-cei-article-records-for (msgid events)
  (declare (xargs :guard t))
  (if (consp events)
      (let ((rest (fn-cei-article-records-for msgid (cdr events)))
            (record (fn-cei-event-article (car events))))
        (if (and (fn-record-p record)
                 (equal msgid (fn-record-msgid record)))
            (cons record rest)
          rest))
    nil))

(defun fn-cei-snoc (xs x)
  (declare (xargs :guard t))
  (if (consp xs) (cons (car xs) (fn-cei-snoc (cdr xs) x)) (list x)))

(defun fn-cei-sequence-trie (index)
  (declare (xargs :guard t))
  (if (consp index) (car index) nil))

(defun fn-cei-msgid-trie (index)
  (declare (xargs :guard t))
  (if (and (consp index) (consp (cdr index))) (cadr index) nil))

; The number of events put into INDEX (0 for the empty index).
(defun fn-cei-count (index)
  (declare (xargs :guard t))
  (if (and (consp index) (consp (cdr index)) (natp (cddr index)))
      (cddr index)
    0))

; A Message-ID's list in the trie: the walk by string index, no allocation.
; The index only ever stores true lists; the test makes that a type.
(defun fn-cei-trie-records (msgid trie)
  (declare (xargs :guard t))
  (let ((value (fn-mxc-lookup msgid trie)))
    (if (true-listp value) value nil)))

(defun fn-cei-msgid-records (msgid index)
  (declare (xargs :guard t))
  (fn-cei-trie-records msgid (fn-cei-msgid-trie index)))

; Adding one event: its article record, if it has one with a string
; Message-ID, is appended to that Message-ID's list.
(defun fn-cei-msgid-add (event trie)
  (declare (xargs :guard t))
  (let ((record (fn-cei-event-article event)))
    (if (and (fn-record-p record) (stringp (fn-record-msgid record)))
        (fn-midx-put-chars
         (coerce (fn-record-msgid record) 'list)
         (fn-cei-snoc (fn-cei-trie-records (fn-record-msgid record) trie)
                      record)
         trie)
      trie)))

(defun fn-cei-put (sequence event index)
  (declare (xargs :guard t))
  (list* (if (fn-cp-uintp sequence)
             (fn-cei-put-digits (fn-cbor-u32-bytes sequence) event
                                (fn-cei-sequence-trie index))
           (fn-cei-sequence-trie index))
         (fn-cei-msgid-add event (fn-cei-msgid-trie index))
         (1+ (fn-cei-count index))))

(defun fn-cei-get (sequence index)
  (declare (xargs :guard t))
  (if (fn-cp-uintp sequence)
      (fn-cei-get-digits (fn-cbor-u32-bytes sequence)
                         (fn-cei-sequence-trie index))
    nil))

; Executed only during observed open/recovery, not during a served poll.
(defun fn-cei-build-aux (events sequence index)
  (declare (xargs :guard (natp sequence)))
  (if (consp events)
      (fn-cei-build-aux (cdr events) (1+ sequence)
                        (fn-cei-put sequence (car events) index))
    index))

(defun fn-cei-build (events)
  (declare (xargs :guard t))
  (fn-cei-build-aux events 0 nil))

(defun fn-cei-correspondencep (index events)
  (declare (xargs :guard t :verify-guards nil))
  (equal index (fn-cei-build events)))

(defthm fn-cei-branch-get-of-put
  (equal (fn-cei-branch-get wanted
                            (fn-cei-branch-put key value branches))
         (if (equal wanted key) value
           (fn-cei-branch-get wanted branches))))

(defthm fn-cei-get-digits-of-put-other-branch
  (implies (and (consp wanted) (not (equal (car wanted) key)))
           (equal (fn-cei-get-digits wanted
                                     (fn-cei-branch-put key value trie))
                  (fn-cei-get-digits wanted trie))))

(defthm fn-cei-get-digits-of-put-same-branch
  (equal (fn-cei-get-digits (cons key rest)
                            (fn-cei-branch-put key value trie))
         (fn-cei-get-digits rest value)))

(defthm fn-cei-octet-is-not-value-key
  (implies (and (integerp octet) (<= 0 octet) (< octet 256))
           (not (equal octet *fn-cei-value-key*))))

(defthm fn-cei-value-of-put-octet
  (implies (and (integerp octet) (<= 0 octet) (< octet 256))
           (equal (fn-cei-branch-get
                   *fn-cei-value-key*
                   (fn-cei-branch-put octet value trie))
                  (fn-cei-branch-get *fn-cei-value-key* trie))))

(defthm fn-cei-get-digits-of-put-value
  (implies (and (consp wanted) (fn-cbor-octet-listp wanted))
           (equal (fn-cei-get-digits
                   wanted (fn-cei-branch-put *fn-cei-value-key* value trie))
                  (fn-cei-get-digits wanted trie))))

(defun fn-cei-lookup-put-induct (wanted digits event trie)
  (declare (xargs :guard t))
  (if (and (consp wanted) (consp digits)
           (equal (car wanted) (car digits)))
      (fn-cei-lookup-put-induct
       (cdr wanted) (cdr digits) event
       (fn-cei-branch-get (car digits) trie))
    (list wanted digits event trie)))

(defthm fn-cei-get-digits-of-put-digits
  (implies (and (fn-cbor-octet-listp wanted)
                (fn-cbor-octet-listp digits))
           (equal (fn-cei-get-digits wanted
                                     (fn-cei-put-digits digits event trie))
                  (if (equal wanted digits) event
                    (fn-cei-get-digits wanted trie))))
  :hints (("Goal" :induct (fn-cei-lookup-put-induct wanted digits event trie)
           :in-theory (disable fn-cei-branch-get fn-cei-branch-put))))

(defthm fn-cei-u32-key-injective
  (implies (and (fn-cp-uintp a) (fn-cp-uintp b))
           (equal (equal (fn-cbor-u32-bytes a)
                         (fn-cbor-u32-bytes b))
                  (equal a b)))
  :hints (("Goal" :use ((:instance fn-cbor-u32-from-u32-bytes (n a))
                         (:instance fn-cbor-u32-from-u32-bytes (n b))))))

(defthm fn-cei-get-of-put
  (implies (and (fn-cp-uintp wanted) (fn-cp-uintp sequence))
           (equal (fn-cei-get wanted
                              (fn-cei-put sequence event index))
                  (if (equal wanted sequence) event
                    (fn-cei-get wanted index))))
  :hints (("Goal"
           :use ((:instance fn-cei-get-digits-of-put-digits
                            (wanted (fn-cbor-u32-bytes wanted))
                            (digits (fn-cbor-u32-bytes sequence))
                            (trie (fn-cei-sequence-trie index)))
                 (:instance fn-cei-u32-key-injective
                            (a wanted) (b sequence)))
           :in-theory (e/d (fn-cei-get fn-cei-put fn-cei-sequence-trie)
                           (fn-cei-get-digits-of-put-digits
                            fn-cei-u32-key-injective)))))

; The recursive build is deliberately a one-time recovery operation.  This
; extension theorem is the maintenance fact needed by Store completion.
(defthm fn-cei-build-aux-append-one
  (implies (natp sequence)
           (equal (fn-cei-build-aux (append events (list event)) sequence index)
                  (fn-cei-put (+ sequence (len events)) event
                              (fn-cei-build-aux events sequence index))))
  ; fn-cei-put stays closed: the step is the same put on both sides, and
  ; opened it unfolds the composite decoder of the Message-ID half (91.9 s,
  ; 74.7 million steps; 2026-09-26 persvati REPL).
  :hints (("Goal" :induct (fn-cei-build-aux events sequence index)
           :in-theory (disable fn-cei-put))))

(defthm fn-cei-extend-preserves-correspondence
  (implies (fn-cei-correspondencep index events)
           (fn-cei-correspondencep
            (fn-cei-put (len events) event index)
            (append events (list event))))
  :hints (("Goal" :in-theory (enable fn-cei-correspondencep fn-cei-build))))

;; ---------------------------------------------------------------------------
;; The count (PRF-180).

(defthm fn-cei-count-is-natural
  (natp (fn-cei-count index))
  :rule-classes :type-prescription)

(defthm fn-cei-count-of-put
  (equal (fn-cei-count (fn-cei-put sequence event index))
         (1+ (fn-cei-count index)))
  :hints (("Goal" :in-theory (e/d (fn-cei-count fn-cei-put)
                                  (fn-cei-msgid-add fn-cei-put-digits)))))

(defthm fn-cei-count-of-build-aux
  (equal (fn-cei-count (fn-cei-build-aux events sequence index))
         (+ (fn-cei-count index) (len events)))
  :hints (("Goal" :induct (fn-cei-build-aux events sequence index)
           :in-theory (disable fn-cei-put fn-cei-count))))

(defthm fn-cei-count-of-build
  (equal (fn-cei-count (fn-cei-build events)) (len events))
  :hints (("Goal" :in-theory (e/d (fn-cei-build) (fn-cei-build-aux)))))

; KEYSTONE (PRF-180, the count half): under the correspondence the Store
; carries for its derived index, the index's count is the length of the
; committed history.  No other hypothesis: every put counts, so the built
; index of any list holds its length.
(defthm fn-cei-count-of-correspondence
  (implies (fn-cei-correspondencep index events)
           (equal (fn-cei-count index) (len events)))
  :hints (("Goal" :in-theory (e/d (fn-cei-correspondencep)
                                  (fn-cei-build fn-cei-count)))))

; The journal sequence is its zero-based position in the dense committed
; Store record list.  This is the exact correspondence used by the poll
; selector; an index-only matching value cannot satisfy this theorem.
(defthm fn-cei-get-of-build-aux
  (implies (and (true-listp events) (natp sequence)
                (fn-cp-uintp wanted)
                (<= (+ sequence (len events))
                    (1+ *fn-cbor-max-uint*)))
           (equal (fn-cei-get wanted
                              (fn-cei-build-aux events sequence index))
                  (if (and (<= sequence wanted)
                           (< wanted (+ sequence (len events))))
                      (nth (- wanted sequence) events)
                    (fn-cei-get wanted index))))
  :hints (("Goal" :induct (fn-cei-build-aux events sequence index)
           :in-theory (disable fn-cei-get fn-cei-put fn-cei-get-digits
                               fn-cei-put-digits fn-cei-branch-get
                               fn-cei-branch-put))))

(defthm fn-cei-get-digits-of-nil
  (equal (fn-cei-get-digits digits nil) nil)
  :hints (("Goal" :induct (fn-cei-get-digits digits nil)
           :in-theory (enable fn-cei-get-digits fn-cei-branch-get))))

(defthm fn-cei-get-of-nil
  (equal (fn-cei-get sequence nil) nil)
  :hints (("Goal" :in-theory (enable fn-cei-get))))

(defthm fn-cei-get-of-build-is-committed-event
  (implies (and (true-listp events)
                (<= (len events) (1+ *fn-cbor-max-uint*))
                (fn-cp-uintp sequence))
           (equal (fn-cei-get sequence (fn-cei-build events))
                  (if (< sequence (len events))
                      (nth sequence events)
                    nil)))
  :hints (("Goal" :use ((:instance fn-cei-get-of-build-aux
                                  (wanted sequence) (sequence 0)
                                  (index nil)))
           :in-theory (e/d (fn-cei-build)
                           (fn-cei-get-of-build-aux fn-cei-get
                            fn-cei-get-digits fn-cei-put-digits
                            fn-cei-branch-get fn-cei-branch-put)))))

(defthm fn-cei-correspondence-lookup
  (implies (and (fn-cei-correspondencep index events)
                (true-listp events)
                (<= (len events) (1+ *fn-cbor-max-uint*))
                (fn-cp-uintp sequence)
                (< sequence (len events)))
           (equal (fn-cei-get sequence index)
                  (nth sequence events)))
  :hints (("Goal"
           :use ((:instance fn-cei-get-of-build-is-committed-event
                            (sequence sequence)))
           :in-theory (e/d (fn-cei-correspondencep)
                           (fn-cei-get-of-build-is-committed-event
                            fn-cei-get fn-cei-build fn-cei-build-aux
                            fn-cei-get-digits fn-cei-put-digits
                            fn-cei-branch-get fn-cei-branch-put)))))

;; ---------------------------------------------------------------------------
;; The Message-ID half (PRF-144 part 1).  The record codec and the composite
;; decoder stay closed: nothing here looks inside an article record.

(local (in-theory (disable fn-record-p fn-cei-event-article
                           fn-replay-composite-record fn-stxa-p
                           fn-record-msgid)))

(defthm fn-cei-snoc-is-append-one
  (implies (true-listp xs)
           (equal (fn-cei-snoc xs x) (append xs (list x)))))

(defthm fn-cei-snoc-is-true-list
  (true-listp (fn-cei-snoc xs x)))

(defthm fn-cei-msgid-records-is-a-true-list
  (true-listp (fn-cei-msgid-records msgid index))
  :rule-classes :type-prescription)

(defthm fn-cei-msgid-records-of-put
  (implies (stringp msgid)
           (equal (fn-cei-msgid-records msgid (fn-cei-put sequence event index))
                  (let ((record (fn-cei-event-article event)))
                    (if (and (fn-record-p record)
                             (equal msgid (fn-record-msgid record)))
                        (fn-cei-snoc (fn-cei-msgid-records msgid index) record)
                      (fn-cei-msgid-records msgid index)))))
  :hints (("Goal"
           :use ((:instance fn-midx-string-list-coercion-injective
                            (a msgid)
                            (b (fn-record-msgid
                                (fn-cei-event-article event)))))
           :in-theory (e/d (fn-cei-msgid-records fn-cei-put fn-cei-msgid-add
                            fn-cei-msgid-trie fn-cei-trie-records
                            fn-midx-lookup fn-midx-key-chars)
                           (fn-cei-snoc fn-cei-snoc-is-append-one
                            fn-midx-put-chars fn-midx-get-chars
                            fn-midx-string-list-coercion-injective)))))

(defthm fn-cei-msgid-records-of-build-aux
  (implies (and (stringp msgid)
                (true-listp (fn-cei-msgid-records msgid index)))
           (equal (fn-cei-msgid-records msgid
                                        (fn-cei-build-aux events sequence index))
                  (append (fn-cei-msgid-records msgid index)
                          (fn-cei-article-records-for msgid events))))
  :hints (("Goal" :induct (fn-cei-build-aux events sequence index)
           :in-theory (e/d (fn-cei-build-aux fn-cei-article-records-for)
                           (fn-cei-msgid-records fn-cei-put)))))

; The Message-ID half of the built index is the fold over the history.
(defthm fn-cei-msgid-records-of-build
  (implies (stringp msgid)
           (equal (fn-cei-msgid-records msgid (fn-cei-build events))
                  (fn-cei-article-records-for msgid events)))
  :hints (("Goal" :use ((:instance fn-cei-msgid-records-of-build-aux
                                   (sequence 0) (index nil)))
           :in-theory (e/d (fn-cei-build fn-cei-msgid-records
                            fn-cei-msgid-trie fn-cei-trie-records)
                           (fn-cei-msgid-records-of-build-aux
                            fn-cei-build-aux)))))

; KEYSTONE (PRF-144 part 1, the index half): under the correspondence the
; Store carries for its derived index, a Message-ID lookup in the index is
; the fold over the committed history.  Established at every open (each
; open installs `fn-cei-build' of the history it read) and preserved by every
; Store transition (books/consumer-event-index-store-invariants.lisp); the
; one transition that grows the history, `fn-sn-io''s record-directory
; append, extends the index by `fn-cei-put' of the appended event
; (`fn-cei-extend-preserves-correspondence').
(defthm fn-cei-msgid-records-of-correspondence
  (implies (and (stringp msgid)
                (fn-cei-correspondencep index events))
           (equal (fn-cei-msgid-records msgid index)
                  (fn-cei-article-records-for msgid events)))
  :hints (("Goal" :in-theory (e/d (fn-cei-correspondencep)
                                  (fn-cei-msgid-records fn-cei-build)))))

(verify-guards fn-cei-build-aux)
(verify-guards fn-cei-build)

; Exported closed: every Store book that carries the index across a
; transition treats fn-cei-put as one opaque step (they already disabled it
; by name), and opened it now unfolds the composite decoder of the
; Message-ID half.
(in-theory (disable fn-cei-put fn-cei-event-article fn-cei-msgid-add
                    fn-cei-count))
