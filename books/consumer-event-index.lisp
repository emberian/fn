; Rebuildable sequence index for the Store's exact committed event list.
; The index contains references to the authoritative event objects, not a
; second journal or an admission decision.  Four octets of the uint32 Store
; sequence choose a fixed-depth radix path.  Every branch has at most 256
; octet keys plus one terminal key, so lookup and extension have a constant
; bound independent of the acknowledged prefix length.
(in-package "ACL2")
(include-book "consumer-position")

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

(defun fn-cei-put (sequence event index)
  (declare (xargs :guard (fn-cp-uintp sequence)))
  (fn-cei-put-digits (fn-cbor-u32-bytes sequence) event index))

(defun fn-cei-get (sequence index)
  (declare (xargs :guard (fn-cp-uintp sequence)))
  (fn-cei-get-digits (fn-cbor-u32-bytes sequence) index))

; Executed only during observed open/recovery, not during a served poll.
(defun fn-cei-build-aux (events sequence index)
  (declare (xargs :guard (and (true-listp events) (natp sequence)
                              (<= (+ sequence (len events))
                                  (1+ *fn-cbor-max-uint*)))
                  :verify-guards nil))
  (if (consp events)
      (fn-cei-build-aux (cdr events) (1+ sequence)
                        (fn-cei-put sequence (car events) index))
    index))

(defun fn-cei-build (events)
  (declare (xargs :guard (and (true-listp events)
                              (<= (len events) (1+ *fn-cbor-max-uint*)))
                  :verify-guards nil))
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
                            (trie index))
                 (:instance fn-cei-u32-key-injective
                            (a wanted) (b sequence)))
           :in-theory (e/d (fn-cei-get fn-cei-put)
                           (fn-cei-get-digits-of-put-digits
                            fn-cei-u32-key-injective)))))

; The recursive build is deliberately a one-time recovery operation.  This
; extension theorem is the maintenance fact needed by Store completion.
(defthm fn-cei-build-aux-append-one
  (implies (natp sequence)
           (equal (fn-cei-build-aux (append events (list event)) sequence index)
                  (fn-cei-put (+ sequence (len events)) event
                              (fn-cei-build-aux events sequence index))))
  :hints (("Goal" :induct (fn-cei-build-aux events sequence index))))

(defthm fn-cei-extend-preserves-correspondence
  (implies (fn-cei-correspondencep index events)
           (fn-cei-correspondencep
            (fn-cei-put (len events) event index)
            (append events (list event))))
  :hints (("Goal" :in-theory (enable fn-cei-correspondencep fn-cei-build))))

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

(verify-guards fn-cei-build-aux)
(verify-guards fn-cei-build)
