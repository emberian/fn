; fn: a Store event's kind and fields, read once it is recognized.
;
; The dispatchers of books/store-events.lisp (fn-store-event-kind, -sequence,
; -txid, -generation) have guard t, so each call decides the event's kind by
; running the recognizers in order: fn-record-p walks the article payload,
; fn-stxa-p walks the composite's record and authored source.  A caller that
; already knows it holds a Store event paid that walk again for every field
; it read.  On the signed POST the dispatchers were 14.5 percent of the
; owner's CPU and the recognizers about 60 percent in all
; (planning/evidence/signed-path-2026-09-25.md sections 2 and 5).
;
; Under fn-store-event-p the kind is fixed by the event's shape, and the
; shape is O(1) to read:
;
;   head :retention         a retention event, fields at 2 3 4
;   head :consumer          a consumer event,  fields at 1 2 3
;   head another symbol     a topic event,     fields at 1 2 3
;   head a number           an article record (11 wide), a statement verdict
;                           (8), a keyring snapshot (6) or an accepted-article
;                           composite (10); fields at 0 1 2
;
; The -by-shape functions below read exactly that and look at no field's
; contents.  Each KEYSTONE says the reading equals the reference dispatcher
; on every recognized event; the test book shows each needs its hypothesis
; (a list shaped like a composite whose field is not an octet is not a Store
; event, and there the reference answers nil while the shape reads a field).
;
; The carried accessors are the references in the logic, so every theorem
; about a caller survives the substitution unchanged, and the by-shape
; readings in execution; their guard is the carried fact (fn-store-event-p),
; and guard verification is where the keystones are used.  A caller calls
; them only where it holds that fact: books/owner-commit-carried.lisp, whose
; history records are Store events under fn-sn-statep (fn-sf-record-valuesp).

(in-package "ACL2")
(include-book "store-events")

; -----------------------------------------------------------------------------
; The readings by shape.  O(1): at most ten conses are stepped, and no field's
; contents are looked at beyond the head's being a symbol.

; The conses after the first N, stepped totally.
(defun fn-evc-drop (n x)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) x (fn-evc-drop (1- n) (if (consp x) (cdr x) nil))))

; Field N (0 sequence, 1 txid, 2 generation) of a Store event.
(defun fn-evc-field-by-shape (n x)
  (declare (xargs :guard (natp n)))
  (if (not (consp x)) nil
    (let ((head (car x)))
      (cond ((eq head :retention) (fn-store-event-nth (+ 2 n) x))
            ((symbolp head) (fn-store-event-nth (+ 1 n) x))
            (t (fn-store-event-nth n x))))))

(defun fn-evc-class-by-shape (x)
  (declare (xargs :guard t))
  (if (not (consp x)) nil
    (let ((head (car x)))
      (cond ((eq head :retention) :retention)
            ((eq head :consumer) :consumer)
            ((symbolp head) :topic)
            ((not (consp (fn-evc-drop 6 x))) :stxk)
            ((not (consp (fn-evc-drop 8 x))) :stxe)
            ((not (consp (fn-evc-drop 10 x))) :stxa)
            (t :record)))))
; -----------------------------------------------------------------------------
; Shape facts of each recognizer, read off its own conjuncts: the head, and
; for the four numbered kinds the width.  No field predicate is opened.

(local
 (defthm fn-evc-consp-drop
   (implies (natp n)
            (iff (consp (fn-evc-drop n x)) (< n (len x))))
   :hints (("Goal" :induct (fn-evc-drop n x)
            :in-theory (union-theories '(fn-evc-drop len)
                                       (theory 'ground-zero))))))
(local
 (defthm fn-evc-record-shape
   (implies (fn-record-p x)
            (and (consp x) (natp (car x)) (equal (len x) 11)
                 (equal (fn-record-sequence x) (fn-store-event-nth 0 x))
                 (equal (fn-record-txid x) (fn-store-event-nth 1 x))
                 (equal (fn-record-generation x) (fn-store-event-nth 2 x))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory '(fn-record-p fn-record-shapep fn-record-uint32p
                                fn-record-sequence fn-record-txid
                                fn-record-generation fn-store-event-nth
                                zp natp len nfix fix
                                (:executable-counterpart zp)
                                (:executable-counterpart not)
                                (:executable-counterpart binary-+)
                                (:executable-counterpart unary--))))))
(local
 (defthm fn-evc-stxe-shape
   (implies (fn-stxe-p x)
            (and (consp x) (natp (car x)) (equal (len x) 8)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory '(fn-stxe-p fn-stxe-shapep fn-record-uint32p
                                fn-stxe-sequence natp len)))))
(local
 (defthm fn-evc-stxk-shape
   (implies (fn-stxk-p x)
            (and (consp x) (natp (car x)) (equal (len x) 6)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory '(fn-stxk-p fn-stxk-shapep fn-record-uint32p
                                fn-stxk-sequence natp len)))))
(local
 (defthm fn-evc-stxa-shape
   (implies (fn-stxa-p x)
            (and (consp x) (natp (car x)) (equal (len x) 10)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory '(fn-stxa-p fn-stxa-shapep fn-record-uint32p
                                fn-stxa-sequence natp len)))))
(local
 (defthm fn-evc-retention-shape
   (implies (fn-store-retention-event-p x)
            (and (consp x) (equal (car x) :retention)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory '(fn-store-retention-event-p fn-store-event-nth
                                zp (:executable-counterpart zp))))))
(local
 (defthm fn-evc-consumer-shape
   (implies (fn-cpe-eventp x)
            (and (consp x) (equal (car x) :consumer)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory '(fn-cpe-eventp fn-cp-nth
                                zp (:executable-counterpart zp))))))
(local
 (defthm fn-evc-topic-shape
   (implies (fn-th-topic-eventp x)
            (and (consp x) (symbolp (car x))
                 (not (equal (car x) :retention))
                 (not (equal (car x) :consumer))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory '(fn-th-topic-eventp fn-th-local-admin-eventp
                                fn-th-at zp (:executable-counterpart zp))))))
(local
 (defthm fn-evc-event-nth-of-atom
   (implies (not (consp x)) (equal (fn-store-event-nth n x) nil))
   :hints (("Goal" :induct (fn-store-event-nth n x)
            :in-theory (union-theories '(fn-store-event-nth)
                                       (theory 'ground-zero))))))
(local
 (defthm fn-evc-cp-nth-is-event-nth
   (equal (fn-cp-nth n x) (fn-store-event-nth n x))
   :hints (("Goal" :induct (fn-cp-nth n x)
            :in-theory (union-theories '(fn-cp-nth fn-store-event-nth
                                         fn-evc-event-nth-of-atom)
                                       (theory 'ground-zero))))))
(local
 (defthm fn-evc-th-at-is-event-nth
   (equal (fn-th-at n x) (fn-store-event-nth n x))
   :hints (("Goal" :induct (fn-th-at n x)
            :in-theory (union-theories '(fn-th-at fn-store-event-nth
                                         fn-evc-event-nth-of-atom)
                                       (theory 'ground-zero))))))

; -----------------------------------------------------------------------------
; KEYSTONES.  On every Store event the readings by shape are the references.
; The hypothesis is needed: tests/acl2/store-events-carried-tests.lisp has a
; list shaped like a composite that is not a Store event, where each
; reference answers nil (or another kind) and the shape reads a field.

(defthm fn-evc-field-by-shape-is-store-event-sequence
  (implies (fn-store-event-p x)
           (equal (fn-evc-field-by-shape 0 x) (fn-store-event-sequence x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-store-event-p fn-store-event-sequence
                                fn-evc-field-by-shape fn-store-event-nth
                                fn-record-sequence fn-stxe-sequence fn-stxk-sequence fn-stxa-sequence
                                fn-cpe-sequence fn-evc-cp-nth-is-event-nth fn-evc-th-at-is-event-nth
                                fn-evc-record-shape fn-evc-stxe-shape
                                fn-evc-stxk-shape fn-evc-stxa-shape
                                fn-evc-retention-shape fn-evc-consumer-shape
                                fn-evc-topic-shape zp)
                              (theory 'ground-zero)))))
(defthm fn-evc-field-by-shape-is-store-event-txid
  (implies (fn-store-event-p x)
           (equal (fn-evc-field-by-shape 1 x) (fn-store-event-txid x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-store-event-p fn-store-event-txid
                                fn-evc-field-by-shape fn-store-event-nth
                                fn-record-txid fn-stxe-txid fn-stxk-txid fn-stxa-txid
                                fn-cpe-txid fn-evc-cp-nth-is-event-nth fn-evc-th-at-is-event-nth
                                fn-evc-record-shape fn-evc-stxe-shape
                                fn-evc-stxk-shape fn-evc-stxa-shape
                                fn-evc-retention-shape fn-evc-consumer-shape
                                fn-evc-topic-shape zp)
                              (theory 'ground-zero)))))
(defthm fn-evc-field-by-shape-is-store-event-generation
  (implies (fn-store-event-p x)
           (equal (fn-evc-field-by-shape 2 x) (fn-store-event-generation x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-store-event-p fn-store-event-generation
                                fn-evc-field-by-shape fn-store-event-nth
                                fn-record-generation fn-stxe-generation fn-stxk-generation fn-stxa-generation
                                fn-cpe-generation fn-evc-cp-nth-is-event-nth fn-evc-th-at-is-event-nth
                                fn-evc-record-shape fn-evc-stxe-shape
                                fn-evc-stxk-shape fn-evc-stxa-shape
                                fn-evc-retention-shape fn-evc-consumer-shape
                                fn-evc-topic-shape zp)
                              (theory 'ground-zero))
           :expand ((fn-store-event-nth 2 x) (fn-store-event-nth 1 (cdr x))
                    (fn-store-event-nth 0 (cddr x))))))
(defthm fn-evc-class-by-shape-is-fn-record-p
  (implies (fn-store-event-p x)
           (iff (fn-record-p x) (equal (fn-evc-class-by-shape x) :record)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-store-event-p fn-evc-class-by-shape
                                fn-evc-consp-drop
                                fn-evc-record-shape fn-evc-stxe-shape
                                fn-evc-stxk-shape fn-evc-stxa-shape
                                fn-evc-retention-shape fn-evc-consumer-shape
                                fn-evc-topic-shape)
                              (theory 'ground-zero)))))
(defthm fn-evc-class-by-shape-is-fn-store-retention-event-p
  (implies (fn-store-event-p x)
           (iff (fn-store-retention-event-p x) (equal (fn-evc-class-by-shape x) :retention)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-store-event-p fn-evc-class-by-shape
                                fn-evc-consp-drop
                                fn-evc-record-shape fn-evc-stxe-shape
                                fn-evc-stxk-shape fn-evc-stxa-shape
                                fn-evc-retention-shape fn-evc-consumer-shape
                                fn-evc-topic-shape)
                              (theory 'ground-zero)))))
(defthm fn-evc-class-by-shape-is-fn-stxe-p
  (implies (fn-store-event-p x)
           (iff (fn-stxe-p x) (equal (fn-evc-class-by-shape x) :stxe)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-store-event-p fn-evc-class-by-shape
                                fn-evc-consp-drop
                                fn-evc-record-shape fn-evc-stxe-shape
                                fn-evc-stxk-shape fn-evc-stxa-shape
                                fn-evc-retention-shape fn-evc-consumer-shape
                                fn-evc-topic-shape)
                              (theory 'ground-zero)))))
(defthm fn-evc-class-by-shape-is-fn-stxk-p
  (implies (fn-store-event-p x)
           (iff (fn-stxk-p x) (equal (fn-evc-class-by-shape x) :stxk)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-store-event-p fn-evc-class-by-shape
                                fn-evc-consp-drop
                                fn-evc-record-shape fn-evc-stxe-shape
                                fn-evc-stxk-shape fn-evc-stxa-shape
                                fn-evc-retention-shape fn-evc-consumer-shape
                                fn-evc-topic-shape)
                              (theory 'ground-zero)))))
(defthm fn-evc-class-by-shape-is-fn-stxa-p
  (implies (fn-store-event-p x)
           (iff (fn-stxa-p x) (equal (fn-evc-class-by-shape x) :stxa)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-store-event-p fn-evc-class-by-shape
                                fn-evc-consp-drop
                                fn-evc-record-shape fn-evc-stxe-shape
                                fn-evc-stxk-shape fn-evc-stxa-shape
                                fn-evc-retention-shape fn-evc-consumer-shape
                                fn-evc-topic-shape)
                              (theory 'ground-zero)))))
(defthm fn-evc-class-by-shape-is-fn-cpe-eventp
  (implies (fn-store-event-p x)
           (iff (fn-cpe-eventp x) (equal (fn-evc-class-by-shape x) :consumer)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-store-event-p fn-evc-class-by-shape
                                fn-evc-consp-drop
                                fn-evc-record-shape fn-evc-stxe-shape
                                fn-evc-stxk-shape fn-evc-stxa-shape
                                fn-evc-retention-shape fn-evc-consumer-shape
                                fn-evc-topic-shape)
                              (theory 'ground-zero)))))
(defthm fn-evc-class-by-shape-is-fn-th-topic-eventp
  (implies (fn-store-event-p x)
           (iff (fn-th-topic-eventp x) (equal (fn-evc-class-by-shape x) :topic)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-store-event-p fn-evc-class-by-shape
                                fn-evc-consp-drop
                                fn-evc-record-shape fn-evc-stxe-shape
                                fn-evc-stxk-shape fn-evc-stxa-shape
                                fn-evc-retention-shape fn-evc-consumer-shape
                                fn-evc-topic-shape)
                              (theory 'ground-zero)))))

; -----------------------------------------------------------------------------
; The carried accessors.  In the logic each IS its reference, so a caller's
; theorems are unchanged by the substitution; in execution each is the
; reading by shape, and its guard, the carried fact fn-store-event-p, is what
; guard verification spends the keystone on.  A caller calls one only where
; it holds that fact.

(defun fn-evc-sequence (x)
  (declare (xargs :guard (fn-store-event-p x)
                  :guard-hints (("Goal" :use fn-evc-field-by-shape-is-store-event-sequence
                                 :in-theory nil))))
  (mbe :logic (fn-store-event-sequence x) :exec (fn-evc-field-by-shape 0 x)))
(defun fn-evc-txid (x)
  (declare (xargs :guard (fn-store-event-p x)
                  :guard-hints (("Goal" :use fn-evc-field-by-shape-is-store-event-txid
                                 :in-theory nil))))
  (mbe :logic (fn-store-event-txid x) :exec (fn-evc-field-by-shape 1 x)))
(defun fn-evc-generation (x)
  (declare (xargs :guard (fn-store-event-p x)
                  :guard-hints (("Goal" :use fn-evc-field-by-shape-is-store-event-generation
                                 :in-theory nil))))
  (mbe :logic (fn-store-event-generation x) :exec (fn-evc-field-by-shape 2 x)))
(defun fn-evc-recordp (x)
  (declare (xargs :guard (fn-store-event-p x)
                  :guard-hints (("Goal" :use fn-evc-class-by-shape-is-fn-record-p
                                 :in-theory (union-theories '((:type-prescription fn-record-p))
                                                            (theory 'ground-zero))))))
  (mbe :logic (fn-record-p x) :exec (eq (fn-evc-class-by-shape x) :record)))
(defun fn-evc-retentionp (x)
  (declare (xargs :guard (fn-store-event-p x)
                  :guard-hints (("Goal" :use fn-evc-class-by-shape-is-fn-store-retention-event-p
                                 :in-theory (union-theories '((:type-prescription fn-store-retention-event-p))
                                                            (theory 'ground-zero))))))
  (mbe :logic (fn-store-retention-event-p x) :exec (eq (fn-evc-class-by-shape x) :retention)))
(defun fn-evc-stxep (x)
  (declare (xargs :guard (fn-store-event-p x)
                  :guard-hints (("Goal" :use fn-evc-class-by-shape-is-fn-stxe-p
                                 :in-theory (union-theories '((:type-prescription fn-stxe-p))
                                                            (theory 'ground-zero))))))
  (mbe :logic (fn-stxe-p x) :exec (eq (fn-evc-class-by-shape x) :stxe)))
(defun fn-evc-stxkp (x)
  (declare (xargs :guard (fn-store-event-p x)
                  :guard-hints (("Goal" :use fn-evc-class-by-shape-is-fn-stxk-p
                                 :in-theory (union-theories '((:type-prescription fn-stxk-p))
                                                            (theory 'ground-zero))))))
  (mbe :logic (fn-stxk-p x) :exec (eq (fn-evc-class-by-shape x) :stxk)))
(defun fn-evc-stxap (x)
  (declare (xargs :guard (fn-store-event-p x)
                  :guard-hints (("Goal" :use fn-evc-class-by-shape-is-fn-stxa-p
                                 :in-theory (union-theories '((:type-prescription fn-stxa-p))
                                                            (theory 'ground-zero))))))
  (mbe :logic (fn-stxa-p x) :exec (eq (fn-evc-class-by-shape x) :stxa)))
(defun fn-evc-consumerp (x)
  (declare (xargs :guard (fn-store-event-p x)
                  :guard-hints (("Goal" :use fn-evc-class-by-shape-is-fn-cpe-eventp
                                 :in-theory (union-theories '((:type-prescription fn-cpe-eventp))
                                                            (theory 'ground-zero))))))
  (mbe :logic (fn-cpe-eventp x) :exec (eq (fn-evc-class-by-shape x) :consumer)))
(defun fn-evc-topicp (x)
  (declare (xargs :guard (fn-store-event-p x)
                  :guard-hints (("Goal" :use fn-evc-class-by-shape-is-fn-th-topic-eventp
                                 :in-theory (union-theories '((:type-prescription fn-th-topic-eventp))
                                                            (theory 'ground-zero))))))
  (mbe :logic (fn-th-topic-eventp x) :exec (eq (fn-evc-class-by-shape x) :topic)))

(deftheory fn-evc-carried-definitions
  '(fn-evc-sequence fn-evc-txid fn-evc-generation fn-evc-recordp
    fn-evc-retentionp fn-evc-stxep fn-evc-stxkp fn-evc-stxap
    fn-evc-consumerp fn-evc-topicp))

(in-theory (disable fn-evc-carried-definitions fn-evc-class-by-shape
                    fn-evc-field-by-shape fn-evc-drop))
