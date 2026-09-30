; Exact schema-3 reference-aware tree program and decoder.
; Capture tables and framed files remain in store-checkpoint-tables.
(in-package "ACL2")
(include-book "store-tree-codec-program-guards")
(include-book "records-shape")
(include-book "consumer-event-index-read")
(include-book "store-checkpoint-accessors")
(local (include-book "arithmetic/top" :dir :system))

(defconst *fn-sct-schema* 3)
(assert-event (equal *fn-sct-schema* *fn-scc-schema*))
; The one op added to the tree codec's 0..7.
(defconst *fn-sct-op-ref* 8)

(local
 (defthm fn-sct-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-sct-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-sct-true-list-fix-of-true-list
   (implies (true-listp x) (equal (true-list-fix x) x))))

; -----------------------------------------------------------------------------
; The payload projection: what a P row holds of an event, and what a
; reference restores.  Total, cheap (no recognizer runs): an article
; record has its Message-ID string at 3 and its payload at 4
; (fn-record-make, books/records-shape); a composite has its article-record
; bytes at 6 (fn-stxa-make-full, books/stx-accept-records); a P row is
; itself; anything else has no payload.

(defun fn-sct-octets-or-nil (v)
  (declare (xargs :guard t))
  (if (fn-scc-octets-valuep v) v nil))

(defun fn-sct-payload-of (v)
  (declare (xargs :guard t))
  (cond ((not (consp v)) nil)
        ((stringp (fn-sco-at 3 v)) (fn-sct-octets-or-nil (fn-sco-at 4 v)))
        ((consp (fn-sco-at 6 v)) (fn-sct-octets-or-nil (fn-sco-at 6 v)))
        (t (fn-sct-octets-or-nil v))))

(defthm fn-sct-payload-of-shape
  (or (null (fn-sct-payload-of v))
      (fn-scc-octets-valuep (fn-sct-payload-of v)))
  :rule-classes nil)

(local
 (defthm fn-sct-nth-of-octet-listp
   (implies (fn-scc-octet-listp x)
            (and (not (stringp (nth n x)))
                 (not (consp (nth n x)))))
   :hints (("Goal" :induct (nth n x)))))

(defthm fn-sct-payload-of-idempotent
  (equal (fn-sct-payload-of (fn-sct-payload-of v))
         (fn-sct-payload-of v))
  :hints (("Goal" :in-theory (enable fn-sco-at))))

(in-theory (disable fn-sct-payload-of))

; The reference target: P[s], read through an event index (fn-cei-get, the
; u32-keyed sequence trie).  At the encode the index is the capture's
; (records by sequence: the payload of record s); at the decode it is the
; index built from the P rows read (P[s] itself, idempotently).
(defun fn-sct-ref-get (s table)
  (declare (xargs :guard t))
  (fn-sct-payload-of (fn-cei-get s table)))

; Two tables agree on every sequence below N.
(defun fn-sct-agreep (te td n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (equal (fn-sct-ref-get (1- n) te) (fn-sct-ref-get (1- n) td))
         (fn-sct-agreep te td (1- n)))))

(defthm fn-sct-agreep-get
  (implies (and (natp n) (fn-sct-agreep te td n) (natp s) (< s n))
           (equal (fn-sct-ref-get s td) (fn-sct-ref-get s te)))
  :hints (("Goal" :induct (fn-sct-agreep te td n)
           :in-theory (disable fn-sct-ref-get))))

(defthm fn-sct-agreep-reflexive
  (fn-sct-agreep te te n))

(in-theory (disable fn-sct-ref-get fn-sct-agreep))

; -----------------------------------------------------------------------------
; The decoder: the tree codec's stack machine with the ref op.

; (STACK . REST), NIL (malformed) or :dangling (a reference to a P row that
; is absent or empty: refused by name).
(defun fn-sct-step (xs stack table)
  (declare (xargs :guard (and (consp xs) (fn-scc-octet-listp xs))))
  (if (equal (car xs) *fn-sct-op-ref*)
      (let ((n (fn-scc-read-nat (cdr xs))))
        (if (not n)
            nil
          (let ((v (fn-sct-ref-get (car n) table)))
            (if (not v) :dangling (cons (cons v stack) (cdr n))))))
    (fn-scc-step xs stack)))

(defthm fn-sct-step-facts
  (implies (and (consp xs) (fn-scc-octet-listp xs)
                (consp (fn-sct-step xs stack table)))
           (and (fn-scc-octet-listp (cdr (fn-sct-step xs stack table)))
                (< (len (cdr (fn-sct-step xs stack table))) (len xs))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-read-nat-facts (xs (cdr xs)))
                 fn-scc-step-facts fn-scc-step-shrinks)
           :in-theory (disable fn-scc-read-nat fn-scc-step fn-scc-read-nat-facts
                               fn-scc-step-facts fn-scc-step-shrinks))))

(defun fn-sct-run (xs stack table)
  (declare (xargs :guard (fn-scc-octet-listp xs) :measure (len xs)
                  :verify-guards nil))
  (if (not (consp xs))
      stack
    (let ((next (fn-sct-step xs stack table)))
      (cond ((eq next :dangling) :dangling)
            ((and (consp next) (mbt (< (len (cdr next)) (len xs))))
             (fn-sct-run (cdr next) (car next) table))
            (t :refused)))))

(verify-guards fn-sct-run
  :hints (("Goal" :use fn-sct-step-facts :in-theory (disable fn-sct-step-facts fn-sct-step))))

; -----------------------------------------------------------------------------
; The encoder: the tree codec's program with references.

; X is written as a reference to S: S below N, encodable, and X the (nonempty)
; bytes the reference restores.
(defun fn-sct-refp (x s n table)
  (declare (xargs :guard t))
  (and (natp n) (natp s) (< s n) (fn-scc-nat-encodablep s) (consp x)
       (equal x (fn-sct-ref-get s table))))

; The candidate for a stored article (MSGID PAYLOAD ...): the sequence of a
; record the Message-ID trie lists whose P row is this payload.
(defun fn-sct-candidate-among (payload records n table)
  (declare (xargs :guard t))
  (if (consp records)
      (let ((s (fn-record-sequence (car records))))
        (if (fn-sct-refp payload s n table)
            s
          (fn-sct-candidate-among payload (cdr records) n table)))
    nil))

(defun fn-sct-candidate (x mtrie n table)
  (declare (xargs :guard t))
  (if (and (consp x) (stringp (car x)) (consp (cdr x)) (consp (cadr x)))
      (fn-sct-candidate-among (cadr x) (fn-cei-trie-records (car x) mtrie) n table)
    nil))

(defthm fn-sct-candidate-among-natp
  (or (null (fn-sct-candidate-among payload records n table))
      (natp (fn-sct-candidate-among payload records n table)))
  :rule-classes :type-prescription)

(defthm fn-sct-candidate-natp
  (or (null (fn-sct-candidate x mtrie n table))
      (natp (fn-sct-candidate x mtrie n table)))
  :rule-classes :type-prescription)

; The program of X.  CAND: nil, or the sequence a leaf below may reference
; (an E row's own sequence; in R, the candidate found at the enclosing
; stored article).  MTRIE: the Message-ID trie candidates are found in (nil
; for F, P and E).
(defun fn-sct-program (x cand mtrie n table)
  (declare (xargs :guard (fn-scc-treep x) :verify-guards nil
                  :measure (acl2-count x)))
  (cond ((and cand (fn-sct-refp x cand n table))
         (cons *fn-sct-op-ref* (fn-scc-nat-octets cand)))
        ((fn-scc-octets-valuep x) (fn-scc-program x))
        ((consp x)
         (let ((c (let ((k (fn-sct-candidate x mtrie n table))) (if k k cand))))
           (append (fn-sct-program (car x) c mtrie n table)
                   (fn-sct-program (cdr x) c mtrie n table)
                   (list *fn-scc-op-cons*))))
        (t (fn-scc-atom-octets x))))

(local
 (defthm fn-sct-le-digits-true-listp
   (true-listp (fn-scc-le-digits n))))

(local
 (defthm fn-sct-atom-octets-true-listp
   (true-listp (fn-scc-atom-octets x))
   :hints (("Goal" :in-theory (enable fn-scc-atom-octets fn-scc-nat-octets
                                      fn-scc-string-octets)))))

(defthm fn-sct-program-true-listp
  (true-listp (fn-sct-program x cand mtrie n table))
  :hints (("Goal" :induct (fn-sct-program x cand mtrie n table)
           :in-theory (e/d (fn-sct-program)
                           (fn-scc-program fn-scc-atom-octets fn-scc-nat-octets
                            fn-sct-refp fn-sct-candidate fn-scc-octets-valuep
                            fn-scc-treep)))))

(verify-guards fn-sct-program
  :hints (("Goal" :expand ((fn-scc-treep x))
           :in-theory (e/d (fn-sct-refp)
                           (fn-scc-program fn-scc-atom-octets fn-scc-nat-octets
                            fn-sct-candidate fn-scc-treep fn-scc-octets-valuep
                            fn-sct-program)))))
