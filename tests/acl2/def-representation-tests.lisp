; What `def-representation' generates (books/def-representation.lisp),
; proved once here; the precedent is tests/acl2/proto-adt-tests.lisp for the
; prototype's own genericity and executed witnesses.
;
; 1. A record instance (the prototype's path, promoted): declared and
;    executed, columns against the logical list.
; 2. The scalar pilot: the payload arena's logical view
;    (books/payload-arena.lisp, `fn-arn-payload-listp': a list of octet
;    lists; count = len, payload = nth, seal = append) re-expressed as one
;    declaration, `(def-representation drt-pay (payload :octets) :scalar t)',
;    and the generated exports proved EQUAL IN MEANING to the arena's
;    logical functions `fn-arena$a-count', `fn-arena$a-payload',
;    `fn-arena$a-seal-list' and its recognizer, on every value.  The arena's
;    own books are untouched: a dependent of `fn-arena' is unchanged.
; 3. The generic: `:generic t' emits the columnar implementation, the
;    attachment and the attachable generic over a list foundation; a
;    function written against the generic runs, under the attachment, on
;    the columns, and answers what the logical side answers.
; 4. Teeth: the expansion-time refusals, each by the check that names it,
;    and the attachment trap: an invariant that reaches an attached
;    function is refused BEFORE any event is generated (the catalog's
;    2026-09-27 lesson, made structural).

(in-package "ACL2")
(include-book "../../books/def-representation")
(include-book "../../books/payload-arena-bytes")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

; -----------------------------------------------------------------------------
; 1. A record instance.

(def-representation drt-held (id :u64) (msgid :octets) (flag :bool))

(defun drt-held-run ()
  (declare (xargs :guard t))
  (with-local-stobj drt-held
    (mv-let (out drt-held)
      (let* ((drt-held (drt-held-append '(7 (104 105) t) drt-held))
             (drt-held (drt-held-append '(9 (1 2 3) nil) drt-held))
             (drt-held (drt-held-set-msgid 0 '(200 201) drt-held))
             (before (list (drt-held-count drt-held)
                           (drt-held-get-id 0 drt-held) (drt-held-get-msgid 0 drt-held)
                           (drt-held-get-flag 0 drt-held)
                           (drt-held-get-id 1 drt-held) (drt-held-get-msgid 1 drt-held)
                           (drt-held-get-flag 1 drt-held)))
             ; The clear, then a fresh append: the pool and the columns restart at 0.
             (drt-held (drt-held-clear drt-held))
             (cleared (drt-held-count drt-held))
             (drt-held (drt-held-append '(3 (5) t) drt-held)))
        (mv (list before cleared (drt-held-count drt-held)
                  (drt-held-get-id 0 drt-held) (drt-held-get-msgid 0 drt-held))
            drt-held))
      out)))

(assert! (equal (drt-held-run) '((2 7 (200 201) t 9 (1 2 3) nil) 0 1 3 (5))))

; The admitted foundation and the instance share a package.
(assert-event (equal (symbol-package-name 'drt-held$c)
                     (symbol-package-name 'drt-held)))

; A non-ACL2 witness: the expansion trees for record, scalar and generic
; put the foundation in the instance's package.
(program)
(defun drt-find-foundation (events)
  (cond ((atom events) nil)
        ((eq (car events) 'defstobj) (cadr events))
        (t (or (drt-find-foundation (car events))
               (drt-find-foundation (cdr events))))))

; Find the concrete clear, including NAME-COLS$C-CLEAR in generic expansions.
(defun drt-find-clear (events name)
  (cond ((atom events) nil)
        ((and (eq (car events) 'defun) (eq (cadr events) name)) events)
        (t (or (drt-find-clear (car events) name)
               (drt-find-clear (cdr events) name)))))

; Collect call heads, not variable occurrences, with the requested prefix.
(defun drt-prefixed-calls (tree prefix)
  (if (atom tree)
      nil
    (append
     (if (and (symbolp (car tree))
              (<= (length prefix) (length (symbol-name (car tree))))
              (equal prefix (subseq (symbol-name (car tree)) 0 (length prefix))))
         (list (car tree))
       nil)
     (drt-prefixed-calls (car tree) prefix)
     (drt-prefixed-calls (cdr tree) prefix))))

(defun drt-calls-in-package-p (calls package)
  (if (endp calls)
      t
    (and (equal (symbol-package-name (car calls)) package)
         (drt-calls-in-package-p (cdr calls) package))))

(defun drt-clear-calls-in-package-p (events package)
  (let* ((clear (drt-find-clear events
                               (adt-sym (drt-find-foundation events) "-CLEAR")))
         (resizes (drt-prefixed-calls (car (last clear)) "RESIZE-"))
         (updates (drt-prefixed-calls (car (last clear)) "UPDATE-")))
    (and clear (consp resizes) (consp updates)
         (drt-calls-in-package-p resizes package)
         (drt-calls-in-package-p updates package))))

(logic)

(assert-event
 (equal (symbol-package-name
         (drt-find-foundation (rep-instance-events :drt-package '((id :u64)) nil nil nil nil nil)))
        (symbol-package-name :drt-package)))
(assert-event
 (equal (symbol-package-name
         (drt-find-foundation (rep-instance-events :drt-package '((id :u64)) t nil nil nil nil)))
        (symbol-package-name :drt-package)))
(assert-event
 (equal (symbol-package-name
         (drt-find-foundation (rep-instance-events :drt-package '((id :u64)) t t nil nil nil)))
        (symbol-package-name :drt-package)))

; Every clear resize/update stays in the instance's package, with both
; kinds of call present (record, scalar and generic).
(assert-event
 (drt-clear-calls-in-package-p
  (rep-instance-events :drt-package '((id :u64)) nil nil nil nil nil)
  (symbol-package-name :drt-package)))
(assert-event
 (drt-clear-calls-in-package-p
  (rep-instance-events :drt-package '((id :u64)) t nil nil nil nil)
  (symbol-package-name :drt-package)))
(assert-event
 (drt-clear-calls-in-package-p
  (rep-instance-events :drt-package '((id :u64)) t t nil nil nil)
  (symbol-package-name :drt-package)))
(assert-event
 (drt-clear-calls-in-package-p
  (rep-instance-events 'drt-two '((id :u64)) nil nil nil nil nil) "ACL2"))

; One spelling in two packages: two instances, two foundations.
(assert-event
 (not (equal (drt-find-foundation (rep-instance-events :drt-two '((id :u64)) nil nil nil nil nil))
             (drt-find-foundation (rep-instance-events 'drt-two '((id :u64)) nil nil nil nil nil)))))
(assert-event
 (equal (symbol-package-name
         (drt-find-foundation (rep-instance-events 'drt-two '((id :u64)) nil nil nil nil nil)))
        "ACL2"))
; An admitted two-package instance needs a defpkg portcullis, which
; tools/certify_books.py does not carry for a test book yet (NEXT).

;; Teeth for adt-corr-of-clear-c (books/proto/adt-lib.lisp): the complete
;; antecedent on a one-column schema, the cleared image exactly, and two
;; images no clear produces: one that forgets the count (adt-corr rejects
;; it) and one that forgets the column (adt-corr ACCEPTS it with the empty
;; abstraction, so only the clear's own image tells it apart).
(defconst *drt-clear-s* '((:u64)))
(defconst *drt-clear-c* '((7 0) nil 2 0))
(assert! (and (adt-schemap *drt-clear-s*) (true-listp *drt-clear-c*)
              (adt-corr *drt-clear-s* (adt-clear-c *drt-clear-s* *drt-clear-c*) nil)))
(assert! (equal (adt-clear-c *drt-clear-s* *drt-clear-c*) '(nil nil 0 0)))
(assert! (not (adt-corr *drt-clear-s* '(nil nil 1 0) nil)))          ; MUTANT forget-count
(assert! (adt-corr *drt-clear-s* '((7 0) nil 0 0) nil))               ; MUTANT forget-column: corr-blind
(assert! (not (equal (adt-clear-c *drt-clear-s* *drt-clear-c*) '((7 0) nil 0 0))))

;; Hypothesis-removal witness: omit adt-schemap, retain true-listp.
(assert! (let ((s '((:bogus))) (c nil))
           (and (true-listp c)
                (not (adt-schemap s))
                (not (adt-corr s (adt-clear-c s c) nil)))))

;; corrupted-state hypothesis-removal witness: omit true-listp, retain adt-schemap.
; THM checks the logical value: executable UPDATE-NTH guards reject this
; deliberately improper input before its logical clear can be observed.
(assert-event
 (thm (let ((s '((:u64))) (c '(nil nil 0 0 . bad-tail)))
        (and (adt-schemap s)
             (not (true-listp c))
             (not (adt-corr s (adt-clear-c s c) nil)))))
 :stobjs-out :auto)

; -----------------------------------------------------------------------------
; 2. The scalar pilot: the arena's logical view.

(def-representation drt-pay (payload :octets) :scalar t)

(defun drt-pay-run ()
  (declare (xargs :guard t))
  (with-local-stobj drt-pay
    (mv-let (out drt-pay)
      (let* ((drt-pay (drt-pay-append '(1 2 3) drt-pay))
             (drt-pay (drt-pay-append '(4) drt-pay))
             (drt-pay (drt-pay-set 0 '(9 9) drt-pay))
             (before (list (drt-pay-count drt-pay) (drt-pay-get 0 drt-pay) (drt-pay-get 1 drt-pay)))
             (drt-pay (drt-pay-clear drt-pay)))
        (mv (list before (drt-pay-count drt-pay)) drt-pay))
      out)))

(assert! (equal (drt-pay-run) '((2 (9 9) (4)) 0)))

; DRT-PAY-COUNT{CORRESPONDENCE}: both hypotheses and its exact conclusion
; at a reachable one-payload foundation, built from the canonical empty.
(defconst *drt-pay-witness-c*
  (adt-append-c *drt-pay-schema* '((1 2 3)) (adt-empty-c *drt-pay-schema*)))
(defconst *drt-pay-witness-a* '((1 2 3)))

(assert-event
 (and (drt-pay$corr *drt-pay-witness-c* *drt-pay-witness-a*)
      (drt-pay$ap *drt-pay-witness-a*)))
; As in the seeded :into witness, THM permits the concrete stobj's logical
; value and evaluates the ground assertion; no implication hides a premise.
(assert-event
 (thm (and (drt-pay$corr *drt-pay-witness-c* *drt-pay-witness-a*)
           (drt-pay$ap *drt-pay-witness-a*)
           (equal (drt-pay$c-count-of *drt-pay-witness-c*)
                  (drt-pay$a-count *drt-pay-witness-a*))))
 :stobjs-out :auto)

; The same program over the logical value: the list of payloads.
(assert! (equal (let* ((a (append (append nil (list '(1 2 3))) (list '(4))))
                       (a (update-nth 0 '(9 9) a)))
                  (list (len a) (nth 0 a) (nth 1 a)))
                '(2 (9 9) (4))))

; Equal in meaning to the arena's logical exports, on every value.
(defthm drt-pay-recognizer-is-arena-recognizer
  (equal (drt-payp x) (fn-arena$ap x))
  :hints (("Goal" :in-theory (enable fn-arena$ap fn-arn-payload-listp adt-scalar-seq-p
                                     adt-val-okp adt-octetsp fn-cbor-octet-listp fn-cbor-octetp))))

(defthm drt-pay-count-is-arena-count
  (equal (drt-pay-count a) (fn-arena$a-count a))
  :hints (("Goal" :in-theory (enable fn-arena$a-count))))

(defthm drt-pay-get-is-arena-payload
  (equal (drt-pay-get h a) (fn-arena$a-payload h a))
  :hints (("Goal" :in-theory (enable fn-arena$a-payload))))

(defthm drt-pay-append-is-arena-seal-list
  (equal (drt-pay-append xs a) (fn-arena$a-seal-list xs a))
  :hints (("Goal" :in-theory (enable fn-arena$a-seal-list))))

; -----------------------------------------------------------------------------
; 3. The generic, attached to its columns.

(def-representation drt-gen (payload :octets) :scalar t :generic t)

; A function against the GENERIC; nothing here names the columns.
(defun drt-gen-total (i drt-gen)
  (declare (xargs :stobjs drt-gen :guard (natp i) :measure (nfix (- (drt-gen-count drt-gen) i))))
  (if (and (mbt (natp i)) (< i (drt-gen-count drt-gen)))
      (+ (len (drt-gen-get i drt-gen)) (drt-gen-total (+ 1 i) drt-gen))
    0))

(defun drt-gen-run ()
  (declare (xargs :guard t))
  (with-local-stobj drt-gen
    (mv-let (out drt-gen)
      (let* ((drt-gen (drt-gen-append '(1 2 3) drt-gen))
             (drt-gen (drt-gen-append '(4) drt-gen))
             (drt-gen (drt-gen-set 1 '(5 6) drt-gen))
             (before (list (drt-gen-count drt-gen) (drt-gen-get 0 drt-gen) (drt-gen-get 1 drt-gen)
                           (drt-gen-total 0 drt-gen)))
             (drt-gen (drt-gen-clear drt-gen)))
        (mv (list before (drt-gen-count drt-gen) (drt-gen-total 0 drt-gen)) drt-gen))
      out)))

(assert! (equal (drt-gen-run) '((2 (1 2 3) (5 6) 5) 0 0)))

; The generic's exports mean the list operations, as the implementation's do.
(defthm drt-gen-count-is-len (equal (drt-gen-count a) (len a)))
(defthm drt-gen-get-is-nth (equal (drt-gen-get i a) (nth i a)))
(defthm drt-gen-clear-is-nil (equal (drt-gen-clear a) nil))

; -----------------------------------------------------------------------------
; 4. Teeth.

(must-fail-checked
 (def-representation drt-r1 (id :u128))
 :unchecked "refused at expansion: an unknown kind")
(must-fail-checked
 (def-representation drt-r2 (id :u64) (b :u8) :scalar t)
 :unchecked "refused at expansion: :scalar with two fields")
(must-fail-checked
 (def-representation drt-r3 (id :u64) :scalar t :invariant drt-not-a-function)
 :unchecked "refused at expansion: :invariant is not a function")
(must-fail-checked
 (def-representation drt-r4 (id :u64) :scalar t :invariant true-listp)
 :unchecked "refused at expansion: :invariant without :invariant-lemmas")

; The attachment trap.  `drt-oracle' stands for `fn-digest': a constrained
; function with an attachment.  An invariant over the sequence that calls
; it would make the recognizer reach an attached function.
(defstub drt-oracle (x) t)
(defun drt-oracle-ok (a)
  (declare (xargs :guard t))
  (equal (drt-oracle a) a))
(defattach drt-oracle identity)

(assert-event (equal (rep-attached-ancestors '(drt-oracle-ok) (w state)) '(drt-oracle)))
(assert-event (equal (rep-attached-ancestors '(adt-corr adt-seq-p adt-scalar-seq-p) (w state)) nil))

(must-fail-checked
 (def-representation drt-r5 (id :u64) :scalar t :invariant drt-oracle-ok
   :invariant-lemmas (drt-pay-count-is-arena-count))
 :unchecked "refused at expansion: the invariant reaches an attached function")

; -----------------------------------------------------------------------------
; 5. The world rows.

(assert-event (equal (cdr (assoc-eq 'drt-pay (table-alist 'fn-generated (w state))))
                     '(:def-representation :scalar t :generic nil :implementation drt-pay :invariant nil :trees nil :write-once nil)))
(assert-event (equal (cdr (assoc-eq 'drt-gen (table-alist 'fn-generated (w state))))
                     '(:def-representation :scalar t :generic t :implementation drt-gen-cols :invariant nil :trees nil :write-once nil)))

; -----------------------------------------------------------------------------
; 6. A TREE field (books/def-representation-tree.lisp, lane paged-catalog-3):
;    refused before the writer's library is in the world; then declared,
;    and NAME-APPEND-T executed: the octets read back are the tree's
;    program (the list codec's `fn-scc-program'), a tree past the codec's
;    reach is refused by its guard's recognizer (`adt-tree-okp'), and the
;    logical value is the append of the encoded record.

(must-fail-checked
 (def-representation drt-t0 (a :u64) (tr :tree))
 :unchecked "refused at expansion: a :tree field needs books/def-representation-tree")

(include-book "../../books/def-representation-tree")

(def-representation drt-t1 (a :u64) (m :octets) (tr :tree) (b :bool))

(defconst *drt-tree* '("fn.x" 3 -4 #\a (5 6 7) nil . :k))

(defun drt-t1-witness (drt-t1)
  (declare (xargs :stobjs drt-t1 :verify-guards nil))
  (let ((drt-t1 (drt-t1-append-t (list 7 '(1 2) *drt-tree* t) drt-t1)))
    (mv (list (drt-t1-count drt-t1) (drt-t1-get-a 0 drt-t1) (drt-t1-get-m 0 drt-t1)
              (drt-t1-get-tr 0 drt-t1) (drt-t1-get-b 0 drt-t1))
        drt-t1)))

(defun drt-t1-witness-ok ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj drt-t1
    (mv-let (got drt-t1) (drt-t1-witness drt-t1)
      (equal got (list 1 7 '(1 2) (fn-scc-program *drt-tree*) t)))))

(assert-event (drt-t1-witness-ok))

; The complete antecedent of the writer's meaning, on the witness's tree,
; and its conclusion (program then the owed CONS operations).
(assert-event (and (adt-tree-okp *drt-tree*) (fn-sccb-treep *drt-tree*)
                   (equal (adt-tree-plen *drt-tree* 0) (len (fn-scc-program *drt-tree*)))))
; A tree the codec cannot carry (a natural of 2^2040 needs 256 digits) is
; not `adt-tree-okp', exactly as it is not `fn-sccb-treep'.
(assert-event (and (not (adt-tree-okp (list (expt 2 2040)))) (not (fn-sccb-treep (list (expt 2 2040))))))

; TEETH of the library keystone adt-tree-push-is-push (Codex r21 F1),
; evaluated at its literal statement (drt-tpp: each hypothesis, then the
; conclusion).  Positive, reachable: the witness's tree into a two-octet pool
; at fill 1, every hypothesis and the conclusion true.  Hypothesis removal,
; each keeping the other two: a tree the codec cannot carry (fn-sccb-treep
; false) and a fill that is not a natural; the conclusion fails for both.
; (natp p) is the generator's constant column count, never a variable.
(defun drt-tpp (p x c)
  (declare (xargs :verify-guards nil))
  (list (natp p) (fn-sccb-treep x) (natp (nth (+ 2 p) c))
        (equal (adt-pool-cputs p (append (fn-scc-program x) (fn-scc-repeat 0 *fn-scc-op-cons*))
                               (adt-pool-room p (+ (nth (+ 2 p) c) (adt-tree-plen x 0)) c))
               (adt-pool-push p (fn-scc-program x) c))))
(assert-event (equal (with-guard-checking :none (drt-tpp 0 *drt-tree* (list '(5 6) 0 1)))
                     '(t t t t)))
(assert-event (equal (with-guard-checking :none (drt-tpp 0 (list (expt 2 2040)) (list '(5 6) 0 1)))
                     '(t nil t nil)))
(assert-event (equal (with-guard-checking :none (drt-tpp 0 *drt-tree* (list '(5 6) 0 -1)))
                     '(t t nil nil)))

; TEETH of the instance's DRT-T1$C-APPEND-T-IS-APPEND, executed on the
; foundation: its antecedents (the tree field adt-tree-okp; the fill a
; natural, which the stobj's type gives) and its conclusion, observed as
; every field of the row, the count and the pool's fill after append-t and
; after the plain append of the encoded record from the same cleared image.
; The WHOLE foundation, every field: each array's length and every element,
; the count and the fill.  Equal snapshots are equal stobjs (a stobj is the
; list of its fields), so comparing them asserts the theorem's conclusion,
; an equality of whole states (Codex r23 F4).
(defun drt-t1-arr-loop (i n f drt-t1$c)
  (declare (xargs :stobjs drt-t1$c :verify-guards nil
                  :measure (nfix (- (nfix n) (nfix i)))))
  (if (< (nfix i) (nfix n))
      (cons (case f
              (:a (drt-t1$c-ai i drt-t1$c))
              (:moff (drt-t1$c-m-offi i drt-t1$c))
              (:mlen (drt-t1$c-m-leni i drt-t1$c))
              (:troff (drt-t1$c-tr-offi i drt-t1$c))
              (:trlen (drt-t1$c-tr-leni i drt-t1$c))
              (:b (drt-t1$c-bi i drt-t1$c))
              (otherwise (drt-t1$c-pooli i drt-t1$c)))
            (drt-t1-arr-loop (+ 1 (nfix i)) n f drt-t1$c))
    nil))

(defun drt-t1-snap (drt-t1$c)
  (declare (xargs :stobjs drt-t1$c :verify-guards nil))
  (list (drt-t1-arr-loop 0 (drt-t1$c-a-length drt-t1$c) :a drt-t1$c)
        (drt-t1-arr-loop 0 (drt-t1$c-m-off-length drt-t1$c) :moff drt-t1$c)
        (drt-t1-arr-loop 0 (drt-t1$c-m-len-length drt-t1$c) :mlen drt-t1$c)
        (drt-t1-arr-loop 0 (drt-t1$c-tr-off-length drt-t1$c) :troff drt-t1$c)
        (drt-t1-arr-loop 0 (drt-t1$c-tr-len-length drt-t1$c) :trlen drt-t1$c)
        (drt-t1-arr-loop 0 (drt-t1$c-b-length drt-t1$c) :b drt-t1$c)
        (drt-t1-arr-loop 0 (drt-t1$c-pool-length drt-t1$c) :pool drt-t1$c)
        (drt-t1$c-count drt-t1$c) (drt-t1$c-fill drt-t1$c)))

; drt-t1$c-append-t-is-append at its literal statement: antecedents (the
; tree field's okp, the INPUT state's fill a natural) asserted on the run's
; input; conclusion the equality of the whole states.  Labelled MUTATION:
; the plain append of a record differing in one octet of the program gives
; an unequal whole state.
(defun drt-t1-is-append-run (drt-t1$c)
  (declare (xargs :stobjs drt-t1$c :verify-guards nil))
  (let* ((rec (list 7 '(1 2) *drt-tree* t))
         (drt-t1$c (drt-t1$c-clear drt-t1$c))
         (drt-t1$c (drt-t1$c-append (list 1 '(9 9 9) '(4) nil) drt-t1$c))
         (in-fill (drt-t1$c-fill drt-t1$c))
         (drt-t1$c (drt-t1$c-append-t rec drt-t1$c))
         (s1 (drt-t1-snap drt-t1$c))
         (drt-t1$c (drt-t1$c-clear drt-t1$c))
         (drt-t1$c (drt-t1$c-append (list 1 '(9 9 9) '(4) nil) drt-t1$c))
         (drt-t1$c (drt-t1$c-append (drt-t1-tree-enc rec) drt-t1$c))
         (s2 (drt-t1-snap drt-t1$c))
         (prog (fn-scc-program *drt-tree*))
         (drt-t1$c (drt-t1$c-clear drt-t1$c))
         (drt-t1$c (drt-t1$c-append (list 1 '(9 9 9) '(4) nil) drt-t1$c))
         (drt-t1$c (drt-t1$c-append (list 7 '(1 2) (cons (logxor 1 (car prog)) (cdr prog)) t)
                                    drt-t1$c))
         (s3 (drt-t1-snap drt-t1$c)))
    (mv (list (adt-tree-okp (caddr rec)) (natp in-fill) (< 0 in-fill) (equal s1 s2) (equal s1 s3))
        drt-t1$c)))

(defun drt-t1-is-append-ok ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj drt-t1$c
    (mv-let (got drt-t1$c) (drt-t1-is-append-run drt-t1$c)
      (equal got '(t t t t nil)))))

(assert-event (drt-t1-is-append-ok))

(defthm drt-t1-append-t-meaning
  (equal (drt-t1-append-t rec drt-t1)
         (append drt-t1 (list (list (car rec) (cadr rec) (fn-scc-program (caddr rec)) (cadddr rec)))))
  :hints (("Goal" :in-theory (enable drt-t1-tree-enc-is-list))))

(assert-event (equal (cdr (assoc-eq 'drt-t1 (table-alist 'fn-generated (w state))))
                     '(:def-representation :scalar nil :generic nil :implementation drt-t1 :invariant nil
                       :trees (tr) :write-once nil)))

; -----------------------------------------------------------------------------
; 7. WRITE-ONCE (:write-once t, lane paged-catalog-4, Codex r21 F1): no
;    octets or tree field has a set export, and the generated
;    NAME$C-FILL-IS-LOAD-OF-* theorems say the pool's fill is `adt-load' of
;    the logical sequence after every writing export.  Refusals; the absent
;    exports; an executed positive witness of the keystone's antecedent and
;    conclusion on the concrete foundation; the hypothesis-removal witness
;    (the same writes on an instance WITHOUT :write-once: rewriting an
;    octets field to its own value leaves the logical sequence unchanged and
;    grows the fill, so fill = load fails -- the bug Codex r21 F1 found in
;    the paged catalog's withdrawal).

(must-fail-checked
 (def-representation drt-w0 (a :u64) (m :octets) :write-once t :scalar t)
 :unchecked "refused at expansion: :write-once is supported without :scalar and :generic")
(must-fail-checked
 (def-representation drt-w0 (a :u64) (m :octets) :write-once 3)
 :unchecked "refused at expansion: :write-once takes t or nil")

(def-representation drt-w1 (a :u64) (m :octets) (tr :tree) :write-once t)

(assert-event (and (function-symbolp 'drt-w1-set-a (w state))
                   (not (function-symbolp 'drt-w1-set-m (w state)))
                   (not (function-symbolp 'drt-w1-set-tr (w state)))
                   (function-symbolp 'drt-w1-get-m (w state))
                   (function-symbolp 'drt-t1-set-m (w state))))

; The keystone at its literal statement (append-t, the export the catalog's
; commit executes): cited by :use, nothing else enabled.
(defthm drt-w1-fill-is-load-of-append-t-statement
  (implies (and (adt-fill-is-load *drt-w1-schema* c a) (adt-tree-okp (car (cdr (cdr rec)))))
           (adt-fill-is-load *drt-w1-schema* (drt-w1$c-append-t rec c) (drt-w1$a-append-t rec a)))
  :hints (("Goal" :use drt-w1$c-fill-is-load-of-append-t
           :in-theory (theory 'minimal-theory))))

; Executed on the foundation: from the empty image (the creator's theorem's
; antecedent-free case), an append-t, an append and a scalar set; after
; each the fill equals the load of the logical sequence built beside it.
(defun drt-w1-run (drt-w1$c)
  (declare (xargs :stobjs drt-w1$c :verify-guards nil))
  (let* ((a0 nil)
         (ok0 (equal (drt-w1$c-fill drt-w1$c) (adt-load *drt-w1-schema* a0)))
         (r1 (list 7 '(1 2 3) *drt-tree*))
         (okp1 (adt-tree-okp (caddr r1)))
         (drt-w1$c (drt-w1$c-append-t r1 drt-w1$c))
         (a1 (drt-w1$a-append-t r1 a0))
         (ok1 (and okp1 (equal (drt-w1$c-fill drt-w1$c) (adt-load *drt-w1-schema* a1))))
         (r2 (list 8 '(9) (fn-scc-program '(1 2))))
         (drt-w1$c (drt-w1$c-append r2 drt-w1$c))
         (a2 (drt-w1$a-append r2 a1))
         (ok2 (equal (drt-w1$c-fill drt-w1$c) (adt-load *drt-w1-schema* a2)))
         (drt-w1$c (drt-w1$c-set-a 0 99 drt-w1$c))
         (a3 (drt-w1$a-set-a 0 99 a2))
         (ok3 (equal (drt-w1$c-fill drt-w1$c) (adt-load *drt-w1-schema* a3))))
    (mv (list ok0 ok1 ok2 ok3 (drt-w1$c-fill drt-w1$c)
              (+ 3 (len (fn-scc-program *drt-tree*)) 1 (len (fn-scc-program '(1 2)))))
        drt-w1$c)))

(defun drt-w1-run-ok ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj drt-w1$c
    (mv-let (got drt-w1$c) (drt-w1-run drt-w1$c)
      (and (equal (take 4 got) '(t t t t)) (equal (nth 4 got) (nth 5 got)) (< 0 (nth 4 got))))))

(assert-event (drt-w1-run-ok))

; Labelled MUTATION (a schema mutation, not a hypothesis removal; Codex r23
; F5): drt-t1 (section 6) is not write-once.  The same
; append-t, then its octets field set to the value it already holds: the
; logical sequence is unchanged, the fill grew by the value's length, and
; the conclusion fill = load fails.
(defun drt-t1-rewrite (drt-t1$c)
  (declare (xargs :stobjs drt-t1$c :verify-guards nil))
  (let* ((r1 (list 7 '(1 2 3) *drt-tree* t))
         (drt-t1$c (drt-t1$c-append-t r1 drt-t1$c))
         (a1 (drt-t1$a-append-t r1 nil))
         (ok1 (equal (drt-t1$c-fill drt-t1$c) (adt-load *drt-t1-schema* a1)))
         (drt-t1$c (drt-t1$c-set-m 0 '(1 2 3) drt-t1$c))
         (a2 (drt-t1$a-set-m 0 '(1 2 3) a1)))
    (mv (list ok1 (equal a2 a1) (equal (drt-t1$c-fill drt-t1$c) (adt-load *drt-t1-schema* a2))
              (- (drt-t1$c-fill drt-t1$c) (adt-load *drt-t1-schema* a2)))
        drt-t1$c)))

(defun drt-t1-rewrite-ok ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj drt-t1$c
    (mv-let (got drt-t1$c) (drt-t1-rewrite drt-t1$c)
      (equal got (list t t nil 3)))))

(assert-event (drt-t1-rewrite-ok))

; HYPOTHESIS REMOVAL, one hypothesis at a time, of
; drt-w1$c-fill-is-load-of-append-t at its literal statement.
; (1) Without (adt-fill-is-load schema c a): c holds one record, a is the
;     empty sequence; the retained hypothesis (the tree's okp) holds, the
;     omitted one fails, and so does the conclusion.
(defun drt-w1-load-removal (drt-w1$c)
  (declare (xargs :stobjs drt-w1$c :verify-guards nil))
  (let* ((r1 (list 7 '(1 2 3) *drt-tree*))
         (drt-w1$c (drt-w1$c-clear drt-w1$c))
         (drt-w1$c (drt-w1$c-append (list 1 '(5 5) (fn-scc-program '(1))) drt-w1$c))
         (a0 nil)
         (hyp-load (equal (drt-w1$c-fill drt-w1$c) (adt-load *drt-w1-schema* a0)))
         (hyp-okp (adt-tree-okp (caddr r1)))
         (drt-w1$c (drt-w1$c-append-t r1 drt-w1$c))
         (a1 (drt-w1$a-append-t r1 a0)))
    (mv (list hyp-okp hyp-load (equal (drt-w1$c-fill drt-w1$c) (adt-load *drt-w1-schema* a1)))
        drt-w1$c)))

(defun drt-w1-load-removal-ok ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj drt-w1$c
    (mv-let (got drt-w1$c) (drt-w1-load-removal drt-w1$c)
      (equal got '(t nil nil)))))

(assert-event (drt-w1-load-removal-ok))

; (2) Without (adt-tree-okp TREE): a tree outside the codec's domain (a
;     natural of 2041 bits).  The retained hypothesis (fill = load, from the
;     empty image) holds, the omitted one fails, and the conclusion fails
;     (fill 260, load 261).  Outside its guard the executable cannot be
;     called, so this runs the definitions -- the theorem's subject -- with
;     guard checking off.
(defun drt-w1-okp-removal (tree drt-w1$c)
  (declare (xargs :stobjs drt-w1$c :verify-guards nil))
  (let* ((r1 (list 7 '(1 2 3) tree))
         (drt-w1$c (drt-w1$c-clear drt-w1$c))
         (hyp-load (equal (drt-w1$c-fill drt-w1$c) (adt-load *drt-w1-schema* nil)))
         (hyp-okp (adt-tree-okp tree))
         (drt-w1$c (drt-w1$c-append-t r1 drt-w1$c))
         (a1 (drt-w1$a-append-t r1 nil)))
    (mv (list hyp-load hyp-okp (equal (drt-w1$c-fill drt-w1$c) (adt-load *drt-w1-schema* a1)))
        drt-w1$c)))

(defun drt-w1-okp-removal-ok (tree)
  (declare (xargs :verify-guards nil))
  (with-local-stobj drt-w1$c
    (mv-let (got drt-w1$c) (drt-w1-okp-removal tree drt-w1$c)
      (equal got '(t nil nil)))))

(with-guard-checking-event :none (assert-event (drt-w1-okp-removal-ok (expt 2 2040))))

(assert-event (equal (cdr (assoc-eq 'drt-w1 (table-alist 'fn-generated (w state))))
                     '(:def-representation :scalar nil :generic nil :implementation drt-w1 :invariant nil
                       :trees (tr) :write-once t)))
