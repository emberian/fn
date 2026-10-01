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
(logic)

(assert-event
 (equal (symbol-package-name
         (drt-find-foundation (rep-instance-events :drt-package '((id :u64)) nil nil nil nil)))
        (symbol-package-name :drt-package)))
(assert-event
 (equal (symbol-package-name
         (drt-find-foundation (rep-instance-events :drt-package '((id :u64)) t nil nil nil)))
        (symbol-package-name :drt-package)))
(assert-event
 (equal (symbol-package-name
         (drt-find-foundation (rep-instance-events :drt-package '((id :u64)) t t nil nil)))
        (symbol-package-name :drt-package)))

; One spelling in two packages: two instances, two foundations.
(assert-event
 (not (equal (drt-find-foundation (rep-instance-events :drt-two '((id :u64)) nil nil nil nil))
             (drt-find-foundation (rep-instance-events 'drt-two '((id :u64)) nil nil nil nil)))))
(assert-event
 (equal (symbol-package-name
         (drt-find-foundation (rep-instance-events 'drt-two '((id :u64)) nil nil nil nil)))
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
                     '(:def-representation :scalar t :generic nil :implementation drt-pay :invariant nil :trees nil)))
(assert-event (equal (cdr (assoc-eq 'drt-gen (table-alist 'fn-generated (w state))))
                     '(:def-representation :scalar t :generic t :implementation drt-gen-cols :invariant nil :trees nil)))

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

(defthm drt-t1-append-t-meaning
  (equal (drt-t1-append-t rec drt-t1)
         (append drt-t1 (list (list (car rec) (cadr rec) (fn-scc-program (caddr rec)) (cadddr rec)))))
  :hints (("Goal" :in-theory (enable drt-t1-tree-enc-is-list))))

(assert-event (equal (cdr (assoc-eq 'drt-t1 (table-alist 'fn-generated (w state))))
                     '(:def-representation :scalar nil :generic nil :implementation drt-t1 :invariant nil
                       :trees (tr))))
