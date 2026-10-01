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
             (drt-held (drt-held-set-msgid 0 '(200 201) drt-held)))
        (mv (list (drt-held-count drt-held)
                  (drt-held-get-id 0 drt-held) (drt-held-get-msgid 0 drt-held)
                  (drt-held-get-flag 0 drt-held)
                  (drt-held-get-id 1 drt-held) (drt-held-get-msgid 1 drt-held)
                  (drt-held-get-flag 1 drt-held))
            drt-held))
      out)))

(assert! (equal (drt-held-run) '(2 7 (200 201) t 9 (1 2 3) nil)))

; The admitted foundation and the instance share a package.
(assert-event (equal (symbol-package-name 'drt-held$c)
                     (symbol-package-name 'drt-held)))

; A non-ACL2 witness detects fixed-ACL2 interning without a new defpkg
; portcullis. Check actual expansion trees for record, scalar and generic.
(program)
(defun drt-find-foundation (events)
  (cond ((atom events) nil)
        ((eq (car events) 'defstobj) (cadr events))
        (t (or (drt-find-foundation (car events))
               (drt-find-foundation (cdr events))))))
(logic)

(assert-event
 (equal (symbol-package-name
         (drt-find-foundation (rep-named-events :drt-package '((id :u64)) nil nil nil nil)))
        (symbol-package-name :drt-package)))
(assert-event
 (equal (symbol-package-name
         (drt-find-foundation (rep-named-events :drt-package '((id :u64)) t nil nil nil)))
        (symbol-package-name :drt-package)))
(assert-event
 (equal (symbol-package-name
         (drt-find-foundation (rep-named-events :drt-package '((id :u64)) t t nil nil)))
        (symbol-package-name :drt-package)))

; Relocation distinguishes generated references from unchanged user data.
(assert-event
 (equal (rep-package-events '(drt-package$c (quote drt-package$c))
                            '(probe$c (quote drt-package$c)) :drt-package)
        '(:drt-package$c (quote drt-package$c))))

; -----------------------------------------------------------------------------
; 2. The scalar pilot: the arena's logical view.

(def-representation drt-pay (payload :octets) :scalar t)

(defun drt-pay-run ()
  (declare (xargs :guard t))
  (with-local-stobj drt-pay
    (mv-let (out drt-pay)
      (let* ((drt-pay (drt-pay-append '(1 2 3) drt-pay))
             (drt-pay (drt-pay-append '(4) drt-pay))
             (drt-pay (drt-pay-set 0 '(9 9) drt-pay)))
        (mv (list (drt-pay-count drt-pay) (drt-pay-get 0 drt-pay) (drt-pay-get 1 drt-pay))
            drt-pay))
      out)))

(assert! (equal (drt-pay-run) '(2 (9 9) (4))))

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
             (drt-gen (drt-gen-set 1 '(5 6) drt-gen)))
        (mv (list (drt-gen-count drt-gen) (drt-gen-get 0 drt-gen) (drt-gen-get 1 drt-gen)
                  (drt-gen-total 0 drt-gen))
            drt-gen))
      out)))

(assert! (equal (drt-gen-run) '(2 (1 2 3) (5 6) 5)))

; The generic's exports mean the list operations, as the implementation's do.
(defthm drt-gen-count-is-len (equal (drt-gen-count a) (len a)))
(defthm drt-gen-get-is-nth (equal (drt-gen-get i a) (nth i a)))

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
                     '(:def-representation :scalar t :generic nil :implementation drt-pay :invariant nil)))
(assert-event (equal (cdr (assoc-eq 'drt-gen (table-alist 'fn-generated (w state))))
                     '(:def-representation :scalar t :generic t :implementation drt-gen-cols :invariant nil)))
