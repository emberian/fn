; What `def-loop' generates, proved once here so no later book proves it
; again (books/def-loop.lisp; the precedent is tests/acl2/defrecord-tests.lisp).
;
; One instance of each shape the library has a theorem for, then the teeth:
;
;   * positive witnesses, executed: the loop (`NAME-loop', which `:exec'
;     runs) and the recursion agree on concrete lists, including the empty
;     list, a stop that fires on the first element and one that never
;     fires, a filter that keeps nothing, a count past the list's end;
;   * a mutation that must fail: a loop that conses a different element
;     cannot be bridged to the recursion by the library theorem, so the
;     functional instance's obligation is doing work (the hand bridge was a
;     local induction; here the claim is the instantiation);
;   * the expansion-time refusals, one per named check;
;   * the hygiene: after a `def-loop', the loop is disabled and nothing of
;     the library is enabled.
;
; The `:into' instance writes into `fn-octets' (books/octets-stobj.lisp),
; the buffer whose logical value is the octet list: its meaning theorem is
; the D27 form of a render that conses nothing.

(in-package "ACL2")
(include-book "../../books/def-loop")
(include-book "../../books/octets-stobj")
(include-book "must-fail-checked")
(include-book "../../books/defkeystone")

; -----------------------------------------------------------------------------
; 1. :map, plain, with an extra formal (the `fn-cl-ring-keys' shape).

(def-loop dlt-pairs (ring account)
  :shape :map :elt k :body (cons k account))

(assert-event (equal (dlt-pairs '(1 2 3) 9) '((1 . 9) (2 . 9) (3 . 9))))
(assert-event (equal (dlt-pairs nil 9) nil))
(assert-event (equal (dlt-pairs-loop '(1 2 3) 9 nil) (dlt-pairs '(1 2 3) 9)))
; the accumulator is reversed onto the result: a non-empty one lands first
(assert-event (equal (dlt-pairs-loop '(1 2) 9 '(z)) '(z (1 . 9) (2 . 9))))
(assert-event (equal (dlt-pairs-loop nil 9 '(b a)) '(a b)))

; Element substitution preserves quoted data.
(def-loop dlt-quoted-elements (xs)
  :shape :map :elt e :body (list e 'e))

(assert-event (equal (dlt-quoted-elements '(7)) '((7 e))))

; 2. :map with :while (the `fn-path-butlast' shape) and :keep (a filter-map).

(def-loop dlt-butlast-ints (xs)
  :shape :map :while (consp (cdr xs)) :keep (integerp (car xs))
  :elt e :body (+ 1 e))

(assert-event (equal (dlt-butlast-ints '(1 a 2 3)) '(2 3)))
(assert-event (equal (dlt-butlast-ints '(a b)) nil))
(assert-event (equal (dlt-butlast-ints '(1)) nil))
(assert-event (equal (dlt-butlast-ints-loop '(1 a 2 3) nil) '(2 3)))

; 3. :map with :stop, :stop-value and :tail (the `fn-gacc-put' shape: replace
; the entry whose key is TEXT, else append it).

(def-loop dlt-put (text e cache)
  :shape :map :over cache
  :stop (and (consp (car cache)) (equal (car (car cache)) text))
  :stop-value (cons e (cdr cache))
  :elt c :body c
  :tail (list e))

(assert-event (equal (dlt-put 'b 'new '((a . 1) (b . 2) (c . 3))) '((a . 1) new (c . 3))))
(assert-event (equal (dlt-put 'a 'new '((a . 1) (b . 2))) '(new (b . 2))))
(assert-event (equal (dlt-put 'z 'new '((a . 1))) '((a . 1) new)))
(assert-event (equal (dlt-put 'z 'new nil) '(new)))
(assert-event (equal (dlt-put-loop 'b 'new '((a . 1) (b . 2) (c . 3)) nil)
                     (dlt-put 'b 'new '((a . 1) (b . 2) (c . 3)))))

; 4. :map with :let (the `fn-nntp-verdict-hdr-lines' shape: the test and
; the element share a computation).

(defun dlt-lookup (k table)
  (declare (xargs :guard t))
  (if (and (consp table) (consp (car table)))
      (if (equal (car (car table)) k) (cdr (car table)) (dlt-lookup k (cdr table)))
    nil))

(def-loop dlt-found (keys table)
  :shape :map
  :let ((k (car keys)) (v (dlt-lookup k table)))
  :keep (consp v)
  :body (cons k (car v)))

(assert-event (equal (dlt-found '(a b c) '((a 1) (c 3))) '((a . 1) (c . 3))))
(assert-event (equal (dlt-found '(x) '((a 1))) nil))

; 5. :take (the `fn-rof-first' shape: at most the first N, no padding).

(def-loop dlt-first (n xs)
  :shape :take :count n :over xs :while (consp xs)
  :elt e :body e :guard (natp n))

(assert-event (equal (dlt-first 2 '(a b c)) '(a b)))
(assert-event (equal (dlt-first 5 '(a b)) '(a b)))
(assert-event (equal (dlt-first 0 '(a b)) nil))
(assert-event (equal (dlt-first-loop 2 '(a b c) nil) '(a b)))

; 6. :sum (a count).

(def-loop dlt-count-ints (xs)
  :shape :sum :elt e :body (if (integerp e) 1 0))

(assert-event (equal (dlt-count-ints '(1 a 2 b 3)) 3))
(assert-event (equal (dlt-count-ints nil) 0))
(assert-event (equal (dlt-count-ints-loop '(1 a 2) 0) 2))
(assert-event (equal (dlt-count-ints-loop '(1 a 2) 10) 12))
; The literal sum bridge, including its numeric accumulator hypothesis.
(assert-event
 (and (acl2-numberp 10)
      (equal (dlt-count-ints-loop '(1 a 2) 10)
             (+ 10 (dlt-count-ints '(1 a 2))))))


; 7. :map with a guard that the body needs, and :into the octet buffer.

(defun dlt-octet-of (x)
  (declare (xargs :guard (natp x)))
  (if (< x 256) x 0))

(defun dlt-nat-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs) (and (natp (car xs)) (dlt-nat-listp (cdr xs))) t))

(def-loop dlt-octets-of (xs)
  :shape :map :elt x :body (dlt-octet-of x)
  :guard (dlt-nat-listp xs) :guard-theory (dlt-nat-listp))

(assert-event (equal (dlt-octets-of '(1 256 300)) '(1 0 0)))

(def-loop dlt-write-octets (xs fn-octets)
  :shape :into :into fn-octets
  :write fn-octets-append-octet
  :write-theory (fn-octets-append-octet fn-octets$a-append-octet fn-oct-snoc-is-append)
  :map dlt-octets-of
  :elt x :body (dlt-octet-of x)
  :guard (dlt-nat-listp xs)
  :guard-hints (("Goal" :in-theory (enable fn-cbor-octetp dlt-octet-of))))

(defun dlt-write-run (xs)
  (declare (xargs :guard (dlt-nat-listp xs)))
  (with-local-stobj fn-octets
    (mv-let (out fn-octets)
      (let ((fn-octets (dlt-write-octets xs fn-octets)))
        (mv (fn-octets-list fn-octets) fn-octets))
      out)))

(assert-event (equal (dlt-write-run '(1 256 300)) '(1 0 0)))
(assert-event (equal (dlt-write-run nil) nil))

; The stobj's logical value cannot be passed to an ordinary evaluated
; term. THM evaluates this ground conjunction through the logical executable
; counterparts; ASSERT-EVENT checks its successful error-triple result.
(assert-event
 (thm (and (true-listp '(9 8))
           (equal (dlt-write-octets '(1 256 300) '(9 8))
                  (append '(9 8) (dlt-octets-of '(1 256 300))))))
 :stobjs-out :auto)

; The meaning theorem is exported, over the buffer's logical list.
(defthm dlt-write-octets-meaning-at-a-constant
  (implies (true-listp fn-octets)
           (equal (dlt-write-octets '(1 256 300) fn-octets)
                  (append fn-octets '(1 0 0))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance dlt-write-octets-is-append (xs '(1 256 300)))))))

; -----------------------------------------------------------------------------
; 8. Teeth.  A loop that conses the wrong element has no bridge: the
; functional instance's obligation (the loop's definitional equation under
; the substitution) fails, so the generated bridge is not vacuous.

(defun dlt-pairs-bad-loop (ring account acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp ring)
      (dlt-pairs-bad-loop (cdr ring) account (cons (cons account (car ring)) acc))
    (revappend acc nil)))

; @mutation-witness
(must-fail-checked
 (defthm dlt-pairs-bad-loop-is-revappend
   (equal (dlt-pairs-bad-loop ring account acc) (revappend acc (dlt-pairs ring account)))
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance
                    fn-dl-map-loop-is-revappend
                    (fn-dl-while (lambda (ring) t))
                    (fn-dl-stop (lambda (ring) nil))
                    (fn-dl-stop-value (lambda (ring) nil))
                    (fn-dl-keep (lambda (ring) t))
                    (fn-dl-f (lambda (ring) (cons (car ring) account)))
                    (fn-dl-tail (lambda (ring) nil))
                    (fn-dl-map (lambda (ring) (dlt-pairs ring account)))
                    (fn-dl-map-loop (lambda (ring acc) (dlt-pairs-bad-loop ring account acc))))
                   (dl-xs ring) (dl-acc acc)))
            :in-theory (union-theories '(dlt-pairs dlt-pairs-bad-loop) (theory 'minimal-theory))))))

; And the mutant is in fact different: evaluated, not only unproved.
(assert-event (not (equal (dlt-pairs-bad-loop '(1 2) 9 nil) (dlt-pairs '(1 2) 9))))

; A wrong bridge statement (the recursion's result consed onto a constant)
; is refused for a generated instance too.
; @mutation-witness
(must-fail-checked
 (defthm dlt-pairs-loop-is-not-shifted
   (equal (dlt-pairs-loop ring account acc) (revappend acc (cons 0 (dlt-pairs ring account))))
   :hints (("Goal" :in-theory (enable dlt-pairs-loop)))))

; -----------------------------------------------------------------------------
; 9. Refusals at expansion, each by the check that names it.

(must-fail-checked
 (def-loop dlt-r1 (xs) :shape :fold :elt e :body e)
 :unchecked "refused at expansion: an unknown shape")
(must-fail-checked
 (def-loop dlt-r2 (xs) :shape :map :over ys :elt e :body e)
 :unchecked "refused at expansion: :over is not a formal")
(must-fail-checked
 (def-loop dlt-r3 (xs acc) :shape :map :elt e :body e)
 :unchecked "refused at expansion: the accumulator is among the formals")
(must-fail-checked
 (def-loop dlt-r4 (xs) :shape :map :elt e)
 :unchecked "refused at expansion: no :body")
(must-fail-checked
 (def-loop dlt-r5 (xs) :shape :map :elt e :body e :stop (null (car xs)))
 :unchecked "refused at expansion: :stop without :stop-value")
(must-fail-checked
 (def-loop dlt-r6 (n xs) :shape :take :count n :over xs :elt e :body e :keep (integerp e))
 :unchecked "refused at expansion: :keep on a shape that has none")
(must-fail-checked
 (def-loop dlt-r7 (xs) :shape :sum :elt e :body 1 :tail (list 0))
 :unchecked "refused at expansion: :tail on a shape that has none")
(must-fail-checked
 (def-loop dlt-r8 (xs fn-octets) :shape :into :into fn-octets :elt e :body e)
 :unchecked "refused at expansion: :into without :write and :map")

(must-fail-checked
 (def-loop dlt-r9 (xs ordinary-buffer)
   :shape :into :into ordinary-buffer
   :write fn-octets-append-octet
   :write-theory (fn-octets-append-octet fn-octets$a-append-octet fn-oct-snoc-is-append)
   :map dlt-octets-of :elt x :body (dlt-octet-of x)
   :guard (dlt-nat-listp xs)
   :guard-hints (("Goal" :in-theory (enable fn-cbor-octetp dlt-octet-of))))
 :unchecked "refused by ACL2: :into names an ordinary variable, not a stobj; all options are present")

; -----------------------------------------------------------------------------
; 10. Hygiene: the loop is disabled after the form, the library's shapes
; stay disabled, and the generated row is in the world.

(assert-event (not (member-equal '(:definition dlt-pairs-loop) (current-theory-fn :here (w state)))))
(assert-event (not (member-equal '(:definition fn-dl-map) (current-theory-fn :here (w state)))))
(assert-event (not (member-equal '(:definition fn-dl-map-loop) (current-theory-fn :here (w state)))))
(assert-event (not (member-equal '(:rewrite fn-dl-map-loop-is-revappend) (current-theory-fn :here (w state)))))
(assert-event (not (member-equal '(:rewrite fn-dl-take-loop-is-revappend) (current-theory-fn :here (w state)))))
(assert-event (not (member-equal '(:rewrite fn-dl-sum-loop-is-plus) (current-theory-fn :here (w state)))))
(assert-event (not (member-equal '(:rewrite fn-dl-into-loop-is-append) (current-theory-fn :here (w state)))))
(assert-event (equal (cdr (assoc-eq 'dlt-pairs (table-alist 'fn-generated (w state))))
                     '(:def-loop :shape :map :loop dlt-pairs-loop :bridge dlt-pairs-loop-is-revappend)))
(assert-event (equal (cdr (assoc-eq 'dlt-write-octets (table-alist 'fn-generated (w state))))
                     '(:def-loop :shape :into :bridge dlt-write-octets-is-append)))

; Gap 1: KEEP may name the skip branch, without moving NOT into the logic.
(def-loop dlt-skip-ints (xs)
  :shape :map :keep-order :skip-first :keep (integerp (car xs))
  :body (car xs))
(assert-event (equal (dlt-skip-ints '(1 a 2 b)) '(a b)))
(assert-event (equal (dlt-skip-ints nil) nil))
(assert-event (equal (dlt-skip-ints '(1 2)) nil))
(assert-event (equal (dlt-skip-ints-loop '(1 a 2 b) '(z))
                     (revappend '(z) (dlt-skip-ints '(1 a 2 b)))))
; @mutation-witness: swapping the meaning of KEEP keeps integers instead.
(def-loop dlt-keep-ints-mutant (xs)
  :shape :map :keep (integerp (car xs)) :body (car xs))
(assert-event (not (equal (dlt-keep-ints-mutant '(1 a))
                          (dlt-skip-ints '(1 a)))))
(must-fail-checked
 (defthm dlt-skip-ints-wrong-branch
   (equal (dlt-keep-ints-mutant-loop '(1 a) nil)
          (revappend nil (dlt-skip-ints '(1 a))))))
(must-fail-checked
 (def-loop dlt-bad-keep-order (xs) :shape :map :body (car xs)
   :keep-order :sideways)
 :unchecked "refused at expansion: :keep-order must be :cons-first or :skip-first")
(must-fail-checked
 (def-loop dlt-keep-order-on-sum (xs) :shape :sum :body 1
   :keep-order :skip-first)
 :unchecked "refused at expansion: :keep-order is a :map option")

; Gap 5: the base term and base-first branch survive expansion literally.
(def-loop dlt-take-base (n xs)
  :shape :take :count n :over xs :body (car xs)
  :base (or (not (posp n)) (atom xs)) :measure (nfix n))
(assert-event (equal (dlt-take-base 2 '(a b c)) '(a b)))
(assert-event (equal (dlt-take-base 9 '(a b)) '(a b)))
(assert-event (equal (dlt-take-base -1 '(a b)) nil))
(assert-event (equal (dlt-take-base 2 nil) nil))
(assert-event (equal (dlt-take-base-loop 2 '(a b c) '(z))
                     (revappend '(z) (dlt-take-base 2 '(a b c)))))
; @mutation-witness: stopping at one drops the last requested element.
(def-loop dlt-take-base-mutant (n xs)
  :shape :take :count n :over xs :body (car xs)
  :base (or (not (posp n)) (equal n 1) (atom xs)) :measure (nfix n))
(assert-event (not (equal (dlt-take-base-mutant 2 '(a b))
                          (dlt-take-base 2 '(a b)))))
(must-fail-checked
 (defthm dlt-take-base-mutant-bridge
   (equal (dlt-take-base-mutant-loop 2 '(a b) nil)
          (revappend nil (dlt-take-base 2 '(a b))))))
(must-fail-checked
 (def-loop dlt-base-on-sum (xs) :shape :sum :body 1 :base (atom xs))
 :unchecked "refused at expansion: :base is a :map or :take option")
(must-fail-checked
 (def-loop dlt-base-and-while (n xs) :shape :take :count n :over xs
   :body (car xs) :base (not (posp n)) :while (consp xs))
 :unchecked "refused at expansion: :base and :while are mutually exclusive")

; Gap 2: one LET binding translates identically to the existing LET* option.
(def-loop dlt-one-binding (keys table)
  :shape :map :let ((v (dlt-lookup (car keys) table))) :keep v :body v)
(assert-event (equal (dlt-one-binding '(a x c) '((a . 1) (c . 3))) '(1 3)))
(assert-event (equal (dlt-one-binding nil '((a . 1))) nil))
(assert-event (equal (dlt-one-binding-loop '(a x c) '((a . 1) (c . 3)) '(z))
                     (revappend '(z) (dlt-one-binding '(a x c) '((a . 1) (c . 3))))))
; @mutation-witness: pairing the key with the value changes each result.
(def-loop dlt-one-binding-mutant (keys table)
  :shape :map :let ((v (dlt-lookup (car keys) table))) :keep v :body (cons (car keys) v))
(assert-event (not (equal (dlt-one-binding-mutant '(a) '((a . 1)))
                          (dlt-one-binding '(a) '((a . 1))))))
(must-fail-checked
 (defthm dlt-one-binding-mutant-bridge
   (equal (dlt-one-binding-mutant-loop '(a) '((a . 1)) nil)
          (revappend nil (dlt-one-binding '(a) '((a . 1)))))))
(must-fail-checked
 (def-loop dlt-let-on-sum (xs) :shape :sum :let ((v (car xs))) :body 1)
 :unchecked "refused at expansion: :let is a :map option")

; Gap 3: an independently written loop guard, with the same map bridge.
(def-loop dlt-loop-guard (xs k)
  :shape :map :body k :guard (and (natp k) (true-listp xs))
  :loop-guard (and (natp k) (true-listp xs) (true-listp acc)))
(assert-event (equal (dlt-loop-guard '(a b) 7) '(7 7)))
(assert-event (equal (dlt-loop-guard-loop '(a b) 7 '(z))
                     (revappend '(z) (dlt-loop-guard '(a b) 7))))
(assert-event (equal (dlt-loop-guard nil 7) nil))
; @mutation-witness: dropping the accumulator conjunct leaves REVAPPEND's
; guard unjustified; ACC = 7 satisfies the mutant guard but not true-listp.
(defun dlt-loop-guard-mutant (xs k acc)
  (declare (xargs :guard (and (natp k) (true-listp xs)) :verify-guards nil))
  (if (consp xs) (dlt-loop-guard-mutant (cdr xs) k (cons k acc))
    (revappend acc nil)))
(assert-event (and (natp 7) (true-listp nil) (not (true-listp 7))))
(must-fail-checked (verify-guards dlt-loop-guard-mutant))
(must-fail-checked
 (def-loop dlt-loop-guard-on-sum (xs) :shape :sum :body 1 :loop-guard t)
 :unchecked "refused at expansion: :loop-guard is a :map option")

; Gap 6: per-element lists are concatenated in input order.
(def-loop dlt-concat (xs) :shape :concat :body (list (car xs) (car xs)))
(assert-event (equal (dlt-concat '(a b)) '(a a b b)))
(assert-event (equal (dlt-concat nil) nil))
(assert-event (equal (dlt-concat-loop '(a b) '(z y))
                     (revappend '(z y) (dlt-concat '(a b)))))
; @mutation-witness: collecting whole lists with CONS nests the output.
(def-loop dlt-concat-mutant (xs) :shape :map :body (list (car xs) (car xs)))
(assert-event (not (equal (dlt-concat-mutant '(a)) (dlt-concat '(a)))))
(must-fail-checked
 (defthm dlt-concat-mutant-bridge
   (equal (dlt-concat-mutant-loop '(a) nil) (revappend nil (dlt-concat '(a))))))
(must-fail-checked
 (def-loop dlt-concat-keep (xs) :shape :concat :body (list (car xs)) :keep (car xs))
 :unchecked "refused at expansion: :keep is a :map option")

; Gap 7: guard-T loops accept even an improper accumulator.
(def-loop dlt-fixed (xs) :shape :map :body (car xs) :acc-fix t)
(def-loop dlt-fixed-skip (xs) :shape :map :body (car xs) :acc-fix t
  :keep-order :skip-first :keep (integerp (car xs)))
(assert-event (equal (dlt-fixed '(a b)) '(a b)))
(assert-event (equal (dlt-fixed-loop '(a b) '(z . tail))
                     (revappend (true-list-fix '(z . tail)) (dlt-fixed '(a b)))))
(assert-event (equal (dlt-fixed-loop nil 7) nil))
(assert-event (equal (dlt-fixed-skip-loop '(1 a 2 b) '(z . tail)) '(z a b)))
; @mutation-witness: omitting TRUE-LIST-FIX from the implementation makes
; REVAPPEND unsafe under guard T; the literal bridge alone cannot verify it.
(defun dlt-fixed-mutant (xs acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs) (dlt-fixed-mutant (cdr xs) (cons (car xs) acc))
    (revappend acc nil)))
(assert-event (not (true-listp '(z . tail))))
(must-fail-checked (verify-guards dlt-fixed-mutant))
(must-fail-checked
 (def-loop dlt-fixed-bad-option (xs) :body (car xs) :acc-fix :sometimes)
 :unchecked "refused at expansion: :acc-fix must be t or nil")
(must-fail-checked
 (def-loop dlt-fixed-sum (xs) :shape :sum :body 1 :acc-fix t)
 :unchecked "refused at expansion: :acc-fix is a :map option")

; Gap 4: immutable stobj context is passed through a list traversal.
(defstobj dlt-context (dlt-value :initially 7))
(def-loop dlt-read-context (xs dlt-context)
  :shape :map :stobjs dlt-context :body (cons (car xs) (dlt-value dlt-context)))
(defun dlt-read-context-run (xs)
  (declare (xargs :guard t))
  (with-local-stobj dlt-context
    (mv-let (out dlt-context)
      (mv (list (dlt-read-context xs dlt-context)
                (dlt-read-context-loop xs dlt-context '(z))
                (dlt-value dlt-context)) dlt-context)
      out)))
(assert-event (equal (dlt-read-context-run '(a b))
                     '(((a . 7) (b . 7)) (z (a . 7) (b . 7)) 7)))
(assert-event (equal (dlt-read-context-run nil) '(nil (z) 7)))
; @mutation-witness: substituting 8 for the read value breaks the bridge;
; the concrete stobj's logical representation is (7).
(must-fail-checked
 (defthm dlt-read-context-mutant-bridge
   (equal (dlt-read-context-loop '(a) '(7) nil) '((a . 8)))))
(assert-event (thm (not (equal (dlt-read-context-loop '(a) '(7) nil) '((a . 8)))))
 :stobjs-out :auto)
(must-fail-checked
 (def-loop dlt-read-ordinary (xs ordinary) :body (car xs) :stobjs ordinary)
 :unchecked "refused at expansion: :stobjs must name distinct stobj formals")
(defmacro dlt-hidden-update (st) `(update-dlt-value 8 ,st))
(must-fail-checked
 (def-loop dlt-read-updater (xs dlt-context)
   :stobjs dlt-context :body (dlt-hidden-update dlt-context))
 :unchecked "refused at expansion: :stobjs is read-only, including macro-expanded updaters")

; :step :stobjs: read-only context in the base test, the emit test and the body.
(def-loop dlt-step-context (xs dlt-context)
  :shape :step :done (atom xs) :emit (not (equal (car xs) (dlt-value dlt-context)))
  :body (cons (car xs) (dlt-value dlt-context)) :next (cdr xs) :skip-next (cdr xs)
  :stobjs dlt-context :guard (true-listp xs))
(defun dlt-step-context-run (xs)
  (declare (xargs :guard (true-listp xs)))
  (with-local-stobj dlt-context
    (mv-let (out dlt-context)
      (mv (list (dlt-step-context xs dlt-context)
                (dlt-step-context-loop xs dlt-context '(z))) dlt-context)
      out)))
; positive: 7 is the stored value, so the 7s are skipped and the rest carry it
(assert-event (equal (dlt-step-context-run '(a 7 b))
                     '(((a . 7) (b . 7)) (z (a . 7) (b . 7)))))
; negative: a :step :stobjs naming a non-stobj formal, and an updater hidden in
; the emit test, are both refused at expansion
(must-fail-checked
 (def-loop dlt-step-ordinary (xs ordinary)
   :shape :step :done (atom xs) :body (car xs) :next (cdr xs) :stobjs ordinary)
 :unchecked "refused at expansion: :stobjs must name distinct stobj formals")
(must-fail-checked
 (def-loop dlt-step-updater (xs dlt-context)
   :shape :step :done (atom xs) :emit (dlt-hidden-update dlt-context)
   :body (car xs) :next (cdr xs) :stobjs dlt-context)
 :unchecked "refused at expansion: :stobjs is read-only, including macro-expanded updaters")
(must-fail-checked
 (def-loop dlt-fold-with-stobjs (xs dlt-context)
   :shape :sum :body 1 :stobjs dlt-context)
 :unchecked "refused at expansion: :stobjs is a read-only :map or :step option")

; :map :base: base-first stopping, with a nonempty tail and extra context.
(def-loop dlt-map-base (xs tail)
  :shape :map :base (or (atom xs) (equal (car xs) :end))
  :body (car xs) :tail tail)
(assert-event (equal (dlt-map-base nil '(tail)) '(tail)))
(assert-event (equal (dlt-map-base '(:end a) '(tail)) '(tail)))
(assert-event (equal (dlt-map-base '(a b :end c) '(tail)) '(a b tail)))
(assert-event (equal (dlt-map-base '(a b) '(tail)) '(a b tail)))
(assert-event
 (equal (dlt-map-base-loop '(a b :end c) '(tail) '(y x))
        (revappend '(y x) (dlt-map-base '(a b :end c) '(tail)))))
(assert-event (equal (dlt-map-base-loop nil '(tail) '(y x)) '(x y tail)))
(assert-event (equal (dlt-map-base-loop '(:end a) '(tail) '(y x)) '(x y tail)))

; INNER remains the existing map shape: LET, STOP, both KEEP orders,
; and the accumulator convention compose with the new outer base.
(def-loop dlt-map-base-filter (xs)
  :base (or (atom xs) (equal (car xs) :end))
  :let ((e (car xs))) :keep (integerp e) :body e
  :stop (equal e :stop) :stop-value (list e) :tail (list :tail))
(def-loop dlt-map-base-skip (xs)
  :base (or (atom xs) (equal (car xs) :end))
  :let ((e (car xs))) :keep-order :skip-first :keep (not (integerp e)) :body e
  :stop (equal e :stop) :stop-value (list e) :tail (list :tail))
(def-loop dlt-map-base-fixed (xs)
  :base (or (atom xs) (equal (car xs) :end))
  :let ((e (car xs))) :keep (integerp e) :body e :acc-fix t
  :stop (equal e :stop) :stop-value (list e) :tail (list :tail))
(def-loop dlt-map-base-skip-fixed (xs)
  :base (or (atom xs) (equal (car xs) :end))
  :let ((e (car xs))) :keep-order :skip-first :keep (not (integerp e)) :body e
  :acc-fix t :stop (equal e :stop) :stop-value (list e) :tail (list :tail))
(assert-event
 (and (equal (dlt-map-base-filter '(1 a 2 :end 3)) '(1 2 :tail))
      (equal (dlt-map-base-skip '(1 a 2 :end 3)) '(1 2 :tail))
      (equal (dlt-map-base-fixed-loop '(1 a :stop 2) '(z . bad)) '(z 1 :stop))
      (equal (dlt-map-base-skip-fixed-loop '(1 a :stop 2) '(z . bad)) '(z 1 :stop))
      (equal (dlt-map-base-fixed-loop '(1 a :end 2) '(z . bad)) '(z 1 :tail))
      (equal (dlt-map-base-skip-fixed-loop '(1 a :end 2) '(z . bad)) '(z 1 :tail))))

(def-loop dlt-map-base-context (xs dlt-context)
  :base (or (atom xs) (equal (car xs) (dlt-value dlt-context)))
  :stobjs dlt-context :body (car xs))
(defun dlt-map-base-context-run (xs)
  (declare (xargs :guard t))
  (with-local-stobj dlt-context
    (mv-let (out dlt-context)
      (mv (dlt-map-base-context xs dlt-context) dlt-context)
      out)))
(assert-event (equal (dlt-map-base-context-run '(1 7 2)) '(1)))

; MUTATION / @mutation-witness: dropping TAIL at the base loses output,
; including when the base fires before any element is visited. The executed
; inequality names the counterexample; proof search failure alone is not it.
(defun dlt-map-base-drop-tail-loop (xs tail acc)
  (declare (xargs :guard (true-listp acc)) (irrelevant tail))
  (if (or (atom xs) (equal (car xs) :end))
      (revappend acc nil)
    (dlt-map-base-drop-tail-loop (cdr xs) tail (cons (car xs) acc))))
(assert-event
 (not (equal (dlt-map-base-drop-tail-loop '(:end a) '(tail) '(z))
             (revappend '(z) (dlt-map-base '(:end a) '(tail))))))
(must-fail-checked
 (defthm dlt-map-base-drop-tail-bridge
   (equal (dlt-map-base-drop-tail-loop xs tail acc)
          (revappend acc (dlt-map-base xs tail)))
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance
                    fn-dl-map-base-loop-is-revappend
                    (fn-dl-mb-base (lambda (xs) (or (atom xs) (equal (car xs) :end))))
                    (fn-dl-mb-fixp (lambda () nil))
                    (fn-dl-stop (lambda (xs) nil))
                    (fn-dl-stop-value (lambda (xs) nil))
                    (fn-dl-keep (lambda (xs) t))
                    (fn-dl-f (lambda (xs) (car xs)))
                    (fn-dl-tail (lambda (xs) tail))
                    (fn-dl-map-base (lambda (xs) (dlt-map-base xs tail)))
                    (fn-dl-map-base-loop (lambda (xs acc) (dlt-map-base-drop-tail-loop xs tail acc))))
                   (dl-xs xs) (dl-acc acc)))
            :in-theory (union-theories '(dlt-map-base dlt-map-base-drop-tail-loop)
                                       (theory 'minimal-theory))))))
(must-fail-checked
 (def-loop dlt-map-base-and-while (xs) :body (car xs)
   :base (atom xs) :while (consp xs))
 :unchecked "refused at expansion: :base and :while are mutually exclusive")
(must-fail-checked
 (def-loop dlt-map-base-and-while-t (xs) :body (car xs)
   :base (atom xs) :while t)
 :unchecked "refused at expansion: explicitly supplied :while t excludes :base too")
(must-fail-checked
 (def-loop dlt-base-on-into (xs fn-octets) :shape :into :body (car xs)
   :base (atom xs) :into fn-octets :write fn-octets-append-octet :map dlt-octets)
 :unchecked "refused at expansion: :base is a :map or :take option")

; NIL is still a supplied base term, not a way to bypass shape validation.
(must-fail-checked
 (def-loop dlt-nil-base-on-sum (xs) :shape :sum :body 1 :base nil)
 :unchecked "refused at expansion: :base is a :map or :take option, even for NIL")
(must-fail-checked
 (def-loop dlt-nil-base-on-into (xs fn-octets) :shape :into :body (car xs)
   :base nil :into fn-octets :write fn-octets-append-octet :map dlt-octets)
 :unchecked "refused at expansion: :base is a :map or :take option, even for NIL")

; -----------------------------------------------------------------------------
; 11. :step --- an advance other than (cdr XS).  One library theorem
; (`fn-dl-step-loop-is-revappend'); an instance owes the two progress facts
; its own termination proof owes.

(defun dlt-byte (b) (declare (xargs :guard t)) (if (equal b 9) 32 b))

; cddr
(def-loop dlt-evens (xs) :shape :step :done (atom xs) :elt e :body e :next (cddr xs)
  :guard (true-listp xs))
(assert-event (equal (dlt-evens '(1 2 3 4 5)) '(1 3 5)))
(assert-event (equal (dlt-evens '(1 2 3 4)) '(1 3)))
(assert-event (equal (dlt-evens nil) nil))
(assert-event (equal (dlt-evens-loop '(1 2 3) '(z)) (revappend '(z) (dlt-evens '(1 2 3)))))

; a skip with its own advance (the `fn-nov-scrub' shape)
(def-loop dlt-scrub (bytes)
  :shape :step :done (atom bytes)
  :skip (and (equal (car bytes) 13) (consp (cdr bytes)) (equal (cadr bytes) 10))
  :body (dlt-byte (car bytes)) :next (cdr bytes) :skip-next (cddr bytes)
  :guard (true-listp bytes))
(assert-event (equal (dlt-scrub '(1 13 10 9 13 2)) '(1 32 13 2)))
(assert-event (equal (dlt-scrub '(13 10)) nil))
(assert-event (equal (dlt-scrub-loop '(1 13 10 9) nil) (dlt-scrub '(1 13 10 9))))

; index up, the measure supplied (the `fn-lgs-range' shape)
(def-loop dlt-range (from to)
  :shape :step :over from :done (not (and (natp from) (natp to) (<= from to)))
  :body from :next (1+ from) :measure (nfix (- (+ 1 (nfix to)) (nfix from)))
  :guard (and (natp from) (natp to)))
(assert-event (equal (dlt-range 2 5) '(2 3 4 5)))
(assert-event (equal (dlt-range 5 2) nil))

; two formals advance together, a :let shared by test and element
(def-loop dlt-head-n (xs n)
  :shape :step :over (xs n) :done (or (atom xs) (zp n)) :elt e :body e
  :next ((cdr xs) (- n 1)) :measure (nfix n)
  :guard (and (true-listp xs) (natp n)))
(assert-event (equal (dlt-head-n '(a b c) 2) '(a b)))
(assert-event (equal (dlt-head-n-loop '(a b c) 2 nil) '(a b)))

(assert-event (equal (cdr (assoc-eq 'dlt-scrub (table-alist 'fn-generated (w state))))
                     '(:def-loop :shape :step :loop dlt-scrub-loop :bridge dlt-scrub-loop-is-revappend)))
(assert-event (not (member-equal '(:rewrite fn-dl-step-loop-is-revappend) (current-theory-fn :here (w state)))))
(assert-event (not (member-equal '(:definition dlt-scrub-loop) (current-theory-fn :here (w state)))))

(local (defthm dlt-sc-natp (natp (acl2-count bytes)) :rule-classes nil))
(local (defthm dlt-sc-emit
         (implies (and (not (atom bytes))
                       (not (not (and (equal (car bytes) 13) (consp (cdr bytes))
                                      (equal (cadr bytes) 10)))))
                  (< (acl2-count (cdr bytes)) (acl2-count bytes)))
         :rule-classes nil))
(local (defthm dlt-sc-skip
         (implies (and (not (atom bytes))
                       (not (not (not (and (equal (car bytes) 13) (consp (cdr bytes))
                                           (equal (cadr bytes) 10))))))
                  (< (acl2-count (cddr bytes)) (acl2-count bytes)))
         :rule-classes nil))

; The library theorem at an instance, as the book states it (the generated
; bridge is local): the loop is the recursion with the accumulator reversed
; on, for every input.
(defthm dlt-scrub-loop-is-revappend
  (equal (dlt-scrub-loop bytes acc) (revappend acc (dlt-scrub bytes)))
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance
                   fn-dl-step-loop-is-revappend
                   (fn-dl-sp-done (lambda (bytes) (atom bytes)))
                   (fn-dl-sp-emit (lambda (bytes)
                                    (not (and (equal (car bytes) 13) (consp (cdr bytes))
                                              (equal (cadr bytes) 10)))))
                   (fn-dl-sp-f (lambda (bytes) (dlt-byte (car bytes))))
                   (fn-dl-sp-tail (lambda (bytes) nil))
                   (fn-dl-sp-ne (lambda (bytes) (cdr bytes)))
                   (fn-dl-sp-ns (lambda (bytes) (cddr bytes)))
                   (fn-dl-sp-m (lambda (bytes) (acl2-count bytes)))
                   (fn-dl-step (lambda (bytes) (dlt-scrub bytes)))
                   (fn-dl-step-loop (lambda (bytes acc) (dlt-scrub-loop bytes acc))))
                  (dl-s bytes) (dl-acc acc)))
           :expand ((dlt-scrub-loop dl-s dl-acc) (dlt-scrub dl-s))
           :in-theory (union-theories '(car-cons cdr-cons) (theory 'minimal-theory)))
          (if stable-under-simplificationp
              '(:computed-hint-replacement nil
                :use ((:instance dlt-sc-emit (bytes dl-ps)) (:instance dlt-sc-skip (bytes dl-ps))
                      (:instance dlt-sc-natp (bytes dl-ps))))
            nil)))

; Teeth: the positive witness is inside the loop guard and satisfies the
; equation (the claim has no hypothesis: REVAPPEND ignores a final cdr, so
; the loop's guard on the accumulator is not needed for the equation); an
; accumulator order that appends instead of reversing falsifies the
; conclusion.
(defteeth dlt-scrub-loop-is-revappend
  :claim (() (equal (dlt-scrub-loop bytes acc) (revappend acc (dlt-scrub bytes))))
  :subject dlt-scrub
  :witness ((bytes '(1 13 10 9 2)) (acc '(z y)))
  :breaks ()
  :mutations ((order
               (:conclusion (equal (dlt-scrub-loop bytes acc) (append acc (dlt-scrub bytes))))
               ((bytes '(1 2)) (acc '(z y)))
               :fault "the accumulator appended in its own order instead of reversed onto the result")))

; Mutations of the instance: a loop that conses the wrong element, and a loop
; that advances by one where the recursion skips two, each have no bridge.
(defun dlt-scrub-bad-loop (bytes acc)
  (declare (xargs :guard (true-listp acc) :measure (acl2-count bytes)))
  (if (atom bytes) (revappend acc nil)
    (dlt-scrub-bad-loop (cdr bytes) (cons (car bytes) acc))))

; @mutation-witness
(must-fail-checked
 (defthm dlt-scrub-bad-loop-is-revappend
   (equal (dlt-scrub-bad-loop bytes acc) (revappend acc (dlt-scrub bytes)))
   :hints (("Goal" :in-theory (enable dlt-scrub dlt-scrub-bad-loop)
            :induct (dlt-scrub-bad-loop bytes acc))))
 :step-limit 20000)
(assert-event (not (equal (dlt-scrub-bad-loop '(9) nil) (dlt-scrub '(9)))))

; A :next that does not shrink the measure is refused by the instance's own
; termination proof.
; @mutation-witness
(must-fail-checked
 (def-loop dlt-step-stuck (xs) :shape :step :done (atom xs) :elt e :body e :next xs)
 :unchecked "the progress obligation of :step fails: :next leaves the measure where it was")

; Refusals at expansion.
(must-fail-checked
 (def-loop dlt-step-no-done (xs) :shape :step :elt e :body e :next (cdr xs))
 :unchecked "refused at expansion: :step needs :done and :next")
(must-fail-checked
 (def-loop dlt-step-emit-and-skip (xs) :shape :step :done (atom xs) :emit (car xs)
   :skip (cdr xs) :body 1 :next (cdr xs))
 :unchecked "refused at expansion: :emit and :skip together")
(must-fail-checked
 (def-loop dlt-step-short-next (xs n) :shape :step :over (xs n) :done (atom xs) :body 1
   :next ((cdr xs)))
 :unchecked "refused at expansion: one :next term per :over formal")
(must-fail-checked
 (def-loop dlt-map-with-done (xs) :shape :map :done (atom xs) :body (car xs))
 :unchecked "refused at expansion: :done is a :step or :fold option")

; -----------------------------------------------------------------------------
; 12. :fold --- a stobj threaded through each element, rows collected, a
; failure value that stops the loop.  One library theorem
; (`fn-dl-fold-loop-is-revappend').

(defstobj dlt-ctr (dlt-n :type integer :initially 0))

(defun dlt-row (w k dlt-ctr)
  (declare (xargs :stobjs dlt-ctr :guard (and (natp k) (dlt-ctrp dlt-ctr))))
  (let ((dlt-ctr (update-dlt-n (+ (nfix k) (dlt-n dlt-ctr)) dlt-ctr)))
    (if (equal w 0) (mv :bad dlt-ctr) (mv (fix w) dlt-ctr))))

(def-loop dlt-rows (ws k dlt-ctr)
  :shape :fold :over ws :st dlt-ctr :done (atom ws) :elt w
  :row (dlt-row w k dlt-ctr) :next (cdr ws)
  :guard (and (natp k) (dlt-ctrp dlt-ctr)))

; the stobj ends at the sum of the steps taken (a failure stops its count)
(defun dlt-all (ws k dlt-ctr)
  (declare (xargs :stobjs dlt-ctr :guard (and (natp k) (dlt-ctrp dlt-ctr))))
  (mv-let (rows dlt-ctr) (dlt-rows ws k dlt-ctr)
    (mv rows (dlt-n dlt-ctr) dlt-ctr)))

(defun dlt-run (ws k)
  (declare (xargs :guard (and (true-listp ws) (natp k))))
  (with-local-stobj dlt-ctr
    (mv-let (rows n dlt-ctr)
      (dlt-all ws k dlt-ctr)
      (mv rows n))))

(assert-event (mv-let (r n) (dlt-run '(1 2 3) 5) (and (equal r '(1 2 3)) (equal n 15))))
(assert-event (mv-let (r n) (dlt-run nil 5) (and (equal r nil) (equal n 0))))
(assert-event (mv-let (r n) (dlt-run '(1 0 3) 5) (and (equal r :bad) (equal n 10))))
(defun dlt-all-loop (ws k acc dlt-ctr)
  (declare (xargs :stobjs dlt-ctr :guard (and (natp k) (dlt-ctrp dlt-ctr) (true-listp acc))))
  (mv-let (rows dlt-ctr) (dlt-rows-loop ws k dlt-ctr acc)
    (mv rows (dlt-n dlt-ctr) dlt-ctr)))
(defun dlt-run-loop (ws k acc)
  (declare (xargs :guard (and (true-listp ws) (natp k) (true-listp acc))))
  (with-local-stobj dlt-ctr
    (mv-let (rows n dlt-ctr) (dlt-all-loop ws k acc dlt-ctr) (mv rows n))))
(assert-event (mv-let (r n) (dlt-run-loop '(4 5) 1 '(z)) (and (equal r '(z 4 5)) (equal n 2))))

(assert-event (equal (cdr (assoc-eq 'dlt-rows (table-alist 'fn-generated (w state))))
                     '(:def-loop :shape :fold :loop dlt-rows-loop :bridge dlt-rows-loop-is-revappend)))
(assert-event (not (member-equal '(:rewrite fn-dl-fold-loop-is-revappend) (current-theory-fn :here (w state)))))

; Teeth.  A loop that leaves the rows reversed has no bridge to the recursion.
(defun dlt-rows-bad-loop (ws k dlt-ctr acc)
  (declare (xargs :stobjs dlt-ctr :guard (and (natp k) (dlt-ctrp dlt-ctr) (true-listp acc))
                  :measure (acl2-count ws)))
  (if (atom ws)
      (mv acc dlt-ctr)
    (mv-let (dl-row dlt-ctr) (dlt-row (car ws) k dlt-ctr)
      (if (eq dl-row :bad)
          (mv :bad dlt-ctr)
        (dlt-rows-bad-loop (cdr ws) k dlt-ctr (cons dl-row acc))))))

; @mutation-witness
(must-fail-checked
 (defthm dlt-rows-bad-loop-is-revappend
   (equal (dlt-rows-bad-loop ws k dlt-ctr acc)
          (mv-let (r a) (dlt-rows ws k dlt-ctr)
            (mv (if (eq r :bad) :bad (revappend acc r)) a)))
   :hints (("Goal" :induct (dlt-rows-bad-loop ws k dlt-ctr acc)
            :in-theory (enable dlt-rows dlt-rows-bad-loop))))
 :step-limit 20000)
(defun dlt-all-bad (ws k dlt-ctr)
  (declare (xargs :stobjs dlt-ctr :guard (and (natp k) (dlt-ctrp dlt-ctr))))
  (mv-let (rows dlt-ctr) (dlt-rows-bad-loop ws k dlt-ctr nil)
    (mv rows (dlt-n dlt-ctr) dlt-ctr)))
(defun dlt-run-bad (ws k)
  (declare (xargs :guard (and (true-listp ws) (natp k))))
  (with-local-stobj dlt-ctr
    (mv-let (rows n dlt-ctr) (dlt-all-bad ws k dlt-ctr) (mv rows n))))
(assert-event (mv-let (r n) (dlt-run-bad '(4 5) 1) (and (equal r '(5 4)) (equal n 2))))

; Refusals at expansion.
(must-fail-checked
 (def-loop dlt-fold-no-st (ws k dlt-ctr) :shape :fold :done (atom ws)
   :row (dlt-row (car ws) k dlt-ctr) :next (cdr ws))
 :unchecked "refused at expansion: :fold needs :st, :row, :done and :next")
(must-fail-checked
 (def-loop dlt-fold-st-is-over (ws k dlt-ctr) :shape :fold :over (ws dlt-ctr) :st dlt-ctr
   :done (atom ws) :row (dlt-row (car ws) k dlt-ctr) :next ((cdr ws) dlt-ctr))
 :unchecked "refused at expansion: :st must not be one of the :over formals")
(must-fail-checked
 (def-loop dlt-fold-with-body (ws k dlt-ctr) :shape :fold :st dlt-ctr :done (atom ws)
   :row (dlt-row (car ws) k dlt-ctr) :body (car ws) :next (cdr ws))
 :unchecked "refused at expansion: :fold takes :row, not :body")
(must-fail-checked
 (def-loop dlt-map-with-row (xs) :shape :map :body (car xs) :row (car xs))
 :unchecked "refused at expansion: :row is a :fold option")

; -----------------------------------------------------------------------------
; 13. :foldr --- a right fold with a non-list accumulator, executed as a left
; fold over the reversal.  One library theorem (`fn-dl-foldr-loop-is-foldr`).

(defun dlt-fput (x trie) (declare (xargs :guard t)) (cons (fix x) trie))
(defun dlt-rev (x y)
  (declare (xargs :guard t))
  (if (consp x) (dlt-rev (cdr x) (cons (car x) y)) y))

; the order is observable: the fold of (1 2 3) puts 3 first
(def-loop dlt-fold-put (xs base)
  :shape :foldr :over xs :elt e :combine (dlt-fput e acc) :init base
  :rev dlt-rev)

(assert-event (equal (dlt-fold-put '(1 2 3) '(z)) '(1 2 3 z)))
(assert-event (equal (dlt-fold-put nil '(z)) '(z)))
(assert-event (equal (dlt-fold-put '(1 2 . 3) nil) '(1 2)))
(assert-event (equal (dlt-fold-put-loop '(3 2 1) '(z) '(z)) '(1 2 3 z)))
(assert-event (equal (cdr (assoc-eq 'dlt-fold-put (table-alist 'fn-generated (w state))))
                     '(:def-loop :shape :foldr :loop dlt-fold-put-loop :bridge dlt-fold-put-loop-is-dlt-fold-put)))
(assert-event (not (member-equal '(:rewrite fn-dl-foldr-loop-is-foldr) (current-theory-fn :here (w state)))))

; a number accumulator, the default reverse (the guard supplies a true list)
(def-loop dlt-fold-count (xs)
  :shape :foldr :over xs :elt e :combine (+ 1 (nfix acc)) :init 0 :guard (true-listp xs))
(assert-event (equal (dlt-fold-count '(a b c)) 3))

; Mutations: a loop that folds the unreversed list (the accumulator order is
; wrong) has no bridge, and a combine that is not the loop's step does not
; either.
(defun dlt-fold-put-bad-loop (xs base acc)
  (declare (xargs :guard t) (ignorable xs base))
  (if (consp xs) (dlt-fold-put-bad-loop (cdr xs) base (dlt-fput (car xs) acc)) acc))

; @mutation-witness
(must-fail-checked
 (defthm dlt-fold-put-bad-loop-is-fold
   (equal (dlt-fold-put-bad-loop xs base base) (dlt-fold-put xs base))
   :hints (("Goal" :in-theory (enable dlt-fold-put dlt-fold-put-bad-loop)
            :induct (dlt-fold-put xs base))))
 :step-limit 20000)
(assert-event (not (equal (dlt-fold-put-bad-loop '(1 2 3) '(z) '(z)) (dlt-fold-put '(1 2 3) '(z)))))

; Refusals at expansion.
(must-fail-checked
 (def-loop dlt-foldr-no-combine (xs) :shape :foldr :elt e :init nil)
 :unchecked "refused at expansion: :foldr needs :elt and :combine")
(must-fail-checked
 (def-loop dlt-foldr-with-body (xs) :shape :foldr :elt e :combine (cons e acc) :init nil :body e)
 :unchecked "refused at expansion: :foldr takes :combine and :init, not :body")
(must-fail-checked
 (def-loop dlt-map-with-combine (xs) :shape :map :body (car xs) :combine (car xs))
 :unchecked "refused at expansion: :combine is a :foldr option")
