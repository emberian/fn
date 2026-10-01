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
