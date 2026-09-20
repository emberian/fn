; What `fn-defrecord' generates, proved once here so no later book proves it
; again.
;
; Three records exercise the three shapes the tree actually uses: an untagged
; three-field record, a tagged record whose field is itself a record (the
; nested case: the recognizer of the outer names the recognizer of the inner),
; and an enum field (a membership predicate, the `fn-sched-classp' shape).
;
; The teeth are the point.  A generated lemma that happens to hold vacuously
; would certify; each `assert-event' below is a concrete value on which the
; generated event has to be doing work:
;
;   * the accessor of a constructor returns the field, on a value built from
;     five distinct constants;
;   * the accessors are total: outside the shape they return without an
;     error, which is what `:guard t' buys and what a raw `car' would not;
;   * the recognizer refuses a value of the wrong length, a value with the
;     wrong tag, and a value whose enum field is not in the enumeration ---
;     one violating value per recognizer conjunct;
;   * injectivity separates two constructions that differ in one field.
;
; The forward-chaining facts are checked by `fn-drt-projection-needs-consp'
; below, which is the shape of the includer failure that motivated them
; (proof-style section 1: `fn-nntp-group-low-is-available' failed for want of
; `(consp a)' once the accessors were opaque).  It is proved with the record
; CLOSED; if the generated forward rules were missing or were rewrite rules
; rather than forward-chaining rules, it would not close.

(in-package "ACL2")
(include-book "../../books/acceptance-alloc")
(include-book "../../books/defrecord")

; -----------------------------------------------------------------------------
; 1. A three-field untagged record, the `fn-sched-result' shape.

(fn-defrecord fn-drt-point
  :constructor (fn-drt-point x-coord y-coord label)
  :fields ((fn-drt-point-x natp)
           (fn-drt-point-y natp)
           (fn-drt-point-label stringp)))

; -----------------------------------------------------------------------------
; 2. An enum field: the type entry is an ordinary unary predicate, so an
; enumeration is a predicate like any other and needs nothing from the macro.

(defun fn-drt-colorp (c)
  (declare (xargs :guard t))
  (if (member-equal c '(:red :green :blue)) t nil))

; 3. A tagged record with a nested record field and an enum field.  The
; `:extra' conjunct is a whole-record constraint in accessor vocabulary, the
; same way `fn-sched-contactp' constrains start against end.

(fn-defrecord fn-drt-mark
  :tag :fn-drt-mark
  :constructor (fn-drt-mark origin color weight)
  :fields ((fn-drt-mark-origin fn-drt-pointp)
           (fn-drt-mark-color fn-drt-colorp)
           (fn-drt-mark-weight posp))
  :extra ((<= (fn-drt-mark-weight x) 1000)))

; -----------------------------------------------------------------------------
; The generated names exist and say what section 1 says they say.  Each of
; these is `:rule-classes nil': they are an audit of the macro's output, not
; rules, and this book exports nothing.

(defthm fn-drt-generated-record-lemmas
  (and (fn-drt-point-shapep (fn-drt-point a b c))
       (equal (fn-drt-point-x (fn-drt-point a b c)) a)
       (equal (fn-drt-point-y (fn-drt-point a b c)) b)
       (equal (fn-drt-point-label (fn-drt-point a b c)) c)
       (fn-drt-mark-shapep (fn-drt-mark o k w))
       (equal (fn-drt-mark-origin (fn-drt-mark o k w)) o)
       (equal (fn-drt-mark-color (fn-drt-mark o k w)) k)
       (equal (fn-drt-mark-weight (fn-drt-mark o k w)) w))
  :rule-classes nil)

; The tag really is at index 0 and the fields really are shifted by one, so
; the host encoding of a tagged record is unchanged by the macro.
(defthm fn-drt-tagged-layout-is-positional
  (equal (fn-drt-mark o k w) (list :fn-drt-mark o k w))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-drt-mark-internals))))

(defthm fn-drt-untagged-layout-is-positional
  (equal (fn-drt-point a b c) (list a b c))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-drt-point-internals))))

; Injectivity is generated `:rule-classes nil': a name for one includer's
; `:use', never a rewrite rule that fires on every constructor equality.
(defthm fn-drt-injectivity-is-usable
  (implies (not (equal x-coord x-coord-2))
           (not (equal (fn-drt-point x-coord y-coord label)
                       (fn-drt-point x-coord-2 y-coord label))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-drt-point-injective
                                   (y-coord-2 y-coord) (label-2 label))))))

; The withdrawal is real: with `fn-drt-point-internals' disabled --- which the
; macro leaves it --- nothing below opens the record, and this projection
; closes from the forward-chaining facts alone.  `(consp p)' is not available
; from type reasoning here; it arrives because `fn-drt-point-label' is a
; trigger term of the generated accessor rule.
(defthm fn-drt-projection-needs-consp
  (implies (stringp (fn-drt-point-label p))
           (consp p))
  :rule-classes nil)

(defthm fn-drt-recognizer-forwards-shape
  (implies (fn-drt-markp m)
           (and (consp m) (true-listp m)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Teeth: reachable witnesses, then one violating value per hypothesis.

(defconst *fn-drt-origin* (fn-drt-point 3 4 "origin"))
(defconst *fn-drt-mark* (fn-drt-mark *fn-drt-origin* :green 7))

(assert-event (fn-drt-pointp *fn-drt-origin*))
(assert-event (fn-drt-markp *fn-drt-mark*))
(assert-event (equal (fn-drt-point-x *fn-drt-origin*) 3))
(assert-event (equal (fn-drt-point-y *fn-drt-origin*) 4))
(assert-event (equal (fn-drt-point-label *fn-drt-origin*) "origin"))
(assert-event (equal (fn-drt-mark-origin *fn-drt-mark*) *fn-drt-origin*))
(assert-event (equal (fn-drt-mark-color *fn-drt-mark*) :green))
(assert-event (equal (fn-drt-mark-weight *fn-drt-mark*) 7))

; The accessors are total, which is the whole reason for the `mbe': an atom
; and a dotted pair are outside every shape and still answer.
(assert-event (equal (fn-drt-point-x 17) nil))
(assert-event (equal (fn-drt-point-label (cons 1 2)) nil))
(assert-event (equal (fn-drt-mark-weight :fn-drt-mark) nil))

; One violating value per recognizer conjunct of `fn-drt-markp'.
(assert-event (not (fn-drt-markp (list :fn-drt-mark *fn-drt-origin* :green))))
(assert-event (not (fn-drt-markp (list :fn-drt-other *fn-drt-origin* :green 7))))
(assert-event (not (fn-drt-markp (fn-drt-mark (list 3 4) :green 7))))
(assert-event (not (fn-drt-markp (fn-drt-mark *fn-drt-origin* :puce 7))))
(assert-event (not (fn-drt-markp (fn-drt-mark *fn-drt-origin* :green 0))))
(assert-event (not (fn-drt-markp (fn-drt-mark *fn-drt-origin* :green 1001))))

; ... and per conjunct of `fn-drt-pointp'.
(assert-event (not (fn-drt-pointp (list 3 4))))
(assert-event (not (fn-drt-pointp (fn-drt-point -1 4 "origin"))))
(assert-event (not (fn-drt-pointp (fn-drt-point 3 "four" "origin"))))
(assert-event (not (fn-drt-pointp (fn-drt-point 3 4 :origin))))

; Injectivity separates, on concrete values, in each field.
(assert-event (not (equal (fn-drt-point 3 4 "o") (fn-drt-point 5 4 "o"))))
(assert-event (not (equal (fn-drt-point 3 4 "o") (fn-drt-point 3 5 "o"))))
(assert-event (not (equal (fn-drt-point 3 4 "o") (fn-drt-point 3 4 "p"))))

; -----------------------------------------------------------------------------
; `fn-defrecord-export' names and withdraws exactly the recognizers it is
; given.  After this, a book above sees neither `fn-drt-pointp' nor
; `fn-drt-markp' opened.

(fn-defrecord-export fn-drt-vocabulary
  :records (fn-drt-point fn-drt-mark)
  :also (fn-drt-colorp))
