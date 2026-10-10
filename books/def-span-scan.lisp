; fn: `def-span-scan' --- loops over a span of an octet buffer, generated with
; their list-model bridge, their work bound and their guards (CONCEPT-01;
; RUNTIME-MODEL section 2).
;
; A span is a range [I, END) of an abstract stobj congruent to `fn-octets'
; (books/octets-stobj.lisp: a resizable (unsigned-byte 8) array with a fill
; count, whose logical value is the octet list).  At an action boundary the
; runtime names it by a handle (h g off len) (books/runtime-contract.lisp,
; `fn-rtc-handlep'); inside one call it is the buffer and two indices, with
; I = off and END = off + len.  The logical value of a span is
; `(fn-oct-slice-list I END ST)', which is `(take (- END I) (nthcdr I ST))'
; when END is within the buffer (`fn-oct-slice-list-is-take-nthcdr').
;
; Writes.  The output stobj's per-octet appends are gone from the :copy and
; :stream loops (landing 2, L2.0): the output is extended once by the exported
; zero-word append (`fn-dss-out-append-word 0 N'), each octet is one inline
; `put' at its index, and the fill point moves once more at the end (a :copy
; touches it not at all after the extend; a :stream truncates to the length
; written on every exit).  `put' and `truncate' are exports without `:protect'
; (books/octets-stobj.lisp, the atomicity line beside each).  The physical
; stores are the charge model NAME-WRITE-CHARGE, bounded by NAME-WRITE-CHARGE-BOUND.
; The :copy guard names CAP a 59-bit fixnum and the :stream guard names the
; output's length one (the index arithmetic is fixnum); both are guards of the
; executable, not of any theorem here.
;
; Each SHAPE is one family of loops.  Its executable form walks the array by
; index and, under A-BODY-COST below, conses nothing; its meaning is a recursion over the span's list;
; the BRIDGE between the two, the WORK bound and the other exported facts are
; proved ONCE in this book over constrained functions, and every instance
; obtains them by `:functional-instance' (books/def-loop.lisp's manner).  The
; obligations ACL2 generates for an instance are the definitional equations of
; the instance's functions under the substitution, which one unfold of each
; discharges in `minimal-theory', plus the shape's constraints on the body,
; which the instance's own hints discharge.  No instance writes an induction.
;
; Shapes (instance formals: CTX, the instance's own context formals, then the
; span formals):
;
;   :find    (NAME CTX.. I END fn-octets): the least K in [I, END) whose octet
;            satisfies BODY, else nil.  List model: the index of the first
;            element satisfying BODY.
;   :fold    (NAME CTX.. ACC I END fn-octets): BODY folded left over the span's
;            octets into ACC, a scalar of the instance's ACC-TYPE.  List model:
;            the left fold.
;   :equal   (NAME CTX.. I END fn-octets): whether the span, each octet mapped by
;            NORM (default the identity), is the constant C; or, with
;            :against :span, (NAME CTX.. I END fn-octets J fn-dss-b): whether
;            the two spans of equal length are equal under NORM.  List model:
;            `equal' of the normalized lists.
;   :copy    (NAME CTX.. I END CAP fn-octets fn-dss-out): append the span, each
;            octet mapped by MAP (default the identity), onto a DISTINCT
;            instance, or, with :within t, (NAME CTX.. I END CAP fn-octets) onto
;            the same instance from a source that lies wholly before its fill
;            point (END <= len at the call).  CAPACITY: the copy happens whole
;            when the destination's length plus (END - I) is at most CAP, and is
;            refused by name (:refused, destination unchanged) otherwise.
;            ALIASING: distinct instances are distinct live objects (ACL2's stobj
;            discipline refuses the same stobj for two formals); within one
;            instance every source index is below the fill point at the call,
;            so no octet is read after it is written.  `fn-octets-append-back''s
;            overlapping LZ semantics (each octet the one OFF back at the time
;            it is appended) is a different, named operation and not this shape.
;   :stream  (NAME CTX.. S I END LAST CAP fn-octets fn-dss-out): a bounded
;            transducer.  STEP (a function of S, the octet and CTX returning
;            (mv S' K W SIG)) is applied octet by octet: it emits the K <=
;            EMIT-MAX <= 7 low octets of W (little-endian, the
;            `fn-octets-append-word' encoding) onto the output and continues
;            (SIG 0), stops after the octet (SIG 1, :yield) or refuses it
;            (SIG 2, :refused: the octet is not consumed, nothing is written).
;            Before each octet the output must have room for EMIT-MAX more
;            octets under CAP, else the call stops with :need-output.  At END
;            the call answers :need-input, or, when LAST, applies FINAL, a
;            function of S returning (mv S' K W SIG): SIG 2 answers :refused
;            with nothing written (an incomplete frame at end of input), else
;            its K <= FINAL-MAX <= 7 octets are written and the call answers
;            :done; either way the state becomes S'.  A call whose
;            output room is below max(EMIT-MAX, FINAL-MAX) answers :no-room at
;            entry, consuming nothing (A-HOST-ROOM).  The result is
;            (mv SIGNAL S' I' fn-dss-out).  The state S is one value of the
;            instance's STATE-TYPE: the transducer's whole workspace.
;
; What every instance exports (the statements the generator prints; each the
; library theorem of its shape under the instance's substitution):
;
;   termination   the admission of NAME (measure (nfix (- END I)));
;   the bridge    NAME-IS-LIST: NAME equals the list model over the span;
;   work          NAME-WORK-BOUND: NAME-WORK <= c0 + c1 * (END - I), where
;                 NAME-WORK charges each octet the loop examines 1 plus the
;                 body's cost (the instance's :cost term, at most :cost-max, the
;                 BODY COST CONTRACT) and the exit 1; c1 = 1 + cost-max;
;   writes        stated separately: :find, :fold, :equal return no stobj (the
;                 buffer is borrowed, read only); :copy writes exactly END - I
;                 octets or none, and counts at most 2 (END - I) physical stores,
;                 the extend's zeroing included (NAME-WRITE-CHARGE-BOUND);
;                 :stream writes at most EMIT-MAX per consumed octet plus
;                 FINAL-MAX, and never past CAP (NAME-WRITES), and counts at
;                 most the zeroed window (CAP - len) plus those octets as
;                 physical stores (NAME-WRITE-CHARGE-BOUND, under the octet-list
;                 hypotheses of NAME-WRITES);
;   workspace     stated separately: the loop's indices and, for :fold, ACC
;                 (one ACC-TYPE scalar) and, for :stream, S (one STATE-TYPE
;                 value) and nothing else; NAME-ACC-TYPE / NAME-STATE-TYPE say
;                 the scalar stays in its type;
;   guards        verified, with I and END (unsigned-byte 59) fixnums declared
;                 in the loop and END within the buffer.
;
; :stream additionally exports the PARTITION property of the stobj loop,
; NAME-DRIVE-STOBJ-IS-ITEMS.  NAME-ITEMS is the logical stream of one pass over
; an octet list (the emitted octets with :yield marking each yield, and the
; final status and state).  NAME-HOST-RUN is the host loop over the stobj
; calls: the input split into any list of PIECES, each loaded whole into the
; input buffer; a call at the returned cursor after every :yield and
; :need-output, the next piece after :need-input; LAST with the final piece
; only; each call offered the next room of the schedule ROOMS on a cleared
; output; FUEL calls at most.  Under A-HOST-ROOM and FUEL at least one call per
; consumed octet, per piece and one more, the run's status, final state and
; stream equal NAME-ITEMS of the concatenated input: any permitted split gives
; the same logical stream and final state.  A call offered less room than
; max(EMIT-MAX, FINAL-MAX) answers :no-room before reading anything.
; NAME-DRIVE-IS-ITEMS is the same property of the list model alone.

; Named assumptions, recorded per instance in the world table
; `fn-dss-assumptions' (a tool reads the world, not this comment):
;
;   A-BODY-COST   NAME-WORK charges each examined octet 1 plus the :cost term
;                 (the constant :cost-max when omitted), and a :stream's final
;                 call 1 plus its :final-cost term.  That the compiled body
;                 (BODY, NORM, MAP, STEP or FINAL) does at most that much work and
;                 allocates nothing is an assumption for EVERY instance that has
;                 one, whether :cost is given or not: no equation ties the term
;                 to the compiled code.  Discharged per instance by the
;                 disassembly and allocation evidence of the landing that ships
;                 it.  The work theorems are theorems about the charge model.
;   A-RESERVED    (:copy, :stream) the output instance's array was reserved to at
;                 least CAP when it was allocated, so neither the :copy reserve nor
;                 an append grows it; the allocation and copying a growth costs is
;                 not in NAME-WORK.  Discharged by the warm-path allocation
;                 measurement (zero).
;   A-HOST-ROOM   (`fn-dss-a-host-room') every :stream call is offered at least
;                 max(EMIT-MAX, FINAL-MAX) octets of output room.  A call
;                 offered less answers :no-room and consumes and writes
;                 nothing; NAME-DRIVE-STOBJ-IS-ITEMS has it as a hypothesis.
;
; Workspace: :acc-type and :state-type must be (unsigned-byte N), N <= 59, or
; (integer 0 H), H < 2^59 (the generator refuses any other), so the persistent
; workspace is one fixnum word; what the body allocates is A-BODY-COST's.
; NORM must map octets to octets (NAME-NORM-OCTET), so each comparison is one
; octet comparison.

; Not here: a CRLF index (`:lines') is built only where a consumer needs random
; access; it is not a shape until one does.  A transducer whose workspace is
; more than one STATE-TYPE value, a fold whose accumulator is more than one
; ACC-TYPE scalar, and a find over two adjacent octets are not shapes.

(in-package "ACL2")
(include-book "octets-stobj")
(include-book "def-buffer")
(include-book "assumptions-spans")

; The two other congruent instances the shapes name: a second input
; (`:equal :against :span') and an output (`:copy', `:stream').  Callers pass
; any stobj congruent to `fn-octets' in these positions.
(def-buffer fn-dss-b :view t)
(def-buffer fn-dss-out :view t)

(defthm fn-dss-out-append-octet-is-snoc
  (equal (fn-dss-out-append-octet o fn-dss-out) (fn-oct-snoc fn-dss-out o))
  :hints (("Goal" :in-theory (enable fn-dss-out-append-octet))))

(defthm fn-dss-out-reserve-is-identity
  (equal (fn-dss-out-reserve n fn-dss-out) fn-dss-out)
  :hints (("Goal" :in-theory (enable fn-dss-out-reserve))))

(defthm fn-dss-b-get-is-nth
  (equal (fn-dss-b-get i fn-dss-b) (nth i fn-dss-b))
  :hints (("Goal" :in-theory (enable fn-dss-b-get fn-oct-nth-is-nth))))

(defthm fn-dss-octets-append-octet-is-snoc
  (equal (fn-octets-append-octet o fn-octets) (fn-oct-snoc fn-octets o))
  :hints (("Goal" :in-theory (enable fn-octets-append-octet))))

(defthm fn-dss-octets-reserve-is-identity
  (equal (fn-octets-reserve n fn-octets) fn-octets)
  :hints (("Goal" :in-theory (enable fn-octets-reserve))))

(defthm fn-dss-octets-from-list-is-list
  (equal (fn-octets-from-list xs fn-octets) xs)
  :hints (("Goal" :in-theory (enable fn-octets-from-list))))

(in-theory (disable fn-dss-out-append-octet fn-dss-out-reserve fn-dss-b-get
                    fn-dss-out-put))

; Proof support, local: the slice opened one octet at a time, appends, and
; the monotonicity of a natural slope.
(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-dss-slice-open
   (implies (and (natp i) (natp n) (< i n))
            (equal (fn-oct-slice-list i n st)
                   (cons (nth i st) (fn-oct-slice-list (+ 1 i) n st))))
   :hints (("Goal" :expand ((fn-oct-slice-list i n st))
            :in-theory (enable fn-oct-get-is-nth)))))

(local
 (defthm fn-dss-slice-empty
   (implies (not (and (natp i) (natp n) (< i n)))
            (equal (fn-oct-slice-list i n st) nil))
   :hints (("Goal" :expand ((fn-oct-slice-list i n st))))))

(local
 (defthm fn-dss-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-dss-snoc-is-append-any
   (implies (true-listp xs) (equal (fn-oct-snoc xs o) (append xs (list o))))))

(local
 (defthm fn-dss-nth-append-below
   (implies (and (natp k) (< k (len xs)))
            (equal (nth k (append xs ys)) (nth k xs)))))

(local
 (defun fn-dss-idx-ind (i end)
   (declare (xargs :measure (nfix (- (nfix end) (nfix i)))))
   (if (and (natp i) (natp end) (< i end))
       (fn-dss-idx-ind (+ 1 i) end)
     (list i end))))

; Every loop here is admitted in a theory that knows only the measure's
; arithmetic: an instance's body sits in the loop's tests and must not be
; reasoned about to show that the index advances.
(defmacro fn-dss-measure-theory ()
  '(union-theories '(o-p o< o-finp nfix natp len zp (:type-prescription len)) (theory 'minimal-theory)))

; =============================================================================
; :find

(encapsulate (((fn-dss-find-p *) => *))
  (local (defun fn-dss-find-p (o) (declare (ignore o)) nil)))

(encapsulate (((fn-dss-find-cost *) => *) ((fn-dss-find-cmax) => *))
  (local (defun fn-dss-find-cost (o) (declare (ignore o)) 0))
  (local (defun fn-dss-find-cmax () 0))
  (defthm fn-dss-find-cost-contract
    (and (natp (fn-dss-find-cmax))
         (<= (nfix (fn-dss-find-cost o)) (fn-dss-find-cmax)))
    :rule-classes nil))

(defun fn-dss-find (i end fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (if (fn-dss-find-p (fn-octets-get i fn-octets))
          i
        (fn-dss-find (+ 1 i) end fn-octets))
    nil))

(defun fn-dss-find-list (xs)
  (if (consp xs)
      (if (fn-dss-find-p (car xs))
          0
        (let ((dss-k (fn-dss-find-list (cdr xs))))
          (if dss-k (+ 1 dss-k) nil)))
    nil))

(defun fn-dss-find-work (i end fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (+ 1 (nfix (fn-dss-find-cost (fn-octets-get i fn-octets)))
         (if (fn-dss-find-p (fn-octets-get i fn-octets))
             0
           (fn-dss-find-work (+ 1 i) end fn-octets)))
    1))

(defthm fn-dss-find-is-list
  (equal (fn-dss-find i end fn-octets)
         (let ((dss-k (fn-dss-find-list (fn-oct-slice-list i end fn-octets))))
           (if dss-k (+ i dss-k) nil)))
  :hints (("Goal" :induct (fn-dss-find i end fn-octets)
           :in-theory (enable fn-oct-get-is-nth))))

(defthm fn-dss-find-hit
  (let ((dss-r (fn-dss-find i end fn-octets)))
    (implies dss-r
             (and (natp dss-r) (<= i dss-r) (< dss-r end)
                  (fn-dss-find-p (nth dss-r fn-octets))))))

(defthm fn-dss-find-least
  (let ((dss-r (fn-dss-find i end fn-octets)))
    (implies (and (natp i) (natp end) (natp j) (<= i j) (< j end)
                  (or (null dss-r) (< j dss-r)))
             (not (fn-dss-find-p (nth j fn-octets))))))

(local
 (defthm fn-dss-find-cost-linear-natp
   (implies (natp (fn-dss-find-cost o))
            (<= (fn-dss-find-cost o) (fn-dss-find-cmax)))
   :rule-classes :linear
   :hints (("Goal" :use fn-dss-find-cost-contract))))

(local
 (defthm fn-dss-find-cmax-natp
   (natp (fn-dss-find-cmax))
   :rule-classes :type-prescription
   :hints (("Goal" :use fn-dss-find-cost-contract))))

(defthm fn-dss-find-work-bound
  (<= (fn-dss-find-work i end fn-octets)
      (+ 1 (* (+ 1 (fn-dss-find-cmax)) (nfix (- (nfix end) (nfix i))))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-dss-find-work i end fn-octets))))

; =============================================================================
; :fold

(encapsulate (((fn-dss-fold-f * *) => *) ((fn-dss-fold-accp *) => *))
  (local (defun fn-dss-fold-f (acc o) (declare (ignore o)) acc))
  (local (defun fn-dss-fold-accp (acc) (declare (ignore acc)) t))
  (defthm fn-dss-fold-f-keeps-type
    (implies (and (fn-dss-fold-accp acc) (fn-cbor-octetp o))
             (fn-dss-fold-accp (fn-dss-fold-f acc o)))
    :rule-classes nil))

(encapsulate (((fn-dss-fold-cost * *) => *) ((fn-dss-fold-cmax) => *))
  (local (defun fn-dss-fold-cost (acc o) (declare (ignore acc o)) 0))
  (local (defun fn-dss-fold-cmax () 0))
  (defthm fn-dss-fold-cost-contract
    (and (natp (fn-dss-fold-cmax))
         (<= (nfix (fn-dss-fold-cost acc o)) (fn-dss-fold-cmax)))
    :rule-classes nil))

(defun fn-dss-fold (acc i end fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (fn-dss-fold (fn-dss-fold-f acc (fn-octets-get i fn-octets)) (+ 1 i) end fn-octets)
    acc))

(defun fn-dss-fold-list (acc xs)
  (if (consp xs)
      (fn-dss-fold-list (fn-dss-fold-f acc (car xs)) (cdr xs))
    acc))

(defun fn-dss-fold-work (acc i end fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (+ 1 (nfix (fn-dss-fold-cost acc (fn-octets-get i fn-octets)))
         (fn-dss-fold-work (fn-dss-fold-f acc (fn-octets-get i fn-octets)) (+ 1 i) end fn-octets))
    1))

(defthm fn-dss-fold-is-list
  (equal (fn-dss-fold acc i end fn-octets)
         (fn-dss-fold-list acc (fn-oct-slice-list i end fn-octets)))
  :hints (("Goal" :induct (fn-dss-fold acc i end fn-octets)
           :in-theory (enable fn-oct-get-is-nth))))

(defthm fn-dss-fold-acc-type
  (implies (and (fn-dss-fold-accp acc)
                (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
           (fn-dss-fold-accp (fn-dss-fold acc i end fn-octets)))
  :hints (("Goal" :induct (fn-dss-fold acc i end fn-octets)
           :in-theory (e/d (fn-oct-get-is-nth (:rewrite fn-oct-nth-of-octet-listp-is-octet . 2))
                           (fn-dss-fold-is-list)))
          ("Subgoal *1/1" :use ((:instance fn-dss-fold-f-keeps-type (o (nth i fn-octets)))))))

(local
 (defthm fn-dss-fold-cost-linear-natp
   (implies (natp (fn-dss-fold-cost acc o))
            (<= (fn-dss-fold-cost acc o) (fn-dss-fold-cmax)))
   :rule-classes :linear
   :hints (("Goal" :use fn-dss-fold-cost-contract))))

(local
 (defthm fn-dss-fold-cmax-natp
   (natp (fn-dss-fold-cmax))
   :rule-classes :type-prescription
   :hints (("Goal" :use fn-dss-fold-cost-contract))))

(defthm fn-dss-fold-work-bound
  (<= (fn-dss-fold-work acc i end fn-octets)
      (+ 1 (* (+ 1 (fn-dss-fold-cmax)) (nfix (- (nfix end) (nfix i))))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-dss-fold-work acc i end fn-octets))))

; =============================================================================
; :equal

(encapsulate (((fn-dss-eq-norm *) => *))
  (local (defun fn-dss-eq-norm (o) o))
  ; A normalized octet is an octet, so comparing two costs one comparison.
  (defthm fn-dss-eq-norm-octet
    (implies (fn-cbor-octetp o) (fn-cbor-octetp (fn-dss-eq-norm o)))
    :rule-classes nil))

(encapsulate (((fn-dss-eq-cost *) => *) ((fn-dss-eq-cmax) => *))
  (local (defun fn-dss-eq-cost (o) (declare (ignore o)) 0))
  (local (defun fn-dss-eq-cmax () 0))
  (defthm fn-dss-eq-cost-contract
    (and (natp (fn-dss-eq-cmax))
         (<= (nfix (fn-dss-eq-cost o)) (fn-dss-eq-cmax)))
    :rule-classes nil))

(defun fn-dss-eq-list (xs)
  (if (consp xs)
      (cons (fn-dss-eq-norm (car xs)) (fn-dss-eq-list (cdr xs)))
    nil))

; Against a constant list XS (the instance passes its quoted constant).
(defun fn-dss-eqc (i end fn-octets xs)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (and (consp xs)
           (equal (fn-dss-eq-norm (fn-octets-get i fn-octets)) (car xs))
           (fn-dss-eqc (+ 1 i) end fn-octets (cdr xs)))
    (null xs)))

(defun fn-dss-eqc-work (i end fn-octets xs)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (+ 1 (nfix (fn-dss-eq-cost (fn-octets-get i fn-octets)))
         (if (and (consp xs)
                  (equal (fn-dss-eq-norm (fn-octets-get i fn-octets)) (car xs)))
             (fn-dss-eqc-work (+ 1 i) end fn-octets (cdr xs))
           0))
    1))

; Against a span of equal length at J of a second instance.
(defun fn-dss-eqs (i end fn-octets j fn-dss-b)
  (declare (xargs :stobjs (fn-octets fn-dss-b) :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end) (natp j))) (< i end))
      (and (equal (fn-dss-eq-norm (fn-octets-get i fn-octets))
                  (fn-dss-eq-norm (fn-dss-b-get j fn-dss-b)))
           (fn-dss-eqs (+ 1 i) end fn-octets (+ 1 j) fn-dss-b))
    t))

(defun fn-dss-eqs-work (i end fn-octets j fn-dss-b)
  (declare (xargs :stobjs (fn-octets fn-dss-b) :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end) (natp j))) (< i end))
      (+ 1 (nfix (fn-dss-eq-cost (fn-octets-get i fn-octets)))
         (nfix (fn-dss-eq-cost (fn-dss-b-get j fn-dss-b)))
         (if (equal (fn-dss-eq-norm (fn-octets-get i fn-octets))
                    (fn-dss-eq-norm (fn-dss-b-get j fn-dss-b)))
             (fn-dss-eqs-work (+ 1 i) end fn-octets (+ 1 j) fn-dss-b)
           0))
    1))

(defthm fn-dss-eqc-is-list
  (equal (fn-dss-eqc i end fn-octets xs)
         (equal (fn-dss-eq-list (fn-oct-slice-list i end fn-octets)) xs))
  :hints (("Goal" :induct (fn-dss-eqc i end fn-octets xs)
           :in-theory (enable fn-oct-get-is-nth))))

(defthm fn-dss-eqs-is-list
  (implies (and (natp i) (natp j))
           (equal (fn-dss-eqs i end fn-octets j fn-dss-b)
                  (equal (fn-dss-eq-list (fn-oct-slice-list i end fn-octets))
                         (fn-dss-eq-list
                          (fn-oct-slice-list j (+ j (nfix (- (nfix end) (nfix i)))) fn-dss-b)))))
  :hints (("Goal" :induct (fn-dss-eqs i end fn-octets j fn-dss-b)
           :in-theory (enable fn-oct-get-is-nth))))

(local
 (defthm fn-dss-eq-cost-linear-natp
   (implies (natp (fn-dss-eq-cost o))
            (<= (fn-dss-eq-cost o) (fn-dss-eq-cmax)))
   :rule-classes :linear
   :hints (("Goal" :use fn-dss-eq-cost-contract))))

(local
 (defthm fn-dss-eq-cmax-natp
   (natp (fn-dss-eq-cmax))
   :rule-classes :type-prescription
   :hints (("Goal" :use fn-dss-eq-cost-contract))))

(defthm fn-dss-eqc-work-bound
  (<= (fn-dss-eqc-work i end fn-octets xs)
      (+ 1 (* (+ 1 (fn-dss-eq-cmax)) (nfix (- (nfix end) (nfix i))))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-dss-eqc-work i end fn-octets xs))))

(local
 (defthm fn-dss-mul-monotone
   (implies (and (natp dss-k) (natp i) (natp e) (<= i e))
            (<= (* dss-k i) (* dss-k e)))
   :rule-classes :linear
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm fn-dss-eqs-slope-monotone
   (implies (and (natp i) (natp e) (<= i e))
            (<= (* (+ 1 (* 2 (fn-dss-eq-cmax))) i) (* (+ 1 (* 2 (fn-dss-eq-cmax))) e)))
   :rule-classes :linear))

(local
 (defthm fn-dss-eqs-slope-nonneg
   (implies (and (natp i) (natp end) (<= i end))
            (<= 0 (* (+ 1 (* 2 (fn-dss-eq-cmax))) (- end i))))
   :rule-classes nil))

(local
 (defthm fn-dss-eqs-work-bound-nat
   (implies (and (natp i) (natp end) (<= i end))
            (<= (fn-dss-eqs-work i end fn-octets j fn-dss-b)
                (+ 1 (* (+ 1 (* 2 (fn-dss-eq-cmax))) (- end i)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-dss-eqs-work i end fn-octets j fn-dss-b))
           ("Subgoal *1/2" :use ((:instance fn-dss-eqs-slope-nonneg)))
           ("Subgoal *1/1" :use ((:instance fn-dss-eqs-slope-nonneg))))))

(defthm fn-dss-eqs-work-bound
  (<= (fn-dss-eqs-work i end fn-octets j fn-dss-b)
      (+ 1 (* (+ 1 (* 2 (fn-dss-eq-cmax))) (nfix (- (nfix end) (nfix i))))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-dss-eqs-work-bound-nat))
           :expand ((fn-dss-eqs-work i end fn-octets j fn-dss-b)))))

; =============================================================================
; :copy

(encapsulate (((fn-dss-copy-f *) => *))
  (local (defun fn-dss-copy-f (o) o))
  (defthm fn-dss-copy-f-octet
    (implies (fn-cbor-octetp o) (fn-cbor-octetp (fn-dss-copy-f o)))
    :rule-classes nil))

(encapsulate (((fn-dss-copy-cost *) => *) ((fn-dss-copy-cmax) => *))
  (local (defun fn-dss-copy-cost (o) (declare (ignore o)) 0))
  (local (defun fn-dss-copy-cmax () 0))
  (defthm fn-dss-copy-cost-contract
    (and (natp (fn-dss-copy-cmax))
         (<= (nfix (fn-dss-copy-cost o)) (fn-dss-copy-cmax)))
    :rule-classes nil))

(defun fn-dss-copy-list (xs)
  (if (consp xs)
      (cons (fn-dss-copy-f (car xs)) (fn-dss-copy-list (cdr xs)))
    nil))

; Onto a distinct instance.  The caller has extended the destination by the
; span's length (zero octets, once, after the capacity check); the loop stores
; each octet at its index J, one `put' per octet, and touches no fill point.
(defun fn-dss-copy-loop (i end j fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (let ((fn-dss-out (fn-dss-out-put j (fn-dss-copy-f (fn-octets-get i fn-octets)) fn-dss-out)))
        (fn-dss-copy-loop (+ 1 i) end (+ 1 j) fn-octets fn-dss-out))
    fn-dss-out))

(defun fn-dss-copy (i end cap fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
  (let ((dss-m (nfix (- (nfix end) (nfix i)))))
    (if (<= (+ (fn-dss-out-len fn-dss-out) dss-m) (nfix cap))
        (let* ((dss-j (fn-dss-out-len fn-dss-out))
               (fn-dss-out (fn-dss-out-reserve (+ dss-j dss-m) fn-dss-out))
               (fn-dss-out (fn-dss-out-append-word 0 (if (and (natp i) (natp end)) dss-m 0)
                                                   fn-dss-out))
               (fn-dss-out (fn-dss-copy-loop i end dss-j fn-octets fn-dss-out)))
          (mv :done fn-dss-out))
      (mv :refused fn-dss-out))))

; Onto the same instance, from below its fill point.
(defun fn-dss-copyw-loop (i end fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (let ((fn-octets (fn-octets-append-octet
                        (fn-dss-copy-f (fn-octets-get i fn-octets)) fn-octets)))
        (fn-dss-copyw-loop (+ 1 i) end fn-octets))
    fn-octets))

(defun fn-dss-copyw (i end cap fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (let ((dss-n (+ (fn-octets-len fn-octets) (nfix (- (nfix end) (nfix i))))))
    (if (<= dss-n (nfix cap))
        (let* ((fn-octets (fn-octets-reserve dss-n fn-octets))
               (fn-octets (fn-dss-copyw-loop i end fn-octets)))
          (mv :done fn-octets))
      (mv :refused fn-octets))))

(defun fn-dss-copy-work (i end fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (+ 1 (nfix (fn-dss-copy-cost (fn-octets-get i fn-octets)))
         (fn-dss-copy-work (+ 1 i) end fn-octets))
    1))

;  Proof support, local: the destination as a prefix and a tail of cells
; the loop overwrites in order.
(local
 (defthm fn-dss-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthmd fn-dss-out-put-is-update
   (equal (fn-dss-out-put i o fn-dss-out) (fn-oct-update i o fn-dss-out))
   :hints (("Goal" :in-theory (enable fn-dss-out-put)))))

(local
 (defun fn-dss-copy-ind (i end pre rest st)
   (declare (xargs :measure (nfix (- (nfix end) (nfix i)))))
   (if (and (natp i) (natp end) (< i end))
       (fn-dss-copy-ind (+ 1 i) end (append pre (list (fn-dss-copy-f (nth i st)))) (cdr rest) st)
     (list i end pre rest st))))

(local
 (defthm fn-dss-update-nth-append-len
   (implies (and (true-listp pre) (consp rest))
            (equal (update-nth (len pre) v (append pre rest))
                   (append pre (cons v (cdr rest)))))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-dss-oct-update-append-len
   (implies (and (true-listp pre) (true-listp rest) (consp rest))
            (equal (fn-oct-update (len pre) v (append pre rest))
                   (append pre (cons v (cdr rest)))))
   :hints (("Goal" :use ((:instance fn-oct-update-is-update-nth (i (len pre)) (o v)
                                    (xs (append pre rest)))
                         fn-dss-update-nth-append-len)
            :in-theory (disable fn-oct-update-is-update-nth fn-dss-update-nth-append-len)))))

(local
 (defthm fn-dss-copy-loop-general
   (implies (and (true-listp pre) (true-listp rest) (natp i) (natp end)
                 (<= (nfix (- end i)) (len rest)))
            (equal (fn-dss-copy-loop i end (len pre) fn-octets (append pre rest))
                   (append pre (fn-dss-copy-list (fn-oct-slice-list i end fn-octets))
                           (nthcdr (nfix (- end i)) rest))))
   :hints (("Goal" :induct (fn-dss-copy-ind i end pre rest fn-octets)
            :expand ((fn-dss-copy-loop i end (len pre) fn-octets (append pre rest)))
            :in-theory (e/d (fn-oct-get-is-nth fn-dss-out-put-is-update)
                            (fn-oct-slice-list-is-take-nthcdr))))))

(local
 (defthm fn-dss-nthcdr-of-word-octets
   (implies (natp n) (equal (nthcdr n (fn-oct-word-octets w n)) nil))
   :hints (("Goal" :use ((:instance fn-oct-len-of-word-octets (k n))
                         (:instance fn-oct-true-listp-of-word-octets (k n)))
            :in-theory (disable fn-oct-len-of-word-octets fn-oct-true-listp-of-word-octets)))))

(defthm fn-dss-copy-is-list
  (implies (true-listp fn-dss-out)
           (equal (fn-dss-copy i end cap fn-octets fn-dss-out)
                  (if (<= (+ (len fn-dss-out) (nfix (- (nfix end) (nfix i)))) (nfix cap))
                      (mv :done (append fn-dss-out
                                        (fn-dss-copy-list (fn-oct-slice-list i end fn-octets))))
                    (mv :refused fn-dss-out))))
  :hints (("Goal" :cases ((and (natp i) (natp end)))
           :do-not-induct t
           :in-theory (e/d (fn-dss-out-len-is-len fn-dss-out-reserve-is-identity
                            fn-dss-out-append-word-is-append)
                           (fn-oct-slice-list-is-take-nthcdr fn-dss-copy-loop-general))
           :use ((:instance fn-dss-copy-loop-general (pre fn-dss-out)
                            (rest (fn-oct-word-octets 0 (nfix (- (nfix end) (nfix i))))))))))

; The physical writes of one :copy call, as a charge model beside NAME-WORK:
; the extend zeroes the span's length in cells, then each octet is one store.
; That the compiled loop stores no more than the charge is the disassembly
; evidence's, as A-BODY-COST is for work; A-RESERVED is unchanged (the array
; is reserved at allocation, and the extend only moves the fill point).
(local
 (defthm fn-dss-len-of-copy-list
   (equal (len (fn-dss-copy-list xs)) (len xs))))

(local
 (defthm fn-dss-len-of-slice-list
   (<= (len (fn-oct-slice-list i end fn-octets)) (nfix (- (nfix end) (nfix i))))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-dss-idx-ind i end)
            :in-theory (e/d (fn-dss-slice-open fn-dss-slice-empty) (fn-oct-slice-list-is-take-nthcdr))))))

(defun fn-dss-copy-write-charge (i end cap fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
  (let ((dss-m (nfix (- (nfix end) (nfix i)))))
    (if (<= (+ (fn-dss-out-len fn-dss-out) dss-m) (nfix cap))
        (+ dss-m (len (fn-dss-copy-list (fn-oct-slice-list i end fn-octets))))
      0)))

(defthm fn-dss-copy-write-charge-bound
  (<= (fn-dss-copy-write-charge i end cap fn-octets fn-dss-out)
      (* 2 (nfix (- (nfix end) (nfix i)))))
  :rule-classes :linear)

; Within one instance: the buffer is the original followed by what has been
; written, and every read is below the original fill point.
(local
 (defthm fn-dss-slice-append-below
   (implies (and (natp i) (natp end) (<= end (len fn-octets)))
            (equal (fn-oct-slice-list i end (append fn-octets ys))
                   (fn-oct-slice-list i end fn-octets)))
   :hints (("Goal" :induct (fn-dss-idx-ind i end)
            :in-theory (disable fn-oct-slice-list-is-take-nthcdr)))))

(local
 (defun fn-dss-copyw-ind (i end st0 w)
   (declare (xargs :measure (nfix (- (nfix end) (nfix i)))))
   (if (and (natp i) (natp end) (< i end))
       (fn-dss-copyw-ind (+ 1 i) end st0 (append w (list (fn-dss-copy-f (nth i st0)))))
     (list i end st0 w))))

(local
 (defthm fn-dss-copyw-loop-general
   (implies (and (true-listp st0) (true-listp w) (natp end) (<= end (len st0)))
            (equal (fn-dss-copyw-loop i end (append st0 w))
                   (append st0 w (fn-dss-copy-list (fn-oct-slice-list i end st0)))))
   :hints (("Goal" :induct (fn-dss-copyw-ind i end st0 w)
            :expand ((fn-dss-copyw-loop i end (append st0 w)))
            :in-theory (e/d (fn-oct-get-is-nth) (fn-oct-slice-list-is-take-nthcdr))))))

(local
 (defthm fn-dss-copyw-loop-is-append
   (implies (and (true-listp fn-octets) (natp end) (<= end (len fn-octets)))
            (equal (fn-dss-copyw-loop i end fn-octets)
                   (append fn-octets (fn-dss-copy-list (fn-oct-slice-list i end fn-octets)))))
   :hints (("Goal" :use ((:instance fn-dss-copyw-loop-general (st0 fn-octets) (w nil)))
            :in-theory (disable fn-dss-copyw-loop-general fn-oct-slice-list-is-take-nthcdr)))))

(defthm fn-dss-copyw-is-list
  (implies (and (true-listp fn-octets) (<= end (len fn-octets)))
           (equal (fn-dss-copyw i end cap fn-octets)
                  (if (<= (+ (len fn-octets) (nfix (- (nfix end) (nfix i)))) (nfix cap))
                      (mv :done (append fn-octets
                                        (fn-dss-copy-list (fn-oct-slice-list i end fn-octets))))
                    (mv :refused fn-octets))))
  :hints (("Goal" :cases ((natp end))
           :in-theory (disable fn-oct-slice-list-is-take-nthcdr))))

(local
 (defthm fn-dss-copy-cost-linear-natp
   (implies (natp (fn-dss-copy-cost o))
            (<= (fn-dss-copy-cost o) (fn-dss-copy-cmax)))
   :rule-classes :linear
   :hints (("Goal" :use fn-dss-copy-cost-contract))))

(local
 (defthm fn-dss-copy-cmax-natp
   (natp (fn-dss-copy-cmax))
   :rule-classes :type-prescription
   :hints (("Goal" :use fn-dss-copy-cost-contract))))

(defthm fn-dss-copy-work-bound
  (<= (fn-dss-copy-work i end fn-octets)
      (+ 1 (* (+ 1 (fn-dss-copy-cmax)) (nfix (- (nfix end) (nfix i))))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-dss-copy-work i end fn-octets))))

; =============================================================================
; :stream

(encapsulate (((fn-dss-st-next * *) => *) ((fn-dss-st-k * *) => *)
              ((fn-dss-st-w * *) => *) ((fn-dss-st-sig * *) => *)
              ((fn-dss-st-fk *) => *) ((fn-dss-st-fw *) => *)
              ((fn-dss-st-fnext *) => *) ((fn-dss-st-fsig *) => *)
              ((fn-dss-st-emax) => *) ((fn-dss-st-fmax) => *))
  (local (defun fn-dss-st-next (s o) (declare (ignore o)) s))
  (local (defun fn-dss-st-k (s o) (declare (ignore s o)) 0))
  (local (defun fn-dss-st-w (s o) (declare (ignore s o)) 0))
  (local (defun fn-dss-st-sig (s o) (declare (ignore s o)) 0))
  (local (defun fn-dss-st-fk (s) (declare (ignore s)) 0))
  (local (defun fn-dss-st-fw (s) (declare (ignore s)) 0))
  (local (defun fn-dss-st-fnext (s) s))
  (local (defun fn-dss-st-fsig (s) (declare (ignore s)) 0))
  (local (defun fn-dss-st-emax () 0))
  (local (defun fn-dss-st-fmax () 0))
  ; Every step on an octet emits at most EMIT-MAX octets, every final at most
  ; FINAL-MAX, both at most 7 (one fixnum word), from every state.
  (defthm fn-dss-st-emit-contract
    (and (natp (fn-dss-st-emax)) (<= (fn-dss-st-emax) 7)
         (natp (fn-dss-st-fmax)) (<= (fn-dss-st-fmax) 7)
         (implies (fn-cbor-octetp o)
                  (and (natp (fn-dss-st-k s o)) (<= (fn-dss-st-k s o) (fn-dss-st-emax))
                       (unsigned-byte-p 56 (fn-dss-st-w s o))))
         (natp (fn-dss-st-fk s)) (<= (fn-dss-st-fk s) (fn-dss-st-fmax))
         (unsigned-byte-p 56 (fn-dss-st-fw s)))
    :rule-classes nil))

(encapsulate (((fn-dss-st-statep *) => *))
  (local (defun fn-dss-st-statep (s) (declare (ignore s)) t))
  (defthm fn-dss-st-next-keeps-type
    (and (implies (and (fn-dss-st-statep s) (fn-cbor-octetp o))
                  (fn-dss-st-statep (fn-dss-st-next s o)))
         (implies (fn-dss-st-statep s)
                  (fn-dss-st-statep (fn-dss-st-fnext s))))
    :rule-classes nil))

(encapsulate (((fn-dss-st-cost * *) => *) ((fn-dss-st-cmax) => *)
              ((fn-dss-st-fcost *) => *) ((fn-dss-st-fcmax) => *))
  (local (defun fn-dss-st-cost (s o) (declare (ignore s o)) 0))
  (local (defun fn-dss-st-cmax () 0))
  (local (defun fn-dss-st-fcost (s) (declare (ignore s)) 0))
  (local (defun fn-dss-st-fcmax () 0))
  (defthm fn-dss-st-cost-contract
    (and (natp (fn-dss-st-cmax))
         (<= (nfix (fn-dss-st-cost s o)) (fn-dss-st-cmax))
         (natp (fn-dss-st-fcmax))
         (<= (nfix (fn-dss-st-fcost s)) (fn-dss-st-fcmax)))
    :rule-classes nil))

; The room every call must be offered, A-HOST-ROOM: enough for one step's
; output and for the final.  A call offered less is refused by name,
; :no-room, and consumes and writes nothing.
(defun fn-dss-floor ()
  (max (nfix (fn-dss-st-emax)) (nfix (fn-dss-st-fmax))))

; The octets of the word W, K of them, stored at IDX, IDX+1, ...: one `put'
; each.  The logic is the recursion `fn-dss-put-word-rec'; the executable is
; the same stores unrolled for the K <= 7 a step or final emits, as an inline
; function, so a loop over the span makes no call per emitted octet.
(defun fn-dss-put-word-rec (w k idx fn-dss-out)
  (declare (xargs :stobjs fn-dss-out :verify-guards nil :measure (nfix k)))
  (if (zp k)
      fn-dss-out
    (let ((fn-dss-out (fn-dss-out-put idx (mod (nfix w) 256) fn-dss-out)))
      (fn-dss-put-word-rec (floor (nfix w) 256) (1- k) (1+ idx) fn-dss-out))))

(defthm fn-dss-len-of-out-put
  (implies (and (natp i) (< i (len xs)) (true-listp xs))
           (equal (len (fn-dss-out-put i o xs)) (len xs)))
  :hints (("Goal" :in-theory (enable fn-dss-out-put-is-update))))

(defthm fn-dss-true-listp-of-out-put
  (implies (true-listp xs) (true-listp (fn-dss-out-put i o xs)))
  :hints (("Goal" :in-theory (enable fn-dss-out-put-is-update))))

(defthm fn-dss-octet-listp-true-listp
  (implies (fn-cbor-octet-listp x) (true-listp x))
  :rule-classes :forward-chaining)

(defun-inline fn-dss-put-word-exec (w k idx fn-dss-out)
  (declare (type (unsigned-byte 56) w) (type (integer 0 7) k) (type (unsigned-byte 59) idx)
           (xargs :stobjs fn-dss-out
                  :guard (and (unsigned-byte-p 56 w) (natp k) (<= k 7) (unsigned-byte-p 59 idx)
                              (<= (+ idx k) (fn-dss-out-len fn-dss-out)))
                  :guard-hints (("Goal" :in-theory (e/d (fn-oct-mod-256-octet fn-oct-floor-256-natp
                                                         fn-oct-floor-256-ub56)
                                                        (mod floor))))))
  (let* ((fn-dss-out (if (< 0 k) (fn-dss-out-put idx (mod w 256) fn-dss-out) fn-dss-out))
         (w (floor w 256))
         (idx (+ idx 1))
         (fn-dss-out (if (< 1 k) (fn-dss-out-put idx (mod w 256) fn-dss-out) fn-dss-out))
         (w (floor w 256))
         (idx (+ idx 1))
         (fn-dss-out (if (< 2 k) (fn-dss-out-put idx (mod w 256) fn-dss-out) fn-dss-out))
         (w (floor w 256))
         (idx (+ idx 1))
         (fn-dss-out (if (< 3 k) (fn-dss-out-put idx (mod w 256) fn-dss-out) fn-dss-out))
         (w (floor w 256))
         (idx (+ idx 1))
         (fn-dss-out (if (< 4 k) (fn-dss-out-put idx (mod w 256) fn-dss-out) fn-dss-out))
         (w (floor w 256))
         (idx (+ idx 1))
         (fn-dss-out (if (< 5 k) (fn-dss-out-put idx (mod w 256) fn-dss-out) fn-dss-out))
         (w (floor w 256))
         (idx (+ idx 1))
         (fn-dss-out (if (< 6 k) (fn-dss-out-put idx (mod w 256) fn-dss-out) fn-dss-out)))
    fn-dss-out))

(local
 (defthm fn-dss-put-word-exec-is-rec
   (implies (and (natp w) (natp k) (<= k 7))
            (equal (fn-dss-put-word-exec w k idx fn-dss-out)
                   (fn-dss-put-word-rec w k idx fn-dss-out)))
   :hints (("Goal" :do-not-induct t
            :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3)
                    (equal k 4) (equal k 5) (equal k 6) (equal k 7))
            :in-theory (e/d (fn-dss-put-word-exec$inline)
                            (fn-oct-update-is-update-nth fn-oct-update))
            :expand ((:free (w k idx out) (fn-dss-put-word-rec w k idx out)))))))

(defun-inline fn-dss-put-word (w k idx fn-dss-out)
  (declare (type (unsigned-byte 56) w) (type (integer 0 7) k) (type (unsigned-byte 59) idx)
           (xargs :stobjs fn-dss-out
                  :guard (and (unsigned-byte-p 56 w) (natp k) (<= k 7) (unsigned-byte-p 59 idx)
                              (<= (+ idx k) (fn-dss-out-len fn-dss-out)))
                  :guard-hints (("Goal" :use fn-dss-put-word-exec-is-rec
                                 :in-theory (disable fn-dss-put-word-exec-is-rec
                                                     fn-dss-put-word-exec$inline
                                                     fn-dss-put-word-rec)))))
  (mbe :logic (fn-dss-put-word-rec w k idx fn-dss-out)
       :exec (fn-dss-put-word-exec w k idx fn-dss-out)))

; The writes stay inside the output (the guard of `fn-dss-put-word' says so),
; so its length is unchanged; instances' guard proofs use this.
(defthm fn-dss-update-len-in-range
  (implies (and (true-listp xs) (natp i) (< i (len xs)))
           (equal (len (fn-oct-update i v xs)) (len xs)))
  :hints (("Goal" :induct (fn-oct-update i v xs) :in-theory (enable fn-oct-update))))

(defthm fn-dss-update-true-listp-in-range
  (implies (and (true-listp xs) (natp i) (< i (len xs)))
           (true-listp (fn-oct-update i v xs)))
  :hints (("Goal" :induct (fn-oct-update i v xs) :in-theory (enable fn-oct-update))))

(defthm fn-dss-put-word-rec-len
  (implies (and (true-listp out) (natp idx) (natp k) (<= (+ idx k) (len out)))
           (and (equal (len (fn-dss-put-word-rec w k idx out)) (len out))
                (true-listp (fn-dss-put-word-rec w k idx out))))
  :hints (("Goal" :induct (fn-dss-put-word-rec w k idx out)
           :in-theory (e/d (fn-dss-out-put-is-update) (fn-oct-update)))))

(defthm fn-dss-put-word-len
  (implies (and (true-listp out) (natp idx) (natp k) (<= (+ idx k) (len out)))
           (and (equal (len (fn-dss-put-word w k idx out)) (len out))
                (true-listp (fn-dss-put-word w k idx out))))
  :hints (("Goal" :in-theory (enable fn-dss-put-word$inline))))

; The stobj loop.  IDX is the length written so far (the output's first IDX
; cells are the stream), ROOM the room left in the extended window, both
; carried so the loop reads no length and adds one fixnum per emitted word.
; Every exit truncates the output to IDX: the cells past it are the window the
; entry zeroed and the loop did not reach.
(defun fn-dss-stream-loop (s i end last idx room fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (if (< (nfix room) (fn-dss-st-emax))
          (let ((fn-dss-out (fn-dss-out-truncate idx fn-dss-out)))
            (mv :need-output s i fn-dss-out))
        (let* ((dss-o (fn-octets-get i fn-octets))
               (dss-sig (fn-dss-st-sig s dss-o)))
          (if (eql dss-sig 2)
              (let ((fn-dss-out (fn-dss-out-truncate idx fn-dss-out)))
                (mv :refused (fn-dss-st-next s dss-o) i fn-dss-out))
            (let* ((dss-k (nfix (fn-dss-st-k s dss-o)))
                   (fn-dss-out (fn-dss-put-word (fn-dss-st-w s dss-o) dss-k idx fn-dss-out))
                   (dss-idx (+ idx dss-k))
                   (dss-room (- (nfix room) dss-k)))
              (if (eql dss-sig 1)
                  (let ((fn-dss-out (fn-dss-out-truncate dss-idx fn-dss-out)))
                    (mv :yield (fn-dss-st-next s dss-o) (+ 1 i) fn-dss-out))
                (fn-dss-stream-loop (fn-dss-st-next s dss-o) (+ 1 i) end last dss-idx dss-room
                                    fn-octets fn-dss-out))))))
    (if last
        (if (< (nfix room) (fn-dss-st-fmax))
            (let ((fn-dss-out (fn-dss-out-truncate idx fn-dss-out)))
              (mv :need-output s i fn-dss-out))
          (if (eql (fn-dss-st-fsig s) 2)
              (let ((fn-dss-out (fn-dss-out-truncate idx fn-dss-out)))
                (mv :refused (fn-dss-st-fnext s) i fn-dss-out))
            (let* ((dss-k (nfix (fn-dss-st-fk s)))
                   (fn-dss-out (fn-dss-put-word (fn-dss-st-fw s) dss-k idx fn-dss-out))
                   (fn-dss-out (fn-dss-out-truncate (+ idx dss-k) fn-dss-out)))
              (mv :done (fn-dss-st-fnext s) i fn-dss-out))))
      (let ((fn-dss-out (fn-dss-out-truncate idx fn-dss-out)))
        (mv :need-input s i fn-dss-out)))))

; One call: the room check at entry, then the output extended once to CAP
; (by the zero-word append: ROOM zero octets after the IDX octets already
; there), then the loop.
(defun fn-dss-stream (s i end last cap fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
  (let* ((dss-len (fn-dss-out-len fn-dss-out))
         (dss-room (nfix (- cap dss-len))))
    (if (< dss-room (fn-dss-floor))
        (mv :no-room s i fn-dss-out)
      (let ((fn-dss-out (fn-dss-out-append-word 0 dss-room fn-dss-out)))
        (fn-dss-stream-loop s i end last dss-len dss-room fn-octets fn-dss-out)))))

; The list model of one call: XS the octets from I to END, ROOM the output
; room (- CAP (len out)).  Answers (mv SIGNAL S' OUTS N): the octets written
; and the number consumed.
(defun fn-dss-stream-list-loop (s xs last room)
  (declare (xargs :measure (len xs) :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (consp xs)
      (if (< (nfix room) (fn-dss-st-emax))
          (mv :need-output s nil 0)
        (let* ((dss-o (car xs))
               (dss-sig (fn-dss-st-sig s dss-o)))
          (if (eql dss-sig 2)
              (mv :refused (fn-dss-st-next s dss-o) nil 0)
            (let ((dss-ws (fn-oct-word-octets (fn-dss-st-w s dss-o) (fn-dss-st-k s dss-o))))
              (if (eql dss-sig 1)
                  (mv :yield (fn-dss-st-next s dss-o) dss-ws 1)
                (mv-let (dss-r dss-s2 dss-outs dss-n)
                  (fn-dss-stream-list-loop (fn-dss-st-next s dss-o) (cdr xs) last
                                      (- (nfix room) (nfix (fn-dss-st-k s dss-o))))
                  (mv dss-r dss-s2 (append dss-ws dss-outs) (+ 1 dss-n))))))))
    (if last
        (if (< (nfix room) (fn-dss-st-fmax))
            (mv :need-output s nil 0)
          (if (eql (fn-dss-st-fsig s) 2)
              (mv :refused (fn-dss-st-fnext s) nil 0)
            (mv :done (fn-dss-st-fnext s)
                (fn-oct-word-octets (fn-dss-st-fw s) (fn-dss-st-fk s)) 0)))
      (mv :need-input s nil 0))))

(defun fn-dss-stream-list (s xs last room)
  (if (< (nfix room) (fn-dss-floor))
      (mv :no-room s nil 0)
    (fn-dss-stream-list-loop s xs last room)))

; The logical stream of one pass, with no output bound: the emitted octets,
; :yield after each yielding octet's output, and the status and state.
(defun fn-dss-stream-items (s xs last)
  (declare (xargs :measure (len xs) :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (consp xs)
      (let* ((dss-o (car xs))
             (dss-sig (fn-dss-st-sig s dss-o)))
        (if (eql dss-sig 2)
            (mv :refused (fn-dss-st-next s dss-o) nil)
          (mv-let (dss-r dss-s2 dss-items)
            (fn-dss-stream-items (fn-dss-st-next s dss-o) (cdr xs) last)
            (mv dss-r dss-s2 (append (fn-oct-word-octets (fn-dss-st-w s dss-o) (fn-dss-st-k s dss-o))
                             (if (eql dss-sig 1) (cons :yield dss-items) dss-items))))))
    (if last
        (if (eql (fn-dss-st-fsig s) 2)
            (mv :refused (fn-dss-st-fnext s) nil)
          (mv :done (fn-dss-st-fnext s)
              (fn-oct-word-octets (fn-dss-st-fw s) (fn-dss-st-fk s))))
      (mv :need-input s nil))))

(defun fn-dss-flatten (pieces)
  (if (consp pieces)
      (append (car pieces) (fn-dss-flatten (cdr pieces)))
    nil))

(defun fn-dss-sum-lens (pieces)
  (if (consp pieces)
      (+ (len (car pieces)) (fn-dss-sum-lens (cdr pieces)))
    0))

; What one call consumes: a count within its input.  The drive's measure
; rests on dss-it, here and in every instance (by `:functional-instance').
(defthm fn-dss-stream-list-loop-consumed
  (let ((dss-n (mv-nth 3 (fn-dss-stream-list-loop s xs last room))))
    (and (natp dss-n) (<= dss-n (len xs))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-dss-stream-list-loop s xs last room))))

(defthm fn-dss-stream-list-consumed
  (let ((dss-n (mv-nth 3 (fn-dss-stream-list s xs last room))))
    (and (natp dss-n) (<= dss-n (len xs))))
  :rule-classes nil
  :hints (("Goal" :use fn-dss-stream-list-loop-consumed)))

(defthm fn-dss-len-nthcdr
  (implies (and (natp dss-n) (<= dss-n (len xs)))
           (equal (len (nthcdr dss-n xs)) (- (len xs) dss-n))))

; How a host drives the loop over a split input: PIECES the successive
; arrivals, ROOMS the output room offered at each call (raised to the floor),
; LAST given with the final piece only.  Every call consumes an octet or ends
; a piece or the dss-run, which is the measure's argument.
(defun fn-dss-drive (s pieces last rooms)
  (declare (xargs :measure (+ (fn-dss-sum-lens pieces) (len pieces))
                  :hints (("Goal" :use ((:instance fn-dss-stream-list-consumed
                                         (xs (if (consp pieces) (car pieces) nil))
                                         (last (and last (atom (cdr pieces))))
                                         (room (max (fn-dss-floor)
                                                    (nfix (if (consp rooms) (car rooms) 0))))))
                           :in-theory (e/d (fn-dss-len-nthcdr) (fn-dss-stream-list nthcdr))))))
  (let* ((xs (if (consp pieces) (car pieces) nil))
         (dss-lastp (and last (atom (cdr pieces))))
         (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
    (mv-let (dss-r dss-s2 dss-outs dss-n) (fn-dss-stream-list s xs dss-lastp room)
      (cond ((or (eq dss-r :refused) (eq dss-r :done))
             (mv dss-r dss-s2 dss-outs))
            ((eq dss-r :need-input)
             (if (consp (cdr pieces))
                 (mv-let (dss-r3 dss-s3 dss-items) (fn-dss-drive dss-s2 (cdr pieces) last (cdr rooms))
                   (mv dss-r3 dss-s3 (append dss-outs dss-items)))
               (mv dss-r dss-s2 dss-outs)))
            ((zp dss-n) (mv dss-r dss-s2 dss-outs))
            (t
             (mv-let (dss-r3 dss-s3 dss-items)
               (fn-dss-drive dss-s2 (cons (nthcdr dss-n xs) (cdr pieces)) last (cdr rooms))
               (mv dss-r3 dss-s3 (append dss-outs (if (eq dss-r :yield) (cons :yield dss-items) dss-items)))))))))

; The work of one call, ROOM the output room at the call: each examined
; octet 1 plus the step's cost, the exit 1 plus the final's cost when LAST.
(defun fn-dss-stream-work (s i end last room fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (if (< (nfix room) (fn-dss-st-emax))
          1
        (let* ((dss-o (fn-octets-get i fn-octets))
               (dss-sig (fn-dss-st-sig s dss-o)))
          (+ 1 (nfix (fn-dss-st-cost s dss-o))
             (if (or (eql dss-sig 2) (eql dss-sig 1))
                 0
               (fn-dss-stream-work (fn-dss-st-next s dss-o) (+ 1 i) end last
                                   (- (nfix room) (nfix (fn-dss-st-k s dss-o))) fn-octets)))))
    (+ 1 (if last (nfix (fn-dss-st-fcost s)) 0))))

; Proof support for the stream bridge, local.  The list loop sees its room
; only through nfix; the stobj loop is the list loop at any room equal to the
; output's under nfix (the induction carries dss-it explicitly).
(local
 (defthm fn-dss-st-emax-natp
   (natp (fn-dss-st-emax))
   :rule-classes :type-prescription
   :hints (("Goal" :use fn-dss-st-emit-contract))))

(local
 (defthm fn-dss-st-fmax-natp
   (natp (fn-dss-st-fmax))
   :rule-classes :type-prescription
   :hints (("Goal" :use fn-dss-st-emit-contract))))

(local
 (defthm fn-dss-nfix-of-nat
   (implies (natp x) (equal (nfix x) x))))

(local
 (defthm fn-dss-len-word-octets
   (equal (len (fn-oct-word-octets w dss-k)) (nfix dss-k))))

(local
 (defthm fn-dss-stream-list-loop-nfix-room
   (equal (fn-dss-stream-list-loop s xs last (nfix room))
          (fn-dss-stream-list-loop s xs last room))
   :hints (("Goal" :expand ((fn-dss-stream-list-loop s xs last (nfix room))
                            (fn-dss-stream-list-loop s xs last room))))))

(local
 (defthm fn-dss-update-facts
   (implies (and (true-listp xs) (natp i) (<= i (len xs)))
            (and (true-listp (fn-oct-update i v xs))
                 (equal (len (fn-oct-update i v xs)) (max (len xs) (+ 1 i)))
                 (equal (take (+ 1 i) (fn-oct-update i v xs)) (append (take i xs) (list v)))))
   :hints (("Goal" :induct (fn-oct-update i v xs)
            :in-theory (enable fn-oct-update)))))

; Writing the word at IDX, from a cell at or before the end: the output's
; first IDX+K cells are what was there up to IDX followed by the word, and
; the output did not shrink.
(local
 (defthm fn-dss-put-word-rec-zero
   (implies (zp k) (equal (fn-dss-put-word-rec w k idx out) out))
   :hints (("Goal" :expand ((fn-dss-put-word-rec w k idx out))))))

(local
 (defthm fn-dss-put-word-rec-prefix
   (implies (and (true-listp out) (natp idx) (natp k) (<= idx (len out)))
            (and (true-listp (fn-dss-put-word-rec w k idx out))
                 (<= (len out) (len (fn-dss-put-word-rec w k idx out)))
                 (<= (+ idx k) (len (fn-dss-put-word-rec w k idx out)))
                 (equal (take (+ idx k) (fn-dss-put-word-rec w k idx out))
                        (append (take idx out) (fn-oct-word-octets w k)))))
   :hints (("Goal" :induct (fn-dss-put-word-rec w k idx out)
            :in-theory (e/d (fn-dss-out-put-is-update) (fn-oct-update take))))))

; The stobj loop is the list loop: IDX cells of the output are the stream so
; far, the rest the window the entry zeroed, and every exit keeps the first
; IDX.  Total: nothing here assumes the step meets its contract.
(local
 (defthm fn-dss-stream-loop-is-list-general
   (implies (and (natp i) (natp idx) (true-listp fn-dss-out)
                 (<= idx (len fn-dss-out)))
            (equal (fn-dss-stream-loop s i end last idx room fn-octets fn-dss-out)
                   (mv-let (dss-r dss-s2 dss-outs dss-n)
                     (fn-dss-stream-list-loop s (fn-oct-slice-list i end fn-octets) last room)
                     (mv dss-r dss-s2 (+ i dss-n) (append (take idx fn-dss-out) dss-outs)))))
   :hints (("Goal" :induct (fn-dss-stream-loop s i end last idx room fn-octets fn-dss-out)
            :in-theory (e/d (fn-oct-get-is-nth fn-dss-put-word$inline)
                            (fn-oct-slice-list-is-take-nthcdr
                             fn-dss-stream-list-loop-nfix-room
                             fn-dss-put-word-rec))))))

(local
 (defthm fn-dss-take-len-append
   (implies (true-listp x) (equal (take (len x) (append x y)) x))))

(defthm fn-dss-stream-is-list
  (implies (and (natp i) (natp cap) (true-listp fn-dss-out))
           (equal (fn-dss-stream s i end last cap fn-octets fn-dss-out)
                  (mv-let (dss-r dss-s2 dss-outs dss-n)
                    (fn-dss-stream-list s (fn-oct-slice-list i end fn-octets) last
                                        (nfix (- cap (len fn-dss-out))))
                    (mv dss-r dss-s2 (+ i dss-n) (append fn-dss-out dss-outs)))))
  :hints (("Goal" :in-theory (e/d (fn-dss-out-len-is-len fn-dss-out-append-word-is-append)
                                  (nfix fn-dss-stream-list-loop-nfix-room fn-dss-stream-loop
                                   fn-dss-stream-list-loop fn-oct-slice-list-is-take-nthcdr)))))

; Proof support for the partition property, local: the one-pass stream of a
; concatenation, what one list-loop call consumes and emits, and the drive's
; one-call step, STEP, from which the drive theorem follows by induction.
(local
 (defthm fn-dss-stream-items-shape
  (equal (list (mv-nth 0 (fn-dss-stream-items s xs last))
               (mv-nth 1 (fn-dss-stream-items s xs last))
               (mv-nth 2 (fn-dss-stream-items s xs last)))
         (fn-dss-stream-items s xs last))
  :hints (("Goal" :induct (fn-dss-stream-items s xs last)))))

(local
 (defthm fn-dss-stream-items-shape-car
  (equal (list (car (fn-dss-stream-items s xs last))
               (mv-nth 1 (fn-dss-stream-items s xs last))
               (mv-nth 2 (fn-dss-stream-items s xs last)))
         (fn-dss-stream-items s xs last))
  :hints (("Goal" :use fn-dss-stream-items-shape))))

(local
 (defthm fn-dss-items-append
  (equal (fn-dss-stream-items s (append a b) last)
         (mv-let (dss-r1 dss-s1 dss-it1) (fn-dss-stream-items s a nil)
           (if (eq dss-r1 :refused)
               (mv dss-r1 dss-s1 dss-it1)
             (mv-let (dss-r2 dss-s2 dss-it2) (fn-dss-stream-items dss-s1 b last)
               (mv dss-r2 dss-s2 (append dss-it1 dss-it2))))))
  :hints (("Goal" :induct (fn-dss-stream-items s a nil)))))

(local
 (defmacro fn-dss-mv3= (x a b c)
  `(and (equal (mv-nth 0 ,x) ,a) (equal (mv-nth 1 ,x) ,b) (equal (mv-nth 2 ,x) ,c))))

(local
 (defthm fn-dss-list-loop-n-natp
  (natp (mv-nth 3 (fn-dss-stream-list-loop s xs lp room)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-dss-stream-list-loop-consumed))))

(local
 (defthm fn-dss-list-loop-n-bound
  (<= (mv-nth 3 (fn-dss-stream-list-loop s xs lp room)) (len xs))
  :rule-classes :linear
  :hints (("Goal" :use fn-dss-stream-list-loop-consumed))))

(local
 (defthm fn-dss-list-loop-items-prefix
  (mv-let (dss-r dss-s2 dss-outs dss-n) (fn-dss-stream-list-loop s xs lp room)
    (and (implies (eq dss-r :need-input)
                  (fn-dss-mv3= (fn-dss-stream-items s xs nil) :need-input dss-s2 dss-outs))
         (implies (eq dss-r :yield)
                  (fn-dss-mv3= (fn-dss-stream-items s (take dss-n xs) nil)
                               :need-input dss-s2 (append dss-outs (list :yield))))
         (implies (eq dss-r :need-output)
                  (fn-dss-mv3= (fn-dss-stream-items s (take dss-n xs) nil) :need-input dss-s2 dss-outs))
         (implies (and (eq dss-r :refused) (< dss-n (len xs)))
                  (fn-dss-mv3= (fn-dss-stream-items s xs nil) :refused dss-s2 dss-outs))
         (implies (and (or (eq dss-r :refused) (eq dss-r :done)) (not (< dss-n (len xs))))
                  (and lp (fn-dss-mv3= (fn-dss-stream-items s xs t) dss-r dss-s2 dss-outs)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-dss-stream-list-loop s xs lp room)
           :in-theory (disable fn-dss-stream-items-shape fn-dss-stream-items-shape-car)))))

(local
 (defthm fn-dss-list-wrapper-is-loop
  (implies (<= (fn-dss-floor) (nfix room))
           (equal (fn-dss-stream-list s xs lp room)
                  (fn-dss-stream-list-loop s xs lp room)))))

(local
 (defthm fn-dss-list-loop-progress
  (implies (and (<= (fn-dss-floor) (nfix room))
                (member-equal (mv-nth 0 (fn-dss-stream-list-loop s xs lp room)) '(:yield :need-output)))
           (< 0 (mv-nth 3 (fn-dss-stream-list-loop s xs lp room))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-dss-stream-list-loop s xs lp room))))))

(local
 (defthm fn-dss-items-true-list-fix
  (equal (fn-dss-stream-items s (append xs nil) last)
         (fn-dss-stream-items s xs last))
  :hints (("Goal" :induct (fn-dss-stream-items s xs last)))))

(local
 (defthm fn-dss-append-take-nthcdr
  (implies (and (natp dss-n) (<= dss-n (len xs)))
           (equal (append (take dss-n xs) (append (nthcdr dss-n xs) dss-r))
                  (append xs dss-r)))))

(local
 (defthm fn-dss-list-loop-shape
  (mv-let (dss-r dss-s2 dss-outs dss-n) (fn-dss-stream-list-loop s xs lp room)
    (declare (ignore dss-s2 dss-outs))
    (and (member-equal dss-r '(:need-input :need-output :yield :refused :done))
         (implies (eq dss-r :done) (and lp (equal dss-n (len xs))))
         (implies (eq dss-r :need-input) (and (not lp) (equal dss-n (len xs))))
         (implies (eq dss-r :refused) (or (< dss-n (len xs)) (and lp (equal dss-n (len xs)))))
         (implies (eq dss-r :yield) (and (< 0 dss-n) (<= dss-n (len xs))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-dss-stream-list-loop s xs lp room)))))

(local
 (defthm fn-dss-items-atom
  (implies (not (consp xs))
           (equal (fn-dss-stream-items s xs last)
                  (if last
                      (if (eql (fn-dss-st-fsig s) 2)
                          (list :refused (fn-dss-st-fnext s) nil)
                        (list :done (fn-dss-st-fnext s)
                              (fn-oct-word-octets (fn-dss-st-fw s) (fn-dss-st-fk s))))
                    (list :need-input s nil))))))

(local
 (defthm fn-dss-items-last-boolean
  (implies (and last (syntaxp (not (equal last ''t))))
           (equal (fn-dss-stream-items s xs last)
                  (fn-dss-stream-items s xs t)))
  :hints (("Goal" :induct (fn-dss-stream-items s xs last)))))

(local
 (defthm fn-dss-items-refused-any-last
  (implies (equal (car (fn-dss-stream-items s xs nil)) :refused)
           (equal (fn-dss-stream-items s xs last)
                  (fn-dss-stream-items s xs nil)))
  :hints (("Goal" :induct (fn-dss-stream-items s xs last)))))

(local
 (defthm fn-dss-items-refused-any-last-2
  (implies (and (syntaxp (not (equal last ''nil)))
                (equal (car (fn-dss-stream-items s xs nil)) :refused))
           (equal (fn-dss-stream-items s xs last)
                  (fn-dss-stream-items s xs nil)))
  :hints (("Goal" :use fn-dss-items-refused-any-last))))

(local (in-theory (disable fn-dss-items-refused-any-last)))

(local
 (defthm fn-dss-items-step
  (implies (<= (fn-dss-floor) (nfix room))
           (let ((xs (if (consp pieces) (car pieces) nil))
                 (lp (and last (atom (cdr pieces)))))
             (equal (fn-dss-stream-items s (fn-dss-flatten pieces) last)
                    (mv-let (dss-r dss-s2 dss-outs dss-n) (fn-dss-stream-list-loop s xs lp room)
                      (cond ((or (eq dss-r :refused) (eq dss-r :done)) (mv dss-r dss-s2 dss-outs))
                            ((eq dss-r :need-input)
                             (if (consp (cdr pieces))
                                 (mv-let (dss-r3 dss-s3 dss-it)
                                   (fn-dss-stream-items dss-s2 (fn-dss-flatten (cdr pieces)) last)
                                   (mv dss-r3 dss-s3 (append dss-outs dss-it)))
                               (mv dss-r dss-s2 dss-outs)))
                            (t (mv-let (dss-r3 dss-s3 dss-it)
                                 (fn-dss-stream-items
                                  dss-s2 (fn-dss-flatten (cons (nthcdr dss-n xs) (cdr pieces))) last)
                                 (mv dss-r3 dss-s3 (append dss-outs (if (eq dss-r :yield) (cons :yield dss-it) dss-it))))))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-dss-list-loop-shape
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces)))))
                 (:instance fn-dss-list-loop-items-prefix
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces)))))
                 (:instance fn-dss-list-loop-progress
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces)))))
                 (:instance fn-dss-items-append
                  (a (if (consp pieces) (car pieces) nil))
                  (b (fn-dss-flatten (cdr pieces))))
                 (:instance fn-dss-items-append
                  (a (take (mv-nth 3 (fn-dss-stream-list-loop
                                      s (if (consp pieces) (car pieces) nil)
                                      (and last (atom (cdr pieces))) room))
                           (if (consp pieces) (car pieces) nil)))
                  (b (append (nthcdr (mv-nth 3 (fn-dss-stream-list-loop
                                                s (if (consp pieces) (car pieces) nil)
                                                (and last (atom (cdr pieces))) room))
                                     (if (consp pieces) (car pieces) nil))
                             (fn-dss-flatten (cdr pieces))))))
           :in-theory (disable fn-dss-items-append fn-dss-stream-list-loop fn-dss-stream-items)
           :expand ((fn-dss-flatten pieces)
                    (fn-dss-flatten (cons (nthcdr (mv-nth 3 (fn-dss-stream-list-loop
                                                             s (if (consp pieces) (car pieces) nil)
                                                             (and last (atom (cdr pieces))) room))
                                                  (if (consp pieces) (car pieces) nil))
                                          (cdr pieces))))))))

(defthm fn-dss-drive-is-items
  (equal (fn-dss-drive s pieces last rooms)
         (fn-dss-stream-items s (fn-dss-flatten pieces) last))
  :hints (("Goal" :induct (fn-dss-drive s pieces last rooms)
           :expand ((fn-dss-drive s pieces last rooms))
           :in-theory (disable fn-dss-stream-list-loop fn-dss-stream-items fn-dss-flatten
                               fn-dss-stream-list fn-dss-items-append))
          ("Subgoal *1/1"
           :use ((:instance fn-dss-items-step
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-shape
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces))))
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-progress
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces))))
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))))
          ("Subgoal *1/2"
           :use ((:instance fn-dss-items-step
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-shape
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces))))
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-progress
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces))))
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))))
          ("Subgoal *1/3"
           :use ((:instance fn-dss-items-step
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-shape
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces))))
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-progress
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces))))
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))))
          ("Subgoal *1/4"
           :use ((:instance fn-dss-items-step
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-shape
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces))))
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-progress
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces))))
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))))
          ("Subgoal *1/5"
           :use ((:instance fn-dss-items-step
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-shape
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces))))
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-progress
                  (xs (if (consp pieces) (car pieces) nil))
                  (lp (and last (atom (cdr pieces))))
                  (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))))))

; A-HOST-ROOM, the host's contract: each of the first FUEL calls is offered
; at least FLOOR octets of output room (the host sends and clears the output
; before the next call).  A call offered less is refused by name (:no-room)
; and consumes nothing, so the theorem below is not made true by a host that
; never makes room: dss-it is a hypothesis, stated, and a host that breaks dss-it sees
; :no-room.
(defun fn-dss-a-host-room (floor rooms fuel)
  (if (zp fuel)
      t
    (and (consp rooms)
         (<= (nfix floor) (nfix (car rooms)))
         (fn-dss-a-host-room floor (cdr rooms) (1- fuel)))))

; The calls a dss-run needs: one per consumed octet, one per piece, one to end.
(defun fn-dss-calls-bound (pieces)
  (+ 1 (len pieces) (fn-dss-sum-lens pieces)))

; The host loop over the stobj calls: the current piece is the input buffer's
; whole content, I the cursor in dss-it; each call is offered the next room of
; ROOMS on a cleared output, whose octets the host then takes as sent; after
; :yield or :need-output the host calls again at the returned cursor, after
; :need-input dss-it loads the next piece at cursor 0, and LAST is given with the
; final piece only.  FUEL bounds the calls; the dss-run ends :fuel when dss-it is out.
(defun fn-dss-host (s pieces i last rooms fuel fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil
                  :measure (nfix fuel)))
  (if (zp fuel)
      (mv :fuel s nil fn-octets fn-dss-out)
    (let* ((fn-dss-out (fn-dss-out-clear fn-dss-out))
           (dss-lastp (and last (atom (cdr pieces))))
           (cap (nfix (if (consp rooms) (car rooms) 0))))
      (mv-let (dss-r dss-s2 dss-i2 fn-dss-out)
        (fn-dss-stream s i (fn-octets-len fn-octets) dss-lastp cap fn-octets fn-dss-out)
        (let ((dss-outs (fn-dss-out-list fn-dss-out)))
          (cond ((or (eq dss-r :refused) (eq dss-r :done) (eq dss-r :no-room))
                 (mv dss-r dss-s2 dss-outs fn-octets fn-dss-out))
                ((eq dss-r :need-input)
                 (if (consp (cdr pieces))
                     (let ((fn-octets (fn-octets-from-list (cadr pieces) fn-octets)))
                       (mv-let (dss-r3 dss-s3 dss-items fn-octets fn-dss-out)
                         (fn-dss-host dss-s2 (cdr pieces) 0 last (cdr rooms) (1- fuel)
                                      fn-octets fn-dss-out)
                         (mv dss-r3 dss-s3 (append dss-outs dss-items) fn-octets fn-dss-out)))
                   (mv dss-r dss-s2 dss-outs fn-octets fn-dss-out)))
                (t
                 (mv-let (dss-r3 dss-s3 dss-items fn-octets fn-dss-out)
                   (fn-dss-host dss-s2 pieces dss-i2 last (cdr rooms) (1- fuel) fn-octets fn-dss-out)
                   (mv dss-r3 dss-s3 (append dss-outs (if (eq dss-r :yield) (cons :yield dss-items) dss-items))
                       fn-octets fn-dss-out)))))))))

(defun fn-dss-host-run (s pieces last rooms fuel fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
  (let ((fn-octets (fn-octets-from-list (if (consp pieces) (car pieces) nil) fn-octets)))
    (fn-dss-host s pieces 0 last rooms fuel fn-octets fn-dss-out)))

; The partition property of the stobj loop: under A-HOST-ROOM and enough
; fuel, every split of the input and every room schedule yields the one-pass
; logical stream and final state.
; Proof support for the stobj partition property, local: one host call is
; the list model on the rest of the loaded piece, so the host loop under
; A-HOST-ROOM and enough fuel is the drive on the unconsumed input.
(local
 (defthm fn-dss-take-len-self
  (implies (true-listp x) (equal (take (len x) x) x))))

(local
 (defthm fn-dss-len-nthcdr-2
  (implies (and (natp i) (<= i (len x)))
           (equal (len (nthcdr i x)) (- (len x) i)))))

(local
 (defthm fn-dss-true-listp-nthcdr
  (implies (true-listp x) (true-listp (nthcdr i x)))))

(local
 (defthm fn-dss-slice-to-end
  (implies (and (natp i) (<= i (len st)) (true-listp st))
           (equal (fn-oct-slice-list i (len st) st) (nthcdr i st)))
  :hints (("Goal" :use ((:instance fn-oct-slice-list-is-take-nthcdr (n (len st)) (fn-octets st))
                        (:instance fn-dss-take-len-self (x (nthcdr i st))))
           :in-theory (disable fn-oct-slice-list-is-take-nthcdr fn-dss-take-len-self)))))

(local
 (defthm fn-dss-host-call
  (implies (and (natp i) (natp cap) (true-listp st) (<= i (len st)))
           (equal (fn-dss-stream s i (len st) lp cap st nil)
                  (mv-let (dss-r dss-s2 dss-outs dss-n) (fn-dss-stream-list s (nthcdr i st) lp cap)
                    (mv dss-r dss-s2 (+ i dss-n) dss-outs))))
  :hints (("Goal" :use ((:instance fn-dss-stream-is-list (end (len st)) (fn-octets st)
                                   (last lp) (fn-dss-out nil)))
           :in-theory (disable fn-dss-stream-is-list fn-dss-stream fn-dss-stream-list)))))

(local
 (defthm fn-dss-nthcdr-nthcdr
  (implies (and (natp i) (natp dss-n))
           (equal (nthcdr dss-n (nthcdr i x)) (nthcdr (+ i dss-n) x)))))

(local
 (defthm fn-dss-a-host-room-car
  (implies (and (fn-dss-a-host-room floor rooms fuel) (not (zp fuel)))
           (and (consp rooms) (<= (nfix floor) (nfix (car rooms)))
                (fn-dss-a-host-room floor (cdr rooms) (1- fuel))))))

(local
 (defthm fn-dss-host-is-drive
  (implies (and (true-list-listp pieces)
                (equal fn-octets (if (consp pieces) (car pieces) nil))
                (natp i) (<= i (len fn-octets))
                (<= (+ 1 (len pieces) (- (fn-dss-sum-lens pieces) i)) (nfix fuel))
                (fn-dss-a-host-room (fn-dss-floor) rooms fuel))
           (let ((dss-run (fn-dss-host s pieces i last rooms fuel fn-octets fn-dss-out)))
             (equal (list (mv-nth 0 dss-run) (mv-nth 1 dss-run) (mv-nth 2 dss-run))
                    (fn-dss-drive s (cons (nthcdr i (if (consp pieces) (car pieces) nil)) (cdr pieces)) last rooms))))
  :hints (("Goal" :induct (fn-dss-host s pieces i last rooms fuel fn-octets fn-dss-out)
           :expand ((fn-dss-host s pieces i last rooms fuel fn-octets fn-dss-out)
                    (fn-dss-drive s (cons (nthcdr i (if (consp pieces) (car pieces) nil)) (cdr pieces)) last rooms))
           :in-theory (disable fn-dss-stream fn-dss-stream-list fn-dss-stream-list-loop
                               fn-dss-drive-is-items fn-dss-stream-is-list
                               fn-oct-slice-list-is-take-nthcdr))
          ("Subgoal *1/1"
           :use ((:instance fn-dss-host-call (st fn-octets) (lp (and last (atom (cdr pieces))))
                            (cap (nfix (if (consp rooms) (car rooms) 0))))
                 (:instance fn-dss-list-loop-shape (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-progress (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-stream-list-consumed (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (last (and last (atom (cdr pieces))))
                            (room (nfix (if (consp rooms) (car rooms) 0))))))
          ("Subgoal *1/2"
           :use ((:instance fn-dss-host-call (st fn-octets) (lp (and last (atom (cdr pieces))))
                            (cap (nfix (if (consp rooms) (car rooms) 0))))
                 (:instance fn-dss-list-loop-shape (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-progress (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-stream-list-consumed (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (last (and last (atom (cdr pieces))))
                            (room (nfix (if (consp rooms) (car rooms) 0))))))
          ("Subgoal *1/3"
           :use ((:instance fn-dss-host-call (st fn-octets) (lp (and last (atom (cdr pieces))))
                            (cap (nfix (if (consp rooms) (car rooms) 0))))
                 (:instance fn-dss-list-loop-shape (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-progress (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-stream-list-consumed (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (last (and last (atom (cdr pieces))))
                            (room (nfix (if (consp rooms) (car rooms) 0))))))
          ("Subgoal *1/4"
           :use ((:instance fn-dss-host-call (st fn-octets) (lp (and last (atom (cdr pieces))))
                            (cap (nfix (if (consp rooms) (car rooms) 0))))
                 (:instance fn-dss-list-loop-shape (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-progress (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-stream-list-consumed (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (last (and last (atom (cdr pieces))))
                            (room (nfix (if (consp rooms) (car rooms) 0))))))
          ("Subgoal *1/5"
           :use ((:instance fn-dss-host-call (st fn-octets) (lp (and last (atom (cdr pieces))))
                            (cap (nfix (if (consp rooms) (car rooms) 0))))
                 (:instance fn-dss-list-loop-shape (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-progress (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-stream-list-consumed (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (last (and last (atom (cdr pieces))))
                            (room (nfix (if (consp rooms) (car rooms) 0))))))
          ("Subgoal *1/6"
           :use ((:instance fn-dss-host-call (st fn-octets) (lp (and last (atom (cdr pieces))))
                            (cap (nfix (if (consp rooms) (car rooms) 0))))
                 (:instance fn-dss-list-loop-shape (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-progress (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-stream-list-consumed (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (last (and last (atom (cdr pieces))))
                            (room (nfix (if (consp rooms) (car rooms) 0))))))
          ("Subgoal *1/7"
           :use ((:instance fn-dss-host-call (st fn-octets) (lp (and last (atom (cdr pieces))))
                            (cap (nfix (if (consp rooms) (car rooms) 0))))
                 (:instance fn-dss-list-loop-shape (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-list-loop-progress (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (lp (and last (atom (cdr pieces)))) (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
                 (:instance fn-dss-stream-list-consumed (xs (nthcdr i (if (consp pieces) (car pieces) nil))) (last (and last (atom (cdr pieces))))
                            (room (nfix (if (consp rooms) (car rooms) 0)))))))))

(local
 (defthm fn-dss-flatten-cons-car
  (implies (true-list-listp pieces)
           (equal (fn-dss-flatten (cons (if (consp pieces) (car pieces) nil) (cdr pieces)))
                  (fn-dss-flatten pieces)))))

(defthm fn-dss-drive-stobj-is-items
  (implies (and (true-list-listp pieces)
                (<= (fn-dss-calls-bound pieces) (nfix fuel))
                (fn-dss-a-host-room (fn-dss-floor) rooms fuel))
           (let ((dss-run (fn-dss-host-run s pieces last rooms fuel fn-octets fn-dss-out)))
             (equal (list (mv-nth 0 dss-run) (mv-nth 1 dss-run) (mv-nth 2 dss-run))
                    (fn-dss-stream-items s (fn-dss-flatten pieces) last))))
  :hints (("Goal" :use ((:instance fn-dss-host-is-drive (i 0)
                         (fn-octets (if (consp pieces) (car pieces) nil)))
                        (:instance fn-dss-drive-is-items
                         (pieces (cons (if (consp pieces) (car pieces) nil) (cdr pieces)))))
           :in-theory (disable fn-dss-host-is-drive fn-dss-drive-is-items fn-dss-host
                               fn-dss-drive fn-dss-stream-items fn-dss-flatten))))

; Proof support for the writes, state-type and progress theorems, local.
(local
 (defthm fn-dss-st-k-linear
   (implies (fn-cbor-octetp o)
            (<= (fn-dss-st-k s o) (fn-dss-st-emax)))
   :rule-classes :linear
   :hints (("Goal" :use fn-dss-st-emit-contract))))

(local
 (defthm fn-dss-st-k-natp
   (implies (fn-cbor-octetp o) (natp (fn-dss-st-k s o)))
   :rule-classes :type-prescription
   :hints (("Goal" :use fn-dss-st-emit-contract))))

(local
 (defthm fn-dss-st-fk-linear
   (<= (fn-dss-st-fk s) (fn-dss-st-fmax))
   :rule-classes :linear
   :hints (("Goal" :use fn-dss-st-emit-contract))))

(local
 (defthm fn-dss-st-fk-natp
   (natp (fn-dss-st-fk s))
   :rule-classes :type-prescription
   :hints (("Goal" :use fn-dss-st-emit-contract))))

(local
 (defthm fn-dss-len-of-take
   (implies (and (natp m) (<= m (len x)))
            (equal (len (take m x)) m))))

(local
 (defthm fn-dss-stream-loop-writes
   (implies (and (natp i) (natp idx) (true-listp fn-dss-out) (<= idx (len fn-dss-out))
                 (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
            (mv-let (dss-r dss-s2 dss-i2 dss-out2)
              (fn-dss-stream-loop s i end last idx room fn-octets fn-dss-out)
              (declare (ignore dss-r dss-s2))
              (and (<= (len dss-out2) (+ idx (nfix room)))
                   (<= (len dss-out2)
                       (+ idx (* (fn-dss-st-emax) (- dss-i2 i)) (fn-dss-st-fmax)))
                   (<= i dss-i2)
                   (or (<= dss-i2 end) (equal dss-i2 i)))))
   :hints (("Goal" :induct (fn-dss-stream-loop s i end last idx room fn-octets fn-dss-out)
            :in-theory (e/d (fn-oct-get-is-nth fn-dss-put-word$inline
                             (:rewrite fn-oct-nth-of-octet-listp-is-octet . 2))
                            (fn-dss-put-word-rec))))))

(local
 (defthm fn-dss-st-next-keeps-type-rw
   (implies (and (fn-dss-st-statep s) (fn-cbor-octetp o))
            (fn-dss-st-statep (fn-dss-st-next s o)))
   :hints (("Goal" :use fn-dss-st-next-keeps-type))))

(local
 (defthm fn-dss-st-fnext-keeps-type-rw
   (implies (fn-dss-st-statep s)
            (fn-dss-st-statep (fn-dss-st-fnext s)))
   :hints (("Goal" :use (:instance fn-dss-st-next-keeps-type (o 0))))))

(local
 (defthm fn-dss-stream-loop-state-type
   (implies (and (fn-dss-st-statep s) (natp i)
                 (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
            (fn-dss-st-statep (mv-nth 1 (fn-dss-stream-loop s i end last idx room fn-octets fn-dss-out))))
   :hints (("Goal" :induct (fn-dss-stream-loop s i end last idx room fn-octets fn-dss-out)
            :in-theory (enable fn-oct-get-is-nth (:rewrite fn-oct-nth-of-octet-listp-is-octet . 2))))))

(local
 (defthm fn-dss-stream-loop-cursor-mono
   (implies (natp i)
            (<= i (mv-nth 2 (fn-dss-stream-loop s i end last idx room fn-octets fn-dss-out))))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-dss-stream-loop s i end last idx room fn-octets fn-dss-out)))))

(defthm fn-dss-stream-writes
  (implies (and (natp i) (natp cap) (true-listp fn-dss-out)
                (<= (len fn-dss-out) cap)
                (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
           (mv-let (dss-r dss-s2 dss-i2 dss-out2) (fn-dss-stream s i end last cap fn-octets fn-dss-out)
             (declare (ignore dss-r dss-s2))
             (and (<= (len dss-out2) cap)
                  (<= (len dss-out2)
                      (+ (len fn-dss-out) (* (fn-dss-st-emax) (- dss-i2 i)) (fn-dss-st-fmax)))
                  (<= i dss-i2)
                  (or (<= dss-i2 end) (equal dss-i2 i)))))
  :hints (("Goal" :use ((:instance fn-dss-stream-loop-writes
                                   (idx (len fn-dss-out))
                                   (room (nfix (- cap (len fn-dss-out))))
                                   (fn-dss-out (fn-dss-out-append-word 0 (nfix (- cap (len fn-dss-out)))
                                                                       fn-dss-out))))
           :expand ((fn-dss-stream s i end last cap fn-octets fn-dss-out))
           :in-theory (e/d (fn-dss-out-len-is-len fn-dss-out-append-word-is-append)
                           (fn-dss-stream fn-dss-stream-loop fn-dss-stream-loop-writes
                            fn-dss-stream-is-list fn-dss-stream-loop-is-list-general)))))

(defthm fn-dss-stream-state-type
  (implies (and (fn-dss-st-statep s) (natp i)
                (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
           (fn-dss-st-statep (mv-nth 1 (fn-dss-stream s i end last cap fn-octets fn-dss-out))))
  :hints (("Goal" :use ((:instance fn-dss-stream-loop-state-type
                                   (idx (fn-dss-out-len fn-dss-out))
                                   (room (nfix (- cap (fn-dss-out-len fn-dss-out))))
                                   (fn-dss-out (fn-dss-out-append-word
                                                0 (nfix (- cap (fn-dss-out-len fn-dss-out)))
                                                fn-dss-out))))
           :expand ((fn-dss-stream s i end last cap fn-octets fn-dss-out))
           :in-theory (disable fn-dss-stream fn-dss-stream-loop fn-dss-stream-loop-state-type
                               fn-dss-stream-is-list fn-dss-stream-loop-is-list-general))))

(defthm fn-dss-stream-progress
  (implies (and (natp i) (natp end) (< i end) (natp cap)
                (<= (+ (len fn-dss-out) (fn-dss-floor)) cap))
           (mv-let (dss-r dss-s2 dss-i2 dss-out2) (fn-dss-stream s i end last cap fn-octets fn-dss-out)
             (declare (ignore dss-s2 dss-out2))
             (or (equal dss-r :refused) (< i dss-i2))))
  :hints (("Goal" :expand ((fn-dss-stream s i end last cap fn-octets fn-dss-out)
                           (:free (idx room out) (fn-dss-stream-loop s i end last idx room fn-octets out)))
           :in-theory (e/d (fn-dss-out-len-is-len fn-dss-out-append-word-is-append)
                           (fn-dss-stream-loop-is-list-general)))))

; Physical writes of one :stream call, a charge model beside NAME-WORK: the
; entry zeroes the window of the output up to CAP (ROOM cells), then each
; emitted octet is one store (the length of the list model's output).  That
; the compiled loop stores no more than the charge is the disassembly
; evidence's; A-RESERVED is unchanged.
(local
 (defthm fn-dss-octet-listp-of-slice
   (implies (and (fn-cbor-octet-listp st) (<= end (len st)))
            (fn-cbor-octet-listp (fn-oct-slice-list i end st)))
   :hints (("Goal" :induct (fn-dss-idx-ind i end)
            :in-theory (e/d (fn-dss-slice-open fn-dss-slice-empty fn-oct-get-is-nth
                             (:rewrite fn-oct-nth-of-octet-listp-is-octet . 2))
                            (fn-oct-slice-list-is-take-nthcdr))))))

(local
 (defthm fn-dss-emax-nonneg-product
   (implies (natp n) (and (natp (* (fn-dss-st-emax) n)) (<= 0 (* (fn-dss-st-emax) n))))
   :hints (("Goal" :use fn-dss-st-emax-natp :in-theory (disable fn-dss-st-emax-natp)))))

(local
 (defthm fn-dss-list-loop-out-bound
   (implies (fn-cbor-octet-listp xs)
            (<= (len (mv-nth 2 (fn-dss-stream-list-loop s xs last room)))
                (+ (* (fn-dss-st-emax) (mv-nth 3 (fn-dss-stream-list-loop s xs last room)))
                   (fn-dss-st-fmax))))
   :hints (("Goal" :induct (fn-dss-stream-list-loop s xs last room)
            :in-theory (enable (:rewrite fn-oct-nth-of-octet-listp-is-octet . 2))))))

(defun fn-dss-stream-write-charge (s i end last cap fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
  (let ((dss-room (nfix (- (nfix cap) (fn-dss-out-len fn-dss-out)))))
    (if (< dss-room (fn-dss-floor))
        0
      (mv-let (dss-r dss-s2 dss-outs dss-n)
        (fn-dss-stream-list-loop s (fn-oct-slice-list i end fn-octets) last dss-room)
        (declare (ignore dss-r dss-s2 dss-n))
        (+ dss-room (len dss-outs))))))

(local
 (defthm fn-dss-list-loop-out-bound-span
   (implies (and (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
            (<= (len (mv-nth 2 (fn-dss-stream-list-loop s (fn-oct-slice-list i end fn-octets) last room)))
                (+ (* (fn-dss-st-emax) (nfix (- (nfix end) (nfix i)))) (fn-dss-st-fmax))))
   :hints (("Goal" :use ((:instance fn-dss-list-loop-out-bound (xs (fn-oct-slice-list i end fn-octets)))
                         (:instance fn-dss-list-loop-n-bound (xs (fn-oct-slice-list i end fn-octets)) (lp last))
                         fn-dss-len-of-slice-list
                         (:instance fn-dss-octet-listp-of-slice (st fn-octets))
                         (:instance fn-dss-emax-nonneg-product (n (nfix (- (nfix end) (nfix i))))))
            :in-theory (disable fn-dss-list-loop-out-bound fn-dss-list-loop-n-bound
                                fn-dss-len-of-slice-list fn-dss-octet-listp-of-slice
                                fn-dss-emax-nonneg-product)))))

(defthm fn-dss-stream-write-charge-bound
  (implies (and (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
           (<= (fn-dss-stream-write-charge s i end last cap fn-octets fn-dss-out)
               (+ (nfix (- (nfix cap) (len fn-dss-out)))
                  (* (fn-dss-st-emax) (nfix (- (nfix end) (nfix i))))
                  (fn-dss-st-fmax))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-dss-list-loop-out-bound-span
                                   (room (nfix (- (nfix cap) (fn-dss-out-len fn-dss-out))))))
           :do-not-induct t
           :in-theory (e/d (fn-dss-out-len-is-len) (fn-dss-list-loop-out-bound-span nfix)))))

(local
 (defthm fn-dss-st-cost-linear-natp
   (implies (natp (fn-dss-st-cost s o))
            (<= (fn-dss-st-cost s o) (fn-dss-st-cmax)))
   :rule-classes :linear
   :hints (("Goal" :use fn-dss-st-cost-contract))))

(local
 (defthm fn-dss-st-fcost-linear-natp
   (implies (natp (fn-dss-st-fcost s))
            (<= (fn-dss-st-fcost s) (fn-dss-st-fcmax)))
   :rule-classes :linear
   :hints (("Goal" :use fn-dss-st-cost-contract))))

(local
 (defthm fn-dss-st-cmax-natp
   (and (natp (fn-dss-st-cmax)) (natp (fn-dss-st-fcmax)))
   :rule-classes ((:type-prescription :corollary (natp (fn-dss-st-cmax)))
                  (:type-prescription :corollary (natp (fn-dss-st-fcmax))))
   :hints (("Goal" :use fn-dss-st-cost-contract))))

(defthm fn-dss-stream-work-bound
  (<= (fn-dss-stream-work s i end last room fn-octets)
      (+ 1 (fn-dss-st-fcmax)
         (* (+ 1 (fn-dss-st-cmax)) (nfix (- (nfix end) (nfix i))))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-dss-stream-work s i end last room fn-octets))))

; Guard support for generated loops that append (:copy :within), enabled
; only in their guard hints.
(defthm fn-dss-guard-len-append
  (equal (len (append a b)) (+ (len a) (len b))))

(in-theory (disable fn-dss-guard-len-append))

; =============================================================================
; The generator.

(defun fn-dss-name (parts witness)
  (declare (xargs :mode :program))
  (packn-pos parts witness))

(defun fn-dss-and (a b)
  (declare (xargs :mode :program))
  (cond ((eq b t) a) ((eq a t) b) (t `(and ,a ,b))))

; The variables of the library theorems; an instance's own names avoid them.
; Every local the generator binds is named DSS-..., and an instance's own
; names may not start with DSS-; the rest are the library theorems' variables.
(defconst *fn-dss-reserved*
  '(i end j xs fn-octets fn-dss-b fn-dss-out cap last s room pieces rooms fuel))

(defun fn-dss-prefixed (syms)
  (declare (xargs :mode :program))
  (cond ((atom syms) nil)
        ((and (<= 4 (length (symbol-name (car syms))))
              (equal (subseq (symbol-name (car syms)) 0 4) "DSS-"))
         (cons (car syms) (fn-dss-prefixed (cdr syms))))
        (t (fn-dss-prefixed (cdr syms)))))

; The span guard: fixnum indices, END within the buffer.
(defconst *fn-dss-span-guard*
  '(and (unsigned-byte-p 59 i) (unsigned-byte-p 59 end) (<= i end)
        (<= end (fn-octets-len fn-octets))))

(defun fn-dss-type-pred (type var wrld)
  ; The predicate a `(type TYPE VAR)' declaration adds to a guard.
  (declare (xargs :mode :program))
  (translate-declaration-to-guard type var wrld))

(defun fn-dss-guard-theory ()
  (declare (xargs :mode :program))
  '((:rewrite fn-oct-nth-of-octet-listp-is-octet . 1)
    (:rewrite fn-oct-nth-of-octet-listp-is-octet . 2)
    fn-oct-octets-p-is-octet-listp fn-oct-octet-listp-of-append fn-dss-guard-len-append
    fn-dss-put-word-len fn-dss-out-len-is-len fn-dss-out-append-word-is-append
    fn-dss-out-truncate-is-take fn-dss-len-of-out-put))

(defun fn-dss-defs-theory (names)
  ; The instance's definitions, unfolded once, in `minimal-theory' plus what
  ; a numeral-for-constrained-constant substitution needs: nfix is a natural
  ; (its type, not its definition, which would split cases before the unfold).
  (declare (xargs :mode :program))
  `(union-theories '(,@names (:type-prescription nfix) car-cons cdr-cons mv-nth)
                   (union-theories (theory 'minimal-theory)
                                   (executable-counterpart-theory :here))))

; The contracts an instance's body meets, each stated as its own theorem
; before the exported ones and used by them (the library constraint of the
; shape under the instance's substitution, in the library's variable O).
(defun fn-dss-use-contract (name elt)
  (declare (xargs :mode :program))
  (if (eq elt 'o) name `(:instance ,name (,elt o))))

; A contract is proved as the functional instance of the library constraint
; LIB under SUBST, in the default theory plus the instance's :constraint-hints
; (a plist of "Goal" hint keywords).  Proving the constraint here records it
; in ACL2's proved-functional-instances cache, so every later instance theorem
; using the same substitution does not re-prove it in its minimal theory.
(defun fn-dss-occurs (x tree)
  (declare (xargs :mode :program))
  (cond ((eq x tree) t)
        ((atom tree) nil)
        ((eq (car tree) 'quote) nil)
        (t (or (fn-dss-occurs x (car tree)) (fn-dss-occurs x (cdr tree))))))

; The bindings an :instance needs: the instance's own name for a library
; variable, when it differs and the statement mentions it.
(defun fn-dss-binds (binds stmt)
  (declare (xargs :mode :program))
  (cond ((atom binds) nil)
        ((and (not (eq (car (car binds)) (cadr (car binds))))
              (fn-dss-occurs (cadr (car binds)) stmt))
         (cons (car binds) (fn-dss-binds (cdr binds) stmt)))
        (t (fn-dss-binds (cdr binds) stmt))))

(defun fn-dss-contract (name stmt lib subst binds ch)
  ; BINDS maps the library's variables (o, acc) to the instance's names.
  (declare (xargs :mode :program))
  (let ((b (fn-dss-binds binds stmt)))
    `(defthm ,name ,stmt :rule-classes nil
       :hints (("Goal" :use (,(if b
                                  `(:instance (:functional-instance ,lib ,@subst) ,@b)
                                `(:functional-instance ,lib ,@subst)))
                ,@ch)))))

; ---- :find

(defun fn-dss-find-events (name ctx elt body cost cost-max guard guard-hints ch exec)
  (declare (xargs :mode :program))
  (let* ((cc (fn-dss-name (list name (if exec "-EXEC-COST-CONTRACT" "-COST-CONTRACT")) name))
         (lst (fn-dss-name (list name "-LIST") name))
         (work (fn-dss-name (list name (if exec "-EXEC-WORK" "-WORK")) name))
         (bridge (fn-dss-name (list name "-IS-LIST") name))
         (hit (fn-dss-name (list name "-HIT") name))
         (least (fn-dss-name (list name "-LEAST") name))
         (wb (fn-dss-name (list name (if exec "-EXEC-WORK-BOUND" "-WORK-BOUND")) name))
         (subst `((fn-dss-find-p (lambda (,elt) ,body))
                  (fn-dss-find (lambda (i end fn-octets) (,name ,@ctx i end fn-octets)))
                  (fn-dss-find-list (lambda (xs) (,lst ,@ctx xs)))))
         (wsubst `((fn-dss-find-p (lambda (,elt) ,body))
                   (fn-dss-find-cost (lambda (,elt) ,cost))
                   (fn-dss-find-cmax (lambda () ,cost-max))
                   (fn-dss-find-work (lambda (i end fn-octets) (,work ,@ctx i end fn-octets))))))
    `(,(fn-dss-contract cc `(and (natp ,cost-max) (<= (nfix ,cost) ,cost-max))
                        'fn-dss-find-cost-contract
                        `((fn-dss-find-cost (lambda (,elt) ,cost)) (fn-dss-find-cmax (lambda () ,cost-max)))
                        `((o ,elt)) ch)
      (defun ,name (,@ctx i end fn-octets)
        (declare (xargs :stobjs fn-octets
                        :guard ,(fn-dss-and guard *fn-dss-span-guard*)
                        :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))
                        :verify-guards nil)
                 (type (unsigned-byte 59) i end))
        (if (and (mbt (and (natp i) (natp end))) (< i end))
            (if (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,body)
                i
              (,name ,@ctx (+ 1 i) end fn-octets))
          nil))
      (defun ,lst (,@ctx xs)
        (declare (xargs :verify-guards nil))
        (if (consp xs)
            (if (let ((,elt (car xs))) (declare (ignorable ,elt)) ,body)
                0
              (let ((dss-k (,lst ,@ctx (cdr xs))))
                (if dss-k (+ 1 dss-k) nil)))
          nil))
      (defun ,work (,@ctx i end fn-octets)
        (declare (xargs :stobjs fn-octets :verify-guards nil
                        :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
        (if (and (mbt (and (natp i) (natp end))) (< i end))
            (+ 1 (nfix (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,cost))
               (if (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,body)
                   0
                 (,work ,@ctx (+ 1 i) end fn-octets)))
          1))
      (defthm ,bridge
        (equal (,name ,@ctx i end fn-octets)
               (let ((dss-k (,lst ,@ctx (fn-oct-slice-list i end fn-octets))))
                 (if dss-k (+ i dss-k) nil)))
        :hints (("Goal" :use ((:functional-instance fn-dss-find-is-list ,@subst))
                 :in-theory ,(fn-dss-defs-theory (list name lst)))))
      (defthm ,hit
        (let ((dss-r (,name ,@ctx i end fn-octets)))
          (implies dss-r
                   (and (natp dss-r) (<= i dss-r) (< dss-r end)
                        (let ((,elt (nth dss-r fn-octets))) (declare (ignorable ,elt)) ,body))))
        :hints (("Goal" :use ((:functional-instance fn-dss-find-hit ,@subst))
                 :in-theory ,(fn-dss-defs-theory (list name lst)))))
      (defthm ,least
        (let ((dss-r (,name ,@ctx i end fn-octets)))
          (implies (and (natp i) (natp end) (natp j) (<= i j) (< j end)
                        (or (null dss-r) (< j dss-r)))
                   (not (let ((,elt (nth j fn-octets))) (declare (ignorable ,elt)) ,body))))
        :hints (("Goal" :use ((:functional-instance fn-dss-find-least ,@subst))
                 :in-theory ,(fn-dss-defs-theory (list name lst)))))
      (defthm ,wb
        (<= (,work ,@ctx i end fn-octets)
            (+ 1 (* (+ 1 ,cost-max) (nfix (- (nfix end) (nfix i))))))
        :rule-classes :linear
        :hints (("Goal" :use (,(fn-dss-use-contract cc elt)
                                     (:functional-instance fn-dss-find-work-bound ,@wsubst))
                 :expand ((,work ,@ctx i end fn-octets))
                 :in-theory ,(fn-dss-defs-theory (list work)))))
      (verify-guards ,name
        :hints ,(or guard-hints
                    `(("Goal" :in-theory (enable ,@(fn-dss-guard-theory))))))
      (table fn-generated ',name
             '(:def-span-scan :shape :find :list ,lst :work ,work :bridge ,bridge
                              :c0 1 :c1 (+ 1 ,cost-max) :writes 0 :workspace (i))))))

; ---- :fold

(defun fn-dss-fold-events (name ctx elt acc acc-type body cost cost-max guard guard-hints ch wrld exec)
  (declare (xargs :mode :program))
  (let* ((cc (fn-dss-name (list name (if exec "-EXEC-COST-CONTRACT" "-COST-CONTRACT")) name))
         (tc (fn-dss-name (list name "-BODY-TYPE") name))
         (lst (fn-dss-name (list name "-LIST") name))
         (work (fn-dss-name (list name (if exec "-EXEC-WORK" "-WORK")) name))
         (bridge (fn-dss-name (list name "-IS-LIST") name))
         (ty (fn-dss-name (list name "-ACC-TYPE") name))
         (wb (fn-dss-name (list name (if exec "-EXEC-WORK-BOUND" "-WORK-BOUND")) name))
         (accp (fn-dss-type-pred acc-type acc wrld))
         (subst `((fn-dss-fold-f (lambda (,acc ,elt) ,body))
                  (fn-dss-fold-accp (lambda (,acc) ,accp))
                  (fn-dss-fold (lambda (,acc i end fn-octets) (,name ,@ctx ,acc i end fn-octets)))
                  (fn-dss-fold-list (lambda (,acc xs) (,lst ,@ctx ,acc xs)))))
         (tsubst subst)
         (wsubst `((fn-dss-fold-f (lambda (,acc ,elt) ,body))
                   (fn-dss-fold-accp (lambda (,acc) ,accp))
                   (fn-dss-fold-cost (lambda (,acc ,elt) ,cost))
                   (fn-dss-fold-cmax (lambda () ,cost-max))
                   (fn-dss-fold-work (lambda (,acc i end fn-octets)
                                       (,work ,@ctx ,acc i end fn-octets))))))
    `(,(fn-dss-contract tc `(implies (and ,accp (fn-cbor-octetp ,elt))
                                      ,(fn-dss-type-pred acc-type body wrld))
                        'fn-dss-fold-f-keeps-type
                        `((fn-dss-fold-f (lambda (,acc ,elt) ,body)) (fn-dss-fold-accp (lambda (,acc) ,accp)))
                        `((o ,elt) (acc ,acc)) ch)
      ,(fn-dss-contract cc `(and (natp ,cost-max) (<= (nfix ,cost) ,cost-max))
                        'fn-dss-fold-cost-contract
                        `((fn-dss-fold-cost (lambda (,acc ,elt) ,cost)) (fn-dss-fold-cmax (lambda () ,cost-max)))
                        `((o ,elt) (acc ,acc)) ch)
      (defun ,name (,@ctx ,acc i end fn-octets)
        (declare (xargs :stobjs fn-octets
                        :guard ,(fn-dss-and guard *fn-dss-span-guard*)
                        :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))
                        :verify-guards nil)
                 (type ,acc-type ,acc)
                 (type (unsigned-byte 59) i end))
        (if (and (mbt (and (natp i) (natp end))) (< i end))
            (,name ,@ctx (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,body) (+ 1 i) end fn-octets)
          ,acc))
      (defun ,lst (,@ctx ,acc xs)
        (declare (xargs :verify-guards nil))
        (if (consp xs)
            (,lst ,@ctx (let ((,elt (car xs))) (declare (ignorable ,elt)) ,body) (cdr xs))
          ,acc))
      (defun ,work (,@ctx ,acc i end fn-octets)
        (declare (xargs :stobjs fn-octets :verify-guards nil
                        :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
        (if (and (mbt (and (natp i) (natp end))) (< i end))
            (+ 1 (nfix (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,cost))
               (,work ,@ctx (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,body) (+ 1 i) end fn-octets))
          1))
      (defthm ,bridge
        (equal (,name ,@ctx ,acc i end fn-octets)
               (,lst ,@ctx ,acc (fn-oct-slice-list i end fn-octets)))
        :hints (("Goal" :use ((:functional-instance fn-dss-fold-is-list ,@subst))
                 :in-theory ,(fn-dss-defs-theory (list name lst)))))
      (defthm ,ty
        (implies (and ,accp
                      (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
                 ,(fn-dss-type-pred acc-type `(,name ,@ctx ,acc i end fn-octets) wrld))
        :hints (("Goal" :use (,(fn-dss-use-contract tc elt)
                                     (:functional-instance fn-dss-fold-acc-type ,@tsubst))
                 :in-theory ,(fn-dss-defs-theory (list name lst)))))
      (defthm ,wb
        (<= (,work ,@ctx ,acc i end fn-octets)
            (+ 1 (* (+ 1 ,cost-max) (nfix (- (nfix end) (nfix i))))))
        :rule-classes :linear
        :hints (("Goal" :use (,(fn-dss-use-contract cc elt)
                                     (:functional-instance fn-dss-fold-work-bound ,@wsubst))
                 :expand ((,work ,@ctx ,acc i end fn-octets))
                 :in-theory ,(fn-dss-defs-theory (list work)))))
      (verify-guards ,name
        :hints ,(or guard-hints
                    `(("Goal" :in-theory (enable ,@(fn-dss-guard-theory))))))
      (table fn-generated ',name
             '(:def-span-scan :shape :fold :list ,lst :work ,work :bridge ,bridge
                              :c0 1 :c1 (+ 1 ,cost-max) :writes 0
                              :workspace (i ,acc :type ,acc-type))))))

; ---- :equal

(defun fn-dss-equal-events (name ctx elt norm cost cost-max against constant guard guard-hints ch exec)
  (declare (xargs :mode :program))
  (let* ((cc (fn-dss-name (list name (if exec "-EXEC-COST-CONTRACT" "-COST-CONTRACT")) name))
         (ccv (fn-dss-contract cc `(and (natp ,cost-max) (<= (nfix ,cost) ,cost-max))
                               'fn-dss-eq-cost-contract
                               `((fn-dss-eq-cost (lambda (,elt) ,cost)) (fn-dss-eq-cmax (lambda () ,cost-max)))
                               `((o ,elt)) ch))
         (nc (fn-dss-name (list name "-NORM-OCTET") name))
         (ncv (fn-dss-contract nc `(implies (fn-cbor-octetp ,elt) (fn-cbor-octetp ,norm))
                               'fn-dss-eq-norm-octet `((fn-dss-eq-norm (lambda (,elt) ,norm))) `((o ,elt)) ch))
         (unc (fn-dss-use-contract nc elt))
         (loop (fn-dss-name (list name "-LOOP") name))
         (lst (fn-dss-name (list name "-LIST") name))
         (work (fn-dss-name (list name (if exec "-EXEC-WORK" "-WORK")) name))
         (bridge (fn-dss-name (list name "-IS-LIST") name))
         (wb (fn-dss-name (list name (if exec "-EXEC-WORK-BOUND" "-WORK-BOUND")) name))
         (normf `(lambda (,elt) ,norm))
         (lsubst `((fn-dss-eq-norm ,normf)
                   (fn-dss-eq-list (lambda (xs) (,lst ,@ctx xs)))))
         (list-def
          `(defun ,lst (,@ctx xs)
             (declare (xargs :verify-guards nil))
             (if (consp xs)
                 (cons (let ((,elt (car xs))) (declare (ignorable ,elt)) ,norm) (,lst ,@ctx (cdr xs)))
               nil))))
    (if (eq against :span)
        `(,ncv ,ccv
          (defun ,name (,@ctx i end fn-octets j fn-dss-b)
            (declare (xargs :stobjs (fn-octets fn-dss-b)
                            :guard ,(fn-dss-and guard
                                                `(and ,*fn-dss-span-guard*
                                                      (unsigned-byte-p 59 j)
                                                      (unsigned-byte-p 59 (+ j (- end i)))
                                                      (<= (+ j (- end i)) (fn-dss-b-len fn-dss-b))))
                            :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))
                            :verify-guards nil)
                     (type (unsigned-byte 59) i end j))
            (if (and (mbt (and (natp i) (natp end) (natp j))) (< i end))
                (and (equal (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,norm)
                            (let ((,elt (fn-dss-b-get j fn-dss-b))) (declare (ignorable ,elt)) ,norm))
                     (,name ,@ctx (+ 1 i) end fn-octets (+ 1 j) fn-dss-b))
              t))
          ,list-def
          (defun ,work (,@ctx i end fn-octets j fn-dss-b)
            (declare (xargs :stobjs (fn-octets fn-dss-b) :verify-guards nil
                            :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
            (if (and (mbt (and (natp i) (natp end) (natp j))) (< i end))
                (+ 1 (nfix (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,cost))
                   (nfix (let ((,elt (fn-dss-b-get j fn-dss-b))) (declare (ignorable ,elt)) ,cost))
                   (if (equal (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,norm)
                              (let ((,elt (fn-dss-b-get j fn-dss-b))) (declare (ignorable ,elt)) ,norm))
                       (,work ,@ctx (+ 1 i) end fn-octets (+ 1 j) fn-dss-b)
                     0))
              1))
          (defthm ,bridge
            (implies (and (natp i) (natp j))
                     (equal (,name ,@ctx i end fn-octets j fn-dss-b)
                            (equal (,lst ,@ctx (fn-oct-slice-list i end fn-octets))
                                   (,lst ,@ctx (fn-oct-slice-list
                                                j (+ j (nfix (- (nfix end) (nfix i)))) fn-dss-b)))))
            :hints (("Goal" :use (,unc
                                  (:functional-instance
                                   fn-dss-eqs-is-list ,@lsubst
                                   (fn-dss-eqs (lambda (i end fn-octets j fn-dss-b)
                                                 (,name ,@ctx i end fn-octets j fn-dss-b)))))
                     :in-theory ,(fn-dss-defs-theory (list name lst)))))
          (defthm ,wb
            (<= (,work ,@ctx i end fn-octets j fn-dss-b)
                (+ 1 (* (+ 1 (* 2 ,cost-max)) (nfix (- (nfix end) (nfix i))))))
            :rule-classes :linear
            :hints (("Goal" :use (,unc ,(fn-dss-use-contract cc elt)
                                  (:functional-instance
                                   fn-dss-eqs-work-bound
                                   (fn-dss-eq-norm ,normf)
                                   (fn-dss-eq-cost (lambda (,elt) ,cost))
                                   (fn-dss-eq-cmax (lambda () ,cost-max))
                                   (fn-dss-eqs-work (lambda (i end fn-octets j fn-dss-b)
                                                      (,work ,@ctx i end fn-octets j fn-dss-b)))))
                     :expand ((,work ,@ctx i end fn-octets j fn-dss-b))
                 :in-theory ,(fn-dss-defs-theory (list work)))))
          (verify-guards ,name
            :hints ,(or guard-hints
                        `(("Goal" :in-theory (enable ,@(fn-dss-guard-theory))))))
          (table fn-generated ',name
                 '(:def-span-scan :shape :equal :against :span :list ,lst :work ,work
                                  :bridge ,bridge :c0 1 :c1 (+ 1 (* 2 ,cost-max)) :writes 0
                                  :workspace (i j))))
      `(,ncv ,ccv
        (defun ,loop (,@ctx i end fn-octets xs)
          (declare (xargs :stobjs fn-octets
                          :guard ,(fn-dss-and guard *fn-dss-span-guard*)
                          :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))
                          :verify-guards nil)
                   (type (unsigned-byte 59) i end))
          (if (and (mbt (and (natp i) (natp end))) (< i end))
              (and (consp xs)
                   (equal (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,norm) (car xs))
                   (,loop ,@ctx (+ 1 i) end fn-octets (cdr xs)))
            (null xs)))
        (defun ,name (,@ctx i end fn-octets)
          (declare (xargs :stobjs fn-octets
                          :guard ,(fn-dss-and guard *fn-dss-span-guard*)
                          :verify-guards nil))
          (,loop ,@ctx i end fn-octets ',constant))
        ,list-def
        (defun ,work (,@ctx i end fn-octets xs)
          (declare (xargs :stobjs fn-octets :verify-guards nil
                          :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
          (if (and (mbt (and (natp i) (natp end))) (< i end))
              (+ 1 (nfix (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,cost))
                 (if (and (consp xs)
                          (equal (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,norm) (car xs)))
                     (,work ,@ctx (+ 1 i) end fn-octets (cdr xs))
                   0))
            1))
        (defthm ,bridge
          (equal (,name ,@ctx i end fn-octets)
                 (equal (,lst ,@ctx (fn-oct-slice-list i end fn-octets)) ',constant))
          :hints (("Goal" :use (,unc
                                (:instance
                                 (:functional-instance
                                  fn-dss-eqc-is-list ,@lsubst
                                  (fn-dss-eqc (lambda (i end fn-octets xs)
                                                (,loop ,@ctx i end fn-octets xs))))
                                 (xs ',constant)))
                   :in-theory ,(fn-dss-defs-theory (list name loop lst)))))
        (defthm ,wb
          (<= (,work ,@ctx i end fn-octets ',constant)
              (+ 1 (* (+ 1 ,cost-max) (nfix (- (nfix end) (nfix i))))))
          :rule-classes :linear
          :hints (("Goal" :use (,unc ,(fn-dss-use-contract cc elt)
                                (:instance
                                 (:functional-instance
                                  fn-dss-eqc-work-bound
                                  (fn-dss-eq-norm ,normf)
                                  (fn-dss-eq-cost (lambda (,elt) ,cost))
                                  (fn-dss-eq-cmax (lambda () ,cost-max))
                                  (fn-dss-eqc-work (lambda (i end fn-octets xs)
                                                     (,work ,@ctx i end fn-octets xs))))
                                 (xs ',constant)))
                   :expand ((,work ,@ctx i end fn-octets xs))
                 :in-theory ,(fn-dss-defs-theory (list work)))))
        (verify-guards ,loop
          :hints ,(or guard-hints
                      `(("Goal" :in-theory (enable ,@(fn-dss-guard-theory))))))
        (verify-guards ,name)
        (table fn-generated ',name
               '(:def-span-scan :shape :equal :against :constant :loop ,loop :list ,lst
                                :work ,work :bridge ,bridge :c0 1 :c1 (+ 1 ,cost-max)
                                :writes 0 :workspace (i)))))))

; ---- :copy

(defun fn-dss-copy-events (name ctx elt map cost cost-max within guard guard-hints ch exec)
  (declare (xargs :mode :program))
  (let* ((cc (fn-dss-name (list name (if exec "-EXEC-COST-CONTRACT" "-COST-CONTRACT")) name))
         (mc (fn-dss-name (list name "-MAP-OCTET") name))
         (loop (fn-dss-name (list name "-LOOP") name))
         (lst (fn-dss-name (list name "-LIST") name))
         (work (fn-dss-name (list name (if exec "-EXEC-WORK" "-WORK")) name))
         (bridge (fn-dss-name (list name "-IS-LIST") name))
         (wb (fn-dss-name (list name (if exec "-EXEC-WORK-BOUND" "-WORK-BOUND")) name))
         (wc (fn-dss-name (list name "-WRITE-CHARGE") name))
         (wcb (fn-dss-name (list name "-WRITE-CHARGE-BOUND") name))
         (mapf `(lambda (,elt) ,map))
         (dst (if within 'fn-octets 'fn-dss-out))
         (dst-len (if within '(fn-octets-len fn-octets) '(fn-dss-out-len fn-dss-out)))
         (dst-reserve (if within 'fn-octets-reserve 'fn-dss-out-reserve))
         (dst-append (if within 'fn-octets-append-octet 'fn-dss-out-append-octet))
         (stobjs (if within 'fn-octets '(fn-octets fn-dss-out)))
         (sfs (if within '(fn-octets) '(fn-octets fn-dss-out)))
         (subst `((fn-dss-copy-f ,mapf)
                  (fn-dss-copy-list (lambda (xs) (,lst ,@ctx xs)))
                  (,(if within 'fn-dss-copyw-loop 'fn-dss-copy-loop)
                   ,(if within
                        `(lambda (i end ,@sfs) (,loop ,@ctx i end ,@sfs))
                      `(lambda (i end j ,@sfs) (,loop ,@ctx i end j ,@sfs))))
                  (,(if within 'fn-dss-copyw 'fn-dss-copy)
                   (lambda (i end cap ,@sfs) (,name ,@ctx i end cap ,@sfs))))))
    `(,(fn-dss-contract mc `(implies (fn-cbor-octetp ,elt) (fn-cbor-octetp ,map))
                        'fn-dss-copy-f-octet `((fn-dss-copy-f ,mapf)) `((o ,elt)) ch)
      ,(fn-dss-contract cc `(and (natp ,cost-max) (<= (nfix ,cost) ,cost-max))
                        'fn-dss-copy-cost-contract
                        `((fn-dss-copy-cost (lambda (,elt) ,cost)) (fn-dss-copy-cmax (lambda () ,cost-max)))
                        `((o ,elt)) ch)
      ,@(if within
            `((defun ,loop (,@ctx i end ,@sfs)
                (declare (xargs :stobjs ,stobjs
                                :guard ,(fn-dss-and guard
                                                    `(and ,*fn-dss-span-guard*
                                                          (<= end (fn-octets-len fn-octets))))
                                :measure (nfix (- (nfix end) (nfix i)))
                                :hints (("Goal" :in-theory (fn-dss-measure-theory)))
                                :verify-guards nil)
                         (type (unsigned-byte 59) i end))
                (if (and (mbt (and (natp i) (natp end))) (< i end))
                    (let ((,dst (,dst-append (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,map) ,dst)))
                      (,loop ,@ctx (+ 1 i) end ,@sfs))
                  ,dst))
              (defun ,name (,@ctx i end cap ,@sfs)
                (declare (xargs :stobjs ,stobjs
                                :guard ,(fn-dss-and guard `(and ,*fn-dss-span-guard* (natp cap)))
                                :verify-guards nil)
                         (type (unsigned-byte 59) i end))
                (let ((dss-n (+ ,dst-len (nfix (- (nfix end) (nfix i))))))
                  (if (<= dss-n (nfix cap))
                      (let* ((,dst (,dst-reserve dss-n ,dst))
                             (,dst (,loop ,@ctx i end ,@sfs)))
                        (mv :done ,dst))
                    (mv :refused ,dst)))))
          ; The destination is extended once by END - I zero octets after the
          ; capacity check (the exported zero-word append), then the loop stores
          ; each octet at its index J with `put'.  The loop touches no fill point.
          `((defun ,loop (,@ctx i end j ,@sfs)
              (declare (xargs :stobjs ,stobjs
                              :guard ,(fn-dss-and guard
                                                  `(and ,*fn-dss-span-guard*
                                                        (unsigned-byte-p 59 j)
                                                        (unsigned-byte-p 59 (+ j (- end i)))
                                                        (<= (+ j (- end i)) (fn-dss-out-len fn-dss-out))))
                              :measure (nfix (- (nfix end) (nfix i)))
                              :hints (("Goal" :in-theory (fn-dss-measure-theory)))
                              :verify-guards nil)
                       (type (unsigned-byte 59) i end j))
              (if (and (mbt (and (natp i) (natp end))) (< i end))
                  (let ((fn-dss-out (fn-dss-out-put j (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,map)
                                                    fn-dss-out)))
                    (,loop ,@ctx (+ 1 i) end (+ 1 j) ,@sfs))
                fn-dss-out))
            (defun ,name (,@ctx i end cap ,@sfs)
              (declare (xargs :stobjs ,stobjs
                              :guard ,(fn-dss-and guard `(and ,*fn-dss-span-guard* (unsigned-byte-p 59 cap)))
                              :verify-guards nil)
                       (type (unsigned-byte 59) i end))
              (let ((dss-m (nfix (- (nfix end) (nfix i)))))
                (if (<= (+ (fn-dss-out-len fn-dss-out) dss-m) (nfix cap))
                    (let* ((dss-j (fn-dss-out-len fn-dss-out))
                           (fn-dss-out (fn-dss-out-reserve (+ dss-j dss-m) fn-dss-out))
                           (fn-dss-out (fn-dss-out-append-word 0 (if (and (natp i) (natp end)) dss-m 0)
                                                               fn-dss-out))
                           (fn-dss-out (,loop ,@ctx i end dss-j ,@sfs)))
                      (mv :done fn-dss-out))
                  (mv :refused fn-dss-out))))))
      (defun ,lst (,@ctx xs)
        (declare (xargs :verify-guards nil))
        (if (consp xs)
            (cons (let ((,elt (car xs))) (declare (ignorable ,elt)) ,map) (,lst ,@ctx (cdr xs)))
          nil))
      (defun ,work (,@ctx i end fn-octets)
        (declare (xargs :stobjs fn-octets :verify-guards nil
                        :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
        (if (and (mbt (and (natp i) (natp end))) (< i end))
            (+ 1 (nfix (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt)) ,cost))
               (,work ,@ctx (+ 1 i) end fn-octets))
          1))
      (defthm ,bridge
        (implies ,(if within
                      '(and (true-listp fn-octets) (<= end (len fn-octets)))
                    '(true-listp fn-dss-out))
                 (equal (,name ,@ctx i end cap ,@sfs)
                        (if (<= (+ (len ,dst) (nfix (- (nfix end) (nfix i)))) (nfix cap))
                            (mv :done (append ,dst (,lst ,@ctx (fn-oct-slice-list i end fn-octets))))
                          (mv :refused ,dst))))
        :hints (("Goal" :use (,(fn-dss-use-contract mc elt)
                              (:functional-instance
                               ,(if within 'fn-dss-copyw-is-list 'fn-dss-copy-is-list) ,@subst))
                 :in-theory ,(fn-dss-defs-theory (list name loop lst)))))
      (defthm ,wb
        (<= (,work ,@ctx i end fn-octets)
            (+ 1 (* (+ 1 ,cost-max) (nfix (- (nfix end) (nfix i))))))
        :rule-classes :linear
        :hints (("Goal" :use (,(fn-dss-use-contract mc elt) ,(fn-dss-use-contract cc elt)
                              (:functional-instance
                               fn-dss-copy-work-bound
                               (fn-dss-copy-f ,mapf)
                               (fn-dss-copy-cost (lambda (,elt) ,cost))
                               (fn-dss-copy-cmax (lambda () ,cost-max))
                               (fn-dss-copy-work (lambda (i end fn-octets)
                                                   (,work ,@ctx i end fn-octets)))))
                 :expand ((,work ,@ctx i end fn-octets))
                 :in-theory ,(fn-dss-defs-theory (list work)))))
      ,@(and (not within)
             `((defun ,wc (,@ctx i end cap fn-octets fn-dss-out)
                 (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
                 (let ((dss-m (nfix (- (nfix end) (nfix i)))))
                   (if (<= (+ (fn-dss-out-len fn-dss-out) dss-m) (nfix cap))
                       (+ dss-m (len (,lst ,@ctx (fn-oct-slice-list i end fn-octets))))
                     0)))
               (defthm ,wcb
                 (<= (,wc ,@ctx i end cap fn-octets fn-dss-out)
                     (* 2 (nfix (- (nfix end) (nfix i)))))
                 :rule-classes :linear
                 :hints (("Goal" :use (,(fn-dss-use-contract mc elt)
                                       (:functional-instance
                                        fn-dss-copy-write-charge-bound
                                        (fn-dss-copy-f ,mapf)
                                        (fn-dss-copy-list (lambda (xs) (,lst ,@ctx xs)))
                                        (fn-dss-copy-write-charge
                                         (lambda (i end cap fn-octets fn-dss-out)
                                           (,wc ,@ctx i end cap fn-octets fn-dss-out)))))
                          :in-theory ,(fn-dss-defs-theory (list wc lst)))))))
      (verify-guards ,loop
        :hints ,(or guard-hints
                    `(("Goal" :in-theory (enable ,@(fn-dss-guard-theory))))))
      (verify-guards ,name)
      (table fn-generated ',name
             '(:def-span-scan :shape :copy :within ,within :loop ,loop :list ,lst :work ,work
                              :bridge ,bridge :c0 1 :c1 (+ 1 ,cost-max)
                              :writes ,(if within '(- end i) '(* 2 (- end i)))
                              :workspace (i))))))

; ---- :stream

(defun fn-dss-stream-events (name ctx elt state-type step final emit-max final-max
                                  cost cost-max final-cost final-cost-max guard guard-hints
                                  constraint-hints wrld exec)
  (declare (xargs :mode :program))
  (let* ((loopn (fn-dss-name (list name "-LOOP") name))
         (lst (fn-dss-name (list name "-LIST") name))
         (lstl (fn-dss-name (list name "-LIST-LOOP") name))
         (host (fn-dss-name (list name "-HOST") name))
         (run (fn-dss-name (list name "-HOST-RUN") name))
         (spart (fn-dss-name (list name "-DRIVE-STOBJ-IS-ITEMS") name))
         (cons (fn-dss-name (list name "-LIST-CONSUMED") name))
         (floor (max emit-max final-max))
         (items (fn-dss-name (list name "-ITEMS") name))
         (drive (fn-dss-name (list name "-DRIVE") name))
         (work (fn-dss-name (list name (if exec "-EXEC-WORK" "-WORK")) name))
         (bridge (fn-dss-name (list name "-IS-LIST") name))
         (part (fn-dss-name (list name "-DRIVE-IS-ITEMS") name))
         (writes (fn-dss-name (list name "-WRITES") name))
         (ty (fn-dss-name (list name "-STATE-TYPE") name))
         (prog (fn-dss-name (list name "-PROGRESS") name))
         (wc (fn-dss-name (list name "-WRITE-CHARGE") name))
         (wcb (fn-dss-name (list name "-WRITE-CHARGE-BOUND") name))
         (fk (fn-dss-name (list name "-STEP-K-NATP") name))
         (fkb (fn-dss-name (list name "-STEP-K-BOUND") name))
         (fw (fn-dss-name (list name "-STEP-W-BYTES") name))
         (ffk (fn-dss-name (list name "-FINAL-K-NATP") name))
         (ffkb (fn-dss-name (list name "-FINAL-K-BOUND") name))
         (ffw (fn-dss-name (list name "-FINAL-W-BYTES") name))
         (wb (fn-dss-name (list name (if exec "-EXEC-WORK-BOUND" "-WORK-BOUND")) name))
         (statep (fn-dss-type-pred state-type 's wrld))
         (stepf `(lambda (s ,elt) ,step))
         (core `((fn-dss-st-next (lambda (s ,elt) (mv-nth 0 ,step)))
                 (fn-dss-st-k (lambda (s ,elt) (mv-nth 1 ,step)))
                 (fn-dss-st-w (lambda (s ,elt) (mv-nth 2 ,step)))
                 (fn-dss-st-sig (lambda (s ,elt) (mv-nth 3 ,step)))
                 (fn-dss-st-fnext (lambda (s) (mv-nth 0 ,final)))
                 (fn-dss-st-fk (lambda (s) (mv-nth 1 ,final)))
                 (fn-dss-st-fw (lambda (s) (mv-nth 2 ,final)))
                 (fn-dss-st-fsig (lambda (s) (mv-nth 3 ,final)))
                 (fn-dss-st-emax (lambda () ,emit-max))
                 (fn-dss-st-fmax (lambda () ,final-max))))
         (lsubst `((fn-dss-floor (lambda () ,floor))
                   (fn-dss-stream-list (lambda (s xs last room) (,lst ,@ctx s xs last room)))
                   (fn-dss-stream-list-loop (lambda (s xs last room) (,lstl ,@ctx s xs last room)))))
         (ssubst `(,@core ,@lsubst
                   (fn-dss-stream (lambda (s i end last cap fn-octets fn-dss-out)
                                    (,name ,@ctx s i end last cap fn-octets fn-dss-out)))
                   (fn-dss-stream-loop (lambda (s i end last idx room fn-octets fn-dss-out)
                                         (,loopn ,@ctx s i end last idx room fn-octets fn-dss-out)))))
         (hsubst `(,@ssubst
                   (fn-dss-stream-items (lambda (s xs last) (,items ,@ctx s xs last)))
                   (fn-dss-host (lambda (s pieces i last rooms fuel fn-octets fn-dss-out)
                                  (,host ,@ctx s pieces i last rooms fuel fn-octets fn-dss-out)))
                   (fn-dss-host-run (lambda (s pieces last rooms fuel fn-octets fn-dss-out)
                                      (,run ,@ctx s pieces last rooms fuel fn-octets fn-dss-out)))))
         (isubst `(,@core ,@lsubst
                   (fn-dss-stream-items (lambda (s xs last) (,items ,@ctx s xs last)))
                   (fn-dss-drive (lambda (s pieces last rooms) (,drive ,@ctx s pieces last rooms)))))
         (wsubst `(,@core
                   (fn-dss-st-cost (lambda (s ,elt) ,cost))
                   (fn-dss-st-cmax (lambda () ,cost-max))
                   (fn-dss-st-fcost (lambda (s) ,final-cost))
                   (fn-dss-st-fcmax (lambda () ,final-cost-max))
                   (fn-dss-stream-work (lambda (s i end last room fn-octets)
                                         (,work ,@ctx s i end last room fn-octets)))))
         (wcsubst `(,@core ,@lsubst
                    (fn-dss-stream-write-charge
                     (lambda (s i end last cap fn-octets fn-dss-out)
                       (,wc ,@ctx s i end last cap fn-octets fn-dss-out)))))
         (sc (fn-dss-name (list name "-STEP-CONTRACT") name))
         (stc (fn-dss-name (list name "-STEP-TYPE") name))
         (cc (fn-dss-name (list name (if exec "-EXEC-COST-CONTRACT" "-COST-CONTRACT")) name))
         (usc (fn-dss-use-contract sc elt)))
    (declare (ignorable stepf))
    `(,(fn-dss-contract
        sc
        `(and (natp ,emit-max) (<= ,emit-max 7) (natp ,final-max) (<= ,final-max 7)
              (implies (fn-cbor-octetp ,elt)
                       (and (natp (mv-nth 1 ,step)) (<= (mv-nth 1 ,step) ,emit-max)
                            (unsigned-byte-p 56 (mv-nth 2 ,step))))
              (natp (mv-nth 1 ,final)) (<= (mv-nth 1 ,final) ,final-max)
              (unsigned-byte-p 56 (mv-nth 2 ,final)))
        'fn-dss-st-emit-contract core `((o ,elt)) constraint-hints)
      ,(fn-dss-contract stc `(and (implies (and ,statep (fn-cbor-octetp ,elt))
                                           ,(fn-dss-type-pred state-type `(mv-nth 0 ,step) wrld))
                                  (implies ,statep
                                           ,(fn-dss-type-pred state-type `(mv-nth 0 ,final) wrld)))
                        'fn-dss-st-next-keeps-type
                        `((fn-dss-st-statep (lambda (s) ,statep)) ,@core) `((o ,elt)) constraint-hints)
      ; The step contract's facts as rules, for the guard proofs of the loop's
      ; arithmetic (the word's octet count and bytes).
      (defthm ,fk
        (implies (fn-cbor-octetp ,elt) (natp (mv-nth 1 ,step)))
        :rule-classes ((:rewrite) (:type-prescription))
        :hints (("Goal" :use (,usc))))
      (defthm ,fkb
        (implies (fn-cbor-octetp ,elt) (<= (mv-nth 1 ,step) ,emit-max))
        :rule-classes :linear
        :hints (("Goal" :use (,usc))))
      (defthm ,fw
        (implies (fn-cbor-octetp ,elt) (unsigned-byte-p 56 (mv-nth 2 ,step)))
        :hints (("Goal" :use (,usc))))
      (defthm ,ffk
        (natp (mv-nth 1 ,final))
        :rule-classes ((:rewrite) (:type-prescription))
        :hints (("Goal" :use (,usc))))
      (defthm ,ffkb
        (<= (mv-nth 1 ,final) ,final-max)
        :rule-classes :linear
        :hints (("Goal" :use (,usc))))
      (defthm ,ffw
        (unsigned-byte-p 56 (mv-nth 2 ,final))
        :hints (("Goal" :use (,usc))))
      ,(fn-dss-contract cc `(and (natp ,cost-max) (<= (nfix ,cost) ,cost-max)
                                 (natp ,final-cost-max) (<= (nfix ,final-cost) ,final-cost-max))
                        'fn-dss-st-cost-contract
                        `((fn-dss-st-cost (lambda (s ,elt) ,cost)) (fn-dss-st-cmax (lambda () ,cost-max))
                          (fn-dss-st-fcost (lambda (s) ,final-cost))
                          (fn-dss-st-fcmax (lambda () ,final-cost-max)))
                        `((o ,elt)) constraint-hints)
      (defun ,loopn (,@ctx s i end last idx room fn-octets fn-dss-out)
        (declare (xargs :stobjs (fn-octets fn-dss-out)
                        :guard ,(fn-dss-and guard `(and ,*fn-dss-span-guard*
                                                       (unsigned-byte-p 59 idx)
                                                       (unsigned-byte-p 59 room)
                                                       (unsigned-byte-p 59 (+ idx room))
                                                       (<= (+ idx room) (fn-dss-out-len fn-dss-out))))
                        :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))
                        :verify-guards nil)
                 (type ,state-type s)
                 (type (unsigned-byte 59) i end idx room))
        (if (and (mbt (and (natp i) (natp end))) (< i end))
            (if (< (nfix room) ,emit-max)
                (let ((fn-dss-out (fn-dss-out-truncate idx fn-dss-out)))
                  (mv :need-output s i fn-dss-out))
              (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt))
                (mv-let (dss-s2 dss-k dss-w dss-sig) ,step
                  (if (eql dss-sig 2)
                      (let ((fn-dss-out (fn-dss-out-truncate idx fn-dss-out)))
                        (mv :refused dss-s2 i fn-dss-out))
                    (let* ((dss-k (mbe :logic (nfix dss-k) :exec (the (integer 0 ,emit-max) dss-k)))
                           (fn-dss-out (fn-dss-put-word dss-w dss-k idx fn-dss-out))
                           (dss-idx (+ idx dss-k))
                           (dss-room (- (nfix room) dss-k)))
                      (if (eql dss-sig 1)
                          (let ((fn-dss-out (fn-dss-out-truncate dss-idx fn-dss-out)))
                            (mv :yield dss-s2 (+ 1 i) fn-dss-out))
                        (,loopn ,@ctx dss-s2 (+ 1 i) end last dss-idx dss-room
                                fn-octets fn-dss-out)))))))
          (if last
              (if (< (nfix room) ,final-max)
                  (let ((fn-dss-out (fn-dss-out-truncate idx fn-dss-out)))
                    (mv :need-output s i fn-dss-out))
                (mv-let (dss-s2 dss-k dss-w dss-sig) ,final
                  (if (eql dss-sig 2)
                      (let ((fn-dss-out (fn-dss-out-truncate idx fn-dss-out)))
                        (mv :refused dss-s2 i fn-dss-out))
                    (let* ((dss-k (mbe :logic (nfix dss-k) :exec (the (integer 0 ,final-max) dss-k)))
                           (fn-dss-out (fn-dss-put-word dss-w dss-k idx fn-dss-out))
                           (fn-dss-out (fn-dss-out-truncate (+ idx dss-k) fn-dss-out)))
                      (mv :done dss-s2 i fn-dss-out)))))
            (let ((fn-dss-out (fn-dss-out-truncate idx fn-dss-out)))
              (mv :need-input s i fn-dss-out)))))
      (defun ,name (,@ctx s i end last cap fn-octets fn-dss-out)
        (declare (xargs :stobjs (fn-octets fn-dss-out)
                        :guard ,(fn-dss-and guard `(and ,*fn-dss-span-guard* (natp cap)
                                                       (unsigned-byte-p 59 cap)
                                                       (unsigned-byte-p 59 (fn-dss-out-len fn-dss-out))))
                        :verify-guards nil)
                 (type ,state-type s)
                 (type (unsigned-byte 59) i end cap))
        (let* ((dss-len (fn-dss-out-len fn-dss-out))
               (dss-room (nfix (- cap dss-len))))
          (if (< dss-room ,floor)
              (mv :no-room s i fn-dss-out)
            (let ((fn-dss-out (fn-dss-out-append-word 0 dss-room fn-dss-out)))
              (,loopn ,@ctx s i end last dss-len dss-room fn-octets fn-dss-out)))))
      (defun ,lstl (,@ctx s xs last room)
        (declare (xargs :verify-guards nil :measure (len xs)
                        :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
        (if (consp xs)
            (if (< (nfix room) ,emit-max)
                (mv :need-output s nil 0)
              (let ((,elt (car xs))) (declare (ignorable ,elt))
                (mv-let (dss-s2 dss-k dss-w dss-sig) ,step
                  (if (eql dss-sig 2)
                      (mv :refused dss-s2 nil 0)
                    (if (eql dss-sig 1)
                        (mv :yield dss-s2 (fn-oct-word-octets dss-w dss-k) 1)
                      (mv-let (dss-r dss-s2 dss-outs dss-n)
                        (,lstl ,@ctx dss-s2 (cdr xs) last (- (nfix room) (nfix dss-k)))
                        (mv dss-r dss-s2 (append (fn-oct-word-octets dss-w dss-k) dss-outs)
                            (+ 1 dss-n))))))))
          (if last
              (if (< (nfix room) ,final-max)
                  (mv :need-output s nil 0)
                (mv-let (dss-s2 dss-k dss-w dss-sig) ,final
                  (if (eql dss-sig 2)
                      (mv :refused dss-s2 nil 0)
                    (mv :done dss-s2 (fn-oct-word-octets dss-w dss-k) 0))))
            (mv :need-input s nil 0))))
      (defun ,lst (,@ctx s xs last room)
        (declare (xargs :verify-guards nil))
        (if (< (nfix room) ,floor)
            (mv :no-room s nil 0)
          (,lstl ,@ctx s xs last room)))
      (defun ,items (,@ctx s xs last)
        (declare (xargs :verify-guards nil :measure (len xs)
                        :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
        (if (consp xs)
            (let ((,elt (car xs))) (declare (ignorable ,elt))
              (mv-let (dss-s2 dss-k dss-w dss-sig) ,step
                (if (eql dss-sig 2)
                    (mv :refused dss-s2 nil)
                  (mv-let (dss-r dss-s2 dss-items) (,items ,@ctx dss-s2 (cdr xs) last)
                    (mv dss-r dss-s2 (append (fn-oct-word-octets dss-w dss-k)
                                         (if (eql dss-sig 1) (cons :yield dss-items) dss-items)))))))
          (if last
              (mv-let (dss-s2 dss-k dss-w dss-sig) ,final
                (if (eql dss-sig 2)
                    (mv :refused dss-s2 nil)
                  (mv :done dss-s2 (fn-oct-word-octets dss-w dss-k))))
            (mv :need-input s nil))))
      (defthm ,cons
        (let ((dss-n (mv-nth 3 (,lst ,@ctx s xs last room))))
          (and (natp dss-n) (<= dss-n (len xs))))
        :rule-classes nil
        :hints (("Goal" :use (,usc (:functional-instance fn-dss-stream-list-consumed ,@core ,@lsubst))
                 :in-theory ,(fn-dss-defs-theory (list lst lstl)))))
      (defun ,drive (,@ctx s pieces last rooms)
        (declare (xargs :verify-guards nil
                        :measure (+ (fn-dss-sum-lens pieces) (len pieces))
                        :hints (("Goal" :use ((:instance ,cons
                                               (xs (if (consp pieces) (car pieces) nil))
                                               (last (and last (atom (cdr pieces))))
                                               (room (max ,floor
                                                          (nfix (if (consp rooms) (car rooms) 0))))))
                                 :in-theory (e/d (fn-dss-len-nthcdr) (,lst nthcdr))))))
        (let* ((xs (if (consp pieces) (car pieces) nil))
               (dss-lastp (and last (atom (cdr pieces))))
               (dss-room (max ,floor (nfix (if (consp rooms) (car rooms) 0)))))
          (mv-let (dss-r dss-s2 dss-outs dss-n) (,lst ,@ctx s xs dss-lastp dss-room)
            (cond ((or (eq dss-r :refused) (eq dss-r :done))
                   (mv dss-r dss-s2 dss-outs))
                  ((eq dss-r :need-input)
                   (if (consp (cdr pieces))
                       (mv-let (dss-r3 dss-s3 dss-items) (,drive ,@ctx dss-s2 (cdr pieces) last (cdr rooms))
                         (mv dss-r3 dss-s3 (append dss-outs dss-items)))
                     (mv dss-r dss-s2 dss-outs)))
                  ((zp dss-n) (mv dss-r dss-s2 dss-outs))
                  (t
                   (mv-let (dss-r3 dss-s3 dss-items)
                     (,drive ,@ctx dss-s2 (cons (nthcdr dss-n xs) (cdr pieces)) last (cdr rooms))
                     (mv dss-r3 dss-s3 (append dss-outs (if (eq dss-r :yield)
                                                    (cons :yield dss-items)
                                                  dss-items)))))))))
      (defun ,host (,@ctx s pieces i last rooms fuel fn-octets fn-dss-out)
        (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil
                        :measure (nfix fuel)))
        (if (zp fuel)
            (mv :fuel s nil fn-octets fn-dss-out)
          (let* ((fn-dss-out (fn-dss-out-clear fn-dss-out))
                 (dss-lastp (and last (atom (cdr pieces))))
                 (dss-cap (nfix (if (consp rooms) (car rooms) 0))))
            (mv-let (dss-r dss-s2 dss-i2 fn-dss-out)
              (,name ,@ctx s i (fn-octets-len fn-octets) dss-lastp dss-cap fn-octets fn-dss-out)
              (let ((dss-outs (fn-dss-out-list fn-dss-out)))
                (cond ((or (eq dss-r :refused) (eq dss-r :done) (eq dss-r :no-room))
                       (mv dss-r dss-s2 dss-outs fn-octets fn-dss-out))
                      ((eq dss-r :need-input)
                       (if (consp (cdr pieces))
                           (let ((fn-octets (fn-octets-from-list (cadr pieces) fn-octets)))
                             (mv-let (dss-r3 dss-s3 dss-items fn-octets fn-dss-out)
                               (,host ,@ctx dss-s2 (cdr pieces) 0 last (cdr rooms) (1- fuel)
                                      fn-octets fn-dss-out)
                               (mv dss-r3 dss-s3 (append dss-outs dss-items) fn-octets fn-dss-out)))
                         (mv dss-r dss-s2 dss-outs fn-octets fn-dss-out)))
                      (t
                       (mv-let (dss-r3 dss-s3 dss-items fn-octets fn-dss-out)
                         (,host ,@ctx dss-s2 pieces dss-i2 last (cdr rooms) (1- fuel) fn-octets fn-dss-out)
                         (mv dss-r3 dss-s3 (append dss-outs (if (eq dss-r :yield)
                                                        (cons :yield dss-items)
                                                      dss-items))
                             fn-octets fn-dss-out)))))))))
      (defun ,run (,@ctx s pieces last rooms fuel fn-octets fn-dss-out)
        (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
        (let ((fn-octets (fn-octets-from-list (if (consp pieces) (car pieces) nil) fn-octets)))
          (,host ,@ctx s pieces 0 last rooms fuel fn-octets fn-dss-out)))
      (defun ,work (,@ctx s i end last room fn-octets)
        (declare (xargs :stobjs fn-octets :verify-guards nil
                        :measure (nfix (- (nfix end) (nfix i)))
                        :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
        (if (and (mbt (and (natp i) (natp end))) (< i end))
            (if (< (nfix room) ,emit-max)
                1
              (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt))
                (mv-let (dss-s2 dss-k dss-w dss-sig) ,step
                  (declare (ignore dss-w))
                  (+ 1 (nfix ,cost)
                     (if (or (eql dss-sig 2) (eql dss-sig 1))
                         0
                       (,work ,@ctx dss-s2 (+ 1 i) end last (- (nfix room) (nfix dss-k))
                              fn-octets))))))
          (+ 1 (if last (nfix ,final-cost) 0))))
      (defthm ,bridge
        (implies (and (natp i) (natp cap) (true-listp fn-dss-out))
                 (equal (,name ,@ctx s i end last cap fn-octets fn-dss-out)
                        (mv-let (dss-r dss-s2 dss-outs dss-n)
                          (,lst ,@ctx s (fn-oct-slice-list i end fn-octets) last
                                (nfix (- cap (len fn-dss-out))))
                          (mv dss-r dss-s2 (+ i dss-n) (append fn-dss-out dss-outs)))))
        :hints (("Goal" :use (,usc (:functional-instance fn-dss-stream-is-list ,@ssubst))
                 :in-theory ,(fn-dss-defs-theory (list name loopn lst lstl)))
))
      (defthm ,part
        (equal (,drive ,@ctx s pieces last rooms)
               (,items ,@ctx s (fn-dss-flatten pieces) last))
        :hints (("Goal" :use (,usc (:functional-instance fn-dss-drive-is-items ,@isubst))
                 :in-theory ,(fn-dss-defs-theory (list drive items lst lstl)))
))
      (defthm ,spart
        (implies (and (true-list-listp pieces)
                      (<= (fn-dss-calls-bound pieces) (nfix fuel))
                      (fn-dss-a-host-room ,floor rooms fuel))
                 (let ((dss-run (,run ,@ctx s pieces last rooms fuel fn-octets fn-dss-out)))
                   (equal (list (mv-nth 0 dss-run) (mv-nth 1 dss-run) (mv-nth 2 dss-run))
                          (,items ,@ctx s (fn-dss-flatten pieces) last))))
        :hints (("Goal" :use (,usc (:functional-instance fn-dss-drive-stobj-is-items ,@hsubst))
                 :in-theory ,(fn-dss-defs-theory
                              (list name loopn lst lstl items host run
                                    'fn-dss-octets-from-list-is-list
                                    'fn-dss-out-clear-is-nil 'fn-dss-out-list-is-identity)))))
      (defthm ,writes
        (implies (and (natp i) (natp cap) (true-listp fn-dss-out)
                      (<= (len fn-dss-out) cap)
                      (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
                 (mv-let (dss-r dss-s2 dss-i2 dss-out2) (,name ,@ctx s i end last cap fn-octets fn-dss-out)
                   (declare (ignore dss-r dss-s2))
                   (and (<= (len dss-out2) cap)
                        (<= (len dss-out2) (+ (len fn-dss-out) (* ,emit-max (- dss-i2 i)) ,final-max))
                        (<= i dss-i2)
                        (or (<= dss-i2 end) (equal dss-i2 i)))))
        :hints (("Goal" :use (,usc (:functional-instance fn-dss-stream-writes ,@ssubst))
                 :in-theory ,(fn-dss-defs-theory (list name loopn lst lstl)))
))
      (defun ,wc (,@ctx s i end last cap fn-octets fn-dss-out)
        (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
        (let ((dss-room (nfix (- (nfix cap) (fn-dss-out-len fn-dss-out)))))
          (if (< dss-room ,floor)
              0
            (mv-let (dss-r dss-s2 dss-outs dss-n)
              (,lstl ,@ctx s (fn-oct-slice-list i end fn-octets) last dss-room)
              (declare (ignore dss-r dss-s2 dss-n))
              (+ dss-room (len dss-outs))))))
      (defthm ,wcb
        (implies (and (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
                 (<= (,wc ,@ctx s i end last cap fn-octets fn-dss-out)
                     (+ (nfix (- (nfix cap) (len fn-dss-out)))
                        (* ,emit-max (nfix (- (nfix end) (nfix i))))
                        ,final-max)))
        :rule-classes :linear
        :hints (("Goal" :use (,usc (:functional-instance fn-dss-stream-write-charge-bound ,@wcsubst))
                 :in-theory ,(fn-dss-defs-theory (list wc lst lstl)))))
      (defthm ,ty
        (implies (and ,statep (natp i)
                      (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
                 ,(fn-dss-type-pred state-type
                                    `(mv-nth 1 (,name ,@ctx s i end last cap fn-octets fn-dss-out))
                                    wrld))
        :hints (("Goal" :use (,usc ,(fn-dss-use-contract stc elt)
                              (:functional-instance fn-dss-stream-state-type
                                (fn-dss-st-statep (lambda (s) ,statep)) ,@ssubst))
                 :in-theory ,(fn-dss-defs-theory (list name loopn lst lstl)))
))
      (defthm ,prog
        (implies (and (natp i) (natp end) (< i end) (natp cap)
                      (<= (+ (len fn-dss-out) ,floor) cap))
                 (mv-let (dss-r dss-s2 dss-i2 dss-out2) (,name ,@ctx s i end last cap fn-octets fn-dss-out)
                   (declare (ignore dss-s2 dss-out2))
                   (or (equal dss-r :refused) (< i dss-i2))))
        :hints (("Goal" :use (,usc (:functional-instance fn-dss-stream-progress ,@ssubst))
                 :in-theory ,(fn-dss-defs-theory (list name loopn lst lstl)))
))
      (defthm ,wb
        (<= (,work ,@ctx s i end last room fn-octets)
            (+ 1 ,final-cost-max (* (+ 1 ,cost-max) (nfix (- (nfix end) (nfix i))))))
        :rule-classes :linear
        :hints (("Goal" :use (,usc ,(fn-dss-use-contract cc elt)
                              (:functional-instance fn-dss-stream-work-bound ,@wsubst))
                 :expand ((,work ,@ctx s i end last room fn-octets))
                 :in-theory ,(fn-dss-defs-theory (list work)))
))
      (verify-guards ,loopn
        :hints ,(or guard-hints
                    `(("Goal" :in-theory (enable ,@(fn-dss-guard-theory))))))
      (verify-guards ,name
        :hints ,(or guard-hints
                    `(("Goal" :in-theory (enable ,@(fn-dss-guard-theory))))))
      (table fn-generated ',name
             '(:def-span-scan :shape :stream :loop ,loopn :list ,lst :items ,items :drive ,drive
                              :host ,host :partition-stobj ,spart :assumes (:a-host-room)
                              :work ,work :bridge ,bridge :partition ,part
                              :c0 (+ 1 ,final-cost-max) :c1 (+ 1 ,cost-max)
                              :writes (+ (* ,emit-max (- dss-i2 i)) ,final-max)
                              :write-charge ,wc
                              :workspace (i s :type ,state-type))))))

; ---- the macro

; One instance's events for SHAPE; EXEC names the work model, its bound and
; its cost contract NAME-EXEC-..., for the real-cost copy.
(defun fn-dss-shape-events (name ctx shape elt body norm map against constant within
                                 acc acc-type state-type step final emit-max final-max
                                 cost cost-max final-cost final-cost-max
                                 guard guard-hints constraint-hints wrld exec)
  (declare (xargs :mode :program))
  (case shape
    (:find (fn-dss-find-events name ctx elt body cost cost-max
                               guard guard-hints constraint-hints exec))
    (:fold (fn-dss-fold-events name ctx elt acc acc-type body cost
                               cost-max guard guard-hints constraint-hints wrld exec))
    (:equal (fn-dss-equal-events name ctx elt (or norm elt) cost
                                 cost-max against constant guard guard-hints constraint-hints exec))
    (:copy (fn-dss-copy-events name ctx elt (or map elt) cost
                               cost-max within guard guard-hints constraint-hints exec))
    (otherwise
     (fn-dss-stream-events name ctx elt state-type step final emit-max final-max
                           cost cost-max final-cost final-cost-max
                           guard guard-hints constraint-hints wrld exec))))

(defun fn-dss-keep-named (names evs)
  (declare (xargs :mode :program))
  (cond ((atom evs) nil)
        ((and (consp (car evs)) (member-eq (cadr (car evs)) names))
         (cons (car evs) (fn-dss-keep-named names (cdr evs))))
        (t (fn-dss-keep-named names (cdr evs)))))

; The workspace types: one non-negative fixnum word.
(defun fn-dss-word-typep (ty)
  (declare (xargs :mode :program))
  (and (true-listp ty) (equal (len ty) 2) (eq (car ty) 'unsigned-byte)
       (posp (cadr ty)) (<= (cadr ty) 59)))

(defun fn-dss-word-type-okp (ty)
  (declare (xargs :mode :program))
  (or (fn-dss-word-typep ty)
      (and (true-listp ty) (equal (len ty) 3) (eq (car ty) 'integer)
           (eql (cadr ty) 0) (natp (caddr ty)) (< (caddr ty) (expt 2 59)))))

(defun fn-dss-fn (name ctx shape elt body norm map against constant within acc acc-type
                       state-type step final emit-max final-max cost cost-max
                       final-cost final-cost-max guard guard-hints constraint-hints state)
  (declare (xargs :mode :program :stobjs state))
  (let* ((ctx-name (fn-dss-name (list "DEF-SPAN-SCAN " name) name))
         (wrld (w state))
         (own (append ctx (list elt) (and (eq shape :fold) (list acc))))
         (clash (append (intersection-eq own *fn-dss-reserved*)
                        (fn-dss-prefixed own)
                        (and (not (no-duplicatesp-eq own)) own))))
    (cond
     ((not (member-eq shape '(:find :fold :equal :copy :stream)))
      (er soft ctx-name "~x0: unknown shape ~x1 (one of :find :fold :equal :copy :stream)." name shape))
     ((not (symbol-listp ctx))
      (er soft ctx-name "~x0: the context formals must be a list of symbols." name))
     (clash
      (er soft ctx-name "~x0: ~&1 name a variable of the library theorems; rename." name clash))
     ((and (member-eq shape '(:find :fold)) (null body))
      (er soft ctx-name "~x0: ~x1 needs :body." name shape))
     ((and (member-eq shape '(:find :fold :stream)) (null cost-max))
      (er soft ctx-name "~x0: ~x1 needs :cost-max, the body cost contract." name shape))
     ((and (eq shape :fold) (not (fn-dss-word-type-okp acc-type)))
      (er soft ctx-name "~x0: :acc-type must be (unsigned-byte N), N from 1 to 59, or (integer 0 H), H below 2^59: one fixnum word." name))
     ((and (eq shape :stream) (not (fn-dss-word-type-okp state-type)))
      (er soft ctx-name "~x0: :state-type must be (unsigned-byte N), N from 1 to 59, or (integer 0 H), H below 2^59: one fixnum word." name))
     ((and (eq shape :equal) (not (member-eq against '(:constant :span))))
      (er soft ctx-name "~x0: :equal needs :against :constant (with :constant C) or :span." name))
     ((and (eq shape :equal) (eq against :constant) (not (true-listp constant)))
      (er soft ctx-name "~x0: :constant must be a true list." name))
     ((and (eq shape :stream)
           (not (and state-type step final (natp emit-max) (<= emit-max 7)
                     (natp final-max) (<= final-max 7))))
      (er soft ctx-name "~x0: :stream needs :state-type, :step, :final, :emit-max and :final-max (both at most 7)." name))
     ((and norm (not (eq shape :equal)))
      (er soft ctx-name "~x0: :norm is an :equal option." name))
     ((and map (not (eq shape :copy)))
      (er soft ctx-name "~x0: :map is a :copy option." name))
     (t
      (let ((cost-max (or cost-max 0)))
        (value
         `(encapsulate
            ()
            ; Scoped to this encapsulate (the acl2-defaults-table is restored
            ; at its end): an instance's work or list model may ignore a
            ; formal its body does not use.
            (set-irrelevant-formals-ok t)
            (set-ignore-ok t)
            (table fn-dss-assumptions ',name
                   ',(append (and (or (member-eq shape '(:find :fold :stream)) norm map)
                                  '(:a-body-cost))
                             (and (member-eq shape '(:copy :stream)) '(:a-reserved))
                             (and (eq shape :stream) '(:a-host-room))))
            ,@(fn-dss-shape-events name ctx shape elt body norm map against constant within
                                   acc acc-type state-type step final emit-max final-max
                                   (or cost cost-max) cost-max
                                   (or final-cost (or final-cost-max 0)) (or final-cost-max 0)
                                   guard guard-hints constraint-hints wrld nil)
            ; A-BODY-COST (books/assumptions-spans.lisp): the same work bound over
            ; the real-cost model, for every instance with a body.
            ,@(and (or (member-eq shape '(:find :fold :stream)) norm map)
                   (fn-dss-keep-named
                    (list (fn-dss-name (list name "-EXEC-COST-CONTRACT") name)
                          (fn-dss-name (list name "-EXEC-WORK") name)
                          (fn-dss-name (list name "-EXEC-WORK-BOUND") name))
                    (fn-dss-shape-events
                     name ctx shape elt body norm map against constant within
                     acc acc-type state-type step final emit-max final-max
                     `(fn-assume-span-exec-cost
                       ',name :body
                       (list ,@(and (eq shape :fold) (list acc))
                             ,@(and (eq shape :stream) (list 's))
                             ,elt ,@ctx))
                     `(fn-assume-span-cost-bound ',name :body)
                     `(fn-assume-span-exec-cost ',name :final (list s ,@ctx))
                     `(fn-assume-span-cost-bound ',name :final)
                     guard guard-hints constraint-hints wrld t))))))))))

(defmacro def-span-scan (name ctx &key shape (elt 'o) body norm map against constant within
                              (acc 'acc) acc-type state-type step final emit-max final-max
                              cost cost-max final-cost final-cost-max (guard 't) guard-hints
                              constraint-hints)
  `(make-event
    (fn-dss-fn ',name ',ctx ',shape ',elt ',body ',norm ',map ',against ',constant ',within
               ',acc ',acc-type ',state-type ',step ',final ',emit-max ',final-max
               ',cost ',cost-max ',final-cost ',final-cost-max ',guard ',guard-hints
               ',constraint-hints state)))
