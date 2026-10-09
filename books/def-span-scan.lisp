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
;                 octets or none; :stream writes at most EMIT-MAX per consumed
;                 octet plus FINAL-MAX, and never past CAP (NAME-WRITES);
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
;                 (the constant :cost-max when omitted).  That the compiled body
;                 (BODY, NORM, MAP or STEP) does at most that much work and
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

(in-theory (disable fn-dss-out-append-octet fn-dss-out-reserve fn-dss-b-get))

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
        (let ((k (fn-dss-find-list (cdr xs))))
          (if k (+ 1 k) nil)))
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
         (let ((k (fn-dss-find-list (fn-oct-slice-list i end fn-octets))))
           (if k (+ i k) nil))))

(defthm fn-dss-find-hit
  (let ((r (fn-dss-find i end fn-octets)))
    (implies r
             (and (natp r) (<= i r) (< r end)
                  (fn-dss-find-p (nth r fn-octets))))))

(defthm fn-dss-find-least
  (let ((r (fn-dss-find i end fn-octets)))
    (implies (and (natp i) (natp end) (natp j) (<= i j) (< j end)
                  (or (null r) (< j r)))
             (not (fn-dss-find-p (nth j fn-octets))))))

(defthm fn-dss-find-work-bound
  (<= (fn-dss-find-work i end fn-octets)
      (+ 1 (* (+ 1 (fn-dss-find-cmax)) (nfix (- (nfix end) (nfix i))))))
  :rule-classes :linear)

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
         (fn-dss-fold-list acc (fn-oct-slice-list i end fn-octets))))

(defthm fn-dss-fold-acc-type
  (implies (and (fn-dss-fold-accp acc)
                (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
           (fn-dss-fold-accp (fn-dss-fold acc i end fn-octets))))

(defthm fn-dss-fold-work-bound
  (<= (fn-dss-fold-work acc i end fn-octets)
      (+ 1 (* (+ 1 (fn-dss-fold-cmax)) (nfix (- (nfix end) (nfix i))))))
  :rule-classes :linear)

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
         (equal (fn-dss-eq-list (fn-oct-slice-list i end fn-octets)) xs)))

(defthm fn-dss-eqs-is-list
  (implies (and (natp i) (natp j))
           (equal (fn-dss-eqs i end fn-octets j fn-dss-b)
                  (equal (fn-dss-eq-list (fn-oct-slice-list i end fn-octets))
                         (fn-dss-eq-list
                          (fn-oct-slice-list j (+ j (nfix (- (nfix end) (nfix i)))) fn-dss-b))))))

(defthm fn-dss-eqc-work-bound
  (<= (fn-dss-eqc-work i end fn-octets xs)
      (+ 1 (* (+ 1 (fn-dss-eq-cmax)) (nfix (- (nfix end) (nfix i))))))
  :rule-classes :linear)

(defthm fn-dss-eqs-work-bound
  (<= (fn-dss-eqs-work i end fn-octets j fn-dss-b)
      (+ 1 (* (+ 1 (* 2 (fn-dss-eq-cmax))) (nfix (- (nfix end) (nfix i))))))
  :rule-classes :linear)

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

; Onto a distinct instance.
(defun fn-dss-copy-loop (i end fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (let ((fn-dss-out (fn-dss-out-append-octet
                         (fn-dss-copy-f (fn-octets-get i fn-octets)) fn-dss-out)))
        (fn-dss-copy-loop (+ 1 i) end fn-octets fn-dss-out))
    fn-dss-out))

(defun fn-dss-copy (i end cap fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
  (let ((n (+ (fn-dss-out-len fn-dss-out) (nfix (- (nfix end) (nfix i))))))
    (if (<= n (nfix cap))
        (let* ((fn-dss-out (fn-dss-out-reserve n fn-dss-out))
               (fn-dss-out (fn-dss-copy-loop i end fn-octets fn-dss-out)))
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
  (let ((n (+ (fn-octets-len fn-octets) (nfix (- (nfix end) (nfix i))))))
    (if (<= n (nfix cap))
        (let* ((fn-octets (fn-octets-reserve n fn-octets))
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

(defthm fn-dss-copy-is-list
  (implies (true-listp fn-dss-out)
           (equal (fn-dss-copy i end cap fn-octets fn-dss-out)
                  (if (<= (+ (len fn-dss-out) (nfix (- (nfix end) (nfix i)))) (nfix cap))
                      (mv :done (append fn-dss-out
                                        (fn-dss-copy-list (fn-oct-slice-list i end fn-octets))))
                    (mv :refused fn-dss-out)))))

(defthm fn-dss-copyw-is-list
  (implies (and (true-listp fn-octets) (<= end (len fn-octets)))
           (equal (fn-dss-copyw i end cap fn-octets)
                  (if (<= (+ (len fn-octets) (nfix (- (nfix end) (nfix i)))) (nfix cap))
                      (mv :done (append fn-octets
                                        (fn-dss-copy-list (fn-oct-slice-list i end fn-octets))))
                    (mv :refused fn-octets)))))

(defthm fn-dss-copy-work-bound
  (<= (fn-dss-copy-work i end fn-octets)
      (+ 1 (* (+ 1 (fn-dss-copy-cmax)) (nfix (- (nfix end) (nfix i))))))
  :rule-classes :linear)

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

; The stobj loop.
(defun fn-dss-stream-loop (s i end last cap fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (if (< (nfix (- cap (fn-dss-out-len fn-dss-out))) (fn-dss-st-emax))
          (mv :need-output s i fn-dss-out)
        (let* ((o (fn-octets-get i fn-octets))
               (sig (fn-dss-st-sig s o)))
          (if (eql sig 2)
              (mv :refused (fn-dss-st-next s o) i fn-dss-out)
            (let ((fn-dss-out (fn-dss-out-append-word (fn-dss-st-w s o) (fn-dss-st-k s o)
                                                      fn-dss-out)))
              (if (eql sig 1)
                  (mv :yield (fn-dss-st-next s o) (+ 1 i) fn-dss-out)
                (fn-dss-stream-loop (fn-dss-st-next s o) (+ 1 i) end last cap
                               fn-octets fn-dss-out))))))
    (if last
        (if (< (nfix (- cap (fn-dss-out-len fn-dss-out))) (fn-dss-st-fmax))
            (mv :need-output s i fn-dss-out)
          (if (eql (fn-dss-st-fsig s) 2)
              (mv :refused (fn-dss-st-fnext s) i fn-dss-out)
            (let ((fn-dss-out (fn-dss-out-append-word (fn-dss-st-fw s) (fn-dss-st-fk s)
                                                      fn-dss-out)))
              (mv :done (fn-dss-st-fnext s) i fn-dss-out))))
      (mv :need-input s i fn-dss-out))))

; One call: the room check at entry, then the loop.
(defun fn-dss-stream (s i end last cap fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
  (if (< (nfix (- cap (fn-dss-out-len fn-dss-out))) (fn-dss-floor))
      (mv :no-room s i fn-dss-out)
    (fn-dss-stream-loop s i end last cap fn-octets fn-dss-out)))

; The list model of one call: XS the octets from I to END, ROOM the output
; room (- CAP (len out)).  Answers (mv SIGNAL S' OUTS N): the octets written
; and the number consumed.
(defun fn-dss-stream-list-loop (s xs last room)
  (declare (xargs :measure (len xs) :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (consp xs)
      (if (< (nfix room) (fn-dss-st-emax))
          (mv :need-output s nil 0)
        (let* ((o (car xs))
               (sig (fn-dss-st-sig s o)))
          (if (eql sig 2)
              (mv :refused (fn-dss-st-next s o) nil 0)
            (let ((ws (fn-oct-word-octets (fn-dss-st-w s o) (fn-dss-st-k s o))))
              (if (eql sig 1)
                  (mv :yield (fn-dss-st-next s o) ws 1)
                (mv-let (r s2 outs n)
                  (fn-dss-stream-list-loop (fn-dss-st-next s o) (cdr xs) last
                                      (- (nfix room) (nfix (fn-dss-st-k s o))))
                  (mv r s2 (append ws outs) (+ 1 n))))))))
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
      (let* ((o (car xs))
             (sig (fn-dss-st-sig s o)))
        (if (eql sig 2)
            (mv :refused (fn-dss-st-next s o) nil)
          (mv-let (r s2 items)
            (fn-dss-stream-items (fn-dss-st-next s o) (cdr xs) last)
            (mv r s2 (append (fn-oct-word-octets (fn-dss-st-w s o) (fn-dss-st-k s o))
                             (if (eql sig 1) (cons :yield items) items))))))
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
; rests on it, here and in every instance (by `:functional-instance').
(defthm fn-dss-stream-list-loop-consumed
  (let ((n (mv-nth 3 (fn-dss-stream-list-loop s xs last room))))
    (and (natp n) (<= n (len xs))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-dss-stream-list-loop s xs last room))))

(defthm fn-dss-stream-list-consumed
  (let ((n (mv-nth 3 (fn-dss-stream-list s xs last room))))
    (and (natp n) (<= n (len xs))))
  :rule-classes nil
  :hints (("Goal" :use fn-dss-stream-list-loop-consumed)))

(defthm fn-dss-len-nthcdr
  (implies (and (natp n) (<= n (len xs)))
           (equal (len (nthcdr n xs)) (- (len xs) n))))

; How a host drives the loop over a split input: PIECES the successive
; arrivals, ROOMS the output room offered at each call (raised to the floor),
; LAST given with the final piece only.  Every call consumes an octet or ends
; a piece or the run, which is the measure's argument.
(defun fn-dss-drive (s pieces last rooms)
  (declare (xargs :measure (+ (fn-dss-sum-lens pieces) (len pieces))
                  :hints (("Goal" :use ((:instance fn-dss-stream-list-consumed
                                         (xs (if (consp pieces) (car pieces) nil))
                                         (last (and last (atom (cdr pieces))))
                                         (room (max (fn-dss-floor)
                                                    (nfix (if (consp rooms) (car rooms) 0))))))
                           :in-theory (e/d (fn-dss-len-nthcdr) (fn-dss-stream-list nthcdr))))))
  (let* ((xs (if (consp pieces) (car pieces) nil))
         (lastp (and last (atom (cdr pieces))))
         (room (max (fn-dss-floor) (nfix (if (consp rooms) (car rooms) 0)))))
    (mv-let (r s2 outs n) (fn-dss-stream-list s xs lastp room)
      (cond ((or (eq r :refused) (eq r :done))
             (mv r s2 outs))
            ((eq r :need-input)
             (if (consp (cdr pieces))
                 (mv-let (r3 s3 items) (fn-dss-drive s2 (cdr pieces) last (cdr rooms))
                   (mv r3 s3 (append outs items)))
               (mv r s2 outs)))
            ((zp n) (mv r s2 outs))
            (t
             (mv-let (r3 s3 items)
               (fn-dss-drive s2 (cons (nthcdr n xs) (cdr pieces)) last (cdr rooms))
               (mv r3 s3 (append outs (if (eq r :yield) (cons :yield items) items)))))))))

; The work of one call, ROOM the output room at the call: each examined
; octet 1 plus the step's cost, the exit 1 plus the final's cost when LAST.
(defun fn-dss-stream-work (s i end last room fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (if (and (mbt (and (natp i) (natp end))) (< i end))
      (if (< (nfix room) (fn-dss-st-emax))
          1
        (let* ((o (fn-octets-get i fn-octets))
               (sig (fn-dss-st-sig s o)))
          (+ 1 (nfix (fn-dss-st-cost s o))
             (if (or (eql sig 2) (eql sig 1))
                 0
               (fn-dss-stream-work (fn-dss-st-next s o) (+ 1 i) end last
                                   (- (nfix room) (nfix (fn-dss-st-k s o))) fn-octets)))))
    (+ 1 (if last (nfix (fn-dss-st-fcost s)) 0))))

(defthm fn-dss-stream-is-list
  (implies (and (natp i) (true-listp fn-dss-out))
           (equal (fn-dss-stream s i end last cap fn-octets fn-dss-out)
                  (mv-let (r s2 outs n)
                    (fn-dss-stream-list s (fn-oct-slice-list i end fn-octets) last
                                        (nfix (- cap (len fn-dss-out))))
                    (mv r s2 (+ i n) (append fn-dss-out outs))))))

(defthm fn-dss-drive-is-items
  (equal (fn-dss-drive s pieces last rooms)
         (fn-dss-stream-items s (fn-dss-flatten pieces) last)))

; A-HOST-ROOM, the host's contract: each of the first FUEL calls is offered
; at least FLOOR octets of output room (the host sends and clears the output
; before the next call).  A call offered less is refused by name (:no-room)
; and consumes nothing, so the theorem below is not made true by a host that
; never makes room: it is a hypothesis, stated, and a host that breaks it sees
; :no-room.
(defun fn-dss-a-host-room (floor rooms fuel)
  (if (zp fuel)
      t
    (and (consp rooms)
         (<= (nfix floor) (nfix (car rooms)))
         (fn-dss-a-host-room floor (cdr rooms) (1- fuel)))))

; The calls a run needs: one per consumed octet, one per piece, one to end.
(defun fn-dss-calls-bound (pieces)
  (+ 1 (len pieces) (fn-dss-sum-lens pieces)))

; The host loop over the stobj calls: the current piece is the input buffer's
; whole content, I the cursor in it; each call is offered the next room of
; ROOMS on a cleared output, whose octets the host then takes as sent; after
; :yield or :need-output the host calls again at the returned cursor, after
; :need-input it loads the next piece at cursor 0, and LAST is given with the
; final piece only.  FUEL bounds the calls; the run ends :fuel when it is out.
(defun fn-dss-host (s pieces i last rooms fuel fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil
                  :measure (nfix fuel)))
  (if (zp fuel)
      (mv :fuel s nil fn-octets fn-dss-out)
    (let* ((fn-dss-out (fn-dss-out-clear fn-dss-out))
           (lastp (and last (atom (cdr pieces))))
           (cap (nfix (if (consp rooms) (car rooms) 0))))
      (mv-let (r s2 i2 fn-dss-out)
        (fn-dss-stream s i (fn-octets-len fn-octets) lastp cap fn-octets fn-dss-out)
        (let ((outs (fn-dss-out-list fn-dss-out)))
          (cond ((or (eq r :refused) (eq r :done) (eq r :no-room))
                 (mv r s2 outs fn-octets fn-dss-out))
                ((eq r :need-input)
                 (if (consp (cdr pieces))
                     (let ((fn-octets (fn-octets-from-list (cadr pieces) fn-octets)))
                       (mv-let (r3 s3 items fn-octets fn-dss-out)
                         (fn-dss-host s2 (cdr pieces) 0 last (cdr rooms) (1- fuel)
                                      fn-octets fn-dss-out)
                         (mv r3 s3 (append outs items) fn-octets fn-dss-out)))
                   (mv r s2 outs fn-octets fn-dss-out)))
                (t
                 (mv-let (r3 s3 items fn-octets fn-dss-out)
                   (fn-dss-host s2 pieces i2 last (cdr rooms) (1- fuel) fn-octets fn-dss-out)
                   (mv r3 s3 (append outs (if (eq r :yield) (cons :yield items) items))
                       fn-octets fn-dss-out)))))))))

(defun fn-dss-host-run (s pieces last rooms fuel fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
  (let ((fn-octets (fn-octets-from-list (if (consp pieces) (car pieces) nil) fn-octets)))
    (fn-dss-host s pieces 0 last rooms fuel fn-octets fn-dss-out)))

; The partition property of the stobj loop: under A-HOST-ROOM and enough
; fuel, every split of the input and every room schedule yields the one-pass
; logical stream and final state.
(defthm fn-dss-drive-stobj-is-items
  (implies (and (true-list-listp pieces)
                (<= (fn-dss-calls-bound pieces) (nfix fuel))
                (fn-dss-a-host-room (fn-dss-floor) rooms fuel))
           (let ((run (fn-dss-host-run s pieces last rooms fuel fn-octets fn-dss-out)))
             (equal (list (mv-nth 0 run) (mv-nth 1 run) (mv-nth 2 run))
                    (fn-dss-stream-items s (fn-dss-flatten pieces) last)))))

(defthm fn-dss-stream-writes
  (implies (and (natp i) (natp cap) (true-listp fn-dss-out)
                (<= (len fn-dss-out) cap)
                (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
           (mv-let (r s2 i2 out2) (fn-dss-stream s i end last cap fn-octets fn-dss-out)
             (declare (ignore r s2))
             (and (<= (len out2) cap)
                  (<= (len out2)
                      (+ (len fn-dss-out) (* (fn-dss-st-emax) (- i2 i)) (fn-dss-st-fmax)))
                  (<= i i2)
                  (or (<= i2 end) (equal i2 i))))))

(defthm fn-dss-stream-state-type
  (implies (and (fn-dss-st-statep s) (natp i)
                (fn-cbor-octet-listp fn-octets) (<= end (len fn-octets)))
           (fn-dss-st-statep (mv-nth 1 (fn-dss-stream s i end last cap fn-octets fn-dss-out)))))

(defthm fn-dss-stream-progress
  (implies (and (natp i) (natp end) (< i end) (natp cap)
                (<= (+ (len fn-dss-out) (fn-dss-floor)) cap))
           (mv-let (r s2 i2 out2) (fn-dss-stream s i end last cap fn-octets fn-dss-out)
             (declare (ignore s2 out2))
             (or (equal r :refused) (< i i2)))))

(defthm fn-dss-stream-work-bound
  (<= (fn-dss-stream-work s i end last room fn-octets)
      (+ 1 (fn-dss-st-fcmax)
         (* (+ 1 (fn-dss-st-cmax)) (nfix (- (nfix end) (nfix i))))))
  :rule-classes :linear)

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
    (:rewrite fn-oct-nth-of-octet-listp-is-octet . 2)))

(defun fn-dss-defs-theory (names)
  ; The instance's definitions, unfolded once, in `minimal-theory' plus what
  ; a numeral-for-constrained-constant substitution needs: nfix is a natural
  ; (its type, not its definition, which would split cases before the unfold).
  (declare (xargs :mode :program))
  `(union-theories '(,@names (:type-prescription nfix))
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

(defun fn-dss-find-events (name ctx elt body cost cost-max guard guard-hints ch)
  (declare (xargs :mode :program))
  (let* ((cc (fn-dss-name (list name "-COST-CONTRACT") name))
         (lst (fn-dss-name (list name "-LIST") name))
         (work (fn-dss-name (list name "-WORK") name))
         (bridge (fn-dss-name (list name "-IS-LIST") name))
         (hit (fn-dss-name (list name "-HIT") name))
         (least (fn-dss-name (list name "-LEAST") name))
         (wb (fn-dss-name (list name "-WORK-BOUND") name))
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
                 :in-theory ,(fn-dss-defs-theory (list work)))))
      (verify-guards ,name
        :hints ,(or guard-hints
                    `(("Goal" :in-theory (enable ,@(fn-dss-guard-theory))))))
      (table fn-generated ',name
             '(:def-span-scan :shape :find :list ,lst :work ,work :bridge ,bridge
                              :c0 1 :c1 (+ 1 ,cost-max) :writes 0 :workspace (i))))))

; ---- :fold

(defun fn-dss-fold-events (name ctx elt acc acc-type body cost cost-max guard guard-hints ch wrld)
  (declare (xargs :mode :program))
  (let* ((cc (fn-dss-name (list name "-COST-CONTRACT") name))
         (tc (fn-dss-name (list name "-BODY-TYPE") name))
         (lst (fn-dss-name (list name "-LIST") name))
         (work (fn-dss-name (list name "-WORK") name))
         (bridge (fn-dss-name (list name "-IS-LIST") name))
         (ty (fn-dss-name (list name "-ACC-TYPE") name))
         (wb (fn-dss-name (list name "-WORK-BOUND") name))
         (accp (fn-dss-type-pred acc-type acc wrld))
         (subst `((fn-dss-fold-f (lambda (,acc ,elt) ,body))
                  (fn-dss-fold (lambda (,acc i end fn-octets) (,name ,@ctx ,acc i end fn-octets)))
                  (fn-dss-fold-list (lambda (,acc xs) (,lst ,@ctx ,acc xs)))))
         (tsubst `((fn-dss-fold-accp (lambda (,acc) ,accp)) ,@subst))
         (wsubst `((fn-dss-fold-f (lambda (,acc ,elt) ,body))
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
                 :in-theory ,(fn-dss-defs-theory (list work)))))
      (verify-guards ,name
        :hints ,(or guard-hints
                    `(("Goal" :in-theory (enable ,@(fn-dss-guard-theory))))))
      (table fn-generated ',name
             '(:def-span-scan :shape :fold :list ,lst :work ,work :bridge ,bridge
                              :c0 1 :c1 (+ 1 ,cost-max) :writes 0
                              :workspace (i ,acc :type ,acc-type))))))

; ---- :equal

(defun fn-dss-equal-events (name ctx elt norm cost cost-max against constant guard guard-hints ch)
  (declare (xargs :mode :program))
  (let* ((cc (fn-dss-name (list name "-COST-CONTRACT") name))
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
         (work (fn-dss-name (list name "-WORK") name))
         (bridge (fn-dss-name (list name "-IS-LIST") name))
         (wb (fn-dss-name (list name "-WORK-BOUND") name))
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

(defun fn-dss-copy-events (name ctx elt map cost cost-max within guard guard-hints ch)
  (declare (xargs :mode :program))
  (let* ((cc (fn-dss-name (list name "-COST-CONTRACT") name))
         (mc (fn-dss-name (list name "-MAP-OCTET") name))
         (loop (fn-dss-name (list name "-LOOP") name))
         (lst (fn-dss-name (list name "-LIST") name))
         (work (fn-dss-name (list name "-WORK") name))
         (bridge (fn-dss-name (list name "-IS-LIST") name))
         (wb (fn-dss-name (list name "-WORK-BOUND") name))
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
                   (lambda (i end ,@sfs) (,loop ,@ctx i end ,@sfs)))
                  (,(if within 'fn-dss-copyw 'fn-dss-copy)
                   (lambda (i end cap ,@sfs) (,name ,@ctx i end cap ,@sfs))))))
    `(,(fn-dss-contract mc `(implies (fn-cbor-octetp ,elt) (fn-cbor-octetp ,map))
                        'fn-dss-copy-f-octet `((fn-dss-copy-f ,mapf)) `((o ,elt)) ch)
      ,(fn-dss-contract cc `(and (natp ,cost-max) (<= (nfix ,cost) ,cost-max))
                        'fn-dss-copy-cost-contract
                        `((fn-dss-copy-cost (lambda (,elt) ,cost)) (fn-dss-copy-cmax (lambda () ,cost-max)))
                        `((o ,elt)) ch)
      (defun ,loop (,@ctx i end ,@sfs)
        (declare (xargs :stobjs ,stobjs
                        :guard ,(fn-dss-and guard
                                            `(and ,*fn-dss-span-guard*
                                                  ,@(and within '((<= end (fn-octets-len fn-octets))))))
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
            (mv :refused ,dst))))
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
                 :in-theory ,(fn-dss-defs-theory (list work)))))
      (verify-guards ,loop
        :hints ,(or guard-hints
                    `(("Goal" :in-theory (enable ,@(fn-dss-guard-theory))))))
      (verify-guards ,name)
      (table fn-generated ',name
             '(:def-span-scan :shape :copy :within ,within :loop ,loop :list ,lst :work ,work
                              :bridge ,bridge :c0 1 :c1 (+ 1 ,cost-max)
                              :writes (- end i) :workspace (i))))))

; ---- :stream

(defun fn-dss-stream-events (name ctx elt state-type step final emit-max final-max
                                  cost cost-max final-cost final-cost-max guard guard-hints
                                  constraint-hints wrld)
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
         (work (fn-dss-name (list name "-WORK") name))
         (bridge (fn-dss-name (list name "-IS-LIST") name))
         (part (fn-dss-name (list name "-DRIVE-IS-ITEMS") name))
         (writes (fn-dss-name (list name "-WRITES") name))
         (ty (fn-dss-name (list name "-STATE-TYPE") name))
         (prog (fn-dss-name (list name "-PROGRESS") name))
         (wb (fn-dss-name (list name "-WORK-BOUND") name))
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
                   (fn-dss-stream-loop (lambda (s i end last cap fn-octets fn-dss-out)
                                         (,loopn ,@ctx s i end last cap fn-octets fn-dss-out)))))
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
         (sc (fn-dss-name (list name "-STEP-CONTRACT") name))
         (stc (fn-dss-name (list name "-STEP-TYPE") name))
         (cc (fn-dss-name (list name "-COST-CONTRACT") name))
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
      ,(fn-dss-contract cc `(and (natp ,cost-max) (<= (nfix ,cost) ,cost-max)
                                 (natp ,final-cost-max) (<= (nfix ,final-cost) ,final-cost-max))
                        'fn-dss-st-cost-contract
                        `((fn-dss-st-cost (lambda (s ,elt) ,cost)) (fn-dss-st-cmax (lambda () ,cost-max))
                          (fn-dss-st-fcost (lambda (s) ,final-cost))
                          (fn-dss-st-fcmax (lambda () ,final-cost-max)))
                        `((o ,elt)) constraint-hints)
      (defun ,loopn (,@ctx s i end last cap fn-octets fn-dss-out)
        (declare (xargs :stobjs (fn-octets fn-dss-out)
                        :guard ,(fn-dss-and guard `(and ,*fn-dss-span-guard* (natp cap)
                                                       (unsigned-byte-p 59 cap)))
                        :measure (nfix (- (nfix end) (nfix i)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))
                        :verify-guards nil)
                 (type ,state-type s)
                 (type (unsigned-byte 59) i end cap))
        (if (and (mbt (and (natp i) (natp end))) (< i end))
            (if (< (nfix (- cap (fn-dss-out-len fn-dss-out))) ,emit-max)
                (mv :need-output s i fn-dss-out)
              (let ((,elt (fn-octets-get i fn-octets))) (declare (ignorable ,elt))
                (mv-let (dss-s2 dss-k dss-w dss-sig) ,step
                  (if (eql dss-sig 2)
                      (mv :refused dss-s2 i fn-dss-out)
                    (let ((fn-dss-out (fn-dss-out-append-word dss-w dss-k fn-dss-out)))
                      (if (eql dss-sig 1)
                          (mv :yield dss-s2 (+ 1 i) fn-dss-out)
                        (,loopn ,@ctx dss-s2 (+ 1 i) end last cap fn-octets fn-dss-out)))))))
          (if last
              (if (< (nfix (- cap (fn-dss-out-len fn-dss-out))) ,final-max)
                  (mv :need-output s i fn-dss-out)
                (mv-let (dss-s2 dss-k dss-w dss-sig) ,final
                  (if (eql dss-sig 2)
                      (mv :refused dss-s2 i fn-dss-out)
                    (let ((fn-dss-out (fn-dss-out-append-word dss-w dss-k fn-dss-out)))
                      (mv :done dss-s2 i fn-dss-out)))))
            (mv :need-input s i fn-dss-out))))
      (defun ,name (,@ctx s i end last cap fn-octets fn-dss-out)
        (declare (xargs :stobjs (fn-octets fn-dss-out)
                        :guard ,(fn-dss-and guard `(and ,*fn-dss-span-guard* (natp cap)
                                                       (unsigned-byte-p 59 cap)))
                        :verify-guards nil)
                 (type ,state-type s)
                 (type (unsigned-byte 59) i end cap))
        (if (< (nfix (- cap (fn-dss-out-len fn-dss-out))) ,floor)
            (mv :no-room s i fn-dss-out)
          (,loopn ,@ctx s i end last cap fn-octets fn-dss-out)))
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
        (implies (and (natp i) (true-listp fn-dss-out))
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
                 :in-theory ,(fn-dss-defs-theory (list name loopn lst lstl items host run)))))
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
                 :in-theory ,(fn-dss-defs-theory (list work)))
))
      (verify-guards ,name
        :hints ,(or guard-hints
                    `(("Goal" :in-theory (enable ,@(fn-dss-guard-theory))))))
      (table fn-generated ',name
             '(:def-span-scan :shape :stream :loop ,loopn :list ,lst :items ,items :drive ,drive
                              :host ,host :partition-stobj ,spart :assumes (:a-host-room)
                              :work ,work :bridge ,bridge :partition ,part
                              :c0 (+ 1 ,final-cost-max) :c1 (+ 1 ,cost-max)
                              :writes (+ (* ,emit-max (- dss-i2 i)) ,final-max)
                              :workspace (i s :type ,state-type))))))

; ---- the macro

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
            ,@(case shape
                (:find (fn-dss-find-events name ctx elt body (or cost cost-max) cost-max
                                           guard guard-hints constraint-hints))
                (:fold (fn-dss-fold-events name ctx elt acc acc-type body (or cost cost-max)
                                           cost-max guard guard-hints constraint-hints wrld))
                (:equal (fn-dss-equal-events name ctx elt (or norm elt) (or cost cost-max)
                                             cost-max against constant guard guard-hints constraint-hints))
                (:copy (fn-dss-copy-events name ctx elt (or map elt) (or cost cost-max)
                                           cost-max within guard guard-hints constraint-hints))
                (otherwise
                 (fn-dss-stream-events name ctx elt state-type step final emit-max final-max
                                       (or cost cost-max) cost-max
                                       (or final-cost (or final-cost-max 0)) (or final-cost-max 0)
                                       guard guard-hints constraint-hints wrld))))))))))

(defmacro def-span-scan (name ctx &key shape (elt 'o) body norm map against constant within
                              (acc 'acc) acc-type state-type step final emit-max final-max
                              cost cost-max final-cost final-cost-max (guard 't) guard-hints
                              constraint-hints)
  `(make-event
    (fn-dss-fn ',name ',ctx ',shape ',elt ',body ',norm ',map ',against ',constant ',within
               ',acc ',acc-type ',state-type ',step ',final ',emit-max ',final-max
               ',cost ',cost-max ',final-cost ',final-cost-max ',guard ',guard-hints
               ',constraint-hints state)))
