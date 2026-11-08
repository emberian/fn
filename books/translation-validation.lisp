; Canonical, lossless export identity, checked against the admitted ACL2 world.
; This book is independent of the assembly: the generated certificate includes
; its subject's assembly first, then submits these checks in that live world.
(in-package "ACL2")

(defun fn2-tv-codes (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars) nil
    (cons (char-code (car chars)) (fn2-tv-codes (cdr chars)))))

(defun fn2-tv-object (x)
  (declare (xargs :guard t))
  (cond ((consp x) (list :cons (fn2-tv-object (car x)) (fn2-tv-object (cdr x))))
        ((symbolp x) (list :symbol
                          (fn2-tv-codes (coerce (symbol-package-name x) 'list))
                          (fn2-tv-codes (coerce (symbol-name x) 'list))))
        ((integerp x) (list :integer x))
        ((rationalp x) (list :rational (numerator x) (denominator x)))
        ((complex-rationalp x) (list :complex (fn2-tv-object (realpart x))
                                            (fn2-tv-object (imagpart x))))
        ((characterp x) (list :character (char-code x)))
        ((stringp x) (list :string (fn2-tv-codes (coerce x 'list))))
        (t (list :unsupported))))

; Missing is different from NIL (a false guard) and from (QUOTE T).
(defun fn2-tv-property (fn key world)
  (declare (xargs :verify-guards nil))
  (getpropc fn key :missing world))

; Resolve ACL2's attachment property indirection without calling its :program
; attachment-pair utility. Both the constrained name and selected implementation
; remain in the export; this is never substituted for a logical body.
(defun fn2-tv-attachment (fn world)
  (declare (xargs :verify-guards nil))
  (let* ((prop (getpropc fn 'attachment nil world))
         (pairs (if (and prop (symbolp prop))
                    (getpropc prop 'attachment nil world) prop)))
    (if (or (atom pairs) (eq (car pairs) :attachment-disallowed)) nil
      (assoc-eq fn pairs))))

(defun fn2-tv-function (fn world)
  (declare (xargs :verify-guards nil))
  (list :function (fn2-tv-object fn)
        :formals (fn2-tv-object (fn2-tv-property fn 'formals world))
        :logical-body (fn2-tv-object (fn2-tv-property fn 'unnormalized-body world))
        :guard (fn2-tv-object (fn2-tv-property fn 'guard world))
        :justification (fn2-tv-object (fn2-tv-property fn 'justification world))
        :stobjs-in (fn2-tv-object (fn2-tv-property fn 'stobjs-in world))
        :stobjs-out (fn2-tv-object (fn2-tv-property fn 'stobjs-out world))
        :attachment (fn2-tv-object (fn2-tv-attachment fn world))))

(defun fn2-tv-matches-function (entry fn world)
  (declare (xargs :verify-guards nil))
  (and (function-symbolp fn world)
       (equal entry (fn2-tv-function fn world))))

(defthm fn2-tv-matches-function-exact
  (implies (fn2-tv-matches-function entry fn world)
           (equal entry (fn2-tv-function fn world)))
  :rule-classes nil)

(defun fn2-tv-declaration-fields (row)
  (declare (xargs :guard t))
  (if (and (consp row) (consp (cdr row)))
      (if (member-eq (car row) '(:generated :signature :reuse :definition))
          (fn2-tv-declaration-fields (cddr row))
        (cons (car row) (cons (cadr row) (fn2-tv-declaration-fields (cddr row)))))
    nil))

(defun fn2-tv-declarations (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (cons (cons (caar rows) (fn2-tv-declaration-fields (cdar rows)))
          (fn2-tv-declarations (cdr rows)))))

; The manifest is data bound to the live assembly, not an asserted checksum.
(defun fn2-tv-manifest (world)
  (declare (xargs :verify-guards nil))
  (list :core-layout (fn2-tv-object (getpropc '*fn2-core-children* 'const :missing world))
        :core-instance (fn2-tv-object (table-alist 'fn2-core-instance world))
        :children (fn2-tv-object (table-alist 'fn2-core-children world))
        :declarations (fn2-tv-object (fn2-tv-declarations (table-alist 'fn2-machine-kinds world)))
        :late-declarations (fn2-tv-object (table-alist 'fn2-machine-arm-bodies world))
        :narrowed-signatures (fn2-tv-object (table-alist 'fn2-arms-child-sigs world))))

(defmacro fn2-tv-check-function (entry fn)
  `(make-event
    (if (fn2-tv-matches-function ,entry ,fn (w state))
        '(value-triple :export-matches-live-function)
      (er soft 'fn2-tv-check-function "Export differs from the live function ~x0." ,fn))))

(defmacro fn2-tv-check-manifest (manifest)
  `(make-event
    (if (equal ,manifest (fn2-tv-manifest (w state)))
        '(value-triple :export-matches-live-assembly)
      (er soft 'fn2-tv-check-manifest "Export differs from the live assembly."))))

; The arm denominator is reconstructed from the live declarations. A proposal
; cannot obtain a larger coverage fraction by omitting a difficult arm.
(defun fn2-tv-declared (kind key world)
  (declare (xargs :verify-guards nil))
  (let ((late (cdr (assoc-eq kind (table-alist 'fn2-machine-arm-bodies world)))))
    (cadr (member-eq key (if (member-eq key late) late
                          (cdr (assoc-eq kind (table-alist 'fn2-machine-kinds world))))))))

(defun fn2-tv-arm-name (kind infix tag)
  (declare (xargs :verify-guards nil))
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name kind) infix (symbol-name tag)) 'fn2-core))

(defun fn2-tv-arm-entries (kind area infix entries children world)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (let* ((entry (car entries))
           (core (fn2-tv-arm-name kind infix (car entry)))
           (fn (if children (fn2-tv-arm-name core "-" 'children) core)))
      (cons (list kind area (car entry) (if children :children :core) fn
                  (if (and children (eq area :subarms)) nil core)
                  (cdr entry) (cdr (assoc-eq fn (table-alist 'fn2-arms-child-sigs world))))
            (fn2-tv-arm-entries kind area infix (cdr entries) children world)))))

(defun fn2-tv-arm-inventory-aux (kinds world)
  (declare (xargs :verify-guards nil))
  (if (atom kinds) nil
    (let* ((kind (caar kinds)) (arms (fn2-tv-declared kind :arms world))
           (children (and (consp arms)
                          (function-symbolp
                           (fn2-tv-arm-name (fn2-tv-arm-name kind "-RUN-" (caar arms))
                                            "-" 'children) world))))
      (append (fn2-tv-arm-entries kind :subarms "-SUB-" (fn2-tv-declared kind :subarms world) children world)
              (fn2-tv-arm-entries kind :arms "-RUN-" arms children world)
              (fn2-tv-arm-entries kind :observe-arms "-ON-" (fn2-tv-declared kind :observe-arms world) children world)
              (fn2-tv-arm-inventory-aux (cdr kinds) world)))))

(defun fn2-tv-arm-inventory (world)
  (declare (xargs :verify-guards nil))
  (fn2-tv-arm-inventory-aux (reverse (table-alist 'fn2-machine-kinds world)) world))

(defmacro fn2-tv-check-arm-inventory (inventory)
  `(make-event
    (if (equal ,inventory (fn2-tv-arm-inventory (w state)))
        '(value-triple :export-matches-complete-arm-inventory)
      (er soft 'fn2-tv-check-arm-inventory "Arm inventory is incomplete or differs from the live world."))))

(defun fn2-tv-matches-functions (entries world)
  (declare (xargs :verify-guards nil))
  (if (atom entries) (null entries)
    (and (fn2-tv-matches-function (cdar entries) (caar entries) world)
         (fn2-tv-matches-functions (cdr entries) world))))

(defmacro fn2-tv-check-functions (entries)
  `(make-event
    (if (fn2-tv-matches-functions ,entries (w state))
        '(value-triple :all-exports-match-live-functions)
      (er soft 'fn2-tv-check-functions "At least one export differs from its live function."))))

; Closure is checked in the live world, not inferred from an emitter's count.
(defconst *fn2-tv-native-boundary*
  '(if return-last equal cons car cdr consp integerp acl2-numberp rationalp symbolp stringp characterp coerce
    < binary-+ binary-* unary-- binary-logand binary-logior binary-logxor binary-logeqv lognot
    logorc1 floor mod evenp nonnegative-integer-quotient expt len nth mv-nth update-nth
    member-equal acl2-count char-code code-char ceiling ash))

(mutual-recursion
 (defun fn2-tv-calls (term)
   (declare (xargs :verify-guards nil))
   (cond ((or (atom term) (eq (car term) 'quote)) nil)
         ((consp (car term)) (append (fn2-tv-calls (caddar term)) (fn2-tv-calls-list (cdr term))))
         (t (cons (car term) (fn2-tv-calls-list (cdr term))))))
 (defun fn2-tv-calls-list (terms)
   (declare (xargs :verify-guards nil))
   (if (atom terms) nil
     (append (fn2-tv-calls (car terms)) (fn2-tv-calls-list (cdr terms))))))

(defun fn2-tv-closed-functions (names available world)
  (declare (xargs :verify-guards nil))
  (if (atom names) t
    (let* ((fn (car names))
           (body (getpropc fn 'unnormalized-body nil world))
           (guard (getpropc fn 'guard nil world))
           (measure (and (getpropc fn 'recursivep nil world)
                         (access justification (getpropc fn 'justification nil world) :measure)))
           (attachment (fn2-tv-attachment fn world)))
      (and (subsetp-eq (append (fn2-tv-calls body) (fn2-tv-calls guard) (fn2-tv-calls measure)
                              (and attachment (list (cdr attachment)))) available)
           (fn2-tv-closed-functions (cdr names) available world)))))

(defun fn2-tv-refused-functions (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) t
    (and (not (getpropc (car names) 'unnormalized-body nil world))
         (not (fn2-tv-attachment (car names) world))
         (fn2-tv-refused-functions (cdr names) world))))

(defun fn2-tv-arm-roots (inventory)
  (declare (xargs :verify-guards nil))
  (if (atom inventory) nil
    (append (list (fifth (car inventory)))
            (and (sixth (car inventory)) (list (sixth (car inventory))))
            (fn2-tv-arm-roots (cdr inventory)))))

(defun fn2-tv-host-roots (world acc)
  (declare (xargs :verify-guards nil))
  (if (atom world) acc
    (let ((fn (caar world)))
      (fn2-tv-host-roots
       (cdr world)
       (if (and (symbolp fn) (eq (cadar world) 'formals)
                (<= 9 (length (symbol-name fn)))
                (equal (subseq (symbol-name fn) 0 9) "FN2-HOST-"))
           (add-to-set-eq fn acc) acc)))))

(defun fn2-tv-served-closure-p (names refused world)
  (declare (xargs :verify-guards nil))
  (let ((available (append names refused *fn2-tv-native-boundary*)))
    (and (no-duplicatesp-eq names)
         (subsetp-eq (append '(fn2-turn) (fn2-tv-host-roots world nil)
                             (fn2-tv-arm-roots (fn2-tv-arm-inventory world))) available)
         (fn2-tv-refused-functions refused world)
         (fn2-tv-closed-functions names available world))))

(defmacro fn2-tv-check-served-closure (names refused)
  `(make-event
    (if (fn2-tv-served-closure-p ,names ,refused (w state))
        '(value-triple :complete-served-export-closure)
      (er soft 'fn2-tv-check-served-closure "Missing served root/callee, duplicate function, or false refusal."))))
