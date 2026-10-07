; fn: decision tracing -- what a trace row is, what it may hold, and whether a
; node may trace at all (lane obs-decision-trace, 2026-10-07; observability
; program section 2a, keystones DT-1, DT-2).
;
; A trace is a VIEW over a decision already made.  The host records what
; `fnn-call' returned (host/native/io.lisp), never computes a value the books
; compute, never branches on a trace.  This book is the books' half:
;
;   * the ROW: (POINT INPUTS OUTCOME), POINT the traced entry's name, INPUTS
;     one atom per input the entry's `:trace' declaration names (its
;     projection: the value of a bounded formal, the length of a list, a
;     digest the host took, or :redacted), OUTCOME the entry's declared
;     projection of what it returned.  Every part is a RECORD: a natural below
;     2^64, a short symbol, or a list of at most 8 atoms and flat lists of
;     atoms, within 256 octets of memory (`fn-dtrace-recordp').  A value that
;     does not fit is recorded as :unbounded, by name, never truncated.
;   * the BOUND: `fn-dtrace-row-octets' of every row built from records is
;     within `*fn-dtrace-max-row-octets*' (DT-2), so the ring the host
;     allocates has a size that is a function of its capacity alone.
;   * the PLAN: `fn-dtrace-admit' decides, from the profile's `[trace]' table
;     and the image profile, whether tracing is configured and with which
;     classes, capacity, sampling and allocation scope, or refuses by name.
;     `fn-dtrace-ring-octets' is the plan's memory, which the heap figure
;     charges (it is 0 for the default: no table, no ring).
;   * the VERB: `fn-dtrace-verb' decides what `trace on|off|drain' does.
;
; What each traced entry records is declared where the entry is, by
; `definterface :trace' (books/definterface.lisp), which generates DT-1 for it:
; the recorded outcome determines the declared decision part.  The selectors
; and clippers the declarations name (`fn-dtrace-v0', `fn-dtrace-v0-clip', ...)
; live here.
;
; This book is pure arithmetic and list recognition: it includes nothing, so
; books/definterface.lisp may include it.  Prefix `fn-dtrace-' (docs/prefixes.md).

(in-package "ACL2")

; -----------------------------------------------------------------------------
; Records.

(defconst *fn-dtrace-classes* '(:verdict :refusal :tariff :schedule :plan))
(defconst *fn-dtrace-max-atom* 18446744073709551615)
(defconst *fn-dtrace-max-name* 48)
(defconst *fn-dtrace-max-width* 8)
(defconst *fn-dtrace-atom-octets* 16)     ; a bignum, the worst case of an atom
(defconst *fn-dtrace-cons-octets* 16)
(defconst *fn-dtrace-max-record-octets* 256)
(defconst *fn-dtrace-row-overhead-octets* 64) ; the row's three conses and its point
(defconst *fn-dtrace-max-row-octets* 576)     ; 64 + 256 + 256

(defun fn-dtrace-atomp (x)
  (declare (xargs :guard t))
  (or (and (natp x) (<= x *fn-dtrace-max-atom*))
      (and (symbolp x) (<= (length (symbol-name x)) *fn-dtrace-max-name*))))

(defun fn-dtrace-flatp (xs n)
  ; a NIL-terminated list of at most N atoms
  (declare (xargs :guard (natp n)))
  (cond ((atom xs) (null xs))
        ((zp n) nil)
        (t (and (fn-dtrace-atomp (car xs))
                (fn-dtrace-flatp (cdr xs) (1- n))))))

(defun fn-dtrace-cellsp (xs n)
  ; a NIL-terminated list of at most N atoms or flat lists
  (declare (xargs :guard (natp n)))
  (cond ((atom xs) (null xs))
        ((zp n) nil)
        (t (and (or (fn-dtrace-atomp (car xs))
                    (fn-dtrace-flatp (car xs) *fn-dtrace-max-width*))
                (fn-dtrace-cellsp (cdr xs) (1- n))))))

(defun fn-dtrace-flat-size (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      0
    (+ *fn-dtrace-cons-octets* *fn-dtrace-atom-octets* (fn-dtrace-flat-size (cdr xs)))))

(defun fn-dtrace-cells-size (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      0
    (+ *fn-dtrace-cons-octets*
       (if (consp (car xs))
           (fn-dtrace-flat-size (car xs))
         *fn-dtrace-atom-octets*)
       (fn-dtrace-cells-size (cdr xs)))))

(defun fn-dtrace-size (x)
  (declare (xargs :guard t))
  (if (consp x) (fn-dtrace-cells-size x) *fn-dtrace-atom-octets*))

(defun fn-dtrace-recordp (x)
  (declare (xargs :guard t))
  (and (or (fn-dtrace-atomp x) (fn-dtrace-cellsp x *fn-dtrace-max-width*))
       (<= (fn-dtrace-size x) *fn-dtrace-max-record-octets*)))

(defun fn-dtrace-clip (x)
  ; X if it is a record, else the word that says it was not
  (declare (xargs :guard t))
  (if (fn-dtrace-recordp x) x :unbounded))

(defun fn-dtrace-atom-clip (x)
  (declare (xargs :guard t))
  (if (fn-dtrace-atomp x) x :unbounded))

(defun fn-dtrace-length-of (x)
  ; the :length projection: the length of a string or list, clipped
  (declare (xargs :guard t))
  (cond ((stringp x) (fn-dtrace-atom-clip (length x)))
        ((true-listp x) (fn-dtrace-atom-clip (len x)))
        (t :unbounded)))

(defthm fn-dtrace-clip-is-a-record
  (fn-dtrace-recordp (fn-dtrace-clip x)))

(defthm fn-dtrace-clip-keeps-a-record
  (implies (fn-dtrace-recordp x)
           (equal (fn-dtrace-clip x) x)))

(defthm fn-dtrace-atom-clip-is-a-record
  (fn-dtrace-recordp (fn-dtrace-atom-clip x)))

(defthm fn-dtrace-length-of-is-a-record
  (fn-dtrace-recordp (fn-dtrace-length-of x)))

; -----------------------------------------------------------------------------
; DT-2.  Bounded rows.

(defun fn-dtrace-row-octets (inputs outcome)
  (declare (xargs :guard t))
  (+ *fn-dtrace-row-overhead-octets*
     (fn-dtrace-size inputs)
     (fn-dtrace-size outcome)))

(defun fn-dtrace-rowp (row)
  (declare (xargs :guard t))
  (and (true-listp row)
       (equal (len row) 3)
       (symbolp (car row))
       (fn-dtrace-atomp (car row))
       (fn-dtrace-recordp (cadr row))
       (fn-dtrace-recordp (caddr row))))

(defthm fn-dtrace-size-of-a-record-is-bounded
  (implies (fn-dtrace-recordp x)
           (<= (fn-dtrace-size x) *fn-dtrace-max-record-octets*))
  :rule-classes :linear)

; KEYSTONE DT-2: a row built from records is within the row bound, whatever
; the entry, the inputs or the outcome.
(defthm fn-dtrace-row-is-bounded
  (implies (and (fn-dtrace-recordp inputs) (fn-dtrace-recordp outcome))
           (<= (fn-dtrace-row-octets inputs outcome) *fn-dtrace-max-row-octets*))
  :rule-classes :linear)

; The bound is reached (the teeth of the statement above: it is not slack).
(defthm fn-dtrace-the-record-bound-is-reached
  (let ((x '(nil nil nil nil nil nil nil nil)))
    (and (fn-dtrace-recordp x)
         (equal (fn-dtrace-size x) *fn-dtrace-max-record-octets*)
         (equal (fn-dtrace-row-octets x x) *fn-dtrace-max-row-octets*)
         ;; one more cell is not a record
         (not (fn-dtrace-recordp (cons nil x)))))
  :rule-classes nil)

; An atom is not slack either: a symbol of 49 characters, a natural of 2^64,
; and a nine-atom list are refused.
(defthm fn-dtrace-the-record-bounds-refuse
  (and (not (fn-dtrace-recordp 18446744073709551616))
       (not (fn-dtrace-recordp '(1 2 3 4 5 6 7 8 9)))
       (not (fn-dtrace-recordp '|AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA|)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The selectors and clippers the declarations name.  VALS is the list of the
; values the entry returned (an mv's values in order; a single value is a
; one-element list).  A clipper is the selector followed by `fn-dtrace-clip',
; so for a decision part that is a record it keeps the part exactly.

(defun fn-dtrace-v0 (vals)
  (declare (xargs :guard t))
  (if (consp vals) (car vals) nil))

(defun fn-dtrace-v1 (vals)
  (declare (xargs :guard t))
  (if (consp vals) (fn-dtrace-v0 (cdr vals)) nil))

(defun fn-dtrace-v0-clip (vals)
  (declare (xargs :guard t))
  (fn-dtrace-clip (fn-dtrace-v0 vals)))

(defun fn-dtrace-v1-clip (vals)
  (declare (xargs :guard t))
  (fn-dtrace-clip (fn-dtrace-v1 vals)))

; The first element of the first value: an entry that returns one list whose
; head is its word.
(defun fn-dtrace-v0car (vals)
  (declare (xargs :guard t))
  (let ((x (fn-dtrace-v0 vals))) (if (consp x) (car x) nil)))

(defun fn-dtrace-v0car-clip (vals)
  (declare (xargs :guard t))
  (fn-dtrace-clip (fn-dtrace-v0car vals)))

(defthm fn-dtrace-v0-clip-keeps-a-record-decision
  (implies (fn-dtrace-recordp (fn-dtrace-v0 vals))
           (equal (fn-dtrace-v0-clip vals) (fn-dtrace-v0 vals))))

(defthm fn-dtrace-v1-clip-keeps-a-record-decision
  (implies (fn-dtrace-recordp (fn-dtrace-v1 vals))
           (equal (fn-dtrace-v1-clip vals) (fn-dtrace-v1 vals))))

(defthm fn-dtrace-v0car-clip-keeps-a-record-decision
  (implies (fn-dtrace-recordp (fn-dtrace-v0car vals))
           (equal (fn-dtrace-v0car-clip vals) (fn-dtrace-v0car vals))))

; -----------------------------------------------------------------------------
; The projections of an entry's inputs.  PROJ is :value, :length, :digest,
; :redact or (:with FN); the host passes, for each non-redacted named input,
; the argument (for :digest, the natural the host's digest of the buffer
; begins with).  `fn-dtrace-input-of' is the one place a projection is
; applied; (:with FN) is applied by the generated dispatch
; (host/interfaces.lisp), which knows FN.

(defun fn-dtrace-input-of (proj x)
  (declare (xargs :guard t))
  (case proj
    (:value (fn-dtrace-atom-clip x))
    (:length (fn-dtrace-length-of x))
    (:digest (fn-dtrace-atom-clip x))
    (otherwise :redacted)))

(defthm fn-dtrace-atomp-is-no-cons
  (implies (fn-dtrace-atomp x) (not (consp x))))

(defthm fn-dtrace-atom-clip-is-an-atom
  (fn-dtrace-atomp (fn-dtrace-atom-clip x)))

(defthm fn-dtrace-length-of-is-an-atom
  (fn-dtrace-atomp (fn-dtrace-length-of x)))

(defthm fn-dtrace-input-of-is-an-atom
  (fn-dtrace-atomp (fn-dtrace-input-of proj x)))

(defthm fn-dtrace-input-of-is-a-record
  (fn-dtrace-recordp (fn-dtrace-input-of proj x)))

(defconst *fn-dtrace-input-projections* '(:value :length :digest :redact))

; Kinds (books/payload-kinds.lisp *fn-entry-guard-kinds*) a bounded :value
; may be taken of, and the kinds whose bytes are secret or payload: those
; admit :redact or :length only.
(defconst *fn-dtrace-value-kinds* '(natp posp booleanp keywordp symbolp))
(defconst *fn-dtrace-secret-kinds*
  '(fn-cbor-octet-listp fn-octet-list-listp fn-payload-handle-p stringp))
(defconst *fn-dtrace-length-kinds*
  '(fn-cbor-octet-listp fn-octet-list-listp true-listp stringp))

; -----------------------------------------------------------------------------
; The plan.  SPEC is the `[trace]' table as the config reader gives it
; (books/decision-trace-config.lisp): NIL when the profile has no table, else
; (CLASSES CAPACITY SAMPLE-EVERY ALLOCATION START RSS-EVERY), each NIL when the key is
; absent.  IMAGE is the saved image's profile, :production or :developer.

(defconst *fn-dtrace-default-capacity* 1024)
(defconst *fn-dtrace-max-capacity* 65536)
(defconst *fn-dtrace-max-sample-every* 1000000)
(defconst *fn-dtrace-max-rss-every* 1000000)  ; 0: resident size never sampled (the default)
(defconst *fn-dtrace-row-slot-octets* 1024)   ; the ring row's struct and a row at the bound
(defconst *fn-dtrace-ring-header-octets* 4096)

(defun fn-dtrace-class-listp (cs)
  (declare (xargs :guard t))
  (cond ((atom cs) (null cs))
        (t (and (member-eq (car cs) *fn-dtrace-classes*)
                (fn-dtrace-class-listp (cdr cs))))))

(defun fn-dtrace-in (x xs)
  (declare (xargs :guard t))
  (cond ((atom xs) nil)
        (t (or (equal x (car xs)) (fn-dtrace-in x (cdr xs))))))

(defun fn-dtrace-dup-free (xs)
  (declare (xargs :guard t))
  (cond ((atom xs) t)
        (t (and (not (fn-dtrace-in (car xs) (cdr xs)))
                (fn-dtrace-dup-free (cdr xs))))))

(defun fn-dtrace-classes-refusal (cs)
  ; NIL, or the reason a class list is refused
  (declare (xargs :guard t))
  (cond ((not (true-listp cs)) :classes)
        ((null cs) :no-classes)
        ((not (fn-dtrace-class-listp cs)) :unknown-class)
        ((not (fn-dtrace-dup-free cs)) :duplicate-class)
        (t nil)))

(defun fn-dtrace-nth (i x)
  (declare (xargs :guard (natp i)))
  (if (true-listp x) (nth i x) nil))

(defun fn-dtrace-spec-classes (spec) (declare (xargs :guard t)) (fn-dtrace-nth 0 spec))
(defun fn-dtrace-spec-capacity (spec) (declare (xargs :guard t)) (fn-dtrace-nth 1 spec))
(defun fn-dtrace-spec-sample-every (spec) (declare (xargs :guard t)) (fn-dtrace-nth 2 spec))
(defun fn-dtrace-spec-allocation (spec) (declare (xargs :guard t)) (fn-dtrace-nth 3 spec))
(defun fn-dtrace-spec-start (spec) (declare (xargs :guard t)) (fn-dtrace-nth 4 spec))
(defun fn-dtrace-spec-rss-every (spec) (declare (xargs :guard t)) (fn-dtrace-nth 5 spec))

; (:off) -- no table, nothing traced and nothing allocated;
; (:plan CLASSES CAPACITY SAMPLE-EVERY ALLOCATION START);
; (:refused REASON), the reason a keyword naming the first thing refused.
(defun fn-dtrace-admit (spec image)
  (declare (xargs :guard t))
  (let ((classes (or (fn-dtrace-spec-classes spec) *fn-dtrace-classes*))
        (capacity (or (fn-dtrace-spec-capacity spec) *fn-dtrace-default-capacity*))
        (every (or (fn-dtrace-spec-sample-every spec) 1))
        (allocation (fn-dtrace-spec-allocation spec))
        (start (fn-dtrace-spec-start spec))
        (rss-every (or (fn-dtrace-spec-rss-every spec) 0)))
    (cond ((null spec) (list :off))
          ((not (member-eq image '(:production :developer))) (list :refused :unknown-image))
          ((fn-dtrace-classes-refusal classes)
           (list :refused (fn-dtrace-classes-refusal classes)))
          ((not (and (natp capacity) (<= 1 capacity) (<= capacity *fn-dtrace-max-capacity*)))
           (list :refused :capacity))
          ((not (and (natp every) (<= 1 every) (<= every *fn-dtrace-max-sample-every*)))
           (list :refused :sample-every))
          ((not (member-eq allocation '(nil :process :isolated-process)))
           (list :refused :allocation))
          ((and (eq allocation :isolated-process) (not (eq image :developer)))
           (list :refused :isolated-allocation-needs-developer-image))
          ((not (member-eq start '(nil :on :off))) (list :refused :start))
          ((not (and (natp rss-every) (<= rss-every *fn-dtrace-max-rss-every*)))
           (list :refused :rss-every))
          (t (list :plan classes capacity every allocation (eq start :on) rss-every)))))

(defun fn-dtrace-planp (p)
  (declare (xargs :guard t))
  (and (true-listp p) (eq (car p) :plan) (equal (len p) 7)))

(defun fn-dtrace-plan-classes (p) (declare (xargs :guard t)) (fn-dtrace-nth 1 p))
(defun fn-dtrace-plan-capacity (p) (declare (xargs :guard t)) (nfix (fn-dtrace-nth 2 p)))
(defun fn-dtrace-plan-sample-every (p) (declare (xargs :guard t)) (fn-dtrace-nth 3 p))
(defun fn-dtrace-plan-allocation (p) (declare (xargs :guard t)) (fn-dtrace-nth 4 p))
(defun fn-dtrace-plan-start-p (p) (declare (xargs :guard t)) (and (fn-dtrace-nth 5 p) t))
(defun fn-dtrace-plan-rss-every (p) (declare (xargs :guard t)) (nfix (fn-dtrace-nth 6 p)))

; The memory a plan commits: a header and one slot per ring row.  The ring is
; reserved from the start whether or not tracing starts on, because `trace on'
; allocates it later and the heap figure must have held it.  No plan, no ring:
; the default charge is 0.
(defun fn-dtrace-ring-octets (plan)
  (declare (xargs :guard t))
  (if (fn-dtrace-planp plan)
      (+ *fn-dtrace-ring-header-octets*
         (* *fn-dtrace-row-slot-octets* (fn-dtrace-plan-capacity plan)))
    0))

(defthm fn-dtrace-ring-octets-natp
  (natp (fn-dtrace-ring-octets plan))
  :rule-classes :type-prescription)

; The row slot holds the row at its bound (the struct's own words fit the
; slack above *fn-dtrace-max-row-octets*).
(defthm fn-dtrace-slot-holds-a-row
  (<= *fn-dtrace-max-row-octets* *fn-dtrace-row-slot-octets*)
  :rule-classes nil)

; The default is off and charges nothing.
(defthm fn-dtrace-the-default-is-off-and-free
  (and (equal (fn-dtrace-admit nil :production) '(:off))
       (equal (fn-dtrace-admit nil :developer) '(:off))
       (equal (fn-dtrace-ring-octets (fn-dtrace-admit nil :production)) 0))
  :rule-classes nil)

; KEYSTONE: an accepted plan is in range -- a capacity the ring can hold, a
; sample rate, a class list of known classes -- and its ring fits the bound
; that is a function of the capacity alone.
(defthm fn-dtrace-admitted-plan-is-in-range
  (implies (fn-dtrace-planp (fn-dtrace-admit spec image))
           (let ((p (fn-dtrace-admit spec image)))
             (and (<= 1 (fn-dtrace-plan-capacity p))
                  (<= (fn-dtrace-plan-capacity p) *fn-dtrace-max-capacity*)
                  (natp (fn-dtrace-plan-sample-every p))
                  (<= 1 (fn-dtrace-plan-sample-every p))
                  (<= (fn-dtrace-plan-sample-every p) *fn-dtrace-max-sample-every*)
                  (consp (fn-dtrace-plan-classes p))
                  (fn-dtrace-class-listp (fn-dtrace-plan-classes p))
                  (<= (fn-dtrace-ring-octets p)
                      (+ *fn-dtrace-ring-header-octets*
                         (* *fn-dtrace-row-slot-octets* *fn-dtrace-max-capacity*))))))
  :rule-classes nil)

; Each refusal, by name (the hypothesis-removal witnesses: one thing wrong,
; everything else right).
(defthm fn-dtrace-admit-refuses-by-name
  (and (equal (fn-dtrace-admit '(nil 0 nil nil nil) :production) '(:refused :capacity))
       (equal (fn-dtrace-admit '(nil 65537 nil nil nil) :production) '(:refused :capacity))
       (equal (fn-dtrace-admit '(nil 8 0 nil nil) :production) '(:refused :sample-every))
       (equal (fn-dtrace-admit '((:verdict :nonsense) 8 nil nil nil) :production)
              '(:refused :unknown-class))
       (equal (fn-dtrace-admit '((:verdict :verdict) 8 nil nil nil) :production)
              '(:refused :duplicate-class))
       (equal (fn-dtrace-admit '(nil 8 nil :everything nil) :production) '(:refused :allocation))
       (equal (fn-dtrace-admit '(nil 8 nil :isolated-process nil) :production)
              '(:refused :isolated-allocation-needs-developer-image))
       (equal (fn-dtrace-admit '(nil 8 nil nil :maybe) :production) '(:refused :start))
       (equal (fn-dtrace-admit '(nil 8 nil nil nil 1000001) :production) '(:refused :rss-every))
       (equal (fn-dtrace-admit '(nil 8 nil nil nil) :elsewhere) '(:refused :unknown-image)))
  :rule-classes nil)

; The acceptance witnesses: an accepted plan with every field read back.
(defthm fn-dtrace-admit-accepts
  (and (equal (fn-dtrace-admit '((:verdict :plan) 8 4 :process :on) :production)
              '(:plan (:verdict :plan) 8 4 :process t 0))
       (equal (fn-dtrace-admit '(nil nil nil nil nil) :production)
              '(:plan (:verdict :refusal :tariff :schedule :plan) 1024 1 nil nil 0))
       (equal (fn-dtrace-admit '(nil 8 nil nil nil 64) :production)
              '(:plan (:verdict :refusal :tariff :schedule :plan) 8 1 nil nil 64))
       (equal (fn-dtrace-admit '(nil 8 nil :isolated-process nil) :developer)
              '(:plan (:verdict :refusal :tariff :schedule :plan) 8 1 :isolated-process nil 0))
       (equal (fn-dtrace-ring-octets
               (fn-dtrace-admit '(nil nil nil nil nil) :production))
              (+ 4096 (* 1024 1024))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The verb.  `fn operator CONFIG trace on|off|drain': the plan the profile
; yields, whether tracing is on now, and the verb.  The answer is the action
; the host takes, or a refusal by name.  The verb writes no store: its FNCT
; kind is classified :read (books/native-control-kinds.lisp).

(defun fn-dtrace-verb (verb plan active)
  (declare (xargs :guard t))
  (cond ((not (member-eq verb '(:on :off :drain))) (list :refused :unknown-verb))
        ((eq verb :on)
         (cond ((not (fn-dtrace-planp plan)) (list :refused :not-configured))
               (active (list :refused :already-on))
               (t (list :enable))))
        ((eq verb :off)
         (if active (list :disable) (list :refused :already-off)))
        (t (if active (list :drain) (list :refused :not-on)))))

(defthm fn-dtrace-verb-never-enables-without-a-plan
  (implies (not (fn-dtrace-planp plan))
           (not (equal (fn-dtrace-verb verb plan active) '(:enable)))))

(defthm fn-dtrace-verb-drains-only-a-running-trace
  (implies (not active)
           (not (equal (fn-dtrace-verb verb plan active) '(:drain)))))

(defthm fn-dtrace-verb-witnesses
  (let ((plan (fn-dtrace-admit '(nil nil nil nil nil) :production)))
    (and (equal (fn-dtrace-verb :on plan nil) '(:enable))
         (equal (fn-dtrace-verb :on plan t) '(:refused :already-on))
         (equal (fn-dtrace-verb :on '(:off) nil) '(:refused :not-configured))
         (equal (fn-dtrace-verb :off plan t) '(:disable))
         (equal (fn-dtrace-verb :off plan nil) '(:refused :already-off))
         (equal (fn-dtrace-verb :drain plan t) '(:drain))
         (equal (fn-dtrace-verb :drain plan nil) '(:refused :not-on))
         (equal (fn-dtrace-verb :flush plan t) '(:refused :unknown-verb))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Counters (DT-5).  The host's ring counts every call it considers; each one
; is recorded, dropped (the ring was full) or sampled out.  The drain asserts
; the identity through ACL2's decision on the snapshot.

(defun fn-dtrace-counters-balance-p (attempts recorded dropped sampled-out)
  (declare (xargs :guard t))
  (and (natp attempts) (natp recorded) (natp dropped) (natp sampled-out)
       (equal attempts (+ recorded dropped sampled-out))))

(defthm fn-dtrace-counters-witnesses
  (and (fn-dtrace-counters-balance-p 100 7 93 0)
       (fn-dtrace-counters-balance-p 100 7 43 50)
       (not (fn-dtrace-counters-balance-p 100 7 92 0))
       (not (fn-dtrace-counters-balance-p 100 8 93 0)))
  :rule-classes nil)
