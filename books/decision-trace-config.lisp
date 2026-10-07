; fn: the profile's `[trace]' table, read (lane obs-decision-trace).
;
; Decision tracing is off in every image by default.  A profile that wants it
; available says so in a table (books/native-config.lisp admits it; the
; owner's configuration record does not carry it, as with `[web]' and `[tls]'):
;
;   [trace]
;   classes = "all"              ; or "verdict,refusal,tariff,schedule,plan"
;   capacity = 4096              ; ring rows, 1 to 65,536 (default 1024)
;   sample_every = 1             ; keep every Nth matching call (default 1)
;   allocation = "none"          ; none, process or isolated-process
;   start = "off"                ; on: the ring runs from the start
;   rss_every = 0                ; resident size every Nth request, 0 never
;
; A table with no key is no table: the plan is then (:off), nothing is
; allocated and `trace on' is refused by name (:not-configured).  Every key is
; optional; a value that is not what its key says is refused by name before
; the node listens.  `fn-dtrace-admit' (books/decision-trace.lisp) decides the
; plan from the values read here and the saved image's profile; the plan's ring
; is what the heap figure charges.
;
; Prefix `fn-dtrace-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "native-config")
(include-book "decision-trace")

(defconst *fn-dtrace-class-names*
  '((:verdict . "verdict") (:refusal . "refusal") (:tariff . "tariff")
    (:schedule . "schedule") (:plan . "plan")))

(defun fn-dtrace-class-of-chars (chars names)
  (declare (xargs :guard t))
  (cond ((atom names) nil)
        ((and (consp (car names)) (stringp (cdr (car names)))
              (equal chars (coerce (cdr (car names)) 'list)))
         (car (car names)))
        (t (fn-dtrace-class-of-chars chars (cdr names)))))

; The classes a `classes' string names: NIL for "all" (every class), a list of
; keywords, or :bad.  Names are separated by commas, with nothing else.
(defun fn-dtrace-split-names (chars current out)
  ; the keyword of each comma-separated name, in order, or :bad
  (declare (xargs :guard t))
  (cond ((atom chars)
         (let ((class (fn-dtrace-class-of-chars (fn-ncfg-reverse current)
                                                *fn-dtrace-class-names*)))
           (if class (fn-ncfg-reverse (cons class out)) :bad)))
        ((equal (car chars) #\,)
         (let ((class (fn-dtrace-class-of-chars (fn-ncfg-reverse current)
                                                *fn-dtrace-class-names*)))
           (if class
               (fn-dtrace-split-names (cdr chars) nil (cons class out))
             :bad)))
        (t (fn-dtrace-split-names (cdr chars) (cons (car chars) current) out))))

(defun fn-dtrace-classes-of (text)
  (declare (xargs :guard t))
  (cond ((null text) nil)
        ((not (stringp text)) :bad)
        ((equal text "all") nil)
        (t (fn-dtrace-split-names (coerce text 'list) nil nil))))

(defun fn-dtrace-allocation-of (text)
  (declare (xargs :guard t))
  (cond ((null text) nil)
        ((equal text "none") nil)
        ((equal text "process") :process)
        ((equal text "isolated-process") :isolated-process)
        (t :bad)))

(defun fn-dtrace-start-of (text)
  (declare (xargs :guard t))
  (cond ((null text) nil)
        ((equal text "on") :on)
        ((equal text "off") :off)
        (t :bad)))

(defun fn-dtrace-table-present-p (pairs)
  (declare (xargs :guard t))
  (cond ((atom pairs) nil)
        ((equal (fn-ncfg-first (car pairs)) "trace") t)
        (t (fn-dtrace-table-present-p (cdr pairs)))))

; (:none), (:spec SPEC) or (:refused KEY).
(defun fn-dtrace-spec-of (pairs)
  (declare (xargs :guard t))
  (if (not (fn-dtrace-table-present-p pairs))
      (list :none)
    (let ((classes (fn-dtrace-classes-of
                    (fn-ncfg-string-value (fn-ncfg-value pairs "trace" "classes")
                                          nil *fn-ncfg-max-text* nil)))
          (capacity (fn-ncfg-nat-value (fn-ncfg-value pairs "trace" "capacity")
                                       nil *fn-ncfg-max-u64*))
          (every (fn-ncfg-nat-value (fn-ncfg-value pairs "trace" "sample_every")
                                    nil *fn-ncfg-max-u64*))
          (allocation (fn-dtrace-allocation-of
                       (fn-ncfg-string-value (fn-ncfg-value pairs "trace" "allocation")
                                             nil *fn-ncfg-max-text* nil)))
          (start (fn-dtrace-start-of
                  (fn-ncfg-string-value (fn-ncfg-value pairs "trace" "start")
                                        nil *fn-ncfg-max-text* nil)))
          (rss (fn-ncfg-nat-value (fn-ncfg-value pairs "trace" "rss_every")
                                  nil *fn-ncfg-max-u64*)))
      (cond ((eq classes :bad) (list :refused :classes))
            ((eq capacity :bad) (list :refused :capacity))
            ((eq every :bad) (list :refused :sample-every))
            ((eq allocation :bad) (list :refused :allocation))
            ((eq start :bad) (list :refused :start))
            ((eq rss :bad) (list :refused :rss-every))
            (t (list :spec (list classes capacity every allocation start rss)))))))

(defun fn-dtrace-pairs-of (octets)
  (declare (xargs :guard t))
  (if (and (fn-ncfg-ascii-octetsp octets)
           (<= (len octets) *fn-ncfg-max-octets*))
      (let ((lines (fn-ncfg-lines octets)))
        (if (< *fn-ncfg-max-lines* (len lines))
            :bad
          (fn-ncfg-parse-lines lines nil nil nil)))
    :bad))

; THE PLAN read from the octets the operator's profile was loaded from and the
; saved image's profile (:production or :developer): (:off), (:plan ...) or
; (:refused REASON), REASON naming the key or the rule.
(defun fn-dtrace-config-plan (octets image)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((pairs (fn-dtrace-pairs-of octets)))
    (if (equal pairs :bad)
        (list :refused :syntax)
      (let ((spec (fn-dtrace-spec-of pairs)))
        (cond ((equal (car spec) :none) (list :off))
              ((equal (car spec) :refused) spec)
              (t (fn-dtrace-admit (cadr spec) image)))))))

; The word of a plan: :plan, :off or :refused.
(defun fn-dtrace-plan-kind (plan)
  (declare (xargs :guard t))
  (cond ((fn-dtrace-planp plan) :plan)
        ((equal plan '(:off)) :off)
        (t :refused)))

(defun fn-dtrace-plan-refusal (plan)
  (declare (xargs :guard t))
  (if (and (true-listp plan) (equal (car plan) :refused) (consp (cdr plan)))
      (cadr plan)
    nil))

; KEYSTONE: a profile with no [trace] table is no trace, whatever the image;
; and what the profile gives, the plan holds.
(defthm fn-dtrace-no-table-no-ring
  (and (equal (fn-dtrace-config-plan (fn-record-string-octets "[store]
path = \"/s\"
") :production)
              '(:off))
       (equal (fn-dtrace-ring-octets
               (fn-dtrace-config-plan (fn-record-string-octets "[store]
path = \"/s\"
") :developer))
              0))
  :rule-classes nil)
