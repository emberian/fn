; One-byte / one-constructor-action checkpoint decode continuation.
; Unhooked until typed recovery, refinement and registered funding compose.
(in-package "ACL2")
(include-book "bp-checkpoint-value-domain")
(include-book "bp-node-rotation-codec")
(set-verify-guards-eagerness 2)

; This cold constant derives names from the actual finite keyword vocabulary.
; Served steps share its tails; they never construct a string or INTERN.
(defun fn-bpcr-keyword-table (symbols)
 (declare (xargs :guard (symbol-listp symbols)))
 (if (consp symbols)
  (cons (cons (fn-bpnr-codes (coerce (symbol-name (car symbols)) 'list))
              (car symbols))
        (fn-bpcr-keyword-table (cdr symbols))) nil))
(defconst *fn-bpcr-keywords* (fn-bpcr-keyword-table *fn-bpcv-keywords*))
(defun fn-bpcr-max-name (table)
 (declare (xargs :guard t))
 (if (consp table)
  (max (len (fn-cbor-ag-car (car table))) (fn-bpcr-max-name (cdr table))) 0))
(defconst *fn-bpcr-max-name* (fn-bpcr-max-name *fn-bpcr-keywords*))
(defun fn-bpcr-keyword-byte (byte table)
 (declare (xargs :guard t))
 (if (consp table)
  (let* ((row (car table)) (name (fn-cbor-ag-car row)))
   (if (and (consp name) (equal (car name) byte))
    (cons (cons (cdr name) (fn-cbor-ag-cdr row))
          (fn-bpcr-keyword-byte byte (cdr table)))
    (fn-bpcr-keyword-byte byte (cdr table)))) nil))

(defun fn-bpcr-keyword-terminal (table)
 (declare (xargs :guard t))
 (if (consp table)
  (if (null (fn-cbor-ag-car (car table)))
   (list t (fn-cbor-ag-cdr (car table)))
   (fn-bpcr-keyword-terminal (cdr table))) nil))

; tag/status/goals/values/phase/kind/remaining/number/work/out/offset.
(defun fn-bpcr-make (status goals values phase kind remaining number work out offset)
 (declare (xargs :guard t))
 (list :bp-checkpoint-reader status goals values phase kind remaining number work out offset))
(defun fn-bpcr-begin (depth)
 (declare (xargs :guard t))
 (fn-bpcr-make :decoding (list (nfix depth)) nil :tag nil 0 0 nil nil 0))
(defun fn-bpcr-action (job)
 (declare (xargs :guard t))
 (let ((goals (fn-bpn-nth 2 job)) (vals (fn-bpn-nth 3 job)))
  (cond ((not (equal (fn-bpn-nth 1 job) :decoding)) :settled)
        ((equal (fn-bpn-nth 4 job) :reverse) :reverse)
        ((not (equal (fn-bpn-nth 4 job) :tag)) :read)
        ((not (consp goals)) (if (and (consp vals) (null (cdr vals))) :done :refuse))
        ((equal (car goals) :pair) :combine)
        ((posp (car goals)) :read)
        (t :refuse))))
(defun fn-bpcr-refuse (job reason offset)
 (declare (xargs :guard t))
 (fn-bpcr-make :refused (fn-bpn-nth 2 job) (fn-bpn-nth 3 job)
  reason nil 0 0 (fn-bpn-nth 8 job) (fn-bpn-nth 9 job) offset))
(defun fn-bpcr-leaf (job value offset)
 (declare (xargs :guard t))
 (fn-bpcr-make :decoding (fn-cbor-ag-cdr (fn-bpn-nth 2 job))
  (cons value (fn-bpn-nth 3 job)) :tag nil 0 0 nil nil offset))

; Result = (next-job consumed-octets). A pure combine/reverse/final turn
; consumes no input. A read turn consumes exactly one caller-supplied octet.
(defun fn-bpcr-decode-tick (job byte)
 (declare (xargs :guard (fn-cbor-octetp byte)))
 (let* ((action (fn-bpcr-action job)) (goals (fn-bpn-nth 2 job))
        (vals (fn-bpn-nth 3 job)) (offset (nfix (fn-bpn-nth 10 job)))
        (phase (fn-bpn-nth 4 job)) (kind (fn-bpn-nth 5 job))
        (remaining (nfix (fn-bpn-nth 6 job))) (work (fn-bpn-nth 8 job)))
  (cond
   ((equal action :settled) (list job 0))
   ((equal action :refuse) (list (fn-bpcr-refuse job :depth offset) 0))
   ((equal action :done)
    (list (fn-bpcr-make :done goals vals :done nil 0 0 nil nil offset) 0))
   ((equal action :combine)
    (if (and (consp vals) (consp (cdr vals)))
     (list (fn-bpcr-make :decoding (cdr goals)
       (cons (cons (cadr vals) (car vals)) (cddr vals))
       :tag nil 0 0 nil nil offset) 0)
     (list (fn-bpcr-refuse job :pair-stack offset) 0)))
   ((equal action :reverse)
    (if (consp work)
     (list (fn-bpcr-make :decoding goals vals :reverse kind 0 0
       (cdr work) (cons (car work) (fn-bpn-nth 9 job)) offset) 0)
     (list (fn-bpcr-leaf job (fn-bpn-nth 9 job) offset) 0)))
   ((equal phase :tag)
    (cond ((equal byte 0) (list (fn-bpcr-leaf job nil (1+ offset)) 1))
          ((equal byte 10)
           (list (fn-bpcr-make :decoding
             (cons (1- (nfix (car goals)))
              (cons (1- (nfix (car goals))) (cons :pair (cdr goals))))
             vals :tag nil 0 0 nil nil (1+ offset)) 1))
          ((member-equal byte '(2 5 9))
           (list (fn-bpcr-make :decoding goals vals :word byte 8 0 nil nil (1+ offset)) 1))
          (t (list (fn-bpcr-refuse job :unsupported-leaf (1+ offset)) 1))))
   ((equal phase :word)
    (let ((number (+ (* 256 (nfix (fn-bpn-nth 7 job))) byte)))
     (if (> remaining 1)
      (list (fn-bpcr-make :decoding goals vals :word kind (1- remaining)
         number nil nil (1+ offset)) 1)
      (cond ((equal kind 5) (list (fn-bpcr-leaf job number (1+ offset)) 1))
            ((equal kind 2)
             (if (and (posp number) (<= number *fn-bpcr-max-name*))
              (list (fn-bpcr-make :decoding goals vals :keyword kind number 0
                *fn-bpcr-keywords* nil (1+ offset)) 1)
              (list (fn-bpcr-refuse job :unknown-keyword (1+ offset)) 1)))
            ((equal kind 9)
             (if (zp number) (list (fn-bpcr-leaf job nil (1+ offset)) 1)
              (list (fn-bpcr-make :decoding goals vals :octets kind number 0 nil nil (1+ offset)) 1)))
            (t (list (fn-bpcr-refuse job :word-kind (1+ offset)) 1))))))
   ((equal phase :keyword)
    (let ((next (fn-bpcr-keyword-byte byte work)))
     (cond ((not (consp next)) (list (fn-bpcr-refuse job :unknown-keyword (1+ offset)) 1))
           ((> remaining 1)
            (list (fn-bpcr-make :decoding goals vals :keyword kind (1- remaining)
             0 next nil (1+ offset)) 1))
           ((consp (fn-bpcr-keyword-terminal next))
            (list (fn-bpcr-leaf job (fn-bpn-nth 1 (fn-bpcr-keyword-terminal next)) (1+ offset)) 1))
           (t (list (fn-bpcr-refuse job :unknown-keyword (1+ offset)) 1)))))
   ((equal phase :octets)
    (list (fn-bpcr-make :decoding goals vals
      (if (> remaining 1) :octets :reverse) kind
      (if (> remaining 1) (1- remaining) 0) 0
      (cons byte work) nil (1+ offset)) 1))
   (t (list (fn-bpcr-refuse job :decoder-phase offset) 0)))))

; Q bounds all read and constructor actions, including list reversal.
; Residual input is shared, and a missing byte yields without consuming it.
(defun fn-bpcr-run (job input quantum)
 (declare (xargs :guard (and (fn-cbor-octet-listp input) (natp quantum))
                 :verify-guards nil :measure (nfix quantum)))
 (let ((action (fn-bpcr-action job)))
  (if (or (zp quantum) (equal action :settled)
          (and (equal action :read) (not (consp input))))
   (list job input 0 0)
   (let* ((tick (fn-bpcr-decode-tick job (if (equal action :read) (car input) 0)))
          (consumed (fn-bpn-nth 1 tick))
          (rest (if (equal consumed 1) (fn-cbor-ag-cdr input) input))
          (answer (fn-bpcr-run (fn-bpn-nth 0 tick) rest (1- quantum))))
    (list (fn-bpn-nth 0 answer) (fn-bpn-nth 1 answer)
          (1+ (fn-bpn-nth 2 answer))
          (+ consumed (fn-bpn-nth 3 answer)))))))

(local (defthm fn-bpcr-decode-tick-consumed-by-definition
 (or (equal (nth 1 (fn-bpcr-decode-tick job byte)) 0)
     (equal (nth 1 (fn-bpcr-decode-tick job byte)) 1))
 :hints (("Goal" :in-theory (e/d (fn-bpcr-decode-tick)
  (fn-bpcr-make fn-bpcr-action fn-bpcr-refuse fn-bpcr-leaf
   fn-bpcr-keyword-byte))))))

(local (defthm fn-bpcr-decode-tick-count-type-by-definition
 (natp (nth 1 (fn-bpcr-decode-tick job byte)))
 :hints (("Goal" :use fn-bpcr-decode-tick-consumed-by-definition
 :in-theory (e/d (natp) (fn-bpcr-decode-tick))))
 :rule-classes :type-prescription))
(local (defthm fn-bpcr-decode-tick-count-bound-by-definition
 (<= (nth 1 (fn-bpcr-decode-tick job byte)) 1)
 :hints (("Goal" :use fn-bpcr-decode-tick-consumed-by-definition
 :in-theory (disable fn-bpcr-decode-tick)))
 :rule-classes :linear))

(local (defthm fn-bpcr-run-count-types-by-definition
 (and (natp (nth 2 (fn-bpcr-run job input quantum)))
      (natp (nth 3 (fn-bpcr-run job input quantum))))
 :hints (("Goal" :induct (fn-bpcr-run job input quantum)
 :in-theory (e/d (fn-bpcr-run) (fn-bpcr-decode-tick fn-bpcr-action))))
 :rule-classes ((:type-prescription :corollary
  (natp (nth 2 (fn-bpcr-run job input quantum))))
 (:type-prescription :corollary
  (natp (nth 3 (fn-bpcr-run job input quantum)))))))

(defthm fn-bpcr-run-bounds-read-and-constructor-turns
 (implies (natp quantum)
  (and (natp (fn-bpn-nth 2 (fn-bpcr-run job input quantum)))
       (natp (fn-bpn-nth 3 (fn-bpcr-run job input quantum)))
       (<= (fn-bpn-nth 3 (fn-bpcr-run job input quantum))
           (fn-bpn-nth 2 (fn-bpcr-run job input quantum)))
       (<= (fn-bpn-nth 2 (fn-bpcr-run job input quantum)) quantum)))
 :hints (("Goal" :induct (fn-bpcr-run job input quantum)
  :in-theory (e/d (fn-bpcr-run)
   (fn-bpcr-decode-tick fn-bpcr-action fn-bpcr-keyword-byte))))
 :rule-classes nil)

(verify-guards fn-bpcr-run
 :hints (("Goal" :in-theory (disable fn-bpcr-decode-tick fn-bpcr-action
                                     fn-bpcr-keyword-byte))))

; Logical trajectory measure only: the served quantum never scans its jobs.
(defun fn-bpcr-measure (job input)
 (declare (xargs :guard t))
 (+ (* 3 (len input)) (len (fn-bpn-nth 2 job))
    (if (member-equal (fn-bpn-nth 4 job) '(:octets :reverse))
        (len (fn-bpn-nth 8 job)) 0)
    (if (equal (fn-bpn-nth 4 job) :reverse) 1 0)))

(defthm fn-bpcr-decode-tick-progress
 (let* ((action (fn-bpcr-action job))
        (tick (fn-bpcr-decode-tick job (if (equal action :read) (car input) 0)))
        (next (fn-bpn-nth 0 tick))
        (rest (if (equal (fn-bpn-nth 1 tick) 1) (fn-cbor-ag-cdr input) input)))
  (implies (and (equal (fn-bpn-nth 1 job) :decoding)
                (or (not (equal action :read)) (consp input))
                (equal (fn-bpn-nth 1 next) :decoding))
   (< (fn-bpcr-measure next rest) (fn-bpcr-measure job input))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpcr-decode-tick fn-bpcr-action fn-bpcr-measure
                   fn-bpcr-make fn-bpcr-leaf fn-bpcr-refuse)
                  (fn-bpcr-keyword-byte fn-bpcr-keyword-terminal))))
 :rule-classes nil)

(local (defthm fn-bpcr-decoding-result-had-live-source-by-definition
 (implies (equal (fn-bpn-nth 1 (fn-bpn-nth 0 (fn-bpcr-decode-tick job byte))) :decoding)
          (equal (fn-bpn-nth 1 job) :decoding))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpcr-decode-tick fn-bpcr-action fn-bpcr-make
                   fn-bpcr-leaf fn-bpcr-refuse)
                  (fn-bpcr-keyword-byte fn-bpcr-keyword-terminal))))))

; The source-status premise was removed only after this weakened proof.
(defthm fn-bpcr-decode-step-progress
 (let* ((action (fn-bpcr-action job))
        (tick (fn-bpcr-decode-tick job (if (equal action :read) (car input) 0)))
        (next (fn-bpn-nth 0 tick))
        (rest (if (equal (fn-bpn-nth 1 tick) 1) (fn-cbor-ag-cdr input) input)))
  (implies (and (or (not (equal action :read)) (consp input))
                (equal (fn-bpn-nth 1 next) :decoding))
   (< (fn-bpcr-measure next rest) (fn-bpcr-measure job input))))
 :hints (("Goal"
  :use ((:instance fn-bpcr-decode-tick-progress)
        (:instance fn-bpcr-decoding-result-had-live-source-by-definition
         (byte (if (equal (fn-bpcr-action job) :read) (car input) 0))))
  :in-theory (theory 'minimal-theory)))
 :rule-classes nil)

; Non-executable logical endpoint. Served code calls only FN-BPCR-RUN.
(defun-nx fn-bpcr-complete (job input)
 (declare (xargs :verify-guards nil :measure (fn-bpcr-measure job input)
  :hints (("Goal" :use fn-bpcr-decode-step-progress
   :in-theory (disable fn-bpcr-decode-tick fn-bpcr-action fn-bpcr-measure)))))
 (let ((action (fn-bpcr-action job)))
  (cond ((not (equal (fn-bpn-nth 1 job) :decoding))
         (list (fn-bpn-nth 1 job) job input))
        ((and (equal action :read) (not (consp input)))
         (list :need-input job input))
        (t (let* ((tick (fn-bpcr-decode-tick job
                          (if (equal action :read) (car input) 0)))
                  (next (fn-bpn-nth 0 tick))
                  (rest (if (equal (fn-bpn-nth 1 tick) 1)
                            (fn-cbor-ag-cdr input) input)))
             (if (equal (fn-bpn-nth 1 next) :decoding)
              (fn-bpcr-complete next rest)
              (list (fn-bpn-nth 1 next) next rest)))))))

(local (defthm fn-bpcr-settled-action-by-definition
 (equal (equal (fn-bpcr-action job) :settled)
        (not (equal (fn-bpn-nth 1 job) :decoding)))
 :hints (("Goal" :in-theory (enable fn-bpcr-action)))))

; Every finite scheduler quantum preserves the exact logical continuation.
(defthm fn-bpcr-run-preserves-completion
 (equal (fn-bpcr-complete (fn-bpn-nth 0 (fn-bpcr-run job input quantum))
                          (fn-bpn-nth 1 (fn-bpcr-run job input quantum)))
        (fn-bpcr-complete job input))
 :hints (("Goal" :induct (fn-bpcr-run job input quantum)
  :in-theory (e/d (fn-bpcr-run fn-bpcr-complete)
    (fn-bpcr-decode-tick fn-bpcr-action fn-bpcr-measure))))
 :rule-classes nil)
