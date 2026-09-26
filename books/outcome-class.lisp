; The fn-wide outcome classes and their exit codes (PRF-143, HST-009;
; specs/host.md "CLI exit codes").
;
; Every native fn command exits with exit(f, x) = code(classify(f, x)): each
; verb family classifies its own outcome into one of the seven classes below,
; and the one map *fn-outcome-codes* gives the code.  The classes are the
; questions a caller must ask next, not the verb families: every accepted
; command shares 0 and every known refusal, whatever its reason, shares 1.
; A reason is printed, never given its own exit code.
;
;   :accepted       0  success, or already satisfied
;   :refused        1  a known refusal with a stable reason (named on output)
;   :fenced         3  indeterminate local durable authority: a publication's
;                      outcome is unknown; recover before further mutation
;   :fault          4  the host could not carry out the operation
;   :usage          5  the invocation itself is wrong or unsupported
;   :interrupted    6  a connection lost after it existed; the local durable
;                      work is retained and re-offered under its identity
;   :not-connected  7  no connection was established; nothing left the node
;
; The table is the native executable's.  An external client (tools/fn_client.py
; and every NNTP client) that lost a reply is uncertain about the SERVER's
; state, not about a local Store; its outcome record carries that scope.

(in-package "ACL2")

(defconst *fn-outcome-codes*
  '((:accepted . 0) (:refused . 1) (:fenced . 3) (:fault . 4)
    (:usage . 5) (:interrupted . 6) (:not-connected . 7)))

(defconst *fn-outcome-classes*
  '(:accepted :refused :fenced :fault :usage :interrupted :not-connected))

(defun fn-outcome-classp (x)
  (declare (xargs :guard t))
  (if (member-equal x *fn-outcome-classes*) t nil))

; The code of a class.  A word that is no class is answered with the fenced
; code (fail closed toward recovery); every family's classify function
; returns a class (fn-*-outcome-class-is-a-class below and in each family),
; so that arm is unreachable-in-composition.
(defun fn-outcome-code (class)
  (declare (xargs :guard t))
  (let ((pair (assoc-equal class *fn-outcome-codes*)))
    (if (consp pair) (cdr pair) 3)))

(defun fn-outcome-codep (code)
  (declare (xargs :guard t))
  (if (member-equal code (strip-cdrs *fn-outcome-codes*)) t nil))

; -----------------------------------------------------------------------------
; The shared classifiers.

; The status words the store, operator and control families answer with
; (:accepted :refused :uncertain :fault :usage).  An uncertain publication is
; the fence; anything that is not one of the words is a fault.
(defun fn-outcome-of-status (status)
  (declare (xargs :guard t))
  (case status
    (:accepted :accepted)
    (:refused :refused)
    (:uncertain :fenced)
    (:usage :usage)
    (otherwise :fault)))

; The host condition that ended a native command (host/native/io.lisp
; fnn-exit-code-for observes its type and names it with one of these words):
; fnn-store-indeterminate :indeterminate, fnn-usage-error :usage, any other
; fnn-store-error (a refusal, an I/O refusal) :refusal, and every fault
; (fnn-store-fault, fnn-input-overbound, fnn-os-error, anything else) :fault.
(defun fn-outcome-of-host-condition (kind)
  (declare (xargs :guard t))
  (case kind
    (:indeterminate :fenced)
    (:usage :usage)
    (:refusal :refused)
    (otherwise :fault)))

(defun fn-outcome-host-condition-exit-code (kind)
  (declare (xargs :guard t))
  (fn-outcome-code (fn-outcome-of-host-condition kind)))

; -----------------------------------------------------------------------------
; Theorems.

(defthm fn-outcome-code-is-an-outcome-code
  (fn-outcome-codep (fn-outcome-code class)))

(defthm fn-outcome-of-status-is-a-class
  (fn-outcome-classp (fn-outcome-of-status status)))

(defthm fn-outcome-of-host-condition-is-a-class
  (fn-outcome-classp (fn-outcome-of-host-condition kind)))

; KEYSTONE 1 (disjoint).  Seven classes, seven codes: different classes never
; share a code, so a wrapper script reads the class from the number alone.
(defthm fn-outcome-code-separates-the-classes
  (implies (and (fn-outcome-classp c1)
                (fn-outcome-classp c2)
                (not (equal c1 c2)))
           (not (equal (fn-outcome-code c1) (fn-outcome-code c2)))))

; KEYSTONE 2 (fixed).  The code of each class is the number specs/host.md's
; table gives it, and the class a code names is unique: fn-outcome-code is a
; bijection from the seven classes onto (0 1 3 4 5 6 7).
(defthm fn-outcome-code-table-by-definition
  (equal (list (fn-outcome-code :accepted) (fn-outcome-code :refused)
               (fn-outcome-code :fenced) (fn-outcome-code :fault)
               (fn-outcome-code :usage) (fn-outcome-code :interrupted)
               (fn-outcome-code :not-connected))
         '(0 1 3 4 5 6 7)))

; KEYSTONE 3 (a fence is the only 3).  Over classes, the code is the fenced
; code exactly when the class is :fenced.
(defthm fn-outcome-code-is-fenced-iff-fenced
  (implies (fn-outcome-classp class)
           (equal (equal (fn-outcome-code class) (fn-outcome-code :fenced))
                  (equal class :fenced))))

; The shared status classifier never masks an uncertain publication and
; never makes anything else a fence.
(defthm fn-outcome-of-status-fences-iff-uncertain
  (equal (equal (fn-outcome-code (fn-outcome-of-status status)) 3)
         (equal status :uncertain)))

; The host's condition classification: exit 3 exactly for an indeterminate
; publication (host/native/io.lisp fnn-exit-code-for).
(defthm fn-outcome-host-condition-fences-iff-indeterminate
  (equal (equal (fn-outcome-host-condition-exit-code kind) 3)
         (equal kind :indeterminate)))
