; fn: the owner's process record -- the per-process state the host installs
; into the owner value, in one field of `fn-own' (books/owner.lisp, field
; `proc', the sixteenth).
;
; It exists because two host facts were state globals beside the owner and
; had to be owner state: whether the operator opted into live reclaim
; (`[resources] reclaim_live', installed once per run by
; host/owner-host.lisp fn-owner-connection-budget), and the checkpoint
; publication's capture serial (RL-02, books/owner-publication-lifecycle.lisp
; fn-opl-next-serial: the capture's identity, which must stay MONOTONE for the
; life of the process, across a second owner install included).  The record
; carries both and has room for the other fn-owner-sco-* side channels without
; another change of the owner's arity.
;
;   (reclaim-live sco-serial)
;
;   reclaim-live  the operator's opt-in, as installed (the host reads it
;                 through a boolean: (and x t));
;   sco-serial    the serial of the newest capture (a natural; 0 before any).
;
; The record is not part of any served decision: every owner step copies it
; (books/owner.lisp, the field is carried like the node secret) and only the
; host writes it, through fn-own-with-proc.  A recovery builds a fresh owner
; (fn-own-start: the initial record) and the installing wrapper carries the
; PRIOR owner's record into it (books/owner-recovery-retain.lisp
; fn-owner-install-extended).
;
; This book owns the prefix `fn-oproc-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "acceptance-alloc")

(defun fn-oproc-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)))
(defun fn-oproc-reclaim-live (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-oproc-sco-serial (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-oproc-make (reclaim-live sco-serial)
  (declare (xargs :guard t))
  (list reclaim-live sco-serial))

; Before any install: no opt-in, no capture.
(defun fn-oproc-initial ()
  (declare (xargs :guard t))
  (fn-oproc-make nil 0))

(defthm fn-oproc-shapep-of-fn-oproc-make
  (fn-oproc-shapep (fn-oproc-make reclaim-live sco-serial)))
(defthm fn-oproc-reclaim-live-of-fn-oproc-make
  (equal (fn-oproc-reclaim-live (fn-oproc-make reclaim-live sco-serial))
         reclaim-live))
(defthm fn-oproc-sco-serial-of-fn-oproc-make
  (equal (fn-oproc-sco-serial (fn-oproc-make reclaim-live sco-serial))
         sco-serial))
(defthm fn-oproc-shapep-forward-shape
  (implies (fn-oproc-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-oproc-accessors-forward-consp
  (and (implies (fn-oproc-reclaim-live x) (consp x))
       (implies (fn-oproc-sco-serial x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-oproc-reclaim-live x) (consp x))
                                    :trigger-terms ((fn-oproc-reclaim-live x)))
                 (:forward-chaining :corollary (implies (fn-oproc-sco-serial x) (consp x))
                                    :trigger-terms ((fn-oproc-sco-serial x)))))

; The ground facts of the initial record (the host's total readers answer
; them for an owner that was never installed).
(defthm fn-oproc-initial-is-shape
  (fn-oproc-shapep (fn-oproc-initial)))
(defthm fn-oproc-reclaim-live-of-initial
  (equal (fn-oproc-reclaim-live (fn-oproc-initial)) nil))
(defthm fn-oproc-sco-serial-of-initial
  (equal (fn-oproc-sco-serial (fn-oproc-initial)) 0))

; The writers: each replaces one member and keeps the other.
(defun fn-oproc-with-reclaim-live (r live)
  (declare (xargs :guard t))
  (fn-oproc-make live (fn-oproc-sco-serial r)))
(defun fn-oproc-with-sco-serial (r serial)
  (declare (xargs :guard t))
  (fn-oproc-make (fn-oproc-reclaim-live r) serial))

(defthm fn-oproc-reclaim-live-of-with-reclaim-live
  (equal (fn-oproc-reclaim-live (fn-oproc-with-reclaim-live r live)) live))
(defthm fn-oproc-sco-serial-of-with-reclaim-live
  (equal (fn-oproc-sco-serial (fn-oproc-with-reclaim-live r live))
         (fn-oproc-sco-serial r)))
(defthm fn-oproc-sco-serial-of-with-sco-serial
  (equal (fn-oproc-sco-serial (fn-oproc-with-sco-serial r serial)) serial))
(defthm fn-oproc-reclaim-live-of-with-sco-serial
  (equal (fn-oproc-reclaim-live (fn-oproc-with-sco-serial r serial))
         (fn-oproc-reclaim-live r)))
(defthm fn-oproc-shapep-of-with-reclaim-live
  (fn-oproc-shapep (fn-oproc-with-reclaim-live r live)))
(defthm fn-oproc-shapep-of-with-sco-serial
  (fn-oproc-shapep (fn-oproc-with-sco-serial r serial)))

(in-theory (disable (:d fn-oproc-shapep) (:d fn-oproc-reclaim-live) (:d fn-oproc-sco-serial)
                    (:d fn-oproc-make) (:d fn-oproc-initial)
                    (:d fn-oproc-with-reclaim-live) (:d fn-oproc-with-sco-serial)))
