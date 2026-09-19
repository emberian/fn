; Finite traces for the abstract composite node machine.
;
; This book is deliberately above the node transition book and below any host
; or storage adapter.  Events are fixed ACL2 data records.  The dispatcher
; rejects malformed/unknown records before selecting a node operation; it does
; not read or evaluate external Lisp forms.  Completion and recovery outcomes
; remain abstract observations supplied to the logical node.
;
; The dispatcher and the trace fold carry `fn-node-statep' as their guard,
; discharged by `fn-node-step-preserves-state'.

(in-package "ACL2")
(include-book "node-invariants")

(local (in-theory (enable fn-node-pending-matchesp fn-node-prepare
                          fn-node-complete fn-node-recover)))

; -----------------------------------------------------------------------------
; Explicit event grammar

; Events are:
;   (:prepare generation msgid payload groups obligation-id subject evidence charge)
;   (:complete txid generation :durable|:aborted|:indeterminate)
;   (:recover txid generation :committed|:absent)
;
; A structurally valid event may still be semantically refused by the node
; (for example, an unknown group, duplicate identity, stale completion, or an
; unaffordable archive obligation).  Structural validation is kept separate so
; the dispatcher never passes malformed fields to a transition.
(defun fn-node-completion-statusp (x)
  (declare (xargs :guard t))
  (or (equal x :durable)
      (equal x :aborted)
      (equal x :indeterminate)))

(defun fn-node-recovery-resultp (x)
  (declare (xargs :guard t))
  (or (equal x :committed)
      (equal x :absent)))

; Fixed-position accessors keep the event ABI explicit.  nth is applied only
; after the recognizer has established the required true list.
(defun fn-node-prepare-generation (event)
  (declare (xargs :guard (true-listp event))) (nth 1 event))
(defun fn-node-prepare-msgid (event)
  (declare (xargs :guard (true-listp event))) (nth 2 event))
(defun fn-node-prepare-payload (event)
  (declare (xargs :guard (true-listp event))) (nth 3 event))
(defun fn-node-prepare-groups (event)
  (declare (xargs :guard (true-listp event))) (nth 4 event))
(defun fn-node-prepare-obligation-id (event)
  (declare (xargs :guard (true-listp event))) (nth 5 event))
(defun fn-node-prepare-subject (event)
  (declare (xargs :guard (true-listp event))) (nth 6 event))
(defun fn-node-prepare-evidence (event)
  (declare (xargs :guard (true-listp event))) (nth 7 event))
(defun fn-node-prepare-charge (event)
  (declare (xargs :guard (true-listp event))) (nth 8 event))
(defun fn-node-complete-txid (event)
  (declare (xargs :guard (true-listp event))) (nth 1 event))
(defun fn-node-complete-generation (event)
  (declare (xargs :guard (true-listp event))) (nth 2 event))
(defun fn-node-complete-status (event)
  (declare (xargs :guard (true-listp event))) (nth 3 event))
(defun fn-node-recover-txid (event)
  (declare (xargs :guard (true-listp event))) (nth 1 event))
(defun fn-node-recover-generation (event)
  (declare (xargs :guard (true-listp event))) (nth 2 event))
(defun fn-node-recover-result (event)
  (declare (xargs :guard (true-listp event))) (nth 3 event))

(defun fn-node-prepare-eventp (event)
  (declare (xargs :guard t))
  (and (true-listp event)
       (equal (len event) 9)
       (equal (car event) :prepare)
       (natp (fn-node-prepare-generation event))
       (stringp (fn-node-prepare-msgid event))
       (fn-octet-listp (fn-node-prepare-payload event))
       (fn-string-listp (fn-node-prepare-groups event))
       (fn-no-duplicatesp (fn-node-prepare-groups event))
       (stringp (fn-node-prepare-obligation-id event))
       (stringp (fn-node-prepare-subject event))
       (stringp (fn-node-prepare-evidence event))
       (posp (fn-node-prepare-charge event))))

(defun fn-node-complete-eventp (event)
  (declare (xargs :guard t))
  (and (true-listp event)
       (equal (len event) 4)
       (equal (car event) :complete)
       (natp (fn-node-complete-txid event))
       (natp (fn-node-complete-generation event))
       (fn-node-completion-statusp (fn-node-complete-status event))))

(defun fn-node-recover-eventp (event)
  (declare (xargs :guard t))
  (and (true-listp event)
       (equal (len event) 4)
       (equal (car event) :recover)
       (natp (fn-node-recover-txid event))
       (natp (fn-node-recover-generation event))
       (fn-node-recovery-resultp (fn-node-recover-result event))))

(defun fn-node-eventp (event)
  (declare (xargs :guard t))
  (or (fn-node-prepare-eventp event)
      (fn-node-complete-eventp event)
      (fn-node-recover-eventp event)))

; -----------------------------------------------------------------------------
; Dispatcher and finite trace fold

(defun fn-node-step (s event)
  (declare (xargs :guard (fn-node-statep s)))
  (if (fn-node-prepare-eventp event)
      (fn-node-prepare s
                       (fn-node-prepare-generation event)
                       (fn-node-prepare-msgid event)
                       (fn-node-prepare-payload event)
                       (fn-node-prepare-groups event)
                       (fn-node-prepare-obligation-id event)
                       (fn-node-prepare-subject event)
                       (fn-node-prepare-evidence event)
                       (fn-node-prepare-charge event))
    (if (fn-node-complete-eventp event)
        (fn-node-complete s
                          (fn-node-complete-txid event)
                          (fn-node-complete-generation event)
                          (fn-node-complete-status event))
      (if (fn-node-recover-eventp event)
          (fn-node-recover s
                           (fn-node-recover-txid event)
                           (fn-node-recover-generation event)
                           (fn-node-recover-result event))
        s))))

; A `-by-definition' fact: the fall-through branch with its tests as
; hypothesis.  Not a registry event and not a rewrite rule.
(defthm fn-node-malformed-step-is-no-op
  (implies (not (fn-node-eventp event))
           (equal (fn-node-step s event) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-node-statep fn-node-prepare
                                      fn-node-complete fn-node-recover))))

(defthm fn-node-step-preserves-state
  (implies (fn-node-statep s)
           (fn-node-statep (fn-node-step s event)))
  :hints (("Goal" :in-theory (disable fn-node-statep fn-node-prepare
                                      fn-node-complete fn-node-recover
                                      fn-node-prepare-eventp
                                      fn-node-complete-eventp
                                      fn-node-recover-eventp))))

(defun fn-node-trace (s events)
  (declare (xargs :guard (fn-node-statep s)
                  :guard-hints (("Goal" :in-theory (disable fn-node-statep
                                                            fn-node-step)))))
  (if (consp events)
      (fn-node-trace (fn-node-step s (car events)) (cdr events))
    s))

; A list relation used for the trace theorem.  It records that every binding
; present before a trace remains present afterward.  fn-node-statep on the
; resulting state supplies the stronger article-membership, watermark, and
; archive-pin consistency for those bindings.
(defun fn-node-bindings-subsetp (old new)
  (declare (xargs :guard t))
  (if (consp old)
      (and (mbe :logic (member-equal (car old) new)
                :exec (fn-ag-member (car old) new))
           (fn-node-bindings-subsetp (cdr old) new))
    t))

(defthm fn-node-bindings-subsetp-cons
  (implies (fn-node-bindings-subsetp old new)
           (fn-node-bindings-subsetp old (cons x new)))
  :hints (("Goal" :induct (fn-node-bindings-subsetp old new))))

(defthm fn-node-bindings-subsetp-reflexive
  (fn-node-bindings-subsetp xs xs)
  :hints (("Goal" :induct (fn-node-bindings-subsetp xs xs))))

(defthm fn-node-bindings-subsetp-transitive
  (implies (and (fn-node-bindings-subsetp old middle)
                (fn-node-bindings-subsetp middle new))
           (fn-node-bindings-subsetp old new))
  :hints (("Goal" :induct (fn-node-bindings-subsetp old middle))))

; -----------------------------------------------------------------------------
; Arbitrary finite traces

(defthm fn-node-trace-preserves-state
  (implies (and (fn-node-statep s)
                (true-listp events))
           (fn-node-statep (fn-node-trace s events)))
  :hints (("Goal"
           :induct (fn-node-trace s events)
           :in-theory (disable fn-node-statep fn-node-step))))

; A prepare leaves the binding list unchanged.  A durable completion or
; committed recovery conses one new binding in front; abort, indeterminate,
; absent, stale, and refused operations leave existing bindings in place.
(defthm fn-node-prepare-preserves-old-bindings
  (implies (fn-node-bindings-subsetp old (fn-node-bindings s))
           (fn-node-bindings-subsetp
            old
            (fn-node-bindings
             (fn-node-prepare s generation msgid payload groups
                              obligation-id subject evidence charge))))
  :hints (("Goal" :in-theory (disable fn-node-prepare))))

(defthm fn-node-complete-preserves-old-bindings
  (implies (and (fn-node-statep s)
                (fn-node-bindings-subsetp old (fn-node-bindings s)))
           (fn-node-bindings-subsetp
            old
            (fn-node-bindings
             (fn-node-complete s txid generation completion-status))))
  :hints (("Goal" :in-theory (disable fn-node-statep))))

(defthm fn-node-recover-preserves-old-bindings
  (implies (and (fn-node-statep s)
                (fn-node-bindings-subsetp old (fn-node-bindings s)))
           (fn-node-bindings-subsetp
            old
            (fn-node-bindings
             (fn-node-recover s txid generation recovery-result))))
  :hints (("Goal" :in-theory (disable fn-node-statep))))

(defthm fn-node-step-preserves-old-bindings
  (implies (and (fn-node-statep s)
                (fn-node-bindings-subsetp old (fn-node-bindings s)))
           (fn-node-bindings-subsetp
            old (fn-node-bindings (fn-node-step s event))))
  :hints (("Goal" :in-theory (disable fn-node-statep fn-node-prepare
                                      fn-node-complete fn-node-recover
                                      fn-node-prepare-eventp
                                      fn-node-complete-eventp
                                      fn-node-recover-eventp))))

(defthm fn-node-trace-preserves-old-bindings-general
  (implies (and (fn-node-statep s)
                (true-listp events)
                (fn-node-bindings-subsetp old (fn-node-bindings s)))
           (fn-node-bindings-subsetp
            old
            (fn-node-bindings (fn-node-trace s events))))
  :hints (("Goal"
           :induct (fn-node-trace s events)
           :in-theory (disable fn-node-statep fn-node-step))))

(defthm fn-node-trace-preserves-old-bindings
  (implies (and (fn-node-statep s)
                (true-listp events))
           (fn-node-bindings-subsetp
            (fn-node-bindings s)
            (fn-node-bindings (fn-node-trace s events))))
  :hints (("Goal"
           :use (:instance fn-node-trace-preserves-old-bindings-general
                           (old (fn-node-bindings s)))
           :in-theory (disable fn-node-statep fn-node-trace
                               fn-node-trace-preserves-old-bindings-general))))

; -----------------------------------------------------------------------------
; Export.  Keystones stay enabled: `fn-node-step-preserves-state',
; `fn-node-trace-preserves-state' and `fn-node-trace-preserves-old-bindings'.
; The dispatcher is withdrawn; the event grammar, the fold and the binding
; relation stay enabled as list vocabulary.
(deftheory fn-node-traces-vocabulary
  '(fn-node-prepare-preserves-old-bindings
    fn-node-complete-preserves-old-bindings
    fn-node-recover-preserves-old-bindings
    fn-node-step-preserves-old-bindings
    fn-node-trace-preserves-old-bindings-general))
(in-theory (disable fn-node-traces-vocabulary
                    (:d fn-node-step)))
