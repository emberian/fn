; store-sweep.lisp -- collecting the staging names an interrupted
; publication left behind.
;
; The deploy gate of 2026-09-20 (planning/evidence/deploy-cce4b11-2026-09-20.md,
; finding 5) injected an uncertain publication and then recovered twice: the
; staging file the interrupted publication had created was still there after
; both recoveries, reported as `staging-orphans=1' and never collected.  That
; is a leak, and the decision about which names may be deleted is a storage
; decision, so it is made here and not in Python and not in the owner.
;
; The store kernel does not model the staging directory: a staging name is a
; host name that exists only between fn-sf-prepare-record and the link into
; the final namespace.  So the sweep takes what the host observed in the
; staging directory and what the live process still holds for a publication
; it has not resolved, and decides which observed names may go.  The kernel
; entries it reads -- fn-sf-phase and fn-sf-record-candidate, through the
; store-node accessors -- are the gate: while the kernel holds an unresolved
; publication, nothing is swept at all.
;
; The store state is returned unchanged.  Sweeping is not a durable-history
; event; it removes nothing the history names, and that is the point.

(in-package "ACL2")

(include-book "store-node-traces")

(local (in-theory (enable fn-sn-statep fn-snt-relation)))

; -----------------------------------------------------------------------------
; Names
;
; A staging name is an octet list beginning ".stage-"; the host builds one
; per publication (tools/run_store.py, Store._stage_path).  A final-namespace
; name is the twenty decimal digits of a transaction sequence
; (tools/run_store.py, SEQ_NAME).  The two namespaces are disjoint by their
; first octet, which is what keeps a completed publication's file out of
; every removal list below.

(defconst *fn-sn-staging-prefix* '(46 115 116 97 103 101 45))

(defun fn-sn-octet-prefixp (prefix name)
  (declare (xargs :guard t))
  (if (consp prefix)
      (and (consp name)
           (equal (car prefix) (car name))
           (fn-sn-octet-prefixp (cdr prefix) (cdr name)))
    t))

(defun fn-sn-staging-namep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (fn-sn-octet-prefixp *fn-sn-staging-prefix* x)))

(defun fn-sn-digit-octet-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (natp (car x))
           (<= 48 (car x))
           (<= (car x) 57)
           (fn-sn-digit-octet-listp (cdr x)))
    (null x)))

; The name a completed publication's record occupies: twenty decimal digits
; (tools/run_store.py, SEQ_NAME, and the sequence check in durable_records).
(defun fn-sn-final-namespace-namep (x)
  (declare (xargs :guard t))
  (and (fn-sn-digit-octet-listp x)
       (equal (len x) 20)))

; -----------------------------------------------------------------------------
; The sweep

; `observed' is what the host enumerated in the staging directory; `held' is
; the staging names the live process still has open for a publication it has
; not resolved.  A name is removable when it is in the staging namespace and
; the process does not hold it.  Anything else in the directory is left
; alone and reported, exactly as before.
; Total membership: member-equal's guard would put a true-listp obligation on
; a list the host supplies, and the sweep must be total on anything it is
; handed.
(defun fn-sn-name-memberp (x names)
  (declare (xargs :guard t))
  (if (consp names)
      (or (equal x (car names))
          (fn-sn-name-memberp x (cdr names)))
    nil))

(defun fn-sn-sweep-removals (observed held)
  (declare (xargs :guard t))
  (if (consp observed)
      (if (and (fn-sn-staging-namep (car observed))
               (not (fn-sn-name-memberp (car observed) held)))
          (cons (car observed) (fn-sn-sweep-removals (cdr observed) held))
        (fn-sn-sweep-removals (cdr observed) held))
    nil))

; The kernel gate.  :ready is the phase at which no file operation is
; outstanding and no record is staged; fn-sf-record-candidate is the record
; a publication in flight has staged.  fn-own-take-submission reads the same
; phase before it lets a submission into the durable path (books/owner.lisp).
(defun fn-sn-sweep-enabledp (s)
  (declare (xargs :guard t))
  (and (equal (fn-sf-phase (fn-sn-files s)) :ready)
       (null (fn-sf-record-candidate (fn-sn-files s)))))

; (removals . store).  The store is returned as it was.
(defun fn-sn-sweep-staging (s observed held)
  (declare (xargs :guard t))
  (cons (if (fn-sn-sweep-enabledp s)
            (fn-sn-sweep-removals observed held)
          nil)
        s))

; -----------------------------------------------------------------------------
; What the sweep may remove
;
; The keystone: every name the sweep hands the host was enumerated in the
; staging directory, is in the staging namespace, and is not one the live
; process holds.  The contrapositive is the safety property -- a held name is
; never removed -- and the disjointness of the two namespaces below is the
; other half: no name a completed publication occupies is ever removed.

(defthm fn-sn-sweep-removes-only-unheld-staging-names
  (implies (member-equal name (car (fn-sn-sweep-staging s observed held)))
           (and (member-equal name observed)
                (fn-sn-staging-namep name)
                (not (fn-sn-name-memberp name held))))
  :hints (("Goal" :induct (fn-sn-sweep-removals observed held))))

(defthm fn-sn-final-namespace-name-is-not-a-staging-name
  (implies (fn-sn-final-namespace-namep name)
           (not (fn-sn-staging-namep name))))

; A completed publication's record occupies a final-namespace name, so the
; sweep can never remove it, whatever the host enumerated.
(defthm fn-sn-sweep-never-removes-a-final-namespace-name
  (implies (fn-sn-final-namespace-namep name)
           (not (member-equal name (car (fn-sn-sweep-staging s observed held)))))
  :hints (("Goal"
           :use ((:instance fn-sn-sweep-removes-only-unheld-staging-names))
           :in-theory (disable fn-sn-sweep-removes-only-unheld-staging-names
                               fn-sn-sweep-staging fn-sn-staging-namep
                               fn-sn-final-namespace-namep))))

; -by-definition: the gate is the `if' of fn-sn-sweep-staging.  Cited by
; :use, never rewritten with.
(defthm fn-sn-sweep-refuses-while-a-publication-is-unresolved
  (implies (not (fn-sn-sweep-enabledp s))
           (equal (car (fn-sn-sweep-staging s observed held)) nil))
  :rule-classes nil)

; The store is untouched.  -by-definition; the two preservation facts below
; are its corollaries and are cited, not registered as proof events.
(defthm fn-sn-sweep-staging-keeps-the-store
  (equal (cdr (fn-sn-sweep-staging s observed held)) s)
  :rule-classes nil)

(defthm fn-sn-sweep-staging-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (cdr (fn-sn-sweep-staging s observed held))))
  :rule-classes nil
  :hints (("Goal" :use fn-sn-sweep-staging-keeps-the-store
           :in-theory (disable fn-sn-sweep-staging fn-sn-statep))))

; The sweep returns the store unchanged, so the index is carried trivially.
; -by-definition, a corollary of fn-sn-sweep-staging-keeps-the-store; cited,
; not registered as a proof event.  It is here because without it the claim
; that fn-sn-indexedp holds of every state the host installs would have a
; hole at the sweep (D21).
(defthm fn-sn-sweep-staging-preserves-indexedp-by-definition
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (cdr (fn-sn-sweep-staging s observed held))))
  :rule-classes nil
  :hints (("Goal" :use fn-sn-sweep-staging-keeps-the-store
           :in-theory (disable fn-sn-sweep-staging fn-sn-indexedp))))

(defthm fn-sn-sweep-staging-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (cdr (fn-sn-sweep-staging s observed held))))
  :rule-classes nil
  :hints (("Goal" :use fn-sn-sweep-staging-keeps-the-store
           :in-theory (disable fn-sn-sweep-staging fn-snt-relation))))

; -----------------------------------------------------------------------------
; Export theory.  The list-recursive vocabulary the proofs induct on stays
; enabled (fn-sn-octet-prefixp, fn-sn-digit-octet-listp,
; fn-sn-sweep-removals); the predicates and the event are withdrawn.

(deftheory fn-sn-sweep-vocabulary
  '(fn-sn-staging-namep fn-sn-final-namespace-namep fn-sn-sweep-enabledp
    fn-sn-sweep-staging))

(in-theory (disable fn-sn-sweep-vocabulary))
