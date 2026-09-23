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
; A staging name is an octet list beginning with one of the prefixes below.
; Each is the prefix of the stage one host program creates in the staging
; directory and then commits by a rename or a link OUT of it; none is ever
; read back by any recovery reader:
;
;   .stage-       record publication (fn-bs-record-program; io.lisp fnn-publish)
;                 and administrative publication (admin.lisp fnn-admin-stage-path)
;   .allocation-  the allocator (fn-bs-frontier-program; io.lisp
;                 fnn-advance-frontier), committed by rename(2) onto
;                 allocation-frontier.json
;   .init-        initialization (fn-bs-init-file-steps; io.lisp
;                 fnn-publish-initial-file), committed by link(2)
;   .anchor-      anchor.lisp fnn-anchor-publish, committed by rename(2)
;   .checkpoint-  checkpoint.lisp, committed by link(2)
;   .selection-   checkpoint.lisp selection marker, committed by rename(2)
;   .pack-        checkpoint.lisp pack generation and its .pack-selection-
;                 marker, committed by link(2) and rename(2)
;
; The decision (finding F2 of
; planning/evidence/campaign-dabebb84-2026-09-22.md): a staged file that was
; never renamed or linked is by construction not authority -- the rename or
; the link IS the commit -- and one that was is a second name for an inode
; the final namespace already holds.  Either way unlinking the staging name
; changes nothing any reader of durable state reads.  The byte-level
; statement of that is fn-bs-staging-unlink-keeps-relation-and-scan
; (books/byte-store-keystones.lisp): an unlink in :staging leaves the byte
; relation to the SAME kernel state and the recovery scan unchanged.  Until
; 2026-09-22 only .stage- was listed here; 65 process deaths at
; frontier-staged-durable left 65 .allocation- files and the 66th open
; faulted at the observation bound.
;
; A final-namespace name is the twenty decimal digits of a transaction
; sequence (tools/run_store.py, SEQ_NAME).  Every staging prefix begins with
; `.' (46) and no decimal digit is 46, which is what keeps a completed
; publication's file out of every removal list below.

(defconst *fn-sn-staging-prefix* '(46 115 116 97 103 101 45))

(defconst *fn-sn-staging-prefixes*
  '((46 115 116 97 103 101 45)                              ; .stage-
    (46 97 108 108 111 99 97 116 105 111 110 45)            ; .allocation-
    (46 105 110 105 116 45)                                 ; .init-
    (46 97 110 99 104 111 114 45)                           ; .anchor-
    (46 99 104 101 99 107 112 111 105 110 116 45)          ; .checkpoint-
    (46 115 101 108 101 99 116 105 111 110 45)              ; .selection-
    (46 112 97 99 107 45)))                                 ; .pack-

; The host's staging observation is bounded before it builds an ACL2 input
; list: one enumeration retains at most this many names and reports whether
; the directory held another.  It bounds one ROUND of the sweep, not the
; directory: fn-sn-sweep-round below decides whether to go round again, and
; fn-sn-sweep-rounds-collect-every-orphan says a directory of N orphans, for
; every N, ends empty.
(defconst *fn-sn-max-staging-observation* 64)

(defun fn-sn-staging-observation-limit ()
  (declare (xargs :guard t))
  *fn-sn-max-staging-observation*)

(defthm fn-sn-staging-observation-limit-is-positive
  (< 0 (fn-sn-staging-observation-limit)))

(defun fn-sn-octet-prefixp (prefix name)
  (declare (xargs :guard t))
  (if (consp prefix)
      (and (consp name)
           (equal (car prefix) (car name))
           (fn-sn-octet-prefixp (cdr prefix) (cdr name)))
    t))

(defun fn-sn-some-prefixp (prefixes name)
  (declare (xargs :guard t))
  (if (consp prefixes)
      (or (fn-sn-octet-prefixp (car prefixes) name)
          (fn-sn-some-prefixp (cdr prefixes) name))
    nil))

(defun fn-sn-staging-namep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (fn-sn-some-prefixp *fn-sn-staging-prefixes* x)
       t))

; Closed from here on: no proof below needs to know which prefixes there
; are, and with seven of them an open recognizer multiplies every case split
; of the list inductions by the prefix enumeration (the keystone below took
; 330 s on persvati with it open, run-20260922T223519Z-2b86).
(local (in-theory (disable fn-sn-staging-namep)))

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
           (not (fn-sn-staging-namep name)))
  :hints (("Goal" :in-theory (enable fn-sn-staging-namep))))

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

;-----------------------------------------------------------------------------
; Rounds: the observation bound is per round, never per directory
;
; The host enumerates at most (fn-sn-staging-observation-limit) names and
; reports OVERP, whether the directory held a further entry.  It asks
; fn-sn-sweep-round what to do with that one observation, unlinks the
; removals, and goes round again while the answer is :again.  The host line
; is fnn-sweep-staging (host/native/io.lisp), through
; fn-store-sn-sweep-round (host/store-node-host.lisp).
;
;   :done     the directory fit in the observation; the removals are this
;             round's and nothing is left for another round.
;   :again    the directory did not fit and this round removes at least one
;             name, so the next observation is of a strictly smaller
;             directory.
;   :refused  the directory did not fit and nothing in this observation may
;             be removed.  Another round would observe the same names.  That
;             is a refusal (exit 1), never a fault: nothing is uncertain and
;             nothing was damaged.  Crashes alone cannot produce it (every
;             name a host program stages is a staging name,
;             fn-sn-sweep-rounds-collect-every-orphan); names the model does
;             not recognize, more than one observation of them, can.

(defun fn-sn-sweep-round (s observed overp held)
  (declare (xargs :guard t))
  (let ((removals (car (fn-sn-sweep-staging s observed held))))
    (cond ((not overp) (list :done removals))
          ((consp removals) (list :again removals))
          (t (list :refused nil)))))

; The subject the host calls, restated from the keystone above: a round
; removes only observed, unheld staging names.
(defthm fn-sn-sweep-round-removes-only-unheld-staging-names
  (implies (member-equal name (cadr (fn-sn-sweep-round s observed overp held)))
           (and (member-equal name observed)
                (fn-sn-staging-namep name)
                (not (fn-sn-name-memberp name held))))
  :hints (("Goal" :use fn-sn-sweep-removes-only-unheld-staging-names
           :in-theory (disable fn-sn-sweep-removes-only-unheld-staging-names
                               fn-sn-sweep-staging fn-sn-staging-namep))))

; The host's loop, as a model.  DIR is the staging directory's names in the
; order an enumeration yields them; a round observes the first LIMIT of
; them.  The recursion is guarded by the strict decrease the :again answer
; promises, so the definition terminates by its own test and the theorems
; below show the test never fails.
(defun fn-sn-take-names (n xs)
  (declare (xargs :guard (natp n)))
  (if (and (consp xs) (not (zp n)))
      (cons (car xs) (fn-sn-take-names (1- n) (cdr xs)))
    nil))

(defun fn-sn-drop-names (removals dir)
  (declare (xargs :guard t))
  (if (consp dir)
      (if (fn-sn-name-memberp (car dir) removals)
          (fn-sn-drop-names removals (cdr dir))
        (cons (car dir) (fn-sn-drop-names removals (cdr dir))))
    nil))

(defun fn-sn-sweep-rounds (s dir held limit)
  (declare (xargs :guard (natp limit) :measure (len dir)))
  (let* ((round (fn-sn-sweep-round s (fn-sn-take-names limit dir)
                                   (< (nfix limit) (len dir)) held))
         (next (fn-sn-drop-names (cadr round) dir)))
    (if (and (equal (car round) :again) (< (len next) (len dir)))
        (fn-sn-sweep-rounds s next held limit)
      (list (car round) next))))

(defun fn-sn-all-sweepablep (dir held)
  (declare (xargs :guard t))
  (if (consp dir)
      (and (fn-sn-staging-namep (car dir))
           (not (fn-sn-name-memberp (car dir) held))
           (fn-sn-all-sweepablep (cdr dir) held))
    t))

(local
 (encapsulate ()
   (defthm fn-sn-sweep-removals-of-all-sweepable
     (implies (and (fn-sn-all-sweepablep x held) (true-listp x))
              (equal (fn-sn-sweep-removals x held) x)))
   (defthm fn-sn-take-names-is-true-list
     (true-listp (fn-sn-take-names n xs)))
   (defthm fn-sn-all-sweepable-of-take-names
     (implies (fn-sn-all-sweepablep x held)
              (fn-sn-all-sweepablep (fn-sn-take-names n x) held)))
   (defthm fn-sn-all-sweepable-of-drop-names
     (implies (fn-sn-all-sweepablep x held)
              (fn-sn-all-sweepablep (fn-sn-drop-names r x) held)))
   (defthm fn-sn-len-of-drop-names-weak
     (<= (len (fn-sn-drop-names r x)) (len x))
     :rule-classes :linear)
   (defthm fn-sn-len-of-drop-names-strict
     (implies (and (consp x) (fn-sn-name-memberp (car x) r))
              (< (len (fn-sn-drop-names r x)) (len x)))
     :rule-classes :linear)
   (defthm fn-sn-name-memberp-of-take-names-car
     (implies (and (consp x) (not (zp n)))
              (fn-sn-name-memberp (car x) (fn-sn-take-names n x))))
   (defthm fn-sn-drop-own-window-is-shorter
     (implies (and (< 0 (len x)) (not (zp n)))
              (< (len (fn-sn-drop-names (fn-sn-take-names n x) x)) (len x)))
     :hints (("Goal" :in-theory (disable fn-sn-drop-names fn-sn-take-names)
              :use ((:instance fn-sn-len-of-drop-names-strict
                               (r (fn-sn-take-names n x)))
                    fn-sn-name-memberp-of-take-names-car)))
     :rule-classes :linear)
   (defun fn-sn-names-subsetp (x y)
     (if (consp x)
         (and (fn-sn-name-memberp (car x) y) (fn-sn-names-subsetp (cdr x) y))
       t))
   (defthm fn-sn-names-subsetp-of-cons
     (implies (fn-sn-names-subsetp x y) (fn-sn-names-subsetp x (cons a y))))
   (defthm fn-sn-names-subsetp-reflexive
     (fn-sn-names-subsetp x x))
   (defthm fn-sn-drop-names-of-subset-is-nil
     (implies (fn-sn-names-subsetp x r)
              (equal (fn-sn-drop-names r x) nil)))
   (defthm fn-sn-names-subsetp-of-true-list-fix
     (fn-sn-names-subsetp x (true-list-fix x)))
   (defthm fn-sn-take-names-of-short-list
     (implies (<= (len x) (nfix n))
              (equal (fn-sn-take-names n x) (true-list-fix x))))))

; Recovery of a store with N orphans, for every N, terminates with none: when
; every name in the staging directory is an unheld staging name and the
; kernel gate is open, the rounds end :done with the directory empty.  The
; hypotheses are the gate (the recovery barriers reached :ready), the shape
; of a directory crashes alone produce (every name one a host program staged,
; none held, since recovery runs before this process stages anything), and a
; positive observation bound.
(defthm fn-sn-sweep-rounds-collect-every-orphan
  (implies (and (fn-sn-sweep-enabledp s)
                (fn-sn-all-sweepablep dir held)
                (posp limit))
           (equal (fn-sn-sweep-rounds s dir held limit) (list :done nil)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-sn-sweep-rounds s dir held limit))))

; The loop never removes a name the sweep may not: every name of the
; directory that is not an unheld staging name is still there at the end,
; whatever the gate and however many rounds ran.
(local
 (defthm fn-sn-name-memberp-of-drop-names
   (implies (and (fn-sn-name-memberp name dir)
                 (not (fn-sn-name-memberp name r)))
            (fn-sn-name-memberp name (fn-sn-drop-names r dir)))))

(local
 (defthm fn-sn-sweep-removals-name-memberp
   (implies (fn-sn-name-memberp name (fn-sn-sweep-removals observed held))
            (and (fn-sn-staging-namep name)
                 (not (fn-sn-name-memberp name held))))))

(local
 (defthm fn-sn-sweep-round-keeps-a-name-it-may-not-remove
   (implies (and (fn-sn-name-memberp name dir)
                 (or (not (fn-sn-staging-namep name))
                     (fn-sn-name-memberp name held)))
            (fn-sn-name-memberp
             name (fn-sn-drop-names (cadr (fn-sn-sweep-round s observed overp held))
                                    dir)))
   :hints (("Goal" :in-theory (disable fn-sn-staging-namep fn-sn-drop-names)
            :cases ((fn-sn-name-memberp
                     name (fn-sn-sweep-removals observed held)))))))

(defthm fn-sn-sweep-rounds-keep-every-name-they-may-not-remove
  (implies (and (fn-sn-name-memberp name dir)
                (or (not (fn-sn-staging-namep name))
                    (fn-sn-name-memberp name held)))
           (fn-sn-name-memberp name (cadr (fn-sn-sweep-rounds s dir held limit))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-sn-sweep-rounds s dir held limit)
           :in-theory (disable fn-sn-staging-namep fn-sn-sweep-round
                               fn-sn-drop-names fn-sn-take-names))))

; The loop ends :done or :refused, never mid-round, and :refused is exactly
; the case the comment above names: more than LIMIT names remain and the
; observation of them removes nothing.
(local
 (defthm fn-sn-sweep-removals-are-members
   (implies (fn-sn-name-memberp name (fn-sn-sweep-removals observed held))
            (fn-sn-name-memberp name observed))))

(local
 (defthm fn-sn-take-names-members-are-members
   (implies (fn-sn-name-memberp name (fn-sn-take-names n x))
            (fn-sn-name-memberp name x))))

(local
 (defthm fn-sn-drop-names-strict-when-a-removal-is-present
   (implies (and (consp r) (fn-sn-name-memberp (car r) x))
            (< (len (fn-sn-drop-names r x)) (len x)))
   :rule-classes :linear))

(local
 (defthm fn-sn-sweep-staging-removals-are-a-true-list
   (true-listp (car (fn-sn-sweep-staging s observed held)))
   :rule-classes :type-prescription))

(local
 (defthm fn-sn-window-removals-shrink-the-directory
   (implies (consp (car (fn-sn-sweep-staging s (fn-sn-take-names n dir) held)))
            (< (len (fn-sn-drop-names
                     (car (fn-sn-sweep-staging s (fn-sn-take-names n dir) held))
                     dir))
               (len dir)))
   :hints (("Goal"
            :in-theory (disable fn-sn-drop-names fn-sn-take-names
                                fn-sn-sweep-removals fn-sn-staging-namep)
            :use ((:instance fn-sn-drop-names-strict-when-a-removal-is-present
                             (r (fn-sn-sweep-removals (fn-sn-take-names n dir) held))
                             (x dir))
                  (:instance fn-sn-sweep-removals-are-members
                             (name (car (fn-sn-sweep-removals
                                         (fn-sn-take-names n dir) held)))
                             (observed (fn-sn-take-names n dir)))
                  (:instance fn-sn-take-names-members-are-members
                             (name (car (fn-sn-sweep-removals
                                         (fn-sn-take-names n dir) held)))
                             (x dir)))))
   :rule-classes :linear))

(local
 (defthm fn-sn-drop-no-names-is-true-list-fix
   (equal (fn-sn-drop-names nil x) (true-list-fix x))))

(local
 (defthm fn-sn-take-names-of-true-list-fix
   (equal (fn-sn-take-names n (true-list-fix x)) (fn-sn-take-names n x))))

(defthm fn-sn-sweep-rounds-end-done-or-refused
  (let ((result (fn-sn-sweep-rounds s dir held limit)))
    (and (member-equal (car result) '(:done :refused))
         (implies (equal (car result) :refused)
                  (and (< (nfix limit) (len (cadr result)))
                       (equal (car (fn-sn-sweep-staging
                                    s (fn-sn-take-names limit (cadr result)) held))
                              nil)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-sn-sweep-rounds s dir held limit)
           :in-theory (disable fn-sn-staging-namep
                               fn-sn-sweep-staging fn-sn-drop-names fn-sn-take-names))))

; -----------------------------------------------------------------------------
; Export theory.  The list-recursive vocabulary the proofs induct on stays
; enabled (fn-sn-octet-prefixp, fn-sn-digit-octet-listp,
; fn-sn-sweep-removals); the predicates and the event are withdrawn.

(deftheory fn-sn-sweep-vocabulary
  '(fn-sn-staging-namep fn-sn-final-namespace-namep fn-sn-sweep-enabledp
    fn-sn-sweep-staging fn-sn-sweep-round fn-sn-sweep-rounds))

(in-theory (disable fn-sn-sweep-vocabulary))
