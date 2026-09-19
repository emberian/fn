; fn: group membership as epochs, and the admissibility of a late message.
;
; This is a POLICY model.  There are no keys, no ciphertext, no ratchet and no
; digest here, and nothing in this book may be cited as evidence that any
; cryptographic construction is sound.  What it models is the decision fn's
; application layer must make on its own account no matter which group
; protocol is later selected: a letter arrives carrying a group epoch, and the
; receiving site must say whether it is admissible now, held for later, or
; refused, using only what that site knows.
;
; The shape is taken from three places.
;
;   * RFC 9420 section 14 ("Sequencing of State Changes"): a Commit is premised
;     on the epoch in its FramedContent, "if the changes implied by a Commit
;     message are made starting from a different state, the results will be
;     incorrect", and "applications MUST have an established way to resolve
;     conflicting Commit messages for the same epoch".  A commit here therefore
;     carries its base epoch explicitly and creates epoch base+1, and the
;     conflict at a base is a first-class value (`fn-me-fork-evidence`) rather
;     than something a merge silently resolves.
;
;   * RFC 9420 section 15.3 ("Delayed and Reordered Application Messages"):
;     applications SHOULD bound how long unused keys are kept and how far a
;     receiver will move forward for one message.  That bound appears here as
;     `fn-me-window` (how far behind the local epoch a message may be and still
;     be admissible) and `fn-me-hold-limit` (how many ahead-of-local messages a
;     site will take custody of).
;
;   * books/lace.lisp: the evidence a site holds about membership is a set of
;     commits keyed by content id, and `fn-me-merge` is the same skip-if-present
;     union.  Merging a peer's evidence is an evidence operation only: it never
;     changes which chain the site has adopted, so no arrival order and no
;     clock can revise a membership decision (AGENTS.md, "do not introduce
;     last-writer-wins based on wall-clock time").
;
; Four outcomes stay distinct all the way out, as D13 requires elsewhere in fn:
;
;   :admit     the site may process this message at the epoch it names
;   :hold      the site has not reached that epoch; it takes custody and waits
;   :capacity  the site cannot take custody (hold limit reached); the sender's
;              obligation is not discharged and nothing is dropped here
;   :refuse    the message is not admissible to the conversation
;
; `:refuse` is a statement about the conversation, not about storage.  The
; opaque object may still be retained under D03 and relayed under REP-006; a
; relay that cannot read inner news metadata is exactly SEC-001's goal.  This
; book decides admissibility and touches no retention pin.
;
; WHAT THIS MODEL DOES NOT CLAIM.  `fn-me-decide` refuses a revoked sender's
; messages at and after the revocation epoch.  It cannot refuse a message that
; a revoked member manufactures while CLAIMING an epoch before its revocation:
; that property belongs to epoch-bound authentication in whatever protocol is
; selected, and is an assumption of this model, not a theorem of it.  SEC-004
; asks when revocation is effective for each sender; the answer this model
; encodes is "from the revocation epoch onward, for every site that knows the
; revocation", and a disconnected sender that has not received the revocation
; keeps producing messages that other sites will refuse.
;
; One policy choice is visible in the definitions and has teeth in the test
; book: a removed member is not re-added under the same member identity
; (`fn-me-no-readmissionp`).  Re-admission would make revocation knowledge
; non-monotone -- a site that had seen the removal but not the re-add would
; refuse what a better-informed site admits, and a site that had seen both
; would admit what the protocol elsewhere treats as revoked.  Under
; disconnection that is not a race to be won but a permanent disagreement, so
; re-admission takes a fresh member identity.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; Commits
;
; A commit is (id, base, actor, op, subject).  `id` is the commit's content id,
; opaque here; `base` is the epoch the commit is premised on, so the commit
; creates epoch base+1.  `op` is one of three membership operations; `:rotate`
; changes key material only and leaves the roster alone, which is why it is a
; separate operation rather than a remove-then-add.

(defun fn-me-opp (x)
  (declare (xargs :guard t))
  (if (member-eq x '(:add :remove :rotate)) t nil))

(defun fn-me-commit (id base actor op subject)
  (declare (xargs :guard t))
  (list :fn-me-commit id base actor op subject))

(defun fn-me-commitp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 6)
       (equal (car x) :fn-me-commit)
       (natp (nth 2 x))
       (fn-me-opp (nth 4 x))))

(defun fn-me-commit-id (c)
  (declare (xargs :guard (fn-me-commitp c)))
  (nth 1 c))

(defun fn-me-commit-base (c)
  (declare (xargs :guard (fn-me-commitp c)))
  (nth 2 c))

(defun fn-me-commit-actor (c)
  (declare (xargs :guard (fn-me-commitp c)))
  (nth 3 c))

(defun fn-me-commit-op (c)
  (declare (xargs :guard (fn-me-commitp c)))
  (nth 4 c))

(defun fn-me-commit-subject (c)
  (declare (xargs :guard (fn-me-commitp c)))
  (nth 5 c))

; The epoch this commit creates.  RFC 9420 section 14's "starting state" is
; `fn-me-commit-base`; the state it produces is one epoch later.
(defun fn-me-commit-epoch (c)
  (declare (xargs :guard (fn-me-commitp c)))
  (+ 1 (fn-me-commit-base c)))

(defun fn-me-commitsp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (fn-me-commitp (car x))
           (fn-me-commitsp (cdr x)))
    (null x)))

(defthm fn-me-commitsp-car
  (implies (and (fn-me-commitsp x) (consp x))
           (fn-me-commitp (car x))))

(defthm fn-me-commitsp-cdr
  (implies (fn-me-commitsp x)
           (fn-me-commitsp (cdr x))))

(defthm fn-me-commitsp-implies-true-listp
  (implies (fn-me-commitsp x) (true-listp x)))

(defthm fn-me-commitsp-of-append
  (implies (true-listp a)
           (equal (fn-me-commitsp (append a b))
                  (and (fn-me-commitsp a) (fn-me-commitsp b)))))

(defthm fn-me-commitsp-member
  (implies (and (fn-me-commitsp x) (member-equal c x))
           (fn-me-commitp c)))

; -----------------------------------------------------------------------------
; Evidence sets and their merge (the lace shape)

(defun fn-me-commit-ids (commits)
  (declare (xargs :guard (fn-me-commitsp commits)))
  (if (consp commits)
      (cons (fn-me-commit-id (car commits))
            (fn-me-commit-ids (cdr commits)))
    nil))

(defun fn-me-hasp (commits id)
  (declare (xargs :guard (fn-me-commitsp commits)))
  (if (member-equal id (fn-me-commit-ids commits)) t nil))

(defun fn-me-new (commits delta)
  (declare (xargs :guard (and (fn-me-commitsp commits) (fn-me-commitsp delta))))
  (if (consp delta)
      (if (member-equal (fn-me-commit-id (car delta)) (fn-me-commit-ids commits))
          (fn-me-new commits (cdr delta))
        (cons (car delta) (fn-me-new commits (cdr delta))))
    nil))

(defthm fn-me-commitsp-of-new
  (implies (fn-me-commitsp delta)
           (fn-me-commitsp (fn-me-new commits delta))))

(defun fn-me-merge (commits delta)
  (declare (xargs :guard (and (fn-me-commitsp commits) (fn-me-commitsp delta))))
  (append commits (fn-me-new commits delta)))

(defun fn-me-ids-subsetp (a b)
  (declare (xargs :guard (and (fn-me-commitsp a) (fn-me-commitsp b))))
  (if (consp a)
      (and (member-equal (fn-me-commit-id (car a)) (fn-me-commit-ids b))
           (fn-me-ids-subsetp (cdr a) b))
    t))

(defun fn-me-same-idsp (a b)
  (declare (xargs :guard (and (fn-me-commitsp a) (fn-me-commitsp b))))
  (and (fn-me-ids-subsetp a b)
       (fn-me-ids-subsetp b a)))

; -----------------------------------------------------------------------------
; Conflict evidence
;
; Two distinct commits premised on the same base epoch are the RFC 9420
; section 14 conflict.  fn does not pick one: `fn-me-fork-evidence` returns the
; pair, so the disagreement is a value a site can hold, report and carry in a
; batch.  Resolution is a separate, named and authorized act.

(defun fn-me-conflict-with (c commits)
  (declare (xargs :guard (and (fn-me-commitp c) (fn-me-commitsp commits))))
  (if (consp commits)
      (if (and (equal (fn-me-commit-base (car commits)) (fn-me-commit-base c))
               (not (equal (fn-me-commit-id (car commits)) (fn-me-commit-id c))))
          (car commits)
        (fn-me-conflict-with c (cdr commits)))
    nil))

(defun fn-me-fork-scan (rest commits)
  (declare (xargs :guard (and (fn-me-commitsp rest) (fn-me-commitsp commits))))
  (if (consp rest)
      (if (fn-me-conflict-with (car rest) commits)
          (cons (car rest) (fn-me-conflict-with (car rest) commits))
        (fn-me-fork-scan (cdr rest) commits))
    nil))

(defun fn-me-fork-evidence (commits)
  (declare (xargs :guard (fn-me-commitsp commits)))
  (fn-me-fork-scan commits commits))

(defun fn-me-forkedp (commits)
  (declare (xargs :guard (fn-me-commitsp commits)))
  (if (fn-me-fork-evidence commits) t nil))

; -----------------------------------------------------------------------------
; Rosters
;
; The roster in epoch n is the founding roster with the first n adopted commits
; applied.  `:rotate` is deliberately the identity on the roster.

(defun fn-me-apply-op (roster op subject)
  (declare (xargs :guard (true-listp roster)))
  (cond ((equal op :add) (add-to-set-equal subject roster))
        ((equal op :remove) (remove-equal subject roster))
        (t roster)))

(defthm fn-me-apply-op-true-listp
  (implies (true-listp roster)
           (true-listp (fn-me-apply-op roster op subject))))

(defun fn-me-roster-fold (roster chain)
  (declare (xargs :guard (and (true-listp roster) (fn-me-commitsp chain))))
  (if (consp chain)
      (fn-me-roster-fold (fn-me-apply-op roster
                                         (fn-me-commit-op (car chain))
                                         (fn-me-commit-subject (car chain)))
                         (cdr chain))
    roster))

(defun fn-me-chain-prefix (n chain)
  (declare (xargs :guard (and (natp n) (fn-me-commitsp chain))))
  (if (and (posp n) (consp chain))
      (cons (car chain) (fn-me-chain-prefix (- n 1) (cdr chain)))
    nil))

(defthm fn-me-commitsp-of-chain-prefix
  (implies (fn-me-commitsp chain)
           (fn-me-commitsp (fn-me-chain-prefix n chain))))

; -----------------------------------------------------------------------------
; Revocation knowledge
;
; `fn-me-revoked-scan` returns the epoch created by the FIRST `:remove` of
; `member` in the adopted chain, or 0 when the chain holds no such commit.  No
; commit creates epoch 0, so 0 is an unambiguous "not revoked as far as this
; site knows".

(defun fn-me-revoked-scan (chain member index)
  (declare (xargs :guard (and (fn-me-commitsp chain) (natp index))))
  (if (consp chain)
      (if (and (equal (fn-me-commit-op (car chain)) :remove)
               (equal (fn-me-commit-subject (car chain)) member))
          (+ 1 (nfix index))
        (fn-me-revoked-scan (cdr chain) member (+ 1 (nfix index))))
    0))

(defthm fn-me-revoked-scan-natp
  (natp (fn-me-revoked-scan chain member index))
  :rule-classes (:rewrite :type-prescription))

; The re-admission policy, as a checkable predicate over a chain: no `:add` of
; a member an earlier commit removed.
(defun fn-me-no-readmission-scan (removed chain)
  (declare (xargs :guard (and (true-listp removed) (fn-me-commitsp chain))))
  (if (consp chain)
      (and (not (and (equal (fn-me-commit-op (car chain)) :add)
                     (member-equal (fn-me-commit-subject (car chain)) removed)))
           (fn-me-no-readmission-scan
            (if (equal (fn-me-commit-op (car chain)) :remove)
                (add-to-set-equal (fn-me-commit-subject (car chain)) removed)
              removed)
            (cdr chain)))
    t))

(defun fn-me-no-readmissionp (chain)
  (declare (xargs :guard (fn-me-commitsp chain)))
  (fn-me-no-readmission-scan nil chain))

; Does this chain segment add `member` at all?  The roster lemma below is
; stated against this rather than against the whole no-readmission predicate,
; so that it holds of any segment a site is reasoning about.
(defun fn-me-addsp (member chain)
  (declare (xargs :guard (fn-me-commitsp chain)))
  (if (consp chain)
      (or (and (equal (fn-me-commit-op (car chain)) :add)
               (equal (fn-me-commit-subject (car chain)) member))
          (fn-me-addsp member (cdr chain)))
    nil))

; -----------------------------------------------------------------------------
; Messages
;
; A message names its sender, the epoch it was produced in, and its content id.
; It carries no payload: this book decides admissibility, it does not read.

(defun fn-me-message (sender epoch content)
  (declare (xargs :guard t))
  (list :fn-me-message sender epoch content))

(defun fn-me-messagep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 4)
       (equal (car x) :fn-me-message)
       (natp (nth 2 x))))

(defun fn-me-msg-sender (m)
  (declare (xargs :guard (fn-me-messagep m)))
  (nth 1 m))

(defun fn-me-msg-epoch (m)
  (declare (xargs :guard (fn-me-messagep m)))
  (nth 2 m))

(defun fn-me-msg-content (m)
  (declare (xargs :guard (fn-me-messagep m)))
  (nth 3 m))

(defthm fn-me-msg-epoch-natp
  (implies (fn-me-messagep m) (natp (fn-me-msg-epoch m)))
  :rule-classes (:rewrite :type-prescription))

(defun fn-me-messagesp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (fn-me-messagep (car x))
           (fn-me-messagesp (cdr x)))
    (null x)))

(defthm fn-me-messagesp-implies-true-listp
  (implies (fn-me-messagesp x) (true-listp x)))

(defthm fn-me-messagesp-of-append
  (implies (true-listp a)
           (equal (fn-me-messagesp (append a b))
                  (and (fn-me-messagesp a) (fn-me-messagesp b)))))

; -----------------------------------------------------------------------------
; Sites
;
; A site holds: its own name, the founding roster, the chain of commits it has
; ADOPTED (in order; the commit at position i creates epoch i+1), the wider set
; of commits it has as EVIDENCE, its admissibility window, its hold limit, and
; the messages it currently holds.  Adopted chain and evidence are separate on
; purpose: receiving a peer's commits is not adopting them.

(defun fn-me-site (id founding chain commits window hold-limit held)
  (declare (xargs :guard t))
  (list :fn-me-site id founding chain commits window hold-limit held))

(defun fn-me-sitep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 8)
       (equal (car x) :fn-me-site)
       (true-listp (nth 2 x))
       (fn-me-commitsp (nth 3 x))
       (fn-me-commitsp (nth 4 x))
       (natp (nth 5 x))
       (natp (nth 6 x))
       (fn-me-messagesp (nth 7 x))))

(defun fn-me-site-id (s)
  (declare (xargs :guard (fn-me-sitep s)))
  (nth 1 s))

(defun fn-me-founding (s)
  (declare (xargs :guard (fn-me-sitep s)))
  (nth 2 s))

(defun fn-me-chain (s)
  (declare (xargs :guard (fn-me-sitep s)))
  (nth 3 s))

(defun fn-me-commits (s)
  (declare (xargs :guard (fn-me-sitep s)))
  (nth 4 s))

(defun fn-me-window (s)
  (declare (xargs :guard (fn-me-sitep s)))
  (nth 5 s))

(defun fn-me-hold-limit (s)
  (declare (xargs :guard (fn-me-sitep s)))
  (nth 6 s))

(defun fn-me-held (s)
  (declare (xargs :guard (fn-me-sitep s)))
  (nth 7 s))

(defthm fn-me-founding-true-listp
  (implies (fn-me-sitep s) (true-listp (fn-me-founding s))))

(defthm fn-me-chain-commitsp
  (implies (fn-me-sitep s) (fn-me-commitsp (fn-me-chain s))))

(defthm fn-me-commits-commitsp
  (implies (fn-me-sitep s) (fn-me-commitsp (fn-me-commits s))))

(defthm fn-me-window-natp
  (implies (fn-me-sitep s) (natp (fn-me-window s)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-me-hold-limit-natp
  (implies (fn-me-sitep s) (natp (fn-me-hold-limit s)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-me-held-messagesp
  (implies (fn-me-sitep s) (fn-me-messagesp (fn-me-held s))))

; The local epoch is the length of the adopted chain: epoch 0 is the founding
; state, and each adopted commit advances by one.
(defun fn-me-epoch (s)
  (declare (xargs :guard (fn-me-sitep s)))
  (len (fn-me-chain s)))

(defun fn-me-roster-at (s n)
  (declare (xargs :guard (and (fn-me-sitep s) (natp n))))
  (fn-me-roster-fold (fn-me-founding s) (fn-me-chain-prefix n (fn-me-chain s))))

(defun fn-me-revoked-at (s member)
  (declare (xargs :guard (fn-me-sitep s)))
  (fn-me-revoked-scan (fn-me-chain s) member 0))

(defthm fn-me-revoked-at-natp
  (natp (fn-me-revoked-at s member))
  :rule-classes (:rewrite :type-prescription))

; -----------------------------------------------------------------------------
; The admissibility decision
;
; The order of the tests is the policy.  Revocation is tested FIRST and against
; the message's own epoch, so a revocation the site knows about decides even
; for epochs the site has not itself reached; otherwise a site could hold, and
; later admit, a message from a member it already knows was removed.

(defconst *fn-me-outcomes* '(:admit :hold :refuse :capacity))

(defun fn-me-decide (site msg)
  (declare (xargs :guard (and (fn-me-sitep site) (fn-me-messagep msg))))
  (let ((sender (fn-me-msg-sender msg))
        (e (fn-me-msg-epoch msg))
        (local (fn-me-epoch site))
        (revoked (fn-me-revoked-at site (fn-me-msg-sender msg))))
    (cond ((and (< 0 revoked) (<= revoked e)) :refuse)
          ((< local e)
           (if (< (len (fn-me-held site)) (fn-me-hold-limit site))
               :hold
             :capacity))
          ((< (+ e (fn-me-window site)) local) :refuse)
          ((not (member-equal sender (fn-me-roster-at site e))) :refuse)
          (t :admit))))

; Taking custody.  Only a `:hold` changes the site, and it changes nothing but
; the held list: no adoption, no roster change, no epoch change.
(defun fn-me-receive (site msg)
  (declare (xargs :guard (and (fn-me-sitep site) (fn-me-messagep msg))))
  (if (equal (fn-me-decide site msg) :hold)
      (fn-me-site (fn-me-site-id site)
                  (fn-me-founding site)
                  (fn-me-chain site)
                  (fn-me-commits site)
                  (fn-me-window site)
                  (fn-me-hold-limit site)
                  (append (fn-me-held site) (list msg)))
    site))

; Merging a peer's evidence.  Evidence only: the adopted chain is untouched.
(defun fn-me-site-merge (site delta)
  (declare (xargs :guard (and (fn-me-sitep site) (fn-me-commitsp delta))))
  (fn-me-site (fn-me-site-id site)
              (fn-me-founding site)
              (fn-me-chain site)
              (fn-me-merge (fn-me-commits site) delta)
              (fn-me-window site)
              (fn-me-hold-limit site)
              (fn-me-held site)))

; Adopting one commit: the named, authorized act that a merge is not.
(defun fn-me-adopt (site commit)
  (declare (xargs :guard (and (fn-me-sitep site) (fn-me-commitp commit))))
  (if (equal (fn-me-commit-base commit) (fn-me-epoch site))
      (fn-me-site (fn-me-site-id site)
                  (fn-me-founding site)
                  (append (fn-me-chain site) (list commit))
                  (fn-me-merge (fn-me-commits site) (list commit))
                  (fn-me-window site)
                  (fn-me-hold-limit site)
                  (fn-me-held site))
    site))

; -----------------------------------------------------------------------------
; The knowledge order
;
; `b` knows at least what `a` knows when it has the same founding roster and
; window, its adopted chain extends a's as a prefix, and its evidence set
; includes a's.  Extension, not arbitrary difference: a site that adopted a
; DIFFERENT commit at some epoch is not better informed, it is forked, and
; `fn-me-fork-evidence` is how that is recorded.

(defun fn-me-chain-prefixp (a b)
  (declare (xargs :guard (and (fn-me-commitsp a) (fn-me-commitsp b))))
  (if (consp a)
      (and (consp b)
           (equal (car a) (car b))
           (fn-me-chain-prefixp (cdr a) (cdr b)))
    t))

(defun fn-me-knowledge-extendsp (a b)
  (declare (xargs :guard (and (fn-me-sitep a) (fn-me-sitep b))))
  (and (equal (fn-me-founding a) (fn-me-founding b))
       (equal (fn-me-window a) (fn-me-window b))
       (fn-me-chain-prefixp (fn-me-chain a) (fn-me-chain b))
       (fn-me-ids-subsetp (fn-me-commits a) (fn-me-commits b))))
