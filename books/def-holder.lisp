; fn: `def-holder' --- holding is a declared relation (lane def-holder,
; Fable deputy, 2026-10-03).
;
; The same question was answered by hand, late, after a defect, four times:
; "who can still hold this resource, and when is it safe to release it?"
; A cold read's file generation (books/page-read-ownership.lisp: a per-row
; walk per close), a payload handle (no holder is recorded at all; the arena
; has no delete), a retention pin (a whole-ledger invariant re-evaluated per
; call), a connection's pinned view (a scan of the connections).  One of the
; four was written right once: the arena readers' generation table
; (books/arena-reader-pins.lisp, PRF-941), a carried count per key kept
; ascending, a quiet test that is one comparison, a release theorem, and a
; refused late unpin.  That table is this book's library; `def-holder'
; declares, for one RESOURCE, who holds it and through which host-called
; entries, and generates what each hand instance wrote:
;
;   (def-holder NAME
;     :shape :keyed | :stamped        ; :keyed: holds are counted per KEY (a
;                                     ; file incarnation, a handle, a slot) and
;                                     ; a key is quiet when its count is 0;
;                                     ; :stamped: holds pin the table's own
;                                     ; generation (fn-arpn-step: :pin/:unpin,
;                                     ; retirements stamped and released)
;     :key "what one key is"          ; prose, carried in the row
;     :holders ((KIND :acquire (FN THM :table I :result P :key K :ok OK
;                                  [:when W] [:keeps THM2])
;                     :release (FN THM :table I :result P :key K :ok OK
;                                  [:when W] [:keeps THM2]))
;               (KIND :host t :acquire FNN :release FNN :in (FNN ...))
;               (KIND :root t :in (FNN ...) :status (WORD "why"))
;               ...)
;     :effect (:process-local "why the table is process memory")
;           | (:durable PROGRAM "cut")
;           | (:physical CUTS :cut K :after K2)
;     [:complete-by "why the holder list is complete"]
;     [:trace nil])
;
; WHAT THIS BOOK IS, AND IS NOT (consultation c05, 2026-10-03).  def-holder
; is an ACCOUNTING component: it generates the carried count of holds per
; key and the theorems about that count.  It authorizes no forget and no
; close by itself.  A release of the resource is licensed only by the
; conjunction of (1) the instance's ROOT theorem -- no reachable root names
; the key: the top history, every connection's view, every captured row
; list, every continuation, every log member, stated over all of them, never
; the top alone -- (2) the generated accounting (every holder that pinned
; before the retirement has ended), (3) physical custody ended (a cold read
; names a file and a place, not a key; storage is reused only after its
; last borrower settles), and (4) the durable ordering (the physical effect
; follows the durable replacement at every cut).  A ROOT holder (:root t)
; declares one such root with the host functions that keep it and its
; status: (:repinned "..") it is rebuilt at every retirement, (:pinned "..")
; it pins a generation before it copies, (:serialized "..") it never
; outlives the owner's quantum, (:excluded "..") the release is refused
; while it names the key, (:unwired "..") no served path reaches it yet.  The world's walk (def-holder-check) and tools/holder_check.py over
; host/native/**/*.lisp are the closure over the declared entries; neither
; is an escape analysis of every copy of a key: the row says what is
; declared, and the instance's root theorem says what is proved.
;
; A LOGIC holder's entries are functions of this world that THREAD the
; table: FN's formal I is the table it is handed, P (a term over `_', the
; call) the table it returns, K (over FN's formals) the key the entry holds
; or drops, OK (over `_') the answer on which it does so.  THE STATEMENTS
; ARE GENERATED from the world; THM is only `:use'd, in the minimal theory,
; so a declared theorem about another term proves nothing and is refused
; where the proof fails (def-carried's rule).  With G FN's guard and CALL
; FN over its formals:
;
;   NAME-KIND-acquire-holds   (implies (and G W) (equal P[_:=CALL]
;                                (if OK[_:=CALL]
;                                    (mv-nth 0 (fn-hd-keyed-step TABLE (list :hold K)))
;                                  TABLE)))
;   NAME-KIND-release-drops   the same with (list :drop K)
;   (:stamped: (fn-arpn-step TABLE '(:pin)) and (list :unpin K))
;   NAME-KIND-acquire-keeps / -release-keeps
;                             (implies (and (TABLEP TABLE) G) (TABLEP P[_:=CALL]))
;                             TABLEP = fn-arpn-pinsp (:keyed) | fn-arpn-okp (:stamped);
;                             proved from the -holds/-drops theorem and the
;                             generic preservation, nothing else -- or, when
;                             the entry declares :when W (one function serves
;                             several arms, as fn-rpin-step does: the holds
;                             theorem covers the selected arm only), from the
;                             declared :keeps THM2, which is then required
;
; and, unless :trace nil, the def-carried row NAME-table over TABLEP with
; those entries as its transitions and NAME-initial (the empty table) as
; its establishing point, so NAME-table-run-carries is the trace theorem
; and the row is in `fn-carried'.  A HOST holder (:host t) names raw host
; functions (host/native/*.lisp) that call the table's step through fnn-call;
; the world proves nothing about them; the row carries their names for
; tools/holder_check.py, which refuses a host call of the step outside a
; declared holder's :in functions.
;
; What the generic proves once (so no instance proves it again):
;   fn-hd-drop-of-unheld-is-refused   KEYSTONE: the LATE HOLDER.  A :drop of
;       a key nobody holds answers :refused and leaves the table as it was --
;       distinct from :dropped, never a silent no-op, never an error;
;   fn-hd-hold-counts-exactly-its-key / fn-hd-drop-counts-exactly-its-key:
;       a hold or drop changes the count at its key by one and no other;
;   fn-hd-run-count-is-holds-less-drops   KEYSTONE: over any run of the keyed
;       step, a key's count is what it was plus the holds of it less the
;       drops of it that were answered :dropped: so from the empty table a
;       QUIET key (count 0) is one whose every hold was dropped -- "quiet
;       implies no reachable holder", the forget/close precondition;
;   fn-arpn-release-postdates-every-live-pin (books/arena-reader-pins.lisp)
;       the same for the :stamped shape: every released retirement is below
;       every live pin.
;
; CRASH POINTS.  Between "decided to release" and "released" there is a cut.
; `def-holder' owns its names: `*NAME-cuts*' and a row in `fn-holder-cuts'
; (:effect EFFECT :cuts (...)).  The EFFECT classifies what the release
; does, because they are not alike (c05):
;   (:process-local "why")   the table and what it frees are process memory
;                            rebuilt at the open (NAME-initial); nothing is
;                            returned to the operating system; cuts
;                            (:NAME-decided :NAME-released), candidate
;                            "rebuilt";
;   (:durable PROGRAM "cut") the release performs a durable step of the
;                            byte-model program PROGRAM at that cut; refused
;                            unless PROGRAM is a function of this world whose
;                            body names "cut" (the step list
;                            tools/native_program_check.py compares with the
;                            host); cuts (:NAME-decided :NAME-released);
;   (:physical CUTS :cut K :after K2)
;                            the release returns storage (a descriptor
;                            closed, a file unlinked, blocks given back) at
;                            cut K of the keyword cut list CUTS, a defconst of
;                            this world the host mirrors (*fn-orcp-cuts* /
;                            +fnn-reclaim-cuts+), and K2, the durable
;                            replacement, precedes K in that list: refused
;                            otherwise.  Returning blocks is never
;                            process-local: a death between K2 and K leaves
;                            the storage held and the replacement durable,
;                            which recovery tolerates; the reverse order
;                            would not be.  Cuts (K2 K).
; A declared cut is a NAME, not a checked host release: tools/holder_check.py
; refuses a declared release whose :in function does not carry both cuts.
; DEF-ENTRY's per-entry crash-point enumeration READS this table for an entry
; declared as a holder's release and emits no cut of its own for it (agreed
; 2026-10-03: generated once, two readers); the row feeds Astra's two-way
; cut check (t40) when it lands.
;
; TEETH.  Every generated theorem is owed teeth: after each `(defthm K ...)'
; the row `(table fn-teeth-owed 'K '(:by def-holder :claim CLAIM :subject
; FN))' is emitted per GENERATORS' defteeth contract v1
; (lanedumps/generators-2.md), CLAIM the statement in its source shape
; `(implies (and H ...) C)' over the same translated parts, so its
; translation IS the theorem; the instance's test book writes `(defteeth K
; :claim CLAIM ...)' and `(defteeth-check)' refuses an owed keystone with no
; fn-teeth row, or one whose claim differs.
;
; FAIL CLOSED.  Admission refuses, each by name: a malformed form; an
; unknown shape; a holder with neither :host nor both entries; an entry
; whose FN is not a function, whose THM is not a theorem, whose :table is
; not a formal position, whose :key mentions a non-formal, whose :ok or
; :result is not over `_' alone; a redeclared NAME; a :durable effect naming
; a program that does not name the cut; and any generated statement ACL2
; does not prove.  `def-holder-check' re-runs every check in the world as
; now loaded (the generated formulas compared with the statements
; regenerated now) and, over the WHOLE world, refuses any function whose
; body calls fn-hd-keyed-step or fn-arpn-step and is neither a declared
; logic entry of some row nor one of the library's own two run functions
; (*fn-hd-library-callers*): an undeclared acquirer of a declared resource
; is a refusal, not a holder.
;
; Not claimed: that the host threads the table at every site is
; tools/holder_check.py's (the raw host is outside the world); that a
; process-local table is rebuilt empty is the host's open, named in the
; effect's reason, not a theorem.

(in-package "ACL2")
(include-book "arena-reader-pins") ; the table (fn-arpn-pinsp, pin-at, unpin-at, pins-of,
                                   ; clear-through-p) and the :stamped step
(include-book "def-carried")       ; fn-cd-* helpers; the trace row

; ---------------------------------------------------------------------------
; The keyed step over the table: a hold or drop names its key.

; Answers (mv TABLE' ANSWER):
;   (:hold K)   K held once more: :held
;   (:drop K)   one holder of K fewer: :dropped; nobody holds K: :refused,
;               TABLE unchanged (the late holder's outcome, by name)
;   (:count K)  the holders of K
;   (:quiet K)  whether nobody holds K
; Any other event -- another verb, a key that is not a natural, a list of
; another length -- is :refused and TABLE unchanged.
(defun fn-hd-keyed-step (table ev)
  (declare (xargs :guard (fn-arpn-pinsp table)))
  (if (not (and (consp ev) (consp (cdr ev)) (null (cddr ev)) (natp (cadr ev))))
      (mv table :refused)
    (let ((k (cadr ev)))
      (case (car ev)
        (:hold (mv (fn-arpn-pin-at k table) :held))
        (:drop (if (fn-arpn-held-p k table)
                   (mv (fn-arpn-unpin-at k table) :dropped)
                 (mv table :refused)))
        (:count (mv table (fn-arpn-pins-of k table)))
        (:quiet (mv table (equal (fn-arpn-pins-of k table) 0)))
        (otherwise (mv table :refused))))))

(defun fn-hd-initial ()
  (declare (xargs :guard t))
  nil)

(defthm fn-hd-initial-is-a-table
  (fn-arpn-pinsp (fn-hd-initial)))

; The empty table holds nothing: every key is quiet.
(defthm fn-hd-initial-is-quiet
  (equal (fn-arpn-pins-of k (fn-hd-initial)) 0))

(defthm fn-hd-keyed-step-preserves-table
  (implies (fn-arpn-pinsp table)
           (fn-arpn-pinsp (mv-nth 0 (fn-hd-keyed-step table ev)))))

; A hold changes exactly its key's count, by one.
(defthm fn-hd-hold-counts-exactly-its-key
  (implies (and (fn-arpn-pinsp table) (natp k))
           (let ((r (fn-hd-keyed-step table (list :hold k))))
             (and (equal (mv-nth 1 r) :held)
                  (equal (fn-arpn-pins-of h (mv-nth 0 r))
                         (if (equal h k)
                             (+ 1 (fn-arpn-pins-of h table))
                           (fn-arpn-pins-of h table)))))))

; Exported (a certified includer's guard proofs need them: a count is a
; natural, a run keeps the table).
(defthm fn-hd-pins-of-natp
  (implies (fn-arpn-pinsp table)
           (natp (fn-arpn-pins-of k table)))
  :rule-classes :type-prescription)

; A drop of a held key changes exactly its count, by one.
(defthm fn-hd-drop-counts-exactly-its-key
  (implies (and (fn-arpn-pinsp table) (natp k) (fn-arpn-held-p k table))
           (let ((r (fn-hd-keyed-step table (list :drop k))))
             (and (equal (mv-nth 1 r) :dropped)
                  (equal (fn-arpn-pins-of h (mv-nth 0 r))
                         (if (equal h k)
                             (- (fn-arpn-pins-of h table) 1)
                           (fn-arpn-pins-of h table))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-arpn-pins-of-unpin-at (g k) (pins table))
                 (:instance fn-hd-pins-of-natp (k h)))
           :in-theory (disable fn-arpn-pins-of-unpin-at fn-arpn-unpin-at fn-arpn-pins-of))))

; KEYSTONE (the late holder).  A drop of a key nobody holds is refused by
; name and changes nothing: the answer is :refused, never :dropped, and the
; table is the one handed in.  (No table hypothesis: the refusal does not
; depend on the table being well formed; natp K is needed, a non-natural
; key is refused on its own arm.)
(defthm fn-hd-drop-of-unheld-is-refused
  (implies (not (and (natp k) (fn-arpn-held-p k table)))
           (equal (mv-list 2 (fn-hd-keyed-step table (list :drop k)))
                  (list table :refused))))

; A run of keyed events, and its answers.
(defun fn-hd-run (table evs)
  (declare (xargs :guard (and (fn-arpn-pinsp table) (true-listp evs))))
  (if (atom evs)
      table
    (mv-let (table1 answer) (fn-hd-keyed-step table (car evs))
      (declare (ignore answer))
      (fn-hd-run table1 (cdr evs)))))

(defun fn-hd-run-answers (table evs)
  (declare (xargs :guard (and (fn-arpn-pinsp table) (true-listp evs))))
  (if (atom evs)
      nil
    (mv-let (table1 answer) (fn-hd-keyed-step table (car evs))
      (cons answer (fn-hd-run-answers table1 (cdr evs))))))

; The holds of K among EVS, and the drops of K among EVS that were answered
; :dropped (ANSWERS the run's answers, in step).
(defun fn-hd-holds-of (k evs)
  (declare (xargs :guard (true-listp evs)))
  (cond ((atom evs) 0)
        ((equal (car evs) (list :hold k)) (+ 1 (fn-hd-holds-of k (cdr evs))))
        (t (fn-hd-holds-of k (cdr evs)))))

(defun fn-hd-drops-of (k evs answers)
  (declare (xargs :guard (and (true-listp evs) (true-listp answers))))
  (cond ((atom evs) 0)
        ((and (equal (car evs) (list :drop k)) (equal (car answers) :dropped))
         (+ 1 (fn-hd-drops-of k (cdr evs) (cdr answers))))
        (t (fn-hd-drops-of k (cdr evs) (cdr answers)))))

(defthm fn-hd-run-preserves-table
  (implies (fn-arpn-pinsp table)
           (fn-arpn-pinsp (fn-hd-run table evs))))

; A well-formed event is exactly its two elements.
(local
 (defthm fn-hd-two-list
   (implies (and (consp ev) (consp (cdr ev)) (null (cddr ev)))
            (equal ev (list (car ev) (cadr ev))))
   :rule-classes nil))

; One step's effect on the count at K, by the event's shape.
(local
 (defthm fn-hd-keyed-step-count-at
   (implies (and (fn-arpn-pinsp table) (natp k))
            (equal (fn-arpn-pins-of k (mv-nth 0 (fn-hd-keyed-step table ev)))
                   (cond ((equal ev (list :hold k)) (+ 1 (fn-arpn-pins-of k table)))
                         ((and (equal ev (list :drop k))
                               (equal (mv-nth 1 (fn-hd-keyed-step table ev)) :dropped))
                          (- (fn-arpn-pins-of k table) 1))
                         (t (fn-arpn-pins-of k table)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-arpn-pins-of-pin-at fn-arpn-pins-of-unpin-at
                                fn-arpn-pin-at fn-arpn-unpin-at fn-arpn-pins-of)
            :use ((:instance fn-arpn-pins-of-pin-at (h k) (g (cadr ev)) (pins table))
                  (:instance fn-arpn-pins-of-unpin-at (h k) (g (cadr ev)) (pins table))
                  (:instance fn-hd-two-list))))))

; KEYSTONE.  Over any run of keyed events, a key's count is what it was,
; plus the holds of it, less the drops of it answered :dropped.  From the
; empty table (fn-hd-initial-is-quiet) a quiet key is one whose every hold
; was dropped: no holder of it is reachable, which is what a forget or a
; close may rely on.
(defthm fn-hd-run-count-is-holds-less-drops
  (implies (and (fn-arpn-pinsp table) (natp k))
           (equal (fn-arpn-pins-of k (fn-hd-run table evs))
                  (+ (fn-arpn-pins-of k table)
                     (fn-hd-holds-of k evs)
                     (- (fn-hd-drops-of k evs (fn-hd-run-answers table evs))))))
  :hints (("Goal" :induct (fn-hd-run-answers table evs)
           :in-theory (e/d (fn-hd-run fn-hd-run-answers fn-hd-holds-of fn-hd-drops-of)
                           (fn-hd-keyed-step mv-nth)))))

(defthm fn-hd-quiet-from-empty-means-every-hold-was-dropped
  (implies (and (natp k)
                (equal (fn-arpn-pins-of k (fn-hd-run (fn-hd-initial) evs)) 0))
           (equal (fn-hd-holds-of k evs)
                  (fn-hd-drops-of k evs (fn-hd-run-answers (fn-hd-initial) evs))))
  :hints (("Goal" :use ((:instance fn-hd-run-count-is-holds-less-drops
                                   (table (fn-hd-initial))))
           :in-theory (disable fn-hd-run-count-is-holds-less-drops fn-hd-run
                               fn-hd-run-answers fn-hd-keyed-step))))

(in-theory (disable fn-hd-keyed-step fn-hd-initial fn-hd-run fn-hd-run-answers))

; ---------------------------------------------------------------------------
; The identified step: a token per holder (c05).  A count knows how many
; hold a key, not who: two holders A and B of K count 2, A drops, and a
; DUPLICATE drop by A would take B's hold.  The identified table keeps, per
; key, the tokens of its holders (a cold read's token, a connection's id), so
; a hold by a token already holding is refused and a drop by a token not
; holding is refused -- the late or duplicate holder by name -- and the count
; is the number of tokens.
;
; TABLE = ((KEY . TOKENS) ...), KEY a natural, TOKENS a non-empty list with
; no duplicates; one row per key.  Not ordered: a key is found by assoc (the
; live keys are bounded by the live holders, a work bound).

; K's row, or nil (guard t: the recognizer below uses it).
(defun fn-hd-ident-row (k table)
  (declare (xargs :guard t))
  (cond ((atom table) nil)
        ((and (consp (car table)) (equal (caar table) k)) (car table))
        (t (fn-hd-ident-row k (cdr table)))))

(defun fn-hd-identp (table)
  (declare (xargs :guard t))
  (if (atom table)
      (null table)
    (and (consp (car table))
         (natp (caar table))
         (consp (cdar table))
         (true-listp (cdar table))
         (no-duplicatesp-equal (cdar table))
         (not (fn-hd-ident-row (caar table) (cdr table)))
         (fn-hd-identp (cdr table)))))

(defun fn-hd-tokens-of (k table)
  (declare (xargs :guard t))
  (cdr (fn-hd-ident-row k table)))

(defun fn-hd-ident-count (k table)
  (declare (xargs :guard (fn-hd-identp table)))
  (len (fn-hd-tokens-of k table)))

; K's row with TOKENS (dropped when TOKENS is empty), the other rows as they were.
(defun fn-hd-ident-put (k tokens table)
  (declare (xargs :guard (and (fn-hd-identp table) (true-listp tokens))))
  (cond ((atom table) (if (consp tokens) (list (cons k tokens)) nil))
        ((equal (caar table) k)
         (if (consp tokens) (cons (cons k tokens) (cdr table)) (cdr table)))
        (t (cons (car table) (fn-hd-ident-put k tokens (cdr table))))))

; Answers (mv TABLE' ANSWER):
;   (:hold K TOK)   TOK holds K once more: :held; TOK already holds K: :refused
;   (:drop K TOK)   TOK's hold of K ends: :dropped; TOK does not hold K: :refused
;   (:count K)      the holders of K
;   (:quiet K)      whether nobody holds K
; Any other event is :refused and TABLE unchanged.
(defun fn-hd-ident-step (table ev)
  (declare (xargs :guard (fn-hd-identp table)))
  (cond
   ((not (and (consp ev) (consp (cdr ev)) (natp (cadr ev))))
    (mv table :refused))
   ((and (member-eq (car ev) '(:hold :drop)) (not (and (consp (cddr ev)) (null (cdddr ev)))))
    (mv table :refused))
   ((and (member-eq (car ev) '(:count :quiet)) (not (null (cddr ev))))
    (mv table :refused))
   (t
    (let* ((k (cadr ev)) (tokens (fn-hd-tokens-of k table)))
      (case (car ev)
        (:hold (let ((tok (caddr ev)))
                 (if (member-equal tok tokens)
                     (mv table :refused)
                   (mv (fn-hd-ident-put k (cons tok tokens) table) :held))))
        (:drop (let ((tok (caddr ev)))
                 (if (member-equal tok tokens)
                     (mv (fn-hd-ident-put k (remove1-equal tok tokens) table) :dropped)
                   (mv table :refused))))
        (:count (mv table (len tokens)))
        (:quiet (mv table (atom tokens)))
        (otherwise (mv table :refused)))))))

(local
 (defthm fn-hd-identp-true-listp
   (implies (fn-hd-identp table) (true-listp table))
   :rule-classes :forward-chaining))

(local
 (defthm fn-hd-tokens-of-shape
   (implies (fn-hd-identp table)
            (and (true-listp (fn-hd-tokens-of k table))
                 (no-duplicatesp-equal (fn-hd-tokens-of k table))))
   :hints (("Goal" :induct (fn-hd-identp table)))))

(local
 (defthm fn-hd-row-of-ident-put
   (implies (fn-hd-identp table)
            (equal (fn-hd-ident-row h (fn-hd-ident-put k tokens table))
                   (if (equal h k)
                       (if (consp tokens) (cons k tokens) nil)
                     (fn-hd-ident-row h table))))
   :hints (("Goal" :induct (fn-hd-ident-put k tokens table)))))

; The tokens of H after K's row is put: K's new tokens (none when empty),
; every other key's as they were.
(local
 (defthm fn-hd-tokens-of-ident-put
   (implies (fn-hd-identp table)
            (equal (fn-hd-tokens-of h (fn-hd-ident-put k tokens table))
                   (if (equal h k)
                       (if (consp tokens) tokens nil)
                     (fn-hd-tokens-of h table))))
   :hints (("Goal" :in-theory (e/d (fn-hd-tokens-of) (fn-hd-ident-put fn-hd-ident-row))))))

(local
 (defthm fn-hd-ident-put-keeps-identp
   (implies (and (fn-hd-identp table) (natp k) (true-listp tokens)
                 (no-duplicatesp-equal tokens))
            (fn-hd-identp (fn-hd-ident-put k tokens table)))
   :hints (("Goal" :induct (fn-hd-ident-put k tokens table)))))

(local
 (defthm fn-hd-member-of-remove1
   (implies (member-equal b (remove1-equal a x))
            (member-equal b x))))

(local
 (defthm fn-hd-true-listp-of-remove1
   (implies (true-listp x)
            (true-listp (remove1-equal a x)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm fn-hd-no-duplicates-of-remove1
   (implies (no-duplicatesp-equal x)
            (no-duplicatesp-equal (remove1-equal a x)))
   :hints (("Goal" :induct (remove1-equal a x)))))

(local
 (defthm fn-hd-tokens-of-natp-key
   ; a row found under the recognizer has a natural key: the step's natp
   ; test is what fn-hd-ident-put needs
   (implies (and (fn-hd-identp table) (fn-hd-ident-row k table))
            (natp (caar (list (fn-hd-ident-row k table)))))
   :rule-classes nil))

(defthm fn-hd-ident-step-preserves-table
  (implies (fn-hd-identp table)
           (fn-hd-identp (mv-nth 0 (fn-hd-ident-step table ev))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-hd-ident-put fn-hd-ident-row fn-hd-tokens-of-shape
                               fn-hd-ident-put-keeps-identp)
           :use ((:instance fn-hd-tokens-of-shape (k (cadr ev)))
                 (:instance fn-hd-ident-put-keeps-identp
                            (k (cadr ev)) (tokens (cons (caddr ev) (fn-hd-tokens-of (cadr ev) table))))
                 (:instance fn-hd-ident-put-keeps-identp
                            (k (cadr ev)) (tokens (remove1-equal (caddr ev) (fn-hd-tokens-of (cadr ev) table))))))))

; A hold by a token adds exactly that token to its key: the key's tokens gain
; TOK, every other key's tokens are unchanged.
(defthm fn-hd-ident-hold-adds-exactly-its-token
  (implies (and (fn-hd-identp table) (natp k)
                (not (member-equal tok (fn-hd-tokens-of k table))))
           (let ((r (fn-hd-ident-step table (list :hold k tok))))
             (and (equal (mv-nth 1 r) :held)
                  (equal (fn-hd-tokens-of h (mv-nth 0 r))
                         (if (equal h k)
                             (cons tok (fn-hd-tokens-of k table))
                           (fn-hd-tokens-of h table))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-hd-ident-put fn-hd-ident-row fn-hd-row-of-ident-put
                               fn-hd-tokens-of-ident-put)
           :use ((:instance fn-hd-tokens-of-ident-put (k k)
                            (tokens (cons tok (fn-hd-tokens-of k table))))))))

; A drop by a holding token removes exactly that token.
(defthm fn-hd-ident-drop-removes-exactly-its-token
  (implies (and (fn-hd-identp table) (natp k)
                (member-equal tok (fn-hd-tokens-of k table)))
           (let ((r (fn-hd-ident-step table (list :drop k tok))))
             (and (equal (mv-nth 1 r) :dropped)
                  (equal (fn-hd-tokens-of h (mv-nth 0 r))
                         (if (equal h k)
                             (remove1-equal tok (fn-hd-tokens-of k table))
                           (fn-hd-tokens-of h table))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-hd-ident-put fn-hd-ident-row fn-hd-row-of-ident-put
                               fn-hd-tokens-of-ident-put)
           :use ((:instance fn-hd-tokens-of-ident-put (k k)
                            (tokens (remove1-equal tok (fn-hd-tokens-of k table))))
                 (:instance fn-hd-tokens-of-shape)))))

; KEYSTONE (the duplicate and the late holder, by name).  A hold by a token
; that already holds the key, and a drop by a token that does not, are
; refused and change nothing: a duplicate drop by A can never take B's hold.
(defthm fn-hd-ident-duplicate-hold-is-refused
  (implies (member-equal tok (fn-hd-tokens-of k table))
           (equal (mv-list 2 (fn-hd-ident-step table (list :hold k tok)))
                  (list table :refused))))

(defthm fn-hd-ident-drop-of-absent-token-is-refused
  (implies (not (member-equal tok (fn-hd-tokens-of k table)))
           (equal (mv-list 2 (fn-hd-ident-step table (list :drop k tok)))
                  (list table :refused))))

; The count is the tokens: a key is quiet exactly when no token holds it.
(defthm fn-hd-ident-quiet-is-no-token
  (implies (natp k)
           (equal (mv-nth 1 (fn-hd-ident-step table (list :quiet k)))
                  (atom (fn-hd-tokens-of k table)))))

(in-theory (disable fn-hd-ident-row fn-hd-identp fn-hd-tokens-of fn-hd-ident-count
                    fn-hd-ident-put fn-hd-ident-step))

; ---------------------------------------------------------------------------
; The form.

(defconst *fn-hd-keys* '(:shape :key :holders :effect :complete-by :trace))

(defconst *fn-hd-shapes* '(:keyed :stamped))

(defconst *fn-hd-entry-keys* '(:table :result :key :ok :when :keeps))

(defun fn-hd-get (key kvs)
  (declare (xargs :mode :program))
  (cadr (assoc-keyword key kvs)))

(defun fn-hd-entry-formp (x)
  (declare (xargs :mode :program))
  ; (FN THM :table I :result P :key K :ok OK)
  (and (true-listp x) (consp (cdr x))
       (symbolp (car x)) (car x) (symbolp (cadr x)) (cadr x)
       (keyword-value-listp (cddr x))
       (null (fn-cd-unknown-keys (cddr x) *fn-hd-entry-keys*))
       (natp (fn-hd-get :table (cddr x)))
       (assoc-keyword :result (cddr x))
       (assoc-keyword :ok (cddr x))
       (symbolp (fn-hd-get :keeps (cddr x)))
       ; an arm selector needs the instance's own preservation theorem
       (or (not (assoc-keyword :when (cddr x))) (fn-hd-get :keeps (cddr x)))))

; A root's status: :repinned (rebuilt at every retirement), :pinned (it
; pins a generation before it copies), :serialized (it never outlives the
; owner's quantum), :excluded (the release is refused while it names the
; key: a checked clause of the release's precondition), :unwired (no served
; path reaches it yet).
(defconst *fn-hd-root-statuses* '(:repinned :pinned :serialized :excluded :unwired))

(defun fn-hd-holder-formp (x)
  (declare (xargs :mode :program))
  ; (KIND :acquire ENTRY :release ENTRY)
  ; | (KIND :host t :acquire FNN :release FNN :in (FNN ...))
  ; | (KIND :root t :in (FNN ...) :status (WORD "why"))
  (and (true-listp x) (consp x) (symbolp (car x)) (car x)
       (keyword-value-listp (cdr x))
       (cond
        ((fn-hd-get :host (cdr x))
         (and (null (fn-cd-unknown-keys (cdr x) '(:host :acquire :release :in)))
              (symbolp (fn-hd-get :acquire (cdr x))) (fn-hd-get :acquire (cdr x))
              (symbolp (fn-hd-get :release (cdr x))) (fn-hd-get :release (cdr x))
              (symbol-listp (fn-hd-get :in (cdr x))) (fn-hd-get :in (cdr x))))
        ((fn-hd-get :root (cdr x))
         (and (null (fn-cd-unknown-keys (cdr x) '(:root :in :status)))
              (symbol-listp (fn-hd-get :in (cdr x))) (fn-hd-get :in (cdr x))
              (let ((status (fn-hd-get :status (cdr x))))
                (and (true-listp status) (equal (len status) 2)
                     (member-eq (car status) *fn-hd-root-statuses*)
                     (stringp (cadr status)) (< 0 (length (cadr status)))))))
        (t
         (and (null (fn-cd-unknown-keys (cdr x) '(:acquire :release)))
              (fn-hd-entry-formp (fn-hd-get :acquire (cdr x)))
              (fn-hd-entry-formp (fn-hd-get :release (cdr x))))))))

(defun fn-hd-holders-formp (x)
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (fn-hd-holder-formp (car x)) (fn-hd-holders-formp (cdr x)))))

(defun fn-hd-effect-formp (x)
  (declare (xargs :mode :program))
  (and (true-listp x)
       (case (car x)
         (:process-local (and (equal (len x) 2) (stringp (cadr x)) (< 0 (length (cadr x)))))
         (:durable (and (equal (len x) 3) (symbolp (cadr x)) (cadr x)
                        (stringp (caddr x)) (< 0 (length (caddr x)))))
         (:physical (and (equal (len x) 6) (symbolp (cadr x)) (cadr x)
                         (eq (caddr x) :cut) (keywordp (cadddr x))
                         (eq (nth 4 x) :after) (keywordp (nth 5 x))))
         (otherwise nil))))

(defun fn-hd-refusal (name kvs)
  (declare (xargs :mode :program))
  ; nil when the form is well-formed; else (REASON . DETAILS)
  (cond
   ((not (and (symbolp name) name)) (list :bad-name name))
   ((not (keyword-value-listp kvs)) (list :bad-options kvs))
   ((fn-cd-unknown-keys kvs *fn-hd-keys*)
    (cons :unknown-keyword (fn-cd-unknown-keys kvs *fn-hd-keys*)))
   ((not (member-eq (fn-hd-get :shape kvs) *fn-hd-shapes*))
    (list :bad-shape (fn-hd-get :shape kvs)))
   ((not (and (stringp (fn-hd-get :key kvs)) (< 0 (length (fn-hd-get :key kvs)))))
    (list :no-key name))
   ((not (fn-hd-holders-formp (fn-hd-get :holders kvs)))
    (list :bad-holders (fn-hd-get :holders kvs)))
   ((null (fn-hd-get :holders kvs)) (list :no-holders name))
   ((not (fn-hd-effect-formp (fn-hd-get :effect kvs)))
    (list :bad-effect (fn-hd-get :effect kvs)))
   ((and (assoc-keyword :complete-by kvs)
         (not (and (stringp (fn-hd-get :complete-by kvs))
                   (< 0 (length (fn-hd-get :complete-by kvs))))))
    (list :bad-complete-by (fn-hd-get :complete-by kvs)))
   ((not (member-eq (fn-hd-get :trace kvs) '(t nil)))
    (list :bad-trace (fn-hd-get :trace kvs)))
   (t nil)))

(defun fn-hd-refusal-text (reason)
  (declare (xargs :mode :program))
  (case (car reason)
    (:bad-shape (msg ":shape ~x0 is not one of ~&1." (cadr reason) *fn-hd-shapes*))
    (:no-key (msg "~x0 has no :key \"what one key is\"." (cadr reason)))
    (:bad-holders (msg ":holders ~x0 is not ((KIND :acquire (FN THM :table I :result P ~
                        :key K :ok OK) :release (...)) | (KIND :host t :acquire FNN ~
                        :release FNN :in (FNN ...)) | (KIND :root t :in (FNN ...) :status ~
                        (~&1 \"why\")) ...)." (cadr reason) *fn-hd-root-statuses*))
    (:no-holders (msg "~x0 declares no holder: a resource nobody holds needs no ~
                       declaration." (cadr reason)))
    (:bad-effect (msg ":effect ~x0 is not (:process-local \"why\"), (:durable PROGRAM ~
                       \"cut\") or (:physical CUTS :cut K :after K2)." (cadr reason)))
    (:bad-complete-by (msg ":complete-by ~x0 is not a string." (cadr reason)))
    (:bad-trace (msg ":trace ~x0 is not t or nil." (cadr reason)))
    (:unknown-keyword (msg "unknown keyword(s) ~&0; the keywords are ~&1."
                           (cdr reason) *fn-hd-keys*))
    (otherwise (msg "malformed form: ~x0." reason))))

; ---------------------------------------------------------------------------
; The generated statements, from the world.

(defun fn-hd-tablep (shape)
  (declare (xargs :mode :program))
  (if (eq shape :stamped) 'fn-arpn-okp 'fn-arpn-pinsp))

(defun fn-hd-event-term (shape verb k)
  (declare (xargs :mode :program))
  ; the translated event term the entry performs: K is a translated term
  (case shape
    (:stamped (if (eq verb :acquire)
                  (kwote (list :pin))
                (list 'cons (kwote :unpin) (list 'cons k *nil*))))
    (otherwise (list 'cons (kwote (if (eq verb :acquire) :hold :drop))
                     (list 'cons k *nil*)))))

(defun fn-hd-step-fn (shape)
  (declare (xargs :mode :program))
  (if (eq shape :stamped) 'fn-arpn-step 'fn-hd-keyed-step))

(defun fn-hd-normal-entry (name kind verb shape entry w)
  (declare (xargs :mode :program))
  ; (mv MSG ENTRY'): (FN THM :name N :keeps N2 :table I :result P' :key K' :ok OK')
  ; with the terms translated
  (let* ((fn (car entry))
         (thm (cadr entry))
         (opts (cddr entry))
         (i (fn-hd-get :table opts))
         (formals (getpropc fn 'formals :none w)))
    (cond
     ((eq formals :none) (mv (msg "~x0 is not a function in this world" fn) nil))
     ((null (getpropc thm 'theorem nil w))
      (mv (msg "~x0 names ~x1, which is not a theorem in this world" fn thm) nil))
     ((and (fn-hd-get :keeps opts) (null (getpropc (fn-hd-get :keeps opts) 'theorem nil w)))
      (mv (msg "~x0 names :keeps ~x1, which is not a theorem in this world"
               fn (fn-hd-get :keeps opts))
          nil))
     ((not (< i (len formals)))
      (mv (msg "~x0 has ~x1 formals; :table ~x2 is none of them" fn (len formals) i) nil))
     (t
      (mv-let (bad terms)
        (fn-cd-translate-list (list (fn-hd-get :result opts) (fn-hd-get :ok opts)
                                    (fn-hd-get :key opts)
                                    (if (assoc-keyword :when opts) (fn-hd-get :when opts) t))
                              w)
        (cond
         (bad (mv (msg "~x0: ~x1 does not translate in this world" fn (car bad)) nil))
         ((not (equal (all-vars (car terms)) '(_)))
          (mv (msg "~x0's :result ~x1 is not a term over `_' (the call) alone"
                   fn (fn-hd-get :result opts))
              nil))
         ((not (equal (all-vars (cadr terms)) '(_)))
          (mv (msg "~x0's :ok ~x1 is not a term over `_' (the call) alone"
                   fn (fn-hd-get :ok opts))
              nil))
         ((not (subsetp-eq (all-vars (caddr terms)) formals))
          (mv (msg "~x0's :key ~x1 mentions variables that are not its formals ~x2"
                   fn (fn-hd-get :key opts) formals)
              nil))
         ((not (subsetp-eq (all-vars (cadddr terms)) formals))
          (mv (msg "~x0's :when ~x1 mentions variables that are not its formals ~x2"
                   fn (fn-hd-get :when opts) formals)
              nil))
         (t (mv nil (list fn thm
                          :name (packn-pos (list name '- kind '- verb
                                                 (if (eq verb :acquire) '-holds '-drops))
                                           name)
                          :keeps (packn-pos (list name '- kind '- verb '-keeps) name)
                          :keeps-by (fn-hd-get :keeps opts)
                          :table i :result (car terms) :ok (cadr terms) :key (caddr terms)
                          :when (cadddr terms)
                          :shape shape)))))))))

(defun fn-hd-entry-call (entry w)
  (declare (xargs :mode :program))
  (cons (car entry) (getpropc (car entry) 'formals nil w)))

(defun fn-hd-entry-table (entry w)
  (declare (xargs :mode :program))
  (nth (fn-hd-get :table (cddr entry)) (getpropc (car entry) 'formals nil w)))

(defun fn-hd-entry-result (entry w)
  (declare (xargs :mode :program))
  (fn-cd-subst (fn-hd-get :result (cddr entry)) (list (cons '_ (fn-hd-entry-call entry w)))))

(defun fn-hd-entry-ok (entry w)
  (declare (xargs :mode :program))
  (fn-cd-subst (fn-hd-get :ok (cddr entry)) (list (cons '_ (fn-hd-entry-call entry w)))))

; Each generated statement in two parts, HYPS (translated terms) and the
; CONCLUSION: the theorem is (implies (and . HYPS) CONCLUSION) in the
; translated form (fn-cd-conj), and the teeth CLAIM the same in the source
; form `(implies (and H ...) C)' GENERATORS' defteeth binds labels to
; (lanedumps/generators-2.md v1): its translation is the theorem, so the
; owed row and the world agree by construction.
(defun fn-hd-holds-parts (verb entry w)
  (declare (xargs :mode :program))
  ; (mv HYPS CONCLUSION): (implies (and G W) (equal RESULT (if OK (mv-nth 0 (STEP TABLE EVENT)) TABLE)))
  (let* ((fn (car entry))
         (guard (getpropc fn 'guard *t* w))
         (when (fn-hd-get :when (cddr entry)))
         (table (fn-hd-entry-table entry w))
         (shape (fn-hd-get :shape (cddr entry)))
         (step (list (fn-hd-step-fn shape) table
                     (fn-hd-event-term shape verb (fn-hd-get :key (cddr entry)))))
         (conclusion (list 'equal (fn-hd-entry-result entry w)
                           (list 'if (fn-hd-entry-ok entry w)
                                 (list 'mv-nth (kwote 0) step)
                                 table))))
    (mv (append (if (equal guard *t*) nil (list guard))
                (if (equal when *t*) nil (list when)))
        conclusion)))

(defun fn-hd-keeps-parts (entry w)
  (declare (xargs :mode :program))
  ; (mv HYPS CONCLUSION): (implies (and (TABLEP TABLE) G) (TABLEP RESULT))
  (let* ((fn (car entry))
         (guard (getpropc fn 'guard *t* w))
         (table (fn-hd-entry-table entry w))
         (tablep (fn-hd-tablep (fn-hd-get :shape (cddr entry)))))
    (mv (cons (list tablep table) (if (equal guard *t*) nil (list guard)))
        (list tablep (fn-hd-entry-result entry w)))))

(defun fn-hd-statement (hyps conclusion)
  (declare (xargs :mode :program))
  (if hyps (list 'implies (fn-cd-conj hyps) conclusion) conclusion))

(defun fn-hd-claim (hyps conclusion)
  (declare (xargs :mode :program))
  (if hyps (list 'implies (cons 'and hyps) conclusion) conclusion))

(defun fn-hd-holds-statement (verb entry w)
  (declare (xargs :mode :program))
  (mv-let (hyps conclusion) (fn-hd-holds-parts verb entry w)
    (fn-hd-statement hyps conclusion)))

(defun fn-hd-keeps-statement (entry w)
  (declare (xargs :mode :program))
  (mv-let (hyps conclusion) (fn-hd-keeps-parts entry w)
    (fn-hd-statement hyps conclusion)))

(defun fn-hd-normal-holders (name shape holders w)
  (declare (xargs :mode :program))
  ; (mv MSG HOLDERS'): each (KIND :host t ...) as given, each logic holder
  ; with its two entries normalized
  (if (atom holders)
      (mv nil nil)
    (let ((kind (caar holders)) (opts (cdar holders)))
      (if (or (fn-hd-get :host opts) (fn-hd-get :root opts))
          (mv-let (msg rest) (fn-hd-normal-holders name shape (cdr holders) w)
            (mv msg (cons (car holders) rest)))
        (mv-let (msg a) (fn-hd-normal-entry name kind :acquire shape (fn-hd-get :acquire opts) w)
          (if msg
              (mv msg nil)
            (mv-let (msg r) (fn-hd-normal-entry name kind :release shape (fn-hd-get :release opts) w)
              (if msg
                  (mv msg nil)
                (mv-let (msg rest) (fn-hd-normal-holders name shape (cdr holders) w)
                  (mv msg (cons (list kind :acquire a :release r) rest)))))))))))

(defun fn-hd-logic-entries (holders)
  (declare (xargs :mode :program))
  ; ((VERB . ENTRY) ...) of the normalized logic holders
  (cond ((atom holders) nil)
        ((or (fn-hd-get :host (cdar holders)) (fn-hd-get :root (cdar holders)))
         (fn-hd-logic-entries (cdr holders)))
        (t (list* (cons :acquire (fn-hd-get :acquire (cdar holders)))
                  (cons :release (fn-hd-get :release (cdar holders)))
                  (fn-hd-logic-entries (cdr holders))))))

(defun fn-hd-entries-problem (entries generatedp w)
  (declare (xargs :mode :program))
  ; the first generated name whose formula is not the regenerated statement
  (if (atom entries)
      nil
    (let* ((verb (caar entries)) (entry (cdar entries)) (opts (cddr entry)))
      (or (and generatedp
               (fn-cd-generated-problem (fn-hd-get :name opts) (fn-hd-holds-statement verb entry w) w))
          (and generatedp
               (fn-cd-generated-problem (fn-hd-get :keeps opts) (fn-hd-keeps-statement entry w) w))
          (fn-hd-entries-problem (cdr entries) generatedp w)))))

; A :durable effect's program must name the cut: the string is found in the
; program's body (its step list is literal data there).
(defun fn-hd-tree-has-string (s tree)
  (declare (xargs :mode :program))
  (cond ((equal tree s) t)
        ((consp tree) (or (fn-hd-tree-has-string s (car tree))
                          (fn-hd-tree-has-string s (cdr tree))))
        (t nil)))

(defun fn-hd-effect-problem (effect w)
  (declare (xargs :mode :program))
  (case (car effect)
    (:durable
     (let* ((program (cadr effect))
            (body (getpropc program 'unnormalized-body :none w)))
       (cond ((eq body :none)
              (msg ":durable names ~x0, which is not a function in this world" program))
             ((not (fn-hd-tree-has-string (caddr effect) body))
              (msg ":durable names cut ~x0 of ~x1, whose body does not name it: a holder's ~
                    durable release is a step of a byte-model program, declared there first"
                   (caddr effect) program))
             (t nil))))
    (:physical
     ; (:physical CUTS :cut K :after K2): CUTS a defconst whose value lists K2
     ; strictly before K
     (let* ((cuts (cadr effect)) (k (cadddr effect)) (k2 (nth 5 effect))
            (val (getpropc cuts 'const :none w))
            (lst (and (not (eq val :none)) (consp val) (eq (car val) 'quote) (cadr val))))
       (cond ((eq val :none)
              (msg ":physical names ~x0, which is not a defconst of this world" cuts))
             ((not (keyword-listp lst))
              (msg ":physical names ~x0, whose value is not a list of keyword cuts" cuts))
             ((not (member-eq k lst))
              (msg ":physical: cut ~x0 is not in ~x1" k cuts))
             ((not (member-eq k2 lst))
              (msg ":physical: the durable replacement ~x0 is not in ~x1" k2 cuts))
             ((not (< (position-eq k2 lst) (position-eq k lst)))
              (msg ":physical: the release ~x0 must come after the durable replacement ~x1 in ~
                    ~x2, else a death between them loses storage the replacement still ~
                    needs" k k2 cuts))
             (t nil))))
    (otherwise nil)))

(defun fn-hd-problem (name row generatedp w)
  (declare (xargs :mode :program))
  ; nil, or a msg naming the first check the world refutes for the normalized ROW
  (let ((entries (fn-hd-logic-entries (fn-hd-get :holders row))))
    (cond
     ((fn-hd-effect-problem (fn-hd-get :effect row) w))
     ((fn-hd-entries-problem entries generatedp w))
     ((and entries (null (fn-hd-get :complete-by row)))
      (msg "~x0 declares logic holders over a value table, so the world cannot say which ~
            entries thread it: say :complete-by \"why the holder list is complete\"" name))
     (t nil))))

(defun fn-hd-declare (name kvs w)
  (declare (xargs :mode :program))
  ; (mv MSG ROW): the normalized row of a well-formed declaration
  (cond
   ((assoc-eq name (table-alist 'fn-holder w))
    (mv (msg "~x0 is already a declared holder relation of this world; a row is ~
              declared once" name)
        nil))
   (t
    (mv-let (msg holders)
      (fn-hd-normal-holders name (fn-hd-get :shape kvs) (fn-hd-get :holders kvs) w)
      (if msg
          (mv msg nil)
        (let ((row (list :shape (fn-hd-get :shape kvs)
                         :key (fn-hd-get :key kvs)
                         :holders holders
                         :effect (fn-hd-get :effect kvs)
                         :complete-by (fn-hd-get :complete-by kvs)
                         :trace (not (and (assoc-keyword :trace kvs)
                                          (null (fn-hd-get :trace kvs))))
                         :cuts (if (eq (car (fn-hd-get :effect kvs)) :physical)
                                   ; the cut list's own names: the durable
                                   ; replacement, then the release
                                   (list (nth 5 (fn-hd-get :effect kvs))
                                         (cadddr (fn-hd-get :effect kvs)))
                                 (list (intern-in-package-of-symbol
                                        (concatenate 'string (symbol-name name) "-DECIDED") :key)
                                       (intern-in-package-of-symbol
                                        (concatenate 'string (symbol-name name) "-RELEASED") :key))))))
          (mv (fn-hd-problem name row nil w) row)))))))

; ---------------------------------------------------------------------------
; The events.

(defun fn-hd-entry-defthms (entries w)
  (declare (xargs :mode :program))
  (if (atom entries)
      nil
    (let* ((verb (caar entries)) (entry (cdar entries)) (opts (cddr entry))
           (shape (fn-hd-get :shape opts))
           (preserved (if (eq shape :stamped)
                          'fn-arpn-step-preserves-okp
                        'fn-hd-keyed-step-preserves-table)))
      (list* `(defthm ,(fn-hd-get :name opts) ,(fn-hd-holds-statement verb entry w)
                :hints (("Goal" :use ,(cadr entry) :in-theory (theory 'minimal-theory)))
                :rule-classes nil)
             ; the debt (GENERATORS' v1 staging): what the teeth must say
             `(table fn-teeth-owed ',(fn-hd-get :name opts)
                     '(:by def-holder
                       :claim ,(mv-let (hyps conclusion) (fn-hd-holds-parts verb entry w)
                                 (fn-hd-claim hyps conclusion))
                       :subject ,(car entry)))
             ; the preservation: from the declared :keeps theorem when the
             ; entry selects an arm, else from the holds/drops theorem and
             ; the generic preservation at the entry's own table and event,
             ; nothing else
             `(defthm ,(fn-hd-get :keeps opts) ,(fn-hd-keeps-statement entry w)
                :hints (("Goal" :use ,(if (fn-hd-get :keeps-by opts)
                                          (fn-hd-get :keeps-by opts)
                                        `(,(fn-hd-get :name opts)
                                          (:instance ,preserved
                                                     (,(if (eq shape :stamped) 'st 'table)
                                                      ,(fn-hd-entry-table entry w))
                                                     (ev ,(fn-hd-event-term shape verb
                                                                            (fn-hd-get :key opts))))))
                         :in-theory (theory 'minimal-theory)))
                :rule-classes nil)
             `(table fn-teeth-owed ',(fn-hd-get :keeps opts)
                     '(:by def-holder
                       :claim ,(mv-let (hyps conclusion) (fn-hd-keeps-parts entry w)
                                 (fn-hd-claim hyps conclusion))
                       :subject ,(car entry)))
             (fn-hd-entry-defthms (cdr entries) w)))))

(defun fn-hd-carried-transitions (entries seen)
  (declare (xargs :mode :program))
  ; the def-carried transitions: each entry FUNCTION once (one function may
  ; serve several arms) with its generated keeps theorem
  (cond ((atom entries) nil)
        ((member-eq (car (cdar entries)) seen)
         (fn-hd-carried-transitions (cdr entries) seen))
        (t (let* ((entry (cdar entries)) (opts (cddr entry)))
             (cons (list (car entry) (fn-hd-get :keeps opts)
                         :state (fn-hd-get :table opts)
                         :result (fn-hd-get :result opts))
                   (fn-hd-carried-transitions (cdr entries) (cons (car entry) seen)))))))

(defun fn-hd-events (name row w)
  (declare (xargs :mode :program))
  (let* ((shape (fn-hd-get :shape row))
         (entries (fn-hd-logic-entries (fn-hd-get :holders row)))
         (tablep (fn-hd-tablep shape))
         (initial (packn-pos (list name '-initial) name))
         (established (packn-pos (list name '-initial-establishes) name)))
    `(progn
       (table fn-holder ',name ',row)
       (defconst ,(packn-pos (list '* name '-cuts*) name) ',(fn-hd-get :cuts row))
       (table fn-holder-cuts ',name '(:effect ,(fn-hd-get :effect row) :cuts ,(fn-hd-get :cuts row)))
       ,@(fn-hd-entry-defthms entries w)
       ,@(and entries (fn-hd-get :trace row)
              `((defun ,initial ()
                  (declare (xargs :guard t))
                  ,(if (eq shape :stamped) '(fn-arpn-initial) '(fn-hd-initial)))
                (defthm ,established (,tablep (,initial))
                  :hints (("Goal" :in-theory (enable ,initial))))
                (def-carried ,(packn-pos (list name '-table) name)
                  :invariant ,tablep
                  :established ((,initial ,established))
                  :transitions ,(fn-hd-carried-transitions entries nil)
                  :complete-by (:enumeration ,(fn-hd-get :complete-by row))))))))

(defmacro def-holder (name &rest kvs)
  (let ((reason (fn-hd-refusal name kvs)))
    (if reason
        `(make-event (er soft 'def-holder "~x0: ~@1" ',name ',(fn-hd-refusal-text reason)))
      `(make-event
        (mv-let (problem row)
          (fn-hd-declare ',name ',kvs (w state))
          (if problem
              (er soft 'def-holder "~x0: ~@1" ',name problem)
            (value (fn-hd-events ',name row (w state)))))))))

; ---------------------------------------------------------------------------
; The checks in the world as now loaded.

; Every function of the world whose body calls a holder step, with the book
; that introduced it; the declared logic entries of every row; and the
; first caller that is neither declared nor introduced by this book or the
; table's.
(mutual-recursion
 (defun fn-hd-calls-step (term)
   (declare (xargs :mode :program))
   ; a translated TERM calls a holder step (a lambda application's body and
   ; actuals included)
   (cond ((atom term) nil)
         ((eq (car term) 'quote) nil)
         ((member-eq (car term) '(fn-hd-keyed-step fn-arpn-step)) t)
         ((consp (car term))
          (or (fn-hd-calls-step (caddr (car term))) (fn-hd-calls-step-lst (cdr term))))
         (t (fn-hd-calls-step-lst (cdr term)))))
 (defun fn-hd-calls-step-lst (terms)
   (declare (xargs :mode :program))
   (and (consp terms)
        (or (fn-hd-calls-step (car terms)) (fn-hd-calls-step-lst (cdr terms))))))

(defun fn-hd-declared-entries (rows)
  (declare (xargs :mode :program))
  (if (atom rows)
      nil
    (append (strip-cdrs (fn-hd-logic-entries (fn-hd-get :holders (cdar rows))))
            (fn-hd-declared-entries (cdr rows)))))

(defun fn-hd-declared-fns (rows)
  (declare (xargs :mode :program))
  (strip-cars (fn-hd-declared-entries rows)))

; The library's own callers of the keyed step: the run and its answers
; (above).  Exact: no other function of this book or of
; books/arena-reader-pins.lisp calls a step (fn-arpn-step is the step).
(defconst *fn-hd-library-callers* '(fn-hd-run fn-hd-run-answers))

(defun fn-hd-first-undeclared-caller (wrld declared)
  (declare (xargs :mode :program))
  (cond ((atom wrld) nil)
        ((and (eq (cadar wrld) 'unnormalized-body)
              (not (eq (cddar wrld) *acl2-property-unbound*))
              (fn-hd-calls-step (cddar wrld))
              (not (member-eq (caar wrld) declared))
              (not (member-eq (caar wrld) *fn-hd-library-callers*)))
         (caar wrld))
        (t (fn-hd-first-undeclared-caller (cdr wrld) declared))))

(defun fn-hd-check-problem (name w)
  (declare (xargs :mode :program))
  (let* ((rows (table-alist 'fn-holder w))
         (row (cdr (assoc-eq name rows)))
         (caller (fn-hd-first-undeclared-caller w (fn-hd-declared-fns rows))))
    (cond ((null row) (msg "no holder relation ~x0 in this world" name))
          ((fn-hd-problem name row t w))
          (caller
           (msg "~x0 calls a holder step and is no declared entry of any holder relation ~
                 (~&1): an undeclared acquirer is a refusal, not a holder"
                caller (strip-cars rows)))
          (t nil))))

(defmacro def-holder-check (name)
  `(make-event
    (let ((problem (fn-hd-check-problem ',name (w state))))
      (if problem
          (er soft 'def-holder-check "~x0: ~@1" ',name problem)
        (value '(value-triple ',name))))))
