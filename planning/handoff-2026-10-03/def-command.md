# CONTINUATION: lane def-command (Fable), wound down 2026-10-03 night at ember's request

START HERE. DC01 is LANDED (origin/dev 413a56c92 = Batch BM merge of lane/def-command 61e7d8751; on
next too). Worktree /Users/ember/dev/fn/build/lanes/def-command, branch lane/def-command, fast-forwarded
onto origin/dev (3e53a723b at wind-down; ff again first). Items DC02-DC05 in the repair ledger
(`python3 build/coordinator/repair/repair.py list --owner def-command`), all deferred until
SERVED-CATALOG-LIVE's SCL1/SCL4 land. Resume with:

1. `git -C build/lanes/def-command merge --ff-only origin/dev`; read books/protocol-served-table.lisp
   (the declarations) and books/protocol-served.lisp (the generator) headers; they say what is generated.
2. REPL: `FN_LANE=def-command python3 tools/proof_repl.py start pserv books/protocol-served --host hbox`
   (the table's closure is cached now; add `--ld books/protocol-served-table` only if its bytes changed).
   Teeth: `send '(include-book "../tests/acl2/must-fail-checked")'` then send-range of
   tests/acl2/protocol-served-tests.lisp --from '#5'; the two both-route forms need
   `(include-book "served-catalog-chain")` first.
3. DC03 (rows): NEXT/LAST = one form each with :by ((:instance fn-nntp-next-or-last-cat-is-next-or-last
   (direction :next|:last))) (proved in the session, 1,441 steps). LISTGROUP, ARTICLE family, LIST COUNTS:
   first EXPORT (drop `local`) fn-scat-built-listgroup-is-fold, fn-scat-pinned-number-line-is-number-
   retrieval, fn-scat-gidx-list-counts-is-fold in books/served-catalog-dispatch.lisp, then :by them.
   OVER/XOVER: re-declare from SCL1 (prelude form :cat = the cursor-returning fn-nntp-over-range-ovw with
   its SERVER formal; :by fn-nntp-over-range-ovw-expands-to-over-range-served-cat / -to-over-range-cat;
   fn-nntp-xref-reply-cat-is-col is :rule-classes nil modulo fn-ovw-expand). LIST: the row from SCL4's arm
   with :view :completed (its :forms must mention the completed-view formal; add it to
   *fn-proto-cat-formals* once, it is ONE formal by agreement).
4. DC02 (switch): fn-scr-command (served-catalog-chain.lisp:249) calls fn-proto-archive-command-cat;
   delete the hand cond and the 78-line hint list in served-catalog-dispatch.lisp (keep its local
   lemmas, now exported); fn-nntp-archive-command-cat-is-pinned's name is then the generated
   keystone's (rename fn-proto-archive-command-cat-is-pinned, keep PRF-202/346 citations); define
   fn-served-advance-eventp's keyword list and fn-nntp-archive-keywordp from *fn-proto-select-names* /
   *fn-proto-archive-names* (served.lisp, nntp.lisp): that is the net-negative diff. Certify
   --affected-by books/served-catalog-dispatch.lisp; natives reader_clients/over_pins on an image at
   the sha (the served path changes at this step).
5. DC04: generate fn-nntp-archive-pinned-arms (nntp.lisp) from the protocol table's :arms.
6. DC05 is policy owners' work (PRF-1237/1238 completion criteria); the generator's part is the
   :completed / :pin-or-completed forms and the two-context boundary replacing the keystone.

Facts worth keeping: every protocol-table.lisp edit recertifies 753 roots (keep served columns in the
served table); protocol_emit --check refuses debt growth (tools/view_policy_debt.json; --write-debt
only shrinks); the ledger's proofs.json formatting must be the ledger's (run remote_check --regen on
hbox after any registry edit, then check-fast-lane); farm.py publish copies certs into persvati's cache
on its own (ember's no-writes rule: say so in the READY). Three pre-existing check-fast reds are
SWEEP-GATES' (CL20 spec_cite, test_roots withdrawal-index-carried-tests, main_last fixed on next).

Policy record: build/coordinator/decisions/command-view-policy-2026-10-03.md (table + c07 rulings +
DECISION block). The DATE defect (clock pinned at accept) is being fixed separately.

---- history below (the lane's running notes) ----

# Lane def-command (Fable deputy), 2026-10-03

Worktree /Users/ember/dev/fn/build/lanes/def-command, branch lane/def-command from
origin/dev 4aa332295. Deliverable: a served NNTP command is ONE declaration, from which
both routes' dispatch arms, the command's case of the pinned-boundary theorem, the view
policy's executable site, the spec/docs command table and the teeth skeleton are generated;
fail closed on a served keyword with no declaration or a declaration with no view policy.

Early deliverable (done): build/coordinator/decisions/command-view-policy-2026-10-03.md,
every served command's view policy from source, six findings A-F for ember.

## Interface sketch (one page; for the adversarial consultation)

THE DECLARATION IS THE PROTOCOL TABLE ROW. books/protocol-table.lisp already holds one
row per command and already generates the command layer (fn-nntp-command-dispatch), the
FAQ and the fuzzer grammar, through ONE non-evaluating reader (tools/ledger.py
defprotocol_expansion, tools/protocol_emit.py). A second table would be the drift the
brief forbids, so `def-nntp-command` is the row's shape, and `defprotocol`'s expansion
is the generator. New columns, all checked by fn-proto-rowp at certification:

    ("GROUP"
     :rfc "RFC 3977 6.1.1" :dispatch :archive ... :arms (:archive ...)   ; unchanged
     :view :select            ; REQUIRED on every row with :arms. One of
                              ;   :none      no view (session, auth; a constant)
                              ;   :pinned    the connection's pinned view (archive index v verdicts
                              ;              and the pinned config): NNT-042's "other reads"
                              ;   :select    re-pin to the owner's committed view before the arm,
                              ;              keep it iff 211 (GROUP, LISTGROUP)
                              ;   :completed the latest completed durable view, pin unmoved
                              ;              (LIST / ACTIVE / COUNTS once option A lands)
                              ;   :live-index the live Message-ID index (transit CHECK/IHAVE)
     :view-rfc "NNT-042; RFC 3977 6.1.1.2"     ; the policy's citation, into the spec table
     [:view-decided :completed]                ; a ruling not yet landed: shown, never executed
     :effect :select          ; :none | :select | :current (moves the current article) | :close | :offer
     :cat-arms ((TEST TERM) ...)   ; the UNRESTRICTED route: this row's clauses of the served
                              ; catalog dispatcher, over formals SESSION ARCHIVE INDEX VERDICTS ENV
                              ; KEYWORD ARGS V FN-ARENA FN-CAT (+ the completed-view formal when
                              ; served-catalog-live's signature lands: one constant)
     :cat-by (fn-nntp-group-result-cat-is-archive ...)   ; the hand -is- theorems the row's
                              ; boundary case is proved from (the only hand proofs; a clause that
                              ; is a def-carried-reader instance names that reader's keystone)
     :quantum nil | (:cursor fn-ovw-cursor-effectp)      ; the reply may be a cursor effect
     :teeth ("GROUP fn.mod.a" "GROUP fn.nowhere" "GROUP") ; lines the generated teeth evaluate
     ...)

GENERATED (books/protocol-served.lisp, new, built BESIDE the hand dispatchers; the switch
deletes them):
 1. fn-proto-archive-command-cat: one flat cond over the rows' :cat-arms (table order; keyword
    tests are exclusive, as protocol-dispatch.lisp proved for the pinned side), and per row
    fn-proto-cat-row-NAME-is-cat (= the hand fn-nntp-archive-command-cat under that keyword).
 2. THE BOUNDARY, per row: fn-proto-cat-row-NAME-is-pinned, (implies (and <the keystone's
    hypotheses> (fn-nntp-keywordp keyword "NAME")) <expanded-result equality with
    fn-nntp-archive-command-pinned>), hints = :use the row's :cat-by instances in the shared
    minimal theory; and fn-nntp-archive-command-cat-is-pinned re-proved as the generated case
    split (NAME and STATEMENT preserved: every ledger citation stays). The 90-line :use /
    :in-theory list of books/served-catalog-dispatch.lisp:286-363 goes.
 3. THE VIEW POLICY'S ONE EXECUTABLE SITE: the keyword disjunction of fn-served-advance-eventp
    (books/served.lisp:1146-1157) is generated from the rows with :view :select; the :completed
    rows generate the discovery-view test the chain branches on, once that branch exists.
 4. fn-nntp-archive-keywordp (nntp.lisp) from :dispatch; the HELP table *fn-nntp-served-command-
    table* (nntp-help.lisp) is checked set-equal to the table's served names (assert-event),
    so a keyword served without a row, or a row the dispatcher ignores, refuses certification.
 5. Step 2 (after the switch): the RESTRICTED route's archive dispatcher fn-nntp-archive-pinned-
    arms (hand macro, nntp.lisp) generated from :arms, so fn-proto-command-pinned-is-command-
    pinned holds by construction and the macro's 70 lines go.
 6. The spec table: tools/protocol_emit.py emits the new columns; tools/docs_check.py writes a
    generated region into specs/nntp.md ("The served command table": command, forms, view policy,
    decided-not-landed, effect, route per client kind, quantum, RFC) checked by make check.
 7. Teeth: tests/acl2/protocol-served-tests.lisp generated from :teeth (both routes vs the
    reference on the hostile archive, as protocol-dispatch-tests does), through GENERATORS'
    fn-teeth-events when it lands (a (table fn-teeth-owed NAME) row per generated keystone;
    defteeth-check refuses an owed keystone with no teeth), the pdt-agree shape until then.
 8. :quantum's meaning (own READY): the exposure scan counts a cursor effect as "answered"
    (books/public-exposure-reply.lisp fn-exp-effects-scan; the theorem fn-exp-effects-scan-is-
    the-reply-scan restated) and host/native/mux.lisp fnn-mux-plan-yield re-arms idle: finding E.

FAIL CLOSED, each by name at expansion: a row with :arms and no :view; :view :pinned whose
:cat-arms or :arms mention the live or completed formal; :view :completed whose :cat-arms do
not mention it; :cat-arms without :cat-by; :quantum on a row whose :cat-arms never emit a
cursor (checked by the teeth, not syntax); a HELP keyword with no row.

NOT GENERATED (stays hand-written, by design): the per-arm -is-archive / -is-col proofs in
books/served-catalog.lisp (the real content); the reference arms' bodies.

## Conversion order (coordination with SERVED-CATALOG-LIVE)

The sibling edits served-catalog-dispatch.lisp's LIST arm (option A), served-catalog.lisp's
group summary (reclaim) and served-plan-cursor.lisp / the OVER arm order (reachability). I
touch NONE of those until its READY lands: the generated dispatcher lives beside the hand
one with per-row equality lemmas. Three rows proved end to end first: XPAT (simple pinned
read), GROUP (selection: :view :select generates the advance keyword list), OVER/XOVER range
(cursor: over the hand arm as it is; the sibling's reorder is a row edit when it lands). Then
the switch (fn-scr-command calls the generated dispatcher; the hand cond deleted), then every
remaining row, then LIST/COUNTS/NEWGROUPS/NEWNEWS as :view :completed when their
implementation lands (:view-decided until then), then step 5.

Ask of the sibling (via the coordinator): keep the completed-view input ONE formal of the
-cat dispatcher, so the generator's formals constant is one line.

## State (2026-10-03 night): READY 1 LANDED on origin/dev as 413a56c92 (Batch BM merge of 61e7d8751; DC01). Lane rebased onto origin/dev (fast-forward).
- check-fast-lane at 61e7d8751: 8/11 ok; the 3 reds are origin/dev's (spec_cite_check CL20,
  test_roots_check withdrawal-index-carried-tests not in the Makefile, main_last_check
  tests/test_depth_check.py). merge_registry, ledger, current_view, docs_check, reach_check, host_check ok.
- Policy table: done, corrected per c07 (decisions/command-view-policy-2026-10-03.md).
- READY 1 = the generated served dispatcher + the protocol-table split, on lane/def-command:
  books/protocol-served-table.lisp (the served columns, defprotocol-served, fn-proto-served-tablep
  cross-check), books/protocol-served.lisp (the generator: XPAT, GROUP, OVER, XOVER declared as
  forms; per-form view contracts; the case-split keystone; the two view-site keystones; HELP
  set-equality assertion; fn-teeth-owed rows), tests/acl2/protocol-served-tests.lisp (hand teeth in
  the v1 shape), tools (protocol_emit join + debt ratchet + keyword-literal inventory, docs_check's
  spec region, ledger mirrors), specs/nntp.md's generated served command table, registry rows
  PRF-1236 (this) / PRF-1237 / PRF-1238 (the c07 rulings as debt), NNT-038/039/042 cites,
  Makefile roots, the manifest certify-20261002T232442Z-2105883 (hbox run-f0bd, 3/0).
  books/protocol-table.lisp is BYTE-IDENTICAL to origin/dev: no host file changed; the served path
  is unchanged until the switch (nothing calls fn-proto-archive-command-cat yet).
- Admitted in the REPL on hbox: generator forms 85.4k steps in all; teeth 44/44 (the two both-route
  reachability forms with served-catalog-chain included). check-fast-lane at the regen head: see the
  READY (the three pre-existing origin/dev reds listed there).
- NOTE for ember/coordinator: tools/farm.py's publish step copied the 3 new certificate entries
  into persvati:~/fn-certcache on its own (its default cross-publication), despite the no-writes
  rule; 3 small files. Not a deletion candidate for me.
- NEXT (after READY 1 lands): the switch (fn-scr-command calls the generated dispatcher; the hand
  cond + 78-line hint list in served-catalog-dispatch.lisp deleted; fn-nntp-archive-keywordp and
  fn-served-advance-eventp's keyword pair defined by the table's constants) once SERVED-CATALOG-LIVE's
  LIST arm lands as a row; the remaining rows (NEXT/LAST proved in the session from one :by each;
  LISTGROUP, the ARTICLE family and LIST COUNTS need served-catalog-dispatch's local lemmas exported);
  the restricted route's pinned-arms macro from :arms; :quantum naming the def-cursor instance when
  GENERATORS lands it; the two-context boundary with PRF-1237/1238's owner.
- Session: proof_repl pserv on hbox (3 h idle timeout) holds the generated book + chain for probes.
