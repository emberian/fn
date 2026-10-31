# fn2 layer D continuation (present state, rewritten whole; 2026-10-31 afternoon, the ninth Opus seat (distilled once))

Seat: Opus, layer D. The seat writes the code itself. Codex (`codex exec -m gpt-6-astra -C /Users/ember/dev/fn`) is used only for
bounded pieces with real signatures. Briefs: `build/coordinator/briefs/FN2-LAYER-D-MACHINES-NNTP.md` and FN2-SEAT-COMMON.md.
**The flow is `build/coordinator/fn2/WORKFLOW-20261031.md`**, binding:
- A commit establishes three things: the books you changed certify; the scenarios for what you
  touched pass in the REPL on the tiny profile; you read your diff.
- Then push and fix forward.
- None of these per commit: whole closures, sim-layer-d-evidence (it is a nightly row), the A4
  baseline, OWED regeneration, gate tables in a READY.
- Main gates dev's tip in batches and routes reds by file.
- Do not hand off at the ceiling: distill and continue.

## Rulings in force
- **Machine form (ember, 10-31).** Write no arms in the old form (defmachine with
  defmachine-callback). Main's new form is landing in parts:
  - P1 is on dev at 516c2daf3: ready links and wait-reason are directory columns.
  - P2, next: kind-declared `:stops` in a kind's own defmachine. txn's `:uncertain` (ruling 6) and
    conn's and upload's stops are declared in their books at the port.
  - D's four kinds are its first migration. Their ports are written below in §6.7's syntax
    (P.1-P.5). Each port waits for P4 and for asks F1-F3.
  - Core children and ops may land now.
- **Standing order (main, 10-31 afternoon).** Never stand by. While P2-P4 land, D's own order is:
  (1) the ports (done here, sent to main with the asks); (2) D7 4/n statement-first in
  d-machines-nntp.md (the request bundle and grants over S1-S6, and the ledger grant pair's liveness
  statement); (3) `fn2-read-frontier` when main sends C's `:published` sha; (4) the WIRE items in
  H14's owed host contracts that are D's. At about 400K tokens, ask main for a distill. The forge
  orphan (pid 3122923) is main's to handle.
- **Identity across peers** (`build/coordinator/fn2/IDENTITY-ACROSS-PEERS-20261030.md`, fourteen rulings).
  - D owns rulings 1, 6 and 8. In the txn port: the identity subject digest (1); the evidence-only
    committed transaction with a separate article refusal (6); replies chosen from the typed read result (8).
  - C's §4a (dev 219184b5d, then b0fbb77e9) brings five records and attributed receipts. Replies are
    decided from the separate facts a decision or read returns (selection relation, evidence status,
    coverage), never from :duplicate/:evidence/:conflict/:stored alone.

## State
- dev: **721f7a50b** (D7 4/n statement, doc only), on 80ff68ab2, the C-S4 second half (this seat, on 516c2daf3). Before it, 89d31a51d was the first half.
- `fn2/books/machines-c-read.lisp` (37 s on forge) is C-S4 whole except the frontier.
  - First half: rows `R = fn2-b-read-rows` (`:x` when `:reading`); children reads/ranges/range-sources(8R)/seeks.
  - Ops: key, key-octets, lookup, range, next, seek, seek-step, value, octets, release.
  - (d) `fn2-read-scan x sid wslot wgen wk ws wg` / `fn2-read-scan-next x budget`: a whole-schema
    ordered scan. The resume key is the delivered key, copied into the caller's workspace and skipped once.
  - (e) `fn2-read-identity x mslot mgen moff mlen okind oslot ogen budget -> (mv code article candidates)`
    gives the selection and evidence status of ruling 8.
  - Owed: `fn2-read-identity-typed-exact` (owed-cursor.lisp). Availability, coverage and authorization
    are `:not-served` until §4a's records and S-ARTICLE-LOCATION; rewrite the read over §4a's exact
    lookup, per-name summary and evidence cursor when main sends the sha.
  - (c) `fn2-read-frontier (fn2-core) -> (mv code position)` is a thin read of C's `(fn2-successor-published
    fn2-core) -> (mv code position)`. It is written as a patch with read-unit's frontier case:
    `build/coordinator/fn2/lanes/d-quests/frontier.patch`,
    applied with `git apply` at C's sha. To land it: certify machines-c-read and read-unit, then push.
    `fn2-cursor-view-pinned` stays owed until the cursor lands.
- Units:
  - `tests/read-unit.lisp` (18 s, in owed-export) covers: lookups; ranges with and without a
    position limit; the seek (31 probes over [1, 2^31), so bound it by the group's high); reads
    across seals (`:stale`); LIST across a seal; identity with conflict evidence; refusals.
  - `*fn2-read-profile*` (owed-cursor.lisp) is the reading profile.
- Answered to B through main: B-S2 §11b, yes with four amendments.
  - :ready order: resolve, stage, out, records, late fill, admit, bind.
  - Re-stage after a park rewrites the fill and the records.
  - Evidence-only members are admissible (ruling 6).
  - Identity records carry C's §4a encodings.
  - The acceptance record's content digest is the subject's digest (ruling 1).
  - Add `:batch-membership` to resources.lisp when the txn ports, with A's sixth grant source.
- C-S3a is on dev (ebcc65eea). Late octet args, fill after the last stage.
- Trees:
  - Mac worktree `build/lanes/fn2/d6` is on branch `fn2/d6-read` = 80ff68ab2.
  - Forge `/build/lanes/d6` is on branch d6-read, its certs warm at the pre-rebase base. Push with
    `git push fn@forge:/build/fn.git HEAD:refs/heads/d6-read`, then on forge
    `git fetch /build/fn.git d6-read && git checkout -B d6-read FETCH_HEAD`.
  - Certify on forge with `setsid sh -c "swarm-build sh fn2/tools/forge-certify.sh <books> > build/rN.out 2>&1; echo rc=\$? > build/rN.status" & echo $! > build/rN.pid`.
    The export is `FN_ACL2=... ACL2_SYSTEM_BOOKS=/tank/fn/acl2-8.7/books swarm-build sh fn2/tools/certify.sh --export-owed`.
  - REPL: `FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k python3 tools/acl2 --timeout N < build/rd-repl.lsp`.
- Orphan to report: on forge, pid 3122923 is a stuck `bash -c` from my own ssh at about 02:40.
  It has no PID file and holds no lock.

## Next, in order (D's own order while the form lands)
1. Done: the ports and asks F1-F13 (this file), sent to main for the form seat.
2. Done: D7 4/n statement-first, d-machines-nntp.md §13.8, dev 721f7a50b. Next is **4/n-a**,
   the ledger's request operations, the grant pair's bodies, and owed-accounts.lisp with the
   keystones and teeth in accounts-unit. These are core operations, so they land now. 4/n-b lands
   at conn's port.
3. `fn2-read-frontier` when C's `:published` sha arrives. Then `fn2-cursor-view-pinned` turns live.
4. H14's WIRE items that are D's: read fn2/docs/h-harness.md H14, list D's rows, and do the ones
   that need no new arm.
5. At P4: port conn, upload and txn (one commit each, scenarios unchanged), then D6 1/n (P.5),
   then D5 2/n (P.4, needs B-S2 and C §4a).
6. When C lands §4a: rewrite fn2-read-identity over its exact lookup, per-name summary and evidence cursor.

## Pitfalls hit (this seat)
- Shape lemmas outside an assembly:
  - Fold every stobj's `-ROWS`, and the accessors read for checks (C-SHAPE-READS).
  - Keep `-ROWS` enabled (`(:keep ...)` in fn2-rd-shape) only where no callee returns that stobj.
  - After a callee returns, re-check read values at run time (`unsigned-byte-p`, `nfix`).
  - Split a function whose shape lemma passes ten seconds: two halves, each with its own lemma.
    This turned 191 s into 4 s, and 52 s into under 1 s.
- Product terms in fn2-idc-profilep cost 121 s: make the function opaque and give new children
  their own profile predicate.
- No core child may have a column named `ref`, `diff` or `copy`.
- A dev landing can renumber a doc's seam list (C-S3a took §8 item 12; C-S4 is item 13).
- Earlier seats: `substitute :test` is not ACL2; `(mv :x (f fn2-core))` is illegal; one wake slot
  per run; run the export on forge.

## Ports: D's four kinds in MACHINE-FORM §6.2/§6.7 syntax (written against G1's generator, dev 80ff68ab2)

These replace the arm tables. Each block is the kind's `defmachine` as it lands at the port, written
against the generator as it reads at dev 80ff68ab2 (`fn2/books/machine-arms.lisp`). Nothing here has
been through `defmachine-arms` yet: the operation edits listed for each kind come first. Then a port
is a paste plus those edits. Ports keep behaviour: every scenario is unchanged, and the few
behaviour changes are named where they occur. D5 2/n and D6 1/n are separate blocks, written after
the ports.

### P.0 Conventions (how today's bodies map to steps)
- `fn2-machine-refuse-phase` → `(:stop :machine-phase)`; `fn2-machine-refuse-observation` →
  `(:stop :machine-observation)`; `fn2-core-stop *fn2-stop-reason-R*` → `(:stop :R :steps ...)`.
- `(fn2-machine-result B S D R)` → `(:charge :bytes B :steps S :descriptors D :runnable R)`.
  `fn2-machine-with-work` disappears: its preflight is statically true once the generator
  checks the cost (§6.4).
- `(fn2-call K-X id budget)` → `(:goto x)` to a sub-arm. The sub-arm reads the row fresh after the
  path's writes are flushed. That is what today's `fn2-call` after a PUT does.
- An issue followed by `fn2-machine-issue-result` → `(:issue (OP ...) :ok ((... (:wait :completion
  :bytes E))))`.
  - `:exhausted` parks on `:operation`.
  - Any other answer goes to the arm's `:on-refusal`, defaulting to `(:halt)`: today's retained R6
    row stop (`stopped 1`).
  - So an **issuing arm or sub-arm declares no `:on-refusal`**, and routes its other operations'
    refusals with an explicit `:case ((:otherwise (:stop :machine-phase))))`. Otherwise its issue
    refusals would stop the core instead of halting the row.
  - The other arms declare `:on-refusal ((:stop :machine-phase))` once, and an unrouted answer goes
    there.
- A `:do` whose `:case` covers every answer it continues on, with no steps after it, writes
  `:accept ()`. Otherwise the generator defaults `:accept (:ok)` and refuses "accepted answers have no
  continuation" (machine-arms.lisp `fn2-arms-do-body`).
- A keyword argument value is quoted (`':insert`, `':value`). `fn2-arms-split-call` ends the
  positional arguments at the first keyword, so an unquoted `:insert` would be read as a formal's
  name.
- Acting for another row's owner (gap 8) is an explicit override: `:okind *fn2-upload-kind* :oslot
  row-upload :ogen row-upload-gen`. Unoverridden, the generator fills the row's own triple.
- `row-slot` (the row's slot in its kind: the claim row, successor tx, decision row and read row x)
  is ask F7. Until it lands, each kind declares `(defcost K-slot-of ...)` over `fn2-machine-slot`
  and writes `(K-slot-of id)`.

### P.1 fn2-conn (the port; `conn.lisp`)
**D's operation edits** (conn.lisp, upload.lisp, accounts-core.lisp; all D's books):
- (a) In every wrapper, rename the owner formals `id owner-gen` to `oslot ogen`, adding `okind`
  where it is `*fn2-conn-kind*` today. The generator then fills them.
- (b) Give `:answers t` to `fn2-conn-frame`, `-run-answer`, `-run-greeting`, `-run-overflow`,
  `-run-block-open`, `-run-outcome`, `-feed-run`, and to D7's `fn2-account-charge-core`. Today each
  returns a code that no declaration names.
- (c) Add `(defconst *fn2-conn-mask-greeted* (logior *fn2-nntp-state-reader*
  *fn2-nntp-state-anonymous*))`.
- (d) `fn2-conn-feed-run` returns `copied` as a natural, and the arm adds it.
- (e) **Behaviour change (gap 19):** the feed's `:need-more` path reports the feed's own work.
  `block-input` charges `*fn2-conn-feed-cost*` plus the receive. Today it charges 0 or `len` after
  2,048 octets of feed. Within the 4,096 cap.

```lisp
(defmachine fn2-conn
 :phases (:free :greeting :command :article-input :reply :upgrading :closing :draining :retired)
 :fields ( ... unchanged (conn.lisp:41-60) ... )
 :holds ( ... unchanged ... )
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-c profile)
 :admission ( ... unchanged ... )
 :initial ( ... unchanged ... )
 :subarms
 (;; RX exhausted between lines (was fn2-conn-input): reset when every octet was
  ;; consumed, compact a retained partial line next run, refuse a slot smaller
  ;; than the line cap, else Receive at the fill
  (input
   (:let nfill (fn2-conn-fill row-rx-slot))
   (:let cap (fn2-conn-cap row-rx-slot))
   (:cond ((and (equal row-start nfill) (< 0 nfill))
           (:do (code) (fn2-core-reset row-rx-slot row-rx-gen) :case ((:otherwise (:stop :machine-phase))))
           (:set (start 0) (pos 0))
           (:charge :bytes *fn2-conn-frame-bytes* :steps *fn2-work-mailbox* :runnable t))
          ((and (<= cap nfill) (< 0 row-start))
           (:set (compacting 1) (cursor 0))
           (:charge :bytes *fn2-conn-frame-bytes* :steps *fn2-work-mailbox* :runnable t))
          ((<= cap nfill)
           (:do (code) (fn2-conn-run-overflow row-mask row-tx-slot row-tx-gen)
            :case ((:otherwise (:stop :machine-phase))))
           (:set (tx-off 0) (after *fn2-conn-after-closing*))
           (:next :reply)
           (:charge :bytes *fn2-conn-frame-bytes* :steps *fn2-work-mailbox* :runnable t))
          (t (:let len (min *fn2-conn-receive-bytes* (nfix (- cap nfill))))
             (:issue (fn2-issue-receive row-cap-index row-cap-nonce row-rx-slot row-rx-gen len
                                        :principal row-principal-slot)
              :ok ((:wait :completion :bytes (+ *fn2-conn-frame-bytes* len)))))))
  ;; frame from the row's continuation; at a line, charge the request and answer
  ;; it (was fn2-conn-frame-run)
  (frame
   (:do (status s p o) (fn2-conn-frame row-rx-slot row-rx-gen row-start row-pos row-overflow)
    :accept ()
    :case (((:line)
            (:do (ccode) (fn2-account-charge-core row-principal-slot *fn2-account-charge-requests* 1)
             :case ((:otherwise (:stop :machine-phase))))
            (:do (code after next) (fn2-conn-run-answer s p row-mask row-auth-pending row-posting
                                                        row-rx-slot row-rx-gen row-tx-slot row-tx-gen)
             :case ((:otherwise (:stop :machine-phase))))
            ;; POST where posting is served: nothing rendered; the next run takes an upload
            (:if (equal after *fn2-conn-after-article-input*)
                 ((:set (start p) (pos p) (overflow 0) (auth-pending next) (rule *fn2-conn-rule-post*)
                        (request row-ordinal) (ordinal (+ 1 row-ordinal)))
                  (:charge :bytes *fn2-conn-run-bytes* :steps *fn2-work-transition* :runnable t))
                 ((:set (start p) (pos p) (overflow 0) (tx-off 0) (after after) (auth-pending next)
                        (ordinal (+ 1 row-ordinal)))
                  (:next :reply)
                  (:charge :bytes *fn2-conn-run-bytes* :steps *fn2-work-transition* :runnable t))))
           ((:overflow :long-line)
            (:do (ccode) (fn2-account-charge-core row-principal-slot *fn2-account-charge-requests* 1)
             :case ((:otherwise (:stop :machine-phase))))
            (:do (code) (fn2-conn-run-overflow row-mask row-tx-slot row-tx-gen)
             :case ((:otherwise (:stop :machine-phase))))
            (:set (start s) (pos p) (overflow o) (tx-off 0) (after *fn2-conn-after-closing*))
            (:next :reply)
            (:charge :bytes *fn2-conn-run-bytes* :steps *fn2-work-transition* :runnable t))
           ((:budget)
            (:set (start s) (pos p) (overflow o))
            (:charge :bytes *fn2-conn-frame-bytes* :steps *fn2-work-transition* :runnable t))
           ((:need-more) (:set (start s) (pos p) (overflow o)) (:goto input))
           (:otherwise (:stop :machine-phase)))))
  ;; move a retained partial line to the front of RX (was fn2-conn-compact-run)
  (compact
   (:do (code cursor) (fn2-core-drop-prefix row-rx-slot row-rx-gen row-start row-cursor *fn2-conn-compact-bytes*)
    :case (((:more) (:set (cursor cursor))
                    (:charge :bytes *fn2-conn-compact-bytes* :steps *fn2-work-transition* :runnable t))
           ((:ok) (:set (compacting 0) (cursor 0) (start 0) (pos cursor))
                  (:charge :bytes *fn2-conn-compact-bytes* :steps *fn2-work-transition* :runnable t))
           (:otherwise (:stop :machine-phase)))))
  ;; a POST line was answered :article-input: take an upload and render 340, or
  ;; park on the upload kind's FIFO (was fn2-conn-open-block; ask F2)
  (open-block
   (:do (tcode u) (fn2-machine-take-fn2-upload *fn2-none* id row-generation row-request *fn2-upload-rule-post*
                                               row-principal-slot)
    :case (((:no-row) (:park :taken fn2-upload :steps *fn2-work-transition*))
           (:otherwise (:stop :machine-phase))))
   (:let ugen (fn2-upload-gen-of u))
   (:do (code) (fn2-conn-run-block-open row-mask row-tx-slot row-tx-gen) :case ((:otherwise (:stop :machine-phase))))
   (:set (tx-off 0) (after *fn2-conn-after-article-input*) (upload u) (upload-gen ugen)
         (feed-mode 0) (feed-discard 0) (fed 0) (word 0) (outcome-ready 0))
   (:next :reply)
   (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
  ;; RX exhausted during a block (was fn2-conn-block-input)
  (block-input
   (:let nfill (fn2-conn-fill row-rx-slot))
   (:let cap (fn2-conn-cap row-rx-slot))
   (:cond ((and (equal row-start nfill) (< 0 nfill))
           (:do (code) (fn2-core-reset row-rx-slot row-rx-gen) :case ((:otherwise (:stop :machine-phase))))
           (:set (start 0) (pos 0))
           (:charge :bytes *fn2-conn-feed-cost* :steps *fn2-work-mailbox* :runnable t))
          ((<= cap nfill) (:stop :machine-phase))
          (t (:let len (min *fn2-conn-receive-bytes* (nfix (- cap nfill))))
             (:issue (fn2-issue-receive row-cap-index row-cap-nonce row-rx-slot row-rx-gen len
                                        :principal row-principal-slot)
              :ok ((:wait :completion :bytes (+ *fn2-conn-feed-cost* len)))))))
  ;; one quantum of the block into the upload, and wake it (was fn2-conn-feed-step)
  (feed
   (:do (status start mode why copied)
        (fn2-conn-feed-run row-start row-feed-mode row-feed-discard row-fed row-rx-slot row-rx-gen
                           row-upload row-upload-gen)
    :accept (:terminator :need-more :budget)
    :why "a feed step ends at the terminator, short of input, or at its quantum; :full is folded into :budget"
    :case ((:otherwise (:stop :machine-phase))))
   (:let fed (+ row-fed copied))
   (:do () (fn2-conn-wake row-upload))
   (:cond ((not (and (unsigned-byte-p 32 start) (unsigned-byte-p 8 mode) (unsigned-byte-p 8 why)
                     (unsigned-byte-p 60 fed)))
           (:stop :machine-phase))
          ((eq status :terminator)
           (:set (start start) (pos start) (feed-mode *fn2-conn-feed-done*) (feed-discard why) (fed fed))
           (:charge :bytes *fn2-conn-feed-cost* :steps *fn2-work-transition*))
          ((eq status :need-more)
           (:set (start start) (pos start) (feed-mode mode) (feed-discard why) (fed fed))
           (:goto block-input))
          (t (:set (start start) (pos start) (feed-mode mode) (feed-discard why) (fed fed))
             (:charge :bytes *fn2-conn-feed-cost* :steps *fn2-work-transition* :runnable t)))))
 :arms
 ((:free (:idle))
  ;; the greeting, or the capacity 400 (an unbooked row or the partition's
  ;; reserve row releases its booking first)
  (:greeting :on-refusal ((:stop :machine-phase))
   (:let ref row-account-ref)
   (:let refused (if (and (not (equal ref *fn2-none*)) (equal row-refused 0)) 0 1))
   (:do (ucode) (fn2-account-unbook-ref (if (equal refused 1) ref *fn2-none*)))
   (:let posting (fn2-conn-posting-p))
   (:do (code after) (fn2-conn-run-greeting refused posting row-mask row-tx-slot row-tx-gen))
   (:set (tx-off 0) (after after) (refused refused) (posting posting)
         (account-ref (if (equal refused 1) *fn2-none* ref)) (mask *fn2-conn-mask-greeted*))
   (:next :reply)
   (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
  (:command
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((not (equal row-rule *fn2-conn-rule-none*)) (:goto open-block))
          ((equal row-compacting 1) (:goto compact))
          (t (:goto frame))))
  ;; feed the block; once the outcome word is posted, render it
  (:article-input
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((equal row-outcome-ready 1)
           (:do (code after) (fn2-conn-run-outcome row-word row-mask row-tx-slot row-tx-gen)
            :case ((:otherwise (:stop :machine-phase))))
           (:set (tx-off 0) (after after) (upload *fn2-none*) (upload-gen 0) (rule *fn2-conn-rule-none*)
                 (word 0) (outcome-ready 0) (feed-mode 0) (feed-discard 0) (fed 0))
           (:next :reply)
           (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
          ((equal row-feed-mode *fn2-conn-feed-done*) (:charge :steps *fn2-work-empty*))
          (t (:goto feed))))
  ;; send [tx-off, fill) by loan; once sent and released, reset TX and move to AFTER
  (:reply
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((not (equal row-borrows 0)) (:charge :steps *fn2-work-poll*))
          (t (:let nfill (fn2-conn-fill row-tx-slot))
             (:if (< row-tx-off nfill)
                  ((:let len (min *fn2-conn-send-bytes* (nfix (- nfill row-tx-off))))
                   (:issue (fn2-issue-send row-cap-index row-cap-nonce row-tx-slot row-tx-gen row-tx-off len 1
                                           :principal row-principal-slot)
                    :ok ((:set (borrows 1)) (:wait :completion :bytes len))))
                  ((:do (code) (fn2-core-reset row-tx-slot row-tx-gen) :case ((:otherwise (:stop :machine-phase))))
                   (:set (tx-off 0))
                   (:next (:if (equal row-after *fn2-conn-after-closing*) :closing
                            (:if (equal row-after *fn2-conn-after-article-input*) :article-input :command)))
                   (:charge :steps *fn2-work-mailbox* :runnable t))))))
  (:upgrading (:stop :machine-phase))
  (:closing
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          (t (:issue (fn2-issue-close row-cap-index row-cap-nonce :principal row-principal-slot)
              :ok ((:wait :completion :bytes 0))))))
  ;; release TX, then RX (D0's descending order), the booking, then the row; an
  ;; upload this row fed is woken so it drains
  (:draining
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((not (equal row-borrows 0)) (:charge :steps *fn2-work-poll*))
          (t (:do (tcode) (fn2-core-release row-tx-slot row-tx-gen) :effects ((:release (:tx-range)))
              :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)"
              :case ((:otherwise (:stop :pool-release :steps *fn2-work-state*))))
             (:do (rcode) (fn2-core-release row-rx-slot row-rx-gen) :effects ((:release (:rx-range)))
              :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)"
              :case ((:otherwise (:stop :pool-release :steps *fn2-work-state*))))
             ;; the booking goes; the charges stay with the principal (rule 5)
             (:do (acode) (fn2-account-unbook-ref row-account-ref)
              :case ((:otherwise (:stop :account :steps *fn2-work-state*))))
             (:do () (fn2-conn-wake row-upload))
             (:let next (fn2-machine-free-head *fn2-conn-admission-ordinal*))
             (:let retire (>= row-generation (fn2-machine-gen-limit)))
             (:set (generation (if retire row-generation (+ 1 row-generation)))
                   (rx-slot *fn2-none*) (rx-gen 0) (tx-slot *fn2-none*) (tx-gen 0) (cap-index 0) (cap-nonce 0)
                   (start 0) (pos 0) (overflow 0) (compacting 0) (cursor 0) (tx-off 0) (ordinal 0)
                   (auth-pending *fn2-conn-auth-none*) (refused 0) (next-free next) (wait-reason *fn2-wait-none*)
                   (account-ref *fn2-none*) (upload *fn2-none*))
             (:next (:if retire :retired :free))
             (:do () (fn2-machine-reclaim-fn2-conn id retire))
             (:charge :steps *fn2-work-release*))))
  (:retired (:idle)))
 :observes
 (;; a completed Receive is charged to the principal from its first byte (D7 13.4)
  (:receive-result :from (:command :article-input)
   (:if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*)) (natp count) (< 0 count))
        ((:do (code) (fn2-account-charge-core row-principal-slot *fn2-account-charge-rx* count)
          :case ((:otherwise (:stop :machine-observation))))
         (:wake))
        ((:next :closing) (:wake))))
  ;; a short Send is terminal and the remainder is a new Send (ROUND2 D.1)
  (:send-result :from (:reply)
   (:if (not (eq (fn2-machine-pool-borrows-read-code row-tx-slot) :ok))
        ((:stop :machine-observation))
        ((:let borrows (fn2-machine-pool-borrows row-tx-slot))
         (:if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*)) (natp count))
              ((:do (code) (fn2-account-charge-core row-principal-slot *fn2-account-charge-tx* count)
                :case ((:otherwise (:stop :machine-observation))))
               (:set (borrows borrows) (tx-off (+ row-tx-off count)))
               (:wake))
              ((:set (borrows borrows)) (:next :closing) (:wake))))))
  (:borrow-released
   (:if (not (eq (fn2-machine-pool-borrows-read-code row-tx-slot) :ok))
        ((:stop :machine-observation))
        ((:set (borrows (fn2-machine-pool-borrows row-tx-slot))) (:wake))))
  (:close-result :from (:closing) (:next :draining) (:wake))))
```
Deleted with the port: the 16 `defmachine-callback`s and `:continuations`, `fn2-conn-input`'s
contract, `fn2-machine-issue-result`'s use, and the `fn2-conn-feed-step` `:need-more` under-charge.
The conn's ops (`fn2-conn-frame` … `fn2-conn-wake`) stay as declared operations until P2 gives them
bodies over the pool. One more behaviour change: `:frame` now stops on a refused charge before it
renders the answer. Today it renders and then stops. Either way the core stops, so no scenario sees
the difference.

### P.2 fn2-upload (the port; `upload.lisp`)
`fn2-upload-advance` (one defcost hiding the transition relation, gap 1/2) and `fn2-upload-finish`
are unrolled into the `work`, `discard` and `finish` sub-arms. The 13 hand writes of
`fn2-upload-scan-run` (gap 25) become one `:set`.

**D's operation edits:**
- (a) New pure cross-row readers with defcosts (stobj in, none out):
  - `fn2-conn-fed-of (conn)`, `fn2-conn-feed-mode-of (conn)`, `fn2-conn-feed-discard-of (conn)`:
    the conn row's `fed`, `feed-mode`, `feed-discard`, 0 when unreadable;
  - `fn2-upload-hasher ()`, which takes the hasher row from `row-slot` (F7): `3 + slot`.
- (b) Defcosts:
  - `fn2-upload-hash-run (row c0 g0 c1 g1 cap0 hashed filled okind oslot ogen)` with `:answers t
    :bytes *fn2-upload-hash-bytes*`, returning `(code hashed)`;
  - `fn2-upload-scan-run (c0 g0 hs off field visible fields lines seen mo ml no nl po pl okind oslot
    ogen)` with `:answers t :bytes *fn2-upload-scan-bytes*`. It returns `(st hs off field visible
    fields lines seen mo ml no nl po pl)`, all widths checked: `:fault` on a bad width, `:skip` with
    the inputs when HS is not scanning, `visible` a bit. It writes nothing;
  - `fn2-upload-digest (row hashed)`, `fn2-upload-word-now (c0 g0 cap0 cap1 filled okind oslot
    ogen)` returning `(code w inj)`, and `fn2-upload-digest-store (row slot gen off okind oslot
    ogen)`, each `:answers t`;
  - `fn2-upload-digest-at` (pure, no stobj);
  - `fn2-conn-post-word` with `:answers (:ok :dropped)`.
- (c) Word constants `*fn2-upload-word-W*` for each of `*fn2-upload-words*` (one `make-event`). The
  arms name words as constants, never by `fn2-upload-word-code`.
- (d) The dead field `filled` is deleted (gap 26). The truth is the conn's `fed`.

```lisp
(defmachine fn2-upload
 :phases (:free :head :identity :receiving :validating :discard :sealed :aborting :draining :retired)
 :fields ( ... unchanged less filled ... )
 :holds ( ... unchanged ... )   :budget (:bytes 4096 :steps 32 :descriptors 0)
 :capacity (fn2-upload-capacity profile)
 :taken ( ... unchanged, :clear less filled ... )
 :initial ( ... unchanged ... )
 :subarms
 (;; the conn discards the block (framing or too large): once its terminator is
  ;; framed, the word goes to the transaction if one was taken, else to the conn
  (discard :on-refusal ((:stop :machine-phase))
   (:let reason (fn2-conn-feed-discard-of row-conn))
   (:cond ((not (equal (fn2-conn-feed-mode-of row-conn) *fn2-conn-feed-done*))
           (:next :discard) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*))
          (t (:let w (if (equal reason 1) *fn2-upload-word-framing* *fn2-upload-word-too-large*))
             (:if (not (equal row-txn *fn2-none*))
                  ((:set (word w) (inj 0))
                   (:do () (fn2-upload-wake row-txn))
                   (:next :sealed)
                   (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*))
                  ((:do (pcode) (fn2-conn-post-word row-conn row-conn-gen row-request w)
                    :accept (:ok :dropped) :why "a connection that moved on takes no word; its release woke this row")
                   (:next :draining)
                   (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))))))
  ;; every octet fed and hashed: the digest, the verdict, and its delivery
  (finish :on-refusal ((:stop :machine-phase))
   (:let filled (fn2-conn-fed-of row-conn))
   (:let cap0 (fn2-upload-chunk-cap row-c0-slot))
   (:do (ecode) (fn2-upload-digest (fn2-upload-hasher) row-hashed))
   (:do (wcode w inj) (fn2-upload-word-now row-c0-slot row-c0-gen cap0 (fn2-upload-chunk-cap row-c1-slot) filled))
   (:cond ((and (equal row-txn *fn2-none*) (equal w 0)) (:stop :machine-phase))
          ((equal row-txn *fn2-none*)
           (:set (word w))
           (:do (pcode) (fn2-conn-post-word row-conn row-conn-gen row-request w)
            :accept (:ok :dropped) :why "a connection that moved on takes no word; its release woke this row")
           (:next :draining)
           (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
          (t (:do (in1 doff) (fn2-upload-digest-at filled cap0))
             (:do (scode) (fn2-upload-digest-store (fn2-upload-hasher) (if in1 row-c1-slot row-c0-slot)
                                                   (if in1 row-c1-gen row-c0-gen) doff))
             (:set (word w) (inj inj))
             (:do () (fn2-upload-wake row-txn))
             (:next :sealed)
             (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*))))
  ;; one run of hashing and header scan (was fn2-upload-advance)
  (work :on-refusal ((:stop :machine-phase))
   (:cond
    ((not (fn2-upload-conn-live-p row-conn row-conn-gen id row-generation))
     (:next :aborting) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
    ((not (equal (fn2-conn-feed-discard-of row-conn) 0)) (:goto discard))
    (t
     (:let filled (fn2-conn-fed-of row-conn))
     (:do (hcode hashed) (fn2-upload-hash-run (fn2-upload-hasher) row-c0-slot row-c0-gen row-c1-slot row-c1-gen
                                              (fn2-upload-chunk-cap row-c0-slot) row-hashed filled))
     (:set (hashed hashed))
     (:do (st hs off field visible fields lines seen mo ml no nl po pl)
          (fn2-upload-scan-run row-c0-slot row-c0-gen row-head-status row-scan-off row-ofield row-visible
                               row-nfields row-nlines row-seen row-mo row-ml row-no row-nl row-po row-pl)
      :accept (:more :budget :header-done :malformed :line-length :header-fields :header-lines :header-octets :skip)
      :why "every scan status but :fault is a header state the verdict reads")
     (:set (scan-off off) (ofield field) (visible visible) (nfields fields) (nlines lines) (seen seen)
           (mo mo) (ml ml) (no no) (nl nl) (po po) (pl pl) (head-status hs))
     (:cond ((and (equal hs *fn2-upload-head-done*) (equal row-txn *fn2-none*))
             (:next :identity) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
            ((and (equal (fn2-conn-feed-mode-of row-conn) *fn2-conn-feed-done*) (<= filled hashed))
             (:goto finish))
            ((or (< hashed filled) (eq st :budget))
             (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
            ((and (not (equal hs *fn2-upload-head-scanning*)) (equal row-phase *fn2-upload-state-head*))
             (:next :receiving) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
            (t (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*)))))))
 :arms
 ((:free (:idle))
  (:head (:goto work))
  ;; the header is complete: take the transaction (bundle :transaction :admit)
  (:identity :on-refusal ((:stop :machine-phase))
   (:cond ((not (fn2-upload-conn-live-p row-conn row-conn-gen id row-generation))
           (:next :aborting) (:charge :steps *fn2-work-transition* :runnable t))
          (t (:do (code tid) (fn2-machine-take-fn2-txn *fn2-none* id row-generation row-conn row-conn-gen row-request
                                                       row-rule row-principal-slot)
              :case (((:no-row) (:park :taken fn2-txn :steps *fn2-work-transition*))))
             (:set (txn tid) (txn-gen (fn2-txn-gen-of tid)))
             (:next :receiving)
             (:charge :steps *fn2-work-transition* :runnable t))))
  (:receiving (:goto work))
  (:validating (:goto work))
  (:discard (:goto work))
  ;; the transaction holds the octets until its outcome, then lets the upload drain
  (:sealed
   (:if (fn2-upload-txn-live-p row-txn row-txn-gen id)
        ((:charge :steps *fn2-work-transition*))
        ((:next :draining) (:charge :steps *fn2-work-transition* :runnable t))))
  (:aborting
   (:if (fn2-upload-txn-live-p row-txn row-txn-gen id)
        ((:do () (fn2-upload-wake row-txn)) (:charge :steps *fn2-work-transition*))
        ((:next :draining) (:charge :steps *fn2-work-transition* :runnable t))))
  (:draining
   (:do (c1code) (fn2-core-release row-c1-slot row-c1-gen) :effects ((:release (:chunk-window)))
    :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)"
    :case ((:otherwise (:stop :pool-release :steps *fn2-work-state*))))
   (:do (c0code) (fn2-core-release row-c0-slot row-c0-gen) :effects ((:release (:chunk-window)))
    :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)"
    :case ((:otherwise (:stop :pool-release :steps *fn2-work-state*))))
   (:let next (fn2-machine-free-head *fn2-upload-admission-ordinal*))
   (:let retire (>= row-generation (fn2-machine-gen-limit)))
   (:set (generation (if retire row-generation (+ 1 row-generation)))
         (c0-slot *fn2-none*) (c0-gen 0) (c1-slot *fn2-none*) (c1-gen 0) (conn *fn2-none*) (conn-gen 0)
         (hashed 0) (txn *fn2-none*) (next-free next) (wait-reason *fn2-wait-none*))
   (:next (:if retire :retired :free))
   (:do () (fn2-machine-reclaim-fn2-upload id retire))
   (:charge :steps *fn2-work-release*))
  (:retired (:idle))))
```
`:descriptors 0` (the upload issues nothing: C's cap-0 ruling) is new and costs nothing; the
generator then refuses any `:issue`. The `:identity` take's `:case` lists only `:no-row`, so
anything else goes to `:on-refusal`, and `:ok` continues.

### P.3 fn2-txn (the port; `txn.lisp`)
The seven staged helpers (`fn2-txn-begin`, `-claim-walk`, `-decide`, `-declare-1`, `-commit-1`,
`-finish`, `-unclaim-run`) and the checked wrappers `fn2-txn-checked` (gap 15) become steps.
`fn2-txn-put-article`'s 17-call `fn2-txn-chain` (gap 14) becomes the `article` sub-arm, one `:do`
per successor call. Each step's cost is then a sum the generator can see.

**D's operation edits:**
- (a) Pure cross-row reader `fn2-txn-upload-view (u)` returning `(ml mo c0 g0 c1 g1 hashed scanned
  no nl)` (gap 6: one declared read set of the upload). It joins `fn2-txn-upload-live-p (u ugen
  oslot ogen)`, `-sealed-p (u)`, `-aborting-p (u)` and `-words (u)`, which return `(w inj)`.
- (b) Defcosts with `:answers t`:
  - `fn2-txn-hash`, `fn2-claim-begin-core`, `fn2-claim-walk-core` (`:claimed :wait :more`),
    `fn2-claim-release-core`;
  - `fn2-txn-offer (d u ugen)`, `fn2-txn-count-run (from to lines c0 g0 c1 g1 cap0 okind oslot ogen)`
    and `fn2-txn-next-name (base cur end skip slot gen okind oslot ogen)`, each with its byte bound;
  - C's `fn2-identity-step`, `fn2-group-lookup`, `fn2-successor-*` and B's `fn2-commit-admit-txn`
    gain `:answers t` in their own books. That is a seam request to C and B, sent with these ports.
- (c) `fn2-txn-claim-state (c)`, a pure reader.

```lisp
(defmachine fn2-txn
 :phases (:free :admit :reserve :lookup :prepare :ready :batched :accepted :refused :uncertain :releasing :draining :retired)
 :fields ( ... unchanged ... )   :holds ( ... unchanged ... )
 :budget (:bytes 16384 :steps 32 :descriptors 0)
 :capacity (fn2-txn-capacity profile)
 :taken ( ... unchanged ... )    :initial ( ... unchanged ... )
 :subarms
 (;; the article's records into the batch's private successor (was fn2-txn-put-article)
  (article :on-refusal ((:stop :machine-phase))
   (:do (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view row-upload))
   (:do (in1 doff) (fn2-upload-digest-at hashed (fn2-upload-chunk-cap c0)))
   (:let ds (if in1 c1 c0)) (:let dg (if in1 g1 g0))
   (:do (c) (fn2-successor-put row-slot *fn2-txn-slot-article* *fn2-txn-article-sid* ':insert))
   (:do (c) (fn2-successor-arg row-slot *fn2-txn-slot-article* *fn2-article-entry-field-article* ':event 0))
   (:do (c) (fn2-successor-arg row-slot *fn2-txn-slot-article* *fn2-article-entry-field-birth* ':event 0))
   (:do (c) (fn2-successor-arg row-slot *fn2-txn-slot-article* *fn2-article-entry-field-state* ':value *fn2-txn-article-live*))
   (:do (c) (fn2-successor-arg row-slot *fn2-txn-slot-article* *fn2-article-entry-field-version* ':value *fn2-txn-article-version*))
   (:do (c) (fn2-successor-arg-octets row-slot *fn2-txn-slot-article* *fn2-article-entry-field-source* ds dg doff
                                      *fn2-upload-digest-octets* :okind *fn2-upload-kind* :oslot row-upload :ogen row-upload-gen))
   (:do (c) (fn2-successor-arg row-slot *fn2-txn-slot-article* *fn2-article-entry-field-bytes* ':value hashed))
   (:do (c) (fn2-successor-arg row-slot *fn2-txn-slot-article* *fn2-article-entry-field-lines* ':value row-lines))
   (:do (c) (fn2-successor-put row-slot *fn2-txn-slot-record* *fn2-txn-identity-sid* ':record))
   (:do (c) (fn2-successor-arg row-slot *fn2-txn-slot-record* 0 ':event 0))
   (:do (c) (fn2-successor-arg row-slot *fn2-txn-slot-record* 1 ':value row-principal-slot))
   (:do (c) (fn2-successor-put row-slot *fn2-txn-slot-outcome* *fn2-txn-outcome-sid* ':insert))
   (:do (c) (fn2-successor-arg row-slot *fn2-txn-slot-outcome* *fn2-outcome-entry-field-principal* ':value row-principal-slot))
   (:do (c) (fn2-successor-arg row-slot *fn2-txn-slot-outcome* *fn2-outcome-entry-field-operation* ':event 0))
   (:do (c) (fn2-successor-arg-octets row-slot *fn2-txn-slot-outcome* *fn2-outcome-entry-field-request* ds dg doff
                                      *fn2-upload-digest-octets* :okind *fn2-upload-kind* :oslot row-upload :ogen row-upload-gen))
   (:do (c) (fn2-successor-arg row-slot *fn2-txn-slot-outcome* *fn2-outcome-entry-field-outcome* ':value *fn2-txn-outcome-accepted*))
   (:do (c) (fn2-successor-arg row-slot *fn2-txn-slot-outcome* *fn2-outcome-entry-field-event* ':event 0))
   (:set (prepared 1))
   (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
  ;; one Newsgroups name: look it up, declare its group-count accept (was fn2-txn-group-step)
  (group :on-refusal ((:stop :machine-phase))
   (:do (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view row-upload))
   (:do (status start len next skip2) (fn2-txn-next-name no row-gcur nl (equal row-gskip 1) c0 g0
                                                         :okind *fn2-upload-kind* :oslot row-upload :ogen row-upload-gen)
    :accept (:run :end :name) :why "the name scan's three continuations; :fault goes to :on-refusal")
   (:cond ((not (unsigned-byte-p 32 next)) (:stop :machine-phase))
          ((eq status :run) (:set (gcur next) (gskip (if skip2 1 0)))
                            (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
          ((eq status :end) (:set (gcur next)) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
          (t (:do (code group) (fn2-group-lookup row-slot c0 g0 (+ no start) len 4096
                                                 :okind *fn2-upload-kind* :oslot row-upload :ogen row-upload-gen)
              :accept ()
              :case (((:more) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                     ((:absent) (:set (gcur next)) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                     ((:ok)
                      (:cond ((>= row-ngroups *fn2-txn-groups-max*)
                              (:set (word *fn2-upload-word-unaffordable*)) (:next :refused)
                              (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                             (t (:let i (+ *fn2-txn-slot-accepts* row-ngroups))
                                (:do (c) (fn2-successor-put row-slot i *fn2-txn-counts-sid* ':accept))
                                (:do (c) (fn2-successor-arg row-slot i 0 ':value group))
                                (:set (ngroups (+ 1 row-ngroups)) (gcur next))
                                (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t)))))))))
  ;; the outcome: the word to the connection (waking it), the successor released
  (reply
   (:if (not (equal row-word 0))
        ((:do (pcode) (fn2-conn-post-word row-conn row-conn-gen row-request row-word)
          :accept (:ok :dropped) :why "a connection that moved on takes no word; its release woke the upload")
         (:do (rcode) (fn2-successor-release row-slot) :case ((:otherwise (:stop :machine-phase))))
         (:next :releasing) (:charge :steps *fn2-work-transition* :runnable t))
        ((:do (rcode) (fn2-successor-release row-slot) :case ((:otherwise (:stop :machine-phase))))
         (:next :releasing) (:charge :steps *fn2-work-transition* :runnable t)))))
 :arms
 ((:free (:idle))
  ;; wait for the verdict when no Message-ID was scanned (posting the upload's
  ;; word, or :not-stored); else hash it and begin the claim
  (:admit :on-refusal ((:stop :machine-phase))
   (:cond ((not (fn2-txn-upload-live-p row-upload row-upload-gen id row-generation))
           (:next :draining) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
          (t (:do (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view row-upload))
             (:cond ((and (equal ml 0) (fn2-txn-upload-sealed-p row-upload))
                     (:do (w inj) (fn2-txn-upload-words row-upload))
                     (:do (pcode) (fn2-conn-post-word row-conn row-conn-gen row-request
                                                      (cond ((not (equal w 0)) w) ((not (equal inj 0)) inj)
                                                            (t *fn2-upload-word-not-stored*)))
                      :accept (:ok :dropped) :why "a connection that moved on takes no word")
                     (:next :draining) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
                    ((and (equal ml 0) (fn2-txn-upload-aborting-p row-upload))
                     (:next :draining) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
                    ((equal ml 0) (:charge :bytes 256 :steps *fn2-work-transition*))
                    (t (:do (hcode hash) (fn2-txn-hash ml c0 g0 mo :okind *fn2-upload-kind* :oslot row-upload :ogen row-upload-gen))
                       (:do (bcode) (fn2-claim-begin-core row-slot hash c0 g0 mo ml
                                                          :ok *fn2-upload-kind* :os row-upload :og row-upload-gen))
                       (:next :reserve) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))))))
  ;; the claim walk: held, waiting in the holder's FIFO (ask F5), or more
  (:reserve :on-refusal ((:stop :machine-phase))
   (:let s (fn2-txn-claim-state row-slot))
   (:cond ((equal s *fn2-claim-state-held*) (:next :lookup) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
          ((equal s *fn2-claim-state-waiting*) (:charge :bytes 4096 :steps *fn2-work-transition*))
          (t (:do (code holder) (fn2-claim-walk-core row-slot *fn2-txn-claim-steps*)
              :accept ()
              :case (((:claimed) (:next :lookup) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                     ((:wait) (:charge :bytes 4096 :steps *fn2-work-transition*))
                     ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t)))))))
  ;; the upload's verdict, then the identity offer (one run) or one decision step
  (:lookup :on-refusal ((:stop :machine-phase))
   (:cond ((not (and (fn2-txn-upload-live-p row-upload row-upload-gen id row-generation)
                     (not (fn2-txn-upload-aborting-p row-upload))))
           (:set (word 0)) (:next :refused) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
          ((not (fn2-txn-upload-sealed-p row-upload)) (:charge :bytes 4096 :steps *fn2-work-transition*))
          (t (:do (w inj) (fn2-txn-upload-words row-upload))
             (:cond ((not (equal w 0)) (:set (word w)) (:next :refused)
                                       (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                    ((not (equal row-offered 1))
                     (:do (code) (fn2-txn-offer row-slot row-upload row-upload-gen))
                     (:set (offered 1)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                    (t (:do (answer) (fn2-identity-step row-slot 4096)
                        :accept ()
                        :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                               ((:stored) (:next :prepare) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                               ((:duplicate) (:set (word *fn2-upload-word-duplicate*)) (:next :refused)
                                             (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                               ((:conflict :evidence) (:set (word *fn2-upload-word-conflict*)) (:next :refused)
                                                      (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))))))))))
  ;; count the body's lines, look each group up, refuse :group or the injected
  ;; fields, declare the slots; then resolve them
  (:prepare :on-refusal ((:stop :machine-phase))
   (:if (equal row-prepared 1)
        ((:do (answer) (fn2-successor-resolve row-slot 4096)
          :case (((:ok) (:next :ready) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                 ((:more) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t)))))
        ((:do (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view row-upload))
         (:let counted (max scanned row-counted))
         (:cond ((< counted hashed)
                 (:do (code counted2 lines2) (fn2-txn-count-run counted hashed row-lines c0 g0 c1 g1 (fn2-upload-chunk-cap c0)
                                                                :okind *fn2-upload-kind* :oslot row-upload :ogen row-upload-gen))
                 (:if (and (unsigned-byte-p 60 counted2) (unsigned-byte-p 32 lines2))
                      ((:set (counted counted2) (lines lines2)) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                      ((:stop :machine-phase))))
                ((< row-gcur nl) (:goto group))
                ((equal row-ngroups 0) (:set (word *fn2-upload-word-group*)) (:next :refused)
                                       (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                (t (:do (w inj) (fn2-txn-upload-words row-upload))
                   (:if (not (equal inj 0))
                        ((:set (word inj)) (:next :refused) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                        ((:goto article))))))))
  ;; stage every slot against the tip, admit the member, bind on :ok (one run)
  (:ready :on-refusal ((:stop :machine-phase))
   (:do (scode i) (fn2-successor-stage row-slot)
    :accept ()
    :case (((:ok)
            (:do (ml mo c0 g0 c1 g1 hashed scanned no nl) (fn2-txn-upload-view row-upload))
            (:do (acode batch event) (fn2-commit-admit-txn c0 g0 hashed
                                                          :okind *fn2-upload-kind* :oslot row-upload :ogen row-upload-gen)
             :accept ()
             :case (((:ok) (:do (bcode) (fn2-successor-bind row-slot batch event))
                           (:next :batched) (:charge :bytes 16384 :steps *fn2-work-transition*))
                    ((:not-served) (:set (word *fn2-upload-word-not-stored*)) (:next :refused)
                                   (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t))
                    ((:exhausted) (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t)))))
           ((:full) (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t))
           ((:stale) (:set (offered 0)) (:next :lookup) (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t))
           ((:duplicate) (:set (word *fn2-upload-word-duplicate*)) (:next :refused)
                         (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t))
           ((:evidence) (:set (word *fn2-upload-word-conflict*)) (:next :refused)
                        (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t))
           ((:identity-conflict-bound) (:set (word *fn2-upload-word-identity-conflict-bound*)) (:next :refused)
                                       (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t))
           ((:capacity) (:set (word *fn2-upload-word-unaffordable*)) (:next :refused)
                        (:charge :bytes 16384 :steps *fn2-work-transition* :runnable t)))))
  (:batched (:stop :machine-phase))        ; reached only once B-S2 admits (D5 2/n)
  (:accepted (:goto reply))
  (:refused (:goto reply))
  (:uncertain (:stop :machine-phase))      ; D5 2/n: a kind-declared stop (P2)
  ;; release the claim; its FIFO's head takes it and is woken (the run's one wake)
  (:releasing :on-refusal ((:stop :machine-phase))
   (:do (code) (fn2-claim-release-core row-slot))
   (:next :draining) (:charge :steps *fn2-work-transition* :runnable t))
  (:draining
   (:let u row-upload) (:let gen row-generation)
   (:let next (fn2-machine-free-head *fn2-txn-admission-ordinal*))
   (:let retire (>= gen (fn2-machine-gen-limit)))
   (:set (generation (if retire gen (+ 1 gen))) (upload *fn2-none*) (upload-gen 0) (conn *fn2-none*) (conn-gen 0)
         (next-free next) (wait-reason *fn2-wait-none*))
   (:next (:if retire :retired :free))
   (:do () (fn2-machine-reclaim-fn2-txn id retire))
   (:do () (fn2-txn-wake-upload u id gen))
   (:charge :steps *fn2-work-release*))
  (:retired (:idle))))
```
The `:ready` `:ok` bind path routes `bcode` to `:on-refusal` (a core stop), as today's `:stop`. Once
admission has succeeded, bind cannot fail (B-S2 S1). That makes this the stop C3 names, not an
absorb.

### P.4 fn2-txn, D5 2/n (written in the form after the port; rulings 1, 6, 8; C §4a; B-S2 §11b with D's amendments)
These are the changed arms only. The signatures marked † land with C's §4a and B-S2, and get
confirmed against their shas.
- **Fields gained:** `mode (:enum fn2-txn-mode (:article :evidence))`, the ruling 6 path;
  `outcome (:enum fn2-txn-outcome (:none :committed :uncertain :refused))`, the evidence commit's
  outcome, reported apart from `word`; `batch :u60 event :u60`; `ws :link wsgen :u60`, the member
  workspace slot, a pool range of the upload class reserved at `:prepare`.
- **Holds:** `:batched` holds `:batch-membership`, as declared today. `:ready` parks on it, ask F4.
- **`:lookup` (ruling 8, C §4a).**
  - The decision returns the separate facts: `(:do (answer sel evid cov) (fn2-identity-step row-slot
    4096))`†, where `sel` is the selection relation, `evid` the evidence status (the locally known
    candidates at this cut) and `cov` the coverage.
  - The reply is chosen from those facts, never from `answer` alone:
    - `sel` = accepted under this name → `:duplicate`, mode stays `:article` (435/437 by rule);
    - `evid` = a valid competing binding → `mode :evidence`, `word *fn2-upload-word-conflict*`, and
      `:next :prepare`. Ruling 6: the evidence is committed, never dropped;
    - an invalid signature or out-of-scope evidence → its own words, `:evidence-invalid` and
      `:evidence-scope`, each with `mode :evidence`. Known evidence → `mode :evidence`, which is
      idempotent at C's decision;
    - `answer :stored` → `mode :article`, `:next :prepare`.
- **`:prepare`.**
  - `mode :article`: as in the port, plus three things:
    - the overview slot with `(fn2-successor-arg-octets-late row-slot i *f-line* *fn2-txn-xover-max*)`,
      C-S3a;
    - the addr entries, one per carried group: `(fn2-successor-arg row-slot i f ':out ...)`, from
      `fn2-successor-out` at `:ready`;
    - the identity record's subject digest, D25's authored source (ruling 1), not the upload's raw
      digest.
  - `mode :evidence`: only the identity record (C §4a's record encoding, by schema and version) and
    the operation outcome; no article, membership or overview slots.
  - Both modes reserve `ws` with `(:do (code slot gen) (fn2-core-reserve *fn2-upload-chunk-class*)
    :effects ((:acquire (:txn-workspace))) :case (((:exhausted) (:park :pool *fn2-upload-chunk-class*))))`.
    D0 gains `:txn-workspace`; resources.lisp is D's book.
  - The Message-ID is generated when the article carried none.
- **`:ready`, in B-S2's amended order.** In one run, because nothing may stage or bind between this
  transaction's stage and its bind:
  1. stage;
  2. `fn2-successor-out`, the group numbers;
  3. write the member records into `ws` in B's encodings (`fn2-txn-write-records`, D's op, `:bytes
     4096`);
  4. `fn2-successor-fill-octets` with the Xref line, rendered into `ws` after the records;
  5. `fn2-commit-admit-txn ws wsgen len`†;
  6. on `:ok`, bind with the returned event, which cannot fail;
  7. on `:exhausted`, `(:park :batch-membership)`, ask F4. The waker is B's sixth grant source. The
     re-stage on wake clears the fill, so steps 2-4 rerun after every stage;
  8. on `:admission`, `:next :refused` with `*fn2-upload-word-not-stored*`, a D defect stop in the
     tiny profile.
  The run is stage 4,096 + out 512 + records 4,096 + fill 2,048 + admit 4,096 + bind 8,192 =
  23,040 bytes. **C ruled (10-31): the budget becomes `(:bytes 24576 ...)`,** recorded as a
  departure beside 16,384. There is no C-S3b now: holding a stage across runs would need bind to
  re-check each slot's tip witness and replan on staleness, which is a seam of the new form's run
  model. C builds C-S3b only if the form's cost model makes 24 KiB matter.
- **`:batched`:**
  `(:do (code outcome) (fn2-commit-take row-batch row-event :okind ...)† :case (((:pending) (:charge
  :steps *fn2-work-empty*)) ((:accepted) ...) ((:uncertain) ...) ((:refused) ...)))`, with B-S2's
  generation-checked wake, so no busy wait.
  - `mode :article`: `:accepted` → word `:accepted`, `:next :accepted`; `:refused` → word
    `:not-stored`, `:next :refused`; `:uncertain` → `:next :uncertain`.
  - `mode :evidence`: the word stays the article refusal, and `outcome` records the commit's answer.
    The connection renders both, as ruling 6 asks.
- **`:accepted` / `:refused`:** the `reply` sub-arm also posts `outcome`.
  `fn2-conn-post-word (conn conn-gen request word outcome)` gains its fifth argument;
  `fn2-answer-outcome` renders "437 … (evidence recorded | evidence uncertain | evidence refused)".
- **`:uncertain`:** a declared stop of the kind (P2's `:stops (:txn-uncertain ...)` in this
  `defmachine`). The batch's journal write was reached and its fate is unknown. The core stops and
  recovery classifies it; B-S2 S7 fences the scope meanwhile.
- **Keystones owed:**
  - `fn2-txn-evidence-committed`: under ruling 6, a valid competing binding always commits its
    evidence or is reported uncertain, and is never refused silently;
  - `fn2-txn-reply-from-facts`: the reply is a function of `(sel evid cov)`;
  - `fn2-txn-no-double-charge`: a replayed offer charges once.
  Their teeth go in txn-unit.

### P.5 fn2-cursor, D6 1/n (new; written in the form, never in the old)
Its home is the new book `fn2/books/cursor.lisp`, after `machines-c-read`.
- The budget is `(:bytes 8192 :steps 32 :descriptors 0)`. §15.2's 4,096 is stale and §15.4's 8,192
  holds; the doc is fixed with this commit. The cursor issues nothing (cap 0).
- `:need-page`, `:inspect` and `:failed` are declared by the slices that reach them (D6 2/n and
  3/n), never as unreached phases.
- The read row x is `row-slot` (F7).

```lisp
(defmachine fn2-cursor
 :phases (:free :select :seek :render :send :finish :draining :retired)
 :fields ((conn :link) (conn-gen :u60) (request :u32) (line-s :u32) (line-e :u32)
          (group :u60) (current :u60) (view :u60) (access-ref :u32)
          (tag :u8) (reply :u16) (arg-off :u32) (arg-len :u32) (lo :u60) (hi :u60) (next :u60) (roff :u32)
          (count :u60) (low :u60) (high :u60) (seen :bool) (step :u8)
          (update (:enum fn2-cursor-update (:none :current :selection))) (more :bool) (done :bool)
          (tx-slot :link) (tx-gen :u60) (stopped :bool) (next-free :link))
 :holds ((:select :cursor-row) (:seek :cursor-row) (:render :cursor-row) (:send :cursor-row)
         (:finish :cursor-row) (:draining :cursor-row))
 :budget (:bytes 8192 :steps 32 :descriptors 0)
 :capacity (fn2-profile-x profile)
 :taken (:phase :select :rows :cursor-row :ranges ()
         :copy (conn conn-gen request line-s line-e group current view access-ref principal-slot)
         :clear (tag reply arg-off arg-len lo hi next roff count low high seen step update more done tx-slot tx-gen stopped))
 :initial ((generation fn2-machine-initial-generation) (conn *fn2-none*) (tx-slot *fn2-none*)
           (account-ref *fn2-none*) (next-free fn2-machine-initial-next-free))
 :subarms
 (;; the connection moved on (generation, query or request): drain (15.3)
  (cancel (:next :finish) (:charge :steps *fn2-work-transition* :runnable t))
  ;; TX back to the connection, the connection woken; wait in :send (15.3 step 2)
  (hand-back :on-refusal ((:stop :machine-phase))
   (:do (code) (fn2-cursor-hand-tx row-tx-slot row-tx-gen row-conn row-conn-gen))
   (:do () (fn2-conn-wake row-conn))
   (:next :send) (:charge :bytes 512 :steps *fn2-work-transition*))
  ;; a refusal line (411, 412, 420-423, 503 :no-projection) is a one-line page
  (refuse :on-refusal ((:stop :machine-phase))
   (:do (code) (fn2-cursor-render-status row-tag row-reply 0 0 0 0 row-tx-slot row-tx-gen))
   (:set (more 0) (done 1)) (:goto hand-back)))
 :arms
 ((:free (:idle))
  ;; accept TX, re-parse the line (<= 512 octets of the conn's RX under its
  ;; owner, ask F9), pin the view at GROUP/LISTGROUP, choose the read
  (:select :on-refusal ((:stop :machine-phase))
   (:cond ((not (fn2-cursor-conn-live-p row-conn row-conn-gen row-request id row-generation)) (:goto cancel))
          (t (:do (code tslot tgen) (fn2-cursor-accept-tx row-conn row-conn-gen)
              :accept (:ok :none) :why ":none is a hand not yet made: the take and the hand are one conn run")
             (:if (eq code :none) ((:charge :steps *fn2-work-empty*))
               ((:do (pcode tag aoff alen lo hi) (fn2-cursor-parse row-conn row-conn-gen row-line-s row-line-e))
                (:set (tx-slot tslot) (tx-gen tgen) (tag tag) (arg-off aoff) (arg-len alen) (lo lo) (hi hi) (step 0))
                (:next :seek) (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))))))
  ;; position the read: one bounded C step per call (C-S4), at most 32 calls a
  ;; run (ask F6); the tag chooses the read
  (:seek :on-refusal ((:stop :machine-phase))
   (:cond
    ((not (fn2-cursor-conn-live-p row-conn row-conn-gen row-request id row-generation)) (:goto cancel))
    ;; GROUP g / LISTGROUP g: the name in fn2-groups, then its counts at the view
    ((and (fn2-cursor-names-group-p row-tag) (equal row-step 0))
     (:do (kcode) (fn2-read-key-octets row-slot 0 (fn2-conn-rx-slot-of row-conn) (fn2-conn-rx-gen-of row-conn)
                                       row-arg-off row-arg-len :okind *fn2-conn-kind* :oslot row-conn :ogen row-conn-gen))
     (:do (lcode) (fn2-read-lookup row-slot *fn2-read-groups-sid* 4096)
      :accept ()
      :case (((:ok) (:do (fcode view) (fn2-read-frontier))
                    (:set (group (fn2-read-value-or-0 row-slot *fn2-groups-field-id*)) (view view) (step 1))
                    (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:absent) (:set (reply *fn2-nntp-reply-group-no-group*)) (:goto refuse))
             ((:miss) (:set (reply *fn2-nntp-reply-no-projection*)) (:goto refuse)))))
    ((and (fn2-cursor-names-group-p row-tag) (equal row-step 1))
     (:do (kcode) (fn2-read-key row-slot 0 row-group))
     (:do (lcode) (fn2-read-lookup row-slot *fn2-read-group-counts-sid* 4096)
      :accept ()
      :case (((:ok) (:set (count (fn2-read-value-or-0 row-slot *fn2-counts-field-count*))
                          (low (fn2-read-value-or-0 row-slot *fn2-counts-field-low*))
                          (high (fn2-read-value-or-0 row-slot *fn2-counts-field-high*))
                          (current (fn2-read-value-or-0 row-slot *fn2-counts-field-low*))
                          (update *fn2-cursor-update-selection*) (step 2) (next 0))
                    (:next :render) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:absent :miss) (:set (reply *fn2-nntp-reply-no-projection*)) (:goto refuse)))))
    ;; every other cursor command needs a selected group (412)
    ((equal row-group 0) (:set (reply *fn2-nntp-reply-no-group-selected*)) (:goto refuse))
    ;; STAT n / NEXT / LAST / OVER range: the overview range over (group, [lo, hi])
    ;; with hi bounded by the group's high (31 probes over [1, 2^31) otherwise,
    ;; read-unit)
    (t (:do (rcode) (fn2-read-range row-slot *fn2-read-overview-sid* *fn2-overview-field-number*
                                    (min row-hi (fn2-cursor-group-high row-group row-view))))
        (:set (next row-lo) (step 2))
        (:next :render) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))))
  ;; a page: restart the read at NEXT, render rows into TX while they fit (a row
  ;; longer than TX splits at ROFF); then hand TX back (15.4)
  (:render :on-refusal ((:stop :machine-phase))
   (:cond
    ((not (fn2-cursor-conn-live-p row-conn row-conn-gen row-request id row-generation)) (:goto cancel))
    (t (:do (code next roff seen done) (fn2-cursor-page row-slot row-tag row-next row-hi row-roff row-seen
                                                        row-count row-low row-high row-group
                                                        row-tx-slot row-tx-gen)
        :accept (:ok :stale) :why ":stale is a page whose overlay was sealed under it; the next page restarts at NEXT")
       (:set (next next) (roff roff) (seen seen) (done done) (more (if done 0 1)))
       (:goto hand-back))))
  ;; TX is the connection's; nothing to do until it hands it again (more) or
  ;; wakes this row to finish
  (:send
   (:cond ((not (fn2-cursor-conn-live-p row-conn row-conn-gen row-request id row-generation)) (:goto cancel))
          ((equal row-done 1) (:if (fn2-cursor-released-p row-conn row-conn-gen id)
                                   ((:next :finish) (:charge :steps *fn2-work-transition* :runnable t))
                                   ((:charge :steps *fn2-work-empty*))))
          (t (:do (code tslot tgen) (fn2-cursor-accept-tx row-conn row-conn-gen)
              :accept (:ok :none) :why ":none: the connection has not handed the next page's TX yet")
             (:if (eq code :ok)
                  ((:set (tx-slot tslot) (tx-gen tgen)) (:next :render)
                   (:charge :steps *fn2-work-transition* :runnable t))
                  ((:charge :steps *fn2-work-empty*))))))
  (:finish :on-refusal ((:stop :machine-phase))
   (:do (code) (fn2-read-release row-slot))
   (:next :draining) (:charge :steps *fn2-work-transition* :runnable t))
  (:draining
   (:let next (fn2-machine-free-head *fn2-cursor-admission-ordinal*))
   (:let retire (>= row-generation (fn2-machine-gen-limit)))
   (:set (generation (if retire row-generation (+ 1 row-generation))) (conn *fn2-none*) (conn-gen 0)
         (tx-slot *fn2-none*) (tx-gen 0) (next-free next) (wait-reason *fn2-wait-none*))
   (:next (:if retire :retired :free))
   (:do () (fn2-machine-reclaim-fn2-cursor id retire))
   (:charge :steps *fn2-work-release*))
  (:retired (:idle))))
```
**D's operations for the cursor** (cursor.lisp, each a defcost; pure ones stobj in, none out):
- pure: `fn2-cursor-conn-live-p (conn conn-gen request oslot ogen)` (the conn's generation,
  `query`, `query-gen` and request still name this row), `fn2-cursor-released-p`,
  `fn2-cursor-gen-of`, `fn2-cursor-names-group-p (tag)`, `fn2-cursor-group-high (group view)`,
  `fn2-read-value-or-0 (x f)` (C-S4's value, 0 unless `:ok`), `fn2-conn-rx-slot-of`, `fn2-conn-rx-gen-of`;
- with `:answers t`:
  - `fn2-cursor-accept-tx (conn conn-gen) -> (code tslot tgen)` and `fn2-cursor-hand-tx (tslot tgen
    conn conn-gen)`, which wrap pool.lisp's hand ops;
  - `fn2-cursor-parse (conn conn-gen s e) -> (code tag aoff alen lo hi)`, ≤ 512 octets under the
    conn's owner;
  - `fn2-cursor-render-status`, `fn2-cursor-page`, `fn2-cursor-selection -> (upd g c v)`;
  - on the conn's side, `fn2-conn-hand-tx`, `fn2-conn-accept-tx` and the pure
    `fn2-conn-query-state -> :handed | :more | :done | :gone | :busy`.

**The page operation.** `fn2-cursor-page` is a declared D operation (`:bytes 6144 :answers t`):
`*fn2-cursor-steps*` = 4 range steps of budget 128 over ≤ 8 sources (`fn2-read-next`), each entry
read by `fn2-read-value` / `fn2-read-octets` into TX by C-S4's copy, at most 2,048 octets rendered.
- The status line comes first on the first page (`next = lo`): GROUP 211, LISTGROUP 211 + list,
  STAT 223, NEXT/LAST 223, OVER 224 + rows.
- Then come numbers (LISTGROUP) or `NUMBER TAB line` (OVER), and the terminator when the read ends.
- NEXT/LAST/STAT also set `current` and `update :current`. The arm's `:set` then carries them, so
  the page returns them too.

The loop lives in the operation until F6 gives the form a bounded `:repeat`. LAST's bisection
(≤ 61 starts) lives in the same operation's `:last` case.

**fn2-conn's half (D6 1/n, the same commit):**
- **Fields and enum.** `fn2-conn` gains `:query`, the fields `query :link query-gen :u60 group
  current view :u60`, and `after :query`. §15.3 says `group article view` and §15.2 says `group
  current view`: the current article number is `current`, and the doc is fixed with this commit.
- **The answer and `:reply`.** `fn2-answer` answers `:query` for every cursor command, with nothing
  rendered. Frame's `:line` branch gains `((equal after *fn2-conn-after-query*) (:set (pos p)
  (auth-pending next) (request row-ordinal) (ordinal (+ 1 row-ordinal))) (:next :query) (:charge
  ...))`, where the line `[start, p)` is not consumed. `:reply`'s `:next` gains `:query`.
- **`:greeting`** pins the view: `(:do (fcode view) (fn2-read-frontier))` then `(:set ... (view
  view))`. `fn2-read-frontier (fn2-core) -> (mv code position)` is C-S4 (c), a pure read of C's
  `fn2-successor-published`. It is written and waits as a patch (State).

```lisp
  (:query :on-refusal ((:stop :machine-phase))
   (:cond
    ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
    ;; no cursor yet: take one (it is woken by the take) and hand it TX (15.3 step 1)
    ((equal row-query *fn2-none*)
     (:do (tcode x) (fn2-machine-take-fn2-cursor *fn2-none* id row-generation row-request row-start row-pos
                                                 row-group row-current row-view row-access-ref row-principal-slot)
      :case (((:no-row) (:park :taken fn2-cursor :steps *fn2-work-transition*))))
     (:let xgen (fn2-cursor-gen-of x))
     (:do (hcode) (fn2-conn-hand-tx row-tx-slot row-tx-gen x xgen))
     (:set (query x) (query-gen xgen))
     (:charge :steps *fn2-work-transition*))
    (t (:case (fn2-conn-query-state row-query row-query-gen row-request row-tx-slot row-tx-gen)
        ;; TX handed back by the matching cursor: send the page (15.3 step 3)
        ((:handed) (:do (code) (fn2-conn-accept-tx row-tx-slot row-tx-gen))
                   (:set (tx-off 0) (after *fn2-conn-after-query*)) (:next :reply)
                   (:charge :steps *fn2-work-transition* :runnable t))
        ;; back from :reply and the cursor has more: hand TX again
        ((:more) (:do (code) (fn2-conn-hand-tx row-tx-slot row-tx-gen row-query row-query-gen))
                 (:do () (fn2-conn-wake row-query))
                 (:charge :steps *fn2-work-transition*))
        ;; the last page was sent: copy the selection back, consume the line, let the cursor finish
        ((:done) (:let x row-query)
                 (:do (upd g c v) (fn2-cursor-selection row-query row-query-gen))
                 (:set (group (if (equal upd *fn2-cursor-update-selection*) g row-group))
                       (current (if (equal upd *fn2-cursor-update-none*) row-current c))
                       (view (if (equal upd *fn2-cursor-update-selection*) v row-view))
                       (query *fn2-none*) (query-gen 0) (start row-pos))
                 (:do () (fn2-conn-wake x))
                 (:next :command) (:charge :steps *fn2-work-transition* :runnable t))
        ;; a cursor gone while named: the query invariant broke
        ((:gone) (:stop :machine-phase))
        (:otherwise (:charge :steps *fn2-work-empty*))))))
```
- **Cancellation.** `:draining`'s wake becomes `(:do () (fn2-conn-wake (if (equal row-upload
  *fn2-none*) row-query row-upload)))`. One wake suffices because an upload and a query are never
  both live: `upload` is set only in `:article-input`, `query` only in `:query`, and neither phase
  reaches the other without passing `:reply` → `:command`, which clears both. That is owed row
  `fn2-conn-one-dependant`, and it answers gap 34 without a second wake slot.
- **The oracle's E rows** H turns live at this landing: "init with groups and profile limits" and
  "store init" (H14).

## Asks of the form seat (through main), from the 35 gaps
Each item maps gaps to an ask, or to D's own fix where the syntax already says it. Asks are in order
of need: F1-F3 block the ports, F4-F9 block D5 2/n and D6 1/n, and F10-F13 can come later.

**F1. Sub-arms take `:on-refusal`.** `fn2-arms-subs` builds the env with refusal nil
(machine-arms.lisp, `fn2-arms-env kind nil nil nil`). Every sub-arm above that declares
`:on-refusal` needs this: two lines, the options parse that arms already use.
- With it, a sub-arm's unrouted answer goes to its posture instead of `:machine-contract`.
- Until then, each `:do` in those sub-arms carries `:case ((:otherwise (:stop :machine-phase)))`.

**F2. A taken kind's take is a plain answer, and its park a step (gap 10).**
- Today `fn2-machine-take-K` parks the waiter inside itself (machines.lisp:1704-1714). Its defcost
  declares no `:own-writes`, so the waiter's `wait-reason ready-prev ready-next` writes are invisible
  and the owed FRAME rows fail on the park path.
- Asked:
  - the take's defcost gains `:answers (:ok :no-row)`;
  - with waiter `*fn2-none*` (already supported) it parks nothing;
  - a step `(:park :taken K [:steps E])` parks the row on K's ordinal FIFO with K's row kind as its
    wait reason: the generated `park` form, emitted as the step's call.
- Also asked: the take returns the target's generation, `(mv code id gen)`, which deletes
  `fn2-upload-gen-of`, `fn2-txn-gen-of` and `fn2-cursor-gen-of` (gap 11).

**F3. `:answers` on A's code-returning operations used by D.** `fn2-core-drop-prefix`
(machines-a-costs.lisp:79: `(:ok :more ...)`) and `fn2-machine-pool-borrows-read-code`, plus
`fn2-account-charge-core` (D's own; D adds it). C and B add theirs (P.3 (b)).

**F4. D0 wait kinds attached by their owners, the `:sealable` pattern, as steps (gap 22; B-S2
S6).**
- `(:park :batch-membership)`: B attaches the ready/grant pair (§11b S6). D adds the kind to
  resources.lisp.
- `(:park :identity-reservation)`: the claim table's FIFO. D attaches it, replacing `:reserve`'s
  `:wait` charge and the hand-computed waiter id `kind-base + w` in `fn2-claim-release-core`
  (txn.lisp:254).
- The ask: `:park` accepts any wait kind whose owner declared `(K-ready-p, K-grant-one)` in its
  own book, not only the three built-ins (machine-arms.lisp `:park` case).

**F5. A wake of another row is a step, counted (gap 9; cursor gap 34).**
- `(:wake-row E)` lowers to `fn2-machine-set-wake-id` after `fn2-machine-idp`. The generator refuses
  a path with two wakes, whether the run's own or another's. The slot is single, and today "one wake
  per run" is a comment (txn.lisp:152).
- D's `fn2-conn-wake`, `fn2-upload-wake`, `fn2-txn-wake-upload` and post-word's wake become this
  step plus a liveness expression.

**F6. A bounded repeat (gaps 13, 19, 31, 32).**
- The step is `(:repeat N (STEP ...) :until E)`, with derived cost N × the body's bound.
- With it:
  - `fn2-cursor-page`'s 4 range steps and `:seek`'s 32 C steps a run become arms;
  - the feed's and the count's per-octet loops can move into the range primitives by handle (A's
    copy-range/scan), rather than living as hand loops;
  - the "charges are self-reported" gap closes, because the charge becomes the sum of the called
    operations' declared bounds.
- Until then the loops stay inside declared D operations whose defcosts state the bound.

**F7. `row-slot` (gap 22).** The row's slot in its kind as an expression, read from the directory
like `id`. Claim row, successor tx, decision d, read row x and hasher row (3 + slot) are all
"indexed by the machine slot", by convention. The asked fact, `(K-row-slot id)` = the slot the take
or admission gave, is the index identity stated once.

**F8. Typed links (gaps 6, 11, 12, 24).**
- Declared as `:links ((upload :kind fn2-upload :slot upload :gen upload-gen [:back txn txn-gen])
  ...)`. The generator emits the liveness test (snapshot read code, generation, back-reference),
  and `(:live L)` is an expression.
- An owner override `:okind/:oslot/:ogen` is accepted only as a declared link's triple (gap 8).
  Cross-row reads go through the link's declared reader set, `(:read L F)`, which is the read set
  §2's frame theorems need.
- The phase protocols between kinds become a declared precondition of a link, e.g. `:when-phase
  (:article-input)` for post-word.

**F9. A range handed between rows (gaps 28, 29).**
- Asked: a hold `(:tx-range :handed-to fn2-cursor)`, plus the steps `(:hand RANGE L)` and
  `(:accept-hand RANGE L)`. They lower to `fn2-pool-hand` / `fn2-pool-accept-hand`.
- The D0 reservation stays with the holder while write authority moves with the pool owner.
- The invariant "owner = holder except between hand and hand-back" becomes a generated owed row.
- Reading the conn's RX line from the cursor is a link read of a range (`(:read-range conn
  rx-slot line-s line-e)`) with the conn's `:pinned (start pos)` while the link lives.
- Until then D writes the thin wrappers named in P.5. Their defcosts carry no D0 effect, which is the
  hidden hand the gap names.

**F10. A phase-valued field (gap 5).** `after` typed as `(:phase-subset (:command :article-input
:query :closing))`, so `(:next row-after)` is allowed and checked against the phases. Today the
nested `:if` in `:reply` says it.

**F11. Per-phase precision through a shared sub-arm (gap 3).** `(:goto work :from (:head
:receiving))`, or the generator recording each arm's `:next` as the reachable subset of the
sub-arm's leaves given `row-phase` tests. Today `(:head (:goto work))` derives the union, so `:head`
can be declared to reach `:sealed`.

**F12. Reachability (gaps 4, 35).** The generator reports a phase that no `:next` names, other than
the taken/admission phase and `:free`.
- D then deletes upload `:validating` and conn `:upgrading` in the port's follow-up commit.
- txn `:accepted`/`:uncertain` become reachable at D5 2/n.

**F13. Holds as multisets (gap 21).** Two `:chunk-window` ranges and two `fn2-core-release` calls
already say the multiset in the port, one `:effects` per call. Asked: the D0 check counts per call,
not per name, so the upload's two releases match its two takes.

**F14. Holds per path (D7 4/n-b, d-machines-nntp.md 13.8).** `:command` holds
`:principal-reservation` only while `reserved = :held`. D0 checks holds per arm
(a-to-d-arm-contracts.md:107); the asked change makes the posture each path ends in carry its holds,
as §6.3 already derives for refusal paths. The fallback is a phase `:requesting`.

**Already said by the syntax (D's own fixes at the port, no ask):**
- gaps 1, 2, 14, 25: the helpers are unrolled into steps;
- gap 15: postures come from `:on-refusal` and `:case`;
- gap 16: R6 is the `:issue` default `(:halt)`, kept on purpose;
- gap 17: refusal-as-phase is a routed `:case`;
- gap 18: `:dropped` is a `:why`'d `:accept`;
- gap 19: the conn feed charge, in P.1 (e);
- gap 20: the txn budget, in P.4;
- gap 23: rule enums. The port keeps the shared order; ask F8's link carries `:map` later;
- gap 26: the dead `filled` field;
- gap 27: handlers' `:next` is derived;
- gap 30: the selection copy-back is a `:do` of a pure reader;
- gap 33: the view pin is a `:set` from `fn2-read-frontier`;
- gap 34: cancellation, answered by `fn2-conn-one-dependant`.

## Seams each kind calls (signatures as in the books)

**fn2-conn.**
- A's pool and host primitives:
  - `fn2-gram-frame (left start pos overflow cap slot gen okind oslot ogen fn2-pool)` (grammar.lisp:71), `fn2-core-reset (slot gen okind oslot ogen)`, `fn2-core-drop-prefix (slot gen k cursor limit okind oslot ogen)` → `(code cursor)`, `fn2-core-release (slot gen okind oslot ogen fn2-core)` (core.lisp:186-205);
  - `fn2-issue-receive (cap-index cap-nonce slot gen len)`, `fn2-issue-send (cap-index cap-nonce slot gen off len may-release)`, `fn2-issue-close` (core.lisp:312-316; each also takes `okind oslot ogen principal`);
  - `fn2-machine-issue-result (id code bytes fn2-core)`, `fn2-machine-pool-borrows(-read-code)`, `fn2-machine-gen-limit`, `fn2-machine-free-head`, `fn2-machine-take-fn2-upload (waiter conn conn-gen request rule principal-slot fn2-core)` → `(mv code id fn2-core)`, `fn2-machine-reclaim-fn2-conn (id retire fn2-core)`, `fn2-machine-set-wake-id`.
- D's ledger: `fn2-account-unbook-ref (ref fn2-core)` and `fn2-account-charge-core (p k a fn2-core)` (accounts-core.lisp:76, :81).
- D's libraries:
  - `fn2-answer (s e mask pending posting seen flags real rslot rgen tslot tgen okind oslot ogen fn2-pool)` → `(mv code after pending fn2-pool)`, `fn2-answer-greeting/-block-open/-outcome/-overflow` (conn-answer.lisp:321-425);
  - `fn2-upload-feed (left i mode discard rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool)` → `(mv status i mode discard copied fn2-pool)` (upload-feed.lisp:127).
- Planned (D6): `fn2-pool-hand (slot gen okind oslot ogen tkind tslot tgen fn2-pool)`, `fn2-pool-accept-hand (slot gen tkind tslot tgen fn2-pool)` (pool.lisp:306, :315), and `fn2-machine-take-fn2-cursor`.

**fn2-upload.**
- B: `fn2-b3-init`, `fn2-b3-update (row slot gen off len okind oslot ogen fn2-digests fn2-b3 fn2-pool)` (blake3.lisp:344), `fn2-b3-finalize (dst row fn2-digests fn2-b3)`, `fn2-digest-store (left row slot gen off okind oslot ogen fn2-digests fn2-pool)` (format-check.lisp:109).
- A: `fn2-core-release`, `fn2-machine-take-fn2-txn (waiter upload upload-gen conn conn-gen request rule principal-slot fn2-core)` → `(mv code id fn2-core)`, `fn2-machine-reclaim-fn2-upload`, `fn2-feed-cap`, `fn2-gram-read (slot gen idx okind oslot ogen fn2-pool)` (grammar.lisp:39).
- D: `fn2-upload-scan (budget off field visible fields lines seen mo ml no nl po pl slot gen okind oslot ogen fn2-pool)` (upload-scan.lisp:234), `fn2-upload-verdict (rule status seen mo ml po pl len bound cslot cgen cs cl ck co cg slot gen okind oslot ogen fn2-pool)` (:358), `fn2-conn-post-word (conn conn-gen request word fn2-core)` → `(mv code fn2-core)` (upload.lisp:311).

**fn2-txn.**
- C, identity, groups and successor (C-S1, C-S2, C-S3/S3a):
  - `fn2-identity-offer (d mslot mgen moff mlen dslot dgen doff okind oslot ogen fn2-core)` → `(mv code fn2-core)`, `fn2-identity-step (d budget fn2-core)` → `(mv answer fn2-core)` (machines-c.lisp:223, :234);
  - `fn2-group-lookup (tx slot gen off len okind oslot ogen budget fn2-core)` → `(mv code group fn2-core)` (machines-c-groups.lisp:332);
  - `fn2-successor-put (tx i sid kind)`, `fn2-successor-arg (tx i j src value)`, `fn2-successor-arg-octets (tx i j slot gen off len okind oslot ogen)`, **`fn2-successor-arg-octets-late (tx i j max)`**, `fn2-successor-resolve (tx budget)` → answer, `fn2-successor-stage (tx)` → `(mv code i fn2-core)`, **`fn2-successor-fill-octets (tx i j slot gen off len okind oslot ogen)`**, `fn2-successor-out (tx i f fn2-core)` → `(mv code value)`, `fn2-successor-bind (tx batch event)`, `fn2-successor-release (tx)` (machines-c-bind.lisp:444-527; each also takes `fn2-core` and returns `(mv code fn2-core)` unless noted);
  - `fn2-ribbon-hash (n slot gen off seed okind oslot ogen fn2-pool)` (ribbon.lisp:117, layer C).
- B-S2: `fn2-commit-admit-txn (member-slot member-gen bytes okind oslot ogen fn2-core)` → `(mv code batch event fn2-core)`. It is an interim that answers `:not-served` (txn.lisp:215).
- D, claims: `fn2-claim-begin (c hash slot gen off len ok os og fn2-claims)`, `fn2-claim-walk (c budget fn2-claims fn2-pool)`, `fn2-claim-release (c fn2-claims)` (claims.lisp:40, :126, :177).
- A: `fn2-gram-read`, `fn2-machine-kind-base`, `fn2-machine-reclaim-fn2-txn`, `fn2-machine-free-head`, `fn2-machine-gen-limit`.

**fn2-cursor (planned, C-S4, fn2/docs/d-machines-nntp.md 15.8):**
- `fn2-read-key (x j value)`, `fn2-read-key-octets (x j slot gen off len okind oslot ogen)`;
- `fn2-read-lookup (x sid budget)` → `:ok :absent :more :miss`;
- `fn2-read-range (x sid pfield plimit)`, `fn2-read-next (x budget)` → `:entry :end :more :miss`;
- `fn2-read-identity (x mslot mgen moff mlen okind oslot ogen budget)` → `(mv code article)`;
- `fn2-read-value (x f)` and `fn2-read-octets (x f dslot dgen okind oslot ogen)`, both now `(mv code ...)`;
- `fn2-read-frontier ()` → position, `fn2-read-release (x)`, and `fn2-read-scan` / `fn2-read-scan-next` (D6 2/n);
- every one takes `fn2-core`. A's `fn2-pool-hand` / `fn2-pool-accept-hand` and `fn2-machine-take-fn2-cursor`, and B's and C's `(:storage-job :read)` (S-ARTICLE-LOCATION).
