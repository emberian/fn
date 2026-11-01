# fn2 layer D continuation (present state, rewritten whole; 2026-10-31 night, the tenth Opus seat)

Seat: Opus, layer D. The seat writes the code itself. Briefs: `build/coordinator/briefs/FN2-LAYER-D-MACHINES-NNTP.md`
and FN2-SEAT-COMMON.md. **The flow is `build/coordinator/fn2/WORKFLOW-20261031.md`**: a commit = the changed books
certify, the scenarios for what you touched pass, you read your diff; push by path; READY one line with the sha;
fix forward. **Boxes (main, 10-31 night):** certify on **hbox** (`swarm-build`, PID files; no new data on /tank;
the lane clone is `~/fn2-d6-lane/work` on `hbox-saas`); forge is the measurement box; the Mac is REPL only
(its load is high).

## Rulings in force
- **Machine form (ember, 10-31).** No arms in the old form. The form as built: MACHINE-FORM §6.10 (G2
  7a0edee7a, arm tuple 65ebca019, P4 cb903f15c, per-arm tuples 24fce1ecd, one shape theorem per generated
  function 82eb2bfc2). D's four kinds port to it (P.1-P.4 below); the cursor is already child form.
- **Identity across peers** (`IDENTITY-ACROSS-PEERS-20261030.md`): D owns rulings 1, 6, 8 in the txn port;
  replies are decided from the separate facts C's decision returns, never from a summary code.
- **Argon review rulings for the txn port (main, 10-31 night; REVIEW-ARGON-RESPONSE-20261031.md):**
  (1) one encoding: C's `fn2-successor-out` emits the member workspace from the staged slots in B's
  record kinds (article acceptance, identity records, memberships, overview, addr, the folds' events,
  the outcome); `:ready` passes that workspace to `fn2-commit-admit-txn`, never a hand-serialized
  subset (this replaces P.4's `fn2-txn-write-records` step); replay feeds the same slots back.
  (2) stage-time `:refused` is reachable (catch-up, generated-Message-ID POSTs without a claim,
  resolution statements): `:ready` replans to evidence-only on stage `:refused`, never a stop; restate
  claim stability accordingly. (3) once any batch is `:uncertain` the node's serving posture is
  `:draining`: new POST/append/IHAVE are refused by word at admission (`:unaffordable` with the
  uncertain reason), never parked behind the uncertain claim; the commit kind exposes the posture
  and the txn reads it (D9's ServicePosture brought forward). (4) small, any time: `fn2-resource-rank`
  = 1 + position in `*fn2-resource-order*`, the hand `:rank` keys and the length pin go; the twin
  bundle/release tables are deleted at the conn port once every kind declares `:holds`/`:effects`.
- **B's forms for these (dev c0645b91e, b-durability.md §11b):** S11 `(fn2-commit-posture fn2-core) ->
  (:serving :draining)`, a read op (defcost naming fn2-machines), `:draining` exactly while some commit
  row is `:uncertain`; `:ready` reads it before staging. S12: pass `fn2-successor-out`'s workspace to
  `fn2-commit-admit-txn` unchanged.
- **The form, latest (dev):** 144596771 derives `*fn2-turn-transition-max*` from the registry (cursor and
  txn budgets are inside the turn bound). a0556c390 (G3 2/n) gives the conn port its language: F14 holds
  per path `(K :while (F V ...))` (`:principal-reservation :while (reserved :held)`), F8 typed `:links`
  (cross-row reads of upload/txn/cursor move to links; a linked kind stops writing okind/oslot/ogen by
  hand), `:phase-subset` fields (conn's `after`), per-path findings at defmachine-run.
- **Never stand by.** While the txn port waits on C's §4a sha, do D's breadth that waits on nothing.

## State (dev)
- **D6 1/n** eee0eb09e + a466488fe: the cursor (GROUP, LISTGROUP name, NEXT, LAST, STAT n/<id>, OVER/XOVER).
- **Argon ruling (4)** 49e7df92f: `fn2-resource-rank` = 1 + position; no `:rank` keys, no length pin.
- **H20 item 2** 689d196a1: sim-session.lsp serves reading over three seeded articles in local.test
  (reader-only profile: *fn2-cursor-profile* less :posting-interim). A's native session is A's.
- **D6 1/n-b** 068fd597a (on dev, 12410f1b9 merge; cursor-unit green at that tip on hbox):
  - LIST ACTIVE / COUNTS / NEWSGROUPS without a wildmat and bare LISTGROUP, through a scan of
    `fn2-groups` in name order (d-machines-nntp.md §15.0 is the as-built record).
  - TX's prefix `[0, roff)` is the cursor's across pages: the connection truncates TX to roff after a
    query page (A's new `fn2-pool-truncate` / `fn2-core-truncate`) and empties it after the last.
    A scan pads TX to a 256-octet key area, gives TX as its workspace (the key lands at offset 0),
    and starts pages after it.
  - Read rows (E's seam, taken): `fn2-b-read-rows` = 2X + N (machines-b.lisp). Cursor slot S reads
    through 2S (and LIST's counts through 2S+1); E's consumer request S through 2X+S
    (`fn2-b-cns-rows`, profile `:cns`). The cursor's capacity is `fn2-b-cursor-rows`. Linear fact
    `fn2-b-read-rows-parts`. E must define `fn2-cns-capacity` as `fn2-b-cns-rows` and keep the base 2X
    in its config child.
  - The interim JSON regenerated (notes only; the table is unchanged); upload-model's pin regenerated
    (H20's model sha).
  - cursor.lisp is 83 s on hbox (over the minute): the form seat's notes say fn2-cursor-render's
    preserves (17 s: close its callees, tau off), the take (10 s) and `:seek` are what is left.
- **Still 503:** OVER <id> (needs the txn's article-to-number address entries), LIST with a wildmat,
  ACTIVE.TIMES, SUBSCRIPTIONS; ARTICLE/HEAD/BODY (3/n).
- Earlier on dev: c7972899d the frontier; 00c493d32 D7 4/n-a (§13.8); 721f7a50b the D7 4/n statement.
- **Arrived for the txn port (P.4):** B-S2 6d4e7f977 (`fn2-commit-admit-txn (slot gen len okind oslot
  ogen) -> (mv code batch event)` `(:ok :exhausted :admission)`; `fn2-commit-take (:ok :pending :none)`;
  `fn2-commit-txn-source`; `fn2-block-read` / `-done`); C §4a NOT yet on dev at 7798b9e35 (main sends
  the sha). C §4a's API as planned: `fn2-identity-decide-start tx mslot mgen moff mlen dslot dgen doff
  okind oslot ogen`; `fn2-identity-decide tx budget`; `fn2-identity-facts tx -> (mv code verdict
  selection h evidence coverage)`; slots evidence 1, history 11, summary 13, candidate 12, article 14.
- B's cd45d4719 (fn2-b-ctl-rows, format slots floor 4 + w + c) is merged; it touched machines-b
  beside the read rows.

## Next, in order
1. **The txn port P.4** the moment main sends C's §4a sha: P.4 below as amended by the Argon rulings (the member workspace is `fn2-successor-out`'s, passed unchanged; stage `:refused` replans to evidence-only; `fn2-commit-posture` `:draining` refuses new POSTs by word),
   `(:park :batch-membership)` on `:exhausted`, the `:consumer` mode with E's declared op then
   `(:wake-row cns)`, C's location bind from `fn2-commit-txn-source`, replies from the facts (rulings 6,
   7, 8), the `fn2-consumer-names` fold at register when main sends C's schema sha), and D5 2/n: the
   durable POST, 240 after publication, posting advertised (`fn2-answer-posting-p` on), D5's interim
   rows leaving. `(defmachine-registry fn2-txn)` is declared; its arms go to child form with the port.
2. **OVER <id>** after the port (the address entries).
3. **D6 3/n** ARTICLE/HEAD/BODY over `fn2-block-read` / `-done` and the location field; the conn port
   when the form's G3 lands (a child-form `(:park :principal-reservation)` needs
   `fn2-account-request-park`'s defcost to name a `:child`).
4. When convenient: cursor.lisp under the minute (above).
- **Commands (hbox):** sync `git push hbox-saas:fn2-d6-lane/work HEAD:refs/heads/<b>` then on hbox
  `git checkout -q <b>` (the clone's working copy holds only my copies). Certify detached:
  `cd ~/fn2-d6-lane/work && rm -f build/rN.status; (setsid sh -c "swarm-build sh fn2/tools/forge-certify.sh -j 16 <tests...> > build/rN.out 2>&1; echo rc=\$? > build/rN.status" > /dev/null 2>&1 < /dev/null &); sleep 2; ps -eo pgid,cmd | grep "build/rN.out" | grep -v grep | awk "{print \$1}" | head -1 > build/rN.pid`.
  Stop with `kill -- -$(cat build/rN.pid)`. Interim JSON: `python3 tools/acl2 < fn2/tests/conn-interim-export.lsp | python3 fn2/tests/conn-interim-json.py`
  with FN_ACL2/ACL2_SYSTEM_BOOKS set. Forge tree `/build/lanes/d6` (branch d6-read at 82eb2bfc2 plus
  scp'd files; its wip branch d6-forge-wip-1031 holds a466488fe's content).

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
- Sub-arms are defined in order: a `(:goto X)` needs X defined above it in `:subarms`.
- An old-form `defmachine-callback` body refuses `b*` `(unless ...)` binders: use `mv-let` + `if`.
- `fn2-pool-preserves ... :disable nil` leaves the function open; a later core wrapper's
  preserves proof then opens it and fails. Leave the default (disabled).
- Copying files with `tar` keeps the Mac's mtimes, so a box's stale `.cert` looks current
  (book-hash mismatch on include). `touch` copied books, or copy with `cat >`.
- A capacity that moves to a new function needs a `:linear` fact tying it to what the profile
  predicates bound (`fn2-b-read-rows-parts`), or the per-child init guards fail (assembly-init).
- `make-event :or` prints ACL2 errors from its first attempt even when the fallback passes:
  judge a certify by its status and the `.cert`, not by grepping "ACL2 Error".

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
- **`mode :consumer`** (E's E.P1 seam, e-continuation.md; one transaction path, D's).
  - Fields gained: `cns :link cns-gen :u60 cevent (:enum fn2-txn-cevent (:ack :rebase)) cid :u60 cepoch
    :u32 ca :u60 cb :u60 op :u60`.
  - **Amendment: one take.** `fn2-machine-take-fn2-txn` has one copy list, so `:taken`'s `:copy` is the
    union with `mode` copied too. The article taker (the upload) passes `*fn2-none*`/0 for the consumer
    fields; `fn2-cns` passes `*fn2-none*`/0 for `upload upload-gen conn conn-gen rule`.
  - `:admit` routes on `row-mode`: `(:if (equal row-mode *fn2-txn-mode-consumer*) ((:next :prepare)
    (:charge ...)) ...)`. That skips `:admit`, `:reserve` and `:lookup`, with no Message-ID and no
    claim, so `:releasing` skips the claim release by the same test.
  - `:prepare` (consumer) puts slot 0, `fn2-consumer-cursor`, by `cevent` with args `(cid cepoch ca)`
    or `(cid cepoch ca cb)`, and slot 1, `fn2-outcome ':insert (principal op request outcome event)`.
    Then it resolves.
  - `:ready` is the same stage, admit and bind; there are no records beyond B's encodings of the two
    slots.
  - **Amendment: the outcome reaches `cns` by a declared operation, not by a wake alone.** The reply
    sub-arm for `:consumer` does `(:do (pcode) (fn2-cns-post-outcome row-cns row-cns-gen row-op
    outcome) :accept (:ok :dropped) :why "a cancelled request takes no outcome")`. That is E's op,
    generation-checked, on the post-word pattern. Then it does `(:wake-row row-cns)` (F5). The cns row
    reads its outcome in its own fields, because the txn drains right after.
  - C's `:applied` / `:unchanged` per fold slot, E's seam to C, comes back through `fn2-successor-stage`.
    The txn maps `:unchanged` on slot 0 to the outcome word `behind`, never `accepted`.
- **Keystones owed:**
  - `fn2-txn-evidence-committed`: under ruling 6, a valid competing binding always commits its
    evidence or is reported uncertain, and is never refused silently;
  - `fn2-txn-reply-from-facts`: the reply is a function of `(sel evid cov)`;
  - `fn2-txn-no-double-charge`: a replayed offer charges once.
  Their teeth go in txn-unit.

### P.5 fn2-cursor (built: `fn2/books/cursor.lisp` is the declaration; §15.0 the record)

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
