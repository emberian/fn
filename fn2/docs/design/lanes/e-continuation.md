# layer E continuation (the E seat's notebook; rewritten whole after every commit)

## Built (dev)
- E3 (6187c6aa0), E3b (5be98c474): port.lisp, consumer-port, consumer-model, owed-consumer, the mini/helm fixtures; layout.lisp's big-endian kinds; consumer-codec.lisp (FNCT, fncu v1/v2, k4 codes 0-18, replies 5/6/9/28, items) and its unit.
- E4a (8754482a1), E4b (291f953b8): peer model, owed-peer, six witnesses; §13 in wire words.
- E5a/E5c (043b32fba, 63172fea2): cns-edges.lisp (buckets = rows, doubly linked chains, free list + fresh, pending-bucket stack, BPOS link race `:behind`, grant clears `:wait-row`); G-LIVE at child level. Certifies in 43 s on hbox under load (under the minute; D's 64 s was the laptop).
- 65ebca019: arm tuple (K five . EXTRA) in machine-arms.lisp.
- E5d (36d26a8da, merged 109ad246b): sim/check-consumer.lisp (CONSUMER), tests/sim-layer-e.lisp (oracle node, 5 scenarios, 5 controls), K10 stated (producer constrained).
- E.P1a (db4b561f0, merged to dev as 788eed64d over D6 1/n; the merged tip certifies on forge: assembly with cursor and cns, sim/sim, sim-layer-e, cns-edges-unit): books/cns.lisp. The edge table is the core child `fn2-core-cns-edges`, rows = the ledger's :subscription-edge capacity (`fn2-account-profile-capacity`, :esub else 4096), `:profilep` states rows >= that capacity and rows < 2^31; `fn2-cns-edge-link-core` (`:answers (:ok :behind :exhausted)`) and `fn2-cns-edge-unlink-core` are defcosts with `:child`; `(defwait :wait-row :ready fn2-cns-wait-ready-p :grant fn2-cns-wait-grant-one)`, attached in assembly-access (`fn2-cns-wait-events`, after D's request events) to core faces over (edges machines control), liveness from `fn2-cns-grant-one-live`. assembly-index includes cns after txn.
- Uncommitted: nothing.

## State of E.P1 (the served consumer): BLOCKED on seams the old notebook did not list
Read against dev 109ad246b: E.P1's two kinds are a design, not a paste. Ops they call that do not exist and
cannot be written inside E without another layer's sizing or records:
1. **Request decode and reply encode: ANSWERED by B at cd45d4719** (a different shape from the ask, which stands as B built it):
   connection S's format slot is `(fn2-b-ctl-slot s profile)` = 4 + w + s; that slot's `fn2-b3` row hashes the FNCT
   trailer, and its 128-row field stripe at 128 x slot holds the codec's decode and encode, both from that one index.
   fn2-ctl's `:capacity` is `(fn2-b-ctl-rows profile)` (profile key `:control-connections`, default 2, the tiny
   profile's); `:format-slots` floor/default is 4 + w + c; `fn2-b-ctl-slot-below-floor` is proved. When pasting, take the
   field base from the slot (128 x slot), not from a separate stripe below the read stripes.
2. **Read rows** (C, D): C's read row X is "one per query cursor slot", `(fn2-b-read-rows profile)` = :x when
   :reading; D6 1/n's cursor kind (cursor.lisp, on dev eee0eb09e) owns [0, x) by its slot. Ask: read rows = x + cns capacity, cns row S uses x + S.
3. **Consumer ids** (C, D): the cursor fold's key is `(:id consumer)` (u60); the wire's consumer is 1-64
   octets per principal. Nothing maps one to the other. Ask: a fold `fn2-consumer-names` keyed ((principal
   (:id principal)) (name (:octets 64))) value ((consumer (:id consumer))), `:unique`, written by register's
   transaction. Until register serves (D's txn port), every cursor verb answers unknown-consumer.
4. **The hook's members** (C): `fn2-commit-stream-wake (batch fn2-core)` must find the batch's fn2-addr
   writes; only C can enumerate them. Ask: `(defcost fn2-successor-stream-member :child ... :answers (:ok
   :done :state))`, (mv code stream position next) for cursor I of published batch BATCH.
5. **Page items** (D6 3/n): an item carries the article's Message-ID and octets (`*fn2-fnct-item-layout*`);
   fn2-addr's row holds only (article stream reasons). Read/wait items wait for the article read op.
6. Smaller, E's own once 1-5 land: an E config child (owner uid for the `:local` check, max wait, the read
   row base), a clock read over fn2-ops (no `fn2-clock` exists; D7's timer service later), cross-row reads
   of ctl/cns liveness as declared ops (G3's `(:read L F)` later), `fn2-read-value` routed (E.P1's
   `fn2-read-value-or-0` was an absorb).
So before D's txn port and D6 3/n, a served ctl/cns pair could only refuse; BRICKS §5 already orders
"cns served over the local socket, K10" after D6 3/n and D5 2/n, and e-surface's owed line says the same.

## Next
1. When main answers seams 1-4 (exact forms above): E's config child, then fn2-ctl (admission through the
   listener with `:listener-targets fn2-ctl` in the simulator profile and the fixture peer record standing
   in for A's :local listener; owner check; FNCT framing by deflayout over the stripe; take of fn2-cns
   core-form; TX hand), then fn2-cns (decode, Grant/Meter interims, cursor lookup, read/park on the edge,
   answer), the hook attached, then the simulator adapter as K10's producer and sim-layer-e's scenarios
   against it. register/ack/append/fetch/rebase/unregister refuse `unavailable` until their sources land.
2. Under ember's spine-only ruling: PARK otherwise (no design, witnesses, §13 or new seams).

## Pitfalls / commands
- Box: hbox is DOWN (ember, 10-31): certify on forge only, my clone `/build/lanes/fn2-e` (branch fn2-e-base pushed from the laptop), `build/cert.sh BOOKS` (forge-certify -j 6 under swarm-build), detached with setsid so `build/cert.pid` is the group leader; stop with `kill -- -$(cat build/cert.pid)`. The hbox scratch `/tank/fn/scratch/fn2-e` is lost.
  A copied tree carries `build/fn2-certify.lock`; remove the copy's lock before its first run.
- REPL: `python3 tools/acl2 --timeout 400 < build/e-seat/<x>.lsp > build/e-seat/<x>.out 2>&1`.
- defwait's ready/grant names are introduced by the access section's encapsulate: never define them yourself;
  attach your core faces to them after `(fn2-machine-access-events)`.
- A kind whose arm calls `fn2-machine-take-K` must be core form (the take has no :child before the assembly).
- must-fail on defport needs :expected :hard; defcarrier refuses soft. Test dispatchers hard-error on an
  undeclared layout. fn1's ACL2 world does not load in this tree.

## E.P1: the two kinds as designed (a design until seams 1-5 land; the op names below are placeholders
## where the list above says so)
### fn2-ctl (the L carrier; Accept on the `:local` listener)
```lisp
(defmachine fn2-ctl
 :phases (:free :greeting :frame :dispatch :waiting :reply :closing :draining :retired)
 :fields ((rx-slot :link) (rx-gen :u60) (tx-slot :link) (tx-gen :u60) (fill :u32) (pos :u32)
          (flen :u32) (fkind :u8) (cns :link) (cns-gen :u60) (owner :bool) (tx-off :u32) (tx-len :u32)
          (request :u32) (next-free :link))
 :holds ((:greeting :connection-row :rx-range :tx-range) (:frame :connection-row :rx-range :tx-range)
         (:dispatch :connection-row :rx-range :tx-range :principal-reservation)
         (:waiting :connection-row :rx-range :tx-range :principal-reservation)
         (:reply :connection-row :rx-range :tx-range) (:closing :connection-row :rx-range :tx-range))
 :budget (:bytes 8192 :steps 32 :descriptors 1)
 :capacity (fn2-ctl-capacity profile)
 :admission (:listener :local :copy (peer-family peer-w0))
 :initial ((generation fn2-machine-initial-generation) (cns *fn2-none*) (next-free fn2-machine-initial-next-free))
 :arms
 ((:free (:idle))
  ;; the owner check before any byte (e-surface 4.2: 0600 socket, peer UID checked)
  (:greeting :on-refusal ((:stop :machine-phase))
   (:if (fn2-ctl-owner-p row-peer-family row-peer-w0)
        ((:set (owner 1) (fill 0) (pos 0)) (:next :frame) (:charge :steps *fn2-work-transition* :runnable t))
        ((:next :closing) (:charge :steps *fn2-work-transition* :runnable t))))
  ;; one FNCT frame: the 10-octet header (magic, version, kind, u32be length), then the payload and the
  ;; 32-octet BLAKE3 trailer, at most 4 + 1 + 1 + 4 + max-payload + 32 octets in RX
  (:frame :on-refusal ((:stop :machine-phase))
   (:do (code kind len) (fn2-ctl-frame row-rx-slot row-rx-gen row-pos row-fill)
    :accept (:frame :need-more :bad) :why ":bad closes (fn1: a malformed frame ends the session)")
   (:case code
    ((:frame) (:set (fkind kind) (flen len) (request (+ 1 row-request))) (:next :dispatch)
              (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
    ((:need-more) (:issue (receive row-rx-slot row-rx-gen row-fill) :ok ((:wait :completion :bytes 4096))))
    ((:bad) (:next :closing) (:charge :steps *fn2-work-transition* :runnable t))))
  ;; take a request row and hand it the frame and TX (as fn2-conn's :query hands the cursor)
  (:dispatch :on-refusal ((:stop :machine-phase))
   (:do (tcode x) (fn2-machine-take-fn2-cns *fn2-none* id row-generation row-request row-pos row-flen
                                            row-fkind row-principal-slot)
    :case (((:no-row) (:park :taken fn2-cns :steps *fn2-work-transition*))))
   (:let xgen (fn2-cns-gen-of x))
   (:do (hcode) (fn2-ctl-hand-tx row-tx-slot row-tx-gen x xgen))
   (:set (cns x) (cns-gen xgen)) (:next :waiting) (:charge :steps *fn2-work-transition*))
  ;; the request row hands TX back with one reply frame; a parked wait keeps it until wake or timeout
  (:waiting
   (:case (fn2-ctl-cns-state row-cns row-cns-gen row-request)
    ((:handed) (:do (code off len) (fn2-ctl-accept-tx row-tx-slot row-tx-gen))
               (:set (tx-off off) (tx-len len) (cns *fn2-none*) (cns-gen 0)) (:next :reply)
               (:charge :steps *fn2-work-transition* :runnable t))
    ((:gone) (:stop :machine-phase))
    (:otherwise (:charge :steps *fn2-work-empty*))))
  (:reply :on-refusal ((:stop :machine-phase))
   (:issue (send row-tx-slot row-tx-gen row-tx-off row-tx-len)
    :ok ((:do () (fn2-ctl-consume row-rx-slot row-rx-gen (+ row-pos row-flen)))
         (:set (pos 0) (fill (fn2-ctl-rest row-fill row-pos row-flen))) (:next :frame)
         (:wait :completion :bytes 4096))))
  (:closing (:issue (close-socket) :ok ((:next :draining) (:wait :completion))))
  (:draining
   (:let next (fn2-machine-free-head *fn2-ctl-admission-ordinal*))
   (:let retire (>= row-generation (fn2-machine-gen-limit)))
   (:do () (fn2-ctl-wake-cns row-cns row-cns-gen))     ; a live request row drains with its connection
   (:set (generation (if retire row-generation (+ 1 row-generation))) (cns *fn2-none*) (next-free next)
         (wait-reason *fn2-wait-none*))
   (:next (:if retire :retired :free)) (:do () (fn2-machine-reclaim-fn2-ctl id retire))
   (:charge :steps *fn2-work-release*))
  (:retired (:idle))))
```

### fn2-cns (one request; a parked wait is this row parked)
```lisp
(defmachine fn2-cns
 :phases (:free :decode :check :lookup :read :page :park :commit :draining :retired)
 :fields ((ctl :link) (ctl-gen :u60) (request :u32) (fpos :u32) (flen :u32) (fkind :u8)
          (verb (:enum fn2-cns-verb (:none :register :read :wait :ack :position :status :append :fetch
                                     :rebase :unregister)))
          (consumer :u60) (epoch :u32) (op :u60) (to :u60) (start :u60) (limit :u16) (timeout :u32)
          (deadline :u60) (pos :u60) (version :u60) (frontier :u60) (count :u16) (more :bool)
          (outcome (:enum fn2-cns-outcome (:none :accepted :refused :uncertain))) (reason :u8)
          (posted (:enum fn2-cns-posted (:none :accepted :unchanged :refused :uncertain))) (posted-word :u8)
          (edge :link) (txn :link) (txn-gen :u60) (tx-slot :link) (tx-gen :u60) (tx-len :u32)
          (next-free :link))
 :holds ((:decode :request-row) (:check :request-row) (:lookup :request-row :cursor-row)
         (:read :request-row :cursor-row) (:page :request-row :cursor-row)
         (:park :request-row :wait-row :subscription-edge) (:commit :request-row :transaction-row))
 :budget (:bytes 8192 :steps 32 :descriptors 0)
 :capacity (fn2-cns-capacity profile)
 :taken (:phase :decode :rows :request-row
         :copy (ctl ctl-gen request fpos flen fkind principal-slot)
         :clear (verb consumer epoch op to start limit timeout deadline pos version frontier count more outcome
                 reason posted posted-word edge txn txn-gen tx-slot tx-gen tx-len))
 :initial ((generation fn2-machine-initial-generation) (ctl *fn2-none*) (edge *fn2-none*) (txn *fn2-none*)
           (next-free fn2-machine-initial-next-free))
 :subarms
 (;; the reply frame into TX (kind 28 with the verb's result, or fn1's 5/6/9 for codes 0-10), then hand
  (answer :on-refusal ((:stop :machine-phase))
   (:do (code len) (fn2-cns-render row-fkind row-verb row-outcome row-reason row-pos row-version row-frontier
                                   row-count row-more row-tx-slot row-tx-gen))
   (:set (tx-len len)) (:goto hand))
  (hand :on-refusal ((:stop :machine-phase))
   (:do (code) (fn2-cns-hand-tx row-tx-slot row-tx-gen row-tx-len row-ctl row-ctl-gen))
   (:do () (fn2-ctl-wake row-ctl))
   (:next :draining) (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
  (refuse (:set (outcome *fn2-cns-outcome-refused*)) (:goto answer))
  ;; register and ack: take a consumer transaction (txn mode :consumer, the D seam) and park on its outcome
  (begin-commit :on-refusal ((:stop :machine-phase))
   (:do (tcode tx) (fn2-machine-take-fn2-txn *fn2-none* id row-generation ':consumer
                                             (if (eq row-verb :register) *fn2-txn-cevent-rebase* *fn2-txn-cevent-ack*)
                                             row-consumer row-epoch row-to row-start row-op row-principal-slot)
    :case (((:no-row) (:park :taken fn2-txn :steps *fn2-work-transition*))))
   (:set (txn tx) (txn-gen (fn2-txn-gen-of tx))) (:next :commit) (:park :cns-wake :steps *fn2-work-transition*))
  (cancel (:next :draining) (:charge :steps *fn2-work-transition* :runnable t)))
 :arms
 ((:free (:idle))
  ;; FNCT kind 4 / 22 payload from the connection's RX under its owner: code -> verb, fields -> row
  (:decode :on-refusal ((:stop :machine-phase))
   (:cond ((not (fn2-cns-ctl-live-p row-ctl row-ctl-gen row-request id row-generation)) (:goto cancel))
          (t (:do (code verb cid ep op to start limit timeout reason)
                  (fn2-cns-decode row-ctl row-ctl-gen row-fpos row-flen row-fkind
                                  :okind *fn2-ctl-kind* :oslot row-ctl :ogen row-ctl-gen)
              :accept (:ok :refused) :why ":refused carries fn1's refusal word (consumer-codec's 21 words)")
             (:set (verb verb) (consumer cid) (epoch ep) (op op) (to to) (start start) (limit limit)
                   (timeout timeout) (reason reason))
             (:if (eq code :refused) ((:goto refuse))
                  ((:next :check) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))))))
  ;; Grant, then Meter (e-surface 6): the consumer belongs to the row's principal (interim: L's owner
  ;; principal holds every consumer of this node); the interim verbs refuse `unavailable`
  (:check :on-refusal ((:stop :machine-phase))
   (:cond ((member-eq row-verb '(:append :fetch :rebase :unregister))
           (:set (reason *fn2-cns-reason-unavailable*)) (:goto refuse))
          ((not (fn2-cns-grant-p row-principal-slot row-consumer)) (:set (reason *fn2-cns-reason-access*)) (:goto refuse))
          ((not (fn2-cns-meter-p row-principal-slot row-verb)) (:set (reason *fn2-cns-reason-meter*)) (:goto refuse))
          ((eq row-verb :register) (:goto begin-commit))
          (t (:next :lookup) (:charge :steps *fn2-work-transition* :runnable t))))
  ;; the cursor: (consumer, epoch) -> (position, version); absent is `scope` (fn1 k4 code 3)
  (:lookup :on-refusal ((:stop :machine-phase))
   (:do (kcode) (fn2-read-key row-slot 0 row-consumer))
   (:do (kcode) (fn2-read-key row-slot 1 row-epoch))
   (:do (lcode) (fn2-read-lookup row-slot *fn2-consumer-cursor-sid* 4096)
    :accept ()
    :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
           ((:absent) (:set (reason *fn2-cns-reason-scope*)) (:goto refuse))
           ((:miss) (:set (reason *fn2-cns-reason-unavailable*)) (:goto refuse))
           ((:ok)
            (:set (pos (fn2-read-value-or-0 row-slot *fn2-consumer-cursor-field-position*))
                  (version (fn2-read-value-or-0 row-slot *fn2-consumer-cursor-field-version*)))
            (:cond ((eq row-verb :ack)
                    (:cond ((<= row-to row-pos) (:set (reason (if (equal row-to row-pos) *fn2-cns-reason-equal*
                                                                *fn2-cns-reason-behind*))) (:goto refuse))
                           ((> row-to (fn2-cns-frontier)) (:set (reason *fn2-cns-reason-beyond-frontier*)) (:goto refuse))
                           (t (:goto begin-commit))))
                   ((member-eq row-verb '(:position :status))
                    (:set (frontier (fn2-cns-frontier)) (outcome *fn2-cns-outcome-accepted*)) (:goto answer))
                   (t (:next :read) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t)))))))
  ;; read and wait: the principal's addr stream from pos + 1 to the frontier, one page (wait is read: K4)
  (:read :on-refusal ((:stop :machine-phase))
   (:do (k) (fn2-read-key row-slot 0 (fn2-account-principal-id row-principal-slot))) (:do (k) (fn2-read-key row-slot 1 (+ 1 row-pos)))
   (:do (rcode) (fn2-read-range row-slot *fn2-addr-sid* *fn2-addr-field-position* (fn2-cns-frontier)))
   (:set (frontier (fn2-cns-frontier)) (count 0)) (:next :page)
   (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
  (:page :on-refusal ((:stop :machine-phase))
   (:cond ((not (fn2-cns-ctl-live-p row-ctl row-ctl-gen row-request id row-generation)) (:goto cancel))
          (t (:do (code count more) (fn2-cns-page row-slot row-count row-limit row-tx-slot row-tx-gen)
              :accept (:ok :stale) :why ":stale: the overlay was sealed under the page; the read restarts")
             (:cond ((eq code :stale) (:next :read) (:charge :steps *fn2-work-transition* :runnable t))
                    ;; an empty page of a wait parks until news or the deadline (now + timeout, capped
                    ;; by *fn2-fnct-max-wait-seconds*, armed once)
                    ((and (equal count 0) (eq row-verb :wait) (equal row-deadline 0) (< 0 row-timeout))
                     (:set (deadline (+ (fn2-clock) (min row-timeout *fn2-fnct-max-wait-seconds*)))) (:next :park)
                     (:charge :steps *fn2-work-transition* :runnable t))
                    ((and (equal count 0) (eq row-verb :wait) (< (fn2-clock) row-deadline))
                     (:next :park) (:charge :steps *fn2-work-transition* :runnable t))
                    (t (:set (count count) (more more) (outcome *fn2-cns-outcome-accepted*)) (:goto answer))))))
  ;; parked: one edge on the stream from pos + 1; woken by the publish hook (or the timeout), it reads again
  (:park :on-refusal ((:stop :machine-phase))
   (:cond ((not (fn2-cns-ctl-live-p row-ctl row-ctl-gen row-request id row-generation))
           (:do () (fn2-cns-edge-unlink row-edge)) (:goto cancel))
          ((equal row-edge *fn2-none*)
           (:do (code e) (fn2-cns-edge-link (fn2-cns-addr-stream row-principal-slot) id row-generation (+ 1 row-pos))
            :case (((:exhausted) (:set (reason *fn2-cns-reason-meter*)) (:goto refuse))))
           (:set (edge e)) (:park :cns-wake :steps *fn2-work-transition*))
          ((>= (fn2-clock) row-deadline)
           (:do () (fn2-cns-edge-unlink row-edge)) (:set (edge *fn2-none*) (count 0) (more 0)
                                                         (outcome *fn2-cns-outcome-accepted*)) (:goto answer))
          (t (:do () (fn2-cns-edge-unlink row-edge)) (:set (edge *fn2-none*)) (:next :read)
             (:charge :steps *fn2-work-transition* :runnable t))))
  ;; register and ack: a consumer transaction (txn mode :consumer, the D seam); its outcome wakes this row
  (:commit :on-refusal ((:stop :machine-phase))
   ;; the txn posted its outcome into this row (fn2-cns-post-outcome: row-posted, row-posted-word) and woke it
   (:case row-posted
    ((*fn2-cns-posted-accepted*) (:set (outcome *fn2-cns-outcome-accepted*) (pos row-to)) (:goto answer))
    ((*fn2-cns-posted-unchanged*) (:set (reason *fn2-cns-reason-behind*)) (:goto refuse))
    ((*fn2-cns-posted-refused*) (:set (reason row-posted-word)) (:goto refuse))
    ((*fn2-cns-posted-uncertain*) (:set (outcome *fn2-cns-outcome-uncertain*)) (:goto answer))
    (:otherwise (:park :cns-wake :steps *fn2-work-empty*))))
  (:draining
   (:let next (fn2-machine-free-head *fn2-cns-admission-ordinal*))
   (:let retire (>= row-generation (fn2-machine-gen-limit)))
   (:do (code) (fn2-read-release row-slot))
   (:set (generation (if retire row-generation (+ 1 row-generation))) (ctl *fn2-none*) (edge *fn2-none*)
         (txn *fn2-none*) (next-free next) (wait-reason *fn2-wait-none*))
   (:next (:if retire :retired :free)) (:do () (fn2-machine-reclaim-fn2-cns id retire))
   (:charge :steps *fn2-work-release*))
  (:retired (:idle))))
```
`:cns-wake` is an owner-declared wait kind (F4), woken by `fn2-cns-wake-stream` and by the txn outcome
(F5). `fn2-clock` is the latest clock observation (D7's services row); `fn2-cns-frontier` reads C's
`fn2-successor-published` (the D6 1/n patch's `fn2-read-frontier`, pure). In `:park`, a woken row unlinks
its edge and reads again; a wake that finds nothing re-parks through `:page`, so a wake is never lost (K4b)
and never answers an empty page before the deadline.


### Acceptance (K10 owed)
The scenarios of tests/sim-layer-e.lisp against the served kinds over the simulator (L carrier, the fixture
peer record for the :local listener), each run's observations checked by CONSUMER; K10's producer
`fn2-cns-served-observations` becomes that run. Until register serves, the served node can only refuse, so
the run is meaningful from D's txn port and D6 3/n on.
