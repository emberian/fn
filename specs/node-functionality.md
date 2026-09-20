# The node functionality F_node and its refinement

Status: design, wave 4. No book in this document exists yet; every ACL2 form
below is a *statement to be certified*, written against the definitions that
do exist at `9321344`, with the names of those definitions used exactly. The
prefixes `fn-ideal-`, `fn-dtn-` and `fn-sys-` are reserved here and must be
registered in [`docs/prefixes.md`](../docs/prefixes.md) by the packet that
first admits them (P0 below). Counts live in the generated ledger and nowhere
in this document.

The document answers one question the review left open: what is the single
object that the functional-correctness theorems refine, such that "clients
cannot crash us regardless of what they send" and "we implement the semantics"
are two consequences of one refinement rather than two families of unrelated
lemmas. The object is an ideal functionality in the sense of Canetti (2001),
written as an ACL2 state machine. Because fn's authority is noncryptographic
in the current profile, the refinement's simulator is the identity and the
whole statement is a deterministic trace refinement that ACL2 can check end
to end. The place where that stops being true, and what changes there, is
stated exactly in section 2.3.

Conventions. `step(state, event) -> (state', effects)` as in
[architecture](../docs/architecture.md), rendered `(mv s2 effects)`. The
shapes of claims follow [proofs](../docs/proofs.md#shape-of-the-claims): an
invariant with a reachable witness, one-step preservation, trace induction.
Nothing here is a proof; a proposed theorem is not a theorem proved by ACL2.

## 1. F_node as an ACL2 state machine

### 1.1 State

The state is chosen so that every existing subsystem machine is a field
accessor, not a reconstruction. The relay state already composes the three
durable machines: `fn-relay-statep` (`books/relay.lisp:95`) requires
`(fn-bp-binding-statep (fn-relay-sender rs))`,
`(equal (fn-bp-state-node (fn-relay-sender rs)) (fn-sn-node (fn-relay-store rs)))`,
a receiver `fn-bpr-statep`, a terms table and undertakings. F_node adds what
the relay lacks: configuration, connections with version pins, the clock
observation and the outbox of effects not yet acknowledged by the host.

```lisp
;; books/ideal-node.lisp (P0)
(defun fn-ideal-make-config (groups capacity max-conns line-limit body-limit
                             bp-config bpr-config terms)
  (list groups capacity max-conns line-limit body-limit bp-config bpr-config terms))

(defun fn-ideal-configp (c)
  (and (true-listp c) (equal (len c) 8)
       (fn-string-listp (fn-ideal-config-groups c))
       (fn-no-duplicatesp (fn-ideal-config-groups c))
       (natp (fn-ideal-config-capacity c))
       (natp (fn-ideal-config-max-conns c))
       (posp (fn-ideal-config-line-limit c))          ; 510 in host/reader-host.lisp:93
       (posp (fn-ideal-config-body-limit c))          ; 8192 there
       (fn-bp-configp (fn-ideal-config-bp c))
       (fn-bpr-configp (fn-ideal-config-bpr c))
       (fn-relay-terms-tablep (fn-ideal-config-terms c))))

;; One connection: wire framing state, NNTP session, pinned committed version.
(defun fn-ideal-make-conn (id wire session version) (list id wire session version))

(defun fn-ideal-connp (c g)                 ; g = current committed generation
  (and (true-listp c) (equal (len c) 4)
       (natp (fn-ideal-conn-id c))
       (fn-wire-statep (fn-ideal-conn-wire c))
       (fn-nntp-sessionp (fn-ideal-conn-session c))
       (natp (fn-ideal-conn-version c))
       (<= (fn-ideal-conn-version c) g)))

(defun fn-ideal-make-state (config relay conns clock outbox)
  (list config relay conns clock outbox))

;; Committed history and generation are projections of the store, never
;; separate fields: the generation is the durable frontier.
(defun fn-ideal-store   (s) (fn-relay-store (fn-ideal-relay s)))
(defun fn-ideal-history (s) (fn-sf-records (fn-sn-files (fn-ideal-store s))))
(defun fn-ideal-generation (s) (fn-sf-frontier (fn-sn-files (fn-ideal-store s))))
(defun fn-ideal-node    (s) (fn-sn-node (fn-ideal-store s)))
(defun fn-ideal-archive (s) (fn-node-acceptance (fn-ideal-node s)))
(defun fn-ideal-pins    (s) (fn-retain-pins (fn-node-retention (fn-ideal-node s))))

;; The archive a connection reads: the replay of the first `version` records
;; at frontier `version` (the owner design's pinned prefix).
(defun fn-ideal-pinned-archive (s conn)
  (fn-node-acceptance
   (fn-sf-replay-node (fn-ideal-config-groups (fn-ideal-config s))
                      (fn-ideal-config-capacity (fn-ideal-config s))
                      (take (fn-ideal-conn-version conn) (fn-ideal-history s))
                      (fn-ideal-conn-version conn))))
```

The recognizer carries every invariant the served path needs, so that no
theorem about a step re-validates the whole state (assurance rule "No
whole-state revalidation on a served path"):

```lisp
(defun fn-ideal-statep (s)
  (and (true-listp s) (equal (len s) 5)
       (fn-ideal-configp (fn-ideal-config s))
       (fn-relay-invp (fn-ideal-relay s))                       ; books/relay.lisp:307
       (fn-snt-relation (fn-ideal-store s))                     ; books/store-node-traces.lisp:111
       (equal (fn-sn-groups (fn-ideal-store s)) (fn-ideal-config-groups (fn-ideal-config s)))
       (equal (fn-sn-capacity (fn-ideal-store s)) (fn-ideal-config-capacity (fn-ideal-config s)))
       (fn-ideal-conn-listp (fn-ideal-conns s) (fn-ideal-generation s))
       (fn-no-duplicatesp (fn-ideal-conn-ids (fn-ideal-conns s)))
       (<= (len (fn-ideal-conns s)) (fn-ideal-config-max-conns (fn-ideal-config s)))
       ;; every session is consistent with the archive it is pinned to
       (fn-ideal-sessions-consistentp s (fn-ideal-conns s))     ; fn-nntp-session-consistentp per conn
       (or (null (fn-ideal-clock s)) (fn-clock-observationp (fn-ideal-clock s)))
       (fn-ideal-effect-listp (fn-ideal-outbox s))))
```

State components and where each already lives:

| F_node component | Field | Existing machine and recognizer |
| --- | --- | --- |
| Committed history, generation | `(fn-ideal-history s)`, `(fn-ideal-generation s)` | `fn-sf-records`, `fn-sf-frontier` of the `fn-sn` store under `fn-snt-relation` |
| Configuration | `(fn-ideal-config s)` | `fn-sn-groups`/`fn-sn-capacity`, `fn-bp-configp`, `fn-bpr-configp`, `fn-relay-terms-tablep`; clock-stamped group facts arrive with C1-05 |
| Connections | `(fn-ideal-conns s)` | `fn-wire-statep` × `fn-nntp-sessionp` × version pin (w2 owner `fn-own-*`) |
| Obligations | `(fn-ideal-pins s)`, `(fn-bp-state-works (fn-relay-sender ...))`, receiver contexts/receipts, `fn-relay-undertakings` | `fn-retain-statep`, `fn-bp-binding-statep`, `fn-bpr-statep`, `fn-relay-invp` |
| Pins | version pins in `conns`; retention pins in the node | owner keystones; `fn-node-articles-have-archive-bindingsp` |
| Pending transaction | `(fn-sf-phase (fn-sn-files store))`, `(fn-node-stage node)` | `fn-sf-phase-shapep`, `fn-node-stagep` |
| Clock | `(fn-ideal-clock s)` | `fn-clock-observationp` |

### 1.2 Environment interface

Inputs are events; each names the port it arrives on. The environment Z
controls every input on every port; nothing below assumes a well-formed
event, and section 3 makes that a theorem.

```lisp
;; Client ports (one per connection). Octets are an arbitrary list; the
;; partition into reads is the environment's choice.
;;   (:open id)                (:octets id octets)         (:close id)
;; Host observations.
;;   (:store ev)     ev is an fn-snrt event: (:prepare record) (:io op result)
;;                   (:finish) (:crash frontier-choice record-choice) (:recover)
;;                   and the resolution events of store-node-resolution-traces
;;   (:reopen frontier records)          ; fn-sn-open-observed after a crash cut
;;   (:clock obs)                        ; fn-clock-observationp
;;   (:contact plan)                     ; contact plan, consumed by scheduling only
;;   (:advance id)                       ; host lets a connection see the current generation
;; Peer port (from F_dtn, section 5.4).
;;   (:bundle src-eid octets)            ; any octets; fn-bpa-decode-exact decides
;; Transport observations returned by the BPA.
;;   (:transport work attempt gen status) (:no-contact work attempt gen)
;;   (:retry work attempt gen policy)    (:restart)
;; Operator port.
;;   (:post record) (:declare-group name) (:enqueue ...) (:undertake ...) (:release receipt-id)

(defun fn-ideal-event-kindp (k)
  (member-equal k '(:open :octets :close :advance :store :reopen :clock :contact
                    :bundle :transport :no-contact :retry :restart
                    :post :declare-group :enqueue :undertake :release)))
```

Outputs are effects; every effect is typed and the type is closed:

```lisp
(defun fn-ideal-effectp (e)
  (and (true-listp e) (consp e)
       (case (car e)
         (:reply   (and (natp (cadr e)) (fn-nntp-effectp (fn-nntp-reply-effect (caddr e)))))
         (:close   (natp (cadr e)))
         (:write   (fn-ideal-write-requestp (cdr e)))     ; the fn-sn-io operations, in order
         (:submit  (fn-ideal-submit-requestp (cdr e)))    ; (:submit work attempt adu), bp-workflow's effect
         (:delete  (fn-ideal-delete-requestp (cdr e)))    ; BPA copy after durable staging
         (:receipt (fn-ideal-receipt-adup (cdr e)))       ; fn-bpr-receipt-adu / fn-relay-receipt-adu bytes
         (:refused (member-equal (cadr e) *fn-ideal-refusals*))
         (:uncertain t)
         (otherwise nil))))
```

`*fn-ideal-refusals*` is the closed enumeration of every refusal reason the
subsystems already produce: the `fn-wire-close` reasons, the NNTP status
lines `fn-nntp-single` emits for a refused command, the store refusals
(`fn-sn-refuse-reservation`, capacity, duplicate Message-ID), the BPA
boundary refusals (`fn-bpa-result-message`), and the policy refusals. It is
finite by construction and section 3.4 states the theorem that nothing else
comes out.

### 1.3 Transition relation

`fn-ideal-step` dispatches on the event kind to the existing machine for that
port. Nothing semantic is written twice.

```lisp
(defun fn-ideal-step (s e)
  (declare (xargs :guard t))                 ; guard t: section 3.1 makes this the theorem
  (if (not (fn-ideal-statep s))
      (mv s (list (list :refused :not-a-state)))
    (case (fn-ideal-event-kind e)
      (:octets    (fn-ideal-octets-step s (fn-ideal-event-id e) (fn-ideal-event-octets e)))
      (:open      (fn-ideal-open-step s (fn-ideal-event-id e)))
      (:close     (fn-ideal-close-step s (fn-ideal-event-id e)))
      (:advance   (fn-ideal-advance-step s (fn-ideal-event-id e)))
      (:store     (fn-ideal-store-step s (fn-ideal-event-store e)))
      (:reopen    (fn-ideal-reopen-step s (fn-ideal-event-frontier e) (fn-ideal-event-records e)))
      (:clock     (fn-ideal-clock-step s (fn-ideal-event-obs e)))
      (:bundle    (fn-ideal-bundle-step s (fn-ideal-event-src e) (fn-ideal-event-octets e)))
      ((:transport :no-contact :retry :restart)
                  (fn-ideal-sender-step s (fn-ideal-bp-event-of e)))
      ((:post :declare-group :enqueue :undertake :release)
                  (fn-ideal-operator-step s e))
      (otherwise  (mv s (list (list :refused :unknown-event)))))))

;; The served path. One connection, one chunk of any length.
(defun fn-ideal-octets-step (s id octets)
  (let ((conn (fn-ideal-find-conn id (fn-ideal-conns s))))
    (if (not conn)
        (mv s (list (list :refused :no-such-connection)))
      (let* ((drive   (fn-wire-drive (fn-ideal-conn-wire conn) octets))   ; books/wire-invariants.lisp:334
             (wire2   (fn-wire-result-state drive))
             (run     (fn-ideal-nntp-run (fn-ideal-conn-session conn)
                                         (fn-ideal-pinned-archive s conn)
                                         (fn-wire-result-events drive)))
             (session2 (mv-nth 0 run))
             (replies  (fn-ideal-tag-replies id (mv-nth 1 run)))
             (closing  (equal (fn-wire-state-mode wire2) :closed)))
        (mv (fn-ideal-update-conn s (fn-ideal-make-conn id wire2 session2
                                                        (fn-ideal-conn-version conn)))
            (append replies (if closing (list (list :close id)) nil)))))))

;; fn-nntp-step folded over the wire events, accumulating effects.
;; fn-nntp-run-session (books/nntp-invariants.lisp:810) is the session half.
(defun fn-ideal-nntp-run (session archive events)
  (if (consp events)
      (let* ((r (fn-nntp-step session archive (car events)))
             (rest (fn-ideal-nntp-run (fn-nntp-result-session r) archive (cdr events))))
        (mv (mv-nth 0 rest) (append (fn-nntp-result-effects r) (mv-nth 1 rest))))
    (mv session nil)))

;; Store events are fn-snrt-step on the embedded store; the relay keeps the
;; sender's node equal to the store's node (fn-relay-statep).
(defun fn-ideal-store-step (s ev)
  (mv (fn-ideal-with-store s (fn-snrt-step (fn-ideal-store s) ev))
      (fn-ideal-store-effects (fn-ideal-store s) ev)))     ; the next :write request, or nil

(defun fn-ideal-sender-step (s bp-event)
  (let ((r (fn-bp-step (fn-relay-sender (fn-ideal-relay s)) bp-event)))     ; books/bp-workflow.lisp:757
    (mv (fn-ideal-with-sender s (fn-bp-result-state r))
        (fn-ideal-submit-effects (fn-bp-result-effects r)))))

(defun fn-ideal-bundle-step (s src octets)
  (let ((decoded (fn-bpa-decode-exact octets)))
    (if (not (fn-bpa-result-okp decoded))
        (mv s (list (list :refused :bundle-undecodable)))
      (let ((request (fn-bpa-result-value decoded)))
        (if (fn-bpa-request-article request)
            (fn-ideal-ingress-step s src request)      ; fn-bpi-ingress-prepare on the store
          (fn-ideal-receipt-step s src request))))))   ; fn-relay-accept / fn-bp-prepare-receipt
```

`fn-ideal-run` folds `fn-ideal-step` over an event list and collects
effects: `(mv final (append effects...))`.

Every subsystem machine is a projection. These are the commuting squares the
book must prove; each is an equality with `fn-ideal-statep` as its only
hypothesis, so a later theorem about the ideal step can be discharged by the
subsystem's own keystone.

```lisp
(defthm fn-ideal-octets-projects-to-wire
  (implies (and (fn-ideal-statep s) (fn-ideal-find-conn id (fn-ideal-conns s)))
           (equal (fn-ideal-conn-wire
                   (fn-ideal-find-conn id (fn-ideal-conns (mv-nth 0 (fn-ideal-step s (list :octets id octets))))))
                  (fn-wire-result-state
                   (fn-wire-drive (fn-ideal-conn-wire (fn-ideal-find-conn id (fn-ideal-conns s))) octets)))))

(defthm fn-ideal-octets-projects-to-nntp
  (implies (and (fn-ideal-statep s) (fn-ideal-find-conn id (fn-ideal-conns s)))
           (let ((conn (fn-ideal-find-conn id (fn-ideal-conns s))))
             (equal (fn-ideal-conn-session
                     (fn-ideal-find-conn id (fn-ideal-conns (mv-nth 0 (fn-ideal-step s (list :octets id octets))))))
                    (fn-nntp-run-session (fn-ideal-conn-session conn)
                                         (fn-ideal-pinned-archive s conn)
                                         (fn-wire-result-events
                                          (fn-wire-drive (fn-ideal-conn-wire conn) octets)))))))

(defthm fn-ideal-store-projects-to-snrt
  (implies (fn-ideal-statep s)
           (equal (fn-ideal-store (mv-nth 0 (fn-ideal-step s (list :store ev))))
                  (fn-snrt-step (fn-ideal-store s) ev))))

(defthm fn-ideal-transport-projects-to-bp
  (implies (fn-ideal-statep s)
           (equal (fn-relay-sender (fn-ideal-relay (mv-nth 0 (fn-ideal-step s (list :transport w a g st)))))
                  (fn-bp-result-state
                   (fn-bp-step (fn-relay-sender (fn-ideal-relay s)) (fn-bp-transport-event w a g st))))))

(defthm fn-ideal-receipt-bundle-projects-to-relay
  (implies (and (fn-ideal-statep s) (fn-ideal-receipt-requestp octets))
           (equal (fn-ideal-relay (mv-nth 0 (fn-ideal-step s (list :bundle src octets))))
                  (car (cdr (fn-relay-accept (fn-ideal-relay s)
                                             (fn-ideal-record-of s octets)
                                             (fn-bpa-result-value (fn-bpa-decode-exact octets))
                                             (fn-assume-policy-authorizedp
                                              (fn-ideal-policy-id s) (fn-ideal-terms s) octets)))))))

;; Frame conditions: an event on one port leaves the other ports' state alone.
(defthm fn-ideal-octets-leave-store-alone
  (equal (fn-ideal-store (mv-nth 0 (fn-ideal-step s (list :octets id octets))))
         (fn-ideal-store s)))
(defthm fn-ideal-store-leaves-connections-alone
  (equal (fn-ideal-conns (mv-nth 0 (fn-ideal-step s (list :store ev))))
         (fn-ideal-conns s)))
```

The last projection is where the authority oracle enters: the `authorized`
argument of `fn-relay-accept` / `fn-bpr-accept-request` and the
`policy-authorizedp` argument of `fn-bp-prepare-receipt` are, in F_node,
the constrained function `fn-assume-policy-authorizedp`
(`books/assumptions.lisp:243`). Section 2.3 explains why that is legitimate.

### 1.4 Initial states and reachability

```lisp
(defun fn-ideal-initial-state (config)
  (fn-ideal-make-state config
                       (fn-relay-initial-state (fn-sn-initial (fn-ideal-config-groups config)
                                                              (fn-ideal-config-capacity config))
                                               (fn-ideal-config-bpr config)
                                               (fn-ideal-config-bp config)
                                               (fn-ideal-config-terms config))
                       nil nil nil))

(defthm fn-ideal-initial-state-is-state
  (implies (fn-ideal-configp config) (fn-ideal-statep (fn-ideal-initial-state config))))

(defthm fn-ideal-step-preserves-state
  (implies (fn-ideal-statep s) (fn-ideal-statep (mv-nth 0 (fn-ideal-step s e)))))   ; no hypothesis on e

(defthm fn-ideal-run-preserves-state
  (implies (fn-ideal-statep s) (fn-ideal-statep (mv-nth 0 (fn-ideal-run s events)))))
```

The reachable witness (assurance rule "Teeth ship with the theorem") is one
`fn-ideal-run` over a trace that opens two connections, posts through the
store events, advances one connection, receives a bundle, emits a receipt,
crashes with a `fn-sf-crash-imagep` choice, reopens, and reads again: every
event kind once, every port once, mirroring the w2 owner witness and the
17-event node witness.

## 2. The refinement claim

### 2.1 The real system R

R is the running system: `tools/run_owner.py` (the one process that holds a
store: it pins a committed version per connection, serializes durable posts
through `fn-own-take-submission` and serves readers and POST on one
listener, w2 and w5), `tools/run_reader.py` (read-only, answers POST with
440) and `tools/run_store.py` over `host/*.lisp`, over the certified books,
over the BPA. Its observable trace is the sequence of port events and the
effects performed: bytes written to a socket, files written and barriered,
bundles submitted or deleted, receipt bytes returned. The environment sees
exactly this.

Two facts about R fix the shape of the claim.

1. The core is the theorem subject (review §5, "no wrapper laundering").
   `host/reader-host.lisp:106-113` calls `fn-wire-next` and `fn-nntp-step`;
   `host/store-node-host.lisp` calls `fn-sn-prepare`, `fn-sn-io`,
   `fn-sn-finish`, `fn-sn-open-observed`; `host/bp-receipt-host.lisp` calls
   `fn-bpr-accept-request`, `fn-bpr-prepare-receipt`, `fn-bpr-commit-receipt`,
   `fn-bpr-receipt-adu`; `host/workflow-host.lisp` calls
   `fn-bp-replay-journal` and `fn-bp-apply-journal-record`.
2. The glue is not in a certified book. `fn-reader-chunk`
   (`host/reader-host.lisp:104`) is `:mode :program` and the `while pending:`
   loop in `tools/run_reader.py:222` iterates it. Together they compute
   `fn-wire-drive`, but no theorem says so, which is precisely the
   `pending_subject` note on the wire row of `planning/proof-events.json:256`.

### 2.2 The relation and the statement

State relation ρ between R and F_node: the host's globals and files
correspond to the fields of `fn-ideal-statep`.

| R component | F_node field |
| --- | --- |
| `fn-reader-wire`, `fn-reader-session`, the Python `pending` suffix | `(fn-ideal-conn-wire conn)`, `(fn-ideal-conn-session conn)`; `pending` is unconsumed input, not state |
| `fn-reader-archive` (a snapshot at open) | `(fn-ideal-pinned-archive s conn)` |
| on-disk records, frontier file, phase | `(fn-ideal-store s)` under `fn-snt-relation` |
| workflow journal, receipt journal | `(fn-relay-sender ...)`, `(fn-relay-receiver ...)` via `fn-bp-replay-journal`, `fn-bprr-replay` |
| BPA inventory | in flight in F_dtn (section 5.4), not in F_node |

The claim is a deterministic trace refinement, stated in three layers.

Layer A (inside ACL2, the whole of the served path): the certified function
the host calls per event equals the ideal step.

```lisp
;; books/ideal-node-host.lisp (P1): the loop of host/reader-host.lisp:104 and
;; tools/run_reader.py:222, written once in logic mode, guard t, and then
;; called from fn-reader-chunk instead of being re-implemented there.
(defun fn-ideal-serve (s e) (declare (xargs :guard t)) (fn-ideal-step s e))

(defthm fn-ideal-serve-is-the-ideal-step
  (equal (fn-ideal-serve s e) (fn-ideal-step s e)))         ; by definition; named so, cited never
```

The theorem with content is the one that retires the `pending_subject` note:
the reader's chunk loop, as an ACL2 function `fn-reader-drive` mirroring
`fn-reader-chunk`'s body under the `while pending:` iteration, is
`fn-wire-drive` followed by `fn-ideal-nntp-run`:

```lisp
(defthm fn-reader-drive-is-ideal-octets-step
  (implies (and (fn-wire-statep wire) (fn-nntp-session-consistentp session archive)
                (fn-wire-octet-listp octets))
           (equal (fn-reader-drive wire session archive octets)
                  (let* ((drive (fn-wire-drive wire octets))
                         (run   (fn-ideal-nntp-run session archive (fn-wire-result-events drive))))
                    (list (fn-wire-result-state drive) (mv-nth 0 run) (mv-nth 1 run))))))
```

Its proof is `fn-wire-drive-is-feed-proper` (`books/wire-invariants.lisp:512`)
plus `fn-wire-next-strictly-consumes` (`:292`) for the measure, and the
partition theorem `fn-wire-drive-partition-independence` (`:561`) makes the
chunking irrelevant.

Layer B (the host contract, A-HOST): the host feeds each port's bytes in
order and unaltered, reports each I/O outcome honestly and once, and
performs each effect exactly. This is `fn-assume-host-events` and
`fn-assume-host-report` (`books/assumptions.lisp:134`), the encapsulate that
C1-15 introduced and no theorem yet takes as a hypothesis. The refinement
statement takes it: with `fn-assume-host-events` applied to the event list
and `fn-assume-host-report` to each `:io` result, R's trace is
`(mv-nth 1 (fn-ideal-run (fn-ideal-initial-state config) events))`. That
sentence is checked by ACL2 in the form "the host's event list is the
identity image under the constrained function", and by tests for the part
that is Python: `tests/test_reader_partitions.py` (every partition gives the
same replies) and `tests/test_host_boundary.py` (octets cross as decimal
literals; no other path exists).

Layer C (the crash schedule): a process death is an event `(:store (:crash
fc rc))` with the choices ranging over `fn-sf-crash-imagep`, and a restart
is `(:reopen frontier records)` through `fn-sn-open-observed`. A cut the
model cannot express is a fidelity defect, not a passing test (assurance
rule D4). A-DURABILITY enters exactly as the `fn-sf-crash-imagep` hypothesis
of `:reopen`, discharged per platform by functional instantiation of
`fn-assume-durability-image` as [proofs](../docs/proofs.md#qualifying-a-platform-against-a-durability)
describes.

The composed statement, in UC vocabulary: for every environment Z (every
input sequence on every port, every partition, every crash schedule), the
trace of R with the dummy adversary equals the trace of F_node with the
dummy adversary. Equality, not indistinguishability: the system is
deterministic and there is no secrecy in the current profile (D04 defers
confidentiality), so "leakage" to the adversary is the whole trace and the
simulator has nothing to hide.

### 2.3 Why the simulator is trivial, where it stops being, and why the noncryptographic instance is legitimate

In Canetti's framework a protocol π UC-realizes F when for every adversary A
there is a simulator S such that no environment distinguishes (π, A) from
(F, S). The completeness of the dummy adversary (Canetti 2001, claim 10 in
the 2020 revision) lets one fix A to the dummy that forwards messages, so S
has one job: given only what F reveals, produce for Z the network view the
real protocol would have produced. S is nontrivial exactly when the real
view contains values that F abstracts away.

fn's current profile abstracts nothing away. F_node emits the same bytes R
emits: replies are `fn-nntp-effectp` octets, receipts are
`fn-bpr-receipt-adu` octets, writes are the records. Authority is a decision
by the oracle `fn-assume-policy-authorizedp`, and R makes the *same* call:
the host passes the `authorized` boolean it obtained from configuration (the
unsigned trusted-loopback profile of [bp-path](bp-path.md)). So S is the
identity and the refinement is Layer A.

The nontrivial simulator enters at three seams, all already visible as
arguments or constrained functions:

1. **Receipts and native articles carry signatures** (D01, D02, C1-11). Then
   F_node's ideal receipt says "issued by principal P, authorized", while R's
   receipt is bytes that verify under P's key. S must produce those bytes for
   honest P without P's cooperation: S runs the signer, which it may because
   in the ideal experiment S generates honest keys (Canetti 2004, the
   realization of F_SIG by any EUF-CMA scheme, and F_CERT by F_SIG with a
   registration functionality). The distinguishing event is a valid
   signature on a statement no honest party issued: a forgery. The bound is
   a reduction, outside ACL2. The entry points are `policy-authorizedp` in
   `fn-bp-prepare-receipt` (`books/bp-workflow.lisp:433`) and `authorized` in
   `fn-bpr-accept-request`; replacing the host boolean by a constrained
   `fn-crypto-verify` is P6.
2. **Content identity by digest.** `fn-frame-digest` (`books/frame.lisp:68`)
   is a constrained function with no injectivity axiom. If F_node compares
   content by bytes and R compares by digest, S must hide collisions; the
   distinguishing event is a collision and the bound is collision resistance.
   fn avoids the simulator here by design: OBJ-001 quarantines on collision,
   so F_node has the same branch as R, and the digest is a semantic event in
   both. That decision must be preserved when C1-13 moves identity derivation
   into ACL2.
3. **Confidentiality** (D04, later). Once articles are encrypted, F_node
   reveals lengths and the real view reveals ciphertexts; S simulates
   ciphertexts. Standard, and not in scope.

Legitimacy of the noncryptographic instance. F_node is defined in the
F_auth-hybrid model: both F_node and R are given the oracle as a subroutine
functionality. Canetti's composition theorem is stated for hybrid models,
and Canetti, Dodis, Pass and Walfish (2007) show it survives a *global*
oracle that Z can also query, which is what a shared authority table is.
The hybrid claim "R realizes F_node given F_auth" is therefore a complete UC
statement, and the crypto is a second, independent claim "some scheme
realizes F_auth", whose proof lives in the crypto literature (F_SIG,
F_CERT) or in a mechanized UC (EasyUC, Canetti, Stoughton and Varia 2019;
CryptHOL's constructive cryptography, Lochbihler, Sefidgar, Basin and Maurer
2019). The composition theorem glues them. In ACL2 terms: the encapsulate
`fn-assume-policy-authorizedp` is the hybrid functionality, its local
witness proves the constraints consistent, and the must-fail cases in
`tests/acl2/assumptions-tests.lisp:161-167` (`stored-bit-needs-evidence`,
`stored-bit-needs-terms`) are the proof that the constraint is not vacuous.
That is exactly the review's §6 remedy for "authority is a boolean that
becomes the constant `t` on disk": the boolean is an oracle answer, named,
and its realization is a separate obligation.

What "UC-like" buys over plain refinement: composability with F_dtn and with
other nodes (section 5.4) without re-proving the node; and a named place
for each cryptographic hypothesis when it arrives, instead of an A-CRYPTO
that covers everything.

### 2.4 Placement in the literature

Frameworks: Canetti, "Universally Composable Security: A New Paradigm for
Cryptographic Protocols" (FOCS 2001; revised ePrint 2000/067 through 2020).
Simplified UC: Canetti, Cohen and Lindell, "A Simpler Variant of Universally
Composable Security for Standard Multiparty Computation" (CRYPTO 2015).
GNUC: Hofheinz and Shoup, "GNUC: A New Universal Composability Framework"
(J. Cryptology 2015). IITM: Küsters, "Simulation-Based Security with
Inexhaustible Interactive Turing Machines" (CSFW 2006); Küsters, Tuengerthal
and Rausch, "The IITM Model" (J. Cryptology 2020); iUC: Camenisch, Krenn,
Küsters and Rausch (ASIACRYPT 2019). Constructive cryptography: Maurer,
"Constructive Cryptography: A New Paradigm for Security Definitions and
Proofs" (TOSCA 2011); Maurer and Renner, "Abstract Cryptography" (ICS 2011).
Reactive simulatability: Backes, Pfitzmann and Waidner (Information and
Computation 2007). Signatures as functionalities: Canetti, "Universally
Composable Signature, Certification, and Authentication" (CSFW 2004). Global
setup: Canetti, Dodis, Pass and Walfish (TCC 2007).

Which framework fn's F_node fits: IITM's and iUC's *responsive* environments
and their treatment of a machine that is run by the environment through
ports match a server whose every input is adversarial; GNUC's explicit
"structured systems" with a static call graph match the fact that fn's
subsystem machines are projections with a fixed wiring; constructive
cryptography's resource/converter view is the cleanest statement of
"F_node × F_dtn constructs the end-to-end obligation resource". The proof
obligations are identical across them for a deterministic, secrecy-free
system; the choice matters only when the signature layer arrives, and iUC's
handling of corruption per instance is then the natural fit for hostile
peers.

Refinement traditions the ACL2 side follows: Abadi and Lamport, "The
Existence of Refinement Mappings" (TCS 1991) and Lynch and Vaandrager,
"Forward and Backward Simulations, Part I" (Information and Computation
1995) for ρ as a forward simulation; Manolios, Namjoshi and Sumners,
"Linking Theorem Proving and Model-Checking with Well-Founded Bisimulation"
(CAV 1999) and Manolios's thesis (2001) for stuttering refinement in ACL2,
which is what `fn-wire-drive` versus per-byte `fn-wire-feed-byte` is; Bevier,
Hunt, Moore and Young, "An Approach to Systems Verification" (JAR 1989) for
the stacked-interpreter shape. seL4: Klein et al. (SOSP 2009) for the
abstract-to-executable-to-C refinement stack, Cock, Klein and Sewell (TPHOLs
2008) for the state-monad refinement calculus, Sewell, Winwood, Gammie,
Murray, Andronick and Klein, "seL4 Enforces Integrity" (ITP 2011) for
integrity as a property proved on the abstract model and transported down,
and Murray et al. (S&P 2013) for information flow, which is the profile fn
reaches only with D04. CompCert: Leroy (POPL 2006, JAR 2009) for forward
simulation diagrams with an external event trace, which is the exact shape
of section 2.2 when the trace is the port events; Ševčík et al.,
"CompCertTSO" (POPL 2011) for the same with a nondeterministic environment.

The novelty of fn's setting relative to seL4 and CompCert is only that the
"program" being refined is an ideal functionality with an adversarial
environment on every port; relative to UC it is only that the simulator is
the identity. Both simplifications are consequences of the design rule
"one owner per decision, and it is ACL2".

## 3. The server-robustness theorem

"Clients cannot crash us regardless of what they send" is five theorems
about `fn-ideal-serve`. All five quantify over every state satisfying the
carried invariant and over every event without hypothesis: every octet
list, every partition, every host observation sequence.

### 3.1 Totality: no guard violation on the served path

ACL2 admits only total functions, so `(fn-ideal-serve s e)` has a value for
every `s` and `e`. The executable claim is stronger: with guard `t`
verified, raw Common Lisp evaluation on any arguments computes that value
without a guard violation (the ACL2 guard theorem). The theorem is over the
world, stated as an `assert-event` in the guard-audit book, in the style of
`tests/acl2/store-node-guards-tests.lisp:6`:

```lisp
;; tests/acl2/ideal-node-guards-tests.lisp (P2)
(assert-event (equal (symbol-class 'fn-ideal-serve (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-ideal-serve nil (w state)) *t*))

;; The closure: every function reachable from fn-ideal-serve through
;; unnormalized bodies is :common-lisp-compliant. fn-guard-closure-compliantp
;; is a :program-mode walker over (w state) using all-fnnames; it is itself
;; evidence-tooling, not a theorem subject.
(assert-event (fn-guard-closure-compliantp '(fn-ideal-serve) (w state)))
```

And the ledger mirror, so `make check` fails when the closure regresses:
`tools/ledger.py --check` gains the rule that every function in the
source-level call graph of `fn-ideal-serve` has guard status `verified`
(not `default-guarded`). The six functions in `books/nntp.lisp` the ledger
lists as default-guarded are either verified or shown unreachable from
`fn-nntp-step` by this rule.

The logical half, with no hypothesis on the event:

```lisp
(defthm fn-ideal-serve-is-total-and-typed
  (and (implies (fn-ideal-statep s) (fn-ideal-statep (mv-nth 0 (fn-ideal-serve s e))))
       (fn-ideal-effect-listp (mv-nth 1 (fn-ideal-serve s e)))))
```

Its proof for the `:octets` case is `fn-wire-drive-preserves-statep`
(`books/wire-invariants.lisp:544`), `fn-nntp-step-preserves-consistent-session`
(`books/nntp-invariants.lisp:786`) lifted through `fn-ideal-nntp-run` by
`fn-nntp-finite-trace-preserves-consistent-session` (`:817`), and
`fn-nntp-step-effects-well-formed` (`books/nntp-effects.lisp:836`); for
`:store`, `fn-snt-step-preserves-relation` (`books/store-node-traces.lisp:406`)
and the resolution-trace sibling; for the sender, `fn-bp-step-preserves-state`
(`books/bp-workflow-invariants.lisp:668`) and `fn-relay-sender-step-preserves-invp`
(`books/relay-invariants.lisp:486`); for `:bundle`,
`fn-relay-accept-preserves-invp` (`:539`) and the receiver family.

### 3.2 Work per step is bounded by configuration and input length

Following `books/article-work-budget.lisp` and
`books/transfer-public-bound.lisp`: an instrumented twin that returns the
same value and a natural, proved equal to the step, and a closed-form bound.

```lisp
(defun fn-ideal-serve-cost (s e) ...)          ; counts fn-wire-feed-byte steps, fn-nntp-step
                                               ; work (fn-aw-*/fn-wm-* budgets), store step work
(defthm fn-ideal-serve-cost-is-the-step
  (equal (mv-nth 0 (fn-ideal-serve-with-cost s e)) (fn-ideal-serve s e)))

(defun fn-ideal-cost-bound (config n)          ; n = (fn-ideal-event-len e)
  (* *fn-ideal-cost-k*
     (+ 1 n
        (fn-ideal-config-line-limit config)
        (fn-ideal-config-body-limit config)
        (len (fn-ideal-config-groups config))
        (fn-ideal-config-capacity config))))

(defthm fn-ideal-serve-cost-is-bounded
  (implies (fn-ideal-statep s)
           (<= (fn-ideal-serve-cost s e)
               (fn-ideal-cost-bound (fn-ideal-config s) (fn-ideal-event-len e)))))
```

Exponent 1 in the input length, exponent 1 in each configuration term (the
worst NNTP command, `LISTGROUP` over a range or `LIST ACTIVE`, is linear in
articles or groups; `fn-wire-drive` is linear in octets by
`fn-wire-next-strictly-consumes`; wildmat is bounded by
`books/wildmat-work.lisp`). When proved, the sentence that reports it
quotes `*fn-ideal-cost-k*` and its distance from a measured chunk cost in the
same sentence (assurance rule "Quote the pessimistic number").

### 3.3 Retained memory is bounded by configuration

```lisp
(defun fn-ideal-size (s) ...)                  ; acl2-count of the retained state minus the history bytes
(defun fn-ideal-size-bound (config)
  (+ (* (fn-ideal-config-max-conns config)
        (+ (fn-ideal-config-line-limit config) (fn-ideal-config-body-limit config) *fn-ideal-session-size*))
     (* *fn-ideal-per-charge-size* (fn-ideal-config-capacity config))
     *fn-ideal-fixed-size*))

(defthm fn-ideal-reachable-size-is-bounded
  (implies (fn-ideal-statep s)
           (<= (fn-ideal-size s) (fn-ideal-size-bound (fn-ideal-config s)))))
```

The invariant carries every term: `(<= (len conns) max-conns)`; per
connection `fn-wire-feed-byte-retained-input-is-bounded`
(`books/wire.lisp:441`) and `fn-wire-statep`'s two `<=` clauses; sessions are
four fields; for the store `fn-retain-accounting-within-capacity`
(`books/retention.lisp:317`) bounds the sum of charges, and
`fn-node-articles-have-archive-bindingsp` ties every article to a pin, so
articles are bounded by capacity **provided every charge is positive**.
`fn-retain-obligationp` admits `natp` charges today; P3 makes the charge
`posp` or the theorem is false. Works are bound to articles
(`fn-bp-works-boundp`, `fn-bp-find-work-by-msgid`), receiver contexts are
grounded in history records (`fn-bprv-contexts-groundedp`), and history
records are bounded by capacity through their pins. Receipts and
undertakings need the same one-per-work argument, which is P3's open item.
Per-principal accounting (C1-08) refines the bound; it does not create it.

### 3.4 The only failures are the typed refusals

```lisp
(defthm fn-ideal-every-effect-is-typed
  (implies (member-equal eff (mv-nth 1 (fn-ideal-serve s e)))
           (fn-ideal-effectp eff)))                       ; no hypotheses on s or e

(defun fn-ideal-outcome (s e)                              ; :accepted, :refused or :uncertain
  (fn-ideal-outcome-of-effects (mv-nth 1 (fn-ideal-serve s e))))

(defthm fn-ideal-outcomes-are-three
  (member-equal (fn-ideal-outcome s e) '(:accepted :refused :uncertain)))

(defthm fn-ideal-refusal-changes-no-committed-history
  (implies (and (fn-ideal-statep s) (equal (fn-ideal-outcome s e) :refused))
           (equal (fn-ideal-history (mv-nth 0 (fn-ideal-serve s e)))
                  (fn-ideal-history s))))

(defthm fn-ideal-uncertain-iff-fenced
  (implies (fn-ideal-statep s)
           (iff (equal (fn-ideal-outcome s e) :uncertain)
                (equal (fn-state-fenced (fn-ideal-archive (mv-nth 0 (fn-ideal-serve s e)))) t))))
```

The third is the assurance rule "three outcomes stay distinct all the way
out" as a theorem; the CLI exit-code table in [host](host.md#cli-exit-codes)
is its image.

### 3.5 The semantic theorem: the reply stream is F_node's

For one connection, any octet stream, any partition into reads:

```lisp
(defun fn-ideal-octet-events (id chunks)                   ; (:octets id c1) (:octets id c2) ...
  (if (consp chunks) (cons (list :octets id (car chunks)) (fn-ideal-octet-events id (cdr chunks))) nil))

(defthm fn-ideal-reply-stream-is-partition-independent
  (implies (and (fn-ideal-statep s)
                (fn-ideal-find-conn id (fn-ideal-conns s))
                (fn-wire-octet-list-listp chunks))
           (equal (fn-ideal-replies id (mv-nth 1 (fn-ideal-run s (fn-ideal-octet-events id chunks))))
                  (fn-ideal-replies id (mv-nth 1 (fn-ideal-serve s (list :octets id (fn-ideal-append-all chunks))))))))
```

Proof: induction on `chunks` with `fn-wire-drive-partition-independence`
(`books/wire-invariants.lisp:561`) for the wire half and the associativity of
`fn-ideal-nntp-run` over `append`ed event lists (a lemma of the same shape as
`fn-wire-feed-proper-append`, `books/wire.lisp:685`).

The reply stream is then, by the definition of `fn-ideal-octets-step`,
`(fn-ideal-nntp-run session archive (fn-wire-result-events (fn-wire-drive wire octets)))`:
`fn-nntp-step` on each framed command against the pinned archive. That
unfolding is a definition and is named `-unfolds`; it is cited nowhere. The
content of "this is the RFC semantics" is the audit
[nntp-audit](nntp-audit.md) plus the cursor and selection theorems already
certified: `fn-nntp-group-selects-the-first-available-article`
(`books/nntp-invariants.lisp:327`), `fn-nntp-group-on-empty-group-invalidates-the-cursor`
(`:350`), `fn-nntp-next-or-last-moves-only-to-an-available-article` (`:685`),
`fn-nntp-archive-free-step-ignores-the-archive` (`:312`), the wildmat
rightmost-wins theorem against RFC 3977 §4.2, and the effect typing
`fn-nntp-replyp-of-block` (`books/nntp-effects.lisp:440`) with the 512-octet
initial line (`*fn-nntp-max-response-octets*`).

### 3.6 Connection isolation under interleaving

The owner serializes; F_node must say that serialization is invisible to a
connection whose pin is not advanced:

```lisp
(defthm fn-ideal-connection-isolation
  (implies (and (fn-ideal-statep s)
                (fn-ideal-find-conn id (fn-ideal-conns s))
                (fn-ideal-event-listp mine) (fn-ideal-events-on-connection-p id mine)
                (fn-ideal-event-listp others) (fn-ideal-events-avoid-connection-p id others))
           (equal (fn-ideal-replies id (mv-nth 1 (fn-ideal-run s (fn-ideal-interleave mine others schedule))))
                  (fn-ideal-replies id (mv-nth 1 (fn-ideal-run s mine))))))
```

Its lemmas are the owner keystones `fn-own-read-is-served-step-on-pinned-prefix-after-any-trace`,
`fn-own-reader-sees-pinned-prefix-replay-after-any-trace` and
`fn-own-pinned-prefix-survives-any-trace` (`books/owner-invariants.lisp`,
landed with w2 and carried over the served POST events by w5): the session
is a function of the pinned prefix, and the prefix only grows. For POST the
owner adds `fn-own-read-touches-only-its-connection` and
`fn-own-outcome-touches-only-its-connection` (a read and an outcome change
one connection and answer one connection) and
`fn-own-durable-reply-names-a-durable-record` (a 240 rendered for a
connection names a completion consumed after its submission was taken,
hence a record in the durable history). Together with 3.5 this is the whole
"we implement the semantics" claim for readers: the reply stream of a
connection is a function of its own octets and the version it pinned, and of
nothing else. Open: the interleaving theorem itself over `fn-ideal-run`
(M7), and that the completion a 240 names is the submission's own article
rather than a control-channel post consumed in the same window (the host
serializes; the book records only the ledger mark).

## 4. Strawman audit

The shape "a fabricated bad thing fails in the expected way" appears in four
forms. The verdicts use the review's distinction: a theorem is a tooth when
it shows a *hypothesis* of a keystone is necessary; it proves nothing about
the system when it restates a branch of a definition or knocks down a
witness that fails only the shape half of a recognizer.

### 4.1 Branch-of-definition refusal theorems (prove nothing about the system)

Already flagged by the detector and excluded from the registry:
`fn-node-capacity-refusal-is-no-op`, `fn-node-stale-completion-is-no-op`
(`books/node.lisp:367,390`), `fn-retain-admission-refusal-is-no-op`,
`fn-retain-wrong-evidence-does-not-release` (`books/retention.lisp:322,359`),
`fn-sn-finish-disabled-is-no-op`, `fn-sn-known-abort-disabled-is-no-op`,
`fn-sn-refuse-reservation-disabled-is-no-op`, `fn-exchange-ingest-refusal-is-no-op`,
`fn-wire-feed-closed-noop`, `fn-sn-open-observed-invalid-history-refuses`,
`fn-frame-decode-refuses-oversize-before-validation`,
`fn-bpc-decode-refuses-overlong-input`, `fn-bpf-out-of-bounds-input-allocates-nothing`,
`fn-bpf-cell-of-uncovered-is-gap`, `fn-nntp-block-scan-start-without-a-dot`,
`fn-bp-effect-for-pending-attempt-unfolds`, and the four
`fn-node-step-*-reduction` lemmas.

The same shape with a recognizer hypothesis added, which the detector does
not catch: `fn-fenced-prepare-is-no-op`, `fn-duplicate-accepted-prepare-is-no-op`,
`fn-unknown-or-duplicate-group-prepare-is-no-op`, `fn-stale-completion-is-no-op`,
`fn-fenced-completion-is-no-op` (`books/acceptance.lisp:745-789`);
`fn-bp-stale-transport-is-no-op`, `fn-bp-unchecked-receipt-is-no-op`,
`fn-bp-fenced-complete-is-no-op` (`books/bp-workflow-transport-invariants.lisp:237-254`);
`fn-exchange-invalid-batch-refuses-atomically`,
`fn-exchange-unknown-schema-batch-refuses-atomically`,
`fn-exchange-unauthorized-batch-refuses-atomically`
(`books/exchange-invariants.lisp:149-165`; "atomically" names a property the
definition cannot violate); `fn-clock-no-wall-and-no-age-is-uncertain`,
`fn-clock-zero-creation-time-without-age-is-uncertain`
(`books/clock-invariants.lisp:42,48`); `fn-node-malformed-step-is-no-op`
(`books/node-traces.lisp:150`); `fn-snt-unknown-io-is-no-op`
(`books/store-node-traces.lisp:371`); `fn-bprl-no-receipt-no-release-no-peer-reliance`
(`books/bp-release-invariants.lisp:865`); `fn-nntp-closed-step-has-no-effects`
(`books/nntp-effects.lisp:849`); `fn-wire-next-closed-noop`,
`fn-wire-begin-article-refusal-keeps-state` (`books/wire.lisp:676,292`).

Verdict: legitimate as rewrite lemmas (several are load-bearing in hints);
not evidence. The relay pair `fn-relay-forwarding-without-undertaking-is-refused-by-definition`
and `fn-relay-archived-receipt-needs-no-undertaking-by-definition` are the
model of honest naming. Recommendation (P7): rename every theorem above
with `-by-definition`; extend the detector with a
`branch-of-definition-plus-recognizer` rule so the second list is flagged;
remove all of them from `planning/proof-events.json` where cited. The system
property each of them gestures at is the *positive* keystone next to it
(for example `fn-prepare-allocates-fresh-monotone-txid`,
`books/acceptance.lisp:857`, whose hypotheses are exactly the refusing
branches), and that is what the registry cites.

### 4.2 Teeth whose witness fails only the shape clause (prove nothing)

`must-fail` cases that drop a recognizer hypothesis and supply a witness
that is not even the right shape (the core cluster's three are now concrete
`assert-event` witnesses, 2026-09-19, and the finding still applies to what
they separate): the `*acc-teeth-forged*` install witness
(`tests/acl2/acceptance-tests.lisp`), the `*node-teeth-forged*` install
witness (`tests/acl2/node-tests.lisp`), the `*ret-teeth-forged*` release
witness (`tests/acl2/retention-tests.lisp`),
`sft-teeth-crash-prefix-without-statep` (`store-files-teeth-tests.lisp:147`),
`snt-teeth-composed-crash-is-kernel-crash-without-statep`,
`snt-teeth-acknowledged-record-survives-without-the-relation`
(`store-node-teeth-tests.lisp:194,291`), `bpre-teeth-committed-without-relation`,
`bpre-teeth-live-extension-without-relation` (`*bpre-untyped-store*`,
`bp-receiver-evolving-tests.lisp:231,337`), `nnt-teeth-step-without-a-consistent-session`
(`*nnt-forged-session*`, `nntp-teeth-tests.lisp:90`).

Verdict: each is a tooth only if its witness satisfies the shape clauses of
the dropped recognizer and fails a semantic clause. A witness named
"untyped" or "forged" that fails `true-listp` shows only that the recognizer
has a shape clause. Recommendation (P7): beside every such witness, an
`assert-event` of the shape recognizer (`fn-sf-phase-shapep` exists; define
`fn-state-shapep`, `fn-node-shapep`, `fn-sn-shapep`, `fn-nntp-session-shapep`
as the pure shape halves), so the ledger can check that the witness is
well-shaped; retire any witness that cannot be made so. The witnesses that
already pass this rule are the model: `nnt-teeth-step-without-a-valid-cursor`
(`*nnt-stale-cursor*`, a well-formed session whose cursor names an absent
article) and `snt-teeth-installs-record-without-binding`.

### 4.3 Reachability witnesses miscounted as teeth (keep, relabel)

`bpw-teeth-trace-does-not-preserve-the-state` (`bp-workflow-teeth-tests.lisp:74`),
`snt-teeth-finish-is-a-no-op-without-being-disabled`,
`snt-teeth-acknowledges-exact-pair-without-enablement`
(`store-node-teeth-tests.lisp:146,155`), `sft-teeth-completing-gate-without-the-completing-phase`,
`sft-teeth-core-completion-without-pair-mismatch`,
`sft-teeth-emit-success-without-mismatch` (`store-files-teeth-tests.lisp:97-123`).
Each shows a no-op theorem's branch is reachable; that is the "reachable
non-degenerate witness" obligation, not a tooth for a hypothesis. Keep,
mark `witness`, do not count under teeth.

### 4.4 Legitimate teeth (keep, cite)

Everything else in the must-fail listing drops a semantic hypothesis
against a well-shaped witness: the acceptance watermark pair
(`acceptance-teeth-tests.lisp:138,157,197`), the article-source pair, the
four codec round-trip families (`cbor-teeth`, `records-teeth`,
`bp-primary-tests:323-382`, `bp-fragment-tests:180,202`), the ten clock cases
(`clock-tests.lisp:134-236`, each dropping one named hypothesis of
`fn-clock-expired-requires-every-admissible-clock-to-agree` and its
siblings), the exchange triple, `ret-teeth-records-evidence-without-match`,
`ret-teeth-independent-pin-without-distinctness`, `ret-teeth-not-reused-without-known-id`,
the store-files window cases (phase dropped, choice dropped), the store-node
membership and admissible-image cases, the evolving-store prefix, idle-phase,
membership, probe and extension cases, the release and relay quartets, the
frame digest-shape and input-shape cases, `wm-teeth-rightmost-without-pattern-listp`,
and `tests/acl2/nntp-tests.lisp:342,356,403,438` (archive-freeness needs its
hypothesis; consistency and effect typing need theirs; `GROUP` on an unknown
group does not move the cursor). The `assumptions-tests.lisp` cases are a
different and correct kind of tooth: they show each encapsulate's constraints
reject a bad witness, which is what makes A-* a hypothesis rather than a
comment.

### 4.5 Unreachable branches

`fn-nntp-step`'s reply of `501 syntax error` to a non-`:command` wire event
(`books/nntp.lisp:1368`) is unreachable today, because the reader never
enters `:article` mode, and wrong once POST lands, because an `:article`
event is then a body, not a syntax error. Mark `unreachable-in-composition`
now and route the event in C1-06. `fn-snt-unknown-io-is-no-op` and
`fn-node-malformed-step-is-no-op` are reachable only from a host that
violates A-HOST; keep them, since F_node must be total on those inputs
(section 3.1), but they are robustness lemmas, not semantics.

## 5. The chaining plan

### 5.1 Existing theorems that are lemmas of the refinement

| Refinement obligation | Lemma (book:line) |
| --- | --- |
| Wire: chunking is invisible | `fn-wire-drive-partition-independence` (`books/wire-invariants.lisp:561`); `fn-wire-drive-is-feed-proper` (`:512`); `fn-wire-feed-proper-append` (`books/wire.lisp:685`) |
| Wire: progress and bounds | `fn-wire-next-strictly-consumes` (`books/wire-invariants.lisp:292`); `fn-wire-next-unconsumed-is-suffix` (`:160`); `fn-wire-feed-byte-retained-input-is-bounded` (`books/wire.lisp:441`); `fn-wire-drive-preserves-statep` (`books/wire-invariants.lisp:544`) |
| NNTP: invariant and typing | `fn-nntp-step-preserves-consistent-session` (`books/nntp-invariants.lisp:786`); `fn-nntp-finite-trace-preserves-consistent-session` (`:817`); `fn-nntp-opened-finite-trace-is-consistent` (`:834`); `fn-nntp-step-effects-well-formed` (`books/nntp-effects.lisp:836`); `fn-nntp-replyp-of-block` (`:440`) |
| NNTP: semantics | `fn-nntp-group-selects-the-first-available-article` (`:327`); `fn-nntp-next-or-last-moves-only-to-an-available-article` (`:685`); `fn-nntp-archive-free-step-ignores-the-archive` (`:312`); `fn-nntp-step-preserves-carried-projection` (`:294`) |
| Store: live history relation | `fn-snt-step-preserves-relation` (`books/store-node-traces.lisp:406`); `fn-snt-mixed-trace-preserves-live-history-relation` (`:412`); `fn-snt-ready-or-recovered-node-is-exact-replay` (`:423`); `fn-snt-acknowledged-history-retained-through-mixed-trace` (`:484`); `fn-snt-admissible-crash-image-is-recoverable` (`:600`); the `fn-sn-open-observed` success relation in `books/store-observed-traces.lisp` |
| Store: acknowledgement | `fn-sn-new-success-requires-actual-matching-durable-node-completion`, `fn-sn-actual-durable-completion-installs-record` (`books/store-node-invariants.lisp`) |
| Node/acceptance | `fn-node-step-preserves-state` (`books/node-traces.lisp:246`); `fn-node-install-stage-preserves-state` (`books/node-invariants.lisp:70`); `fn-install-preserves-state`, `fn-watermark-does-not-conflict`, `fn-allocate-at-watermark` (`books/acceptance-invariants.lisp:188,172,65`); `fn-prepare-allocates-fresh-monotone-txid` (`books/acceptance.lisp:857`) |
| Retention | `fn-retain-accounting-within-capacity` (`books/retention.lisp:317`); `fn-retain-known-obligation-id-is-not-reused` (`:351`); `fn-retain-release-preserves-independent-pin` (`books/retention-invariants.lisp:92`) |
| Sender | `fn-bp-step-preserves-state` (`books/bp-workflow-invariants.lisp:668`); `fn-bp-trace-preserves-node` (`:787`); `fn-bp-step-submit-requires-matching-durable-attempt-completion` (`:911`); `fn-bp-transport-trace-preserves-receipt` (`books/bp-workflow-transport-invariants.lisp:205`); `fn-bp-observe-transport-never-moves-status-backward` (`:325`) |
| Release | `fn-bprl-release-removes-the-forward-pin`, `-preserves-independent-pin`, `-preserves-archive-pin` (`books/bp-release-invariants.lisp:457,537,561`); `fn-bprl-authorized-receipt-evidence-matches-required` (`:372`); `fn-bprl-undertake-pins-the-forwarding-obligation` (`:831`) |
| Receiver | `fn-bprv-replayed-receipt-is-grounded` (`books/bp-receiver-retention-invariants.lisp:359`); `fn-bprv-evolving-output-is-history-grounded` (`books/bp-receiver-evolving-history-invariants.lisp:559`); `fn-bprv-evolving-output-is-node-grounded-when-idle` (`books/bp-receiver-evolving-node-invariants.lisp:611`); `fn-bpr-live-state-is-replay-of-journal`, `fn-bpr-live-receipt-regenerated-after-restart`, `fn-bprv-evolving-invariant-survives-observed-reopen` (`books/bp-receiver-evolving-store-invariants.lisp:548,620,421`) |
| Relay | `fn-relay-forwarding-receipt-has-durable-onward-obligation`, `fn-relay-crash-recover-never-yields-a-promise-alone` (`books/relay-crash-invariants.lisp:103,156`); `fn-relay-accept-preserves-invp`, `fn-relay-sender-step-preserves-invp` (`books/relay-invariants.lisp:539,486`) |
| Time and identity | `fn-clock-expired-requires-every-admissible-clock-to-agree`, `fn-clock-expired-and-live-cannot-both-be-sound` (`books/clock-invariants.lisp:61,97`); `fn-bpp-decode-of-encode`, `fn-bpp-encode-is-injective` (`books/bp-primary-invariants.lisp:217,288`) |
| Facts | `fn-exchange-merge-idempotent`, `fn-exchange-merge-commutative-member` (`books/exchange.lisp:256,265`); `fn-exchange-admitted-ingest-retains-conflicting-evidence` (`books/exchange-invariants.lisp:131`) |
| Assumptions | the seven encapsulates in `books/assumptions.lisp:58-275`; `fn-frame-digest` (`books/frame.lisp:68`) |

### 5.2 Missing, in proof order

1. **M1 F_node book** (P0): `fn-ideal-*` state, step, `fn-ideal-statep`,
   initial state, preservation, the projection theorems of 1.3 and the
   witness trace. Cheap; the content is choosing fields so projections are
   accessors. Depends on nothing; the relay state exists.
2. **M2 the served path in logic mode** (P1): `fn-reader-drive` and
   `fn-reader-drive-is-ideal-octets-step`; `fn-reader-chunk` becomes a call
   to it. Closes the wire `pending_subject`. Depends on M1.
3. **M3 guard closure** (P2): `fn-guard-closure-compliantp`, the
   `assert-event`s of 3.1, the `ledger.py --check` rule, and resolving the
   six default-guarded `fn-nntp-*` functions. Depends on M1.
4. **M4 partition independence lifted** (P1): `fn-ideal-reply-stream-is-partition-independent`
   and the `append` lemma for `fn-ideal-nntp-run`. Depends on M2.
5. **M5 typed refusals** (P4): `*fn-ideal-refusals*`, the three theorems of
   3.4. Depends on M1.
6. **M6 cost and size** (P3): the instrumented twin, `fn-ideal-cost-bound`,
   `fn-ideal-size-bound`, `posp` charges, the one-per-work bounds for
   receipts and undertakings. Depends on M1; the wildmat and article budgets
   exist.
7. **M7 isolation** (P1): `fn-ideal-connection-isolation` from the owner
   keystones. Depends on M1; `w2/mutable-owner` and `w5/owner-post` have
   landed the owner keystones it lifts.
8. **M8 A-HOST and A-DURABILITY applied** (P5): `fn-ideal-run` stated with
   `fn-assume-host-events` on the event list; `:reopen` with
   `fn-sf-crash-imagep`; the first theorems in the tree that take an
   encapsulate as a hypothesis. Depends on M1.
9. **M9 F_dtn and the composed system** (P5): section 5.4. Depends on M1, M8.
10. **M10 the crypto seam** (P6, with C1-11): `fn-crypto-verify` encapsulate
    replacing the host boolean; the functional-instance theorem that
    F_node under the oracle equals F_node under `fn-crypto-verify` whenever
    the two agree on the reachable set; the written simulator argument for
    the disagreement event. Depends on M9 and the substrate lane.

### 5.3 What each step retires

M2 retires `pending_subject` on the wire row. M3 retires the review's
"97-function guard gap" as a *served-path* concern (functions off the path
stay honestly unverified). M5 retires D13. M6 quotes the pessimistic numbers
D3 asked for. M8 is C1-15's "no theorem takes an assumption as hypothesis".
M9 is the first multi-node theorem (refinement ladder rung 5). M10 is the
first place A-CRYPTO is a hypothesis of anything.

### 5.4 Composition with the BP layer: F_dtn and F_node × F_dtn

F_dtn is an unauthenticated, adversarially scheduled channel. It never
delivers what was not sent or injected; the adversary chooses delay by
withholding, reorder by choosing which in-flight bundle to deliver,
duplication by delivering again, and loss by dropping. Injection is the
hostile peer: a bundle that no honest node sent.

```lisp
;; books/dtn-channel.lisp (P5)
(defun fn-dtn-make-bundle (id src dst octets) (list id src dst octets))
(defun fn-dtn-statep (d) (fn-dtn-bundle-listp d))          ; the in-flight multiset

(defun fn-dtn-step (d e)
  (case (car e)
    (:send    (cons (fn-dtn-make-bundle (fn-bpp-bundle-id-of (cadddr e)) (cadr e) (caddr e) (cadddr e)) d))
    (:inject  (cons (fn-dtn-make-bundle :injected (cadr e) (caddr e) (cadddr e)) d))
    (:deliver d)                                            ; a copy is delivered; the bundle stays in flight
    (:drop    (fn-dtn-remove (cadr e) d))
    (otherwise d)))

(defun fn-dtn-deliverable (d id) (fn-dtn-find id d))        ; nil unless in flight: no fabrication
```

Expiry is decided by the receiving node from its own clock
(`fn-clock-expiry-decision`, `books/clock.lisp:170`) on the bundle's
creation time and lifetime (`fn-bpp-creation-time`, `fn-bpp-lifetime`,
`books/bp-primary.lisp:396,398`); F_dtn may also drop an expired bundle.
The channel has no clock of its own, which is FLR-004's "safety must not
require a synchronized global clock" made structural.

The composed system is a finite map from endpoint id to F_node states plus
one F_dtn:

```lisp
(defun fn-sys-step (sys e)
  (case (car e)
    (:node    ;; (:node eid ev): step that node; route its :submit effects into the channel
     (let* ((r (fn-ideal-step (fn-sys-node (cadr e) sys) (caddr e))))
       (fn-sys-with-channel (fn-sys-with-node sys (cadr e) (mv-nth 0 r))
                            (fn-dtn-sends (cadr e) (mv-nth 1 r) (fn-sys-channel sys)))))
    (:deliver ;; (:deliver id): the adversary picks an in-flight bundle; its destination receives it
     (let ((b (fn-dtn-find (cadr e) (fn-sys-channel sys))))
       (if (not b) sys
         (fn-sys-with-node sys (fn-dtn-bundle-dst b)
                           (mv-nth 0 (fn-ideal-step (fn-sys-node (fn-dtn-bundle-dst b) sys)
                                                    (list :bundle (fn-dtn-bundle-src b) (fn-dtn-bundle-octets b))))))))
    ((:drop :inject) (fn-sys-with-channel sys (fn-dtn-step (fn-sys-channel sys) e)))
    (otherwise sys)))

(defun fn-sys-invariantp (sys)
  (and (fn-sys-nodes-are-statesp (fn-sys-nodes sys))
       (fn-dtn-statep (fn-sys-channel sys))))

(defthm fn-sys-step-preserves-invariant
  (implies (fn-sys-invariantp sys) (fn-sys-invariantp (fn-sys-step sys e))))   ; any e, any schedule
```

The authority oracle, instantiated for the composed system, is the ideal
one: a receipt is authorized iff its issuer is a node of the system and the
grounding record is in that node's committed history. This is where an
ideal functionality is stronger than any real one, and it is exactly what
signatures under A-PEER approximate.

```lisp
(defun fn-sys-ideal-authorizedp (sys receipt)
  (let ((issuer (fn-sys-node (fn-bp-receipt-issuer receipt) sys)))
    (and issuer
         (fn-bpi-node-record-committedp (fn-ideal-node issuer)
                                        (fn-sys-grounding-record issuer receipt)))))
```

The end-to-end theorem: an obligation is released only against a receipt
grounded in a durable record at a node of the system, under every schedule
of delay, reorder, duplication, loss and injection.

```lisp
(defthm fn-sys-release-is-grounded-end-to-end
  (implies (and (fn-sys-invariantp sys)
                (fn-sys-obligation-pinned-p sys a work-id)                   ; pinned at a before the run
                (not (fn-sys-obligation-pinned-p (fn-sys-run sys es) a work-id))) ; released after it
           (let* ((final   (fn-sys-run sys es))
                  (work    (fn-bp-find-work work-id (fn-bp-state-works (fn-sys-sender a final))))
                  (receipt (fn-bp-work-receipt work)))
             (and (fn-bp-authorized-receiptp (fn-sys-bp-config a final) work receipt)
                  (fn-sys-ideal-authorizedp final receipt)
                  (fn-retain-find-id (fn-bp-work-archive-id work) (fn-ideal-pins (fn-sys-node a final)))))))
```

The three conjuncts are, respectively, `fn-bprl-authorized-receipt-evidence-matches-required`
lifted; `fn-bprv-replayed-receipt-is-grounded` and
`fn-bprv-evolving-output-is-node-grounded-when-idle` at the issuer, carried
through the channel by `fn-dtn-deliverable`'s no-fabrication; and
`fn-bprl-release-preserves-archive-pin`. No hypothesis mentions delivery, so
loss and delay are covered; the event list is arbitrary, so reorder is
covered; injection is covered because an injected receipt fails
`fn-sys-ideal-authorizedp`.

Duplicate delivery is idempotent on state and regenerates the receipt:

```lisp
(defthm fn-sys-duplicate-delivery-is-idempotent
  (implies (fn-sys-invariantp sys)
           (equal (fn-sys-run sys (list (list :deliver id) (list :deliver id)))
                  (fn-sys-run sys (list (list :deliver id))))))
```

from `fn-bpr-live-receipt-regenerated-after-restart` and the ingress
duplicate recognition (`fn-bpi-adu-durably-acceptedp`,
`books/bp-ingress.lisp:482`). Progress is not a theorem of this section:
PRF-018 needs `fn-assume-fairness-contact-index` (`books/assumptions.lisp:275`)
and a contact plan, and is stated separately, as [proofs](../docs/proofs.md)
requires.

## 6. Packets

Owners use the roles of [swarm-cycles](../planning/swarm-cycles.md): the
service integrator owns `books/nntp.lisp`, the wire dispatcher and
`tools/run_reader.py`; the storage integrator owns the store host; the
assurance-tooling lane owns `tools/ledger.py` and the test-book conventions;
the substrate lane owns the crypto seam. Tiers follow the C1 packet table.

| Order | Packet | Owner | Deliverable | Acceptance |
| --- | --- | --- | --- | --- |
| P0 | `books/ideal-node.lisp`, `ideal-node-invariants.lisp`, `tests/acl2/ideal-node-tests.lisp` | core lane, Opus implementation over this design | Section 1 as certified books; `fn-ideal-`, `fn-dtn-`, `fn-sys-` registered in `docs/prefixes.md` | Both books certify as Makefile roots; every projection theorem of 1.3 proved with `fn-ideal-statep` as sole hypothesis; the every-port witness trace runs under `fn-ideal-run` with `assert-event`s on each intermediate state; one `must-fail` per projection hypothesis with a well-shaped witness (4.2 rule); `ledger.py --check` green |
| P1 | served path in logic mode | service integrator, Opus | `fn-reader-drive`, `fn-reader-drive-is-ideal-octets-step`, `fn-ideal-reply-stream-is-partition-independent`; `fn-reader-chunk` calls the logic-mode function | The wire `pending_subject` note deleted and `ledger.py --check` still green; `tests/test_reader_partitions.py` and `tests/interop_nntplib.py` byte-identical before and after; `host/reader-host.lisp` no longer contains protocol logic outside the call |
| P2 | guard closure | assurance-tooling lane, Sonnet | `fn-guard-closure-compliantp`, `tests/acl2/ideal-node-guards-tests.lisp`, the `ledger.py` closure rule, the six `fn-nntp-*` resolutions | The guards book certifies; `ledger.py --check` fails on a synthetic regression (one callee set `:verify-guards nil`) and passes on the tree; the ledger row for `fn-ideal-serve` reads `verified` with closure size reported by the tool, not typed |
| P3 | cost and size | core lane, Opus | 3.2 and 3.3 with `posp` charges and the one-per-work bounds | Theorems certified; the report sentence quotes `*fn-ideal-cost-k*`, the exponent, and the measured chunk cost from `tests/evidence/` in one sentence; no change to any served-path definition |
| P4 | typed refusals | service integrator, Sonnet | `*fn-ideal-refusals*`, the theorems of 3.4, `unreachable-in-composition` marks of 4.5 | Every refusal reason in the enumeration is produced by a witness in the test book; `run_store.exit_code_for` and the reader map each `:refused`/`:uncertain` effect to the existing code table with a test per row |
| P5 | F_dtn, composition, assumptions applied | core lane, Fable design then Opus proofs | `books/dtn-channel.lisp`, `books/system.lisp`, 5.4's theorems, M8 | `fn-sys-release-is-grounded-end-to-end` and `fn-sys-duplicate-delivery-is-idempotent` certified; a two-node witness with a reorder, a duplicate, a drop and an injection; `fn-assume-host-events` and `fn-sf-crash-imagep` appear as hypotheses of cited theorems; `tests/bp-dtn7` scenario SCN-007/008 runs unchanged |
| P6 | crypto seam entry | substrate lane (C1-11), Fable | `fn-crypto-verify` encapsulate; the oracle/verify functional-instance theorem; the simulator argument as prose in this document's 2.3 with the reduction named | The host boolean is gone from `fn-bp-prepare-receipt` and `fn-bpr-accept-request` call sites; no `defaxiom`, no trust tag; the theorem that the two worlds agree on the reachable set certifies; the disagreement event is named `forgery` in the registry with status `deferred` until a scheme is selected (D09) |
| P7 | strawman retirements | assurance-tooling lane, Sonnet | 4.1 renames and detector rule; 4.2 shape recognizers and witness `assert-event`s; 4.3 relabels; registry edits | Detector flags every theorem in 4.1's second list; every 4.2 witness has a passing shape `assert-event` or is removed; `proof-events.json` cites none of 4.1; `make check` green |

P0 through P2 are sequential. P3, P4 and P7 run in parallel after P0. P5
needs P0 and, for isolation, `w2/mutable-owner`. P6 waits for the substrate
lane's profile.

## 7. References

Canetti 2001 (UC); Canetti, Cohen, Lindell 2015 (simplified UC); Hofheinz,
Shoup 2015 (GNUC); Küsters 2006 and Küsters, Tuengerthal, Rausch 2020
(IITM); Camenisch, Krenn, Küsters, Rausch 2019 (iUC); Maurer 2011 and
Maurer, Renner 2011 (constructive and abstract cryptography); Backes,
Pfitzmann, Waidner 2007 (reactive simulatability); Canetti 2004 (F_SIG,
F_CERT); Canetti, Dodis, Pass, Walfish 2007 (global setup); Canetti,
Stoughton, Varia 2019 (EasyUC); Lochbihler, Sefidgar, Basin, Maurer 2019
(CryptHOL constructive cryptography); Abadi, Lamport 1991; Lynch, Vaandrager
1995; Manolios, Namjoshi, Sumners 1999 and Manolios 2001 (well-founded
bisimulation in ACL2); Bevier, Hunt, Moore, Young 1989 (the CLI stack);
Klein et al. 2009, Cock, Klein, Sewell 2008, Sewell et al. 2011, Murray et
al. 2013 (seL4); Leroy 2006, 2009 and Ševčík et al. 2011 (CompCert forward
simulation with event traces).
