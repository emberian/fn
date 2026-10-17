# Applications on fn: what they can rely on

Status: the application boundary as of the apps lane, 2026-10-04. This page
says which contracts an application process can build on today, and which
it cannot yet. It does not add an interface. The detailed contracts are in
[consumer progress](consumer-progress.md) and the
[E1/E2 experiment](../planning/experiments/e1-e2-agent-exchange.md). The
reference application is `tools/fn_consumer.py`, a sleeping agent with its
own SQLite inbox, outbox and attempt journal.

**Evidence scope.** These are source contracts. The native runs that
exercised them were made on an initialized source process that was not dev
(the `ad8da41fc` world plus overlays, 2026-10-03; see `planning/now.md`). No
image built from the current source has run them yet. The six native
scenarios below are the check, and the LANEDUMP `apps` entry records the
image and run ids once they have run. Until then, read "can rely on" as
"specified, with source and an earlier native coordinate", not as
"qualified on this release".

## What an application can rely on today

1. **Signed exact-byte storage.** An author signs its exact source with the
   hybrid profile, Ed25519 and ML-DSA-65 together (`fn hybrid-sign`), and
   submits it with `fn hybrid-author` over the owner's control socket. The
   Store keeps the authored source byte for byte. Node-injected headers
   (Path, Xref, Injection-Date, Injection-Info) sit outside the authored
   projection. A consumer can check the source with
   `tools/fn_verify.py check-article` against its own keyring, without
   trusting the node's verdict. fn keeps no secrets: encrypt before signing
   if confidentiality matters.
2. **Idempotent resend (D25).** Resending byte-identical poster bytes under
   the same Message-ID gets "already stored here" (exit 0). Different bytes
   under the same Message-ID are a conflict. A lost reply is `uncertain`
   (exit 3), and fn never answers it with a guessed refusal. An application
   keeps the signed artifact and resends it unchanged. It never re-signs:
   ML-DSA signing is randomized, so a fresh signature makes a different
   carrier and therefore a conflict. A resend that current permission
   refuses (a revoked enrolment, for example) stays uncertain until the
   Store serves the artifact back through the cursor.
3. **The local consumer cursor.** The commands are `fn consumer` bootstrap,
   register, poll, wait, ack, position, status and unregister, plus the
   `bound-` forms that take an account password. They run over the owner's
   mode-0600 Unix control socket.
   - The cursor (`fncu` v1) names the Store history, incarnation, consumer,
     registration epoch, principal, query and query version, view version
     and scanned position. A cursor from another store, incarnation or epoch
     is refused before any ack.
   - Poll is a read. Ack declares only the consumer's own processing, is
     monotone and idempotent, and `position` settles an uncertain ack.
   - Wait is a poll that sleeps on the owner's commit signal rather than a
     timer. At most 12 waits run at once, and one more is refused as
     `waiters` rather than queued.
   - Withdrawals arrive as withdrawal events, never as the withdrawn
     content.
   - Delivery is at least once. The application owns deduplication by
     application operation ID, and the inbox, transition and outbox
     transaction that comes before the ack.
4. **Two nodes over NNTP peering.** Each agent talks only to its own node.
   The authored source and both signatures arrive unchanged at every hop;
   only the node's stored projection (Path) differs.
5. **A remote consumer**, once that scenario has run (see "Remote consumer"
   below).

The six native scenarios that check these are in
`tests/test_native_consumer_exchange.py` and `..._two_nodes.py`. Each needs
`FN_RUN_CONSUMER_EXCHANGE=1` and a source-matched developer image.

| scenario | selector |
|---|---|
| delivery, projection failure, owner restart | `NativeConsumerExchangeTests.test_saved_delivery_survives_projection_fault_and_owner_restart` |
| key-free immutable retry | `NativeConsumerExchangeTests.test_saved_submission_retries_after_restart_without_signing_keys` |
| revoked resend settled by Store observation | `NativeConsumerExchangeTests.test_death_after_acceptance_then_revocation_is_never_refused` |
| two-node cuts | `tests.test_native_consumer_exchange_two_nodes` |
| poll, wait and ack end to end | `NativeConsumerExchangeTests.test_sleeping_consumer_waits_for_the_report_then_acks` (`fn_consumer.py CONFIG wake --wait S`) |
| remote consumer across two nodes | `NativeTwoNodeConsumerExchangeTests.test_remote_consumer_reads_a_store_it_is_not_local_to` |

## Not yet

- **Views that change, and rebase.** The cursor names a history and a view,
  but the local profile fixes query version 1 and view version 0 over one
  registered group. There is no `rebase` command and no view-change
  workflow, and multi-group selection is not served. A consumer whose
  account loses access to a group is refused; it is not rebased.
- **Retention.** A cursor creates no retention pin. Reclaimed content shows
  up as an explicit unavailable gap, and nothing promises the content
  stays.
- **A non-NNTP inter-node protocol.** Between nodes there is only NNTP
  peering and BP carriage. Signed R/Q over the BP path (SCN-1125) is
  prepared but has not run on the current source.
- **Patterns.** Pub/sub maps onto groups plus the cursor, and req/rep onto
  an article plus a correlated reply. These are application conventions
  (the `fn-app: e1/2` envelope), not fn operations. Push/pull with
  competing consumers, and anything the 6.6.1 ZMQ-shaped surface would add,
  belong to the TARIFF/ZMQ design lane.

## Remote consumer (source, 2026-10-04; native evidence pending)

An application on another machine reads a node's Store as one of that
node's accounts (D48 / PKT-673: "authenticated remote access scoped to the
account; operator controls stay private"). The operator binds a consumer to
the account (`fn operator CONFIG consumer bind NAME --account LOGIN`). The
application then uses `fn consumer-remote OP HOST PORT TRUST LOGIN
SECRET-FILE ...` for `poll`, `wait`, `ack`, `position` and `status`, or
`fn_consumer.py` with a `remote` section. It posts through its own node, as
before.

- **The route.** `books/consumer-remote-bound.lisp` `fn-crbd-route` maps an
  FNCR request to the account's bound local operation (`bound-poll`,
  `bound-wait`, `bound-ack`, or `position`/`status` behind the same gate), or
  refuses it by name:
  - `operator-control` for register, rebase and unregister;
  - `credential` for a consumer not bound to the named login, or for a wrong
    password;
  - the bound gate's own `access` or `scope` reasons.

  Proved: `fn-crbd-operator-controls-stay-private`,
  `fn-crbd-route-is-the-accounts-bound-operation` (every non-refusal is the
  named account's bound operation, on the request's own consumer and
  password, with the gate passed) and `fn-crbd-another-login-is-refused`.
  `tests/acl2/consumer-remote-bound-tests.lisp` carries a satisfying witness
  and teeth.

  Delivery is not decided anew. A remote answer is one of the answers
  `fn-cbind-poll` / `fn-cbind-ack` give, so their keystones (only readable
  events, the consumer's own ack or a refusal) hold of it unchanged.
- **The cursor** is the node's `fncu` v1 cursor. It names that node's Store
  history, incarnation, consumer, registration epoch, principal, query and
  view. A cursor read remotely therefore names the remote Store's history,
  never the reader's own. An uncertain ack is settled with a remote
  `position`, as it is locally.
- **Funding (interim tariff, a projection).** The class has one private
  resource ledger. Each session draws the connection vector at accept,
  before the handshake or any read: resident octets covering the frame and
  reply bounds plus the session thread, one descriptor, one worker and one
  spent connection identity. It settles only at physical close (thread
  joined, socket closed); `fn-crf-open` and `fn-crf-close` are in
  `books/consumer-remote-operation-source.lisp`.
  - A socket the ledger cannot fund is closed before the handshake.
  - Every read is admitted against the live draw and the frame bound
    (`fn-cro-admitted-read-is-funded-and-bounded`,
    `fn-cro-unfunded-read-is-refused`).

  The owner work a request causes is the local consumer operation's, charged
  as the control socket's is. The class's own budget is not yet reconciled
  with the owner's heap reservation. The full per-connection charge row
  (`:principal :connection`, tariff packet Q2 amendment (i)) is owed.
- **The listener** is `[remote_consumer]` ([native config](native-config.md)).
  It requires TLS (`fn-crc-plan-serves-only-with-a-certificate`), does one
  exchange per connection, and never forwards an FNCT request to owner
  control.

Not yet:
- the D46 remote event grammar (FNCE4 remote register and rebase) and the
  multi-group remote query: remote consumers are registered and bound by the
  operator;
- the FNRB1 collection report: a remote page carries one event, as a local
  page does.

The Codex FNCR scope, selection and decision stack (`fn-owner-remote-scope-*`,
`-selection-*`, `-decision-*`, `fn-cre-ingress`) has no caller in this
route and is listed for drop or park in the ledger.

## For the design lane (zmq-shaped patterns, 6.6.1)

Pub/sub is groups plus a consumer (now local or remote). Req/rep is an
article plus a correlated reply under the `fn-app: e1/2` envelope. Push/pull
with competing consumers needs a shared-position consumer kind, which does
not exist.
