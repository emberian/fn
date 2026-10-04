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
image built from the current source has run them yet. The five native
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

The five native scenarios that check these are in
`tests/test_native_consumer_exchange.py` and `..._two_nodes.py`. Each needs
`FN_RUN_CONSUMER_EXCHANGE=1` and a source-matched developer image.

| scenario | selector |
|---|---|
| delivery, projection failure, owner restart | `NativeConsumerExchangeTests.test_saved_delivery_survives_projection_fault_and_owner_restart` |
| key-free immutable retry | `NativeConsumerExchangeTests.test_saved_submission_retries_after_restart_without_signing_keys` |
| revoked resend settled by Store observation | `NativeConsumerExchangeTests.test_death_after_acceptance_then_revocation_is_never_refused` |
| two-node cuts | `tests.test_native_consumer_exchange_two_nodes` |
| poll, wait and ack end to end | `NativeConsumerExchangeTests.test_sleeping_consumer_waits_for_the_report_then_acks` (`fn_consumer.py CONFIG wake --wait S`) |

## Not yet

- **Remote consumer.** Applications must run on the node's own machine for
  now. The FNCR transport source is loaded (`host/native/consumer-remote.lisp`),
  but no listener calls `fnn-remote-receive-installed`. Even with a caller,
  every frame would be refused before its first octet is read:
  `fn-owner-remote-operation-preflight` has no positive answer, and returns
  `(:unavailable :remote-operation-entry-installer)` by construction
  (`fn-cro-source-plan`). Three things are missing:
  - an installed, funded operation entry for remote frames (the tariff
    packet, wave 3 row 1);
  - a funded connection class for FNCR on the I/O loops, with TLS handshake
    admission and a configuration key;
  - the event grammar decision for D46.

  The remote report writer (`fn-cr-response-installed-profile`) answers
  unavailable as well.
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

## For the design lane

One possible remote consumer needs no new event grammar: carry the existing
local-control `bound-` consumer requests (password-authenticated) over a
TLS connection class, and admit each request exactly as the control socket
admits it. This is a proposal for that lane and for ember. Nothing here
selects it.
