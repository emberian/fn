# The DTN image is a BP node: N08, the relay with expiry, and a dtn7-rs return leg admitted

Lane `dtn-node-image`, 2026-09-24 18:10Z to 18:30Z, on hbox. The source was
branch `lane/dtn-node-image` at `0b0de690bceb79c02ca9240677a0f395599430da`
(dev `86857cf3` plus this lane's change). Everything ran under
`/tank/fn/scratch/dtn-node-image/`. Logs, runners and lab output are in
[`dtn-node-image/`](dtn-node-image/), with a `SHA256SUMS` that verifies.

This lane addresses findings 1 to 4 of [m4-dtn-n08](m4-dtn-n08-2026-09-24.md),
along with its finding 5.

## The decision: what the DTN image runs

The sources are specs/bp-node-machine.md, specs/bp-design.md §1.5 and the
direction that fn is a BPv7 node.

- **The node is `bp-node serve`.** It is one FNBS machine
  (`fn-bpnp-step`), the kind-8 retry policy and the owner Store with
  FNRJ/FNWF. It admits each TCPCL session from the channel the kernel
  observed, checked against the Store's enrolled boundaries.
- **`bp send` and `bp receive` are the lab's transport tools.**
- **The node needs configuration.** It needs a path identity and enrolled
  boundaries. It also needs the owner's peer-transit signature check, which
  runs when bp-app accepts a peer-authored article.
- **What the DTN image now loads** (`host/native/build-dtn.lisp`):
  - the node and its application: `bp-node.lisp`, `bp-obligation.lisp` and
    `bp-app.lisp`;
  - the owner and its configuration: `owner.lisp`, `operator.lisp`,
    `config.lisp` and `feed-filename.lisp`;
  - the crypto facility: `crypto.lisp`, `tls.lisp` and `signatures.lisp`.
    It uses the same restart revalidation as build.lisp.
  - the host files for these: `native-config-host`, `feed-filename-host`,
    `native-operator-host`, `hybrid-signature-host`, `bp-release-owner-host`
    and `bp-native-app-host`;
  - `books/bp-app-handoff-time`, `bp-handoff-status` and
    `bp-native-app-fast`.
- **What it still omits:** the NNTP reader, the NNTP service (auth, the
  feed service and the control listener), credential administration and
  the control socket.
  - Each omission is declared in io.lisp's `*fnn-image-omitted-surfaces*`
    (`io.lisp:2584-2598`).
  - The operator refuses `run`, `post` and `principal` with exit 5 instead
    of calling an absent function (`operator.lisp:318-330`). It never takes
    the live-control arm (`operator.lisp:254`).
  - The raw `owner` verb is withdrawn (`build-dtn.lisp:184`).
- **The verb set** is documented in docs/operator.md, "The DTN image".
- **The build-list check** (`tools/build_lists_check.py`):
  - Six `DTN_OMITTED` entries became false and were removed.
  - The two `DTN_RAW_REACH` reasons were removed, because both rested on "bp-node.lisp is not loaded":
    `admin.lisp`'s owner arm and `bp-service.lisp`'s owner ingress.
  - New reach entries cover the operator's refused arms and
    `fnn-owner-topic-local-serialized`'s CSPRNG.
  - Result: "default ld closure 29, DTN 20, omitted with reasons 9; 0
    finding(s)". `tests/test_build_lists_check.py` passes 9/9, with its
    three fixtures re-pointed.

## The fixes

1. **`bp send`: a severed contact is uncertain.** The session runs under a
   `fnn-os-error`/`socket-error` handler that prints `BP send uncertain
   path=<authored wire> reason=contact: ...` and exits 3 (`bp.lisp:559-566`).
2. **`bp send` RETRY re-offers the same identity.**
   - A new trailing positional RETRY names a durable `authored-N.wire` in the
     journal (`bp.lisp:472-493`, `:512-518`).
   - ACL2 `fn-bpn-host-authored-retry` (`host/bp-node-host.lisp:157`) returns
     `(creation sequence)` only under three conditions:
     - the wire decodes;
     - the name is the authored-wire name of the wire's own sequence;
     - the wire is byte for byte `fn-bpn-send` of this ADU to this peer
       under this config, at that creation time and sequence.
   - Otherwise the answer is NIL, and the host refuses (exit 1).
   - A retry reserves no sequence and authors nothing new.
   - Without RETRY, `bp send` authors a new bundle as before. The retry is
     explicit, not inferred from the ADU, because `bp send` keeps no
     resolution record. Two intentional sends of one ADU remain two bundles.
3. **`bp receive` STORE.** A new trailing positional STORE installs the owner
   over that Store and passes `(fnn-bpnode-observed-channel socket)` to
   `fnn-bp-deliver-node` (`bp.lisp:572-650`). Admission is then ACL2's
   `fn-owner-bp-tcpcl-ingress`, as in bp-node. The result depends on the
   peer:
   - **Enrolled boundary:** admitted.
   - **Unenrolled peer:** `BP channel admission refused
     reason=no-trust-profile` is logged. Under ACL2's existing contract
     (`fn-bpaj-tcpcl-ingress-result`, bp-channel-ingress.lisp:25-39) custody
     is kept with no principal, and the node refuses the application request
     (`test_absent_bp_trust_keeps_custody_but_refuses_request_application`).
   - **No STORE:** ACL2 refuses every inbound bundle at the receive boundary,
     unchanged.
4. **Relay expiry (finding 4): the test was wrong, not the host clock
   plumbing and not the machine.**
   - A queued job carries its Bundle Age anchor, which is `fn-bpn-anchor-of`
     at the enqueue's CLOCK_BOOTTIME reading (bp-node-machine.lisp:625).
   - `fn-clock-expiry-decision` (clock.lisp:212) ages an anchored bundle by
     that clock alone.
   - A creation time of 0, which is what wall 0 authors, is also RFC 9171
     §4.2.6's "no accurate clock".
   - So no wall tick can expire it.
   - The test now authors `work-to-expire` in a separate journal with
     lifetime 1000 ms, waits 1.5 s, and ticks with that lifetime.
     `status=expired` is observed.
5. **Tests re-pointed.**
   - `test_bp_node_native` reads `FN_NATIVE_BP_NODE_HOST` and falls back to
     `FN_NATIVE_DEVELOPER_HOST`.
   - The relay receiver is `FN_NATIVE_CONTACT_RECEIVER` running `bp-node
     serve`.
   - The dtn7 driver retries by name and enrolls the carrier (`store init`,
     `operator policy set path-identity`, `operator bp-boundary add
     carrier-boundary dtn7c.bp.gate.invalid dtn://dtn7c/ <port>`) before
     `bp receive ... <store>`.

## Certification and images

- **Farm.** There was one run:
  - Command: `python3 tools/farm.py submit hbox <98 dtn roots>
    tests/acl2/bp-node-host-tests --jobs 2 --timeout-seconds 600
    --remote-root /tank/fn/gates/dtn-node-image-0b0de690 --acl2
    /tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache`.
  - Run `run-20260924T181628Z-3bf6`: 274 of 276 books installed from the
    cache. `host/bp-node-host` and `tests/acl2/bp-node-host-tests` both
    **passed** in 9.3 s.
  - The test book holds the retry witnesses: with a wall clock `(812345678
    7)` and without one `(0 3)`. It also has one refusal each for another
    ADU, another peer, another node, a wrong name and a truncated wire.
  - Manifest: `certify-20260924T181647Z-1772092`, archived.
- **Images.**
  - Built from `git archive 0b0de690` with `acquire`/`validate` loaded for
    `--profile dtn` (98 roots) and `default` (113), then `swarm-build sh
    tools/build_native_host.sh`.
  - The build log has no `undefined` line.
  - These are unfrozen scratch images, not a release: launchers point at
    `/tank/fn/sbcl`, and the runtime needs `LD_LIBRARY_PATH` set to the
    OpenSSL 3.5.8 pair.

| image | launcher SHA-256 | core SHA-256 |
| --- | --- | --- |
| `fn-host-dtn` | `101d2cc819da8126…` | `bd5cbe915370aa42…` |
| `fn-host-dtn-developer` | `c2c9e1b19074d143…` | `1461791c346b49a2…` |

**Smoke test on `fn-host-dtn`:**
- `store init`: exit 0.
- `operator policy set path-identity`: exit 0, generation 2.
- `operator run`: exit 5, `run needs the nntp-service surface, which this
  image omits`.
- `owner` on the developer image: exit 5, `unknown verb owner`.

## Native modules

- **Runner.** [`run.sh`](dtn-node-image/run.sh) sets these variables:
  - `FN_NATIVE_BP_NODE_HOST` and `FN_NATIVE_BP_HOST`: `fn-host-dtn-developer`;
  - `FN_NATIVE_CONTACT_SENDER` and `_RECEIVER`: `fn-host-dtn`;
  - `FN_NATIVE_DTN_HOST` and `FN_NATIVE_DTN_DEVELOPER_HOST`: the DTN pair.
- **Execution.** Each module ran alone, with ephemeral ports and stores
  under `/tmp`.
- **Image profiles.** `test_native_image_profiles` also needs the default
  pair. It ran with the frozen `1b734868` default images of the m4 lane.

| module (log) | image | tests | pass | fail | s | log SHA-256 (16) | vs m4-dtn-n08 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| N08 `test_death_after_kind_eight_retries_once_and_peer_holds_one_copy` | `fn-host-dtn-developer` | 1 | **1** | 0 | 28.7 | `ce7221644b2709cb` | was 0/1 (no verb) |
| test_bp_node_native (whole module) | `fn-host-dtn-developer` | 17 | **17** | 0 | 325.0 | `dd717ba95bc2f90f` | first run on a DTN image |
| test_bp_contact_relay_native (cut, restart, closed window, delivery, expiry) | `fn-host-dtn` both ends | 1 | **1** | 0 | 2.2 | `ed137cae2dfb5de0` | was 0/1 |
| test_bp_service_native | `fn-host-dtn-developer` | 16 | 16 | 0 | 14.1 | `75e8807388a3aa58` | same |
| test_native_app_journal | `fn-host-dtn` / `-developer` | 10 | 10 | 0 | 7.6 | `83212267ba7fcf8b` | same |
| test_bp_contact_native | `fn-host-dtn` | 2 | 2 | 0 | 0.5 | `3be953dde96b5d9e` | same |
| test_bp_receive_integrity_native | `fn-host-dtn-developer` | 4 | 4 | 0 | 0.9 | `cba484ed77a45d64` | same |
| test_native_image_profiles | DTN pair plus the `1b734868` default pair | 12 | 12 | 0 | 5.0 | `eb6d113202d3d0db` | same |

## Real BPA: dtn7-rs 0.21.0 (`/tank/fn/dtn7/repo`), `run_fn_dtn7_interrupted_contact.py --image build/fn-host-dtn`

The output is [`ic1.json`](dtn-node-image/ic1.json), with SHA-256
`6f6776a5abc94a3d…`.

| step | result | log SHA-256 (16) |
| --- | --- | --- |
| 1 interrupted (relay cuts after one byte) | exit **3 (uncertain)**: `BP send uncertain path=…/authored-0.wire reason=contact: [Errno 104] Connection reset by peer`; authored creation=843589253855 sequence=0 | `ca56b6b33ee3a01b` |
| 2 retry `authored-0.wire` straight to the carrier | exit 0; `BP retry creation=843589253855 sequence=0`, so `same_identity_as_step1: true`; one wire in the journal; TCPCL accepted xfer 0 | `e5303709a3636749` |
| 3 carrier SIGKILL and restart on its sled store | dtn7d delivered the ADU **once** | in `ic1.json` |
| 4 return: dtnsend to `dtn://fn-a/incoming` through the carrier | enrollment: 3 steps, exit 0; `bp receive … <store>` logged **no** admission refusal; `BP accepted xfer=1 adu=36` with a kind-5 FNBS row; exit 0 | `303e6ad57fffa683` |

**The unenrolled control.**
- Setup: a fresh store with a path identity and no boundary. `bp receive
  <port> … <store>` ran on it, and `bp send` sent from `dtn://fn-a/`.
- The receiver logged `BP channel admission refused reason=no-trust-profile`,
  then `BP accepted` (custody with no principal, as the ACL2 contract says).
- Logs: `unenrolled-recv.log` (`1929fa69971bb76e`) and `unenrolled-send.log`
  (`67294ff04ef6d2ba`).

**Stopped:**
- The lab's `finally` stopped dtnd by PID. The m4 lab already stops its own
  processes this way.
- The smoke `bp receive` exited by itself (`once`).
- `/tank/fn/node` was not touched.

## M4's exit clause, now

*Interrupted exchange and restart preserve accepted responsibilities;
application acceptance remains distinguishable from transport delivery.*

- **Now has, on the DTN image:**
  - Death after a durable kind 8 is retried with the original identity,
    delivered once and held once (N08).
  - The whole node module passes 17/17. It includes application acceptance,
    refusal without trust, and receipt release.
  - A severed `bp send` is uncertain, and its retry keeps the bundle
    identity.
  - The interrupted relay contact delivers after restart.
  - Expiry is observed.
  - A return bundle from a real BPA through an enrolled carrier is admitted.
- **Still lacks:**
  - A native fn *application* receipt through a real BPA. Step 4 is custody
    by `bp receive`, not `bp-node serve`'s request/receipt dispatch. The
    dtn7 return ADU is not an fn receipt.
  - A four-node run on a real BPA (`--dtn7-repo` mode is unwired).
  - Frozen DTN images from a shared cut. These images are unfrozen scratch
    images.
  - A theorem, as opposed to test witnesses, for `fn-bpn-host-authored-retry`.
    The function is ACL2 in a certified host book, and it has teeth but no
    keystone.
  - `bp send` has no durable resolution record. RETRY is named by the
    operator, not found automatically.
- **Known ACL2 contract, reported and not changed:** an unenrolled channel's
  bundle is kept in custody with no principal. It is not refused at the CL.
  Refusal happens at the application (`request-refused`).
