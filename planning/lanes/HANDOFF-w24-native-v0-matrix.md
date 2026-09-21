# W24 native v0 matrix backend

## Contract

`tools/v0_matrix.py --backend native-operator` makes the two server processes
the packaged native public entry point:

```text
FN_NATIVE_HOST=IMAGE packaging/fn-native operator CONFIG run
```

There is one candidate per node and no fallback to `bin/fn`,
`tools/run_owner.py`, `tools/run_reader.py`, or raw `--fn owner`. Python only
ships files, waits for `LISTENING`, drives NNTP as a test client, and writes the
evidence document. It does not initialize a store, construct native config or
peer records, or run a Python fn peer.

The first slice requires `--native-image`, `--native-config-a`, and
`--native-config-b`. The configs and their stores must already exist on the
execution host, name distinct loopback listener ports, serve `--native-group`
(default `fn.letters`), and permit the test's unauthenticated local POST. The
harness invokes the public native `status` action before starting each node.
It hashes the image and records the image path, digest, selected backend, and
deployed source revision on the document and every row. Those labels identify
the subjects; they do not prove that an externally supplied image was built
from the deployed source.

New records use schema 2. The validator continues to accept immutable schema-1
records as historical development-Python evidence. It requires every schema-2
row's backend/source/image labels to equal the document subject.

## Executed and withheld rows

The native slice executes these existing matrix surfaces on both native
listeners:

- `V0-NODE-STATUS-*` through packaged native `operator CONFIG status`;
- `V0-NODE-START-*` only after packaged native `run` emits `LISTENING`;
- `V0-POST-*` through the raw NNTP test client, including commit, fresh read,
  duplicate refusal, and post-duplicate clock observation;
- `V0-READ-*` through the same socket-only driver after the POST supplies a
  known article.

The current public surface has no native init/reinit contract and no orderly
stop command/result. Those rows are emitted `not-built`; killing a harness
child during cleanup is not relabeled as an accepted operator stop. Native
group/capacity administration is still pending its integrated build and is not
called by this slice. Credential administration and secrets are also excluded;
the command transcript must not become a credential sink.

The native owner currently has reader/POST service but no activated outbound
feed lifecycle. Its durable peer records alone do not start a dialer. All four
`V0-FEED-*` rows therefore remain `not-built`, owned by native outbound-feed
activation. This is deliberate: the ACL2 feed phase/framer and raw adapter do
not establish that the packaged owner loads the feed service or registers its
start/wake/close hooks. Once that composition has a source-matched saved image,
the next slice can require two preprovisioned source-address peer records and
run the existing owner-feed arrival/re-offer observations. Until then the
matrix makes no native feed acceptance claim.

## Verification

The harness tests pin all of the boundary decisions above: the native backend
has exactly one packaged candidate, status uses the same subject, schema-2
labels are complete, schema-1 history still validates, and native feed rows
cannot become outcomes in this slice. Run:

```text
python3 -m unittest tests.test_v0_matrix tests.test_native_v0_matrix
```

This is a harness contract and executable first slice. It is not a two-node
native measurement; no saved native image or preprovisioned pair was run in
this lane.
