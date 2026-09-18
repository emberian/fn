# Pinned dtn7-rs BPv7 loopback candidate

`bootstrap.sh EMPTY_WORK_DIRECTORY` clones the revision in `pin.json`, builds it
with Cargo's locked dependency graph, and runs `run_two_node.sh` with IPv6
loopback control and TCP convergence-layer listeners only. It writes compact
`evidence.json` beside the temporary build/run tree. The candidate folder does
not contain upstream source, binaries, logs, or payload artifacts.

The harness distinguishes discovery plus non-destructive download from endpoint
pop. Its safe ingress prototype writes a temporary download, fsyncs the file,
renames it into an inbox, fsyncs that directory, and only then explicitly
deletes the BPA bundle. That is not fn validation, acceptance, a receipt, or a
retention release.

This optional test requires Cargo, Git, zsh, Python, curl, ripgrep and lsof.
Fixed loopback ports 32101/32102/32111/32112 must be available. The exact
recorded run is [transport evidence](../evidence/2026-09-18-bpv7-transport.md).

`DTN7_REPO=/absolute/path/to/pinned/dtn7-rs ./run_fn_ingress_lab.sh` additionally
exercises the current repository's actual fn receiver, including restart and
new-bundle/same-article duplicate recognition. It uses ports
32301/32302/32311/32312 and requires the fn ACL2 books to have been certified.
See [fn ingress evidence](../evidence/2026-09-18-bp-ingress.md). Its sender is a
BPA with a fixture file; durable fn sender jobs and receipts are separate work.

The fn ingress runner builds a small extra binary with
`build_payload_extractor.sh`, using the pinned checkout's existing BP decoder.
Its receive path uses `tools/bpa_dtn7.py` for bounded non-destructive HTTP
download, then extracts the ADU from that local raw bundle. The
[boundary evidence](../evidence/2026-09-18-bpa-boundary.md) records the byte caps,
timeouts, mock HTTP cases and repeated real-BPA acceptance/duplicate test.

The complete application exchange now runs with:

```sh
python3 tests/bp-dtn7/run_fn_exchange_lab.py --dtn7-repo /absolute/path/to/pinned/dtn7-rs
```

Run from the repository root with the current ACL2 books certified. It uses
ports 32401/32402/32411/32412 and writes its exact source/version/results record
under `build/bp-fn-exchange/`. It connects actual fn sender work and receiver
acceptance through BP, omits a receipt, restarts, regenerates on a distinct-BID
retry and returns the receipt through BP into durable sender state. All authority
is trusted local test policy; this is not authenticated peering.

The [exchange evidence](../evidence/2026-09-18-bp-exchange.md) retains a pinned
BPA restart window in which stored inventory does not resume forwarding. The
driver uses explicit durable fn retry after sender restart, without assuming
that an API reply or inventory appearance makes the BPA reliable. It records
process-stop signals and any SIGKILL fallback. No physical power-loss claim follows.
