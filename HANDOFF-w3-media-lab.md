# w3-media-lab handoff (C2-08)

HEAD: (filled in at commit)

Carried-media import/export through the same bounded staging and acceptance
path as network receipt, and a four-node non-overlapping-contact lab with one
carried-media hop.

## What was added

- `tools/media.py` — export a node's outbound work as a carried-media
  directory (`manifest.json` plus one file per bundle under `bundles/`), and
  import it through `WorkflowJournal.stage_inbound` then
  `run_bp_receive.receive_bpa_request`. The media is read-only: every read is
  one `O_RDONLY | O_NOFOLLOW` descriptor, nothing under the media root is
  opened for writing, and the BPA `delete` step becomes a durable consumption
  record beside the importing node's journals.
- `tests/bp-dtn7/mock_bpa.py` — a file-backed store-and-forward BPA stand-in
  with explicit non-overlapping contact windows, bundle lifetimes and expiry,
  duplicate re-forwarding and reordering. Used when `DTN7_REPO` is unset.
- `tests/bp-dtn7/run_four_node_lab.py` — `home -> relay-a -> relay-b ->
  destination`.
- `tests/test_media.py`, `tests/test_four_node_lab.py`.
- `tests/evidence/2026-09-19-four-node-lab.md` / `.json`.
- `specs/bp-path.md` — the carried-media path.

## Outcomes table (carried media)

(filled in from the run)

## Lab events

(filled in from the run)

## Python counts

(filled in from the run)

## Proposals

(filled in)
