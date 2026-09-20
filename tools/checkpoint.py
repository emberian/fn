"""Checkpoint generation publication and selection over the store's file kernel.

The generation machine is `books/checkpoint-publish.lisp`; the bytes are
`books/checkpoint-codec.lisp`.  This module issues the syscalls in the order
the model names and reports nothing the model does not decide:

    write candidate to staging, fsync            checkpoint:candidate-durable
    link it under its generation name            checkpoint:candidate-linked
    fsync the checkpoints directory              checkpoint:candidate-published
    write the selection marker to staging, fsync checkpoint:selection-durable
    os.replace it over the selection marker      checkpoint:selection-replaced
    fsync the checkpoints directory              checkpoint:selection-published

Authority is the explicit selection marker, not the newest valid generation:
a newest-valid rule would turn a corrupt newest generation into a silent
roll-back to its predecessor, which is exactly the outcome the model keeps
distinct (`fn-cpp-recover-reports-corruption`).  With a marker, a corrupt
selected generation is reported as `corrupt`, a missing marker as `none`, and
only a generation that decodes and validates is `ok`.

Every `faults.at("checkpoint:<name>")` site is a cut in tests/campaign/cuts.py.
The host computes the SHA-256 trailer over bytes ACL2 produced (A-CRYPTO) and
slices the suffix by the sequence ACL2 returned; ACL2 revalidates the suffix.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import frame_bridge  # noqa: E402
from tools import run_store  # noqa: E402
from tools.run_store import (EXIT_FAULT, EXIT_OK, NO_FAULTS, StoreError,  # noqa: E402
                             StoreFault, check_regular, fsync_dir, fsync_file,
                             read_regular_bounded, write_all)

GENERATION_NAME = re.compile(r"^generation-([0-9]+)\.fncp$")
SELECTION_NAME = "selected.fncp"
# The selection frame is a header, one CBOR uint and a trailer.
SELECTION_BOUND = 4096


class CheckpointCorrupt(StoreFault):
    """The selected generation or the marker exists but does not decode."""


def _octets(data):
    return "'(" + " ".join(str(byte) for byte in data) + ")"


def checkpoints_dir(store):
    return store.root / "checkpoints"


def generations(store):
    """Published generation numbers, ascending."""
    directory = checkpoints_dir(store)
    if not directory.is_dir():
        return []
    found = []
    for name in os.listdir(directory):
        match = GENERATION_NAME.match(name)
        if match:
            found.append(int(match.group(1)))
    return sorted(found)


def generation_path(store, generation):
    return checkpoints_dir(store) / "generation-{}.fncp".format(generation)


def selection_path(store):
    return checkpoints_dir(store) / SELECTION_NAME


def _payload_bound():
    constants = frame_bridge.session().constants
    return constants["overhead"] + constants["max_inbound"]


def _ensure_dir(store):
    directory = checkpoints_dir(store)
    if not directory.is_dir():
        directory.mkdir(mode=0o700)
        fsync_dir(store.root)


def capture_protected(bridge, records, frontier):
    """ACL2 captures the checkpoint of `records` at `frontier` and frames it."""
    literal = "(" + " ".join(bridge.literal(record) for record in records) + ")"
    form = "(fn-store-checkpoint-protected '{} {} state)".format(literal, int(frontier))
    timeout = max(run_store.ACL2_RECOVER_BASE_SECONDS
                  + run_store.ACL2_RECOVER_PER_RECORD_SECONDS * len(records),
                  bridge.form_timeout(form))
    value = frame_bridge.read_form(bridge.call(form, timeout=timeout))
    if isinstance(value, frame_bridge.Keyword):
        raise StoreError("ACL2 refused to frame a checkpoint: {}".format(value))
    if isinstance(value, list) and value and value[0] == "error":
        raise StoreError("ACL2 refused to capture a checkpoint: {}".format(value[1:]))
    return frame_bridge._as_bytes(value)


def publish(store, bridge, records, faults=NO_FAULTS):
    """Publish a complete new generation.  Returns its number; selects nothing."""
    store._require_writer()
    _ensure_dir(store)
    protected = capture_protected(bridge, records, store.frontier)
    framed = frame_bridge.session().seal(protected)
    existing = generations(store)
    generation = (existing[-1] + 1) if existing else 0
    stage = store.staging / ".checkpoint-{}-{}".format(os.getpid(), os.urandom(12).hex())
    final = generation_path(store, generation)
    # The file kernel's publication discipline: data barrier under a staged
    # name, non-overwriting link under the generation name, directory barrier.
    fd = os.open(stage, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        write_all(fd, framed)
        fsync_file(fd)
    finally:
        os.close(fd)
    faults.at("checkpoint:candidate-durable")
    try:
        os.link(stage, final)
        faults.at("checkpoint:candidate-linked")
        fsync_dir(final.parent)
        faults.at("checkpoint:candidate-published")
    finally:
        try:
            os.unlink(stage)
        except OSError:
            pass
    # Only on the success path: the model's program ends the publication here,
    # and a cut on the error path would mask the exception being raised.
    faults.at("checkpoint:candidate-stage-unlinked")
    return generation


def select(store, bridge, generation, faults=NO_FAULTS):
    """Make a complete published generation the authority."""
    store._require_writer()
    if generation not in generations(store):
        raise StoreError("generation {} is not published".format(generation))
    value = frame_bridge.read_form(bridge.call(
        "(fn-store-checkpoint-selection-protected {})".format(int(generation))))
    if isinstance(value, frame_bridge.Keyword):
        raise StoreError("ACL2 refused to frame the selection marker")
    framed = frame_bridge.session().seal(frame_bridge._as_bytes(value))
    stage = store.staging / ".selection-{}-{}".format(os.getpid(), os.urandom(12).hex())
    fd = os.open(stage, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        write_all(fd, framed)
        fsync_file(fd)
    finally:
        os.close(fd)
    faults.at("checkpoint:selection-durable")
    try:
        os.replace(stage, selection_path(store))
    except OSError:
        try:
            os.unlink(stage)
        except OSError:
            pass
        raise
    faults.at("checkpoint:selection-replaced")
    fsync_dir(checkpoints_dir(store))
    faults.at("checkpoint:selection-published")


def selected_generation(store, bridge):
    """The marker's generation, None without a marker; corrupt markers raise."""
    path = selection_path(store)
    if not check_regular(path):
        return None
    raw = read_regular_bounded(path, SELECTION_BOUND)
    session = frame_bridge.session()
    value = frame_bridge.read_form(bridge.call(
        "(fn-store-checkpoint-selection-decode {} {})".format(
            _octets(raw), _octets(session.digest_of(raw)))))
    if not isinstance(value, list) or not value or value[0] != "ok":
        reason = value[1] if isinstance(value, list) and len(value) > 1 else value
        raise CheckpointCorrupt("selection marker does not decode: {}".format(reason))
    return int(value[1])


def restore_selected(store, bridge, records, frontier):
    """Decode the selected generation and replay only the suffix.

    Returns ("none",), ("ok", generation, sequence, differential) or raises
    CheckpointCorrupt.  `differential` is ACL2's comparison of the restored
    node with the node full replay produced; the caller asserts on it only
    under FN_CHECKPOINT_DIFFERENTIAL.
    """
    generation = selected_generation(store, bridge)
    if generation is None:
        return ("none",)
    path = generation_path(store, generation)
    if not check_regular(path):
        raise CheckpointCorrupt(
            "selected generation {} is missing".format(generation))
    raw = read_regular_bounded(path, _payload_bound())
    session = frame_bridge.session()
    form = "(fn-store-checkpoint-decode {} {} {} {} state)".format(
        _octets(raw), _octets(session.digest_of(raw)), int(frontier), len(records))
    decoded = frame_bridge.read_form(bridge.call(form, timeout=bridge.form_timeout(form)))
    if not isinstance(decoded, list) or not decoded or decoded[0] != "ok":
        reason = decoded[1] if isinstance(decoded, list) and len(decoded) > 1 else decoded
        raise CheckpointCorrupt(
            "selected generation {} does not decode: {}".format(generation, reason))
    sequence = int(decoded[1])
    suffix = records[sequence:]
    literal = "(" + " ".join(bridge.literal(record) for record in suffix) + ")"
    form = "(fn-store-checkpoint-restore '{} {} state)".format(literal, int(frontier))
    timeout = max(run_store.ACL2_RECOVER_BASE_SECONDS
                  + run_store.ACL2_RECOVER_PER_RECORD_SECONDS * len(suffix),
                  bridge.form_timeout(form))
    restored = frame_bridge.read_form(bridge.call(form, timeout=timeout))
    if restored != "ok":
        raise CheckpointCorrupt(
            "selected generation {} does not restore: {}".format(generation, restored))
    differential = frame_bridge.read_form(bridge.call(
        "(fn-store-checkpoint-differential state)")) is True
    return ("ok", generation, sequence, differential)


def differential_enabled():
    return os.environ.get("FN_CHECKPOINT_DIFFERENTIAL", "") not in ("", "0")


def describe(outcome):
    if outcome[0] == "none":
        return "checkpoint=none"
    if outcome[0] == "ok":
        return "checkpoint=ok generation={} suffix-from={} differential={}".format(
            outcome[1], outcome[2], "equal" if outcome[3] else "DIFFERENT")
    return "checkpoint=corrupt reason={}".format(outcome[1])


def command_publish(args):
    store, bridge, records = run_store.open_live_store(args.store, writable=True)
    try:
        generation = publish(store, bridge, records)
        if args.select:
            select(store, bridge, generation)
        print("published generation={} records={} selected={}".format(
            generation, len(records), "yes" if args.select else "no"))
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def command_select(args):
    store, bridge, unused = run_store.open_live_store(args.store, writable=True)
    try:
        select(store, bridge, args.generation)
        print("selected generation={}".format(args.generation))
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def command_status(args):
    store, bridge, unused = run_store.open_live_store(args.store, writable=False)
    try:
        print("generations={} {}".format(
            " ".join(map(str, generations(store))) or "-",
            describe(store.checkpoint_outcome)))
        return EXIT_FAULT if store.checkpoint_outcome[0] == "corrupt" else EXIT_OK
    finally:
        bridge.close()
        store.close()


def main(argv=None):
    parser = run_store.UsageParser(description=__doc__)
    parser.add_argument("--store", required=True)
    sub = parser.add_subparsers(dest="command", required=True)
    publish_parser = sub.add_parser("publish")
    publish_parser.add_argument("--select", action="store_true")
    select_parser = sub.add_parser("select")
    select_parser.add_argument("--generation", type=int, required=True)
    sub.add_parser("status")
    args = parser.parse_args(argv)
    try:
        return {"publish": command_publish, "select": command_select,
                "status": command_status}[args.command](args)
    except (StoreError, OSError, UnicodeError) as error:
        print("checkpoint: {}".format(error), file=sys.stderr)
        return run_store.exit_code_for(error)


if __name__ == "__main__":
    sys.exit(main())
