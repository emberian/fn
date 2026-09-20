#!/usr/bin/env python3
"""Carried media: export a node's outbound work, import it as network receipt.

A media directory is a transport, not an authority.  Export writes one file per
bundle of a node's outbound work -- each bundle being the request ADU ACL2
projected for that work's own durable attempt -- plus a manifest naming each
bundle's transport identity, octet count and copy digest.  Import replays that directory through the *same* bounded staging and
acceptance path the network uses -- `WorkflowJournal.stage_inbound` followed by
`run_bp_receive.receive_bpa_request` -- so no acceptance, receipt, charge,
retention obligation or local number is decided in this module.

The manifest digest is a media-copy-integrity check only.  It detects a damaged
or truncated copy before the bytes reach staging; it is not a content identity.
Content identity, immutable subject, archive obligation and receipt identity
remain ACL2's, derived from the ADU after staging exactly as for a bundle
downloaded from a BPA.  A digest that matches buys the item nothing beyond a
staging attempt.

The media is read-only to this module.  Every read uses one
`O_RDONLY | O_NOFOLLOW` descriptor, no path under `media_root` is ever opened
for writing, and the BPA `delete` step becomes a durable *consumption* record
beside the importing node's own journals.  A carried volume is never mutated by
the node that reads it, so the same volume can be carried onward or re-imported.
"""

from __future__ import annotations

from dataclasses import dataclass
import errno
import hashlib
import json
import os
from pathlib import Path
import stat
import sys
from typing import Iterable

if __package__ in (None, ""):  # loaded with tools/ itself on sys.path
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import run_bp_ingress, run_bp_receive, run_store, workflow_journal

SCHEMA = 1
MANIFEST_NAME = "manifest.json"
ITEM_DIRECTORY = "bundles"
ITEM_SUFFIX = ".bp"
CONSUMED_SUFFIX = ".consumed"

# Bounds are the media's own; the staging and acceptance bounds that matter are
# still the journal's and ACL2's, and are re-applied after these.
MAX_MEDIA_ITEMS = 1024
MAX_ITEM_OCTETS = 65538
MAX_MEDIA_OCTETS = 64 * 1024 * 1024
MAX_MANIFEST_OCTETS = 1024 * 1024
MAX_MEDIA_ID_OCTETS = 128

# Bound names the workflow journal raises when a staging quota is exhausted.
# Matching them only *names* the refusal in this module's report; the decision
# to refuse was the journal's and has already been taken.
STAGING_QUOTA_MESSAGES = frozenset(
    {"inbound count", "inbound aggregate", "inbound bundle bound"})

OUTCOMES = ("accepted", "duplicate", "refused", "uncertain")


class MediaError(RuntimeError):
    """A media-copy boundary failure; never an fn acceptance decision."""


class MediaIncomplete(MediaError):
    """The manifest names an item this copy of the media does not carry whole."""


class MediaCorrupt(MediaError):
    """An item's bytes disagree with the manifest's copy digest."""


@dataclass(frozen=True)
class MediaItem:
    bid: str
    file: str
    octets: int
    sha256: str


@dataclass(frozen=True)
class ExportResult:
    root: Path
    media_id: str
    items: tuple[MediaItem, ...]
    manifest_sha256: str


@dataclass(frozen=True)
class ImportOutcome:
    bid: str
    outcome: str
    reason: str
    receipt_sha256: str = ""

    def __post_init__(self):
        if self.outcome not in OUTCOMES:
            raise MediaError(f"import outcome outside the reported vocabulary: {self.outcome}")


def item_file_name(bid: str) -> str:
    """One media file per bundle, named by its transport identity."""
    return hashlib.sha256(bid.encode("utf-8", "strict")).hexdigest() + ITEM_SUFFIX


def _bounded_media_text(value: str, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise MediaError(f"{label} is not text")
    raw = value.encode("ascii", "strict") if value.isascii() else b""
    if not raw or len(raw) > MAX_MEDIA_ID_OCTETS:
        raise MediaError(f"{label} is outside the bounded media profile")
    if any(byte < 33 or byte > 126 for byte in raw):
        raise MediaError(f"{label} is outside the bounded media profile")
    return value


def _durable_file(path: Path, data: bytes, mode: int = 0o600) -> None:
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode)
    try:
        view = memoryview(data)
        while view:
            written = os.write(fd, view)
            if written <= 0:
                raise OSError("short media write")
            view = view[written:]
        run_store.durable_barrier(fd)
    finally:
        os.close(fd)


def _read_regular_readonly(path: Path, maximum: int) -> bytes:
    """Read one regular file through a single no-follow read-only descriptor.

    The type check, the size and the bytes come from the same open descriptor,
    so a replacement between a path check and an open cannot be read as the
    checked file.  Nothing under the media root is ever opened for writing.
    """
    try:
        fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    except OSError as error:
        if error.errno in (errno.ENOENT, errno.ELOOP):
            raise MediaIncomplete(f"media item is absent or not a regular file: {path.name}") from error
        raise
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode):
            raise MediaIncomplete(f"media item is not a regular file: {path.name}")
        if info.st_size > maximum:
            raise MediaError(f"media item exceeds its bound: {path.name}")
        chunks, remaining = [], maximum + 1
        while remaining:
            chunk = os.read(fd, min(65536, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        data = b"".join(chunks)
        if len(data) != info.st_size:
            raise MediaError(f"media item changed while reading: {path.name}")
        return data
    finally:
        os.close(fd)


def media_digest(media_root: Path) -> dict[str, str]:
    """Digest every file under the media, to show a read did not mutate it."""
    root = Path(media_root)
    result = {}
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        result[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


# --------------------------------------------------------------------------
# Export
# --------------------------------------------------------------------------

def export_media(*, media_root: Path, media_id: str,
                 items: Iterable[tuple[str, bytes]]) -> ExportResult:
    """Write one file per bundle and a manifest, durably, into an empty root.

    `items` are `(transport identity, ADU bytes)` pairs, one per bundle of the
    node's outbound work.  Each ADU is the projection ACL2 produced for that
    work's own durable attempt (`fn-bpo-host-request-adu`, reached through the
    sender's `persist_attempt_then_call`), so a carried hop records its
    submission intent before any byte leaves, exactly as a BPA hop does.  The
    ADU is opaque here: it is not parsed, re-derived or summarized.

    A carried transport identity is a transport concern -- a BPA invents one
    too -- and is never the article's identity, which only ACL2 derives from
    the carried ADU after staging.
    """
    media_id = _bounded_media_text(media_id, "media id")
    root = Path(media_root)
    root.mkdir(mode=0o700, parents=True, exist_ok=False)
    bundles = root / ITEM_DIRECTORY
    bundles.mkdir(mode=0o700)
    described: list[MediaItem] = []
    aggregate = 0
    seen: set[str] = set()
    for bid, adu in items:
        bid = _bounded_media_text(bid, "media bundle identity")
        if bid in seen:
            raise MediaError("media carries one file per bundle identity")
        seen.add(bid)
        if not isinstance(adu, bytes) or not adu:
            raise MediaError("media bundle payload is not bytes")
        if len(adu) > MAX_ITEM_OCTETS:
            raise MediaError("media bundle exceeds the carried item bound")
        aggregate += len(adu)
        if len(described) >= MAX_MEDIA_ITEMS or aggregate > MAX_MEDIA_OCTETS:
            raise MediaError("media exceeds its carried bound")
        name = item_file_name(bid)
        _durable_file(bundles / name, adu, 0o400)
        described.append(MediaItem(bid, name, len(adu),
                                   hashlib.sha256(adu).hexdigest()))
    workflow_journal.fsync_dir(bundles)
    manifest = json.dumps({
        "schema": SCHEMA, "media-id": media_id,
        "items": [{"bid": i.bid, "file": i.file, "octets": i.octets,
                   "sha256": i.sha256} for i in described],
    }, indent=1, sort_keys=True).encode("ascii") + b"\n"
    # The manifest lands last and is fsynced last: a copy interrupted before it
    # has no manifest and is not a media at all, rather than a media that
    # silently under-reports what it carries.
    _durable_file(root / MANIFEST_NAME, manifest, 0o400)
    workflow_journal.fsync_dir(root)
    return ExportResult(root, media_id, tuple(described),
                        hashlib.sha256(manifest).hexdigest())


# --------------------------------------------------------------------------
# Import
# --------------------------------------------------------------------------

def read_manifest(media_root: Path) -> tuple[MediaItem, ...]:
    root = Path(media_root)
    raw = _read_regular_readonly(root / MANIFEST_NAME, MAX_MANIFEST_OCTETS)
    try:
        document = json.loads(raw.decode("ascii"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise MediaError("media manifest is not bounded ASCII JSON") from error
    if not isinstance(document, dict) or document.get("schema") != SCHEMA:
        raise MediaError("unsupported media manifest schema")
    _bounded_media_text(document.get("media-id", ""), "media id")
    entries = document.get("items")
    if not isinstance(entries, list) or len(entries) > MAX_MEDIA_ITEMS:
        raise MediaError("media manifest item list is outside its bound")
    items, aggregate, seen = [], 0, set()
    for entry in entries:
        if not isinstance(entry, dict):
            raise MediaError("media manifest entry is not an object")
        bid = _bounded_media_text(entry.get("bid", ""), "media bundle identity")
        name, octets, digest = entry.get("file"), entry.get("octets"), entry.get("sha256")
        if bid in seen:
            raise MediaError("media manifest repeats a bundle identity")
        seen.add(bid)
        if name != item_file_name(bid):
            raise MediaError("media manifest file does not name its bundle identity")
        if not isinstance(octets, int) or isinstance(octets, bool) or not 0 < octets <= MAX_ITEM_OCTETS:
            raise MediaError("media manifest octet count is outside its bound")
        if not isinstance(digest, str) or len(digest) != 64 or any(
                c not in "0123456789abcdef" for c in digest):
            raise MediaError("media manifest digest is not a sha256 hex digest")
        aggregate += octets
        if aggregate > MAX_MEDIA_OCTETS:
            raise MediaError("media manifest exceeds the carried bound")
        items.append(MediaItem(bid, name, octets, digest))
    return tuple(items)


class MediaVolume:
    """Read-only BPA-shaped view of a carried media directory.

    `inventory` and `download` are exactly the callbacks the network receiver
    is given.  `download` verifies the copy digest and refuses damaged bytes
    *before* they can be staged; it does not decide anything else.
    """

    def __init__(self, media_root: Path):
        self.root = Path(media_root)
        self.items = read_manifest(self.root)
        self.by_bid = {item.bid: item for item in self.items}

    def present(self, bid: str) -> bool:
        item = self.by_bid.get(bid)
        if item is None:
            return False
        path = self.root / ITEM_DIRECTORY / item.file
        try:
            info = os.stat(path, follow_symlinks=False)
        except OSError:
            return False
        return stat.S_ISREG(info.st_mode) and info.st_size == item.octets

    def inventory(self) -> list[str]:
        """The identities this copy of the media actually carries whole."""
        return [item.bid for item in self.items if self.present(item.bid)]

    def download(self, bid: str) -> bytes:
        item = self.by_bid.get(bid)
        if item is None:
            raise MediaIncomplete(f"media does not carry {bid}")
        data = _read_regular_readonly(self.root / ITEM_DIRECTORY / item.file,
                                      MAX_ITEM_OCTETS)
        if len(data) != item.octets:
            raise MediaIncomplete(f"media item is a partial copy: {item.file}")
        if hashlib.sha256(data).hexdigest() != item.sha256:
            raise MediaCorrupt(f"media item disagrees with its copy digest: {item.file}")
        return data


def record_consumed(consumed_root: Path, bid: str) -> Path:
    """Durably record that this node has finished with a carried identity.

    This is what the BPA `delete` step means for read-only media: the media is
    untouched and the record lives with the importing node's journals.  It is
    transport bookkeeping and never an fn acceptance event.
    """
    root = Path(consumed_root)
    root.mkdir(mode=0o700, parents=True, exist_ok=True)
    path = root / (hashlib.sha256(bid.encode("utf-8", "strict")).hexdigest() + CONSUMED_SUFFIX)
    if not path.exists():
        _durable_file(path, bid.encode("utf-8", "strict") + b"\n")
        workflow_journal.fsync_dir(root)
    return path


def consumed_identities(consumed_root: Path) -> int:
    root = Path(consumed_root)
    if not root.is_dir():
        return 0
    return len([p for p in root.iterdir() if p.suffix == CONSUMED_SUFFIX])


def import_item(*, volume: MediaVolume, bid: str, store_root: Path,
                inbox_root: Path, receipt_root: Path, consumed_root: Path,
                source_eid: str, pending_outcome=None,
                faults=run_store.NO_FAULTS,
                store_faults=run_store.NO_FAULTS,
                inbox_faults=run_store.NO_FAULTS,
                receipt_faults=run_store.NO_FAULTS) -> ImportOutcome:
    """Import one carried identity through the network receipt path.

    Every outcome below is the receiver's, the journal's or the media copy
    check's.  The three distinct fn outcomes stay distinct: an uncertain
    staging or publication is reported `uncertain` and never as a refusal, and
    a refusal never reports an acceptance.  There is no partial acceptance: an
    item is either accepted whole through `receive_bpa_request` or it changes
    no acceptance, receipt or pin at all.
    """
    if not volume.present(bid):
        return ImportOutcome(bid, "refused", "media-incomplete")
    try:
        result = run_bp_receive.receive_bpa_request(
            store_root=Path(store_root), inbox_root=Path(inbox_root),
            receipt_root=Path(receipt_root), bid=bid,
            inventory=volume.inventory, download=volume.download,
            delete=lambda found: record_consumed(consumed_root, found),
            source_eid=source_eid, pending_outcome=pending_outcome,
            faults=faults, store_faults=store_faults,
            inbox_faults=inbox_faults, receipt_faults=receipt_faults)
    except MediaCorrupt:
        return ImportOutcome(bid, "refused", "media-digest")
    except MediaIncomplete:
        return ImportOutcome(bid, "refused", "media-incomplete")
    except run_bp_receive.BpReceiveDeletePending as error:
        # The fn decision is durable; only the consumption record is pending.
        return ImportOutcome(bid, error.outcome, "consumption-pending",
                             hashlib.sha256(error.receipt_adu).hexdigest()
                             if error.receipt_adu else "")
    except (workflow_journal.JournalUncertain, run_store.StoreIndeterminate) as error:
        return ImportOutcome(bid, "uncertain", type(error).__name__)
    except workflow_journal.JournalFault as error:
        return ImportOutcome(bid, "refused", f"journal-fault: {error}")
    except workflow_journal.JournalError as error:
        reason = "staging-quota" if str(error) in STAGING_QUOTA_MESSAGES else "staging-refused"
        return ImportOutcome(bid, "refused", f"{reason}: {error}")
    except run_bp_ingress.BpIngressError as error:
        return ImportOutcome(bid, "refused", f"ingress-refused: {error}")
    except run_bp_receive.BpReceiveError as error:
        return ImportOutcome(bid, "refused", f"receiver-refused: {error}")
    if result.outcome in ("accepted", "duplicate"):
        return ImportOutcome(bid, result.outcome, result.outcome,
                             hashlib.sha256(result.receipt_adu).hexdigest()
                             if result.receipt_adu else "")
    # `refused-capacity`, `refused-receipt-id`, `pending-absent`: the receiver
    # refused or deferred with the request still present and nothing charged.
    return ImportOutcome(bid, "refused", result.outcome)


def import_media(*, media_root: Path, store_root: Path, inbox_root: Path,
                 receipt_root: Path, consumed_root: Path, source_eid: str,
                 **kwargs) -> tuple[ImportOutcome, ...]:
    """Import every identity the manifest names, in manifest order."""
    volume = MediaVolume(media_root)
    return tuple(import_item(volume=volume, bid=item.bid, store_root=store_root,
                             inbox_root=inbox_root, receipt_root=receipt_root,
                             consumed_root=consumed_root, source_eid=source_eid,
                             **kwargs)
                 for item in volume.items)


# ---------------------------------------------------------------------------
# Command line
#
# The three outcomes stay distinct all the way out (D13): a carried import
# exits `run_store.EXIT_OK` only when every item was accepted or recognised as
# a duplicate, `EXIT_REFUSED` when one was refused with nothing charged, and
# `EXIT_UNCERTAIN` when one item's staging or publication is undecided.  An
# uncertain item DOMINATES a refused one in a multi-item volume: reporting the
# volume as refused would assert that nothing landed, which is exactly what an
# uncertain cut does not know.  No outcome is decided here -- every line below
# renders a decision `run_bp_receive`, the workflow journal or the copy digest
# already made.
# ---------------------------------------------------------------------------

VOLUME_EXIT = {"accepted": run_store.EXIT_OK, "duplicate": run_store.EXIT_OK,
               "refused": run_store.EXIT_REFUSED,
               "uncertain": run_store.EXIT_UNCERTAIN}


def volume_exit_code(outcomes: Iterable[ImportOutcome]) -> int:
    """The volume's exit code: uncertain over refused over accepted."""
    code = run_store.EXIT_OK
    for outcome in outcomes:
        item = VOLUME_EXIT[outcome.outcome]
        if item == run_store.EXIT_UNCERTAIN:
            return run_store.EXIT_UNCERTAIN
        if item == run_store.EXIT_REFUSED:
            code = run_store.EXIT_REFUSED
    return code


def report_outcome(outcome: ImportOutcome, out=None, err=None) -> None:
    """One line per item, on the stream its outcome belongs to."""
    line = "{} {} {}".format(outcome.outcome, outcome.bid, outcome.reason)
    if outcome.receipt_sha256:
        line += " receipt={}".format(outcome.receipt_sha256)
    if VOLUME_EXIT[outcome.outcome] == run_store.EXIT_OK:
        print(line, file=sys.stdout if out is None else out)
    else:
        print("media: {}".format(line), file=sys.stderr if err is None else err)


def command_verify(args) -> int:
    """Read-only copy check: manifest, item presence and copy digest.

    No store, no journal and no ACL2 process.  A volume that fails here is
    refused before a byte of it reaches staging.
    """
    try:
        volume = MediaVolume(Path(args.media))
        for item in volume.items:
            volume.download(item.bid)
    except (MediaIncomplete, MediaCorrupt) as error:
        print("media: refused {}".format(error), file=sys.stderr)
        return run_store.EXIT_REFUSED
    except MediaError as error:
        print("media: refused {}".format(error), file=sys.stderr)
        return run_store.EXIT_REFUSED
    except OSError as error:
        print("media: fault {}".format(error), file=sys.stderr)
        return run_store.EXIT_FAULT
    print("accepted {} items={} manifest={}".format(
        args.media, len(volume.items),
        media_digest(Path(args.media)).get(MANIFEST_NAME, "")))
    return run_store.EXIT_OK


def command_export(args) -> int:
    """Write a volume from bundle files the sender already projected.

    Each `--bundle <transport-id>=<path>` is an ADU ACL2 produced for that
    work's own durable attempt.  This command copies octets; it derives no
    identity, parses no ADU and invents no manifest field beyond the copy
    digest.
    """
    items = []
    for pair in args.bundle:
        bid, separator, path = pair.partition("=")
        if not separator or not bid:
            print("media: usage --bundle wants <transport-id>=<path>", file=sys.stderr)
            return run_store.EXIT_USAGE
        try:
            items.append((bid, _read_regular_readonly(Path(path), MAX_ITEM_OCTETS)))
        except MediaError as error:
            print("media: refused {}".format(error), file=sys.stderr)
            return run_store.EXIT_REFUSED
        except OSError as error:
            print("media: fault {}".format(error), file=sys.stderr)
            return run_store.EXIT_FAULT
    try:
        result = export_media(media_root=Path(args.media), media_id=args.media_id,
                              items=items)
    except MediaError as error:
        print("media: refused {}".format(error), file=sys.stderr)
        return run_store.EXIT_REFUSED
    except FileExistsError:
        # An existing root is a refusal, not a fault: a volume is written once
        # and never mutated by the node that reads it.
        print("media: refused {} already exists".format(args.media), file=sys.stderr)
        return run_store.EXIT_REFUSED
    except OSError as error:
        print("media: fault {}".format(error), file=sys.stderr)
        return run_store.EXIT_FAULT
    print("accepted {} media-id={} items={} manifest={}".format(
        result.root, result.media_id, len(result.items), result.manifest_sha256))
    return run_store.EXIT_OK


def command_import(args) -> int:
    """Import a volume through the network receipt path and report per item."""
    try:
        outcomes = import_media(
            media_root=Path(args.media), store_root=Path(args.store),
            inbox_root=Path(args.inbox), receipt_root=Path(args.receipts),
            consumed_root=Path(args.consumed), source_eid=args.source_eid)
    except MediaError as error:
        print("media: refused {}".format(error), file=sys.stderr)
        return run_store.EXIT_REFUSED
    except OSError as error:
        print("media: fault {}".format(error), file=sys.stderr)
        return run_store.EXIT_FAULT
    for outcome in outcomes:
        report_outcome(outcome)
    return volume_exit_code(outcomes)


def build_parser():
    parser = run_store.UsageParser(prog="media", description=__doc__.splitlines()[0])
    subs = parser.add_subparsers(dest="command", required=True)

    export = subs.add_parser("export", help="write a carried volume")
    export.add_argument("--media", required=True, help="volume root; must not exist")
    export.add_argument("--media-id", required=True)
    export.add_argument("--bundle", action="append", default=[],
                        metavar="ID=PATH", help="one projected request ADU")
    export.set_defaults(handler=command_export)

    verify = subs.add_parser("verify", help="copy check only; no store, no ACL2")
    verify.add_argument("--media", required=True)
    verify.set_defaults(handler=command_verify)

    importer = subs.add_parser("import", help="import a volume as network receipt")
    importer.add_argument("--media", required=True)
    importer.add_argument("--store", required=True)
    importer.add_argument("--inbox", required=True)
    importer.add_argument("--receipts", required=True)
    importer.add_argument("--consumed", required=True)
    importer.add_argument("--source-eid", required=True,
                          help="the carrier's observed source EID")
    importer.set_defaults(handler=command_import)
    return parser


def main(argv=None) -> int:
    args = build_parser().parse_args(argv)
    return args.handler(args)


if __name__ == "__main__":
    sys.exit(main())
