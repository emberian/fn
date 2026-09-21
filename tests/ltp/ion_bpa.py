"""ION-side adapter surfaces for the fn LTP feasibility laboratory.

ION exposes no non-destructive receive: `bp_receive()` deletes the delivery
queue element, detaches the payload ZCO and destroys the bundle inside one SDR
transaction it commits before returning.  So the inventory/download/delete
triple fn's receiver requires cannot be served by the BPA.  `IonStagingInbox`
serves it from the *app-level staging copy* written by `fn_ltp_stage.c`, and
`delete` therefore removes fn's own staged file, not an ION-retained bundle.

The same destruction is why `bundle` is a reconstruction here and not a read.
fn stages an inbound bundle under the identity ACL2 derives from the bundle's
own primary block, so the receiver needs that block; ION has already destroyed
it by the time any application runs.  What `BpDelivery` does report is exactly
the three fields the identity projection reads, and `IonStagingInbox.bundle`
hands those back to ACL2 to encode.  See the method for what that costs.
"""
from __future__ import annotations

from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import bundle_bridge  # noqa: E402

MAX_BID_OCTETS = 512
MAX_ADU_OCTETS = 65538

# RFC 9171 section 4.2.8 measures a bundle's lifetime in milliseconds, and
# `fn-clock-expiry-decision` compares it against a millisecond DTN time.  ION's
# `bpsendfile` takes its TTL in seconds.  The two units belong to two different
# programs and neither is a quantity ACL2 computes; this is the one place the
# lab writes the correspondence down.
MILLISECONDS_PER_SECOND = 1000


class IonLtpSender:
    """Submit an ADU through ION's shipped `bpsendfile` over the LTP outduct."""

    def __init__(self, node_dir: Path, run: Path, own_eid: str, env: dict,
                 bp_destination: str, lifetime_seconds: int = 300):
        self.node_dir, self.run, self.own_eid, self.env = node_dir, run, own_eid, env
        # The TTL every submission of this sender asks ION for.  The staging
        # inbox reconstructs the primary block with the same number, so the
        # receiver's expiry verdict is about the deadline the bundle was
        # actually given rather than one the lab invented at the far end.
        self.lifetime_seconds = int(lifetime_seconds)
        # fn's configured `peer-eid` is an *application* identity that ACL2
        # binds inside the request ADU.  ION's BP layer needs its own
        # registered destination EID, and ION registers only the `ipn` scheme
        # in this laboratory, so the two cannot be the same string.  An ION
        # adapter must carry this mapping explicitly; the pinned dtn7-rs lab
        # conflated them because dtn7-rs is natively `dtn:`-scheme.
        self.bp_destination = bp_destination
        self.submits = []

    def submit(self, adu: bytes, destination: str, label: str,
               lifetime: int | None = None) -> str:
        if not isinstance(adu, bytes) or not 0 < len(adu) <= MAX_ADU_OCTETS:
            raise ValueError("outbound ADU outside lab profile")
        lifetime = self.lifetime_seconds if lifetime is None else int(lifetime)
        path = self.run / (label + ".adu")
        path.write_bytes(adu)
        result = subprocess.run(
            ["bpsendfile", self.own_eid, self.bp_destination, str(path), "0",
             str(lifetime)],
            cwd=str(self.node_dir), env=self.env, timeout=60,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (self.run / (label + "-submit.txt")).write_bytes(result.stdout)
        if result.returncode != 0:
            raise RuntimeError(f"bpsendfile failed: {result.stdout!r}")
        # ION's `bpsendfile` prints no bundle identifier and `bp_send()` returns
        # only an in-process SDR object address.  There is no transport handle
        # for fn's durable attempt record to bind here; the label below is a
        # local fn name, not an observed BPA identity.
        self.submits.append({"label": label, "application_peer_eid": destination,
                             "bp_destination_eid": self.bp_destination})
        return "ion-unreported:" + label


class IonStagingInbox:
    """inventory/download/delete/bundle over `fn_ltp_stage`, not over ION."""

    def __init__(self, stage_dir: Path, *, destination_eid: str = "ipn:2.1",
                 lifetime_seconds: int = 300, bridge=None):
        self.stage_dir = Path(stage_dir)
        # Neither of these is identity-bearing: `fn-bpp-primary-identity`
        # reads the source, the creation time and the sequence, and
        # books/bp-primary.lisp carries the theorems that it ignores the
        # destination and the report-to.  They are here because a primary
        # block is not well formed without them.
        self.destination_eid = destination_eid
        self.lifetime_seconds = int(lifetime_seconds)
        self.bridge = bridge

    def inventory(self) -> tuple[str, ...]:
        names = []
        for entry in sorted(self.stage_dir.iterdir()):
            if entry.name.startswith("."):
                continue
            raw = entry.name.encode("ascii", "strict")
            if not 1 <= len(raw) <= MAX_BID_OCTETS:
                raise RuntimeError("staged BID outside the bounded lab profile")
            names.append(entry.name)
        return tuple(names)

    def download(self, bid: str) -> bytes:
        path = self.stage_dir / bid
        if path.parent != self.stage_dir or not path.is_file():
            raise RuntimeError("staged BID is not a staged file")
        raw = path.read_bytes()
        if not 0 < len(raw) <= MAX_ADU_OCTETS:
            raise RuntimeError("staged ADU outside the bounded lab profile")
        return raw

    def delete(self, bid: str) -> None:
        (self.stage_dir / bid).unlink()

    # -- the primary block fn stages under -------------------------------

    def observed_fields(self, bid: str) -> tuple:
        """The three identity-bearing fields ION reported, out of the BID.

        `fn_ltp_stage.c` names each staged file `<source EID>|<creation
        milliseconds>|<creation sequence>` from `BpDelivery`, with `/` turned
        into `_` so the name is one path component.  That substitution is not
        invertible, so a `dtn`-scheme source cannot be recovered from the name
        and this method refuses rather than guessing; the laboratory registers
        the `ipn` scheme (tests/ltp/pin.json), whose text form contains no `/`.
        Running it over `dtn` endpoints needs `fn_ltp_stage.c` to record the
        fields beside the payload instead of inside the name.
        """
        source_text, _, rest = bid.partition("|")
        creation, _, sequence = rest.partition("|")
        if not creation.isdigit() or not sequence.isdigit() or "|" in sequence:
            raise RuntimeError(
                "staged BID {!r} is not fn_ltp_stage.c's "
                "<source>|<creation>|<sequence>".format(bid))
        if "_" in source_text:
            raise RuntimeError(
                "staged BID {!r} carries a source EID that fn_ltp_stage.c's "
                "'/' -> '_' substitution has made unrecoverable; this lab is "
                "pinned to the ipn scheme".format(bid))
        return bundle_bridge.ipn_eid(source_text), int(creation), int(sequence)

    def bundle(self, bid: str) -> bytes:
        """The primary block of the bundle whose payload was staged under `bid`.

        fn stages an inbound bundle under the identity ACL2 derives from the
        bundle's own primary block, so the receiver is handed that block and
        never the transport's opinion of it.  Over ION the block itself cannot
        be handed over: `bp_receive()` destroys the bundle inside the SDR
        transaction it commits before it returns (README, "the receive seam"),
        and no ION API gives an application the octets afterwards.

        What survives is `BpDelivery`'s report of the source EID and the
        creation timestamp -- which is exactly `fn-bpp-primary-identity-value`
        (books/bp-primary.lisp): source, creation time, sequence, for a bundle
        that is not a fragment.  So this re-encodes those three observed
        fields through ACL2's own `fn-bpi-host-bundle-prefix`, and every field
        it supplies rather than observes (destination, report-to, flags, CRC
        type) is one the identity projection provably ignores.

        What that costs, stated plainly and recorded in the lab's evidence:
        the identity fn stages under here is derived from ION's report of the
        bundle's fields, re-encoded canonically, and NOT from the bundle's own
        octets as they crossed the link.  A transport that misreported those
        fields would be believed.  The dtn7-rs lab does not have this gap --
        its agent hands over the bundle -- and closing it for ION needs the
        block captured inside `fn_ltp_stage.c` before `bp_receive()` returns,
        through the C API and not through any shipped utility.
        """
        source, creation, sequence = self.observed_fields(bid)
        return bundle_bridge.encode_primary(
            destination=bundle_bridge.ipn_eid(self.destination_eid),
            source=source, report_to=source, creation=creation,
            sequence=sequence,
            lifetime=self.lifetime_seconds * MILLISECONDS_PER_SECOND,
            bridge=self.bridge)
