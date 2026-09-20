"""ION-side adapter surfaces for the fn LTP feasibility laboratory.

ION exposes no non-destructive receive: `bp_receive()` deletes the delivery
queue element, detaches the payload ZCO and destroys the bundle inside one SDR
transaction it commits before returning.  So the inventory/download/delete
triple fn's receiver requires cannot be served by the BPA.  `IonStagingInbox`
serves it from the *app-level staging copy* written by `fn_ltp_stage.c`, and
`delete` therefore removes fn's own staged file, not an ION-retained bundle.
"""
from __future__ import annotations

from pathlib import Path
import subprocess

MAX_BID_OCTETS = 512
MAX_ADU_OCTETS = 65538


class IonLtpSender:
    """Submit an ADU through ION's shipped `bpsendfile` over the LTP outduct."""

    def __init__(self, node_dir: Path, run: Path, own_eid: str, env: dict,
                 bp_destination: str):
        self.node_dir, self.run, self.own_eid, self.env = node_dir, run, own_eid, env
        # fn's configured `peer-eid` is an *application* identity that ACL2
        # binds inside the request ADU.  ION's BP layer needs its own
        # registered destination EID, and ION registers only the `ipn` scheme
        # in this laboratory, so the two cannot be the same string.  An ION
        # adapter must carry this mapping explicitly; the pinned dtn7-rs lab
        # conflated them because dtn7-rs is natively `dtn:`-scheme.
        self.bp_destination = bp_destination
        self.submits = []

    def submit(self, adu: bytes, destination: str, label: str, lifetime: int = 300) -> str:
        if not isinstance(adu, bytes) or not 0 < len(adu) <= MAX_ADU_OCTETS:
            raise ValueError("outbound ADU outside lab profile")
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
    """inventory/download/delete over `fn_ltp_stage` output, not over ION."""

    def __init__(self, stage_dir: Path):
        self.stage_dir = Path(stage_dir)

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
