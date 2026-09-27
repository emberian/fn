"""slrn and pan against a scratch native owner, over TLS, with a redeemed account.

reader-clients-2 lane (planning/evidence/reader-clients-2-2026-09-27/).  For
each image hbox_native built (FN_NATIVE_HOST, the production image, and
FN_NATIVE_DEVELOPER_HOST) this module runs tools/reader_clients_phase.py
with `--clients slrn,pan`: a scratch owner from that image (implicit TLS
under a scratch CA, `[auth] required`, `protected_only`), `account invite`,
XREDEEM over TLS, then stock Debian slrn 1.0.3 and pan 0.162 in the
container tools/reader_clients/Dockerfile builds, typing at them through
tmux and xdotool (tools/reader_clients/drive.py).  Each client talks TLS to
the phase's relay, which presents the node's certificate and logs every line
both ways; the scratch CA is in the container's system trust store, and pan
verifies against it (trust 0).  slrn 1.0.3 verifies nothing (a client
property, recorded).

Every row's verdict is the node's reply line in the client's own transcript
(v0_matrix.client_wire_outcomes); each row is printed as READER-CLIENT-ROW
JSON on stderr, so the module log is the evidence.  Assertions are what the
RFCs and specs/nntp.md require of the node; a known defect's assertion is an
expectedFailure naming its packet, so the fix turns it into an unexpected
success that must be looked at.  Measurements with no settled expectation
(slrn's --create against LIST SUBSCRIPTIONS 503, slrn's Xref marking, pan's
refresh on a pinned connection) are printed, not asserted.

Needs docker on the host (hbox has it; the image is built from
tools/reader_clients/ on first use).  About six minutes per image.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

from v0_matrix import client_wire_outcomes, reply_verdict  # noqa: E402

IMAGES = [(name, path) for name, path in (
    ("production", os.environ.get("FN_NATIVE_HOST")),
    ("developer", os.environ.get("FN_NATIVE_DEVELOPER_HOST"))) if path]
GROUP, SECOND = "local.general", "local.crosspost"
RUNS = {}


def emit(image, row, **fields):
    print("READER-CLIENT-ROW " + json.dumps(dict(image=image, row=row, **fields),
                                              sort_keys=True), file=sys.stderr, flush=True)


def phase(image, work):
    step = subprocess.run(
        [sys.executable, str(ROOT / "tools" / "reader_clients_phase.py"), "--image", image,
         "--work", str(work), "--clients", "slrn,pan", "--group", GROUP,
         "--second-group", SECOND], cwd=str(ROOT), stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, timeout=2400, check=False)
    text = step.stdout.decode("utf-8", "replace").strip()
    report = json.loads(text.splitlines()[-1]) if text else {}
    report["phase_exit"] = step.returncode
    report["phase_stderr"] = step.stderr.decode("utf-8", "replace")[-800:]
    return report


def setUpModule():
    if not IMAGES:
        raise unittest.SkipTest("neither FN_NATIVE_HOST nor FN_NATIVE_DEVELOPER_HOST is set")
    if not shutil.which("docker"):
        raise unittest.SkipTest("docker is not on PATH: the newsreader container cannot run")
    # Under the tree's build/ so the wire logs outlive the run (hbox_native
    # keeps the shipped tree); the module log carries their SHA-256.
    (ROOT / "build").mkdir(exist_ok=True)
    base = Path(tempfile.mkdtemp(prefix="reader-clients-", dir=str(ROOT / "build")))
    for name, image in IMAGES:
        work = base / name
        work.mkdir(parents=True, exist_ok=True)
        report = phase(image, work)
        for client, entry in report.get("clients", {}).items():
            log = Path(entry.get("log", ""))
            entry["seen"] = client_wire_outcomes(log.read_text(encoding="utf-8")) \
                if log.is_file() else {}
            emit(name, client.upper() + "-RUN", log=str(log), sha256=entry.get("sha256"),
                 versions=entry.get("versions"), error=entry.get("error"),
                 driver=entry.get("driver"), check=entry.get("check"),
                 prelude=entry.get("prelude"))
        emit(name, "PHASE", exit=report["phase_exit"], error=report.get("error"),
             owner_exit=report.get("owner_exit"), init=report.get("init"),
             image_core_sha256=report.get("image_core_sha256"))
        RUNS[name] = report


class ReaderClientRows(unittest.TestCase):
    def clients(self):
        for name, report in RUNS.items():
            for client in ("slrn", "pan"):
                entry = report.get("clients", {}).get(client, {})
                yield name, client, entry, entry.get("seen", {})

    def test_the_phase_ran_every_client(self):
        for name, report in RUNS.items():
            with self.subTest(image=name):
                self.assertEqual(report["phase_exit"], 0, report.get("error"))
                self.assertEqual(sorted(report.get("clients", {})), ["pan", "slrn"])

    def test_each_login_was_redeemed_over_tls(self):
        for name, client, entry, seen in self.clients():
            with self.subTest(image=name, client=client):
                emit(name, client.upper() + "-REDEEM", redeem=seen.get("redeem"),
                     login=seen.get("login"))
                self.assertTrue(seen.get("redeem") and seen["redeem"][-1].startswith("281"),
                                seen.get("redeem"))
                self.assertTrue((seen.get("login") or "").startswith("281"), seen.get("login"))

    def test_read_reply_post_and_cancel_draw_the_expected_replies(self):
        # RFC 3977 6.2.1 (220) and 6.3.1 (340 then 240).  CANCEL's 240 is
        # the node filing the control article; whether the target goes is
        # P1 (planning/nntp-gap-inventory-2026-09-26.md), printed not asserted.
        for name, client, entry, seen in self.clients():
            for action, code in (("read", "220"), ("reply", "240"), ("post", "240"),
                                 ("cancel", "240")):
                with self.subTest(image=name, client=client, action=action):
                    line = seen.get(action)
                    extra = {}
                    if action == "cancel":
                        extra["target_afterwards"] = (entry.get("check", {})
                                                      .get("cancelled", {}).get("status"))
                    emit(name, "{}-{}".format(client.upper(), action.upper()), node=line,
                         verdict=reply_verdict(line) if line else "not-exercised", **extra)
                    self.assertTrue((line or "").startswith(code), (action, line))

    def test_pan_verified_the_scratch_ca_through_the_system_trust_store(self):
        # pan (trust 0) refuses an unverifiable certificate before a line is
        # exchanged; a relay handshake failure would be logged.  slrn 1.0.3
        # has no verification at all: recorded, not asserted.
        for name, report in RUNS.items():
            entry = report.get("clients", {}).get("pan", {})
            log = Path(entry.get("log", ""))
            text = log.read_text(encoding="utf-8") if log.is_file() else ""
            with self.subTest(image=name):
                self.assertNotIn("client TLS handshake failed", text)
                self.assertIn("C: AUTHINFO USER pan-friend", text)

    def test_newnews_reports_this_run_and_nothing_after_it(self):
        # RFC 3977 7.4: the Message-IDs of articles in matching groups
        # accepted since the instant; specs/nntp.md NNT-008.
        for name, report in RUNS.items():
            for client in ("slrn", "pan"):
                entry = report.get("clients", {}).get(client, {})
                new = entry.get("new", {})
                seed = entry.get("prelude", {}).get("seed_id")
                with self.subTest(image=name, client=client):
                    emit(name, client.upper() + "-NEWNEWS",
                         **{k: new.get(k) for k in ("newnews_all", "newnews_group",
                                                    "newnews_future")})
                    self.assertTrue(new.get("newnews_all", {}).get("status", "")
                                    .startswith("230"))
                    self.assertIn(seed, new["newnews_all"]["lines"])
                    self.assertIn(seed, new["newnews_group"]["lines"])
                    self.assertEqual(new["newnews_future"]["lines"], [])
                    self.assertTrue(new["newnews_future"]["status"].startswith("230"))

    @unittest.expectedFailure
    def test_newgroups_lists_the_groups_created_since_the_instant(self):
        # RFC 3977 7.3: 231 and every group created since the instant.  The
        # phase's `operator init` created all three during this run, so a
        # day-old instant must list them, in slrn's yymmdd form and the
        # four-digit one; LIST ACTIVE.TIMES (RFC 3977 7.6.4) too.  PKT-665:
        # no host path records a group creation fact (fn-own-declare-group
        # has no caller), so both are always empty.
        for name, report in RUNS.items():
            new = report.get("clients", {}).get("slrn", {}).get("new", {})
            with self.subTest(image=name):
                emit(name, "NEWGROUPS", **{k: new.get(k) for k in (
                    "newgroups_slrn", "newgroups_4digit", "newgroups_future",
                    "active_times")})
                for key in ("newgroups_slrn", "newgroups_4digit"):
                    listed = {line.split()[0] for line in new[key]["lines"] if line.strip()}
                    self.assertTrue(new[key]["status"].startswith("231"))
                    self.assertTrue({GROUP, SECOND, "control.cancel"} <= listed, (key, listed))
                self.assertEqual(new["newgroups_future"]["lines"], [])
                times = {line.split()[0] for line in new["active_times"]["lines"]}
                self.assertTrue({GROUP, SECOND} <= times, times)

    def test_measurements_are_recorded(self):
        # Printed for the record; see the lane's evidence for the packets.
        for name, report in RUNS.items():
            slrn = report.get("clients", {}).get("slrn", {})
            pan = report.get("clients", {}).get("pan", {})
            acts = (slrn.get("driver") or {}).get("actions", {})
            emit(name, "SLRN-CREATE", lists=slrn.get("seen", {}).get("create"),
                 client=acts.get("create"))
            emit(name, "SLRN-XREF", xref=acts.get("xref"))
            emit(name, "PAN-REFRESH",
                 refresh=((pan.get("driver") or {}).get("actions", {}).get("refresh")))
            with self.subTest(image=name):
                self.assertIn("create", acts)
                self.assertIn("xref", acts)


if __name__ == "__main__":
    unittest.main()
