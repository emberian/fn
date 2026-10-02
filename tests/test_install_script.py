"""packaging/install.sh's own decisions, over a fake release (no image).

S061 (sweep 2026-10-03): `ask` refused only on the literal
`reason=store-format`; every other answer of the next release's `status`
(a fault such as the heap probe that never ran, a fence, a usage error)
printed "this continues" and the upgrade switched `current` to a release
that had just said it could not open the store.  Only the stopped report
(exit 0) is a yes now.

S139: `health_wait` took any `health exit=` line other than not-running,
fenced and 19 as the node being up, so an upgrade exited 0 on a node
answering `exhausted`, `unqualified-profile` or `disk`.  Only exit 0 is.

The upgrade walk needs Linux or OpenBSD (install.sh refuses other
systems), so it runs on a build box (tools/remote_check.sh); the health
classification is plain sh and runs anywhere.  The native walk with a real
image is tests.test_native_install.
"""
from __future__ import annotations

import hashlib
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
INSTALL = ROOT / "packaging" / "install.sh"

FAKE_FN = """#!/bin/sh
case $1 in
  --version) echo "fn 6.6.0 (REV)" ;;
  operator)
    case $3 in
      status) printf '%s\\n' "$FAKE_ANSWER"; exit "${FAKE_RC:-0}" ;;
      *) exit 0 ;;
    esac ;;
esac
"""


def release(root: Path, rev: str) -> Path:
    """An unpacked release as check_release reads one, its bin/fn a fake."""
    here = root / f"fn-{rev}"
    (here / "bin").mkdir(parents=True)
    (here / "libexec" / "fn").mkdir(parents=True)
    (here / "share" / "fn" / "systemd").mkdir(parents=True)
    (here / "share" / "fn" / "rc.d").mkdir(parents=True)
    fn = here / "bin" / "fn"
    fn.write_text(FAKE_FN.replace("REV", rev))
    fn.chmod(0o755)
    host = here / "libexec" / "fn" / "fn-host"
    host.write_text("#!/bin/sh\n")
    host.chmod(0o755)
    (here / "share" / "fn" / "systemd" / "fn.service.in").write_text("ExecStart=@PREFIX@\n")
    (here / "share" / "fn" / "rc.d" / "fn.rc.in").write_text("daemon=@PREFIX@\n")
    shutil.copy2(INSTALL, here / "install.sh")
    lines = []
    for path in sorted(p for p in here.rglob("*") if p.is_file()):
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        lines.append(f"{digest}  {path.relative_to(here)}\n")
    (here / "SHA256SUMS").write_text("".join(lines))
    return here


@unittest.skipUnless(platform.system() in ("Linux", "OpenBSD"),
                     "install.sh installs on Linux and OpenBSD only")
class UpgradeAskTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.prefix = self.root / "opt"
        self.node = self.root / "node"
        self.node.mkdir()
        (self.node / "fn.toml").write_text("# fake\n")
        first = release(self.root, "aaaa")
        (self.prefix / "releases").mkdir(parents=True)
        shutil.copytree(first, self.prefix / "releases" / "6.6.0+aaaa", symlinks=True)
        (self.prefix / "current").symlink_to("releases/6.6.0+aaaa")
        self.next = release(self.root, "bbbb")

    def upgrade(self, rc: int, answer: str) -> subprocess.CompletedProcess:
        env = {"PATH": os.environ.get("PATH", "/usr/bin:/bin"),
               "FAKE_RC": str(rc), "FAKE_ANSWER": answer}
        return subprocess.run(
            ["sh", str(self.next / "install.sh"), "--upgrade", "--no-service",
             "--prefix", str(self.prefix), "--node", str(self.node)],
            env=env, capture_output=True, text=True, timeout=60)

    def current(self) -> str:
        return os.readlink(self.prefix / "current")

    def test_a_stopped_report_switches(self):
        done = self.upgrade(0, "stopped checkpoint=none journal-octets=0 transactions-at-most=0")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertEqual(self.current(), "releases/6.6.0+bbbb")

    def assert_refused(self, rc: int, answer: str, said: str) -> None:
        done = self.upgrade(rc, answer)
        self.assertEqual(done.returncode, 4, done.stdout + done.stderr)
        self.assertEqual(self.current(), "releases/6.6.0+aaaa")
        self.assertFalse((self.prefix / "releases" / "6.6.0+bbbb").exists())
        self.assertIn(said, done.stderr)
        self.assertNotIn("this continues", done.stdout + done.stderr)

    def test_a_format_refusal_switches_nothing(self):
        self.assert_refused(1, "open refused reason=store-format: not an fn store of this release",
                            "refuses that store's format")

    def test_a_fault_switches_nothing(self):
        """The case the old ask let through: the next release cannot run
        here (packaging/fn's heap probe, exit 4)."""
        self.assert_refused(4, "fn: fault heap-probe-did-not-run", "fault (status exit 4")

    def test_a_fence_or_any_other_answer_switches_nothing(self):
        self.assert_refused(3, "fenced: recover before further mutation", "uncertain (status exit 3")
        self.assert_refused(5, "usage", "usage (status exit 5)")
        self.assert_refused(9, "", "status exit 9")


class HealthClassTests(unittest.TestCase):
    """install.sh's health_class, run as sh runs it."""

    def classify(self, line: str) -> str:
        text = INSTALL.read_text()
        start = text.index("health_class() {")
        body = text[start:text.index("\n}\n", start) + 3]
        done = subprocess.run(["sh", "-c", body + 'health_class "$1"', "sh", line],
                              capture_output=True, text=True, check=True)
        return done.stdout.strip()

    def test_only_exit_zero_is_up(self):
        self.assertEqual(self.classify("health exit=00 state=clear"), "ok")
        self.assertEqual(self.classify("health exit=04 state=x"), "held")
        for line in ("", "health exit=18 state=not-running (...)",
                     "health exit=20 state=fenced reason=starting",
                     "health exit=19 state=none-held (some states unobserved)"):
            self.assertEqual(self.classify(line), "wait", line)
        for line in ("health exit=21 state=exhausted",
                     "health exit=22 state=unqualified-profile format=9",
                     "health exit=23 state=space-pressure",
                     "health exit=28 state=disk stalled"):
            self.assertEqual(self.classify(line), "held", line)


if __name__ == "__main__":
    unittest.main()
