"""Row S2 (lane operability-9): a node moves to the next release beside
the one it runs, and back.

packaging/install.sh keeps each release under PREFIX/releases/VERSION+REV
and points PREFIX/current at the one that runs (the unit's ExecStart goes
through it).  `install.sh --upgrade`, run from the unpacked next release,
prints the gap to expect (the service log's last `run opened ms=N`: ACL2's
rendering, books/native-health.lisp fn-nh-run-opened-line, of the start the
host measured), installs the release beside the current one, stops the
node, asks the next release whether it opens the store (its own verdict;
`reason=store-format` is refused by name and nothing is switched),
switches, starts and waits for `health`.  `PREFIX/current/install.sh
--rollback` is the switch back.  There are no migrations (D34, D38).

This walk stages the production image twice through
packaging/install-native.sh under two source revisions (the releases differ
by REV), writes each release's SHA256SUMS as the tarball does, and runs
install.sh with --no-service, doing the stop and the start itself through
PREFIX/current/bin/fn (what the unit does), so the printed gap is compared
with the interval it measures (SCN-214).

Run with a native image (tests.native_harness): FN_NATIVE_HOST=... python3
-m unittest tests.test_native_install
"""

import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

from tests import foreign_format_store as foreign
from tests.native_harness import ROOT, Node, durable_root, free_port, native_image, requires
from tools.outcome_codes import EXIT

IMAGE = native_image("FN_NATIVE_HOST")
MISSION = "small-community"
OPENSSL = os.environ.get("FN_TEST_OPENSSL_BIN") or "openssl"
# install.sh runs as the operator does: the installed bin/fn ignores the
# harness's variables (packaging/fn, PKT-481 (a)).
CLEAN_ENV = {"PATH": "/usr/bin:/bin:/usr/sbin:/sbin", "HOME": "/tmp", "LANG": "C"}
REV_A = "a" * 40
REV_B = "b" * 40
GAP = re.compile(r"^the node will be away for about (\d+) s: its last start took (\d+) ms", re.M)
UNMEASURED = re.compile(r"^the gap is unmeasured: no OWNER-OPEN line with ms=|^the gap is unmeasured", re.M)
OPENED = re.compile(rb"^run opened ms=(\d+)$", re.M)
TRANSACTIONS = re.compile(rb"^transactions=(\d+) ", re.M)
# The printed gap is the last open alone; the measured interval also holds
# the installer's ask (a heap probe and the stopped report), the start's
# heap probe, the listen and the health call: the slack names them.
SLACK_SECONDS = 30.0


def article(tag):
    tag = str(tag).encode("ascii")
    return (b"From: walk@example.invalid\r\nNewsgroups: local.test\r\n"
            b"Subject: install " + tag + b"\r\n"
            b"Date: Tue, 29 Sep 2026 12:00:00 +0000\r\n"
            b"Message-ID: <install-" + tag + b"@example.invalid>\r\n\r\n"
            b"body " + tag + b"\r\n")


def stage_release(tmp, label, revision):
    """The production image staged as an unpacked release (DESTDIR/fn),
    named by REVISION, with SHA256SUMS as packaging/release-tarball.sh
    writes it (sha256sum lines over every file)."""
    destdir = tmp / ("stage-" + label)
    staged = subprocess.run(
        ["sh", "packaging/install-native.sh"], cwd=ROOT, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=300, check=False,
        env=dict(os.environ, FN_NATIVE_HOST=str(IMAGE), FN_NATIVE_CORE=str(IMAGE) + ".core",
                 FN_NATIVE_SOURCE_REVISION=revision, DESTDIR=str(destdir), PREFIX="/fn"))
    if staged.returncode != 0:
        raise AssertionError("install-native.sh exit {}: {}".format(
            staged.returncode, staged.stdout.decode("utf-8", "replace")[-4096:]))
    top = destdir / "fn"
    lines = []
    for path in sorted(p for p in top.rglob("*") if p.is_file()):
        lines.append("{}  ./{}\n".format(hashlib.sha256(path.read_bytes()).hexdigest(),
                                         path.relative_to(top).as_posix()))
    (top / "SHA256SUMS").write_text("".join(lines))
    return top


def release_name(fn):
    """VERSION+REV from `FN --version` (`fn VERSION (REV)`)."""
    printed = subprocess.run([str(fn), "--version"], env=CLEAN_ENV, capture_output=True,
                             text=True, timeout=300)
    words = printed.stdout.split()
    if words[:1] != ["fn"] or len(words) < 3:
        raise AssertionError("{} --version printed {!r} / {!r}".format(fn, printed.stdout, printed.stderr))
    return "{}+{}".format(words[1], words[2].strip("()"))


@requires(IMAGE)
class InstallWalkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Durable storage (a mission's init refuses tmpfs; PKT-670), a short
        # path (store/control.sock is a Unix socket path).
        cls.tmp = Path(tempfile.mkdtemp(prefix="in-", dir=durable_root()))
        cls.addClassCleanup(shutil.rmtree, cls.tmp, True)
        cls.release_a = stage_release(cls.tmp, "a", REV_A)
        cls.release_b = stage_release(cls.tmp, "b", REV_B)
        cls.name_a = release_name(cls.release_a / "bin" / "fn")
        cls.name_b = release_name(cls.release_b / "bin" / "fn")
        assert cls.name_a != cls.name_b, (cls.name_a, cls.name_b)

    def mark(self, label):
        print("install-walk {}".format(label), file=sys.stderr, flush=True)

    def install(self, script, *flags, prefix, node):
        return subprocess.run(["sh", str(script), "--prefix", str(prefix), "--node", str(node),
                               "--no-service", *flags],
                              env=CLEAN_ENV, capture_output=True, text=True, timeout=600)

    def node(self, launcher, root):
        """A node whose fn.toml `mission` writes (loopback, a fresh port), run
        through LAUNCHER (PREFIX/current/bin/fn: the release current at each
        call), with the self-signed certificate the mission names at
        ROOT/tls."""
        node = Node(self, IMAGE, root=root, name="node", launcher=str(launcher), control=False,
                    port=free_port())
        node.config.unlink()
        node.operator("mission", MISSION, "--port", str(node.port), expect=EXIT.OK)
        (root / "tls").mkdir(exist_ok=True)
        subprocess.run([OPENSSL, "req", "-x509", "-newkey", "ec", "-pkeyopt",
                        "ec_paramgen_curve:P-256", "-nodes", "-days", "2",
                        "-subj", "/CN=127.0.0.1", "-addext", "subjectAltName=IP:127.0.0.1",
                        "-keyout", str(root / "tls" / "key.pem"),
                        "-out", str(root / "tls" / "cert.pem")],
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        os.chmod(root / "tls" / "key.pem", 0o600)
        node.log = root / "log" / "fn.log"
        return node

    def transactions(self, node):
        status = node.operator("status", expect=EXIT.OK)
        found = TRANSACTIONS.search(status.stdout)
        self.assertIsNotNone(found, status.stdout)
        return int(found.group(1))

    def opened_lines(self, node):
        return [int(ms) for ms in OPENED.findall(node.log.read_bytes())]

    def test_upgrade_beside_and_rollback_walk_with_the_printed_gap(self):
        prefix, root = self.tmp / "opt", self.tmp / "node"
        root.mkdir()
        current = prefix / "current" / "bin" / "fn"
        # 1. The first install: releases/A, current -> A, the rendered unit
        #    starts through current.
        first = self.install(self.release_a / "install.sh", prefix=prefix, node=root)
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        self.assertEqual(os.readlink(prefix / "current"), "releases/" + self.name_a)
        self.assertFalse((prefix / "previous").exists())
        self.assertIn("{}/current/bin/fn operator {}/fn.toml run".format(prefix, root),
                      (root / "fn.service").read_text())
        self.assertEqual(release_name(current), self.name_a)
        node = self.node(current, root)
        node.operator("init", expect=EXIT.OK)
        # 2. The node serves on A; its start is measured into the service log
        #    (`run opened ms=N', once per start); posts; stop.
        node.start()
        for i in range(3):
            node.post("<install-{}@example.invalid>".format(i), article(i), group="local.test",
                      expect=EXIT.OK)
        before = self.transactions(node)
        node.stop()
        opened = self.opened_lines(node)
        self.assertEqual(len(opened), 1, node.log.read_bytes()[-3000:])
        last_ms = opened[-1]
        self.mark("A served {} transactions; its start took {} ms".format(before, last_ms))
        # 3. --upgrade from B (--no-service: the node stopped by hand): the
        #    gap printed from that line, B installed beside A, B's own verdict
        #    on the stopped store, the switch.  Measured from here to health.
        began = time.monotonic()
        upgrade = self.install(self.release_b / "install.sh", "--upgrade", prefix=prefix, node=root)
        self.assertEqual(upgrade.returncode, 0, upgrade.stdout + upgrade.stderr)
        gap = GAP.search(upgrade.stdout)
        self.assertIsNotNone(gap, upgrade.stdout)
        self.assertEqual(int(gap.group(2)), last_ms, upgrade.stdout)
        self.assertEqual(int(gap.group(1)), (last_ms + 999) // 1000, upgrade.stdout)
        self.assertIn("stopped checkpoint=", upgrade.stdout)
        self.assertIn("current -> releases/{} (previous -> releases/{})".format(self.name_b, self.name_a),
                      upgrade.stdout)
        self.assertEqual(os.readlink(prefix / "current"), "releases/" + self.name_b)
        self.assertEqual(os.readlink(prefix / "previous"), "releases/" + self.name_a)
        self.assertTrue((prefix / "releases" / self.name_a / "bin" / "fn").is_file())
        self.assertEqual(release_name(current), self.name_b)
        # 4. Start through current, as the unit does; health answers; the
        #    posts are served on B; the interval against the printed gap.
        node.start()
        health = node.operator("health")
        away = time.monotonic() - began
        self.assertTrue(health.stdout.startswith(b"health exit="), health.stdout + health.stderr)
        self.assertNotIn(b"state=not-running", health.stdout)
        self.assertNotIn(b"state=fenced", health.stdout)
        self.assertEqual(self.transactions(node), before)
        node.post("<install-3@example.invalid>", article(3), group="local.test", expect=EXIT.OK)
        self.assertEqual(self.transactions(node), before + 1)
        printed = int(gap.group(1))
        self.mark("gap printed about {} s (last start {} ms); measured stop..health {:.1f} s".format(
            printed, last_ms, away))
        self.assertLessEqual(away, printed + SLACK_SECONDS,
                             "measured {:.1f} s, printed {} s + slack {}".format(away, printed, SLACK_SECONDS))
        self.assertEqual(len(self.opened_lines(node)), 2)
        node.stop()
        # 5. --rollback from PREFIX/current/install.sh (the prefix found by
        #    where it is): A's verdict, the switch back; A serves the post made
        #    under B (one format).
        rollback = subprocess.run(["sh", str(prefix / "current" / "install.sh"), "--rollback",
                                   "--node", str(root), "--no-service"],
                                  env=CLEAN_ENV, capture_output=True, text=True, timeout=600)
        self.assertEqual(rollback.returncode, 0, rollback.stdout + rollback.stderr)
        self.assertIsNotNone(GAP.search(rollback.stdout), rollback.stdout)
        self.assertIn("current -> releases/{} (previous -> releases/{})".format(self.name_a, self.name_b),
                      rollback.stdout)
        self.assertEqual(release_name(current), self.name_a)
        node.start()
        self.assertEqual(self.transactions(node), before + 1)
        node.stop()
        # 6. Refused by name, nothing switched: an installed release as an
        #    upgrade; a rollback when the previous release (B) refuses the
        #    store (its config.json names another format for the ask; the
        #    node's own is put back).
        again = self.install(self.release_a / "install.sh", "--upgrade", prefix=prefix, node=root)
        self.assertEqual(again.returncode, 4, again.stdout + again.stderr)
        self.assertIn("is already installed at", again.stderr)
        config_json = root / "store" / "config.json"
        own = config_json.read_bytes()
        mode = config_json.stat().st_mode & 0o777
        config_json.write_bytes(foreign.ANOTHER_FORMAT_CONFIG)
        config_json.chmod(mode)
        try:
            refused = subprocess.run(["sh", str(prefix / "current" / "install.sh"), "--rollback",
                                      "--node", str(root), "--no-service"],
                                     env=CLEAN_ENV, capture_output=True, text=True, timeout=600)
        finally:
            config_json.write_bytes(own)
            config_json.chmod(mode)
        self.assertEqual(refused.returncode, 4, refused.stdout + refused.stderr)
        self.assertIn("reason=store-format", refused.stdout)
        self.assertIn("refuses that store's format", refused.stderr)
        self.assertEqual(os.readlink(prefix / "current"), "releases/" + self.name_a)
        self.assertEqual(os.readlink(prefix / "previous"), "releases/" + self.name_b)
        # The node still opens its own store on A.
        node.start()
        self.assertEqual(self.transactions(node), before + 1)
        node.stop()

    def test_a_release_that_refuses_the_store_switches_nothing(self):
        # A fresh prefix running A; the node's store is of another format
        # (tests.foreign_format_store: the config.json's format word); B's
        # upgrade is refused by name by B's own verdict: B removed again,
        # current still A, no previous; a rollback there has nothing to go
        # back to.  The gap is unmeasured: the node never ran.
        prefix = self.tmp / "opt2"
        root = self.tmp / "node2"
        root.mkdir()
        first = self.install(self.release_a / "install.sh", prefix=prefix, node=root)
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        _, config, _ = foreign.make_store(None, root, env=CLEAN_ENV,
                                          argv=[str(prefix / "current" / "bin" / "fn")])
        node = config.parent
        upgrade = self.install(self.release_b / "install.sh", "--upgrade", prefix=prefix, node=node)
        self.assertEqual(upgrade.returncode, 4, upgrade.stdout + upgrade.stderr)
        self.assertIsNotNone(UNMEASURED.search(upgrade.stdout), upgrade.stdout)
        self.assertIn("reason=store-format", upgrade.stdout)
        self.assertIn("refuses that store's format", upgrade.stderr)
        self.assertFalse((prefix / "releases" / self.name_b).exists())
        self.assertEqual(os.readlink(prefix / "current"), "releases/" + self.name_a)
        self.assertFalse((prefix / "previous").exists())
        rollback = self.install(prefix / "current" / "install.sh", "--rollback", prefix=prefix, node=node)
        self.assertEqual(rollback.returncode, 4, rollback.stdout + rollback.stderr)
        self.assertIn("nothing to roll back to", rollback.stderr)


if __name__ == "__main__":
    unittest.main()
