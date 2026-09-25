"""Actual saved-image checkpoint publication, selection, and recovery."""

import os
from pathlib import Path
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import time
import unittest

from tools import run_store
from tests.native_process import wait_for_announcement, stop_and_diagnostics


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
PRODUCTION_IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host-developer is required for raw Store fixtures")
class NativeCheckpointTests(unittest.TestCase):
    image = IMAGE

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-checkpoint-")
        self.base = Path(self.temporary.name)
        self.payload = self.base / "payload"
        self.payload.write_bytes(b"native checkpoint payload\r\n")
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)

    def tearDown(self):
        self.temporary.cleanup()

    def native(self, *args, expected=0, env=None):
        result = subprocess.run(
            [str(self.image), "--fn", *map(str, args)], cwd=ROOT,
            env=env or self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=30, check=False, text=True)
        self.assertEqual(result.returncode, expected,
                         f"native {args} returned {result.returncode}\n"
                         f"stdout={result.stdout}\nstderr={result.stderr}")
        return result

    def python_checkpoint(self, store, command, *args, expected=0):
        result = subprocess.run(
            [sys.executable, "tools/checkpoint.py", "--store", str(store),
             command, *map(str, args)], cwd=ROOT, env=self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
            check=False, text=True)
        self.assertEqual(result.returncode, expected,
                         f"python checkpoint {command} returned {result.returncode}\n"
                         f"stdout={result.stdout}\nstderr={result.stderr}")
        return result

    def python_store(self, store, command, *args, expected=0):
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(store),
             command, *map(str, args)], cwd=ROOT, env=self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
            check=False, text=True)
        self.assertEqual(result.returncode, expected,
                         f"python store {command} returned {result.returncode}\n"
                         f"stdout={result.stdout}\nstderr={result.stderr}")
        return result

    def initialized(self, name="store", article=True):
        store = self.base / name
        self.native("store", store, "init", "fn.letters")
        if article:
            self.native("store", store, "post", "<checkpoint@example.invalid>",
                        self.payload, "-", "-", "fn.letters")
        return store

    def consumer_history(self, control, name):
        """Commit real owner bootstrap, registration, and zero-position ACK."""
        cursor = self.base / (name + "-register.fncu")
        position = self.base / (name + "-position.fncu")
        self.assertIn("consumer accepted",
                      self.native("consumer", "bootstrap", control).stdout)
        self.assertIn("consumer accepted",
                      self.native("consumer", "register", control, name,
                                  "fn.letters", cursor).stdout)
        self.assertTrue(cursor.read_bytes().startswith(b"fncu\x01"))
        self.assertIn("consumer accepted",
                      self.native("consumer", "position", control, name,
                                  position).stdout)
        self.assertEqual(position.read_bytes(), cursor.read_bytes())
        self.assertIn("consumer accepted",
                      self.native("consumer", "ack", control, cursor).stdout)
        self.assertEqual(position.read_bytes(), cursor.read_bytes())
        return cursor

    @unittest.skipUnless(sys.platform.startswith("linux") and
                         os.environ.get("FN_RUN_NATIVE_CLONE") == "1",
                         "run only against a combined E2/checkpoint developer image")
    def test_fenced_clone_rollover_after_selected_pack_reclaim(self):
        source = self.initialized("clone-source")
        control = self.base / "clone-source-control.sock"
        with socket.socket() as probe:
            probe.bind(("127.0.0.1", 0))
            port = probe.getsockname()[1]
        config = self.base / "clone-source.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\n[control]\npath = "{}"\n'.format(source, port, control),
            encoding="ascii")
        owner = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(config), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        try:
            wait_for_announcement(owner, b"LISTENING ")
            initial_cursor = self.consumer_history(control, "clone-worker")
            # An accepted article after registration gives poll a real
            # report and a cursor strictly beyond the zero ACK.  Poll itself
            # is read-only; only the subsequent ACK changes durable progress.
            msgid = "<clone-progress@example.invalid>"
            progress_article = self.base / "clone-progress.eml"
            progress_article.write_bytes(
                b"From: author@example.invalid\r\n"
                b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
                b"Newsgroups: fn.letters\r\n"
                b"Subject: clone progress\r\nMessage-ID: " +
                msgid.encode("ascii") + b"\r\n\r\nadvance before clone\r\n")
            self.native("operator", config, "post", "--message-id", msgid,
                        "--payload", progress_article, "--group", "fn.letters")
            advanced_cursor = self.base / "clone-worker-advanced.fncu"
            report = self.base / "clone-worker-report.fnse"
            self.assertIn("consumer accepted",
                          self.native("consumer", "poll", control,
                                      "clone-worker", advanced_cursor,
                                      report).stdout)
            self.assertTrue(report.read_bytes())
            self.assertNotEqual(advanced_cursor.read_bytes(),
                                initial_cursor.read_bytes())
            self.assertIn("consumer accepted",
                          self.native("consumer", "ack", control,
                                      advanced_cursor).stdout)
            old_cursor = advanced_cursor
            settled = self.base / "clone-worker-settled.fncu"
            self.native("consumer", "position", control, "clone-worker",
                        settled)
            self.assertEqual(settled.read_bytes(), advanced_cursor.read_bytes())
        finally:
            diagnostic = stop_and_diagnostics(owner, timeout=60)
            self.assertEqual(owner.returncode, 0, diagnostic)
        self.native("checkpoint", "pack", source, "select")
        self.native("checkpoint", "pack-reclaim", source)

        # ACL2's native Store path width is enforced before an oversized or
        # relative destination reaches filesystem traversal.
        oversized = self.base / ("x" * 500)
        refused = self.native("checkpoint", "clone", source, oversized,
                              expected=run_store.EXIT_REFUSED)
        self.assertIn("clone path", refused.stderr)
        refused = self.native("checkpoint", "clone", source,
                              "relative-target",
                              expected=run_store.EXIT_REFUSED)
        self.assertIn("clone path", refused.stderr)

        # A nonempty destination is refused without touching its contents.
        occupied = self.base / "occupied"
        occupied.mkdir()
        (occupied / "keep").write_bytes(b"preserve")
        self.native("checkpoint", "clone", source, occupied,
                    expected=run_store.EXIT_REFUSED)
        self.assertEqual((occupied / "keep").read_bytes(), b"preserve")

        target = self.base / "clone-target"
        self.native("checkpoint", "clone", source, target)
        self.assertFalse((target / "clone-pending.fnce").exists())
        self.assertEqual(
            (source / "packs" / "generation-0.fncp").read_bytes(),
            (target / "packs" / "generation-0.fncp").read_bytes())
        self.assertIn("articles=2",
                      self.native("store", target, "recover").stdout)
        # Prefix reclamation changed physical names, never dense history.
        packed = self.native("checkpoint", "pack", target)
        # Zero-position ACK is idempotent and adds no Store event.  The
        # advancing ACK is the sole progress publication in this history.
        self.assertIn("records=6", packed.stdout)
        target_control = self.base / "clone-target-control.sock"
        with socket.socket() as probe:
            probe.bind(("127.0.0.1", 0))
            target_port = probe.getsockname()[1]
        target_config = self.base / "clone-target.toml"
        target_config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\n[control]\npath = "{}"\n'.format(
                target, target_port, target_control), encoding="ascii")
        owner = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(target_config), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        try:
            wait_for_announcement(owner, b"LISTENING ")
            refused = self.native("consumer", "ack", target_control,
                                  old_cursor,
                                  expected=run_store.EXIT_REFUSED)
            self.assertIn("consumer refused", refused.stdout)
            missing_position = self.base / "clone-old-position.fncu"
            refused = self.native("consumer", "position", target_control,
                                  "clone-worker", missing_position,
                                  expected=run_store.EXIT_REFUSED)
            self.assertIn("consumer refused", refused.stdout)
            self.assertFalse(missing_position.exists())
        finally:
            diagnostic = stop_and_diagnostics(owner, timeout=60)
            self.assertEqual(owner.returncode, 0, diagnostic)
        self.native("checkpoint", "clone", source, target,
                    expected=run_store.EXIT_REFUSED)

        # Publication has not happened at this cut.  The abandoned sibling
        # staging tree remains fenced, and the source remains recoverable.
        prepublication = self.base / "clone-prepublication"
        self.stopped_then_killed(
            ("checkpoint", "clone", source, prepublication),
            "clone-fence-durable")
        self.assertFalse(prepublication.exists())
        self.assertIn("articles=2",
                      self.native("store", source, "recover").stdout)

        for point in ("clone-published", "clone-rollover-durable"):
            with self.subTest(point=point):
                destination = self.base / point
                self.stopped_then_killed(
                    ("checkpoint", "clone", source, destination), point)
                self.assertTrue((destination / "clone-pending.fnce").is_file())
                refused = self.native("store", destination, "recover",
                                      expected=run_store.EXIT_REFUSED)
                self.assertIn("fenced pending durable incarnation", refused.stderr)
                self.native("checkpoint", "clone-resume", destination)
                self.assertFalse((destination / "clone-pending.fnce").exists())
                self.assertIn("articles=2",
                              self.native("store", destination, "recover").stdout)
                packed = self.native("checkpoint", "pack", destination)
                self.assertIn("records=6", packed.stdout)

        # Process death after unlink is safe because the independent reopen
        # already confirmed the durable rollover.  A power-loss claim still
        # relies on the subsequent parent-directory fsync and OS contract.
        unlinked = self.base / "clone-fence-unlinked"
        self.stopped_then_killed(
            ("checkpoint", "clone", source, unlinked),
            "clone-fence-unlinked")
        self.assertFalse((unlinked / "clone-pending.fnce").exists())
        self.assertIn("articles=2",
                      self.native("store", unlinked, "recover").stdout)
        self.assertIn("records=6",
                      self.native("checkpoint", "pack", unlinked).stdout)

    @unittest.skipUnless(sys.platform.startswith("linux") and
                         os.environ.get("FN_RUN_NATIVE_CLONE") == "1",
                         "run only against a combined E2/checkpoint developer image")
    def test_clone_refuses_canonical_parent_alias_above_path_bound(self):
        long_parent = (self.base / ("a" * 180) / ("b" * 180) /
                       ("c" * 180))
        long_parent.mkdir(parents=True)
        alias = self.base / "short-parent"
        alias.symlink_to(long_parent, target_is_directory=True)
        source = alias / "source"
        self.native("store", source, "init", "fn.letters")
        target = alias / "target"
        refused = self.native("checkpoint", "clone", source, target,
                              expected=run_store.EXIT_REFUSED)
        self.assertIn("clone path", refused.stderr)
        self.assertFalse(target.exists())

    @unittest.skipUnless(sys.platform.startswith("linux") and
                         os.environ.get("FN_RUN_NATIVE_CLONE") == "1",
                         "run only against a combined E2/T10/checkpoint developer image")
    def test_clone_reopens_historical_authorship_verdict(self):
        source = self.initialized("authored-source", article=False)
        control = self.base / "author-control.sock"
        with socket.socket() as probe:
            probe.bind(("127.0.0.1", 0))
            port = probe.getsockname()[1]
        config = self.base / "author.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\n[control]\npath = "{}"\n'.format(source, port, control),
            encoding="ascii")
        principal = self.base / "principal.bin"
        ed_public = self.base / "ed-public.bin"
        ed_secret = self.base / "ed-secret.bin"
        ml_private = self.base / "ml-private.pem"
        ml_public = self.base / "ml-public.pem"
        article = self.base / "authored.eml"
        principal.write_bytes(bytes([85]) * 32)
        ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        openssl = os.environ.get("FN_TEST_OPENSSL", "openssl")
        subprocess.run([openssl, "genpkey", "-algorithm", "ML-DSA-65",
                        "-out", str(ml_private)], timeout=60, check=True)
        subprocess.run([openssl, "pkey", "-in", str(ml_private), "-pubout",
                        "-out", str(ml_public)], timeout=60, check=True)
        msgid = "<clone-authored@example.invalid>"
        article.write_bytes(
            b"From: author@example.invalid\r\n"
            b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
            b"Newsgroups: fn.letters\r\n"
            b"Subject: clone historical verdict\r\nMessage-ID: " +
            msgid.encode("ascii") + b"\r\n\r\nexact authored source\r\n")

        owner = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(config), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        try:
            wait_for_announcement(owner, b"LISTENING ")
            self.native("hybrid-enroll", control, "1", principal,
                        ed_public, ml_public)
            signed = self.native("hybrid-sign", principal, ed_public,
                                 ed_secret, ml_public, ml_private, article)
            parts = dict(line.split() for line in signed.stdout.splitlines())
            ed_sig = self.base / "ed.sig"
            ml_sig = self.base / "ml.sig"
            ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
            ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
            self.native("hybrid-author", control, "1", article,
                        ed_sig, ml_sig, ml_public)
            wrong_ed = self.base / "wrong-ed-public.bin"
            wrong_ed.write_bytes(bytes([99]) * 32)
            self.native("hybrid-enroll", control, "2", principal,
                        wrong_ed, ml_public)
            self.consumer_history(control, "authored-worker")
        finally:
            diagnostic = stop_and_diagnostics(owner, timeout=60)
            self.assertEqual(owner.returncode, 0, diagnostic)

        self.native("checkpoint", "pack", source, "select")
        self.native("checkpoint", "pack-reclaim", source)
        # Replace the lossless pack as well as the physical transaction
        # prefix.  The clone must still recover the historical author verdict
        # and exact signed source from the surviving selected generation.
        self.native("checkpoint", "pack", source, "select")
        self.assertIn("retired pack-generations=1",
                      self.native("checkpoint", "pack-retire", source).stdout)
        target = self.base / "authored-clone"
        self.native("checkpoint", "clone", source, target)
        self.assertIn("articles=1",
                      self.native("store", target, "recover").stdout)

        target_control = self.base / "clone-control.sock"
        with socket.socket() as probe:
            probe.bind(("127.0.0.1", 0))
            target_port = probe.getsockname()[1]
        target_config = self.base / "clone.toml"
        target_config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\n[control]\npath = "{}"\n'.format(
                target, target_port, target_control), encoding="ascii")
        owner = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(target_config), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        try:
            wait_for_announcement(owner, b"LISTENING ")
            with socket.create_connection(("127.0.0.1", target_port),
                                          timeout=30) as sock:
                with sock.makefile("rwb", buffering=0) as stream:
                    self.assertTrue(stream.readline().startswith(b"200 "))
                    stream.write(("ARTICLE {}\r\n".format(msgid)).encode())
                    self.assertTrue(stream.readline().startswith(b"220 "))
                    received = bytearray()
                    while True:
                        line = stream.readline()
                        self.assertTrue(line, "cloned ARTICLE ended early")
                        if line == b".\r\n":
                            break
                        received.extend(line[1:] if line.startswith(b"..") else line)
                    self.assertIn(b"FN-Authorship: ", bytes(received)[:200])
                    self.assertTrue(bytes(received).endswith(article.read_bytes()))
                    carried = self.base / "clone-received.eml"
                    carried.write_bytes(bytes(received))
                    self.native("hybrid-verify-carrier", carried, ml_public)
                    stream.write(("HDR :fn-verified {}\r\n".format(msgid)).encode())
                    self.assertEqual(stream.readline(), b"225 headers follow\r\n")
                    self.assertEqual(stream.readline(),
                                     b"0 verified " + b"55" * 32 +
                                     b" keyring 1\r\n")
                    self.assertEqual(stream.readline(), b".\r\n")
        finally:
            diagnostic = stop_and_diagnostics(owner, timeout=60)
            self.assertEqual(owner.returncode, 0, diagnostic)

    def test_native_and_python_frames_cross_open_byte_identically(self):
        source = self.initialized("source")
        native_store = self.base / "native"
        python_store = self.base / "python"
        shutil.copytree(source, native_store)
        shutil.copytree(source, python_store)

        published = self.native("checkpoint", "publish", native_store, "select")
        self.assertIn("published generation=0 records=1 selected=yes", published.stdout)
        py_status = self.python_checkpoint(native_store, "status")
        self.assertIn("checkpoint=ok generation=0 suffix-from=1 differential=equal",
                      py_status.stdout)
        py_recover = self.python_store(native_store, "recover")
        self.assertIn("transactions=1 articles=1", py_recover.stdout)

        self.python_checkpoint(python_store, "publish", "--select")
        native_status = self.native("checkpoint", "status", python_store)
        self.assertIn("generations=0 checkpoint=ok generation=0", native_status.stdout)
        self.assertEqual(
            (native_store / "checkpoints" / "generation-0.fncp").read_bytes(),
            (python_store / "checkpoints" / "generation-0.fncp").read_bytes())
        self.assertEqual(
            (native_store / "checkpoints" / "selected.fncp").read_bytes(),
            (python_store / "checkpoints" / "selected.fncp").read_bytes())

    def test_selected_corruption_is_reported_without_rollback_or_lost_replay(self):
        original = self.initialized("original")
        self.native("checkpoint", "publish", original, "select")
        generation = Path("checkpoints/generation-0.fncp")
        marker = Path("checkpoints/selected.fncp")
        cases = (
            ("marker-truncated", marker, lambda raw: raw[:-1]),
            ("generation-truncated", generation, lambda raw: raw[:-1]),
            ("generation-malformed", generation,
             lambda raw: b"BAD!" + raw[4:]),
        )
        for label, relative, damage in cases:
            with self.subTest(label=label):
                store = self.base / label
                shutil.copytree(original, store)
                path = store / relative
                path.write_bytes(damage(path.read_bytes()))
                status = self.native("checkpoint", "status", store,
                                     expected=run_store.EXIT_FAULT)
                self.assertIn("checkpoint=corrupt", status.stdout)
                recovered = self.native("store", store, "recover",
                                        expected=run_store.EXIT_FAULT)
                self.assertIn("transactions=1 articles=1", recovered.stdout)
                self.assertIn("checkpoint=corrupt", recovered.stdout)

        missing = self.base / "generation-missing"
        shutil.copytree(original, missing)
        (missing / generation).unlink()
        status = self.native("checkpoint", "status", missing,
                             expected=run_store.EXIT_FAULT)
        self.assertIn("selected generation 0 is missing", status.stdout)

    def test_corrupt_unselected_generation_is_invisible(self):
        store = self.initialized("unselected")
        self.native("checkpoint", "publish", store, "select")
        self.native("checkpoint", "publish", store)
        second = store / "checkpoints" / "generation-1.fncp"
        second.write_bytes(b"unselected garbage")
        status = self.native("checkpoint", "status", store)
        self.assertIn("generations=0 1 checkpoint=ok generation=0", status.stdout)

    def test_acl2_namespace_codec_rejects_alias_overflow_and_excess(self):
        original = self.initialized("namespace", article=False)
        self.native("checkpoint", "publish", original)
        generation = original / "checkpoints" / "generation-0.fncp"
        for label, alias in (("leading-zero", "generation-00.fncp"),
                             ("overflow", "generation-4294967296.fncp")):
            with self.subTest(label=label):
                store = self.base / label
                shutil.copytree(original, store)
                shutil.copy2(generation, store / "checkpoints" / alias)
                result = self.native("checkpoint", "status", store,
                                     expected=run_store.EXIT_FAULT)
                self.assertIn("ACL2 rejected checkpoint namespace", result.stderr)

        excess = self.base / "namespace-excess"
        shutil.copytree(original, excess)
        directory = excess / "checkpoints"
        for index in range(4097):
            (directory / f"unexpected-{index}").touch()
        result = self.native("checkpoint", "status", excess,
                             expected=run_store.EXIT_FAULT)
        self.assertIn("checkpoint namespace exceeds ACL2 observation bound",
                      result.stderr)

    def test_differential_mismatch_is_always_corruption(self):
        store = self.initialized("mismatch")
        self.native("checkpoint", "publish", store, "select")
        env = dict(self.env)
        env["FN_CHECKPOINT_DIFFERENTIAL"] = "0"
        env["FN_CHECKPOINT_TEST_MISMATCH"] = "1"
        status = self.native("checkpoint", "status", store,
                             expected=run_store.EXIT_FAULT, env=env)
        self.assertIn("checkpoint=corrupt", status.stdout)
        self.assertIn("differs from full replay", status.stdout)
        recovered = self.native("store", store, "recover",
                                expected=run_store.EXIT_FAULT, env=env)
        self.assertIn("transactions=1 articles=1", recovered.stdout)
        self.assertIn("checkpoint=corrupt", recovered.stdout)

    def test_known_and_ambiguous_failures_keep_distinct_exit_codes(self):
        refused_store = self.initialized("candidate-refused", article=False)
        refused_env = dict(self.env)
        refused_env["FN_IMMUTABLE_PUBLISH_TEST_FAIL"] = "file-barrier"
        refused = self.native("checkpoint", "publish", refused_store,
                              expected=run_store.EXIT_REFUSED, env=refused_env)
        self.assertIn("publication refused", refused.stderr)
        self.assertEqual(list((refused_store / "checkpoints").glob("generation-*")), [])

        uncertain_store = self.initialized("candidate-uncertain", article=False)
        uncertain_env = dict(self.env)
        uncertain_env["FN_IMMUTABLE_PUBLISH_TEST_FAIL"] = "namespace"
        uncertain = self.native("checkpoint", "publish", uncertain_store,
                                expected=run_store.EXIT_UNCERTAIN, env=uncertain_env)
        self.assertIn("publication is uncertain", uncertain.stderr)
        self.assertTrue((uncertain_store / "checkpoints" / "generation-0.fncp").is_file())

        marker_store = self.initialized("marker", article=False)
        self.native("checkpoint", "publish", marker_store)
        marker_refused_env = dict(self.env)
        marker_refused_env["FN_CHECKPOINT_TEST_FAIL"] = "selection-file"
        self.native("checkpoint", "select", marker_store, "0",
                    expected=run_store.EXIT_REFUSED, env=marker_refused_env)
        self.assertFalse((marker_store / "checkpoints" / "selected.fncp").exists())

        marker_uncertain_env = dict(self.env)
        marker_uncertain_env["FN_CHECKPOINT_TEST_FAIL"] = "selection-directory"
        self.native("checkpoint", "select", marker_store, "0",
                    expected=run_store.EXIT_UNCERTAIN, env=marker_uncertain_env)
        reopened = self.native("checkpoint", "status", marker_store)
        self.assertIn("checkpoint=ok generation=0", reopened.stdout)

    def transaction_bytes(self, store):
        return {path.name: path.read_bytes()
                for path in sorted((store / "transactions").glob("*.txn"))}

    def stopped_then_killed(self, args, point, occurrence=1):
        env = dict(self.env)
        env["FN_CHECKPOINT_TEST_STOP"] = point
        env["FN_CHECKPOINT_TEST_STOP_AFTER"] = str(occurrence)
        process = subprocess.Popen(
            [str(IMAGE), "--fn", *map(str, args)], cwd=ROOT, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 10
            while time.monotonic() < deadline:
                if process.poll() is not None:
                    stdout, stderr = process.communicate()
                    self.fail(f"process exited before {point}: {stdout} {stderr}")
                state = subprocess.run(
                    ["ps", "-o", "state=", "-p", str(process.pid)],
                    stdout=subprocess.PIPE, text=True, check=False).stdout.strip()
                if state.startswith("T"):
                    break
                time.sleep(0.02)
            else:
                self.fail(f"process did not stop at {point}")
            os.kill(process.pid, signal.SIGKILL)
        finally:
            if process.poll() is None:
                process.kill()
            # Reap the process and close both pipes.  wait() alone leaves the
            # Popen-owned file objects open and obscures real warning output.
            process.communicate(timeout=5)

    def test_process_death_at_every_native_checkpoint_cut_reopens(self):
        candidate_expectations = {
            "candidate-file": "generations=- checkpoint=none",
            "candidate-link": "generations=0 checkpoint=none",
            "candidate-directory": "generations=0 checkpoint=none",
        }
        for point, expected in candidate_expectations.items():
            with self.subTest(point=point):
                store = self.initialized(point)
                before = self.transaction_bytes(store)
                self.stopped_then_killed(("checkpoint", "publish", store), point)
                status = self.native("checkpoint", "status", store)
                self.assertIn(expected, status.stdout)
                recovered = self.native("store", store, "recover")
                self.assertIn("transactions=1 articles=1", recovered.stdout)
                self.assertEqual(self.transaction_bytes(store), before)

    def test_process_death_at_every_selection_cut_preserves_event_bytes(self):
        selection_expectations = {
            "selection-file": "checkpoint=none",
            "selection-replace": "checkpoint=ok generation=0",
            "selection-directory": "checkpoint=ok generation=0",
        }
        for point, expected in selection_expectations.items():
            with self.subTest(point=point):
                store = self.initialized(point)
                self.native("checkpoint", "publish", store)
                before = self.transaction_bytes(store)
                self.stopped_then_killed(("checkpoint", "select", store, "0"), point)
                status = self.native("checkpoint", "status", store)
                self.assertIn(expected, status.stdout)
                recovered = self.native("store", store, "recover")
                self.assertIn("transactions=1 articles=1", recovered.stdout)
                self.assertEqual(self.transaction_bytes(store), before)

    def test_selected_lossless_pack_splices_before_generic_replay(self):
        store = self.initialized("pack")
        packed = self.native("checkpoint", "pack", store, "select")
        self.assertIn("packed generation=0 records=1 selected=yes", packed.stdout)
        recovered = self.native("store", store, "recover")
        self.assertIn("transactions=1 articles=1", recovered.stdout)

    def test_retiring_old_pack_generations_keeps_exact_retained_sources(self):
        store = self.initialized("pack-retire")
        before_first = self.native("store", store, "inspect",
                                   "<checkpoint@example.invalid>").stdout
        self.native("checkpoint", "pack", store, "select")
        older = store / "packs" / "generation-0.fncp"
        old_bytes = older.stat().st_size
        self.native("store", store, "post", "<retired-pack-suffix@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        before_second = self.native("store", store, "inspect",
                                    "<retired-pack-suffix@example.invalid>").stdout
        before_retention = self.native("store", store, "retention").stdout
        self.native("checkpoint", "pack", store, "select")
        selected = store / "packs" / "generation-1.fncp"
        selected_bytes = selected.read_bytes()
        before_total = sum(p.stat().st_size for p in
                           (store / "packs").glob("generation-*.fncp"))

        retired = self.native("checkpoint", "pack-retire", store)
        self.assertIn("retired pack-generations=1", retired.stdout)
        self.assertFalse(older.exists())
        self.assertEqual(selected.read_bytes(), selected_bytes)
        self.assertEqual(sum(p.stat().st_size for p in
                             (store / "packs").glob("generation-*.fncp")),
                         before_total - old_bytes)
        self.assertIn("transactions=2 articles=2",
                      self.native("store", store, "recover").stdout)
        self.assertEqual(self.native("store", store, "inspect",
                                     "<checkpoint@example.invalid>").stdout,
                         before_first)
        self.assertEqual(self.native("store", store, "inspect",
                                     "<retired-pack-suffix@example.invalid>").stdout,
                         before_second)
        self.assertEqual(self.native("store", store, "retention").stdout,
                         before_retention)
        # With no older generation, the command has no directory barrier or
        # process-death cut; a selected stop hook must never be reached.
        no_op_env = dict(self.env)
        no_op_env["FN_CHECKPOINT_TEST_STOP"] = "pack-retire-directory"
        self.assertIn("retired pack-generations=0",
                      self.native("checkpoint", "pack-retire", store,
                                  env=no_op_env).stdout)
        # A later publication must advance to generation 2, never reuse 0.
        self.assertIn("generation=2",
                      self.native("checkpoint", "pack", store).stdout)

    def test_pack_generation_retirement_death_reopens_and_retries(self):
        for point, occurrence in (("pack-retire-unlink", 1),
                                  ("pack-retire-unlink", 2),
                                  ("pack-retire-directory", 1)):
            with self.subTest(point=point, occurrence=occurrence):
                store = self.initialized(f"{point}-{occurrence}")
                self.native("checkpoint", "pack", store, "select")
                self.native("checkpoint", "pack", store, "select")
                self.native("checkpoint", "pack", store, "select")
                selected = store / "packs" / "generation-2.fncp"
                selected_bytes = selected.read_bytes()
                before_source = self.native("store", store, "inspect",
                                            "<checkpoint@example.invalid>").stdout
                self.stopped_then_killed(("checkpoint", "pack-retire", store),
                                         point, occurrence=occurrence)
                self.assertEqual(selected.read_bytes(), selected_bytes)
                self.assertIn("transactions=1 articles=1",
                              self.native("store", store, "recover").stdout)
                self.assertEqual(self.native("store", store, "inspect",
                                             "<checkpoint@example.invalid>").stdout,
                                 before_source)
                self.native("checkpoint", "pack-retire", store)
                self.assertFalse((store / "packs" / "generation-0.fncp").exists())
                self.assertFalse((store / "packs" / "generation-1.fncp").exists())
                self.assertEqual(selected.read_bytes(), selected_bytes)

    def test_selected_pack_missing_or_corrupt_fails_closed(self):
        for mode in ("missing", "corrupt"):
            with self.subTest(mode=mode):
                store = self.initialized("pack-" + mode)
                self.native("checkpoint", "pack", store, "select")
                generation = store / "packs" / "generation-0.fncp"
                if mode == "missing":
                    generation.unlink()
                else:
                    raw = bytearray(generation.read_bytes())
                    raw[len(raw) // 2] ^= 1
                    generation.write_bytes(raw)
                refused = self.native("store", store, "recover",
                                      expected=run_store.EXIT_FAULT)
                self.assertNotIn("articles=", refused.stdout)

    def test_surviving_covered_transaction_conflict_fails_closed(self):
        store = self.initialized("pack-conflict")
        other = self.initialized("pack-conflict-other", article=False)
        self.native("store", other, "post", "<other@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        self.native("checkpoint", "pack", store, "select")
        source = other / "transactions" / "00000000000000000000.txn"
        target = store / "transactions" / "00000000000000000000.txn"
        target.write_bytes(source.read_bytes())
        refused = self.native("store", store, "recover",
                              expected=run_store.EXIT_FAULT)
        self.assertNotIn("articles=", refused.stdout)

    def test_selected_pack_reclaims_physical_prefix_and_replays_suffix(self):
        store = self.initialized("pack-reclaim")
        self.native("checkpoint", "pack", store, "select")
        self.native("store", store, "post", "<suffix@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        reclaimed = self.native("checkpoint", "pack-reclaim", store)
        self.assertIn("reclaimed transaction-prefix=1", reclaimed.stdout)
        self.assertEqual([p.name for p in (store / "transactions").iterdir()],
                         ["00000000000000000001.txn"])
        recovered = self.native("store", store, "recover")
        self.assertIn("transactions=2 articles=2", recovered.stdout)

    def test_active_reader_blocks_pack_reclaim_and_reopen_keeps_archive_pin(self):
        store = self.initialized("pack-active-reader", article=False)
        msgid = "<pack-active-reader@example.invalid>"
        article = self.base / "active-reader.eml"
        article.write_bytes(
            b"From: author@example.invalid\r\n"
            b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
            b"Newsgroups: fn.letters\r\n"
            b"Subject: pinned before reclaim\r\n"
            b"Message-ID: " + msgid.encode("ascii") +
            b"\r\n\r\naccepted source survives reclaim\r\n")
        control = self.base / "active-reader-control.sock"
        with socket.socket() as probe:
            probe.bind(("127.0.0.1", 0))
            port = probe.getsockname()[1]
        config = self.base / "active-reader.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\n[control]\npath = "{}"\n'.format(store, port, control),
            encoding="ascii")

        def start_owner():
            process = subprocess.Popen(
                [str(IMAGE), "--fn", "operator", str(config), "run"],
                cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE)
            wait_for_announcement(process, b"LISTENING ")
            return process

        owner = start_owner()
        try:
            posted = self.native("operator", config, "post", "--message-id",
                                 msgid, "--payload", article, "--group",
                                 "fn.letters")
            self.assertIn("accepted operator post", posted.stderr)
        finally:
            diagnostic = stop_and_diagnostics(owner, timeout=60)
            self.assertEqual(owner.returncode, 0, diagnostic)

        def inspect_source():
            result = subprocess.run(
                [str(IMAGE), "--fn", "store", str(store), "inspect", msgid],
                cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, timeout=30, check=False)
            self.assertEqual(result.returncode, 0, result.stderr.decode())
            return result.stdout

        before_source = inspect_source()
        self.assertTrue(before_source.endswith(article.read_bytes()))
        before_retention = self.native("store", store, "retention").stdout
        self.assertRegex(before_retention, r"^pins=1 reserved=[1-9][0-9]*\n$")
        self.native("checkpoint", "pack", store, "select")
        before_transactions = self.transaction_bytes(store)
        selected_pack = store / "packs" / "generation-0.fncp"
        before_pack = selected_pack.read_bytes()

        owner = start_owner()
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=30) as sock:
                sock.settimeout(10)
                with sock.makefile("rwb", buffering=0) as stream:
                    self.assertTrue(stream.readline().startswith(b"200 "))

                    def read_pinned_article():
                        stream.write(("ARTICLE {}\r\n".format(msgid)).encode("ascii"))
                        self.assertTrue(stream.readline().startswith(b"220 "))
                        received = bytearray()
                        while True:
                            line = stream.readline()
                            self.assertTrue(line, "pinned ARTICLE ended early")
                            if line == b".\r\n":
                                break
                            received.extend(line[1:] if line.startswith(b"..") else line)
                        return bytes(received)

                    first_read = read_pinned_article()
                    self.assertTrue(first_read.endswith(article.read_bytes()))
                    # The operator holds the exclusive Store lock for the
                    # lifetime of this pinned connection. Reclaim must refuse
                    # before any unlink, with a definite refusal exit.
                    refused = self.native("checkpoint", "pack-reclaim", store,
                                          expected=run_store.EXIT_REFUSED)
                    self.assertIn("store is already locked", refused.stderr)
                    retire_refused = self.native("checkpoint", "pack-retire", store,
                                                 expected=run_store.EXIT_REFUSED)
                    self.assertIn("store is already locked", retire_refused.stderr)
                    self.assertEqual(self.transaction_bytes(store), before_transactions)
                    self.assertEqual(selected_pack.read_bytes(), before_pack)
                    self.assertEqual(read_pinned_article(), first_read)
        finally:
            diagnostic = stop_and_diagnostics(owner, timeout=60)
            self.assertEqual(owner.returncode, 0, diagnostic)

        reclaimed = self.native("checkpoint", "pack-reclaim", store)
        self.assertIn("reclaimed transaction-prefix=1", reclaimed.stdout)
        self.assertEqual(self.transaction_bytes(store), {})
        self.assertEqual(selected_pack.read_bytes(), before_pack)
        self.assertIn("transactions=1 articles=1",
                      self.native("store", store, "recover").stdout)
        self.assertEqual(inspect_source(), before_source)
        self.assertEqual(self.native("store", store, "retention").stdout,
                         before_retention)

    def test_pack_prefix_reclaim_process_death_recovers_from_selected_pack(self):
        for point in ("pack-reclaim-unlink", "pack-reclaim-directory"):
            with self.subTest(point=point):
                store = self.initialized(point)
                self.native("checkpoint", "pack", store, "select")
                before = self.transaction_bytes(store)
                self.stopped_then_killed(("checkpoint", "pack-reclaim", store), point)
                recovered = self.native("store", store, "recover")
                self.assertIn("transactions=1 articles=1", recovered.stdout)
                # Recovery observes the selected packed bytes; any transaction
                # file that survived the cut remains byte-identical.
                after = self.transaction_bytes(store)
                self.assertEqual(after, {name: before[name] for name in after})

    def test_partial_multi_file_prefix_reclaim_resumes_from_selected_pack(self):
        store = self.initialized("pack-partial")
        self.native("store", store, "post", "<prefix-two@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        self.native("checkpoint", "pack", store, "select")
        self.native("store", store, "post", "<suffix-three@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        before = self.transaction_bytes(store)
        suffix_name = "00000000000000000002.txn"
        self.stopped_then_killed(("checkpoint", "pack-reclaim", store),
                                 "pack-reclaim-unlink")
        recovered = self.native("store", store, "recover")
        self.assertIn("transactions=3 articles=3", recovered.stdout)
        self.native("checkpoint", "pack-reclaim", store)
        self.assertEqual(sorted((store / "transactions").glob("*.txn")),
                         [store / "transactions" / "00000000000000000002.txn"])
        self.assertEqual((store / "transactions" / suffix_name).read_bytes(),
                         before[suffix_name])

    def test_death_after_each_covered_unlink_preserves_exact_suffix_and_resumes(self):
        for occurrence in range(1, 5):
            with self.subTest(occurrence=occurrence):
                store = self.initialized(f"pack-unlink-{occurrence}")
                for number in range(1, 4):
                    self.native("store", store, "post",
                                f"<covered-{number}@example.invalid>",
                                self.payload, "-", "-", "fn.letters")
                self.native("checkpoint", "pack", store, "select")
                self.native("store", store, "post", "<retained@example.invalid>",
                            self.payload, "-", "-", "fn.letters")
                before = self.transaction_bytes(store)
                suffix_name = "00000000000000000004.txn"

                self.stopped_then_killed(
                    ("checkpoint", "pack-reclaim", store),
                    "pack-reclaim-unlink", occurrence=occurrence)
                recovered = self.native("store", store, "recover")
                self.assertIn("transactions=5 articles=5", recovered.stdout)
                self.assertEqual((store / "transactions" / suffix_name).read_bytes(),
                                 before[suffix_name])

                # Retry removes exactly the remaining covered prefix and does
                # not expire or rewrite the retained suffix event.
                self.native("checkpoint", "pack-reclaim", store)
                self.assertEqual(self.transaction_bytes(store),
                                 {suffix_name: before[suffix_name]})

    def test_missing_retained_suffix_gap_fails_closed_without_reclamation(self):
        store = self.initialized("pack-suffix-gap")
        self.native("checkpoint", "pack", store, "select")
        self.native("store", store, "post", "<suffix-one@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        self.native("store", store, "post", "<suffix-two@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        transactions = store / "transactions"
        (transactions / "00000000000000000001.txn").unlink()
        before = self.transaction_bytes(store)

        refused = self.native("store", store, "recover",
                              expected=run_store.EXIT_FAULT)
        self.assertNotIn("articles=", refused.stdout)
        self.assertEqual(self.transaction_bytes(store), before)
        reclaim = self.native("checkpoint", "pack-reclaim", store,
                              expected=run_store.EXIT_FAULT)
        self.assertNotEqual(reclaim.returncode, 0)
        self.assertEqual(self.transaction_bytes(store), before)

    def test_arbitrary_covered_deletion_image_recovers_and_resumes(self):
        store = self.initialized("pack-subset")
        for number in range(1, 4):
            self.native("store", store, "post",
                        f"<prefix-{number}@example.invalid>",
                        self.payload, "-", "-", "fn.letters")
        self.native("checkpoint", "pack", store, "select")
        self.native("store", store, "post", "<suffix-4@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        before = self.transaction_bytes(store)

        # A process-death image may contain any subset of already-issued
        # covered unlinks.  Keep covered 1 and 3, remove covered 0 and 2, and
        # retain the complete suffix at 4.
        for sequence in (0, 2):
            (store / "transactions" /
             f"{sequence:020d}.txn").unlink()
        recovered = self.native("store", store, "recover")
        self.assertIn("transactions=5 articles=5", recovered.stdout)
        for name, raw in self.transaction_bytes(store).items():
            self.assertEqual(raw, before[name])
        self.native("checkpoint", "pack-reclaim", store)
        suffix_name = "00000000000000000004.txn"
        self.assertEqual(self.transaction_bytes(store),
                         {suffix_name: before[suffix_name]})

    # -- M5 compaction: the served view across a reclaim -------------------

    def owner_config(self, store, name):
        control = self.base / (name + "-control.sock")
        with socket.socket() as probe:
            probe.bind(("127.0.0.1", 0))
            port = probe.getsockname()[1]
        config = self.base / (name + ".toml")
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\n[control]\npath = "{}"\n'.format(store, port, control),
            encoding="ascii")
        return config, port

    def run_owner(self, config):
        process = subprocess.Popen(
            [str(self.image), "--fn", "operator", str(config), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        wait_for_announcement(process, b"LISTENING ")
        return process

    def stop_owner(self, process):
        diagnostic = stop_and_diagnostics(process, timeout=60)
        self.assertEqual(process.returncode, 0, diagnostic)

    def operator_post(self, config, msgid, subject):
        article = self.base / ("post-" + subject + ".eml")
        article.write_bytes(
            b"From: author@example.invalid\r\n"
            b"Date: Thu, 24 Sep 2026 12:00:00 +0000\r\n"
            b"Newsgroups: fn.letters\r\n"
            b"Subject: " + subject.encode("ascii") + b"\r\n"
            b"Message-ID: " + msgid.encode("ascii") +
            b"\r\n\r\nbody of " + subject.encode("ascii") + b"\r\n")
        posted = self.native("operator", config, "post", "--message-id", msgid,
                             "--payload", article, "--group", "fn.letters")
        self.assertIn("accepted operator post", posted.stderr)

    def served_view(self, config, port, msgids):
        """GROUP, every ARTICLE by number and by Message-ID, HDR Subject."""
        owner = self.run_owner(config)
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=30) as sock:
                sock.settimeout(10)
                with sock.makefile("rwb", buffering=0) as stream:
                    self.assertTrue(stream.readline().startswith(b"200 "))

                    def command(line):
                        stream.write(line.encode("ascii") + b"\r\n")
                        return stream.readline()

                    def block():
                        lines = []
                        while True:
                            line = stream.readline()
                            self.assertTrue(line, "multi-line response ended early")
                            if line == b".\r\n":
                                return b"".join(lines)
                            lines.append(line)

                    group = command("GROUP fn.letters")
                    self.assertTrue(group.startswith(b"211 "), group)
                    _, count, low, high = (int(x) for x in group.split()[:4])
                    view = {"group": group}
                    for number in range(low, high + 1):
                        status = command("ARTICLE {}".format(number))
                        self.assertTrue(status.startswith(b"220 "), status)
                        view[number] = (status, block())
                    for msgid in msgids:
                        status = command("ARTICLE {}".format(msgid))
                        self.assertTrue(status.startswith(b"220 "), status)
                        view[msgid] = (status, block())
                    status = command("HDR Subject {}-{}".format(low, high))
                    self.assertTrue(status.startswith(b"225 "), status)
                    view["hdr"] = block()
                    command("QUIT")
        finally:
            self.stop_owner(owner)
        return view

    def compaction_fixture(self, name, covered=4, suffix=2):
        store = self.initialized(name, article=False)
        config, port = self.owner_config(store, name)
        msgids = []
        owner = self.run_owner(config)
        try:
            for number in range(covered):
                msgids.append("<{}-c{}@example.invalid>".format(name, number))
                self.operator_post(config, msgids[-1], "{}-c{}".format(name, number))
        finally:
            self.stop_owner(owner)
        packed = self.native("checkpoint", "pack", store, "select")
        self.assertIn("selected=yes", packed.stdout)
        self.covered_names = set(self.transaction_bytes(store))
        owner = self.run_owner(config)
        try:
            for number in range(suffix):
                msgids.append("<{}-s{}@example.invalid>".format(name, number))
                self.operator_post(config, msgids[-1], "{}-s{}".format(name, number))
        finally:
            self.stop_owner(owner)
        return store, config, port, msgids

    def assert_view_kept_and_next_number(self, store, config, port, msgids,
                                         before, before_retention, name):
        after = self.served_view(config, port, msgids)
        self.assertEqual(after, before)
        self.assertEqual(self.native("store", store, "retention").stdout,
                         before_retention)
        high = int(before["group"].split()[3])
        owner = self.run_owner(config)
        try:
            self.operator_post(config, "<{}-next@example.invalid>".format(name),
                               name + "-next")
        finally:
            self.stop_owner(owner)
        grown = self.served_view(config, port,
                                 msgids + ["<{}-next@example.invalid>".format(name)])
        self.assertEqual(int(grown["group"].split()[3]), high + 1)
        self.assertIn(b"<" + name.encode("ascii") + b"-next@example.invalid>",
                      grown[high + 1][1])
        for key, value in before.items():
            if key not in ("group", "hdr"):
                self.assertEqual(grown[key], value)

    def test_reclaim_keeps_served_view_watermarks_and_next_number(self):
        name = "reclaim-view"
        store, config, port, msgids = self.compaction_fixture(name)
        before = self.served_view(config, port, msgids)
        self.assertEqual(int(before["group"].split()[1]), 6)
        before_retention = self.native("store", store, "retention").stdout
        suffix = {n: raw for n, raw in self.transaction_bytes(store).items()
                  if n not in self.covered_names}
        self.assertTrue(suffix)
        reclaimed = self.native("checkpoint", "pack-reclaim", store)
        self.assertIn("reclaimed transaction-prefix=", reclaimed.stdout)
        self.assertIn("reclaimed transaction-prefix={}".format(
            len(self.covered_names)), reclaimed.stdout)
        self.assertEqual(self.transaction_bytes(store), suffix)
        self.assert_view_kept_and_next_number(store, config, port, msgids,
                                              before, before_retention, name)

    def test_reclaim_cuts_keep_served_view_and_next_number(self):
        # Every reclaim cut of fn-bs-pack-reclaim-steps: each covered unlink
        # (by occurrence) and the closing directory barrier.
        self.compaction_fixture("reclaim-count")
        covered = len(self.covered_names)
        self.assertGreater(covered, 1)
        cuts = [("pack-reclaim-unlink", k) for k in range(1, covered + 1)]
        cuts.append(("pack-reclaim-directory", 1))
        for point, occurrence in cuts:
            with self.subTest(point=point, occurrence=occurrence):
                name = "cut-{}-{}".format(point.split("-")[-1], occurrence)
                store, config, port, msgids = self.compaction_fixture(name)
                before = self.served_view(config, port, msgids)
                before_retention = self.native("store", store, "retention").stdout
                suffix = {n: raw for n, raw in self.transaction_bytes(store).items()
                          if n not in self.covered_names}
                self.stopped_then_killed(("checkpoint", "pack-reclaim", store),
                                         point, occurrence=occurrence)
                after_cut = self.transaction_bytes(store)
                # Old-or-new per covered name, the suffix byte for byte.
                self.assertEqual({n: after_cut[n] for n in suffix}, suffix)
                self.assertTrue(set(after_cut) - set(suffix) <= self.covered_names)
                self.assert_view_kept_and_next_number(
                    store, config, port, msgids, before, before_retention, name)
                self.native("checkpoint", "pack-reclaim", store)


@unittest.skipUnless(PRODUCTION_IMAGE.is_file() and os.access(PRODUCTION_IMAGE, os.X_OK),
                     "build/fn-host (the production image) is required")
class NativeProductionCompactTests(unittest.TestCase):
    """`operator CONFIG store compact' on the production image (M5).

    The helpers are NativeCheckpointTests', run against the production image;
    no developer selector or developer verb is used here.
    """
    image = PRODUCTION_IMAGE
    setUp = NativeCheckpointTests.setUp
    tearDown = NativeCheckpointTests.tearDown
    native = NativeCheckpointTests.native
    owner_config = NativeCheckpointTests.owner_config
    run_owner = NativeCheckpointTests.run_owner
    stop_owner = NativeCheckpointTests.stop_owner
    operator_post = NativeCheckpointTests.operator_post
    served_view = NativeCheckpointTests.served_view
    transaction_bytes = NativeCheckpointTests.transaction_bytes
    assert_view_kept_and_next_number = NativeCheckpointTests.assert_view_kept_and_next_number

    def test_operator_compact_keeps_every_article_and_next_number(self):
        name = "prod-compact"
        store = self.base / name
        config, port = self.owner_config(store, name)
        init = self.native("operator", config, "init", "fn.letters")
        self.assertIn("accepted operator init", init.stderr)
        msgids = ["<{}-{}@example.invalid>".format(name, k) for k in range(5)]
        owner = self.run_owner(config)
        try:
            for k, msgid in enumerate(msgids):
                self.operator_post(config, msgid, "{}-{}".format(name, k))
            # Refused while an owner runs, and nothing changes.
            held = self.native("operator", config, "store", "compact", expected=1)
            self.assertIn("refused operator compact", held.stderr)
            self.assertIn("locked", held.stderr)
        finally:
            self.stop_owner(owner)
        files = self.transaction_bytes(store)
        self.assertGreaterEqual(len(files), 5)
        before = self.served_view(config, port, msgids)
        before_retention = self.native("store", store, "retention").stdout
        compacted = self.native("operator", config, "store", "compact")
        self.assertIn("compacted steps=pack,select,reclaim,retire records={} "
                      "generation=0 links=1 reclaimed={} retired=0".format(len(files), len(files)),
                      compacted.stdout)
        self.assertIn("accepted operator compact", compacted.stderr)
        self.assertEqual(self.transaction_bytes(store), {})
        self.assert_view_kept_and_next_number(store, config, port, msgids,
                                              before, before_retention, name)
        # The post after the first compaction is the new suffix: a second
        # compaction packs only that suffix into a second link of the chain
        # (P5), reclaims it and retires nothing: generation 0 is the chain's
        # first link.
        suffix = len(self.transaction_bytes(store))
        self.assertGreaterEqual(suffix, 1)
        again = self.native("operator", config, "store", "compact")
        self.assertIn("compacted steps=pack,select,reclaim,retire records={} "
                      "generation=1 links=1 reclaimed={} retired=0".format(len(files) + suffix, suffix),
                      again.stdout)
        self.assertEqual(self.transaction_bytes(store), {})
        refused = self.native("operator", config, "store", "compact", expected=1)
        self.assertIn("refused operator compact", refused.stderr)
        self.assertIn("already-compact", refused.stderr)
        usage = self.native("operator", config, "store", "compact", "now", expected=5)
        self.assertIn("usage operator store", usage.stderr)
        grown_ids = msgids + ["<{}-next@example.invalid>".format(name)]
        view = self.served_view(config, port, grown_ids)
        self.assertEqual(int(view["group"].split()[3]),
                         int(before["group"].split()[3]) + 1)
        for key, value in before.items():
            if key not in ("group", "hdr"):
                self.assertEqual(view[key], value)
        self.assert_view_kept_and_next_number(
            store, config, port, grown_ids, view,
            self.native("store", store, "retention").stdout, name + "-2")


if __name__ == "__main__":
    unittest.main()
