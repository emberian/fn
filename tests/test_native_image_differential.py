"""The stripped release image against its full reference twin (gpt-6's wave-5
review s.4; HST-025; lane image-floor-3).

host/native/build.lisp saves the production image twice from one certified
session: stripped (the release, build/fn-host, with the build-derived
dependency set build/fn-host.world-deps) and full (the reference,
build/fn-host-reference); the developer image likewise, full
(build/fn-host-developer) and stripped (build/fn-host-developer-stripped).
Each case below runs the same command on byte-identical inputs under the
full image and under the stripped one, and compares the OUTCOME (exit code,
stdout, stderr, NNTP replies; temporary paths and timings normalized) and
the DURABLE STATE (every file of the store after the case, by SHA-256;
where a case writes time- or randomness-dependent bytes the comparison falls
back to the file list and the store's own `status' report, and says so).

The stripped run is instrumented (tools/runtime_image/world-deps-check.lisp,
loaded into the core before ACL2 starts): every world read is classified
against the dependency set, and a read of a property the strip removed
(OMITTED) fails the module; reads of properties the full image never had
either (ABSENT) are recorded.  The mutation case removes one required
property the run read and shows the check catches it.

Cases: ordinary traffic (POST, ARTICLE, OVER, HDR, LIST); malformed input
(binary, an over-long line, an unknown command, a POST without Newsgroups,
a truncated command); a guard violation at the host boundary (developer
pair); a failed signature check (hybrid-verify-carrier on an altered
source); a missing runtime dependency (the ML-DSA-65 library absent);
a corrupt checkpoint; full replay (no checkpoint); init; export and import;
capacity refusal (an article over the profile's bound; an init the budget
cannot hold).  Named deferral: a failure during a protected stobj update
has no externally reachable trigger in the production verbs.

Needs FN_NATIVE_HOST, FN_NATIVE_REFERENCE_HOST, FN_NATIVE_DEVELOPER_HOST,
FN_NATIVE_DEVELOPER_STRIPPED_HOST (tools/hbox_native.sh --images
production,reference,developer,developer-stripped) and FN_TEST_OPENSSL
(ML-DSA-65 keys).  FN_DIFF_OUT, when set, receives the per-case outcome
table as JSON.
"""
import hashlib
import json
import os
import re
import shlex
import shutil
import socket
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from tests.native_harness import EXIT, free_port, native_image, start, stop_and_diagnostics

ROOT = Path(__file__).resolve().parent.parent
STRIPPED = str(native_image("FN_NATIVE_HOST"))
REFERENCE = str(native_image("FN_NATIVE_REFERENCE_HOST"))
DEVELOPER = str(native_image("FN_NATIVE_DEVELOPER_HOST"))
DEVELOPER_STRIPPED = str(native_image("FN_NATIVE_DEVELOPER_STRIPPED_HOST"))
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")
CHECK = ROOT / "tools" / "runtime_image" / "world-deps-check.lisp"
REPORT = {}


def ready(*images):
    return all(i and Path(i).is_file() and Path(i + ".core").is_file() for i in images)


def tree(root):
    """Every regular file under ROOT: relative path -> SHA-256."""
    found = {}
    root = Path(root)
    if not root.exists():
        return found
    for path in sorted(root.rglob("*")):
        if path.is_file() and not path.is_symlink():
            found[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return found


class Image:
    """One saved image, started the way its own script starts it, optionally
    with the world-deps check loaded first."""

    def __init__(self, path, checked, work):
        self.path, self.checked, self.work = path, checked, Path(work)
        text = Path(path).read_text()
        line = next(l for l in text.splitlines() if l.startswith("exec "))
        words = shlex.split(line.replace("${SBCL_USER_ARGS}", ""))[1:]
        self.runtime = words[:words.index("--end-runtime-options") + 1]
        home = re.search(r"SBCL_HOME='([^']*)'", text)
        self.home = home.group(1) if home else None
        self.deps = path + ".world-deps"
        self.out = self.work / ("world-reads-" + Path(path).name)

    def argv(self, args, runtime=None):
        top = ["--no-userinit"]
        if self.checked:
            top += ["--load", str(CHECK)]
        top += ["--eval", "(acl2::sbcl-restart)", "--disable-debugger",
                "--end-toplevel-options", "--fn"]
        return (self.runtime if runtime is None else runtime) + top + [str(a) for a in args]

    def launch_argv(self, args, env, timeout=300):
        words = [str(a) for a in args]
        if len(words) < 3 or words[0] != "operator" or words[2] != "run":
            return self.argv(words)
        # Match fn_decide_heap's boot heap and probe the same runtime words
        # for each image.  The saved exec line's heap is for offline commands.
        core_octets = Path(self.path + ".core").stat().st_size
        boot = (core_octets + 1048575) // 1048576 + 128
        env.pop("FN_LOG_EXTENT_CAP", None)
        probe = subprocess.run(
            [self.path, "--fn", "heap", "--", *words],
            env=dict(env, SBCL_USER_ARGS="--dynamic-space-size {}".format(boot)),
            cwd=self.work, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=timeout, check=False)
        out = probe.stdout.decode("utf-8", "replace")
        heap = re.search(r"^heap=(\d+) MB\b", out)
        stack = re.search(r"\bstack=(\d+) KB\b", out)
        if probe.returncode != 0 or not (heap and stack):
            raise AssertionError("{} heap probe exit={}: {}{}".format(
                self.path, probe.returncode, out, probe.stderr.decode("utf-8", "replace")))
        extent = re.search(r"\bextent=(\d+)\b", out)
        if extent:
            env["FN_LOG_EXTENT_CAP"] = extent.group(1)
        runtime = self.runtime[:-1] + [
            "--dynamic-space-size", heap.group(1),
            "--control-stack-size", stack.group(1) + "KB", self.runtime[-1]]
        return self.argv(words, runtime)

    def env(self, **extra):
        env = {k: v for k, v in os.environ.items()
               if not k.startswith(("FN_NATIVE_", "FN_WORLD_DEPS", "SBCL_"))}
        if self.home:
            env["SBCL_HOME"] = self.home
        if self.checked:
            env["FN_WORLD_DEPS"] = self.deps
            env["FN_WORLD_DEPS_OUT"] = str(self.out)
        env.update(extra)
        return env

    def run(self, args, timeout=300, **extra):
        env = self.env(**extra)
        return subprocess.run(self.launch_argv(args, env, timeout), env=env, cwd=self.work,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              timeout=timeout, check=False)

    def start(self, args, **extra):
        env = self.env(**extra)
        return start(self.launch_argv(args, env), env=env, cwd=self.work)

    def reads(self):
        """(kind, text) of every classified first read the check wrote."""
        lines = []
        for path in sorted(self.work.glob(self.out.name + ".*")):
            for line in path.read_text(errors="replace").splitlines():
                kind, _, rest = line.partition(" ")
                lines.append((kind, rest))
        return lines


class ImageLaunchTests(unittest.TestCase):
    """Launch plumbing with independent per-image probe answers; no native core."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="fn-diff-launch-")
        self.addCleanup(self.tmp.cleanup)
        self.work = Path(self.tmp.name)

    def image(self, name, checked):
        path = self.work / name
        path.write_text('exec /fake/sbcl --dynamic-space-size 1797 '
                        '--control-stack-size 1024KB --core fake.core '
                        '${SBCL_USER_ARGS} --end-runtime-options "$@"\n')
        Path(str(path) + ".core").write_bytes(b"core")
        return Image(str(path), checked, self.work)

    def test_each_served_start_uses_its_own_probe_and_runtime_words(self):
        words = ["operator", self.work / "node.toml", "run", "--once"]
        for name, checked, heap, stack in (("full", False, 25244, 1536),
                                           ("stripped", True, 24831, 2048)):
            with self.subTest(image=name):
                image = self.image(name, checked)
                probe = subprocess.CompletedProcess([], 0,
                    f"heap={heap} MB stack={stack} KB extent=4096\n".encode(), b"")
                with mock.patch.object(subprocess, "run", return_value=probe) as run_probe, \
                        mock.patch(__name__ + ".start") as start_owner:
                    image.start(words, FN_LOG_EXTENT_CAP="stale")
                argv, = start_owner.call_args.args
                self.assertEqual(run_probe.call_args.args[0],
                                 [image.path, "--fn", "heap", "--", *map(str, words)])
                self.assertEqual(run_probe.call_args.kwargs["env"]["SBCL_USER_ARGS"],
                                 "--dynamic-space-size 129")
                self.assertNotIn("FN_LOG_EXTENT_CAP", run_probe.call_args.kwargs["env"])
                self.assertEqual(argv[:len(image.runtime) + 4], image.runtime[:-1] + [
                    "--dynamic-space-size", str(heap), "--control-stack-size",
                    str(stack) + "KB", "--end-runtime-options"])
                self.assertEqual(argv[-len(words):], list(map(str, words)))
                self.assertEqual("--load" in argv, checked)
                self.assertEqual(start_owner.call_args.kwargs["env"]["FN_LOG_EXTENT_CAP"], "4096")

    def test_synchronous_served_run_probes_but_offline_keeps_saved_runtime(self):
        image = self.image("full", False)
        words = ["operator", "node.toml", "run"]
        probe = subprocess.CompletedProcess([], 0, b"heap=25244 MB stack=1536 KB\n", b"")
        result = subprocess.CompletedProcess([], 1, b"", b"reason=checkpoint-damaged")
        with mock.patch.object(subprocess, "run", side_effect=[probe, result]) as run:
            self.assertIs(image.run(words), result)
        self.assertIn("25244", run.call_args.args[0])
        offline = ["operator", "node.toml", "status"]
        with mock.patch.object(subprocess, "run", return_value=result) as run:
            image.run(offline)
        run.assert_called_once()
        self.assertEqual(run.call_args.args[0], image.argv(offline))

    def test_refused_or_incomplete_probe_never_starts_an_owner(self):
        image = self.image("full", False)
        for code, out in ((1, b"refused memory\n"), (0, b"heap=25244 MB\n")):
            with self.subTest(code=code, out=out), \
                    mock.patch.object(subprocess, "run", return_value=
                                      subprocess.CompletedProcess([], code, out, b"")), \
                    mock.patch(__name__ + ".start") as start_owner:
                with self.assertRaisesRegex(AssertionError, "heap probe"):
                    image.start(["operator", "node.toml", "run"])
                start_owner.assert_not_called()


def normalize(data, *roots):
    text = data.decode("utf-8", "replace")
    for root in roots:
        text = text.replace(str(root), "<T>")
    text = re.sub(r"\bpid[= ]\d+", "pid=<N>", text)
    # The run reserves its image content + LIMIT + pools (fn-mo-serve-decide);
    # offline commands retain their own sizing.  Image content is an input.
    text = re.sub(r"\bheap=\d+ MB", "heap=<core-dependent> MB", text)
    text = re.sub(r"\breservation=\d+ MB", "reservation=<core-dependent> MB", text)
    # Wall-clock readings: a file's modification time, an accept's time.
    text = re.sub(r"\bmodified=\d+", "modified=<clock>", text)
    text = re.sub(r"\btime=\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ", "time=<clock>", text)
    text = re.sub(r"\bms=\d+", "ms=<N>", text)
    text = re.sub(r"\b\d+(\.\d+)? ?(ms|s)\b", "<N>\\2", text)
    return text


def config(path, store, port, extra=""):
    path.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n{}'
                    .format(store, port, extra), encoding="ascii")
    return path


def article(n, octets=None, groups="local.test"):
    body = (octets if octets is not None else "body line {}\r\n".format(n))
    return ("From: author@example.invalid\r\nDate: Sat, 26 Sep 2026 12:00:00 +0000\r\n"
            "Newsgroups: {}\r\nSubject: differential {}\r\n"
            "Message-ID: <diff-{}@example.invalid>\r\n\r\n{}".format(groups, n, n, body))


class Session:
    def __init__(self, port):
        self.conn = socket.create_connection(("127.0.0.1", port), timeout=120)
        self.stream = self.conn.makefile("rwb")
        self.log = bytearray(self.stream.readline())

    def send(self, raw):
        self.stream.write(raw)
        self.stream.flush()
        self.log += b"C: " + raw[:200] + b"\n"

    def line(self):
        got = self.stream.readline()
        self.log += got
        return got

    def multiline(self):
        while True:
            got = self.line()
            if got in (b".\r\n", b""):
                return

    def command(self, text, multi=False):
        self.send(text.encode("ascii") + b"\r\n")
        first = self.line()
        if multi and first[:1] == b"2":
            self.multiline()
        return first

    def post(self, text):
        first = self.command("POST")
        if first.startswith(b"340"):
            self.send(text.encode("latin-1").replace(b"\r\n.", b"\r\n..") + b".\r\n")
            return self.line()
        return first

    def close(self):
        try:
            self.command("QUIT")
        except OSError:
            pass
        self.conn.close()
        return bytes(self.log)


@unittest.skipUnless(ready(STRIPPED, REFERENCE),
                     "set FN_NATIVE_HOST and FN_NATIVE_REFERENCE_HOST "
                     "(tools/hbox_native.sh --images production,reference)")
class ReleaseAgainstReferenceTests(unittest.TestCase):
    """Each case on byte-identical inputs: the reference (full) image and the
    release (stripped, checked) image; outcomes and durable state compared."""
    maxDiff = None

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="fn-diff-"))
        cls.full = Image(REFERENCE, False, cls.tmp)
        cls.stripped = Image(STRIPPED, True, cls.tmp)
        # The base store: made once by the reference image, 20 articles, a
        # published checkpoint; each case copies it.
        cls.base = cls.tmp / "base"
        port = free_port()
        cfg = config(cls.tmp / "base.toml", cls.base, port)
        made = cls.full.run(["operator", cfg, "init", "local.test", "local.other"])
        assert made.returncode == 0, made.stderr.decode()
        owner = cls.full.start(["operator", cfg, "run"])
        try:
            owner.announcement(b"LISTENING ")
            s = Session(port)
            for n in range(20):
                assert s.post(article(n)).startswith(b"240")
            s.close()
        finally:
            diagnostics = stop_and_diagnostics(owner, timeout=120)
        assert owner.returncode == 0, diagnostics
        # The same history with no checkpoint yet: `store checkpoint' below
        # rotates the log and drops the segments the checkpoint covers
        #, after which a store without its checkpoint is refused
        # by name (checkpoint-damaged), not replayed.  The full replay runs
        # on this copy (lane fitness, for release-machinery's native-rm1).
        cls.base_log = cls.tmp / "base-log"
        shutil.copytree(cls.base, cls.base_log, symlinks=True)
        published = cls.full.run(["operator", cfg, "store", "checkpoint"])
        assert published.returncode == 0, published.stderr.decode()

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, True)
        out = os.environ.get("FN_DIFF_OUT")
        if out:
            Path(out).write_text(json.dumps(REPORT, indent=1, sort_keys=True))

    def copy(self, name, base=None):
        """A byte-identical copy of the base store (or BASE) and its configuration."""
        store = self.tmp / name
        shutil.copytree(base or self.base, store, symlinks=True)
        port = free_port()
        return config(self.tmp / (name + ".toml"), store, port), store, port

    def pair(self, name, action, base=None):
        """ACTION(image, config, store, port) -> outcome, on a fresh copy of
        the base (or BASE) for each image; returns both outcomes and both trees."""
        results = {}
        for label, image in (("full", self.full), ("stripped", self.stripped)):
            cfg, store, port = self.copy("{}-{}".format(name, label), base)
            outcome = action(image, cfg, store, port)
            results[label] = (outcome, tree(store), store)
        return results

    def compare(self, name, results, durable="bytes", clocked=()):
        """CLOCKED: files the run writes from its own clock readings (the
        decision journal, books/owner-time-journal.lisp): compared by
        presence, every other file by bytes."""
        (a, ta, sa), (b, tb, sb) = results["full"], results["stripped"]
        for key in clocked:
            for t in (ta, tb):
                if key in t:
                    t[key] = "present"
        na = [normalize(x, sa, self.tmp) if isinstance(x, bytes) else x for x in a]
        nb = [normalize(x, sb, self.tmp) if isinstance(x, bytes) else x for x in b]
        row = {"outcome": na, "outcome-equal": na == nb}
        self.assertEqual(na, nb, name)
        if durable == "bytes":
            differing = sorted(k for k in set(ta) | set(tb) if ta.get(k) != tb.get(k))
            row["durable"] = ("bytes-equal" if not differing else "differs: " + " ".join(differing)) \
                + ("" if not clocked else " (clocked, by presence: " + " ".join(clocked) + ")")
            self.assertEqual(differing, [], name)
        else:
            row["durable"] = durable
            self.assertEqual(sorted(ta), sorted(tb), name + ": the stores' file lists")
        REPORT[name] = row

    def status(self, image, cfg, *options):
        got = image.run(["operator", cfg, "status", *options])
        return got.returncode, got.stdout, got.stderr

    # -- the cases ---------------------------------------------------------

    def test_ordinary_traffic(self):
        def act(image, cfg, store, port):
            owner = image.start(["operator", cfg, "run"])
            owner.announcement(b"LISTENING ")
            s = Session(port)
            for n in range(20, 25):
                s.post(article(n))
            s.command("GROUP local.test")
            s.command("OVER 1-25", multi=True)
            s.command("HDR Subject 1-25", multi=True)
            s.command("LIST ACTIVE", multi=True)
            s.command("LIST NEWSGROUPS", multi=True)
            for n in (0, 12, 24):
                s.command("ARTICLE <diff-{}@example.invalid>".format(n), multi=True)
            transcript = s.close()
            stop_and_diagnostics(owner, timeout=120)
            return [owner.returncode, transcript] + list(self.status(image, cfg))
        # The owner stamps what it accepts (Injection-Date and the like) at
        # the wall clock: bytes can differ, the file list and the report not.
        self.compare("ordinary-traffic", self.pair("ordinary", act),
                     durable="file list and status equal (accepts carry wall-clock stamps)")

    def test_malformed_input(self):
        def act(image, cfg, store, port):
            owner = image.start(["operator", cfg, "run"])
            owner.announcement(b"LISTENING ")
            s = Session(port)
            replies = []
            for raw in (b"\x00\xff\xfe junk\r\n", b"X" * 20000 + b"\r\n",
                        b"FROBNICATE\r\n", b"ARTICLE <absent@example.invalid>\r\n",
                        b"GROUP no.such.group\r\n", b"OVER 99999-1\r\n",
                        b"HDR\r\n", b"NEXT\r\n"):
                s.send(raw)
                replies.append(s.line())
            replies.append(s.post("From: a@example.invalid\r\nSubject: none\r\n"
                                  "Message-ID: <no-groups@example.invalid>\r\n\r\nx\r\n"))
            replies.append(s.post("garbage without headers\r\n"))
            transcript = s.close()
            stop_and_diagnostics(owner, timeout=120)
            return [owner.returncode, transcript, b"".join(replies)]
        self.compare("malformed-input", self.pair("malformed", act),
                     durable="file list equal (the owner's run writes its own records)")

    def test_capacity_refusal(self):
        def act(image, cfg, store, port):
            owner = image.start(["operator", cfg, "run"])
            owner.announcement(b"LISTENING ")
            s = Session(port)
            big = s.post(article(99, octets=("y" * 78 + "\r\n") * 30000))
            transcript = s.close()
            stop_and_diagnostics(owner, timeout=120)
            refused = image.run(["operator", cfg, "store", "import", self.tmp / "absent"])
            return [owner.returncode, big, transcript, refused.returncode,
                    refused.stdout, refused.stderr]
        self.compare("capacity-refusal", self.pair("capacity", act),
                     durable="file list equal")

    def test_init_budget_refusal_and_init(self):
        def act(image, cfg, store, port):
            fresh = Path(str(store) + "-fresh")
            fcfg = config(Path(str(store) + "-fresh.toml"), fresh, free_port())
            refused = image.run(["operator", fcfg, "init", "--budget", "1000",
                                 "--profile", "scale", "local.test"])
            # Capacity-free init selects a funded rung using this image's core
            # file and dynamic content (fn-pfd-init-decide -> fn-heap-init-decide).
            # Full and stripped cores are distinct physical inputs. Compare
            # identical explicit capacities, retaining their exact status/limits.
            made = image.run(["operator", fcfg, "init", "--budget", "4000",
                              "--profile", "development", "--max-transactions", "16384",
                              "--max-history-octets", "33554432", "local.test"])
            self.assertEqual(refused.returncode, EXIT.REFUSED, refused.stdout + refused.stderr)
            self.assertEqual(made.returncode, EXIT.OK, made.stdout + made.stderr)
            status = self.status(image, fcfg)
            self.assertEqual(status[0], EXIT.OK, status[1] + status[2])
            self.assertIn(b"max-transactions=16384 max-history-octets=33554432", status[1])
            files = sorted(tree(fresh))
            shutil.rmtree(fresh, True)
            return [refused.returncode, refused.stdout, refused.stderr,
                    made.returncode, made.stdout, made.stderr, status[0], status[1], files]
        self.compare("init", self.pair("init", act),
                     durable="the fresh stores' file lists and status equal (init draws node secrets)")

    def test_corrupt_checkpoint(self):
        def act(image, cfg, store, port):
            checkpoints = sorted(p for p in store.rglob("*") if p.is_file()
                                 and "checkpoint" in str(p.relative_to(store)))
            self.assertTrue(checkpoints, "the base store has a checkpoint file")
            victim = checkpoints[-1]
            data = bytearray(victim.read_bytes())
            data[len(data) // 2] ^= 0x40
            victim.write_bytes(bytes(data))
            status = self.status(image, cfg)
            owner = image.start(["operator", cfg, "run"])
            try:
                owner.announcement(b"LISTENING ", timeout=300)
                s = Session(port)
                s.command("ARTICLE <diff-7@example.invalid>", multi=True)
                transcript = s.close()
            except (AssertionError, OSError, subprocess.SubprocessError) as e:
                transcript = ("did not serve: " + type(e).__name__).encode()
            diag = stop_and_diagnostics(owner, timeout=120)
            return list(status) + [owner.returncode, transcript,
                                   normalize(diag.encode(), store, self.tmp)[-2000:]]
        self.compare("corrupt-checkpoint", self.pair("corrupt", act))

    def test_full_replay(self):
        """The whole log from segment 1, no checkpoint ever published."""
        def act(image, cfg, store, port):
            self.assertTrue((store / "journal" / "000001.log").is_file(),
                            "the uncompacted base keeps segment 1")
            self.assertFalse([p for p in store.rglob("*") if "checkpoint" in p.name],
                             "the uncompacted base has no checkpoint")
            status = self.status(image, cfg)
            owner = image.start(["operator", cfg, "run"])
            owner.announcement(b"LISTENING ", timeout=300)
            s = Session(port)
            s.command("GROUP local.test")
            s.command("OVER 1-20", multi=True)
            s.command("ARTICLE <diff-19@example.invalid>", multi=True)
            transcript = s.close()
            stop_and_diagnostics(owner, timeout=120)
            return list(status) + [owner.returncode, transcript]
        # The run appends its clock readings to the decision journal (lane
        # time-model-2): that file differs by the wall clock, never by image.
        self.compare("full-replay", self.pair("replay", act, base=self.base_log),
                     clocked=("decisions/decisions.fnj",))

    def test_checkpoint_deleted_after_compaction_is_refused_by_name(self):
        """An operator error: the checkpoint removed after `store checkpoint'
        dropped the segments it covers.  That is not a replay; both images
        refuse the open by name (books/store-log-segments.lisp
        :checkpoint-damaged) at `status' and at `run', and write nothing."""
        def act(image, cfg, store, port):
            self.assertFalse((store / "journal" / "000001.log").exists(),
                             "the checkpointed base dropped segment 1")
            for p in sorted(store.rglob("*"), reverse=True):
                if "checkpoint" in p.name and p.is_file():
                    p.unlink()
            before = tree(store)
            # `status --replay': the plain status reads the checkpoint
            # header alone (row S3), so the open's refusal is --replay's.
            status = self.status(image, cfg, "--replay")
            run = image.run(["operator", cfg, "run"], timeout=300)
            for code, err in ((status[0], status[2]), (run.returncode, run.stderr)):
                self.assertEqual(code, 1, err)
                self.assertIn(b"reason=checkpoint-damaged", err)
            self.assertEqual(tree(store), before, "a refused open wrote nothing")
            return list(status) + [run.returncode, run.stdout, run.stderr]
        self.compare("checkpoint-deleted-after-compaction", self.pair("dropped", act))

    def test_export_and_import(self):
        exported = self.tmp / "export"
        cfg, store, port = self.copy("export-source")
        done = self.full.run(["operator", cfg, "store", "export", exported])
        self.assertEqual(done.returncode, 0, done.stderr.decode())

        def act(image, cfg, store, port):
            target = Path(str(store) + "-imported")
            tcfg = config(Path(str(store) + "-imported.toml"), target, free_port())
            got = image.run(["operator", tcfg, "store", "import", exported])
            status = self.status(image, tcfg)
            files = sorted(tree(target))
            shutil.rmtree(target, True)
            return [got.returncode, got.stdout, got.stderr, status[0], status[1], files]
        self.compare("export-import", self.pair("import", act),
                     durable="the imported stores' file lists and status equal")

    def test_failed_signature_check(self):
        work = self.tmp / "sig"
        work.mkdir(exist_ok=True)
        principal, ed_public, ed_secret = (work / "p.bin", work / "edp.bin", work / "eds.bin")
        principal.write_bytes(bytes([85]) * 32)
        ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ml_private, ml_public = work / "ml.pem", work / "ml-pub.pem"
        made = subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out",
                               str(ml_private)], capture_output=True, timeout=60)
        if made.returncode != 0:
            # waiver-ok: capability -- FN_TEST_OPENSSL is the test tool OpenSSL
            # (3.5+ makes ML-DSA-65 keys); an older one is a tool this tree has
            # not built, and the signature case needs an independent key.
            self.skipTest("no ML-DSA-65 in FN_TEST_OPENSSL: " + made.stderr.decode()[-200:])
        subprocess.run([OPENSSL, "pkey", "-in", str(ml_private), "-pubout", "-out",
                        str(ml_public)], check=True, timeout=60)
        source, carried = work / "source.eml", work / "carried.eml"
        source.write_bytes(article(500).encode("ascii"))
        signed = self.full.run(["hybrid-sign-carrier", principal, ed_public, ed_secret,
                                ml_public, ml_private, source, carried])
        self.assertEqual(signed.returncode, 0, signed.stderr.decode())
        altered = work / "altered.eml"
        altered.write_bytes(carried.read_bytes().replace(b"body line 500", b"body line 501"))
        rows = {}
        for label, image in (("full", self.full), ("stripped", self.stripped)):
            ok = image.run(["hybrid-verify-carrier", carried, ml_public])
            bad = image.run(["hybrid-verify-carrier", altered, ml_public])
            rows[label] = ([ok.returncode, ok.stdout, ok.stderr,
                            bad.returncode, bad.stdout, bad.stderr], {}, work)
        self.assertEqual(rows["full"][0][3], EXIT.REFUSED, rows["full"][0][5])
        self.compare("failed-signature", rows)

    def test_missing_runtime_dependency(self):
        """The ML-DSA-65 library the image loads at start is not there."""
        rows = {}
        for label, image in (("full", self.full), ("stripped", self.stripped)):
            got = image.run(["hybrid-verify-carrier", self.tmp / "absent.eml",
                             self.tmp / "absent.pem"],
                            FN_MLDSA_LIBRARY=str(self.tmp / "lib" / "libfn-mldsa65.so"))
            rows[label] = ([got.returncode, got.stdout, got.stderr], {}, self.tmp)
        self.assertNotEqual(rows["full"][0][0], 0)
        self.compare("missing-runtime-dependency", rows)

    def test_zz_world_reads_stay_within_the_dependency_set(self):
        """Every stripped run above: no read of an omitted property."""
        reads = self.stripped.reads()
        kept = [r for k, r in reads if k == "KEPT"]
        absent = sorted({r for k, r in reads if k == "ABSENT"})
        omitted = sorted({r for k, r in reads if k == "OMITTED"})
        REPORT["world-reads"] = {"kept-pairs": len(set(kept)), "absent": absent,
                                 "omitted": omitted}
        print("NATIVE-DIFF world reads: kept pairs {}, absent {}, omitted {}".format(
            len(set(kept)), len(absent), len(omitted)))
        for row in absent + omitted:
            print("NATIVE-DIFF   " + row)
        self.assertGreater(len(kept), 0, "the check saw no reads: was it loaded?")
        self.assertEqual(omitted, [])
        # The prover state the strip replaced (lane image-strip): still
        # trapped at every stripped run's exit; nothing rebuilt it.
        # trapped at every stripped run's exit, nothing rebuilt it, and no
        # function that reads it was called.
        stripped = [r for k, r in reads if k == "STRIPPED"]
        rebuilt = sorted({r for k, r in reads if k == "REBUILT"})
        prover = sorted({r for k, r in reads if k == "PROVER-READ"})
        REPORT["prover-state"] = {"exits": len(stripped), "rebuilt": rebuilt,
                                  "prover-reads": prover}
        print("NATIVE-DIFF prover state: {} exits checked, rebuilt {}, prover reads {}".format(
            len(stripped), rebuilt, prover))
        self.assertGreater(len(stripped), 0, "no stripped run reported its prover state")
        self.assertTrue(all(r.endswith(" rebuilt=0") for r in stripped), stripped)
        self.assertEqual(rebuilt, [])
        self.assertEqual(prover, [])

    def test_zz_a_prover_read_of_stripped_state_fails_loudly(self):
        """The trace and trap witness (FN_WORLD_DEPS_USE, before start): a
        call of ens is traced as a PROVER-READ; a use of what it returns, or
        of a type-set table's value, from code compiled with safety fails
        with an error naming the stripped item."""
        for use, name in (("ens", "GLOBAL-ENABLED-STRUCTURE"),
                          ("type-set-table", "*TYPE-SET-BINARY-+-TABLE*")):
            probe = Image(STRIPPED, True, self.tmp / ("trap-" + use))
            probe.work.mkdir(exist_ok=True)
            got = probe.run(["--version"], FN_WORLD_DEPS_USE=use)
            reads = probe.reads()
            lines = [(k, r) for k, r in reads if k in ("TRAPPED", "UNTRAPPED")]
            if use == "ens":
                self.assertTrue(any(k == "PROVER-READ" and r.startswith("ENS ")
                                    for k, r in reads), reads)
            REPORT.setdefault("trap", {})[use] = {"exit": got.returncode, "lines": lines}
            print("NATIVE-DIFF trap {}: exit {} {}".format(use, got.returncode, lines))
            self.assertEqual(got.returncode, 72)
            self.assertEqual(len(lines), 1, lines)
            kind, text = lines[0]
            self.assertEqual(kind, "TRAPPED", lines)
            self.assertIn("FNN-STRIPPED :NAME " + name, text)

    def test_zz_the_check_catches_a_required_property_removed(self):
        """The mutation witness: remove one symbol-class the status verb reads
        (a required property) from the stripped image's world before start;
        the check reports it OMITTED."""
        cfg, store, port = self.copy("mutation")
        probe = Image(STRIPPED, True, self.tmp / "mutation-probe")
        probe.work.mkdir(exist_ok=True)
        self.assertEqual(probe.run(["operator", cfg, "status"]).returncode, 0)
        candidates = sorted(r for k, r in probe.reads()
                            if k == "KEPT" and r.endswith(" SYMBOL-CLASS")
                            and r.startswith("FN-"))
        self.assertTrue(candidates, "status read no fn symbol-class")
        drop = candidates[0]
        mutated = Image(STRIPPED, True, self.tmp / "mutation-run")
        mutated.work.mkdir(exist_ok=True)
        got = mutated.run(["operator", cfg, "status"], FN_WORLD_DEPS_DROP=drop)
        omitted = [r for k, r in mutated.reads() if k == "OMITTED"]
        REPORT["mutation"] = {"dropped": drop, "exit": got.returncode,
                              "omitted": omitted}
        print("NATIVE-DIFF mutation: dropped {} -> exit {}, omitted {}".format(
            drop, got.returncode, omitted))
        self.assertTrue(any(r.startswith(drop) for r in omitted), omitted)


@unittest.skipUnless(ready(DEVELOPER, DEVELOPER_STRIPPED),
                     "set FN_NATIVE_DEVELOPER_HOST and FN_NATIVE_DEVELOPER_STRIPPED_HOST "
                     "(tools/hbox_native.sh --images developer,developer-stripped)")
class GuardViolationTests(unittest.TestCase):
    """A guard violation at the host boundary: the developer verb
    `guard-probe' calls fn-b3-left-chunks on 42 and -1 through fnn-call."""
    maxDiff = None

    def test_the_same_refusal_full_and_stripped(self):
        tmp = Path(tempfile.mkdtemp(prefix="fn-diff-guard-"))
        self.addCleanup(shutil.rmtree, tmp, True)
        full = Image(DEVELOPER, False, tmp)
        stripped = Image(DEVELOPER_STRIPPED, True, tmp)
        a, b = full.run(["guard-probe"]), stripped.run(["guard-probe"])
        self.assertEqual(a.returncode, EXIT.FAULT, a.stderr.decode())
        self.assertEqual((a.returncode, a.stdout, a.stderr), (b.returncode, b.stdout, b.stderr))
        omitted = [r for k, r in stripped.reads() if k == "OMITTED"]
        REPORT["guard-violation"] = {"exit": a.returncode, "stderr": a.stderr.decode()[-300:],
                                     "outcome-equal": True, "omitted": omitted}
        self.assertEqual(omitted, [])


if __name__ == "__main__":
    unittest.main()
