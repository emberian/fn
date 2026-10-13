"""tools/test_budget.py: per-module wall time, and the three outcomes kept apart."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import test_budget  # noqa: E402


class NativeMemoryTests(unittest.TestCase):
    def test_literal_reader_never_imports_and_defaults_to_24g(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tests").mkdir()
            source = root / "tests/test_need.py"
            source.write_text('raise RuntimeError("must not import")\n')
            self.assertEqual(test_budget.native_memory("tests.test_need", root), "24G")
            source.write_text('NATIVE_MEMORY = "40G"\nraise RuntimeError("must not import")\n')
            self.assertEqual(test_budget.native_memory("tests.test_need", root), "40G")
            self.assertEqual(test_budget.native_memory("tests.test_need.SomeTests", root), "40G")
            for declaration in ('NATIVE_MEMORY = calculate()', 'NATIVE_MEMORY = "0G"',
                                'NATIVE_MEMORY = "48G; touch x"', 'NATIVE_MEMORY = 48',
                                'NATIVE_MEMORY = "2G"\nNATIVE_MEMORY = "48G"'):
                source.write_text(declaration)
                with self.assertRaises(ValueError):
                    test_budget.native_memory("tests.test_need", root)

    def test_sizes_and_bigmem_threshold_use_the_effective_unit(self):
        self.assertEqual(test_budget.memory_bytes("40960M"), 40 * 1024 ** 3)
        with mock.patch.object(test_budget, "native_memory", return_value="40G"):
            import contextlib
            import io
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                test_budget.memory_plan(["tests.test_need FN_X=1\n"], "2G")
            self.assertEqual(out.getvalue(), "tests.test_need 2G 0 FN_X=1\n")
            self.assertIn("40G -> 2G", err.getvalue())
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                test_budget.memory_plan(["tests.test_need FN_X=1"])
            self.assertEqual(out.getvalue().strip(), "tests.test_need 40G 1 FN_X=1")

    def test_module_inventory(self):
        expected = {"pack_chain": "48G", "bounds_join": "40G", "heap_from_profile": "2G",
                    "open_depth": "80G", "status_scale": "80G", "load": "16G",
                    "owner": "24G"}
        for module, value in expected.items():
            with self.subTest(module=module):
                self.assertEqual(test_budget.native_memory("tests.test_native_" + module), value)


class NodeDeadResultTests(unittest.TestCase):
    def test_mission_tls_and_web_ports_belong_to_the_started_owner(self):
        from tests import native_harness as harness
        process = mock.Mock(pid=42)
        process.poll.return_value = None
        process.stdout.wait_for.return_value = (b"CONTROL ready\n", 14)
        try:
            with tempfile.TemporaryDirectory() as directory:
                node = harness.Node(self, "fixture", root=Path(directory), listener=False,
                                    control=False, image_heap="mock starter")
                node.config.write_text('tls_port = 1234\nweb_port = 4321\n')
                with mock.patch.object(harness, "start", return_value=process) as start:
                    node.start(ready=None)
                    start.assert_called_once()
                harness.observe_node_greeting(1234, b"200 tls ready\r\n")
                self.assertEqual(harness.node_start_failures(self.id()), [])
                with mock.patch.object(harness, "start", return_value=process):
                    node.start(ready=None)
                harness.observe_http_reply(4321, b"HTTP/1.1 200 OK\r\n")
                self.assertEqual(harness.node_start_failures(self.id()), [])
                node.processes.clear()  # These mock starters own no process.
        finally:
            harness._NODE_GREETINGS.pop(self.id(), None)
            harness._NODE_DEAD.pop(self.id(), None)

    def test_raw_reader_and_stock_tool_bytes_satisfy_only_their_own_live_start(self):
        import io
        import queue
        import threading
        from tests import native_harness as harness
        from tests.test_native_article_slots import Poster
        from tests.test_native_credits import Reader
        from tests.test_native_outside_in import Talk
        process = mock.Mock(pid=42)
        process.poll.return_value = None
        try:
            harness.require_node_greeting(process, 1234)
            conn = mock.Mock()
            conn.makefile.return_value = io.BytesIO(b"200 raw ready\r\n")
            with mock.patch("tests.test_native_article_slots.socket.create_connection", return_value=conn) as connect:
                Poster(1234).close()
                connect.assert_called_once_with(("127.0.0.1", 1234), timeout=300)
            self.assertEqual(harness.node_start_failures(self.id()), [])

            harness.require_node_greeting(process, 1234)
            stop = threading.Event(); stop.set()
            reader = Reader(1234, stop)
            conn.makefile.return_value = io.BytesIO(b"200 thread ready\r\n")
            with mock.patch("tests.test_native_credits.socket.create_connection", return_value=conn) as connect:
                reader.start(); reader.join(1)
                self.assertFalse(reader.is_alive())
                connect.assert_called_once()
            self.assertEqual(harness.node_start_failures(self.id()), [])

            def dump(direction, data):
                return (direction + b" 0x123 [0x456] (16 bytes => 16 (0x10))\n0000 - "
                        + b" ".join(f"{b:02x}".encode() for b in data) + b"   captured\n")
            hidden = (dump(b"read from", b"20") + dump(b"write to", b"ignored")
                      + dump(b"read from", b"0 ready\r\n") + b"382 continue\r\n200 later\r\n")
            for output, valid in ((b"201 ready\r\n", True), (hidden, True),
                                  (dump(b"write to", b"200 fake\r\n"), False),
                                  (b"382 continue\r\n200 later\r\n", False),
                                  (dump(b"read from", b"400 no\r\n") + dump(b"read from", b"200 later\r\n"), False)):
                harness.require_node_greeting(process, 1234)
                self.assertEqual(harness.observe_tool_greeting(1234, output), valid)
                self.assertEqual(bool(harness.node_start_failures(self.id())), not valid)
                harness._NODE_GREETINGS.pop(self.id(), None)

            harness.require_node_greeting(process, 1234)
            talk = object.__new__(Talk)
            talk.port, talk.timeout, talk.argv = 1234, 1, ["openssl", "-debug"]
            talk.captured, talk.greeted, talk.raw_err = bytearray(), False, []
            talk.debug_dump = False
            talk.lines, talk.err, talk.transcript = queue.Queue(), [], []
            for line in hidden.splitlines(keepends=True): talk.lines.put(line)
            self.assertEqual(talk.line(), "382 continue")
            self.assertTrue(talk.greeted)
            self.assertEqual(harness.node_start_failures(self.id()), [])
            talk.lines.put(b"0000 - this is article text\r\n")
            self.assertEqual(talk.line(), "200 later")
            self.assertEqual(talk.line(), "0000 - this is article text")

            from tests.campaign import native_production_kill as campaign
            for greeting in (b"200 child ready\r\n", b""):
                harness.require_node_greeting(process, 1234)
                child = mock.Mock()
                with mock.patch.object(campaign.subprocess, "Popen", return_value=child) as spawn, \
                     mock.patch.object(campaign, "wait_line", return_value=b"GREETING " + greeting.hex().encode()) as wait:
                    if greeting:
                        self.assertIs(campaign.spawn_client(1234, Path("payload")), child)
                        self.assertEqual(harness.node_start_failures(self.id()), [])
                        child.communicate.assert_not_called()
                    else:
                        with self.assertRaisesRegex(harness.NodeDead, "never greeted"):
                            campaign.spawn_client(1234, Path("payload"))
                        child.communicate.assert_called_once_with(timeout=90)
                    wait.assert_called_once_with(child, b"GREETING ")
                    self.assertEqual(spawn.call_args.kwargs["bufsize"], 0)
                harness._NODE_GREETINGS.pop(self.id(), None)
                harness._NODE_DEAD.pop(self.id(), None)

            harness.require_node_greeting(process, 1234)
            process.poll.return_value = 1
            with self.assertRaisesRegex(harness.NodeDead, "exited before its greeting"):
                harness.observe_tool_greeting(1234, b"200 stale\r\n")
        finally:
            harness._NODE_GREETINGS.pop(self.id(), None)
            harness._NODE_DEAD.pop(self.id(), None)

    def test_existing_raw_response_helpers_acknowledge_without_a_probe(self):
        from tests import native_harness as harness
        from tests.test_native_control import control_exchange
        from tests.test_native_starttls import recv_line
        from tests.test_native_web import Browser
        process = mock.Mock(pid=42)
        process.poll.return_value = None
        try:
            harness.require_node_greeting(process, 1234, control="fixture.control")
            conn = mock.MagicMock()
            conn.__enter__.return_value = conn
            conn.recv.side_effect = [b"control reply", b""]
            with mock.patch("tests.test_native_control.socket.socket", return_value=conn) as create:
                self.assertEqual(control_exchange("fixture.control", b"request"), b"control reply")
                create.assert_called_once()
            self.assertEqual(harness.node_start_failures(self.id()), [])

            harness.require_node_greeting(process, 1234)
            conn = mock.Mock()
            conn.getpeername.return_value = ("127.0.0.1", 1234)
            conn.recv.return_value = b"201 ready\r\nnext"
            self.assertEqual(recv_line(conn), (b"201 ready\r\n", b"next"))
            conn.recv.assert_called_once_with(65536)
            self.assertEqual(harness.node_start_failures(self.id()), [])

            harness.require_node_greeting(process, None, web_port=4321)
            conn = mock.Mock()
            reply = conn.getresponse.return_value
            reply.status = 200
            reply.read.return_value = b"page"
            reply.getheaders.return_value = []
            reply.msg.get_all.return_value = []
            with mock.patch("tests.test_native_web.http.client.HTTPConnection", return_value=conn) as create:
                self.assertEqual(Browser(4321).request("GET", "/")[0], 200)
                create.assert_called_once()
            conn.request.assert_called_once()
            self.assertEqual(harness.node_start_failures(self.id()), [])

            for verb, words, rc, reply in (
                    ("operator", ["fixture.toml", "status"], 0, b"articles=0"),
                    ("identity", ["fixture.control"], 0, b"fn-store-identity-v1 reply"),
                    ("consumer", ["bootstrap", "fixture.control"], 0, b"consumer accepted"),
                    ("topic", ["install", "fixture.control"], 1, b"topic refused"),
                    ("hybrid-enroll", ["fixture.control", "1"], 0, b"hybrid accepted")):
                harness.require_node_greeting(process, None, control="fixture.control", config="fixture.toml")
                result = subprocess.CompletedProcess([], rc, reply, b"")
                with mock.patch.object(harness.subprocess, "run", return_value=result) as run, \
                     mock.patch.object(Path, "is_socket", return_value=True):
                    harness.run(["image", "--fn", verb, *words])
                    run.assert_called_once()
                self.assertEqual(harness.node_start_failures(self.id()), [])
        finally:
            harness._NODE_GREETINGS.pop(self.id(), None)
            harness._NODE_DEAD.pop(self.id(), None)

    def test_obligation_uses_only_real_test_responses_and_cannot_be_hidden(self):
        import contextlib
        import io
        from tests import native_harness as harness
        modes = ("exit", "silent", "eof", "greeting", "caught", "skip", "xfail", "missing",
                 "control", "offline", "control-dead", "account-hash", "refusal", "bad-refusal")
        for mode in modes:
            with self.subTest(mode=mode):
                process = mock.Mock(pid=42, returncode=1)
                process.poll.return_value = 1 if mode in ("exit", "refusal", "bad-refusal") else None
                class Cases(unittest.TestCase):
                    def test_row(self):
                        if mode.endswith("refusal"):
                            harness.require_node_greeting(process, 1234,
                                refusal="refused operator run machine-cannot-hold-profile" if mode == "refusal" else "")
                            return
                        harness.require_node_greeting(process, 1234, control="fixture.control")
                        if mode == "missing": return
                        if mode in ("control", "offline", "control-dead", "account-hash"):
                            if mode == "control-dead": process.poll.return_value = 1
                            with mock.patch.object(Path, "is_socket", return_value=True):
                                harness.observe_operator_reply(process, Path("fixture.control"),
                                    ("show",) if mode == "offline" else
                                    ("account", "hash", "alice") if mode == "account-hash" else ("status",),
                                    0, b"articles=0\n", b"")
                            return
                        sock = mock.Mock()
                        sock.recv.side_effect = ([b"200 ready\r\n"] if mode == "greeting" else
                                                [EOFError("closed") if mode == "eof" else TimeoutError("no greeting")])
                        try:
                            with mock.patch.object(harness.socket, "create_connection", return_value=sock) as connect:
                                harness.Client(1234).close(quit=False)
                            self.assertEqual(connect.call_count, 1)
                        except harness.NodeDead:
                            if mode == "skip": self.skipTest("startup hidden")
                            if mode != "caught": raise
                if mode == "xfail": Cases.test_row = unittest.expectedFailure(Cases.test_row)
                suite = unittest.defaultTestLoader.loadTestsFromTestCase(Cases)
                out, err = io.StringIO(), io.StringIO()
                with mock.patch.object(test_budget.unittest.defaultTestLoader, "loadTestsFromName", return_value=suite), \
                     mock.patch.dict(os.environ, {"FN_VERDICT_STORE": ""}), \
                     contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                    rc = test_budget.run_one("fixture")
                record = json.loads(next(line[len(test_budget.RESULT_PREFIX):] for line in out.getvalue().splitlines()
                                         if line.startswith(test_budget.RESULT_PREFIX)))
                expected = mode in ("greeting", "control", "refusal")
                self.assertEqual(rc, 0 if expected else 1, err.getvalue())
                self.assertEqual(bool(record["node_dead"]), not expected)
                self.assertEqual(record["skipped"], 0)
                self.assertEqual(record["cases"][0][1], "ok" if expected else "FAIL")



class TestBudgetRunner(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-test-budget-")
        self.directory = Path(self.temp.name)
        # A package of throwaway modules the child imports by dotted name.
        package = self.directory / "budgetcases"
        package.mkdir()
        (package / "__init__.py").write_text("")
        (package / "passing.py").write_text(textwrap.dedent("""
            import unittest
            class Passing(unittest.TestCase):
                def test_quick(self):
                    self.assertTrue(True)
        """))
        (package / "failing.py").write_text(textwrap.dedent("""
            import unittest
            class Failing(unittest.TestCase):
                def test_wrong(self):
                    self.assertEqual(1, 2)
        """))
        (package / "slow.py").write_text(textwrap.dedent("""
            import time, unittest
            class Slow(unittest.TestCase):
                def test_sleeps(self):
                    time.sleep(60)
        """))
        # Order-dependent: the second test reads what the first one left in a
        # shared world (a module global standing in for a class fixture or a
        # process-wide session).
        (package / "leaky.py").write_text(textwrap.dedent("""
            import unittest
            WORLD = {}
            class Leaky(unittest.TestCase):
                def test_a_writes(self):
                    WORLD["authority"] = "granted"
                def test_b_relies(self):
                    self.assertEqual(WORLD.get("authority"), "granted")
        """))
        # Every test skipped, one by a decorator and a class by setUpClass
        # (counted in testsRun and not, respectively): nothing executed.
        (package / "skipping.py").write_text(textwrap.dedent("""
            import unittest
            class Skipped(unittest.TestCase):
                @unittest.skip("no image")
                def test_needs_image(self):
                    pass
            class ClassSkipped(unittest.TestCase):
                @classmethod
                def setUpClass(cls):
                    raise unittest.SkipTest("no production image")
                def test_needs_production(self):
                    pass
        """))
        (package / "partial.py").write_text(textwrap.dedent("""
            import unittest
            class Partial(unittest.TestCase):
                def test_runs(self):
                    pass
                @unittest.skip("opt-in unset")
                def test_gated(self):
                    pass
        """))
        # correctness-remainder's bounds_blob: an unguarded unittest.main()
        # inside a class body read the runner's argv and exited 2.
        (package / "exits.py").write_text(textwrap.dedent("""
            import unittest
            class Exits(unittest.TestCase):
                def test_x(self):
                    pass
                unittest.main()
        """))
        (package / "empty.py").write_text("import unittest\n")
        fake = self.directory / "fake-node"
        fake.write_text("#!" + sys.executable + "\n" + textwrap.dedent("""
            import os, socket, sys, time, tomllib
            from pathlib import Path
            config = Path(sys.argv[3])
            (config.parent / 'fake.pid').write_text(str(os.getpid()))
            mode = os.environ['FAKE_NODE_MODE']
            if mode == 'exit': sys.exit(3)
            port = tomllib.loads(config.read_text())['listener']['port']
            with socket.socket() as listener:
                listener.bind(('127.0.0.1', port)); listener.listen()
                print('LISTENING', port, flush=True)
                while True:
                    conn, _ = listener.accept()
                    with conn:
                        if mode == 'silent': time.sleep(30)
                        else: conn.sendall(b'200 ready\\r\\n')
        """))
        fake.chmod(0o755)
        (package / "node.py").write_text(textwrap.dedent("""
            import os, unittest
            from pathlib import Path
            from tests.campaign.native_operator_campaign import Node
            from tests.native_harness import Client, Node as HarnessNode
            class Startup(unittest.TestCase):
                def test_before_cut(self):
                    image, work = Path(os.environ['FAKE_NODE']), Path(os.environ['FAKE_WORK'])
                    if os.environ['FAKE_NODE_MODE'] == 'exit':
                        node = HarnessNode(self, image, root=work / 'owner', listener=False,
                                           control=False, image_heap='fake executable')
                        node.start(timeout=.3)
                    else:
                        node = Node(image, work, 'owner')
                        self.addCleanup(node.reap)
                        node.start_owner(timeout=.3)
                        if os.environ.get('FAKE_NODE_READER') == 'raw':
                            from tests.test_native_article_slots import Poster
                            Poster(node.port, timeout=.3).close()
                        else:
                            Client(node.port, timeout=.3).close(quit=False)
        """))
        self.environment = mock.patch.dict(
            os.environ, {"PYTHONPATH": str(self.directory)
                         + os.pathsep + os.environ.get("PYTHONPATH", "")})
        self.environment.start()

    def tearDown(self):
        self.environment.stop()
        self.temp.cleanup()

    def run_module(self, name, budget):
        return test_budget.run_module(f"budgetcases.{name}", budget, None)

    def test_fake_nodes_report_dead_start_or_silent_greeting_as_failed(self):
        self.check_fake_nodes(("exit", "silent", "greeting"))

    def test_fake_nodes_reached_only_by_a_raw_reader_have_the_correct_verdict(self):
        self.check_fake_nodes(("silent", "greeting"), raw=True)

    def check_fake_nodes(self, modes, raw=False):
        import contextlib
        import io
        for mode in modes:
            with self.subTest(mode=mode):
                work = self.directory / mode; work.mkdir()
                log_dir = work / "logs"
                with mock.patch.dict(os.environ, {"FAKE_NODE": str(self.directory / "fake-node"),
                    "FAKE_WORK": str(work), "FAKE_NODE_MODE": mode,
                    "FAKE_NODE_READER": "raw" if raw else "client",
                    "FN_VERDICT_STORE": ""}):
                    record = test_budget.run_module("budgetcases.node", 10, log_dir)
                log = Path(record["log"])
                stream = io.StringIO()
                with contextlib.redirect_stdout(stream):
                    rc = test_budget.verdict_of_log(log)
                if mode == "greeting":
                    self.assertTrue(record["passed"], log.read_text())
                    self.assertEqual(rc, 0); self.assertIn(": OK (", stream.getvalue())
                    self.assertFalse(record.get("node_dead"))
                else:
                    self.assertFalse(record["passed"], log.read_text())
                    self.assertFalse(record["all_skipped"])
                    self.assertEqual(record["returncode"], 1)
                    self.assertEqual(rc, 1)
                    self.assertTrue(record["node_dead"])
                    self.assertIn("FAILED (node dead)", stream.getvalue())
                    self.assertIn("FAILED (node dead)", test_budget.summarize(record, 0))

    def test_a_passing_module_reports_its_time_and_tests(self):
        record = self.run_module("passing", 60)
        self.assertTrue(record["passed"], record)
        self.assertFalse(record["over_budget"])
        self.assertEqual(record["tests"], 1)
        self.assertEqual(len(record["timings"]), 1)
        self.assertLess(record["seconds"], 60)

    def test_reverse_order_exposes_a_test_that_relies_on_an_earlier_one(self):
        forward = test_budget.run_module("budgetcases.leaky", 60, None)
        self.assertTrue(forward["passed"], forward)
        backward = test_budget.run_module("budgetcases.leaky", 60, None, "reverse")
        self.assertFalse(backward["passed"])
        self.assertFalse(backward["over_budget"])
        self.assertEqual((backward["tests"], backward["failures"]), (2, 1))
        self.assertEqual([name.rsplit(".", 1)[-1] for name, _ in backward["timings"]],
                         ["test_b_relies", "test_a_writes"])

    def test_a_test_over_its_own_budget_makes_the_module_over(self):
        with mock.patch.object(test_budget, "TEST_BUDGET_SECONDS", -1.0):
            record = self.run_module("passing", 60)
        self.assertTrue(record["over_budget"])
        self.assertFalse(record["terminated"])
        self.assertFalse(record["passed"])
        self.assertEqual(record["returncode"], 0)
        self.assertEqual([name.rsplit(".", 1)[-1] for name, _ in record["slow_tests"]],
                         ["test_quick"])
        self.assertIn("a test over", test_budget.summarize(record, 1))

    def test_a_failing_module_is_failed_not_over_budget(self):
        record = self.run_module("failing", 60)
        self.assertFalse(record["passed"])
        self.assertFalse(record["over_budget"])
        self.assertEqual(record["failures"], 1)

    def test_a_module_past_its_budget_is_terminated_and_reported_over(self):
        record = self.run_module("slow", 2)
        self.assertTrue(record["over_budget"])
        self.assertFalse(record["passed"])
        # Terminated near the budget, not after the test's 60 s.
        self.assertLess(record["seconds"], 2 + test_budget.GRACE_SECONDS + 5)

    def test_exit_codes_keep_failure_and_budget_apart(self):
        def invoke(*names, budget="30"):
            return subprocess.run(
                [sys.executable, str(ROOT / "tools" / "test_budget.py"), "--budget", budget,
                 *(f"budgetcases.{name}" for name in names)],
                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                env=os.environ.copy(), timeout=120).returncode
        self.assertEqual(invoke("passing"), 0)
        self.assertEqual(invoke("failing"), 1)
        self.assertEqual(invoke("slow", budget="2"), 2)
        self.assertEqual(invoke("failing", "slow", budget="2"), 3)

    def test_a_module_that_skipped_every_test_is_skipped_not_passed(self):
        record = self.run_module("skipping", 60)
        self.assertTrue(record["all_skipped"], record)
        self.assertFalse(record["passed"])
        self.assertEqual((record["executed"], record["skipped"]), (0, 2))
        line = test_budget.summarize(record, 1)
        self.assertIn("SKIPPED (2 of 2", line)
        self.assertIn("no production image", line)
        self.assertNotIn(" ok", line)

    def test_a_module_with_some_skips_passes_and_names_them(self):
        record = self.run_module("partial", 60)
        self.assertTrue(record["passed"], record)
        self.assertFalse(record["all_skipped"])
        self.assertEqual((record["executed"], record["skipped"]), (1, 1))
        line = test_budget.summarize(record, 1)
        self.assertIn("ok (1 skipped: NOT RUN, not passed)", line)
        self.assertIn("opt-in unset", line)

    def test_all_skipped_has_its_own_exit_bit(self):
        def invoke(*arguments):
            return subprocess.run(
                [sys.executable, str(ROOT / "tools" / "test_budget.py"), "--budget", "30",
                 *arguments], cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                env=os.environ.copy(), timeout=120)
        answer = invoke("budgetcases.skipping", "budgetcases.passing")
        self.assertEqual(answer.returncode, 4, answer.stdout)
        self.assertIn(b"1 SKIPPED (no test executed)", answer.stdout)
        self.assertEqual(invoke("budgetcases.skipping", "budgetcases.failing").returncode, 5)
        allowed = invoke("--allow-skipped", "budgetcases.skipping")
        self.assertEqual(allowed.returncode, 0)
        self.assertIn(b"SKIPPED (2 of 2", allowed.stdout)

    def test_verdict_of_a_one_log(self):
        for name, code, needle in (("skipping", 4, "SKIPPED (2 of 2"),
                                   ("partial", 0, "OK (1 ran, 1 skipped)"),
                                   ("failing", 1, "FAILED (1 failures"),
                                   ("exits", 1, "did not load: importing budgetcases.exits "
                                                "exited with SystemExit(2)"),
                                   ("empty", 1, "FAILED (0 tests collected")):
            log = self.directory / f"{name}.log"
            with open(log, "wb") as out:
                subprocess.run([sys.executable, str(ROOT / "tools" / "test_budget.py"),
                                "--one", f"budgetcases.{name}"], cwd=ROOT, stdout=out,
                               stderr=subprocess.STDOUT, env=os.environ.copy(), timeout=120)
            answer = subprocess.run(
                [sys.executable, str(ROOT / "tools" / "test_budget.py"), "--verdict", str(log)],
                cwd=ROOT, capture_output=True, text=True, timeout=60)
            self.assertEqual(answer.returncode, code, answer.stdout)
            self.assertIn(needle, answer.stdout)

    def test_a_module_with_no_test_or_that_exits_on_import_is_not_a_pass(self):
        for name in ("empty", "exits"):
            record = self.run_module(name, 60)
            self.assertFalse(record["passed"], record)
            self.assertFalse(record["all_skipped"], record)

    def test_the_budget_can_be_lowered_never_raised(self):
        self.assertEqual(test_budget.budget_for("m", 300, {"m": 120}), 120)
        self.assertEqual(test_budget.budget_for("m", 300, {"m": 900}), 300)
        with self.assertRaises(SystemExit):
            test_budget.main(["--budget", "301", "tests.test_x"])


if __name__ == "__main__":
    unittest.main()
