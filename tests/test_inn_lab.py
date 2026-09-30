"""tools/inn_lab.py against a fake host, a fake INN and a fake native image.

The lab's value is that it talks to a *real* INN and the *real* native image,
so nothing here can say it works -- the real evidence is
`planning/evidence/inn-lab-<image>-<date>.md`, from a run on hbox.  What this
file establishes is the other half: that the lab's own logic is right before
it is pointed at a box.  That its relay parsing pairs every command with its
reply; that its header comparison names exactly the fields two copies differ
in; that it refuses to run without a native image (D07); that its scenarios
run in order and each records a verdict; that the INN configuration it
writes is the configuration docs/interop-inn.md quotes; that a serving-agent
deviation is reported as violated rather than passed; and that the lab leaves
no process behind while leaving the INN install alone.

Both sides are fakes (`tests/inn_lab_fake/bin` for INN,
`tests/inn_lab_fake/native/fn-host` for the image).  Every reply in this
file's runs comes from `tests/`, and a green run says the harness works.
"""
import base64
import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import ssl
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import inn_lab  # noqa: E402

FAKE_IMAGE = ROOT / "tests/inn_lab_fake/native/fn-host"


def free_port() -> int:
    import socket
    sock = socket.socket()
    sock.bind(("127.0.0.1", 0))
    port = sock.getsockname()[1]
    sock.close()
    return port


def tap_line(pair, conn, way, data: bytes) -> str:
    return json.dumps({"t": 0, "pair": pair, "conn": conn, "way": way,
                       "data": base64.b64encode(data).decode()})


class ConfigurationTests(unittest.TestCase):
    """The five files the lab writes are the five docs/interop-inn.md quotes."""

    fields = dict(prefix="/tank/fn/inn/2.7.4", inn_port=11419, innfeed_port=11417,
                  inn_identity=inn_lab.INN_PATH_IDENTITY,
                  fn_identity=inn_lab.FN_PATH_IDENTITY, user="hbox", group="hbox")

    def rendered(self):
        return {"inn.conf": inn_lab.INN_CONF, "incoming.conf": inn_lab.INCOMING_CONF,
                "newsfeeds": inn_lab.NEWSFEEDS, "innfeed.conf": inn_lab.INNFEED_CONF,
                "readers.conf": inn_lab.READERS_CONF}

    def test_every_template_renders_and_is_named_in_config_files(self):
        for name, template in self.rendered().items():
            self.assertIn(name, inn_lab.CONFIG_FILES)
            template.format(**self.fields)      # a missing key raises here

    def test_the_ports_are_the_114xx_decade_and_all_differ(self):
        ports = (inn_lab.INN_PORT, inn_lab.NNRPD_PORT, inn_lab.FN_PORT,
                 inn_lab.TAP_OUT_PORT, inn_lab.TAP_IN_PORT)
        self.assertEqual(len(set(ports)), 5)
        for one in ports:
            self.assertEqual(one // 100, 114, one)
        text = inn_lab.INN_CONF.format(**self.fields)
        self.assertIn("port:                   11419", text)
        self.assertIn("bindaddress:            127.0.0.1", text)

    def test_innfeed_names_the_relay_that_forwards_to_the_owner(self):
        self.assertIn("port-number:         11417",
                      inn_lab.INNFEED_CONF.format(**self.fields))

    def test_the_me_entry_carries_the_exclusion_that_makes_a_loop_a_437(self):
        lines = inn_lab.NEWSFEEDS.format(**self.fields).splitlines()
        me = [one for one in lines if one.startswith("ME/")]
        self.assertEqual(len(me), 1, me)
        self.assertIn(inn_lab.INN_PATH_IDENTITY, me[0])
        self.assertNotIn(inn_lab.FN_PATH_IDENTITY, me[0],
                         "excluding fn's own identity in ME would refuse every "
                         "article fn ever feeds, not just a loop")

    def test_the_fn_site_excludes_fn_so_its_articles_are_not_offered_back(self):
        site = [one for one in inn_lab.NEWSFEEDS.format(**self.fields).splitlines()
                if one.startswith("fn")]
        self.assertEqual(site, ["fn/{}:fn.*:Tm:innfeed!".format(
            inn_lab.FN_PATH_IDENTITY)])

    def test_incoming_conf_has_no_identity_key(self):
        # inncheck rejects `identity` outright; specs/peering.md section 5 puts
        # the site name in newsfeeds instead, and this is that correction.
        self.assertNotIn("identity:", inn_lab.INCOMING_CONF)
        self.assertIn("patterns:        fn.*", inn_lab.INCOMING_CONF)


class PidParseTests(unittest.TestCase):
    """The pid a start step reports, and the two ways it used to crash."""

    def test_an_empty_pid_file_is_the_empty_string_and_not_an_exception(self):
        self.assertEqual(inn_lab.reported_pid("NNRPD-UP pid=\n"), "")
        self.assertEqual(inn_lab.reported_pid("NNRPD-UP pid="), "")
        self.assertEqual(inn_lab.reported_pid("NNRPD-TIMEOUT\n"), "")

    def test_a_pid_is_read_and_a_non_numeric_tail_is_not(self):
        self.assertEqual(inn_lab.reported_pid("INND-UP pid=629111\n"), "629111")
        self.assertEqual(inn_lab.reported_pid("INND-UP pid=629111 extra\n"), "629111")
        self.assertEqual(inn_lab.reported_pid("INND-UP pid=cat: no such file"), "")

    def test_the_fake_writes_the_pid_file_the_lab_reads(self):
        source = (ROOT / "tests/inn_lab_fake/bin/_fakeinn.py").read_text()
        self.assertIn('"nnrpd-{}.pid".format(port)', source)
        self.assertIn("run/nnrpd-{port}.pid", (ROOT / "tools/inn_lab.py").read_text())


class ArticleTests(unittest.TestCase):
    """The octets the lab builds, and the comparison it reports."""

    def test_a_posted_article_has_no_path_and_a_relayed_one_does(self):
        posted = inn_lab.article("<a@b>", "s", "Tue, 22 Sep 2026 00:00:00 +0000")
        self.assertFalse(posted.startswith(b"Path:"))
        self.assertTrue(posted.endswith(b"\r\n"))
        relayed = inn_lab.article("<a@b>", "s", "d", path="x!not-for-mail")
        self.assertTrue(relayed.startswith(b"Path: x!not-for-mail\r\n"))

    def test_the_differences_are_named_field_by_field(self):
        fn = (b"Path: fnA!not-for-mail\r\nFrom: a\r\nSubject: s\r\n"
              b"Message-ID: <m@x>\r\n\r\nbody\r\n")
        inn = (b"Path: inn!fnA!not-for-mail\r\nFrom: a\r\nSubject: s\r\n"
               b"Message-ID: <m@x>\r\nXref: inn fn.letters:3\r\n\r\nbody\r\n")
        diff = inn_lab.header_differences(fn, inn)
        self.assertEqual(diff["changed"], ["path"])
        self.assertEqual(diff["only_second"], ["xref"])
        self.assertEqual(diff["only_first"], [])
        self.assertTrue(diff["body_identical"])
        self.assertTrue(inn_lab.relay_changes_permitted(diff))
        self.assertIn("changed: path", inn_lab.describe_differences(diff))

    def test_a_changed_subject_or_body_is_not_a_permitted_relay_change(self):
        a = b"Path: x\r\nSubject: one\r\n\r\nbody\r\n"
        self.assertFalse(inn_lab.relay_changes_permitted(inn_lab.header_differences(
            a, a.replace(b"one", b"two"))))
        diff = inn_lab.header_differences(a, a.replace(b"body", b"bodY"))
        self.assertFalse(diff["body_identical"])
        self.assertFalse(inn_lab.relay_changes_permitted(diff))
        self.assertIn("BODY DIFFERS", inn_lab.describe_differences(diff))

    def test_folded_fields_and_case_are_one_field(self):
        a = b"Subject: one\r\n two\r\nPATH: x\r\n\r\nb\r\n"
        b = b"subject: one\r\n two\r\npath: x\r\n\r\nb\r\n"
        diff = inn_lab.header_differences(a, b)
        self.assertEqual((diff["changed"], diff["only_first"], diff["only_second"]),
                         ([], [], []))
        self.assertFalse(diff["identical"])
        self.assertEqual(inn_lab.header_value(a, "subject"), "one\r\n two")


class RelayParseTests(unittest.TestCase):
    """What the tap logged becomes the exchange the evidence quotes."""

    PAIR = "11418>11419"

    def test_ihave_pairs_both_replies_and_carries_the_article_unstuffed(self):
        client = (b"IHAVE <m@x>\r\nPath: a\r\n\r\n..dot\r\n.\r\nQUIT\r\n")
        server = (b"200 inn ready\r\n335 Send it\r\n235 Article transferred OK\r\n"
                  b"205 Bye!\r\n")
        text = "\n".join([tap_line(self.PAIR, 1, "server", server[:20]),
                          tap_line(self.PAIR, 1, "client", client),
                          tap_line(self.PAIR, 1, "server", server[20:])])
        found = inn_lab.find_exchange(text, self.PAIR, "<m@x>")
        self.assertEqual(found["verbs"], ["IHAVE"])
        self.assertEqual(found["offer"], "335 Send it")
        self.assertEqual(found["result"], "235 Article transferred OK")
        self.assertEqual(found["article"], b"Path: a\r\n\r\n.dot\r\n")
        self.assertTrue(found["complete"])

    def test_check_then_takethis_is_one_exchange_answered_twice(self):
        client = b"MODE STREAM\r\nCHECK <m@x>\r\nTAKETHIS <m@x>\r\nA: b\r\n\r\nc\r\n.\r\n"
        server = b"200 fn\r\n203 ok\r\n238 <m@x>\r\n239 <m@x>\r\n"
        text = "\n".join([tap_line("11417>11490", 1, "client", client),
                          tap_line("11417>11490", 1, "server", server)])
        found = inn_lab.find_exchange(text, "11417>11490", "<m@x>")
        self.assertEqual(found["verbs"], ["CHECK", "TAKETHIS"])
        self.assertEqual((found["offer"], found["result"]), ("238 <m@x>", "239 <m@x>"))
        self.assertEqual(found["article"], b"A: b\r\n\r\nc\r\n")
        self.assertIsNone(inn_lab.find_exchange(text, self.PAIR, "<m@x>"))

    def test_a_transfer_without_its_final_reply_is_not_complete(self):
        text = "\n".join([tap_line(self.PAIR, 1, "server", b"200 x\r\n335 go\r\n"),
                          tap_line(self.PAIR, 1, "client", b"IHAVE <m@x>\r\nA: b\r\n")])
        found = inn_lab.find_exchange(text, self.PAIR, "<m@x>")
        self.assertFalse(found["complete"])
        declined = "\n".join([tap_line(self.PAIR, 1, "server", b"200 x\r\n435 dup\r\n"),
                              tap_line(self.PAIR, 1, "client", b"IHAVE <m@x>\r\n")])
        self.assertTrue(inn_lab.find_exchange(declined, self.PAIR, "<m@x>")["complete"])

    def test_connections_are_kept_apart_and_the_last_offer_is_reported(self):
        lines = []
        for conn, reply in ((1, b"437 no\r\n"), (2, b"235 ok\r\n")):
            lines.append(tap_line(self.PAIR, conn, "server", b"200 x\r\n335 go\r\n" + reply))
            lines.append(tap_line(self.PAIR, conn, "client",
                                  b"IHAVE <m@x>\r\nA: b\r\n\r\nc\r\n.\r\n"))
        found = inn_lab.find_exchange("\n".join(lines), self.PAIR, "<m@x>")
        self.assertEqual(found["result"], "235 ok")


class CommandLineTests(unittest.TestCase):

    def test_the_lab_refuses_to_run_without_a_native_image(self):
        with self.assertRaises(SystemExit) as raised, \
                contextlib.redirect_stderr(io.StringIO()) as said:
            inn_lab.main(["HEAD", "--host", "hbox"])
        self.assertIn("--native-image is required", said.getvalue())
        self.assertEqual(raised.exception.code, 2)

    def test_no_development_entry_point_is_left_in_the_lab(self):
        source = (ROOT / "tools/inn_lab.py").read_text()
        for retired in ("run_reader.py", "run_owner.py", "run_store.py", "bin/fn "):
            self.assertNotIn(retired, source)

    def test_the_owner_is_the_packaged_entry_with_the_named_image(self):
        lab = inn_lab.InnLab(
            inn_lab.LocalHost(Path(tempfile.mkdtemp())), ROOT, "a" * 40, "abc1234",
            "dev", native_image="/opt/fn/fn-host", native_openssl_prefix="/opt/ssl",
            inn_prefix="/x", inn_version="2.7.4", inn_port=1, nnrpd_port=2,
            fn_port=3, tap_out_port=4, tap_in_port=5)
        self.assertEqual(
            lab.operator("run"),
            "env FN_OPENSSL_PREFIX=/opt/ssl FN_NATIVE_HOST=/opt/fn/fn-host "
            "packaging/fn-native operator $HOME/fn-inn-lab/dev-abc1234/node/fn.toml run")
        self.assertTrue(lab.deploy.startswith("$HOME/fn-inn-lab/"))


class DryRun:
    """One whole lab run against a fake host, a fake INN and a fake image."""

    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="fn-inn-lab-")
        base = Path(cls.temp.name)
        cls.home = base / "home"
        cls.home.mkdir(parents=True)
        cls.inn = base / "inn/2.7.4"
        shutil.copytree(ROOT / "tests/inn_lab_fake/bin", cls.inn / "bin")
        for one in (cls.inn / "bin").iterdir():
            one.chmod(0o755)
        (cls.inn / "etc").mkdir(exist_ok=True)
        (base / "inn/src").mkdir(parents=True, exist_ok=True)
        (base / "inn/src/inn-2.7.4.tar.gz.sha256").write_text(
            "0000fake0000  inn-2.7.4.tar.gz\n")
        try:
            commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                                    stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                    check=True).stdout.decode().strip()
        except (subprocess.CalledProcessError, FileNotFoundError) as error:
            raise unittest.SkipTest(
                "the lab ships the tree with `git archive`; this checkout is not a "
                "git repository") from error
        cls.evidence = base / "inn-lab-evidence.md"
        cls.ports = [free_port() for _ in range(5)]
        argv = [commit, "--dry-run", "--home", str(cls.home), "--repo", str(ROOT),
                "--evidence", str(cls.evidence), "--keep",
                "--native-image", str(FAKE_IMAGE),
                "--inn-prefix", str(cls.inn),
                "--inn-port", str(cls.ports[0]), "--nnrpd-port", str(cls.ports[1]),
                "--fn-port", str(cls.ports[2]), "--tap-out-port", str(cls.ports[3]),
                "--tap-in-port", str(cls.ports[4]), "--feed-wait", "20"]
        cls.code = inn_lab.main(argv)
        cls.text = cls.evidence.read_text()

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def named(self, fragment):
        return [line for line in self.text.splitlines()
                if line.startswith("| ") and fragment in line]

    def findings(self):
        return json.loads(self.evidence.with_suffix(".findings.json").read_text())

    def keys_with(self, verdict):
        return {row["key"] + ("[{}]".format(row["instance"]) if row["instance"] else "")
                for row in self.findings()["rows"] if row["verdict"] == verdict}


class LabTests(DryRun, unittest.TestCase):

    def test_every_message_id_carries_this_run_s_tag(self):
        ids = inn_lab.message_ids("abc1234-20260920T000000Z")
        self.assertEqual(len(set(ids.values())), len(inn_lab.ID_TEMPLATES))
        for one in ids.values():
            self.assertIn("abc1234-20260920T000000Z", one)

    def test_every_decided_key_is_a_declared_assertion(self):
        """A held row reads its sentence from ASSERTIONS; the fake image holds
        none of the violated rows, so only this catches an undeclared key."""
        import re
        source = (ROOT / "tools/inn_lab.py").read_text()
        keys = set(re.findall(r'self\.(?:check|record)\(\s*"([a-z0-9-]+)"', source))
        self.assertTrue(keys)
        self.assertEqual(keys - set(inn_lab.InnLab.ASSERTIONS), set())

    def test_the_violations_are_exactly_the_three_the_fake_image_commits(self):
        """The fake stores `operator post` payloads with no Path, serves a
        transit article with the sender's Path and Xref, and takes `From: yue`,
        as the image did on 2026-09-22; the lab must call each of those
        violated and nothing else."""
        self.assertEqual(self.keys_with("violated"),
                         {"operator-post-feeds-inn", "fn-serves-own-path-identity",
                          "fn-serves-no-sender-xref", "fn-post-from-invalid-441"},
                         self.text[-6000:])
        self.assertEqual(self.code, 1)
        self.assertNotIn("lab error", self.text)
        self.assertEqual(self.keys_with("not-exercised"), set())
        self.assertEqual(self.keys_with("inconclusive"), set())

    def test_the_transit_rows_hold_with_their_replies_quoted(self):
        held = self.keys_with("held")
        for key in ("fn-post-240", "fn-feeds-inn", "inn-serves-fn-article",
                    "inn-transfer-235", "inn-duplicate-435", "inn-duplicate-435[fn-article]",
                    "inn-loop-437", "innfeed-feeds-fn", "fn-serves-inn-article",
                    "fn-duplicate-435[inn-article]", "fn-duplicate-435[fn-article]",
                    "fn-loop-refused", "entry-point-listening", "path-identity-set",
                    "peer-record-accepted", "tap-up"):
            self.assertIn(key, held)
        self.assertIn("| fn feed to inn | IHAVE: 335 Send it / 235 Article transferred OK",
                      self.text)
        self.assertIn('437 Missing \\"Path\\" header field', json.dumps(self.text))
        self.assertIn("| innfeed to fn | CHECK+TAKETHIS: 238", self.text)

    def test_the_header_differences_are_recorded_by_name(self):
        row = self.named("| fn served vs inn served |")
        self.assertTrue(row and "changed: path; only in the second: xref" in row[0], row)
        row = self.named("| fn post vs fn served |")
        self.assertTrue(row and "injection-date, injection-info, path" in row[0], row)

    def test_the_owner_was_stopped_recovered_and_reread(self):
        held = self.keys_with("held")
        for key in ("fn-term-stopped", "fn-recover", "innd-survived-fn-term",
                    "fn-articles-survived-term[fn-article]",
                    "fn-articles-survived-term[inn-article]"):
            self.assertIn(key, held)

    def test_innd_was_killed_and_its_history_survived(self):
        held = self.keys_with("held")
        for key in ("innd-died", "innd-restarted", "inn-history-survived-kill[inn-article]",
                    "inn-history-survived-kill[fn-article]"):
            self.assertIn(key, held)

    def test_the_configuration_on_disk_is_the_configuration_in_the_tool(self):
        for name in inn_lab.CONFIG_FILES:
            self.assertTrue((self.inn / "etc" / name).exists(), name)
            self.assertTrue(self.named("INN {} as written".format(name)), name)

    def test_the_evidence_carries_the_subject_and_the_relay_transcript(self):
        for heading in ("## What ran", "## Every command", "### Commands in full",
                        "## The relay's transcript", "## Raw step output"):
            self.assertIn(heading, self.text)
        self.assertIn("| native image | {}".format(FAKE_IMAGE), self.text)
        self.assertIn("| inn version |", self.text)
        self.assertIn("C: IHAVE <inn-lab-fn-post-", self.text)
        self.assertIn("C: TAKETHIS <inn-lab-fed-", self.text)
        self.assertNotIn("(the relay carried nothing)", self.text)
        self.assertIn("INN and fn are on ONE host", self.text)

    def test_the_box_is_left_clean_and_the_install_is_left_alone(self):
        clean = self.named("stray lab processes")
        self.assertTrue(clean and "CLEAN" in clean[0], clean)
        self.assertTrue((self.inn / "bin/innd").exists())
        self.assertTrue(self.named("innd and innfeed are gone"))


if __name__ == "__main__":
    unittest.main()


class ProtectedReaderDriverTests(unittest.TestCase):
    """Driver outcomes from a scripted peer; this cannot certify real INN."""

    def driver(self):
        namespace = {"__name__": "inn_driver_test"}
        exec(compile(inn_lab.INN_DRIVER, "<inn_driver>", "exec"), namespace)
        return namespace

    def test_failed_login_does_not_authorize_then_correct_login_reads(self):
        driver = self.driver()
        commands = []
        replies = iter(["381 password", "481 denied", "480 authenticate",
                        "381 password", "281 authenticated", "211 group", "220 article"])
        class ScriptedPeer:
            greeting = "200 ready"
            sock = SimpleNamespace(version=lambda: "TLSv1.3")
            def __init__(self, port):
                self.port = port
            def starttls(self, cafile):
                commands.append(("TLS", cafile))
                return "382 negotiate"
            def cmd(self, command):
                commands.append(command)
                return next(replies)
            def block(self):
                return b"Subject: test\r\n\r\nbody\r\n"
            def close(self):
                commands.append("closed")
        driver["Wire"] = ScriptedPeer
        with tempfile.TemporaryDirectory() as tmp:
            password = Path(tmp) / "password"
            password.write_bytes(b"fixture-secret\n")
            result = driver["protected_read"](SimpleNamespace(
                port=11421, cafile="scratch-ca", username="fn-lab", group="fn.letters",
                password_file=str(password), msgid="<secure@example.invalid>"))
        self.assertTrue(result["ok"], result)
        self.assertEqual(commands[0], ("TLS", "scratch-ca"))
        self.assertEqual(commands[-1], "closed")
        self.assertEqual(commands.count("AUTHINFO PASS fixture-secret"), 1)
        self.assertNotIn("fixture-secret", json.dumps(result))
        self.assertNotIn("not-the-fixture-password", json.dumps(result))

    def test_refused_login_stops_without_article_or_claim_of_success(self):
        driver = self.driver()
        commands = []
        replies = iter(["381 password", "481 denied", "480 authenticate",
                        "381 password", "481 still denied"])
        class ScriptedPeer:
            greeting = "200 ready"
            sock = SimpleNamespace(version=lambda: "TLSv1.3")
            def __init__(self, port):
                pass
            def starttls(self, cafile):
                return "382 negotiate"
            def cmd(self, command):
                commands.append(command)
                return next(replies)
            def close(self):
                commands.append("closed")
        driver["Wire"] = ScriptedPeer
        with tempfile.TemporaryDirectory() as tmp:
            password = Path(tmp) / "password"
            password.write_bytes(b"fixture-secret\n")
            result = driver["protected_read"](SimpleNamespace(
                port=11421, cafile="scratch-ca", username="fn-lab", group="fn.letters",
                password_file=str(password), msgid="<secure@example.invalid>"))
        self.assertFalse(result["ok"], result)
        self.assertNotIn("article", result)
        self.assertFalse(any(c.startswith("ARTICLE ") for c in commands))
        self.assertEqual(commands[-1], "closed")

    def test_rejected_tls_cannot_send_credentials_and_still_closes(self):
        driver = self.driver()
        commands = []
        class ScriptedPeer:
            greeting = "200 ready"
            def __init__(self, port):
                pass
            def starttls(self, cafile):
                raise ssl.SSLCertVerificationError("untrusted certificate")
            def cmd(self, command):
                commands.append(command)
                raise AssertionError("no credentials after TLS refusal")
            def close(self):
                commands.append("closed")
        driver["Wire"] = ScriptedPeer
        with self.assertRaises(ssl.SSLCertVerificationError):
            driver["protected_read"](SimpleNamespace(port=11421, cafile="wrong-ca"))
        self.assertEqual(commands, ["closed"])


class ProtectedReaderFixtureTests(unittest.TestCase):
    """The optional row is isolated and fails on authentication or article changes."""

    def lab(self, security=True, streaming=False):
        return inn_lab.InnLab(inn_lab.LocalHost(Path("/tmp/unused-inn-fixture")),
            ROOT, "a" * 40, "abc1234", "dev", native_image="/opt/fn/fn-host",
            inn_prefix="/isolated/test-inn", inn_version="2.7.4", inn_port=1,
            nnrpd_port=2, fn_port=3, tap_out_port=4, tap_in_port=5,
            inn_security=security, inn_security_port=6, inn_streaming=streaming)

    def test_requires_an_explicit_prefix_and_distinct_security_port(self):
        for extra in (["--inn-security"],
                      ["--inn-security", "--inn-prefix", "/tank/fn/inn/2.7.4"],
                      ["--inn-security", "--inn-prefix", "/isolated/test-inn",
                       "--inn-security-port", str(inn_lab.FN_PORT)]):
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as out:
                inn_lab.main(["HEAD", "--native-image", "/opt/fn/fn-host"] + extra)
            self.assertEqual(out.exception.code, 2)

    def test_cleanup_kills_only_the_owned_recorded_reader_pids(self):
        lab = self.lab()
        lab.started_pids = {"nnrpd-security": "123", "nnrpd": "456", "unrelated": "789"}
        commands = []
        lab.sh = lambda name, command, **kwargs: commands.append(command)
        lab.inn_stop()
        self.assertEqual(len(commands), 2)
        self.assertIn("kill 123 ", commands[0])
        self.assertIn("kill 456 ", commands[1])
        self.assertEqual(lab.started_pids, {"unrelated": "789"})

    def test_row_is_absent_when_not_selected_and_keeps_transit_gap_when_selected(self):
        self.assertNotIn("inn-protected-reader", self.lab(False).ASSERTIONS)
        lab = self.lab()
        self.assertIn("inn-protected-reader", lab.ASSERTIONS)
        self.assertTrue(any("transit relays remain clear" in x for x in lab.STANDING_GAPS))
        config = inn_lab.READERS_SECURITY_CONF.format(prefix="/isolated/test-inn", inn_port=1, access="RA")
        self.assertNotIn("default:", config)
        self.assertIn("require_encryption: true", config)
        self.assertIn("access: RA", config)

    def test_success_requires_authorized_read_and_unchanged_body(self):
        original = b"Path: fn!not-for-mail\r\nSubject: example\r\n\r\nbody\r\n"
        for authenticated, served, expected in ((True, original, True),
                (False, original, False), (True, original.replace(b"body", b"edit"), False),
                (True, b"", False)):
            lab = self.lab()
            lab.held_octets["fn-article"] = original
            result = dict(ok=authenticated, starttls="382 ready", tls="TLSv1.3",
                bad_pass="481 refused", before_login="480 auth required", **{"pass": "281 accepted"},
                article="220 article", octets=base64.b64encode(served).decode())
            commands = []
            lab.drive_inn = lambda phase, extra, name: (
                commands.append(extra) or inn_lab.Step(name, extra, 0, json.dumps(result), 0))
            checks = []
            lab.check = lambda name, ok, *args, **kwargs: checks.append((name, ok))
            lab.scenario_protected_read()
            self.assertEqual(checks, [("inn-protected-reader", expected)])
            self.assertIn('"$HOME"/fn-inn-lab/', commands[0])


class ProtectedInjectionFixtureTests(unittest.TestCase):
    """Native-feed assertion accounting, without claiming an INN/native run."""

    def test_feed_outcome_requires_exact_peer_subject_and_accepted_code(self):
        wanted = "accepted feed peer=inn-security message-id=<fresh@x> code=235 time=none"
        self.assertEqual(inn_lab.InnLab.protected_feed_acceptance(wanted, "inn-security", "<fresh@x>"), wanted)
        for text in (wanted.replace("235", "435"), wanted.replace("fresh", "older"),
                     wanted.replace("inn-security", "inn"), wanted.replace("accepted", "refused"),
                     "other words " + wanted):
            self.assertEqual(inn_lab.InnLab.protected_feed_acceptance(text, "inn-security", "<fresh@x>"), "")

    def test_refused_pause_prevents_new_peer_or_post(self):
        lab = ProtectedReaderFixtureTests().lab()
        commands = []
        lab.sh = lambda name, command, **kwargs: (
            commands.append(command) or inn_lab.Step(name, command, 1, "refused pause", 0))
        checks = []
        lab.check = lambda name, ok, *args, **kwargs: checks.append((name, ok))
        lab.scenario_protected_feed()
        self.assertEqual(len(commands), 1)
        self.assertEqual(checks, [("fn-protected-injection", False)])

    def test_completed_tls_feed_still_fails_when_clear_relay_carried_article(self):
        for clear in (False, True):
            lab = ProtectedReaderFixtureTests().lab()
            msgid = lab.ids["FN_PROTECTED_ID"]
            served = inn_lab.article(msgid, "native protected INN injection", lab.date)
            commands = []
            lab.sh = lambda name, command, **kwargs: (
                commands.append((name, command)) or inn_lab.Step(name, command, 0, "accepted", 0))
            lab.put_article = lambda name, octets: "/scratch/fn-protected.article"
            lab.wait_protected_feed = lambda peer, ident: "accepted feed peer=" + peer + " message-id=" + ident + " code=235"
            lab.drive_inn = lambda phase, extra, name: inn_lab.Step(name, extra, 0,
                json.dumps(dict(ok=True, article="220 article", octets=base64.b64encode(served).decode())), 0)
            lab.read_tap = lambda: None
            if clear:
                lab.tap_text = "\n".join([
                    tap_line("4>1", 1, "client", ("IHAVE " + msgid + "\r\n").encode() + served + b".\r\n"),
                    tap_line("4>1", 1, "server", b"200 ready\r\n335 send\r\n235 accepted\r\n")])
            checks = []
            lab.check = lambda name, ok, *args, **kwargs: checks.append((name, ok))
            lab.scenario_protected_feed()
            self.assertEqual(checks, [("fn-protected-injection", not clear)])
            self.assertIn("peer feed inn pause", commands[0][1])
            self.assertIn("source-address 127.0.0.1", commands[1][1])
            self.assertIn("false false starttls 127.0.0.1", commands[1][1])

    def test_injection_flag_requires_the_protected_reader_and_is_absent_by_default(self):
        self.assertNotIn("fn-protected-injection", ProtectedReaderFixtureTests().lab().ASSERTIONS)
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            inn_lab.main(["HEAD", "--native-image", "/opt/fn/fn-host", "--inn-security-feed"])


class StreamingFixtureTests(unittest.TestCase):
    """Harness accounting only: native/INN observations are still pending."""

    def test_completed_streaming_requires_matching_replies_and_article(self):
        good = dict(verbs=["CHECK", "TAKETHIS"], offer="238 <new@x> wanted",
                    result="239 <new@x> taken", article=b"article")
        self.assertTrue(inn_lab.streaming_transfer_completed(good, "<new@x>"))
        for field, bad in (("verbs", ["IHAVE"]), ("offer", "238 <old@x>"),
                ("result", "239 <old@x>"), ("offer", "431 <new@x>"),
                ("result", "439 <new@x>"), ("article", b"")):
            with self.subTest(field=field, bad=bad):
                self.assertFalse(inn_lab.streaming_transfer_completed(
                    dict(good, **{field: bad}), "<new@x>"))

    def test_wire_sends_takethis_only_after_same_subject_check_and_always_closes(self):
        for mode, check, final, expected in (("203 ready", "238 <new@x>", "239 <new@x>", True),
                ("500 no mode", "238 <new@x>", "239 <new@x>", False),
                ("203 ready", "238 <old@x>", "239 <new@x>", False),
                ("203 ready", "238 <new@x>", "239 <old@x>", False)):
            ns = {"__name__": "inn_driver_test"}
            exec(compile(inn_lab.INN_DRIVER, "inn-driver", "exec"), ns)
            events = []
            class Peer:
                greeting = "200 ready"
                def __init__(self, port): self.sock = SimpleNamespace(sendall=events.append)
                def cmd(self, text):
                    events.append(text)
                    return mode if text == "MODE STREAM" else check
                def send_block(self, data): events.append(data)
                def line(self): return final
                def close(self): events.append("closed")
            ns["Wire"], ns["octets"] = Peer, lambda path: b"complete fixture\r\n"
            got = ns["stream"](SimpleNamespace(port=1, msgid="<new@x>", file="fixture"))
            self.assertEqual(got["ok"], expected)
            self.assertEqual(events[-1], "closed")
            self.assertEqual(b"TAKETHIS <new@x>\r\n" in events,
                             mode.startswith("203") and check == "238 <new@x>")

    def test_both_actual_feed_directions_require_receiver_content_and_streaming(self):
        for mutation in (None, "ihave", "body", "feed-body", "subject", "submission"):
            lab = ProtectedReaderFixtureTests().lab(False)
            captured, commands, checks = {}, [], []
            lab.sh = lambda name, command, **kwargs: inn_lab.Step(name, command, 0, "accepted", 0)
            def put(name, octets): captured[name] = octets; return "/scratch/" + name
            lab.put_article = put
            def drive(phase, extra, name):
                commands.append((phase, extra))
                direction = "fn-to-inn" if "fn-to-inn" in name else "inn-to-fn"
                payload = captured["stream-" + direction]
                if phase == "fetch":
                    if mutation == "body": payload = payload.replace(b"From the fn INN interop lab.", b"EDIT")
                    if mutation == "subject": payload = payload.replace(b"Message-ID:", b"X-Wrong-ID:")
                    result = dict(article="220 article", octets=base64.b64encode(payload).decode())
                else: result = dict(ok=mutation != "submission",
                                    octets=base64.b64encode(payload).decode())
                return inn_lab.Step(name, extra, 0, json.dumps(result), 0)
            lab.drive_inn = drive
            def tap(pair, msgid, name):
                direction = "fn-to-inn" if "fn-to-inn" in name else "inn-to-fn"
                data = captured["stream-" + direction]
                if mutation == "feed-body": data = data.replace(b"From the fn INN interop lab.", b"EDIT")
                return dict(verbs=["IHAVE"] if mutation == "ihave" else ["CHECK", "TAKETHIS"],
                    offer="238 " + msgid, result="239 " + msgid,
                    article=data)
            lab.wait_tap = tap
            lab.check = lambda name, ok, *args, **kwargs: checks.append((kwargs["instance"], ok))
            lab.scenario_bidirectional_streaming()
            self.assertEqual(checks, [("fn-to-inn", mutation is None), ("inn-to-fn", mutation is None)])
            self.assertEqual([phase for phase, _ in commands], ["post", "fetch", "stream", "fetch"])

    def test_peer_refusal_starts_no_submission_and_option_is_unselected_by_default(self):
        lab = ProtectedReaderFixtureTests().lab(False)
        self.assertNotIn("bidirectional-streaming", lab.ASSERTIONS)
        self.assertIn("bidirectional-streaming", ProtectedReaderFixtureTests().lab(False, streaming=True).ASSERTIONS)
        lab.sh = lambda name, command, **kwargs: inn_lab.Step(name, command, 1, "refused", 0)
        lab.drive_inn = lambda *args, **kwargs: self.fail("submission after config refusal")
        checks = []
        lab.check = lambda name, ok, *args, **kwargs: checks.append((kwargs["instance"], ok))
        lab.scenario_bidirectional_streaming()
        self.assertEqual(checks, [("fn-to-inn", False), ("inn-to-fn", False)])


class CheckgroupsDriverTests(unittest.TestCase):
    """Actual-control observation accounting with scripted sockets only."""

    def test_filing_and_absence_are_all_required_from_a_non_peer_reader(self):
        for in_filing, in_ordinary, proposed, expected in (
                (True, False, False, True), (False, False, False, False),
                (True, True, False, False), (True, False, True, False)):
            ns = {"__name__": "inn_driver_test"}
            exec(compile(inn_lab.INN_DRIVER, "inn-driver", "exec"), ns)
            events = []
            class Peer:
                greeting = "200 reader"
                def __init__(self, port, source_address):
                    events.append(source_address)
                    self.blocks = iter([
                        b"1\r\n" if in_filing else b"",
                        b"2\r\n" if in_ordinary else b"",
                        b"fn.checkgroups.proposed 0 1 y\r\n" if proposed else b"",
                        b"Control: checkgroups\r\n\r\nbody\r\n"])
                def cmd(self, text):
                    if text.startswith("LISTGROUP"): return "211 1 1 1 group"
                    if text.startswith("STAT"): return "223 1 <control@x> article"
                    if text.startswith("LIST ACTIVE"): return "215 active"
                    if text.startswith("ARTICLE"): return "220 article"
                    raise AssertionError(text)
                def block(self): return next(self.blocks)
                def close(self): events.append("closed")
            ns["Wire"] = Peer
            got = ns["control_view"](SimpleNamespace(port=1, reader_source="127.0.0.2",
                group="control.checkgroups", other_group="fn.letters",
                probe_group="fn.checkgroups.proposed", msgid="<control@x>"))
            self.assertEqual(got["ok"], expected)
            self.assertEqual(events, ["127.0.0.2", "closed"])

    def test_invalid_local_number_is_not_sent_as_a_command(self):
        ns = {"__name__": "inn_driver_test"}
        exec(compile(inn_lab.INN_DRIVER, "inn-driver", "exec"), ns)
        commands = []
        peer = SimpleNamespace(cmd=lambda text: commands.append(text) or "211 group",
                               block=lambda: b"1; bad-command\r\n")
        with self.assertRaises(ValueError): ns["group_ids"](peer, "control.checkgroups")
        self.assertEqual(commands, ["LISTGROUP control.checkgroups"])


class CheckgroupsFixtureTests(unittest.TestCase):
    def test_refused_filing_group_prevents_control_injection(self):
        lab = ProtectedReaderFixtureTests().lab()
        commands = []
        lab.sh = lambda name, command, **kwargs: commands.append(command) or inn_lab.Step(name, command, 1, "refused", 0)
        checks = []
        lab.check = lambda name, ok, *args, **kwargs: checks.append((name, ok))
        lab.scenario_checkgroups_control()
        self.assertEqual(len(commands), 1)
        self.assertEqual(checks, [("inn-checkgroups-control", False)])

    def test_real_control_header_and_body_preservation_are_required(self):
        for mutation, expected in ((None, True), ("body", False), ("control", False)):
            lab = ProtectedReaderFixtureTests().lab()
            msgid = lab.ids["INN_CHECKGROUPS_ID"]
            captured = []
            lab.sh = lambda name, command, **kwargs: inn_lab.Step(name, command, 0, "accepted", 0)
            lab.put_article = lambda name, octets: captured.append(octets) or "/scratch/checkgroups.article"
            lab.wait_tap = lambda *args: dict(offer="238 " + msgid, result="239 " + msgid,
                verbs=["CHECK", "TAKETHIS"], article=captured[0])
            def drive(phase, extra, name):
                if phase == "offer": result = dict(offer="335 send", transfer="235 accepted")
                else:
                    served = captured[0]
                    if mutation == "body": served = served.replace(b"must not create", b"will be created")
                    if mutation == "control": served = served.replace(b"Control: checkgroups", b"Subject: control-like")
                    result = dict(ok=True, octets=base64.b64encode(served).decode(),
                        filing={"ids": [msgid]}, ordinary={"ids": []}, active_rows=[])
                return inn_lab.Step(name, extra, 0, json.dumps(result), 0)
            lab.drive_inn = drive
            checks = []
            lab.check = lambda name, ok, *args, **kwargs: checks.append((name, ok))
            lab.scenario_checkgroups_control()
            self.assertIn(b"\r\nControl: checkgroups\r\n", captured[0])
            self.assertEqual(checks, [("inn-checkgroups-control", expected)])
