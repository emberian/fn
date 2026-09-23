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
import subprocess
import sys
import tempfile
import unittest

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
