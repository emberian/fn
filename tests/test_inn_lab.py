"""tools/inn_lab.py against a fake host and a fake INN: no ssh, no news server.

The lab's value is that it talks to a *real* INN, so nothing here can say it
works -- the real evidence is `planning/evidence/inn-lab-<rev>-<date>.md`, from
a run against the install on hbox.  What this file establishes is the other
half: that the lab's own logic is right before it is pointed at a box.  That
its five scenarios run in order and each records an outcome; that the INN
configuration it writes is the configuration docs/interop-inn.md quotes; that
the scenario the tree cannot support today is a *skip* carrying the exact
reply that made it one, and not a pass under the same name; that a SIGKILL of
each server is followed by a restart and a reread; and that the lab leaves no
process behind while leaving the install alone.

Both the INN side and the fn side are fakes (`tests/inn_lab_fake`,
`tests/deploy_gate_fake`).  Every reply in this file's runs comes from
`tests/`, and a green run says the harness works.
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

import inn_lab  # noqa: E402

FAKE_ACL2 = "#!/bin/sh\necho 'ACL2 Version 8.7 fake'\ncat > /dev/null\nexit 0\n"


def free_port() -> int:
    import socket
    sock = socket.socket()
    sock.bind(("127.0.0.1", 0))
    port = sock.getsockname()[1]
    sock.close()
    return port


class ConfigurationTests(unittest.TestCase):
    """The five files the lab writes are the five docs/interop-inn.md quotes."""

    fields = dict(prefix="/tank/fn/inn/2.7.4", inn_port=11119, fn_port=11190,
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

    def test_innd_listens_on_the_port_innfeed_does_not(self):
        text = inn_lab.INN_CONF.format(**self.fields)
        self.assertIn("port:                   11119", text)
        self.assertIn("bindaddress:            127.0.0.1", text)
        self.assertNotEqual(inn_lab.INN_PORT, inn_lab.FN_PORT)
        self.assertNotEqual(inn_lab.NNRPD_PORT, inn_lab.FN_PORT)

    def test_innfeed_names_the_port_the_fn_node_is_started_on(self):
        self.assertIn("port-number:         11190",
                      inn_lab.INNFEED_CONF.format(**self.fields))

    def test_the_me_entry_carries_the_exclusion_that_makes_a_loop_a_437(self):
        line = [one for one in inn_lab.NEWSFEEDS.format(**self.fields).splitlines()
                if one.startswith("ME/")]
        self.assertEqual(len(line), 1, line)
        self.assertIn(inn_lab.INN_PATH_IDENTITY, line[0])
        self.assertNotIn(inn_lab.FN_PATH_IDENTITY, line[0],
                         "excluding fn's own identity would refuse every article "
                         "fn ever feeds, not just a loop")

    def test_incoming_conf_has_no_identity_key(self):
        # inncheck rejects `identity` outright; specs/peering.md section 5 puts
        # the site name in newsfeeds instead, and this is that correction.
        self.assertNotIn("identity:", inn_lab.INCOMING_CONF)
        self.assertIn("patterns:        fn.*", inn_lab.INCOMING_CONF)


class DryRun:
    """One whole lab run against a fake host and a fake INN in a temporary HOME."""

    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="fn-inn-lab-")
        base = Path(cls.temp.name)
        cls.home = base / "home"
        acl2 = cls.home / "fn-tools/acl2-8.7"
        acl2.mkdir(parents=True)
        (acl2 / "saved_acl2").write_text(FAKE_ACL2)
        (acl2 / "saved_acl2").chmod(0o755)
        cls.inn = base / "inn/2.7.4"
        shutil.copytree(ROOT / "tests/inn_lab_fake", cls.inn)
        for one in (cls.inn / "bin").iterdir():
            one.chmod(0o755)
        (cls.inn / "etc").mkdir(exist_ok=True)
        (base / "inn/src").mkdir(parents=True, exist_ok=True)
        (base / "inn/src/inn-2.7.4.tar.gz.sha256").write_text(
            "0000fake0000  inn-2.7.4.tar.gz\n")
        # A farm gate runs from a `git archive` tree with no repository; the
        # fake-host run needs only a revision string, so fall back to a fixed one.
        try:
            commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                                    stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                    check=True).stdout.decode().strip()
        except (subprocess.CalledProcessError, FileNotFoundError):
            commit = "0123456789abcdef0123456789abcdef01234567"
        cls.rev = commit[:7]
        books = cls.home / "fn-gates/dev-{}/books".format(cls.rev)
        books.mkdir(parents=True)
        (books / "acceptance.cert").write_text("(:CERT fake)\n")
        (books / "acceptance.port").write_text("()\n")
        cls.evidence = base / "inn-lab-evidence.md"
        cls.ports = [free_port() for _ in range(3)]
        argv = [commit, "--dry-run", "--home", str(cls.home), "--repo", str(ROOT),
                "--evidence", str(cls.evidence), "--keep",
                "--inn-prefix", str(cls.inn),
                "--gate-root", "$HOME/fn-gates",
                "--acl2", "$HOME/fn-tools/acl2-8.7/saved_acl2",
                "--inn-port", str(cls.ports[0]),
                "--nnrpd-port", str(cls.ports[1]),
                "--fn-port", str(cls.ports[2]),
                "--overlay", str(ROOT / "tests/deploy_gate_fake")]
        os.environ["PATH"] = "{}:{}".format(cls.inn / "bin", os.environ["PATH"])
        cls.code = inn_lab.main(argv)
        cls.text = cls.evidence.read_text()

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def named(self, fragment):
        return [line for line in self.text.splitlines()
                if line.startswith("| ") and fragment in line]

    def failures(self):
        return [line for line in self.text.splitlines() if " FAIL " in line]

    def inn_spool(self):
        return json.loads((self.inn / "db/spool.json").read_text())


class LabTests(DryRun, unittest.TestCase):

    def test_every_message_id_carries_this_run_s_tag(self):
        # INN's history is not reset between runs, so a fixed Message-ID would
        # make the second run of the transfer scenario a duplicate.
        ids = inn_lab.message_ids("abc1234-20260920T000000Z")
        self.assertEqual(len(set(ids.values())), len(inn_lab.ID_TEMPLATES))
        for one in ids.values():
            self.assertIn("abc1234-20260920T000000Z", one)
        self.assertIn("<inn-lab-fed-", self.text)

    def test_the_lab_is_green_against_a_tree_with_no_transit_surface(self):
        self.assertEqual(self.code, 0, "\n".join(self.failures()) or self.text[-4000:])
        self.assertNotIn("lab error", self.text)

    def test_the_configuration_on_disk_is_the_configuration_in_the_tool(self):
        for name in inn_lab.CONFIG_FILES:
            self.assertTrue((self.inn / "etc" / name).exists(), name)
            self.assertTrue(self.named("INN {} as written".format(name)), name)
        self.assertIn("port-number:", (self.inn / "etc/innfeed.conf").read_text())
        self.assertIn("ME/", (self.inn / "etc/newsfeeds").read_text())

    def test_the_port_scheme_is_recorded_and_the_three_ports_differ(self):
        row = self.named("| ports |")
        self.assertTrue(row, self.text[:3000])
        self.assertEqual(len(set(self.ports)), 3)

    def test_an_article_crossed_into_inn_and_reads_back_from_nnrpd(self):
        row = self.named("| ihave |")
        self.assertTrue(row, self.text[-4000:])
        self.assertIn("transfer=235", row[0])
        self.assertTrue([one for one in self.inn_spool()["articles"]
                         if one.startswith("<inn-lab-fed-")],
                        self.inn_spool()["articles"])
        accepted = self.named("INN accepted the transfer with 235")
        self.assertTrue(accepted and "| 0 |" in accepted[0], accepted)
        read = self.named("nnrpd served the article the transit path stored")
        self.assertTrue(read and "| 0 |" in read[0], read)

    def test_the_duplicate_is_435_and_the_path_loop_is_437(self):
        row = self.named("| ihave |")[0]
        self.assertIn("duplicate=435", row)
        self.assertIn("loop=437", row)
        self.assertFalse([one for one in self.inn_spool()["articles"]
                          if one.startswith("<inn-lab-loop-")],
                         "the loop article was stored by INN")

    def test_the_absent_fn_transit_surface_is_a_skip_and_never_a_pass(self):
        self.assertIn("peering: not available on this tree", self.text)
        for name in ("INN's innfeed transfers an article to fn",
                     "the article INN fed is served by the fn node"):
            rows = self.named(name)
            self.assertTrue(rows, "{} is missing".format(name))
            self.assertIn("not exercised", rows[0], rows)
        self.assertIn("cxnsleep response unknown", self.text,
                      "the skip must say what INN's innfeed does with the reply")
        offer = self.named("| offer |")
        self.assertTrue(offer and "500" in offer[0], offer)

    def test_the_fn_node_was_killed_recovered_and_reread(self):
        self.assertTrue(self.named("kill -9 the fn node mid-"), self.text[-3000:])
        gone = self.named("the fn node is gone")
        self.assertTrue(gone and "GONE" in gone[0], gone)
        self.assertTrue(self.named("fn recover after the kill"))
        held = self.named("the fn node still holds <inn-lab-fn-seed-")
        self.assertTrue(held and "| 0 |" in held[0], held)
        lost = self.named("the fn node does not hold the interrupted")
        self.assertTrue(lost and "| 1 |" in lost[0], lost)

    def test_innd_was_killed_and_its_history_survived(self):
        self.assertTrue(self.named("kill -9 innd"), self.text[-3000:])
        back = self.named("restart innd after the kill")
        self.assertTrue(back and "INND-UP" in back[0], back)
        survived = self.named("INN's history survived the SIGKILL")
        self.assertTrue(survived and "| 0 |" in survived[0], survived)

    def test_the_three_outcomes_stay_distinct_on_the_fn_node(self):
        self.assertIn("| three outcomes | accepted=0 refused=1 uncertain=3", self.text)
        self.assertIn("asserted in neither direction", self.text)

    def test_the_evidence_has_the_deploy_gate_s_shape(self):
        for heading in ("## What ran", "## Every command", "### Commands in full",
                        "## What was NOT exercised", "## Raw step output"):
            self.assertIn(heading, self.text)
        self.assertIn("ACL2 Version 8.7 fake", self.text)
        self.assertIn("| inn version |", self.text)
        self.assertIn("| inn tarball sha256 |", self.text)
        self.assertIn("INN and fn are on ONE host", self.text)

    def test_the_reader_gap_names_whose_client_it_was(self):
        self.assertIn("the reader here is the lab's raw-socket client, not fn",
                      self.text)

    def test_the_box_is_left_clean_and_the_install_is_left_alone(self):
        clean = self.named("stray lab processes")
        self.assertTrue(clean and "CLEAN" in clean[0], clean)
        kept = self.named("the INN install is left in place")
        self.assertTrue(kept and "INN-KEPT" not in "".join(self.failures()), kept)
        self.assertTrue((self.inn / "bin/innd").exists())
        gone = self.named("innd and innfeed are gone")
        self.assertTrue(gone, self.text[-2000:])


if __name__ == "__main__":
    unittest.main()
