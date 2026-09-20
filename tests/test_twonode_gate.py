"""tools/twonode_gate.py against local fake hosts: no ssh, no ACL2, no network.

Two runs of the whole gate are under test, because the gate has to be right in
both of the worlds it will meet.

* `NoTransitTests` runs it against the deploy gate's fake reader, which has no
  transit surface -- the world of this tree today.  The feed scenario must
  record "peering: not available on this tree" and NOT pass under its own
  name, the independence control must still run with teeth, and the gate must
  come out green: a harness that went red until the peering lane landed would
  simply be switched off.
* `TransitTests` adds `tests/twonode_gate_fake/tools/run_peer.py`, a fake that
  does answer IHAVE, and requires all four teeth: 335/235 for the transfer,
  435 for the second offer, 437 for an article whose Path already names the
  target, and the same octets read back on the far side.

A green run here says the harness works.  It says nothing about fn: every
reply in both scenarios comes from a fake in `tests/`, and the day a real
transit surface lands the gate finds it the same way -- by asking a live
server, never by looking for a file name.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import twonode_gate  # noqa: E402

FAKE_ACL2 = "#!/bin/sh\necho 'ACL2 Version 8.7 fake'\ncat > /dev/null\nexit 0\n"
PEER_SERVER = ("python3 tools/run_peer.py --store {store} --port 0 --post "
               "--path-identity {node}.gate.example.invalid")


class PeerRecordTests(unittest.TestCase):
    """The stub is the record kind of specs/peering.md 1.2, not a note."""

    def gate(self):
        return twonode_gate.TwoNodeGate(twonode_gate.LocalHost(Path("/tmp/unused-fn")),
                                        ROOT, "a" * 40, "abc1234", "dev")

    def test_the_stub_carries_every_field_of_fn_cfg_peerp(self):
        gate = self.gate()
        gate.b.port = 4119
        text = gate.peer_stub(gate.a, gate.b).decode()
        self.assertIn("(fn-cfg-peer-make", text)
        self.assertIn('"b.gate.example.invalid"', text)     # path-identity
        self.assertIn('(:nntp "127.0.0.1" 4119)', text)     # transport
        self.assertIn('(("fn.*") 1048576 4)', text)         # inbound
        self.assertIn('(("fn.*") nil 64 1000)', text)       # outbound
        self.assertIn("(:source-address", text)             # auth
        self.assertIn("NOTHING ON THIS TREE READS THIS FILE", text)

    def test_a_missing_peer_cli_is_a_skip_and_never_a_pass(self):
        gate = self.gate()
        gate.skip("node A peer record for B", "cli",
                  "peer record: not available on this tree")
        self.assertIsNone(gate.steps[0].rc)
        self.assertFalse(gate.steps[0].exercised)
        self.assertTrue(any("not available on this tree" in gap for gap in gate.gaps))


class DryRun:
    """One whole gate run against a fake host in a temporary HOME."""

    overlays = ["tests/deploy_gate_fake"]
    server_command = None

    @classmethod
    def run_gate(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="fn-twonode-gate-")
        cls.home = Path(cls.temp.name) / "home"
        acl2 = cls.home / "fn-tools/acl2-8.7"
        acl2.mkdir(parents=True)
        (acl2 / "saved_acl2").write_text(FAKE_ACL2)
        (acl2 / "saved_acl2").chmod(0o755)
        # A farm gate runs from a `git archive` tree with no repository.
        # Unlike test_deploy_gate, which needs only a revision string, this
        # harness exports the tree with `git archive <rev>`: without a
        # repository there is nothing to export, so the case is skipped rather
        # than reported as a gate failure.
        try:
            commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                                    stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                    check=True).stdout.decode().strip()
        except (subprocess.CalledProcessError, FileNotFoundError) as error:
            raise unittest.SkipTest(
                "gate harness exports the tree with `git archive`; "
                "this checkout is not a git repository") from error
        cls.rev = commit[:7]
        books = cls.home / "fn-gates/dev-{}/books".format(cls.rev)
        books.mkdir(parents=True)
        (books / "acceptance.cert").write_text("(:CERT fake)\n")
        (books / "acceptance.port").write_text("()\n")
        cls.evidence = Path(cls.temp.name) / "twonode-evidence.md"
        argv = [commit, "--dry-run", "--home", str(cls.home), "--repo", str(ROOT),
                "--evidence", str(cls.evidence), "--keep"]
        for overlay in cls.overlays:
            argv += ["--overlay", str(ROOT / overlay)]
        if cls.server_command:
            argv += ["--server-command", cls.server_command]
        cls.code = twonode_gate.main(argv)
        cls.text = cls.evidence.read_text()

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def named(self, fragment):
        return [line for line in self.text.splitlines()
                if line.startswith("| ") and fragment in line]

    def store(self, node):
        path = self.home / "fn-deploy/{}/{}/store/store.json".format(self.rev, node)
        return json.loads(path.read_text())

    def ids(self, node):
        return {article["msgid"] for article in self.store(node)["articles"]}

    def failures(self):
        return [line for line in self.text.splitlines() if " FAIL " in line]


class NoTransitTests(DryRun, unittest.TestCase):
    """The tree as it is today: two nodes that cannot reach each other."""

    @classmethod
    def setUpClass(cls):
        cls.run_gate()

    def test_the_gate_is_green_without_a_transit_surface(self):
        self.assertEqual(self.code, 0, "\n".join(self.failures()) or self.text[-3000:])
        self.assertNotIn("gate error", self.text)

    def test_two_nodes_on_two_ports_with_two_stores(self):
        rows = self.named("| node a |") + self.named("| node b |")
        self.assertEqual(len(rows), 2, rows)
        ports = [row.split("on port ")[1].split()[0] for row in rows]
        self.assertNotEqual(ports[0], ports[1], rows)
        self.assertEqual(set(self.store("a")["groups"]), set(twonode_gate.GROUPS))
        self.assertEqual(set(self.store("b")["groups"]), set(twonode_gate.GROUPS))

    def test_the_independence_control_ran_with_teeth(self):
        for name in ("independent: node A holds its own and not B's",
                     "independent: node B holds its own and not A's"):
            rows = self.named(name)
            self.assertTrue(rows, "{} is missing from the evidence".format(name))
            self.assertIn("| 0 |", rows[0], rows)
        self.assertIn(twonode_gate.ARTICLE_A, self.ids("a"))
        self.assertIn(twonode_gate.ARTICLE_B, self.ids("b"))
        self.assertNotIn(twonode_gate.ARTICLE_A, self.ids("b"))
        self.assertNotIn(twonode_gate.ARTICLE_B, self.ids("a"))

    def test_the_absent_feed_is_a_gap_and_three_skipped_steps(self):
        self.assertIn("peering: not available on this tree", self.text)
        for name in ("feed: {} reread on B".format(twonode_gate.ARTICLE_A),
                     "feed: a second IHAVE of",
                     "feed: an article whose Path names B is refused"):
            rows = self.named(name)
            self.assertTrue(rows, "{} is missing".format(name))
            self.assertIn("not exercised", rows[0], rows)
        self.assertNotIn(twonode_gate.ARTICLE_A, self.ids("b"),
                         "nothing may have crossed without a transit surface")

    def test_the_peer_record_is_a_stub_and_says_so(self):
        rows = self.named("node A peer record for B")
        self.assertTrue(rows and "not exercised" in rows[0], rows)
        stub = self.home / "fn-deploy/{}/a/peers/b.peer".format(self.rev)
        self.assertIn("fn-cfg-peer-make", stub.read_text())

    def test_the_kill_landed_in_a_post_and_b_recovered(self):
        self.assertTrue(self.named("kill -9 node B mid-post"), self.text[-2000:])
        gone = self.named("node B is gone")
        self.assertTrue(gone and "GONE" in gone[0], gone)
        survived = self.named("node A survived node B's death")
        self.assertTrue(survived and "ALIVE" in survived[0], survived)
        self.assertTrue(self.named("reread node B after recovery"))
        self.assertIn(twonode_gate.ARTICLE_B, self.ids("b"))
        self.assertNotIn(twonode_gate.INTERRUPTED_ID, self.ids("b"))

    def test_the_three_outcomes_stay_distinct_on_both_nodes(self):
        for node in ("a", "b"):
            self.assertIn("| three outcomes {} | accepted=0 refused=1 uncertain=3".format(
                node), self.text)

    def test_an_indeterminate_outcome_is_asserted_in_neither_direction(self):
        self.assertIn("asserted in neither direction", self.text)

    def test_the_evidence_has_the_deploy_gate_s_shape(self):
        for heading in ("## What ran", "## Every command", "### Commands in full",
                        "## What was NOT exercised", "## Raw step output"):
            self.assertIn(heading, self.text)
        self.assertIn("ACL2 Version 8.7 fake", self.text)
        self.assertIn("| python3 |", self.text)
        self.assertIn("Both nodes are on ONE host", self.text)

    def test_the_box_is_left_clean(self):
        clean = self.named("stray fn processes")
        self.assertTrue(clean and "CLEAN" in clean[0], clean)


class TransitTests(DryRun, unittest.TestCase):
    """The tree with a transit surface: the four teeth must all bite."""

    overlays = ["tests/deploy_gate_fake", "tests/twonode_gate_fake"]
    server_command = PEER_SERVER

    @classmethod
    def setUpClass(cls):
        cls.run_gate()

    def test_the_gate_is_green_with_a_transit_surface(self):
        self.assertEqual(self.code, 0, "\n".join(self.failures()) or self.text[-4000:])
        self.assertNotIn("gate error", self.text)

    def test_the_article_crossed_and_reads_back_identically(self):
        row = self.named("| transit |")
        self.assertTrue(row and "335" in row[0], row)
        feed = self.named("| feed |")
        self.assertTrue(feed, self.text[-3000:])
        self.assertIn("transfer=235", feed[0])
        self.assertIn("reread=220", feed[0])
        self.assertIn("identical=True", feed[0])
        self.assertIn(twonode_gate.ARTICLE_A, self.ids("b"),
                      "the offered article is not in node B's store")

    def test_the_second_offer_is_refused_by_the_message_id_history(self):
        self.assertIn("duplicate=435", self.named("| feed |")[0])
        self.assertEqual(
            [a["msgid"] for a in self.store("b")["articles"]].count(
                twonode_gate.ARTICLE_A), 1, "the article crossed twice")

    def test_a_loop_is_refused_and_leaves_nothing_behind(self):
        self.assertIn("loop=437", self.named("| feed |")[0])
        self.assertNotIn(twonode_gate.LOOP_ID, self.ids("b"))

    def test_the_kill_landed_inside_the_transfer(self):
        self.assertTrue(self.named("kill -9 node B mid-transit"), self.text[-2000:])
        self.assertNotIn(twonode_gate.INTERRUPTED_ID, self.ids("b"))
        self.assertIn(twonode_gate.ARTICLE_A, self.ids("b"),
                      "the article B acknowledged before the kill was lost")
        self.assertIn(twonode_gate.ARTICLE_B, self.ids("b"))

    def test_node_a_is_unchanged_by_all_of_it(self):
        rows = self.named("node A is unchanged by node B's death")
        self.assertTrue(rows and "| 0 |" in rows[0], rows)
        self.assertNotIn(twonode_gate.ARTICLE_B, self.ids("a"))

    def test_the_feed_steps_are_not_skipped_when_the_surface_is_there(self):
        self.assertNotIn("peering: not available on this tree", self.text)
        rows = self.named("feed: {} reread on B".format(twonode_gate.ARTICLE_A))
        self.assertTrue(rows and "| 0 |" in rows[0], rows)


if __name__ == "__main__":
    unittest.main()
