#!/usr/bin/env python3
"""`tools/gate_reap.py`: the policy, and the guards on an irreversible step.

The reaper's one dangerous act is `rm -rf` on a box, so everything that
decides whether a directory is removable is a pure function over a listing
(`verdicts`) and is exercised here against listings this file writes.  No
box, no ssh, no ACL2.  The probe itself -- reading /proc and du on the far
side -- is not faked: what it returns is the input to every case below, and
a run against a real box is the only thing that establishes it.
"""
from __future__ import annotations

import json
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import gate_reap  # noqa: E402

NOW = 1_700_000_000.0
HOUR = 3600.0


def gate(name, hours, live=(), certs=100, kilobytes=50000):
    return {"name": name, "path": "/gates/" + name, "mtime": NOW - hours * HOUR,
            "kilobytes": kilobytes, "certs": certs, "live": list(live)}


def listing(gates, locked="no", proc=True):
    return {"root": "/gates", "locked": locked, "proc": proc, "gates": gates,
            "memory": {}}


ALL_ANCESTORS = {"aaaaaaa": "ancestor", "bbbbbbb": "ancestor", "ccccccc": "ancestor",
                 "ddddddd": "ancestor", "eeeeeee": "ancestor", "fffffff": "ancestor"}


def verdicts(gates, ancestors=None, locked="no", proc=True, min_age=24.0,
             keep_recent=0, include_unknown=False):
    return {row["name"]: row for row in gate_reap.verdicts(
        listing(gates, locked, proc), ancestors or ALL_ANCESTORS, NOW,
        min_age, keep_recent, include_unknown)}


class PolicyTests(unittest.TestCase):

    def test_a_gate_with_a_process_in_it_is_live_and_never_stale(self):
        # The case the tool exists for: three ACL2 children of a retired
        # gate survived 19 hours at 0% CPU.  Old, landed, and not removable.
        rows = verdicts([gate("dev-aaaaaaa", 19.0,
                              live=[{"pid": 111, "cmd": "saved_acl2"}])])
        self.assertEqual(rows["dev-aaaaaaa"]["verdict"], "live")
        self.assertIn("111", rows["dev-aaaaaaa"]["reason"])

    def test_a_process_in_a_subdirectory_makes_the_gate_live(self):
        # The probe attributes a cwd under the gate to the gate; this pins
        # that the row it produces is treated as live and not merely noted.
        rows = verdicts([gate("dev-aaaaaaa", 99.0,
                              live=[{"pid": 7, "cmd": "acl2"}])])
        self.assertEqual(rows["dev-aaaaaaa"]["verdict"], "live")

    def test_an_old_landed_process_free_gate_is_stale(self):
        rows = verdicts([gate("dev-aaaaaaa", 40.0)])
        self.assertEqual(rows["dev-aaaaaaa"]["verdict"], "stale")
        self.assertIn("ancestor of dev", rows["dev-aaaaaaa"]["reason"])

    def test_a_young_gate_is_kept_however_landed_it_is(self):
        rows = verdicts([gate("dev-aaaaaaa", 23.9)])
        self.assertEqual(rows["dev-aaaaaaa"]["verdict"], "keep")
        self.assertIn("floor", rows["dev-aaaaaaa"]["reason"])

    def test_a_branch_that_has_not_landed_is_kept(self):
        rows = verdicts([gate("w2-bbbbbbb", 500.0)],
                        ancestors={"bbbbbbb": "present-not-ancestor"})
        self.assertEqual(rows["w2-bbbbbbb"]["verdict"], "keep")
        self.assertIn("not an ancestor", rows["w2-bbbbbbb"]["reason"])

    def test_a_revision_git_does_not_know_is_kept_unless_asked_for(self):
        # The export may be the only copy of that tree, so the default is to
        # keep it and say why; `--include-unknown` is the operator saying so.
        unknown = {"ccccccc": "unknown"}
        rows = verdicts([gate("dev-ccccccc", 500.0)], ancestors=unknown)
        self.assertEqual(rows["dev-ccccccc"]["verdict"], "keep")
        self.assertIn("only copy", rows["dev-ccccccc"]["reason"])
        rows = verdicts([gate("dev-ccccccc", 500.0)], ancestors=unknown,
                        include_unknown=True)
        self.assertEqual(rows["dev-ccccccc"]["verdict"], "stale")

    def test_the_newest_gates_of_each_tree_are_protected_per_tree(self):
        rows = verdicts([gate("dev-aaaaaaa", 30.0), gate("dev-bbbbbbb", 40.0),
                         gate("dev-ccccccc", 50.0), gate("w2-ddddddd", 60.0)],
                        keep_recent=2)
        self.assertEqual(rows["dev-aaaaaaa"]["verdict"], "keep")
        self.assertEqual(rows["dev-bbbbbbb"]["verdict"], "keep")
        self.assertEqual(rows["dev-ccccccc"]["verdict"], "stale")
        # `w2` is its own tree and its single gate is the newest of it.
        self.assertEqual(rows["w2-ddddddd"]["verdict"], "keep")

    def test_a_held_box_lock_keeps_everything(self):
        rows = verdicts([gate("dev-aaaaaaa", 90.0), gate("dev-bbbbbbb", 90.0)],
                        locked="yes")
        self.assertEqual({row["verdict"] for row in rows.values()}, {"keep"})
        self.assertIn("certification is running", rows["dev-aaaaaaa"]["reason"])

    def test_a_box_with_no_proc_keeps_everything(self):
        # No /proc is no way to rule a process out, and "I could not check"
        # must not read the same as "nothing is running".
        rows = verdicts([gate("dev-aaaaaaa", 90.0)], proc=False)
        self.assertEqual(rows["dev-aaaaaaa"]["verdict"], "keep")
        self.assertIn("no /proc", rows["dev-aaaaaaa"]["reason"])

    def test_a_directory_whose_name_carries_no_revision_is_kept(self):
        rows = verdicts([gate("scratch", 900.0)])
        self.assertEqual(rows["scratch"]["verdict"], "keep")
        self.assertIsNone(rows["scratch"]["rev"])

    def test_every_row_carries_the_four_facts_the_listing_promises(self):
        rows = verdicts([gate("dev-aaaaaaa", 40.0, certs=138, kilobytes=64512)])
        row = rows["dev-aaaaaaa"]
        self.assertEqual(row["rev"], "aaaaaaa")
        self.assertEqual(row["ancestor"], "ancestor")
        self.assertEqual(row["age_hours"], 40.0)
        self.assertEqual(row["certs"], 138)
        self.assertEqual(row["kilobytes"], 64512)


class FakeHost:
    label = "fake"

    def __init__(self, stdout=b"", rc=0):
        self.scripts = []
        self.stdout, self.rc = stdout, rc

    def sh(self, script, timeout):
        self.scripts.append(script)
        return subprocess.CompletedProcess([], self.rc, self.stdout)


class RemovalTests(unittest.TestCase):

    def rows(self, **kwargs):
        return list(verdicts([gate("dev-aaaaaaa", 40.0)], **kwargs).values())

    def test_removal_names_one_directory_under_the_root_it_was_given(self):
        host = FakeHost(b"REMOVED dev-aaaaaaa\n")
        done = gate_reap.remove(host, "/gates", self.rows())
        self.assertEqual(len(host.scripts), 1)
        self.assertIn('rm -rf -- "$R/dev-aaaaaaa"', host.scripts[0])
        self.assertIn('R="/gates"', host.scripts[0])
        self.assertEqual(done[0]["name"], "dev-aaaaaaa")
        self.assertEqual(done[0]["rc"], 0)

    def test_removal_refuses_a_row_that_is_not_stale(self):
        host = FakeHost()
        for verdict in ("live", "keep"):
            row = dict(self.rows()[0], verdict=verdict)
            with self.assertRaises(gate_reap.ReapError):
                gate_reap.remove(host, "/gates", [row])
        self.assertEqual(host.scripts, [])

    def test_removal_refuses_a_name_that_could_widen_the_target(self):
        host = FakeHost()
        for name in ("", ".", "..", "../..", "a/b", "-rf"):
            row = dict(self.rows()[0], name=name)
            with self.assertRaises(gate_reap.ReapError):
                gate_reap.remove(host, "/gates", [row])
        self.assertEqual(host.scripts, [])

    def test_a_live_gate_never_reaches_removal_through_main_s_filter(self):
        # main() passes only the stale rows; this is that filter, spelled out
        # so a future edit that widens it fails here.
        rows = list(verdicts([gate("dev-aaaaaaa", 40.0,
                                   live=[{"pid": 3, "cmd": "acl2"}]),
                              gate("dev-bbbbbbb", 40.0)]).values())
        stale = [row for row in rows if row["verdict"] == "stale"]
        self.assertEqual([row["name"] for row in stale], ["dev-bbbbbbb"])


class ProbeTests(unittest.TestCase):

    def test_the_probe_reads_the_root_and_the_lock_it_is_given(self):
        host = FakeHost(json.dumps({"root": "/gates", "gates": [],
                                    "locked": "no", "proc": True,
                                    "memory": {}}).encode())
        answer = gate_reap.probe(host, "/tank/fn/gates", "/tank/fn/gates/.lock")
        self.assertIn('FN_GATE_ROOT="/tank/fn/gates"', host.scripts[0])
        self.assertIn('FN_GATE_LOCK="/tank/fn/gates/.lock"', host.scripts[0])
        self.assertEqual(answer["gates"], [])
        # The probe is a python heredoc: its own braces must survive intact.
        self.assertIn('out = {"root": root', host.scripts[0])

    def test_output_that_is_not_a_listing_raises_and_shows_the_tail(self):
        host = FakeHost(b"bash: python3: command not found\n")
        with self.assertRaises(gate_reap.ReapError) as caught:
            gate_reap.probe(host, "/gates", "/gates/.lock")
        self.assertIn("command not found", str(caught.exception))


class AncestryTests(unittest.TestCase):
    """Against this repository, which is the authority a gate directory lacks."""

    def test_head_is_an_ancestor_of_dev_and_a_made_up_sha_is_unknown(self):
        head = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--short", "HEAD"],
                              stdout=subprocess.PIPE).stdout.decode().strip()
        answer = gate_reap.ancestry(ROOT, [head, "0123456789ab"])
        self.assertEqual(answer["0123456789ab"], "unknown")
        self.assertIn(answer[head], ("ancestor", "present-not-ancestor"))


class RenderTests(unittest.TestCase):

    def test_the_table_names_every_gate_and_totals_what_is_freeable(self):
        gates = [gate("dev-aaaaaaa", 40.0, kilobytes=1048576),
                 gate("dev-bbbbbbb", 1.0, kilobytes=1048576)]
        rows = list(verdicts(gates).values())
        text = gate_reap.render(listing(gates), rows)
        self.assertIn("dev-aaaaaaa", text)
        self.assertIn("dev-bbbbbbb", text)
        self.assertIn("1 stale (1.0 G freeable)", text)

    def test_the_memory_line_says_not_to_read_free(self):
        report = listing([])
        report["memory"] = {"mem_total_kb": 128 * 1048576, "anon_pages_kb": 1258291,
                            "rss_sum_kb": 2831155, "arc_kb": 47290942}
        text = gate_reap.render(report, [])
        self.assertIn("AnonPages", text)
        self.assertIn("RSS sum", text)
        self.assertIn("ARC", text)
        self.assertIn("free", text)


if __name__ == "__main__":
    unittest.main()
