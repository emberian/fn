"""D27, PRF-171, SCN-101: a peer's carried rows grow past the old 1,024.

Before PRF-171 every `peer carries NAME HEX` published the peer's WHOLE row
group as one (:set-peer NAME ROWS) delta, so a peer stopped at
`*fn-cfg-max-rows*` (1,024) rows: its carried principals were data capped by
a constant.  Now each request publishes only its own rows, (:add-peer-rows
NAME ROWS) (books/peer-carriage-rows.lisp `fn-pcb-extend-deltas', through
books/native-admin.lisp `fn-native-admin-plan-deltas-over' from
host/native-admin-host.lisp `fn-native-admin-host-apply'), and 1,024 is the
work bound of one delta (`fn-cfg-add-peer-rows-refuses-exactly-past-the-work-
bound').

On the developer image, offline: `init` with room for the requests
(`--max-transactions` and `--max-config-generations`), `peer add far ...`,
then N separate `peer carries far HEX` requests (N = 1,100 by default,
FN_PEER_ROWS_REQUESTS to change it), each accepted; `peer list` (a fresh open
that replays every configuration record) lists all N principals in request
order; `peer budget far ...` twice over the grown group (the second
publishes :remove-peer-rows for the first's two rows) keeps every
principal; repeating a principal adds no row.
"""
import os
import time
import unittest

from tests import test_native_operator_verbs as verbs

EXIT_OK = verbs.EXIT_OK
REQUESTS = int(os.environ.get("FN_PEER_ROWS_REQUESTS", "1100"))


def principal(k):
    return "{:064x}".format(k + 1)


@unittest.skipUnless(verbs.executable(verbs.DEVELOPER), "the developer image is required")
class NativePeerRowsGrowthTests(verbs.NativeOperatorVerbFixture):
    def operator(self, *words, **kwargs):
        return super().operator(*words, image=verbs.DEVELOPER, **kwargs)

    def ok(self, *words):
        result = self.operator(*words)
        self.assertEqual(result.returncode, EXIT_OK,
                         "{}: {}".format(" ".join(words[:3]),
                                         result.stderr.decode(errors="replace")))
        return result

    def carried(self):
        listed = self.ok("peer", "list")
        lines = listed.stdout.decode("ascii").splitlines()
        self.assertEqual(len(lines), 1, listed.stdout[:400])
        words = lines[0].split()
        return ([w.split("=", 1)[1] for w in words
                 if w.startswith("carries-principal=")], lines[0])

    def test_a_peer_carries_more_than_the_old_row_cap(self):
        room = str(REQUESTS + 64)
        self.ok("init", "--max-transactions", room,
                "--max-config-generations", room, "fn.test")
        self.ok("peer", "add", "far", "far.example.invalid", "192.0.2.44",
                "1119", "fn.*", "-", "192.0.2.44", "true")
        started = time.monotonic()
        for k in range(REQUESTS):
            self.ok("peer", "carries", "far", principal(k))
        elapsed = time.monotonic() - started
        print("peer-rows-growth: {} requests in {:.1f} s".format(REQUESTS, elapsed))

        carried, _ = self.carried()
        self.assertEqual(carried, [principal(k) for k in range(REQUESTS)])
        if REQUESTS >= 1100:
            self.assertGreater(len(carried), 1024)

        # A single-valued slot over the grown group: the old budget rows go,
        # the principals stay.
        self.ok("peer", "budget", "far", "1048576", "3")
        self.ok("peer", "budget", "far", "2097152", "5")
        carried_after, _ = self.carried()
        self.assertEqual(carried_after, carried)

        # Repeating a principal adds nothing (the row moves to the end, as
        # the whole-group extension always did).
        self.ok("peer", "carries", "far", principal(0))
        carried_again, _ = self.carried()
        self.assertEqual(len(carried_again), REQUESTS)
        self.assertEqual(sorted(carried_again), sorted(carried))


OLD_IMAGE = os.environ.get("FN_OLD_IMAGE")


@unittest.skipUnless(verbs.executable(verbs.DEVELOPER), "the developer image is required")
class NativePeerRowsLiveTests(verbs.NativeOperatorVerbFixture):
    """PKT-451 (4) and (5): the live owner's arm, and an older image's refusal.

    With a node running, `peer carries` and `peer budget` reach the owner
    over the control socket (host/native/control.lisp -> host/native/admin.lisp
    `fnn-owner-live-admin-serialized' -> host/native-admin-host.lisp
    `fn-native-admin-host-owner-reconfigure', the same
    `fn-native-admin-plan-deltas-over'), so the owner publishes
    :add-peer-rows (code 18) and, for the second budget, :remove-peer-rows
    (code 19).  After the owner stops, `peer list' (a fresh open replaying
    every record) names the principals and the second budget.  When
    FN_OLD_IMAGE names an image from before the two codes (bbf52159), that
    image refuses the store at open and opens a fresh store (the control):
    the rollback sentence in docs/operator.md.
    """
    start_owner = verbs.NativeOperatorUncertainOutcomeTests.start_owner
    reap = verbs.NativeOperatorUncertainOutcomeTests.reap

    def setUp(self):
        super().setUp()
        self.control = self.root / "control.sock"
        self.config.write_text(
            '[store]\npath = "{}"\n'
            '[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, verbs.free_port(),
                                               self.control),
            encoding="ascii")

    def operator(self, *words, **kwargs):
        kwargs.setdefault("image", verbs.DEVELOPER)
        return super().operator(*words, **kwargs)

    def ok(self, *words):
        result = self.operator(*words)
        self.assertEqual(result.returncode, EXIT_OK,
                         "{}: {}".format(" ".join(words[:3]),
                                         result.stderr.decode(errors="replace")))
        return result

    def test_the_live_owner_extends_a_peer_and_an_older_image_refuses_it(self):
        self.ok("init", "fn.test")
        owner = self.start_owner(verbs.DEVELOPER)
        self.ok("peer", "add", "far", "far.example.invalid", "192.0.2.44",
                "1119", "fn.*", "-", "192.0.2.44", "true")
        for k in range(3):
            self.ok("peer", "carries", "far", principal(k))
        self.ok("peer", "budget", "far", "1048576", "3")
        self.ok("peer", "budget", "far", "2097152", "5")
        owner.send_signal(verbs.signal.SIGTERM)
        self.assertEqual(owner.wait(timeout=60), EXIT_OK,
                         owner.stderr.read().decode("utf-8", "replace"))
        listed = self.ok("peer", "list").stdout.decode("ascii")
        words = listed.split()
        self.assertEqual([w.split("=", 1)[1] for w in words
                          if w.startswith("carries-principal=")],
                         [principal(k) for k in range(3)])
        self.assertIn("2097152", listed)
        self.assertNotIn("1048576", listed)
        print("peer-rows-live:", listed.strip()[:300])
        if OLD_IMAGE:
            def old_status(store, name):
                config = self.root / (name + ".toml")
                config.write_text('[store]\npath = "{}"\n[listener]\n'
                                  'host = "127.0.0.1"\nport = {}\n'.format(
                                      store, verbs.free_port()), encoding="ascii")
                result = verbs.subprocess.run(
                    [OLD_IMAGE, "--fn", "operator", str(config), "status"],
                    cwd=verbs.ROOT, env=verbs.environment(),
                    stdout=verbs.subprocess.PIPE, stderr=verbs.subprocess.PIPE,
                    timeout=240, check=False)
                print("peer-rows-old-image", name, "->", result.returncode,
                      (result.stdout + result.stderr).decode(
                          "utf-8", "replace")[-200:].replace("\n", " "))
                return result
            fresh = self.root / "fresh"
            fresh_config = self.root / "fresh-new.toml"
            fresh_config.write_text('[store]\npath = "{}"\n[listener]\n'
                                    'host = "127.0.0.1"\nport = {}\n'.format(
                                        fresh, verbs.free_port()), encoding="ascii")
            made = verbs.subprocess.run(
                [str(verbs.DEVELOPER), "--fn", "operator", str(fresh_config),
                 "init", "fn.test"], cwd=verbs.ROOT, env=verbs.environment(),
                stdout=verbs.subprocess.PIPE, stderr=verbs.subprocess.PIPE,
                timeout=240, check=False)
            self.assertEqual(made.returncode, EXIT_OK, made.stderr.decode())
            self.assertEqual(old_status(fresh, "fresh").returncode, EXIT_OK)
            self.assertEqual(old_status(self.store, "extended").returncode,
                             verbs.EXIT_FAULT)


if __name__ == "__main__":
    unittest.main()
