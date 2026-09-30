"""The process heap from the store profile, native (lane heap-from-profile,
2026-09-26; PKT-016; PRF-198; HST-013; SCN-127).

The installed `bin/fn` (packaging/fn with libexec/fn beside it) no longer
runs every command under the image launcher's `--dynamic-space-size 32000`:
it first runs the same image as `heap -- ARGV`, where ACL2 decides the
figure from the command's store profile and this machine's memory
(books/heap-figure.lisp `fn-heap-decide'), and then execs the command with
that figure; a profile the machine cannot hold is refused there by name,
exit 1, and nothing else runs.

The case is the friend's machine: the module runs under a 2 GiB memory
limit (tools/hbox_native.sh --mem 2G: `systemd-run --user --scope -p
MemoryMax=2G`), which the host reads as the machine (the cgroup's
memory.max).  It needs FN_NATIVE_HOST (the production image) and skips, by
name, outside a limit of at most 2 GiB.

* A fresh node: `init' with no profile word takes a conservative preset
  within the budget and prints it (books/heap-reservation.lisp
  fn-heap-init-decide, judging the first run of the empty store it makes:
  reservation-after-flip); the small node here is the small preset's fields
  named at init: `status' prints the next run's figure over the store on
  disk, `heap=N MB profile=small machine=2048 MB'.  The node starts under
  that figure, takes 100 POSTs of
  2 KiB, serves them (ARTICLE, OVER), publishes one automatic checkpoint
  (K = 128: at 64), stops, reopens from the checkpoint and serves them
  again.  Each run's VmHWM is printed.
* The refusal: `init --profile development' is the operator's request,
  never resized: under the launcher and run directly, init refuses it by
  name with both numbers (lane
  membership-budget); `init --budget 16384 --profile scale'
  writes it for that target (`within-budget=no target-budget=16384 MB'),
  and the launcher refuses its `run' and `status' by name (an empty
  development store's run fits 2 GiB since lane heap-bounds, B4).
* FreshInitTests (also without a small limit): conservative sizing,
  `init --largest', `init --budget MB' (below the machine: init
  warns by name with both figures), and the default mission
  (inits and runs, under 2 GiB too; refused by name under a 500 MB budget).
"""
import base64
import hashlib
import os
import resource
import re
import shutil
import socket
import subprocess
import tempfile
import time
import unittest
from pathlib import Path

from tests.native_harness import (
    EXIT_OK, EXIT_REFUSED, EXIT_USAGE, ROOT, Client, Node, article, environment, native_image,
    node_log_on_failure, run)

IMAGE = str(native_image("FN_NATIVE_HOST"))
SMALL_FLAGS = ("--profile", "development", "--max-transactions", "16384",
               "--max-history-octets", "8388608", "--max-record-octets", "196608",
               "--max-groups-per-article", "16", "--max-open-suffix", "128")
# `status' prints the launcher's run reservation (books/heap-reservation.lisp
# fn-heap-status-decide): the heap line with the stack and the threads.
HEAP_LINE = re.compile(r"^heap=(\d+) MB profile=([a-z]+) machine=(\d+) MB"
                       r" stack=\d+ KB threads=\d+$", re.M)
REFUSED = re.compile(
    r"refused machine-cannot-hold-profile heap=(\d+) MB machine=(\d+) MB")
# What `init' prints (books/heap-reservation.lisp fn-heap-init-report-line).
INIT_LINE = re.compile(r"^init: profile=([a-z]+) sizing=([a-z]+) "
                       r"reservation=(\d+) MB budget=(\d+) MB within-budget=(yes|no)$",
                       re.M)
# A named budget below the machine init observes (finding R1 of the
# public-node rehearsal: books/heap-reservation.lisp fn-heap-init-budget-note-line).
INIT_NAMED_BELOW = re.compile(r"fn: warning init-budget-below-machine named-budget=(\d+) MB "
                              r"machine-budget=(\d+) MB: ")
INIT_REFUSED = re.compile(r"refused init-budget-cannot-hold-profile profile=([a-z]+) "
                          r"sizing=([a-z]+) reservation=(\d+) MB budget=(\d+) MB")


def cgroup_limit():
    """The least memory.max from this process's cgroup up, or None."""
    try:
        line = next(l for l in Path("/proc/self/cgroup").read_text().splitlines()
                    if l.startswith("0::"))
    except (OSError, StopIteration):
        return None
    path, found = line[3:], []
    while path and path != "/":
        try:
            text = (Path("/sys/fs/cgroup" + path) / "memory.max").read_text().strip()
            if text.isdigit():
                found.append(int(text))
        except OSError:
            pass
        path = path.rsplit("/", 1)[0]
    return min(found) if found else None


LIMIT = cgroup_limit()
READY = bool(Path(IMAGE).is_file() and Path(IMAGE + ".core").is_file())
SMALL = bool(LIMIT and LIMIT <= 2 * 1024 ** 3)


def text(result):
    return (result.stdout + result.stderr).decode("utf-8", "replace")


def vmhwm(pid):
    for line in Path("/proc/{}/status".format(pid)).read_text().splitlines():
        if line.startswith("VmHWM:"):
            return int(line.split()[1])
    return None


class Harness:
    def setUp(self):
        # A durable mount: a mission's init requires durable storage
        # (store-mount-identity, PKT-670) and /tmp is tmpfs on hbox.
        durable = ROOT / "build" / "test-tmp"
        durable.mkdir(parents=True, exist_ok=True)
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-heap-", dir=durable))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        prefix = self.tmp / "opt" / "fn"
        (prefix / "bin").mkdir(parents=True)
        (prefix / "libexec" / "fn").mkdir(parents=True)
        shutil.copy(ROOT / "packaging" / "fn", prefix / "bin" / "fn")
        os.symlink(IMAGE, prefix / "libexec" / "fn" / "fn-host")
        os.symlink(IMAGE + ".core", prefix / "libexec" / "fn" / "fn-host.core")
        self.fn = str(prefix / "bin" / "fn")

    def config(self, name):
        """The node: the store at tmp/NAME, run through the installed launcher."""
        self.node = Node(self, IMAGE, root=self.tmp, launcher=self.fn, env=self.stripped())
        self.node.store_path = self.tmp / name
        # The control socket in a short directory: under a deep scratch tree
        # store/control.sock passes the 103 octets a Unix socket binds whole
        # everywhere, and `run' is refused :control-path-too-long
        # (books/native-operator.lisp; lane ops-fixes).
        self.node.control = Path(tempfile.mkdtemp(prefix="fnh-")) / "c.sock"
        self.addCleanup(shutil.rmtree, self.node.control.parent, True)
        self.node.write_config()
        return self.node.config, self.node.port

    @staticmethod
    def stripped():
        """What the launcher must not inherit: every FN_NATIVE_/FN_RUN_/
        FN_TEST_ and SBCL_ variable (the launcher sets the stack)."""
        names = [name for name in os.environ
                 if name.startswith(("FN_NATIVE_", "FN_RUN_", "FN_TEST_", "SBCL_"))]
        return dict.fromkeys(names + ["SBCL_USER_ARGS"])

    def env(self, **extra):
        return environment(dict(self.stripped(), **extra), stack=False)

    def run_fn(self, *words, command=None, env=None):
        result = run([*(command or [self.fn]), *words], env=self.env(**(env or {})),
                     timeout=600)
        print("NATIVE-HEAP", " ".join(map(str, words[1:3])), "->", result.returncode,
              text(result).strip().replace("\n", " | ")[-300:])
        return result

    def start(self):
        """The owner, once ITS OWN stdout announced `LISTENING PORT' (a
        greeting read from a released port proves only that somebody
        listens there) and the port greets."""
        owner = self.node.start(timeout=600)
        with Client(self.node.port, timeout=5):
            pass
        return owner

    def stop(self):
        hwm = vmhwm(self.node.process.pid)
        self.node.stop(grace=120)
        return hwm

    def post(self, port, ids):
        body = ("x" * 72 + "\r\n") * 28  # 2,072 octets
        with Client(port, timeout=300) as client:
            for message_id in ids:
                first, final = client.post(article(message_id, groups="local.test",
                                                   subject="heap", date=None,
                                                   body=body.encode("ascii")))
                self.assertTrue(first.startswith(b"340"), first)
                self.assertEqual(final.rstrip(b"\r\n"), b"240 article received OK")

    def serve(self, port, ids):
        with Client(port, timeout=300) as client:
            for message_id in (ids[0], ids[-1]):
                served = client.article(message_id)
                self.assertIsNotNone(served, message_id)
                self.assertIn(("Message-ID: " + message_id + "\r\n").encode("ascii"),
                              served.splitlines(keepends=True))
            self.assertTrue(client.command("GROUP local.test").startswith(b"211 100 "))
            status, rows = client.multiline("OVER 1-100")
            self.assertTrue(status.startswith(b"224"), status)
            self.assertEqual(rows.count(b"\r\n"), 100)

    def wait_for(self, pattern, port, seconds=300):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            found = re.search(pattern, self.node.process.stderr.since(0))
            if found:
                return found
            try:  # the owner publishes between accepts
                with socket.create_connection(("127.0.0.1", port), timeout=5) as conn:
                    conn.makefile("rb").readline()
            except OSError:
                pass
            time.sleep(1)
        self.fail("no {!r} in the owner's log".format(pattern))


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to the production image")
class FreshInitTests(Harness, unittest.TestCase):
    """PKT-582 in gpt-6's wave-5 shape (books/heap-reservation.lisp
    fn-heap-init-decide): a bare `init' takes a conservative preset within
    the budget (the least of the physical memory less a quarter, at least
    512 MiB, and every limit the process runs under) and prints it; the
    launcher then runs that store.  Run under --mem 2G (small) and without a
    small limit (development; never scale unless asked)."""

    def init_line(self, made):
        found = INIT_LINE.search(made.stdout.decode())
        self.assertIsNotNone(found, text(made))
        word, sizing, reservation, budget = (found.group(1), found.group(2),
                                             int(found.group(3)), int(found.group(4)))
        # Every capacity-free init is within the budget it prints.
        self.assertEqual(found.group(5), "yes")
        self.assertLessEqual(reservation, budget)
        if LIMIT:
            self.assertLessEqual(budget, LIMIT // (1024 * 1024))
        print("NATIVE-HEAP init profile={} sizing={} reservation={} MB budget={} MB"
              .format(word, sizing, reservation, budget))
        return word, sizing, reservation, budget

    def test_a_bare_init_on_the_friends_2_gb_machine_is_accepted_and_runs(self):
        """The OpenBSD friend's machine: 2 GB of memory, 1,536 MB after the
        system's share (fn-heap-os-reserve-octets), named here as the init
        budget.  A bare init is ACCEPTED (lane heap-pool, B9: the header state
        charged to the history budget; under lane heap-bounds' uncharged
        term the small floor's first run was 1,872 MB and this was refused),
        within 1,536 MB, and the store runs and takes POSTs."""
        config, port = self.config("friend")
        made = self.run_fn("operator", config, "init", "--budget", "1536", "local.test")
        self.assertEqual(made.returncode, EXIT_OK, text(made))
        word, sizing, reservation, budget = self.init_line(made)
        self.assertEqual(sizing, "conservative")
        self.assertIn(word, ("custom", "small"))
        self.assertEqual(budget, 1536)
        self.assertLessEqual(reservation, 1536)
        self.start()
        self.post(port, ["<friend-{}@example.invalid>".format(n) for n in range(3)])
        self.stop()

    def test_a_bare_init_is_conservative_printed_and_runs(self):
        config, port = self.config("fresh")
        made = self.run_fn("operator", config, "init", "local.test")
        self.assertEqual(made.returncode, EXIT_OK, text(made))
        word, sizing, _, _ = self.init_line(made)
        self.assertEqual(sizing, "conservative")
        # PKT-707: the largest friend rung the budget holds (the word is
        # `custom' for a rung, `small' for the floor), never development.
        self.assertIn(word, ("custom", "small"))
        status = self.run_fn("operator", config, "status")
        self.assertEqual(status.returncode, EXIT_OK, text(status))
        heap = HEAP_LINE.search(status.stdout.decode())
        self.assertIsNotNone(heap, text(status))
        self.assertEqual(heap.group(2), word)
        ids = ["<fresh-{}@example.invalid>".format(n) for n in range(3)]
        self.start()
        self.post(port, ids)
        self.stop()

    def test_largest_within_the_budget_on_request(self):
        """`init --largest' takes the first of scale, development and
        small the budget holds; an operator budget below the machine
        (`init --budget' 2000) takes small, or the friend rung whose
        first run it holds (the word is `custom').  (1,500 until lane
        heap-bounds: the small floor's first run is 1,906 MB since the
        records' term is derived from the profile's limits.)"""
        config, _ = self.config("largest")
        made = self.run_fn("operator", config, "init", "--largest", "local.test")
        self.assertEqual(made.returncode, EXIT_OK, text(made))
        self.assertNotIn(b"init-budget-below-machine", made.stderr)
        word, sizing, _, budget = self.init_line(made)
        self.assertEqual(sizing, "largest")
        self.assertIn(word, ("small", "development", "scale"))
        if SMALL:
            self.assertEqual(word, "small")
        config, _ = self.config("budget")
        made = self.run_fn("operator", config, "init", "--budget", "2000", "local.test")
        self.assertEqual(made.returncode, EXIT_OK, text(made))
        word, _, _, budget = self.init_line(made)
        self.assertIn(word, ("small", "custom"))
        self.assertEqual(budget, 2000)
        # The machine gives more than the named 2,000 MB (2 GiB or more):
        # init says so by name with both figures, on stderr, and still writes.
        below = INIT_NAMED_BELOW.search(made.stderr.decode())
        self.assertIsNotNone(below, text(made))
        self.assertEqual(int(below.group(1)), 2000)
        self.assertGreater(int(below.group(2)), 2000)
        if LIMIT:
            self.assertLessEqual(int(below.group(2)), LIMIT // (1024 * 1024))
        config, _ = self.config("badbudget")
        # Row Q10b: a malformed budget is init's usage error, by name.
        refused = self.run_fn("operator", config, "init", "--budget", "lots", "local.test")
        self.assertEqual(refused.returncode, EXIT_USAGE, text(refused))
        self.assertIn("invalid-init-budget", text(refused).lower())
        self.assertFalse((self.tmp / "badbudget").exists())

    def test_the_default_mission_inits_and_runs(self):
        """`[ops] mission = "small-community"' (1 MiB articles, 8 groups per
        article) keeps its fields: without a small limit on development's
        capacity, under 2 GiB (the friend's machine) on the small preset's
        (1,326 MB: the thread stacks are a constant since
        served-line-iterative); it runs and takes POSTs either way.  A
        budget that cannot hold its first run (`init --budget' 500) is
        refused by name with no store made."""
        config, port = self.config("mission")
        with open(config, "a", encoding="ascii") as f:
            f.write('[ops]\nmission = "small-community"\n')
        refused = self.run_fn("operator", config, "init", "--budget", "500")
        self.assertEqual(refused.returncode, EXIT_REFUSED, text(refused))
        found = INIT_REFUSED.search(text(refused))
        self.assertIsNotNone(found, text(refused))
        self.assertGreater(int(found.group(3)), int(found.group(4)))
        self.assertFalse((self.tmp / "mission").exists())
        made = self.run_fn("operator", config, "init")
        self.assertEqual(made.returncode, EXIT_OK, text(made))
        word, _, _, _ = self.init_line(made)
        self.assertEqual(word, "custom")
        status = self.run_fn("operator", config, "status")
        self.assertEqual(status.returncode, EXIT_OK, text(status))
        self.assertIn("max-article-octets=1048576", status.stdout.decode())
        # PKT-707: at least the friend floor (16,384 transactions, 8 MiB of
        # history), and the capacity named in plain words.
        out = status.stdout.decode()
        transactions = re.search(r"max-transactions=(\d+)", out)
        self.assertIsNotNone(transactions, out)
        self.assertGreaterEqual(int(transactions.group(1)), 16384)
        left = re.search(r"^capacity articles-left=(\d+) ", out, re.M)
        self.assertIsNotNone(left, out)
        self.assertGreaterEqual(int(left.group(1)), 16384)
        ids = ["<mission-{}@example.invalid>".format(n) for n in range(3)]
        self.start()
        self.post(port, ids)
        # PKT-708: the mission's init serves control.cancel, so a poster's
        # own cancel (RFC 8315 Cancel-Lock / Cancel-Key) is filed with no
        # `group create' first.
        self.assertEqual(self.own_cancel(port), (b"240", b"430"))
        self.stop()

    def own_cancel(self, port):
        key = base64.b64encode(hashlib.sha256(b"friend secret").digest()).decode("ascii")
        lock = base64.b64encode(hashlib.sha256(key.encode("ascii")).digest()).decode("ascii")
        target, cancel = "<mission-own@example.invalid>", "<mission-cancel@example.invalid>"
        with Client(port, timeout=300) as client:
            status, listed = client.multiline("LIST ACTIVE control.cancel")
            self.assertTrue(status.startswith(b"215"), status)
            self.assertEqual([line.split(b" ")[0] for line in listed.splitlines()],
                             [b"control.cancel"])
            answers = []
            for posted in (
                    article(target, groups="local.test", subject="mine", date=None,
                            headers=("Cancel-Lock: sha256:" + lock,)),
                    article(cancel, groups="local.test", subject="cmsg cancel " + target,
                            date=None, body=b"cancel\r\n",
                            headers=("Control: cancel " + target,
                                     "Cancel-Key: sha256:" + key))):
                first, final = client.post(posted)
                self.assertTrue(first.startswith(b"340"), first)
                answers.append(final.rstrip(b"\r\n"))
            self.assertTrue(answers[0].startswith(b"240"), answers)
            self.assertTrue(answers[1].startswith(b"240"), answers)
            after = client.command("ARTICLE {}".format(target))
        return answers[1][:3], after[:3]


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to the production image")
@unittest.skipUnless(SMALL, "run under a memory limit of at most 2 GiB "
                            "(tools/hbox_native.sh --mem 2G)")
class HeapFromProfileTests(Harness, unittest.TestCase):
    def test_a_small_node_starts_serves_checkpoints_and_reopens_in_2g(self):
        config, port = self.config("small")
        # The small preset's fields, named (a bare init under 2 GiB now takes
        # the 16 MiB rung, whose first run fits: reservation-after-flip).
        made = self.run_fn("operator", config, "init", *SMALL_FLAGS, "local.test")
        self.assertEqual(made.returncode, EXIT_OK, text(made))
        status = self.run_fn("operator", config, "status")
        self.assertEqual(status.returncode, EXIT_OK, text(status))
        out = status.stdout.decode()
        self.assertIn("max-history-octets=8388608", out)
        heap = HEAP_LINE.search(out)
        self.assertIsNotNone(heap, out)
        figure, word, machine = int(heap.group(1)), heap.group(2), int(heap.group(3))
        self.assertEqual(word, "small")
        self.assertEqual(machine, LIMIT // (1024 * 1024))
        self.assertLessEqual(figure, machine)
        print("NATIVE-HEAP figure={} MB machine={} MB".format(figure, machine))

        ids = ["<heap-{}@example.invalid>".format(n) for n in range(100)]
        self.start()
        self.post(port, ids)
        self.serve(port, ids)
        # checkpoint-pipeline's line carries steps= (host/native/owner.lisp).
        auto = self.wait_for(rb"CHECKPOINT auto sequence=(\d+) suffix=(\d+) "
                                   rb"octets=(\d+) (?:steps=\d+ )?ms=(\d+)", port)
        print("NATIVE-HEAP", auto.group(0).decode())
        hwm1 = self.stop()
        print("NATIVE-HEAP vmhwm run=1 kB={}".format(hwm1))

        reopened = self.run_fn("operator", config, "status")
        self.assertEqual(reopened.returncode, EXIT_OK, text(reopened))
        self.assertRegex(reopened.stdout.decode(), r"open=checkpoint:\d+")
        self.start()
        self.serve(port, ids)
        hwm2 = self.stop()
        print("NATIVE-HEAP vmhwm run=2 kB={}".format(hwm2))
        self.assertLess(max(hwm1, hwm2) * 1024, LIMIT)

    def test_a_store_init_admitted_fills_to_its_limit_and_still_restarts(self):
        """The coordinator's release blocker (friend-path, packet A): a store
        `init' sized within this machine's budget must reopen on this machine
        however full it gets.  A bare init under 2 GiB (the conservative
        rung the budget holds, judged by its FULL store since lane
        membership-budget: books/heap-reservation.lisp
        `fn-heap-init-accepted-store-always-reopens'), filled with 30 KiB
        articles until the store refuses by name (the history budget, which
        now also pays for every group membership), then `status' and a
        restart are accepted and the articles are served."""
        config, port = self.config("fill")
        began = time.monotonic()
        made = self.run_fn("operator", config, "init", "local.test")
        self.assertEqual(made.returncode, EXIT_OK, text(made))
        found = INIT_LINE.search(made.stdout.decode())
        self.assertIsNotNone(found, text(made))
        self.assertEqual(found.group(5), "yes")
        reservation = int(found.group(3))
        body = ("y" * 72 + "\r\n") * 400  # 29,600 octets
        self.start()
        started = time.monotonic()
        stored, reply = [], b""
        with Client(port, timeout=600) as client:
            for n in range(20000):
                message_id = "<fill-{}@example.invalid>".format(n)
                first, final = client.post(article(message_id, groups="local.test",
                                                   subject="fill", date=None,
                                                   body=body.encode("ascii")))
                self.assertTrue(first.startswith(b"340"), first)
                reply = final.rstrip(b"\r\n")
                if not reply.startswith(b"240"):
                    break
                stored.append(message_id)
        print("NATIVE-HEAP fill init-and-start-s={:.1f} fill-s={:.1f} posts={}".format(
            started - began, time.monotonic() - started, len(stored)))
        with node_log_on_failure(self.node.process):
            self.assertEqual(reply.decode("ascii"),
                             "441 posting failed; the store is full: no capacity for this "
                             "article (unaffordable); the node's operator can raise it",
                             "after {} posts".format(len(stored)))
        hwm1 = self.stop()
        print("NATIVE-HEAP fill posts={} vmhwm kB={} init-reservation={} MB".format(
            len(stored), hwm1, reservation))
        status = self.run_fn("operator", config, "status")
        self.assertEqual(status.returncode, EXIT_OK, text(status))
        heap = HEAP_LINE.search(status.stdout.decode())
        self.assertIsNotNone(heap, text(status))
        self.assertLessEqual(int(heap.group(1)), int(heap.group(3)))
        print("NATIVE-HEAP full store: {}".format(heap.group(0)))
        self.start()
        with Client(port, timeout=300) as client:
            for message_id in (stored[0], stored[-1]):
                self.assertIsNotNone(client.article(message_id), message_id)
        hwm2 = self.stop()
        print("NATIVE-HEAP restart vmhwm kB={}".format(hwm2))
        self.assertLess(max(hwm1, hwm2) * 1024, LIMIT)

    def test_a_profile_the_machine_cannot_hold_is_refused_by_name_at_start(self):
        """`--profile development' is the operator's request: never resized.
        Under the launcher its probe refuses it by name here; the image's own
        init REFUSES it by name with both numbers and makes nothing (ember,
        2026-09-27: lane membership-budget), unless `init --budget MB' names a
        target budget that holds it: then it is written for that machine
        (`within-budget=no target-budget=16384 MB', the scale preset) and
        the launcher refuses its run and status here by name."""
        config, port = self.config("development")
        refused = self.run_fn("operator", config, "init", "--profile", "development",
                              "local.test")
        # The launcher's probe of `init' sizes the empty store's first run
        # (it fits under 2 GiB since the memberships are charged to H); the
        # refusal is init's own, by name with both numbers.
        self.assertEqual(refused.returncode, EXIT_REFUSED, text(refused))
        self.assertRegex(text(refused), INIT_REFUSED)
        self.assertFalse((self.tmp / "development").exists())
        own = self.run_fn("operator", config, "init", "--profile", "development",
                          "local.test", command=[IMAGE, "--fn"])
        self.assertEqual(own.returncode, EXIT_REFUSED, text(own))
        found = INIT_REFUSED.search(text(own))
        self.assertIsNotNone(found, text(own))
        self.assertEqual(found.group(1), "development")
        self.assertEqual(found.group(2), "requested")
        self.assertGreater(int(found.group(3)), int(found.group(4)))
        self.assertEqual(own.stdout, b"")
        self.assertFalse((self.tmp / "development").exists())
        print("NATIVE-HEAP init refused reservation={} MB budget={} MB".format(
            found.group(3), found.group(4)))
        # The store written for a bigger machine: since lane heap-bounds (B4)
        # an EMPTY development store's run fits 2 GiB (the open's chunk is
        # bounded by the input, and a run sizes the open by the store on
        # disk), so the launcher's refusal is shown on the scale preset,
        # whose state at its bounds alone is past 2 GiB.
        made = self.run_fn("operator", config, "init", "--budget", "16384", "--profile", "scale",
                           "local.test", command=[IMAGE, "--fn"])
        self.assertEqual(made.returncode, EXIT_OK, text(made))
        self.assertRegex(made.stdout.decode(),
                         r"init: profile=scale sizing=requested reservation=\d+ MB "
                         r"budget=\d+ MB within-budget=no target-budget=16384 MB")
        for verb in ("run", "status"):
            result = self.run_fn("operator", config, verb)
            self.assertEqual(result.returncode, EXIT_REFUSED, text(result))
            found = REFUSED.search(text(result))
            self.assertIsNotNone(found, text(result))
            self.assertGreater(int(found.group(1)), int(found.group(2)))
            self.assertEqual(int(found.group(2)), LIMIT // (1024 * 1024))
            self.assertEqual(result.stdout, b"")
        with self.assertRaises(OSError):
            socket.create_connection(("127.0.0.1", port), timeout=2).close()


@unittest.skipUnless(READY, "FN_NATIVE_HOST (the production image and its core) is not set")
class DatasizeTests(Harness, unittest.TestCase):
    """The process's datasize limit (RLIMIT_DATA; OpenBSD's login classes:
    `default' 1536M, `daemon' 4096M) and the launcher (lane
    openbsd-datasize).  A command naming no store (--version, help)
    gets the store-less heap (books/heap-figure.lisp fn-heap-storeless-decide), so it
    runs under both stock classes.  Under a limit below the image's own
    mappings the runtime stops before the probe reaches ACL2: the launcher
    reports that as a fault by name (exit 4), never as ACL2's refusal
    (exit 1, which SBCL's own exit code would otherwise read as)."""

    def under(self, mib, *words):
        octets = mib * 1024 * 1024
        result = subprocess.run(
            [self.fn, *words], env=self.env(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=600, check=False,
            preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_DATA, (octets, octets)))
        print("NATIVE-HEAP datasize={} MiB {} -> {} {}".format(
            mib, " ".join(words), result.returncode,
            text(result).strip().replace("\n", " | ")[-300:]))
        return result

    def test_a_storeless_command_runs_under_both_stock_classes(self):
        # `operator CONFIG help VERB' names no store, as --version does (which
        # a build tree cannot answer: its image records no source revision;
        # cut_release gate 13 checks --version itself on the installed release).
        config = self.tmp / "absent.toml"
        for mib in (1536, 4096):
            with self.subTest(datasize_mib=mib):
                result = self.under(mib, "operator", str(config), "help", "run")
                self.assertEqual(result.returncode, EXIT_OK, text(result))
                self.assertIn("usage: fn operator CONFIG run", result.stdout.decode())

    def test_a_limit_below_the_image_is_a_named_fault_not_a_refusal(self):
        result = self.under(64, "--version")
        self.assertEqual(result.returncode, 4, text(result))
        stderr = result.stderr.decode("utf-8", "replace")
        self.assertIn("fn: fault heap-probe-did-not-run exit=", stderr)
        self.assertIn("datasize-kib=65536", stderr)
        self.assertNotIn("refused", stderr)
        self.assertEqual(result.stdout, b"")


if __name__ == "__main__":
    unittest.main()
