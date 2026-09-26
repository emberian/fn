"""The operator verbs that stand a node up, read its peers, and lose an outcome.

Three subjects:

* `operator CONFIG init [GROUP...]` -- the store the configuration names,
  created through the public verb, refused when it already exists, and refused
  without opening or taking the writer lock when a live owner holds it.
* `operator CONFIG peer list` -- the peer records the durable configuration
  holds, rendered by ACL2 and only written out here.
* the developer-only uncertain outcome -- one control submission whose durable
  result its caller cannot learn, so that the three outcomes are all
  observable at the operator boundary (D13).

The source checks are always active.  The executable witnesses need the saved
images; when one is absent the witness skips and says which image it wanted,
rather than a source inspection being reported as runtime evidence.
"""
import fcntl
import os
from pathlib import Path
import select
import signal
import socket
import subprocess
import tempfile
import unittest

from tests.native_process import next_log_number, start_filed


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
DEVELOPER = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))

EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, EXIT_FAULT, EXIT_USAGE = 0, 1, 3, 4, 5


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    env.pop("FN_NATIVE_CONTROL_FAULT", None)
    env.pop("FN_NATIVE_CONTROL_TEST_STOP", None)
    return env


def executable(image):
    return image.is_file() and os.access(image, os.X_OK)


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


class NativeOperatorVerbCompositionTests(unittest.TestCase):
    """What the source has to say, whether or not an image was built."""

    def setUp(self):
        self.model = (ROOT / "books" / "native-operator.lisp").read_text(encoding="utf-8")
        self.admin = (ROOT / "books" / "native-admin.lisp").read_text(encoding="ascii")
        self.host = (ROOT / "host" / "native" / "operator.lisp").read_text(encoding="ascii")
        self.owner = (ROOT / "host" / "native" / "owner.lisp").read_text(encoding="ascii")
        self.admin_host = (ROOT / "host" / "native" / "admin.lisp").read_text(encoding="ascii")

    def test_init_outcome_is_acl2s_and_the_host_only_observes(self):
        # The plan, the marker names and the outcome are all ACL2's; the host
        # contributes lstat and nothing else.
        self.assertIn("(defun fn-native-operator-init-outcome (result observed)", self.model)
        self.assertIn("(defconst *fn-nop-store-markers*", self.model)
        self.assertIn('"writer.lock"', self.model)
        self.assertIn("'fn-native-operator-host-init-marker-octets", self.host)
        self.assertIn("'fn-native-operator-host-init-outcome", self.host)
        self.assertIn("(:init (fnn-operator-execute-init result))", self.host)
        # The observation opens nothing: no lock call inside it.
        observe = self.host.index("(defun fnn-operator-init-observed")
        execute = self.host.index("(defun fnn-operator-execute-run", observe)
        body = self.host[observe:execute]
        self.assertIn("(fnn-lstat", body)
        for forbidden in ("fnn-open-lock", "fnn-flock", "fnn-open-live-store", "fnn-acquire"):
            self.assertNotIn(forbidden, body)

    def test_peer_list_is_a_query_and_the_host_asks_acl2_which(self):
        self.assertIn("(defun fn-native-admin-result-queryp (result)", self.admin)
        self.assertIn(":list-peers", self.admin)
        # The peer report moved to books/native-admin-peer.lisp; the query
        # report in native-admin still asks it for a :list-peers plan.
        admin_peer = (ROOT / "books" / "native-admin-peer.lisp").read_text(encoding="ascii")
        self.assertIn("(defun fn-native-admin-peer-report (peers)", admin_peer)
        self.assertIn('(include-book "native-admin-peer")', self.admin)
        report = self.admin.index("(defun fn-native-admin-query-report (plan value)")
        self.assertIn("(fn-native-admin-peer-report (fn-cfg-peers value))",
                      self.admin[report:self.admin.index("\n(", report)])
        self.assertIn("'fn-native-admin-host-queryp plan", self.host)
        self.assertIn("(queryp (fnn-admin-query root plan))", self.host)
        # The read-only executor opens the store non-writable and publishes
        # nothing; the ACL2 report is written out, not rebuilt.
        query = self.admin_host.index("(defun fnn-admin-query (root plan)")
        execute = self.admin_host.index("(defun fnn-admin-execute (root plan)", query)
        body = self.admin_host[query:execute]
        self.assertIn("(fnn-open-live-store root nil)", body)
        self.assertIn("'fn-native-admin-host-query-report plan", body)
        for forbidden in ("fnn-admin-publish", "fnn-admin-reconfigure", "fnn-control-admin"):
            self.assertNotIn(forbidden, body)

    def test_uncertain_fault_is_gated_on_the_saved_image_profile(self):
        # Read only through the accessor that answers NIL on a production
        # image, which refuses to start with the variable set at all
        # (host/native/io.lisp `fnn-developer-selector-gate').  There is no
        # production branch in the serialized action any more: the one it had
        # answered 3 and stopped the node (campaign dabebb84, F5).
        self.assertIn('(fnn-developer-selector "FN_NATIVE_CONTROL_FAULT")', self.owner)
        self.assertNotIn('(sb-ext:posix-getenv "FN_NATIVE_CONTROL_FAULT")', self.owner)
        gate = self.owner.index("(defun fnn-owner-control-test-fault ()")
        arm = self.owner.index("(defun fnn-owner-control-arm-fault", gate)
        body = self.owner[gate:arm]
        self.assertNotIn("fnn-developer-image-p", body)
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="ascii")
        self.assertIn('"FN_NATIVE_CONTROL_FAULT"', io[io.index(
            "(defparameter +fnn-developer-selectors+"):io.index(
            "(defun fnn-developer-selector ")])
        # It selects an existing named model cut rather than inventing one.
        self.assertIn("+fnn-cli-faults+", body)
        self.assertNotIn("FN_NATIVE_CONTROL_FAULT",
                         (ROOT / "host" / "native" / "operator.lisp").read_text(encoding="ascii"))

    def test_the_uncertain_word_is_acl2s_control_vocabulary(self):
        control = (ROOT / "books" / "native-control.lisp").read_text(encoding="ascii")
        self.assertIn(":accepted :duplicate :refused :clock-unusable :busy :uncertain :fault", control)
        self.assertIn("(equal status :uncertain) :uncertain", control)
        owner_book = (ROOT / "books" / "owner.lisp").read_text(encoding="ascii")
        self.assertIn("(defun fn-own-control-outcome-result (o word)", owner_book)


class NativeOperatorVerbFixture(unittest.TestCase):
    """A scratch directory and the two commands every witness below runs."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-verbs-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.store = self.root / "store"
        self.config = self.root / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n'.format(self.store), encoding="ascii")

    def operator(self, *words, image=None, env=None, timeout=180):
        return subprocess.run(
            [str(image or IMAGE), "--fn", "operator", str(self.config), *words],
            cwd=ROOT, env=env or environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=timeout, check=False)


@unittest.skipUnless(executable(IMAGE), "build/fn-host is required")
class NativeOperatorInitTests(NativeOperatorVerbFixture):
    def test_init_creates_the_configured_store_and_then_refuses_it(self):
        created = self.operator("init", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.assertIn(b"initialized", created.stdout)
        self.assertIn(b"accepted operator init", created.stderr)
        for entry in ("config.json", "writer.lock", "allocation-frontier.json",
                      "transactions", "config"):
            self.assertTrue((self.store / entry).exists(), entry)

        status = self.operator("status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        self.assertIn(b"transactions=0", status.stdout)

        again = self.operator("init", "fn.test")
        self.assertEqual(again.returncode, EXIT_REFUSED, again.stderr.decode())
        # Case-insensitive, as the other refusal checks here: both sides upper.
        self.assertIn(b"REFUSED OPERATOR INIT STORE-EXISTS", again.stderr.upper(),
                      again.stderr.decode())

    def test_a_locked_store_is_refused_without_the_lock_being_touched(self):
        self.assertEqual(self.operator("init", "fn.test").returncode, EXIT_OK)
        lock = os.open(str(self.store / "writer.lock"), os.O_RDWR)
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            refused = self.operator("init", "fn.test")
            # The refusal names the store's existence, not a failed
            # acquisition: nothing tried to take this lock.
            self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
            self.assertIn(b"STORE-EXISTS", refused.stderr.upper())
            self.assertNotIn(b"already locked", refused.stderr)
            # And a command that does open the store says so, which is what
            # makes the line above a distinction and not a coincidence.
            status = self.operator("status")
            self.assertEqual(status.returncode, EXIT_REFUSED, status.stderr.decode())
            self.assertIn(b"already locked", status.stderr)
        finally:
            os.close(lock)

    def test_init_without_a_group_is_usage_and_writes_nothing(self):
        bare = self.operator("init")
        self.assertEqual(bare.returncode, EXIT_USAGE, bare.stderr.decode())
        self.assertFalse(self.store.exists())
        bad = self.operator("init", "Not A Group")
        self.assertEqual(bad.returncode, EXIT_USAGE, bad.stderr.decode())
        self.assertFalse(self.store.exists())
        duplicate = self.operator("init", "fn.test", "fn.test")
        self.assertEqual(duplicate.returncode, EXIT_USAGE, duplicate.stderr.decode())
        self.assertFalse(self.store.exists())

    def test_help_names_init(self):
        # The property: one line, the init grammar naming the profile and
        # every capacity field ACL2 accepts at init (books/native-operator.lisp
        # fn-nop-help-text), then optionally the [ops] mission clause operator-walk
        # added (the mission takes GROUP words only).  A dropped or renamed
        # field, a second line, or a clause of another shape still fails.
        helped = self.operator("help", "init")
        self.assertEqual(helped.returncode, EXIT_OK, helped.stderr.decode())
        text = helped.stdout.decode()
        grammar = ("usage: fn operator CONFIG init [--profile development|scale|default] [--max-transactions N] [--max-history-octets N] [--max-record-octets N] [--max-article-octets N] [--max-groups-per-article N] [--max-group-name-octets N] [--max-open-suffix N] [--max-consumers N] [--max-bp-rows N] [--max-config-generations N] [--max-credentials N] [--max-policy-members N] GROUP [GROUP...]")
        self.assertTrue(text.endswith("\n") and text.count("\n") == 1, text)
        self.assertTrue(text.startswith(grammar), text)
        clause = text[len(grammar):-1]
        self.assertTrue(clause == "" or clause.startswith(
            "; under [ops] mission: init [GROUP...] only "), clause)


class NativeOperatorReservedGroupSourceTests(unittest.TestCase):
    """RFC 5536 s3.1.4 reserved names are ACL2's refusal; the host adds none."""

    def test_reserved_names_are_refused_by_acl2_at_init_and_create(self):
        model = (ROOT / "books" / "native-operator.lisp").read_text(encoding="utf-8")
        admin = (ROOT / "books" / "native-admin.lisp").read_text(encoding="ascii")
        initial = (ROOT / "host" / "config-host.lisp").read_text(encoding="ascii")
        self.assertIn("(defun fn-native-admin-group-name-reservedp (text)", admin)
        self.assertIn("(fn-native-admin-result :refused :reserved-group-name", admin)
        self.assertIn("(fn-nop-refused :reserved-group-name \"init\"", model)
        self.assertIn("(fn-native-admin-some-group-name-reservedp names)", initial)
        for path in (ROOT / "host" / "native").glob("*.lisp"):
            text = path.read_text(encoding="ascii").lower()
            self.assertNotIn('"example"', text, path.name)
            self.assertNotIn('"poster"', text, path.name)


@unittest.skipUnless(executable(IMAGE), "build/fn-host is required")
class NativeOperatorReservedGroupTests(NativeOperatorVerbFixture):
    def test_init_of_a_reserved_name_is_refused_and_writes_nothing(self):
        for words in (("example.test",), ("fn.test", "Poster")):
            refused = self.operator("init", *words)
            self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
            self.assertIn(b"RESERVED-GROUP-NAME", refused.stderr.upper())
            self.assertFalse(self.store.exists())

    def test_group_create_poster_is_refused_and_publishes_nothing(self):
        self.assertEqual(self.operator("init", "fn.test").returncode, EXIT_OK)
        before = sorted(p.name for p in (self.store / "config").iterdir())
        refused = self.operator("group", "create", "poster")
        self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
        self.assertIn(b"RESERVED-GROUP-NAME", refused.stderr.upper())
        self.assertEqual(sorted(p.name for p in (self.store / "config").iterdir()),
                         before)
        created = self.operator("group", "create", "fn.poster")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())


@unittest.skipUnless(executable(IMAGE), "build/fn-host is required")
class NativeOperatorPeerListTests(NativeOperatorVerbFixture):
    def setUp(self):
        super().setUp()
        self.assertEqual(self.operator("init", "fn.test").returncode, EXIT_OK)

    def test_an_added_peer_reads_back_in_the_grammar_that_wrote_it(self):
        empty = self.operator("peer", "list")
        self.assertEqual(empty.returncode, EXIT_OK, empty.stderr.decode())
        self.assertEqual(empty.stdout, b"")

        added = self.operator("peer", "add", "far", "far.example.invalid",
                              "192.0.2.44", "1119", "fn.*", "-", "192.0.2.44",
                              "true")
        self.assertEqual(added.returncode, EXIT_OK, added.stderr.decode())

        listed = self.operator("peer", "list")
        self.assertEqual(listed.returncode, EXIT_OK, listed.stderr.decode())
        lines = listed.stdout.decode("ascii").splitlines()
        self.assertEqual(len(lines), 1, listed.stdout)
        self.assertEqual(
            lines[0],
            "far path-identity=far.example.invalid address=192.0.2.44 "
            "port=1119 security=clear inbound=fn.* outbound=- "
            "auth=source-address:192.0.2.44")

        removed = self.operator("peer", "remove", "far")
        self.assertEqual(removed.returncode, EXIT_OK, removed.stderr.decode())
        after = self.operator("peer", "list")
        self.assertEqual(after.returncode, EXIT_OK, after.stderr.decode())
        self.assertEqual(after.stdout, b"")

    def test_listing_a_locked_store_refuses_and_publishes_nothing(self):
        self.assertEqual(
            self.operator("peer", "add", "far", "far.example.invalid",
                          "192.0.2.44", "1119", "fn.*", "-", "192.0.2.44",
                          "true").returncode, EXIT_OK)
        before = sorted(p.name for p in (self.store / "config").iterdir())
        lock = os.open(str(self.store / "writer.lock"), os.O_RDWR)
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            refused = self.operator("peer", "list")
            self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
            self.assertIn(b"already locked", refused.stderr)
            self.assertEqual(refused.stdout, b"")
        finally:
            os.close(lock)
        self.assertEqual(sorted(p.name for p in (self.store / "config").iterdir()),
                         before)

    def test_the_d23_rows_are_listed_one_word_per_row(self):
        # D23 rows the typed record does not hold: an NNTP peer's carried
        # principals and a BP boundary's carried sources and release issuers.
        # ACL2 renders every word (`fn-native-admin-peer-extra-octets');
        # `fn-native-admin-peer-extra-decode-lists-exactly-the-rows' is the
        # theorem that the words are exactly the rows.
        hex_a, hex_b = "0a" * 32, "0b" * 32
        added = self.operator("peer", "add", "far", "far.example.invalid",
                              "192.0.2.44", "1119", "fn.*", "-", "192.0.2.44",
                              "true", "carries", hex_a, hex_b)
        self.assertEqual(added.returncode, EXIT_OK, added.stderr.decode())
        boundary = self.operator("bp-boundary", "add", "relay",
                                 "relay.example.invalid", "dtn://relay/", "4557",
                                 "carries", "dtn://sender/", "ipn:9.1",
                                 "releases-for", "dtn://receiver/")
        self.assertEqual(boundary.returncode, EXIT_OK, boundary.stderr.decode())
        listed = self.operator("peer", "list")
        self.assertEqual(listed.returncode, EXIT_OK, listed.stderr.decode())
        lines = listed.stdout.decode("ascii").splitlines()
        self.assertEqual(lines, [
            "far path-identity=far.example.invalid address=192.0.2.44 "
            "port=1119 security=clear inbound=fn.* outbound=- "
            "auth=source-address:192.0.2.44 "
            "carries-principal={} carries-principal={}".format(hex_a, hex_b),
            "relay path-identity=relay.example.invalid address=dtn://relay/ "
            "port=0 security=- inbound=- outbound=- "
            "auth=principal:bp-only-no-nntp-principal "
            "carries=dtn://sender/ carries=ipn:9.1 releases-for=dtn://receiver/"])

    def test_peer_list_takes_no_argument(self):
        extra = self.operator("peer", "list", "far")
        self.assertEqual(extra.returncode, EXIT_USAGE, extra.stderr.decode())


@unittest.skipUnless(
    executable(IMAGE) and executable(DEVELOPER),
    "build/fn-host and build/fn-host-developer are both required: the "
    "uncertain outcome is a developer-image cut and the production image "
    "refuses the variable that selects it")
class NativeOperatorUncertainOutcomeTests(NativeOperatorVerbFixture):
    def setUp(self):
        super().setUp()
        self.control = self.root / "control.sock"
        self.port = free_port()
        self.config.write_text(
            '[store]\npath = "{}"\n'
            '[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")
        self.assertEqual(self.operator("init", "fn.test").returncode, EXIT_OK)

    @staticmethod
    def article(message_id):
        return (b"From: author@example.invalid\r\n"
                b"Newsgroups: fn.test\r\n"
                b"Subject: an outcome nobody learns\r\n"
                b"Date: Mon, 21 Sep 2026 09:00:00 +0000\r\n"
                b"Message-ID: " + message_id.encode("ascii") +
                b"\r\n\r\nexact payload bytes\r\n")

    def start_owner(self, image, extra_env=None):
        """The owner, ready: its LISTENING line read from stdout.

        Its stderr goes to a file in the test's temporary directory, never a
        pipe (PKT-505): the owner logs one line per accepted POST under its
        log mutex, and a pipe nobody reads fills at 64 KiB (about 500 POSTs),
        after which the logging thread blocks in pipe_write holding the mutex
        and the owner answers nothing more.  `owner.stderr' is a read handle
        on that file, so a caller that reads it after the owner stops gets
        the whole log, as it did from the pipe; `owner.stderr_path' names it.
        """
        env = environment()
        if extra_env:
            env.update(extra_env)
        process = start_filed(
            [str(image), "--fn", "operator", str(self.config), "run"],
            self.root / "owner-{}.err".format(next_log_number(self)),
            cwd=ROOT, env=env)
        self.addCleanup(self.reap, process)
        for _ in range(4):
            self.assertTrue(select.select([process.stdout], [], [], 180)[0],
                            "the owner did not become ready")
            line = process.stdout.readline()
            if line.startswith(b"LISTENING "):
                return process
            if process.poll() is not None:
                self.fail("owner failed: {}".format(
                    process.stderr.read()[-8192:].decode("utf-8", "replace")))
        self.fail("the owner's readiness output was malformed")

    def reap(self, process):
        if process.poll() is None:
            process.send_signal(signal.SIGKILL)
            process.wait(timeout=10)
        for stream in (process.stdout, process.stderr):
            if stream and not stream.closed:
                stream.close()

    def post(self, message_id, image=None):
        path = self.root / (message_id.strip("<>").replace("@", "-") + ".eml")
        path.write_bytes(self.article(message_id))
        return self.operator("post", "--message-id", message_id,
                             "--payload", str(path), "--group", "fn.test",
                             image=image, timeout=120)

    def test_a_lost_durable_outcome_exits_three_and_recover_resolves_it(self):
        owner = self.start_owner(
            DEVELOPER, {"FN_NATIVE_CONTROL_FAULT": "postpublish"})
        message_id = "<native-operator-uncertain@example.invalid>"
        unsure = self.post(message_id)
        self.assertEqual(unsure.returncode, EXIT_UNCERTAIN, unsure.stderr.decode())
        self.assertIn(b"uncertain operator post", unsure.stderr)
        # The owner fenced itself on the same observation and released the
        # store; that is what makes the recovery below reach it at all.
        self.assertEqual(owner.wait(timeout=60), EXIT_UNCERTAIN,
                         owner.stderr.read().decode("utf-8", "replace"))

        recovered = self.operator("recover")
        self.assertEqual(recovered.returncode, EXIT_OK, recovered.stderr.decode())
        self.assertIn(b"recovered transactions=", recovered.stdout)

        # The three outcomes, from one command, at one boundary (D13).  The
        # article itself is asserted in neither direction here: an
        # indeterminate outcome is evidence about the report.
        second = self.start_owner(DEVELOPER)
        accepted = self.post("<native-operator-accepted@example.invalid>")
        self.assertEqual(accepted.returncode, EXIT_OK, accepted.stderr.decode())
        self.assertEqual(
            sorted({EXIT_OK, EXIT_UNCERTAIN}),
            sorted({accepted.returncode, unsure.returncode}))
        second.send_signal(signal.SIGTERM)
        self.assertEqual(second.wait(timeout=60), EXIT_OK,
                         second.stderr.read().decode("utf-8", "replace"))

    def test_the_production_image_refuses_the_selector(self):
        # The production image has no such cut.  It does not quietly ignore
        # the variable and it does not honour it: it refuses to start, with a
        # usage exit naming the variable, before the store or the control
        # socket is opened.  No request can meet the variable, so no request
        # outcome is spent on it (campaign dabebb84, F4 and F5).
        env = environment()
        env["FN_NATIVE_CONTROL_FAULT"] = "postpublish"
        started = subprocess.run(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=120, check=False)
        self.assertEqual(started.returncode, EXIT_USAGE, started.stderr.decode())
        self.assertIn(b"FN_NATIVE_CONTROL_FAULT", started.stderr)
        self.assertNotIn(b"LISTENING", started.stdout)
        # And a node started without it serves an ordinary post.
        owner = self.start_owner(IMAGE)
        answered = self.post("<native-operator-production@example.invalid>")
        self.assertEqual(answered.returncode, EXIT_OK, answered.stderr.decode())
        owner.send_signal(signal.SIGTERM)
        self.assertEqual(owner.wait(timeout=60), EXIT_OK,
                         owner.stderr.read().decode("utf-8", "replace"))


if __name__ == "__main__":
    unittest.main()


@unittest.skipUnless(executable(IMAGE), "build/fn-host is required")
class NativeOperatorCapacityTests(NativeOperatorVerbFixture):
    """M5: the Store's transaction budget, reported and enforced by ACL2.

    `operator status` prints ACL2's headroom (books/store-budget.lisp
    `fn-sbud-headroom'); the served POST at the budget is refused by the
    prepare the owner installs (books/owner-store-budget.lisp
    `fn-sbud-prepare') and the refusal names its reason on the wire.
    """

    def setUp(self):
        super().setUp()
        self.control = self.root / "control.sock"
        self.port = free_port()
        self.config.write_text(
            '[store]\npath = "{}"\n'
            '[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")

    start_owner = NativeOperatorUncertainOutcomeTests.start_owner
    reap = NativeOperatorUncertainOutcomeTests.reap

    def headroom(self):
        status = self.operator("status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        fields = {}
        count = None
        for line in status.stdout.decode("ascii").splitlines():
            if line.startswith("headroom "):
                fields = dict(word.split("=", 1) for word in line.split()[1:])
            elif line.startswith("transactions="):
                count = int(line.split()[0].split("=", 1)[1])
        self.assertTrue(fields, status.stdout.decode())
        # The host's enumeration of transaction files and ACL2's count agree.
        self.assertEqual(int(fields["transactions-used"]), count)
        return {key: int(value) for key, value in fields.items()}

    def post_many(self, message_ids, subject=b"capacity"):
        replies = []
        with socket.create_connection(("127.0.0.1", self.port), timeout=120) as conn:
            stream = conn.makefile("rwb")
            self.assertTrue(stream.readline().startswith(b"200"))
            for message_id in message_ids:
                stream.write(b"POST\r\n")
                stream.flush()
                self.assertTrue(stream.readline().startswith(b"340"))
                stream.write(b"From: author@example.invalid\r\n"
                             b"Newsgroups: fn.test\r\n"
                             b"Subject: " + subject + b"\r\n"
                             b"Message-ID: " + message_id.encode("ascii") +
                             b"\r\n\r\nbody\r\n.\r\n")
                stream.flush()
                replies.append(stream.readline().rstrip(b"\r\n").decode("ascii"))
            stream.write(b"QUIT\r\n")
            stream.flush()
        return replies

    def stop(self, owner):
        owner.send_signal(signal.SIGTERM)
        self.assertEqual(owner.wait(timeout=60), EXIT_OK,
                         owner.stderr.read().decode("utf-8", "replace"))

    def test_the_development_profile_budget_is_reported_and_refused_by_name(self):
        self.assertEqual(self.operator("init", "--profile", "development", "fn.test").returncode,
                         EXIT_OK)
        before = self.headroom()
        self.assertEqual(before["transactions-used"], 0)
        self.assertEqual(before["transactions-budget"], 128)
        self.assertEqual(before["charge-reserved"], 0)

        owner = self.start_owner(IMAGE)
        ids = ["<cap-{}@example.invalid>".format(n) for n in range(130)]
        self.assertEqual(self.post_many(ids[:1]), ["240 article received OK"])
        # D25: the Store compares what the poster sent, not the stored copy
        # the owner injected Path and Injection-Info into.  A re-POST of the
        # same bytes is the duplicate answer; one changed authored byte under
        # the same Message-ID is the conflict answer.  Neither writes a
        # transaction (the count below is still 1).
        self.assertEqual(
            self.post_many(ids[:1]),
            ["441 posting failed; this article is already stored here"])
        self.assertEqual(
            self.post_many(ids[:1], subject=b"capacitz"),
            ["441 posting failed; a different article with this Message-ID is stored here"])
        self.stop(owner)
        after = self.headroom()
        self.assertEqual(after["transactions-used"], 1)
        self.assertEqual(after["transactions-budget"], 128)
        self.assertGreater(after["charge-reserved"], 0)

        owner = self.start_owner(IMAGE)
        # PKT-169 (STO-019): admission keeps the maintenance reservation, one
        # release record, including its transaction.  So an article is
        # admitted while used + 1 < budget: the last one at used = 126, and
        # the 128th transaction stays the release's
        # (books/store-maintenance-reserve.lisp `fn-smr-article-budget').
        replies = self.post_many(ids[1:127])
        self.assertEqual(replies, ["240 article received OK"] * 126)
        # used = budget-1 and it stays there: refused by name, twice.  A
        # Message-ID the store already holds is still answered by the Store's
        # existing-article decision, not by the budget: the same bytes are
        # the duplicate answer and a changed authored byte the conflict
        # answer (D25), neither the capacity refusal.
        refused = self.post_many(ids[127:129] + ids[:1])
        self.assertEqual(
            refused[:2],
            ["441 posting failed; the store has no capacity for this article"] * 2)
        self.assertEqual(
            refused[2],
            "441 posting failed; this article is already stored here")
        self.assertEqual(
            self.post_many(ids[:1], subject=b"capacitz"),
            ["441 posting failed; a different article with this Message-ID is stored here"])
        self.stop(owner)
        full = self.headroom()
        self.assertEqual(full["transactions-used"], 127)
        self.assertEqual(full["transactions-budget"], 128)

    def test_the_scale_profile_is_reachable_from_init(self):
        created = self.operator("init", "--profile", "scale", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        room = self.headroom()
        self.assertEqual(room["transactions-used"], 0)
        self.assertEqual(room["transactions-budget"], 4096)
        huge = self.operator("init", "--profile", "huge", "fn.other")
        self.assertEqual(huge.returncode, EXIT_USAGE, huge.stderr.decode())

    def profile_line(self):
        status = self.operator("status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        for line in status.stdout.decode("ascii").splitlines():
            if line.startswith("profile "):
                return {k: int(v) if v.isdigit() else v
                        for k, v in (w.split("=", 1) for w in line.split()[1:])}
        self.fail(status.stdout.decode())

    def test_init_writes_the_operators_fields_and_status_prints_them(self):
        # D27: no flag is the default profile; flags set fields; a relation
        # the fields break is refused by its name and writes nothing.
        created = self.operator("init", "--max-transactions", "1000",
                                "--max-article-octets", "20000", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        fields = self.profile_line()
        self.assertEqual(fields["format"], 8)
        self.assertEqual(fields["max-transactions"], 1000)
        self.assertEqual(fields["max-article-octets"], 20000)
        self.assertEqual(fields["max-history-octets"], 1 << 40)
        self.assertEqual(fields["max-open-suffix"], 1000)
        room = self.headroom()
        self.assertEqual((room["transactions-used"], room["transactions-budget"]), (0, 1000))
        self.assertEqual((room["bytes-used"], room["history-bound"]), (0, 1 << 40))

    def test_bare_init_is_the_default_profile(self):
        created = self.operator("init", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        fields = self.profile_line()
        self.assertEqual((fields["format"], fields["max-transactions"]), (8, 4294967295))

    def test_init_refuses_a_profile_by_the_relation_it_breaks(self):
        refused = self.operator("init", "--max-record-octets", "100", "fn.test")
        self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
        self.assertIn(b"max-record-octets-below-an-event-kind", refused.stderr.lower())
        self.assertFalse((self.store / "config.json").exists())
        repeated = self.operator("init", "--max-transactions", "5",
                                 "--max-transactions", "6", "fn.test")
        self.assertEqual(repeated.returncode, EXIT_USAGE, repeated.stderr.decode())
