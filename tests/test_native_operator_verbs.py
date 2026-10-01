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
import re
import subprocess
import unittest

from tests.campaign import native_cuts
from tests.native_harness import (
    EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, EXIT_USAGE, ROOT, Node, article,
    environment, executable, native_image)


IMAGE = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")


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
        execute = self.host.index("\n(defun ", observe + 1)
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
        # The query report renders the peers through an ACL2 peer report
        # over (fn-cfg-peers value), defined in a native-admin-peer* book
        # native-admin includes; by name, not by line (since a50312ef it is
        # fn-native-admin-peer-budget-report, books/native-admin-peer-budget.lisp).
        report = self.admin.index("(defun fn-native-admin-query-report (plan value)")
        called = re.findall(r"\((fn-native-admin-peer[a-z-]*-report) \(fn-cfg-peers value\)\)",
                            self.admin[report:self.admin.index("\n(", report)])
        self.assertEqual(len(called), 1, called)
        book, peer_report = native_cuts.book_function(called[0])
        self.assertTrue(book.stem.startswith("native-admin-peer"), book)
        self.assertIn('(include-book "{}")'.format(book.stem), self.admin)
        self.assertTrue(peer_report.startswith("(defun {} (peers)".format(called[0])), peer_report[:80])
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
    """A scratch node (tests/native_harness.py Node) and its operator verb.
    LISTENER: whether fn.toml names a loopback listener and control socket."""
    listener = False

    def setUp(self):
        self.node = Node(self, IMAGE, listener=self.listener, control=self.listener)
        self.root, self.store, self.config = self.node.root, self.node.store_path, self.node.config
        self.port, self.control = self.node.port, self.node.control

    def operator(self, *words, image=None, env=None, timeout=180):
        return self.node.operator(*words, image=image, env=env, timeout=timeout)


@unittest.skipUnless(executable(IMAGE), "build/fn-host is required")
class NativeOperatorWideArgvTests(NativeOperatorVerbFixture):
    """PKT-867 (HST-032): an operator command has no word count or word
    length bound.  `init' names 60 groups in one argv (the 32-word bound
    refused 29); on the running owner a `motd set' of 40 lines and a
    `group describe' of 60 words travel in one control frame (the admin
    vector's 16-word bound refused them) and read back whole over NNTP."""

    listener = True

    def test_init_names_sixty_groups_and_a_live_command_carries_sixty_words(self):
        groups = ["fit.g%02d" % n for n in range(60)]
        created = self.operator("init", *groups)
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.node.start()
        with self.node.session(timeout=60) as client:
            status, body = client.multiline("LIST NEWSGROUPS")
            self.assertTrue(status.startswith(b"215"), status)
            rows = body.splitlines(keepends=True)
            self.assertEqual(sorted(row.split(b"\t")[0] for row in rows),
                             [g.encode("ascii") for g in groups])
        lines = ["line %02d of the message" % n for n in range(40)]
        motd = self.operator("motd", "set", *lines)
        self.assertEqual(motd.returncode, EXIT_OK, motd.stderr.decode())
        words = ["w%02d" % n for n in range(60)]
        described = self.operator("group", "describe", "fit.g07", *words)
        self.assertEqual(described.returncode, EXIT_OK, described.stderr.decode())
        with self.node.session(timeout=60) as client:
            status, body = client.multiline("LIST MOTD")
            self.assertTrue(status.startswith(b"215"), status)
            self.assertEqual(body.decode("ascii").splitlines(), lines)
            status, body = client.multiline("LIST NEWSGROUPS fit.g07")
            self.assertEqual(body, ("fit.g07\t" + " ".join(words) + "\r\n").encode("ascii"))
        # An empty word is still refused by name before anything is read.
        bad = self.operator("status", "")
        self.assertEqual(bad.returncode, EXIT_USAGE, bad.stderr.decode())
        self.assertIn(b"ARGV-MALFORMED", bad.stderr.upper(), bad.stderr.decode())
        self.node.stop()


@unittest.skipUnless(executable(IMAGE), "build/fn-host is required")
class NativeOperatorInitTests(NativeOperatorVerbFixture):
    def test_reports_piped_to_a_reader_that_left_exit_quietly(self):
        # PKT-712: `status | head` and `health | head` printed SBCL's
        # BROKEN-PIPE backtrace.  The reader here leaves before the first
        # line: the verb finishes, prints nothing on stderr about the pipe,
        # and exits 141 (never 0: the report was not delivered).
        created = self.operator("init", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        for verb, codes in (("status", (141,)), ("health", None)):
            read, write = os.pipe()
            os.close(read)
            try:
                result = subprocess.run(
                    [str(IMAGE), "--fn", "operator", str(self.config), verb],
                    cwd=ROOT, env=environment(), stdout=write,
                    stderr=subprocess.PIPE, timeout=180, check=False)
            finally:
                os.close(write)
            err = result.stderr.decode(errors="replace")
            for word in ("Backtrace", "BROKEN-PIPE", "Couldn't write", "fault operator"):
                self.assertNotIn(word, err, (verb, err))
            if codes:
                self.assertIn(result.returncode, codes, (verb, err))
            else:
                # health's own code (20..27, 19) is kept; its 0 becomes 141.
                self.assertNotEqual(result.returncode, 0, (verb, err))

    def test_init_creates_the_configured_store_and_then_refuses_it(self):
        created = self.operator("init", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.assertIn(b"initialized", created.stdout)
        self.assertIn(b"accepted operator init", created.stderr)
        # the history is the record log's segment (the frontier
        # and transactions/ a init still leaves are PKT-COL-2's).
        for entry in ("config.json", "writer.lock", "journal/000001.log", "config"):
            self.assertTrue((self.store / entry).exists(), entry)

        status = self.operator("status", "--replay")
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
        grammar = ("usage: fn operator CONFIG init [--budget MB] [--largest] [--profile development|scale|default] [--max-transactions N] [--max-history-octets N] [--max-record-octets N] [--max-article-octets N] [--max-groups-per-article N] [--max-group-name-octets N] [--max-open-suffix N] [--max-consumers N] [--max-bp-rows N] [--max-config-generations N] [--max-credentials N] [--max-policy-members N] [--max-control-clients N] GROUP [GROUP...]")
        self.assertTrue(text.endswith("\n") and text.count("\n") == 1, text)
        self.assertTrue(text.startswith(grammar), text)
        clause = text[len(grammar):-1]
        self.assertTrue(clause == "" or clause.startswith(
            "; under [ops] mission: init [--budget MB] [GROUP...] only "), clause)


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
    listener = True

    def setUp(self):
        super().setUp()
        self.assertEqual(self.operator("init", "fn.test").returncode, EXIT_OK)

    @staticmethod
    def article(message_id):
        return article(message_id, subject="an outcome nobody learns",
                       body=b"exact payload bytes\r\n")

    def post(self, message_id, image=None):
        return self.node.post(message_id, self.article(message_id), image=image, timeout=120)

    def test_a_lost_durable_outcome_exits_three_and_recover_resolves_it(self):
        self.node.start(image=DEVELOPER, env={"FN_NATIVE_CONTROL_FAULT": "postpublish"})
        message_id = "<native-operator-uncertain@example.invalid>"
        unsure = self.post(message_id)
        self.assertEqual(unsure.returncode, EXIT_UNCERTAIN, unsure.stderr.decode())
        self.assertIn(b"uncertain operator post", unsure.stderr)
        # The owner fenced itself on the same observation and released the
        # store; that is what makes the recovery below reach it at all.
        self.node.exited(EXIT_UNCERTAIN)

        recovered = self.operator("recover")
        self.assertEqual(recovered.returncode, EXIT_OK, recovered.stderr.decode())
        self.assertIn(b"recovered transactions=", recovered.stdout)

        # The three outcomes, from one command, at one boundary (D13).  The
        # article itself is asserted in neither direction here: an
        # indeterminate outcome is evidence about the report.
        self.node.start(image=DEVELOPER)
        accepted = self.post("<native-operator-accepted@example.invalid>")
        self.assertEqual(accepted.returncode, EXIT_OK, accepted.stderr.decode())
        self.assertEqual(
            sorted({EXIT_OK, EXIT_UNCERTAIN}),
            sorted({accepted.returncode, unsure.returncode}))
        self.node.stop()

    def test_the_production_image_refuses_the_selector(self):
        # The production image has no such cut.  It does not quietly ignore
        # the variable and it does not honour it: it refuses to start, with a
        # usage exit naming the variable, before the store or the control
        # socket is opened.  No request can meet the variable, so no request
        # outcome is spent on it (campaign dabebb84, F4 and F5).
        started = self.operator("run", env={"FN_NATIVE_CONTROL_FAULT": "postpublish"},
                                timeout=120)
        self.assertEqual(started.returncode, EXIT_USAGE, started.stderr.decode())
        self.assertIn(b"FN_NATIVE_CONTROL_FAULT", started.stderr)
        self.assertNotIn(b"LISTENING", started.stdout)
        # And a node started without it serves an ordinary post.
        self.node.start()
        answered = self.post("<native-operator-production@example.invalid>")
        self.assertEqual(answered.returncode, EXIT_OK, answered.stderr.decode())
        self.node.stop()


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

    listener = True

    def headroom(self):
        # Row S3: `--replay' asks a stopped store for the replayed counts (a
        # running owner answers its own either way).
        status = self.operator("status", "--replay")
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

    def post_many(self, message_ids, subject="capacity"):
        """POST each Message-ID on one connection; the final reply lines."""
        replies = []
        with self.node.session(timeout=120) as client:
            for message_id in message_ids:
                first, final = client.post(article(message_id, subject=subject, date=None))
                self.assertTrue(first.startswith(b"340"), first)
                replies.append(final.rstrip(b"\r\n").decode("ascii"))
        return replies

    def test_the_development_profile_budget_is_reported_and_refused_by_name(self):
        self.assertEqual(self.operator("init", "--profile", "development", "fn.test").returncode,
                         EXIT_OK)
        before = self.headroom()
        self.assertEqual(before["transactions-used"], 0)
        self.assertEqual(before["transactions-budget"], 128)
        self.assertEqual(before["charge-reserved"], 0)

        self.node.start()
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
            self.post_many(ids[:1], subject="capacitz"),
            ["441 posting failed; a different article with this Message-ID is stored here"])
        self.node.stop()
        after = self.headroom()
        self.assertEqual(after["transactions-used"], 1)
        self.assertEqual(after["transactions-budget"], 128)
        self.assertGreater(after["charge-reserved"], 0)

        self.node.start()
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
            ["441 posting failed; the store is full: no capacity for this article (unaffordable); the node's operator can raise it"] * 2)
        self.assertEqual(
            refused[2],
            "441 posting failed; this article is already stored here")
        self.assertEqual(
            self.post_many(ids[:1], subject="capacitz"),
            ["441 posting failed; a different article with this Message-ID is stored here"])
        self.node.stop()
        full = self.headroom()
        self.assertEqual(full["transactions-used"], 127)
        self.assertEqual(full["transactions-budget"], 128)

    @staticmethod
    def body_of(n, fill=b"x"):
        """A body of exactly N octets in lines of at most 78 (CRLF included)."""
        line = fill * 76 + b"\r\n"
        whole, rest = divmod(n, len(line))
        return line * whole + fill * rest

    def post_article(self, message_id, groups, body):
        """POST one article to GROUPS; the reply line and the bytes sent."""
        text = article(message_id, groups=",".join(groups), subject="crosspost",
                       date=None, body=body + b"\r\n")
        with self.node.session(timeout=120) as client:
            first, final = client.post(text)
            self.assertTrue(first.startswith(b"340"), first)
        return final.rstrip(b"\r\n").decode("ascii"), len(text)

    @staticmethod
    def header_octets(message_id, groups):
        """The octets of the header post_article sends, through its blank line
        (what the facts' body start counts: books/catalog-record.lisp)."""
        text = article(message_id, groups=",".join(groups), subject="crosspost",
                       date=None, body=b"x\r\n")
        return text.index(b"\r\n\r\n") + 4

    # The history charge of one stored article (books/store-budget.lisp
    # fn-sbud-row-octets): its stored octets, 320 a group, and since lane
    # heap-pool its header charge, 8 a header octet and 12 a Message-ID octet.
    @staticmethod
    def charge(stored, header, msgid, groups):
        return stored + 320 * groups + 8 * header + 12 * len(msgid)

    def test_a_crosspost_is_charged_per_group_and_refused_by_name_past_the_budget(self):
        """Lane membership-budget (ember, 2026-09-27): each group an article is
        filed in is charged 320 octets of the history budget
        (books/store-budget.lisp `*fn-sbud-membership-octets*'), so a
        crosspost is allowed but paid for; when the article alone would fit
        and its memberships do not, the POST is refused by name,
        `441 ... (memberships)', distinct from the full store's
        (unaffordable) (books/store-capacity-vector.lisp
        `fn-cvec-article-refusal-word-names-the-memberships')."""
        groups = ["fn.g{}".format(n) for n in range(12)]
        created = self.operator(
            "init", "--profile", "development", "--max-history-octets", "262144",
            "--max-record-octets", "196608", "--max-article-octets", "32768",
            "--max-groups-per-article", "16", *groups)
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.node.start()
        # One group, then three: the stored charge is the payload as stored
        # (the owner injects the same Path and Injection-Info into both: the
        # Message-IDs have one length) plus 320 per group, plus (lane
        # heap-pool) the header charge: the two groups more are header octets,
        # charged 1 + 8 each.
        reply, one = self.post_article("<xp-a01@example.invalid>", groups[:1], b"body")
        self.assertEqual(reply, "240 article received OK")
        self.node.stop()
        after_one = self.headroom()["bytes-used"]
        self.node.start()
        reply, three = self.post_article("<xp-a03@example.invalid>", groups[:3], b"body")
        self.assertEqual(reply, "240 article received OK")
        self.node.stop()
        after_three = self.headroom()["bytes-used"]
        self.assertEqual(after_three - 2 * after_one, 9 * (three - one) + 640)
        # The injected octets are header octets: the first article's charge
        # is charge(one + i, header + i, its Message-ID, 1).
        header_one = self.header_octets("<xp-a01@example.invalid>", groups[:1])
        base = self.charge(one, header_one, "<xp-a01@example.invalid>", 1)
        self.assertEqual((after_one - base) % 9, 0, (after_one, base))
        injected = (after_one - base) // 9
        # Fill with one-group articles to leave ROOM octets of history: a
        # 10-group article of stored payload P is charged at its figure,
        # P + 1083 + 261 x 10 and its header charge at its worst, 8 P +
        # 12 x 250 (books/store-budget-article.lisp fn-sbud-article-figure),
        # without its memberships, and 3,200 more with them, beside the
        # 4,096-octet maintenance reservation.  Aim the room at the middle of
        # that window.
        room = self.headroom()
        target_payload = 600
        record = 9 * target_payload + 1083 + 261 * 10 + 3000
        want_left = record + 4096 + 1600
        filler_total = room["history-bound"] - room["bytes-used"] - want_left
        self.node.start()
        fill, count = 0, 0
        while filler_total - fill > 0:
            filler_id = "<xp-f{:03d}@example.invalid>".format(count)
            header = self.header_octets(filler_id, groups[:1]) + injected
            # The gate admits a filler of stored payload P at its figure,
            # 9 P + 1,083 + 261 + 320 + 3,000, beside the 4,096 reserve
            # (lane heap-pool), though it is charged far less.
            remaining = room["history-bound"] - room["bytes-used"] - fill
            gate_cap = (remaining - (1083 + 261 + 320 + 3000 + 4096) - 200) // 9 - header
            size = min(30000, gate_cap, filler_total - fill - 320 - 9 * injected - 8 * header
                       - 12 * len(filler_id) - 200)
            if size < 200:
                break
            body = self.body_of(size)
            reply, sent = self.post_article(filler_id, groups[:1], body)
            self.assertEqual(reply, "240 article received OK")
            fill += self.charge(sent + injected, header, filler_id, 1)
            count += 1
        self.node.stop()
        left = self.headroom()
        # The crosspost's stored payload P: its bytes plus the injected
        # headers.  Choose P so the room is 1,600 octets past its record
        # figure and the reservation: it fits without its memberships (3,200).
        room_left = left["history-bound"] - left["bytes-used"]
        bare = len(b"From: author@example.invalid\r\nNewsgroups: " +
                   ",".join(groups[:10]).encode("ascii") +
                   b"\r\nSubject: crosspost\r\nMessage-ID: <xp-x10@example.invalid>"
                   b"\r\n\r\n\r\n")
        stored = (room_left - (1083 + 261 * 10 + 3000 + 4096 + 1600)) // 9
        pad = stored - injected - bare
        print("NATIVE-CROSSPOST room_left={} injected={} bare={} stored={} pad={} left={}"
              .format(room_left, injected, bare, stored, pad, left))
        self.assertGreater(pad, 0, left)
        self.node.start()
        crosspost, _ = self.post_article("<xp-x10@example.invalid>", groups[:10],
                                         self.body_of(pad, b"y"))
        self.assertEqual(
            crosspost,
            "441 posting failed; the store cannot pay for this article's groups: each "
            "group it is posted to is charged to the history budget, and the article "
            "alone would fit; post it to fewer groups (memberships)",
            left)
        # The same article in one group fits: the refusal was the memberships.
        single, _ = self.post_article("<xp-x01@example.invalid>", groups[:1],
                                      self.body_of(pad, b"y"))
        self.assertEqual(single, "240 article received OK", left)
        self.node.stop()
        # Nothing of the refused crosspost was written.
        final = self.headroom()
        self.assertEqual(final["transactions-used"], left["transactions-used"] + 1)

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
        # D27: `--profile default' names D27's profile; flags set fields; a
        # relation the fields break is refused by its name and writes nothing.
        # The default H is 1 TiB, whose full store no machine holds (the
        # arena and the memberships H / 320 bounds): since lane
        # membership-budget `init' refuses it by name unless a target budget
        # is named (`init --budget MB', a store for another machine).  (With
        # no --profile, a capacity field takes development's other fields,
        # row Q10b: test_init_capacity_fields_take_the_development_preset.)
        refused = self.operator("init", "--profile", "default", "--max-transactions", "1000",
                                "--max-article-octets", "20000", "fn.test")
        self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
        self.assertIn(b"refused init-budget-cannot-hold-profile profile=custom "
                      b"sizing=requested reservation=", refused.stderr)
        self.assertFalse(self.store.exists() and any(self.store.iterdir()))
        created = self.operator("init", "--budget", "99999999", "--profile", "default",
                                "--max-transactions", "1000",
                                "--max-article-octets", "20000", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.assertIn(b"within-budget=no target-budget=99999999 MB", created.stdout)
        fields = self.profile_line()
        self.assertEqual(fields["format"], 10)  # the record log with its genesis (fn-store-10)
        self.assertEqual(fields["max-transactions"], 1000)
        self.assertEqual(fields["max-article-octets"], 20000)
        self.assertEqual(fields["max-history-octets"], 1 << 40)
        self.assertEqual(fields["max-open-suffix"], 1000)
        room = self.headroom()
        self.assertEqual((room["transactions-used"], room["transactions-budget"]), (0, 1000))
        self.assertEqual((room["bytes-used"], room["history-bound"]), (0, 1 << 40))

    def test_init_capacity_fields_take_the_development_preset(self):
        """Row Q10b: with no --profile a capacity field takes development's
        other fields, never D27's 1 TiB history; a refused profile names its
        numbers and the value to pass; `--budget' is init's grammar word (the
        FN_INIT_* variables are gone) and a malformed one is a usage error."""
        refused = self.operator("init", "--max-history-octets", "1000", "fn.test")
        self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
        self.assertIn(b"init: max-history-octets 1000 is below max-record-octets 17138486; "
                      b"pass --max-history-octets 17138486 or more", refused.stderr)
        self.assertFalse(self.store.exists() and any(self.store.iterdir()))
        for words in (("--budget", "lots"), ("--budget", "0"), ("--largest", "--largest")):
            usage = self.operator("init", *words, "fn.test")
            self.assertEqual(usage.returncode, EXIT_USAGE, usage.stderr.decode())
            self.assertIn(b"--budget takes the memory budget in MiB", usage.stderr)
        created = self.operator("init", "--budget", "4096", "--max-transactions", "1000",
                                "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        fields = self.profile_line()
        self.assertEqual(fields["max-transactions"], 1000)
        self.assertEqual(fields["max-history-octets"], 25165824)

    def test_bare_init_takes_the_budgeted_preset(self):
        # PKT-582 (image-floor, batch AR): a capacity-free init sizes within
        # the process budget, conservatively, and prints the decision
        # (books/heap-reservation.lisp fn-heap-init-decide): development when
        # the budget holds its reservation, else small; never the default
        # preset's 1 TiB history.
        created = self.operator("init", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        line = re.search(rb"init: profile=(\w+) sizing=conservative ", created.stdout)
        self.assertIsNotNone(line, created.stdout.decode())
        fields = self.profile_line()
        # PKT-707: the largest friend rung the budget holds, never
        # development's 128 transactions (books/heap-reservation.lisp
        # fn-heap-init-decide-conservative-holds-the-floor).
        self.assertIn(line.group(1), (b"custom", b"small"), created.stdout.decode())
        self.assertEqual(fields["format"], 10)  # the record log with its genesis (fn-store-10)
        self.assertIn(fields["max-transactions"], (131072, 65536, 32768, 16384))
        status = self.operator("status", "--replay")
        self.assertIn(b"capacity articles-left=", status.stdout, status.stdout.decode())

    def test_init_refuses_a_profile_by_the_relation_it_breaks(self):
        refused = self.operator("init", "--max-record-octets", "100", "fn.test")
        self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
        self.assertIn(b"max-record-octets-below-an-event-kind", refused.stderr.lower())
        self.assertFalse((self.store / "config.json").exists())
        repeated = self.operator("init", "--max-transactions", "5",
                                 "--max-transactions", "6", "fn.test")
        self.assertEqual(repeated.returncode, EXIT_USAGE, repeated.stderr.decode())
