"""The v0 conformance rows, as native cases on the harness.

planning/v0-matrix.json (its last run: b6759850, 2026-09-26, 233 rows, all on
the native operator backend) was the release's protocol-conformance matrix
(planning/release-v6.6.0.md section 2b, step 7), driven by tools/v0_matrix.py
over ssh.  python-diet T2b retired that driver; every row it exercised has an
owner here or in the module named in
planning/evidence/python-diet-2-2026-09-28/v0-row-owners.md.  Each case
names its rows (`V0-...`); the -A/-B pairs were the same property on two
nodes and are one case on one node here.  A row's outcome class is the one
the matrix recorded: accepted, refused (a refusal by its code or exit 1) or
uncertain (exit 3), never collapsed.

The transit and feed rows between two live nodes (V0-TRANSIT-OFFER,
-TRANSFER, -IDENTICAL, -DUPLICATE, V0-FEED-*) were already
tests.test_native_peering's and tests.test_native_protected_peering's
witnesses; V0-INN-* are tools/inn_lab.py's; V0-CLIENT-SLRN and PAN are
tests.test_native_reader_clients'; V0-CLIENT-NNTPLIB is
tests/interop_nntplib.py against a native owner.
"""
import time
import unittest

from tests.native_harness import (
    EXIT, Client, Node, article, dot_stuff, executable, native_image, requires)

IMAGE = native_image("FN_NATIVE_HOST")
# The uncertain outcome is a developer-image cut (FN_NATIVE_CONTROL_FAULT);
# the production image refuses the variable that selects it.
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
GROUP = "fn.letters"
SECRET = "matrix-secret-8f21\nmatrix-secret-8f21\n"


def code(line):
    return line[:3].decode("ascii", "replace")


def post_over(client, text):
    """POST TEXT on CLIENT: (the 340-or-other line, the final line or None)."""
    first = client.command(b"POST")
    if not first.startswith(b"340"):
        return first, None
    client.send(dot_stuff(text) + b".\r\n")
    return first, client.line()


def capability_labels(client):
    status, body = client.multiline(b"CAPABILITIES")
    assert status.startswith(b"101"), status
    return [line.split()[0].upper().decode("ascii") for line in body.splitlines() if line.strip()]


@requires(IMAGE)
class NodeOperatorRows(unittest.TestCase):
    """The public operator on one node: init, outcomes, groups, capacity,
    peers, principals, identity, live and offline administration."""

    def setUp(self):
        self.node = Node(self, IMAGE)

    def test_init_reinit_status_and_the_store_it_names(self):
        """V0-NODE-INIT, V0-NODE-CONFIG, V0-NODE-STATUS, V0-NODE-REINIT,
        V0-NODE-REINIT-SAFE, V0-NODE-START, V0-NODE-STOP."""
        created = self.node.init(GROUP)
        self.assertIn(str(self.node.store_path).encode(), created.stdout)   # CONFIG
        # Row S3: a stopped store's bare `status' is its checkpoint header's;
        # the replayed counts are `--replay'.
        status = self.node.operator("status", "--replay", expect=EXIT.OK)
        self.assertRegex(status.stdout, rb"transactions=0 articles=0 ")
        self.node.start()                                                    # START
        self.node.post("<reinit@example.invalid>", article("<reinit@example.invalid>",
                                                         groups=GROUP), group=GROUP,
                       expect=EXIT.OK)
        self.node.stop(EXIT.OK)                                              # STOP
        before = self.node.operator("recover", expect=EXIT.OK)
        again = self.node.init(GROUP, expect=EXIT.REFUSED)                   # REINIT
        self.assertIn(b"STORE-EXISTS", again.stdout + again.stderr)
        after = self.node.operator("recover", expect=EXIT.OK)                # REINIT-SAFE
        self.assertIn(b"articles=1 ", before.stdout)
        self.assertEqual(before.stdout, after.stdout)

    def post_both(self, message_id, text, expect):
        path = self.node.root / "crosspost-{}.eml".format(len(list(self.node.root.glob("crosspost-*"))))
        path.write_bytes(text)
        return self.node.operator("post", "--message-id", message_id, "--payload", path,
                                  "--group", GROUP, "--group", "fn.side", expect=expect)

    def test_a_crosspost_is_one_article_and_a_resubmission_overwrites_nothing(self):
        """SCN-002 (atomic cross-post and duplicate acceptance): one article
        posted to two groups is one stored article with a local number in
        each, across a restart; an identical resubmission is the idempotent
        duplicate (exit 0, nothing allocated) and a changed source under the
        held Message-ID is refused and does not replace the stored octets."""
        self.node.init(GROUP, "fn.side")
        self.node.start()
        message_id = "<crosspost@example.invalid>"
        text = article(message_id, groups=GROUP + ",fn.side", body=b"first octets\r\n")
        self.post_both(message_id, text, EXIT.OK)
        self.node.stop(EXIT.OK)
        self.node.start()
        self.post_both(message_id, text, EXIT.OK)
        self.post_both(message_id, article(message_id, groups=GROUP + ",fn.side",
                                           body=b"other octets\r\n"), EXIT.REFUSED)
        with self.node.session() as client:
            for group in (GROUP, "fn.side"):
                self.assertEqual(client.command(b"GROUP " + group.encode()).split()[:4],
                                 [b"211", b"1", b"1", b"1"], group)
                status, served = client.multiline(b"ARTICLE 1")
                self.assertEqual(code(status), "220")
                self.assertIn(message_id.encode(), status)
                self.assertIn(b"first octets", served)
        self.node.stop(EXIT.OK)
        self.assertRegex(self.node.operator("status", expect=EXIT.OK).stdout,
                         rb"articles=1 ")

    def test_a_wildcard_listener_is_refused_before_bind(self):
        """V0-NODE-LOOPBACK: `0.0.0.0` is refused at configuration admission
        (books/native-config.lisp fn-native-config-listener-hostp) as a usage
        error, outside the three outcomes."""
        self.node.init(GROUP)
        self.node.config.write_text(self.node.config.read_text().replace(
            'host = "127.0.0.1"', 'host = "0.0.0.0"'))
        process, stderr = self.node.try_start(timeout=60)
        self.assertIsNotNone(stderr, "a wildcard listener reached LISTENING")
        self.assertEqual(process.returncode, EXIT.USAGE, stderr)

    def test_log_path_is_honoured_and_a_posting_agent_is_refused_by_name(self):
        """V0-NODE-PROFILE."""
        self.node.init(GROUP)
        log = self.node.root / "service.log"
        plain = self.node.config.read_text()
        self.node.config.write_text(plain + '[posting]\nagent = "matrix-agent"\n')
        refused = self.node.operator("run", timeout=60)
        self.assertEqual(refused.returncode, EXIT.USAGE, refused.stderr)
        self.node.config.write_text(plain + '[log]\npath = "{}"\n'.format(log))
        self.node.start()
        message_id = "<profile@example.invalid>"
        self.node.post(message_id, article(message_id, groups=GROUP), group=GROUP,
                       expect=EXIT.OK)
        self.node.stop(EXIT.OK)
        self.assertIn(b"accepted post path=control", log.read_bytes())

    def test_the_three_outcomes_stay_distinct_and_recover_resolves_the_third(self):
        """V0-OUT-ACCEPTED, V0-OUT-REFUSED (a changed source under a held
        Message-ID; an identical resubmission is the idempotent duplicate,
        exit 0), V0-OUT-UNCERTAIN and V0-OUT-RECOVER (developer image)."""
        self.node.init(GROUP)
        self.node.start()
        message_id = "<outcome@example.invalid>"
        text = article(message_id, groups=GROUP, body=b"written once\r\n")
        self.node.post(message_id, text, group=GROUP, expect=EXIT.OK)
        self.node.post(message_id, text, group=GROUP, expect=EXIT.OK)
        self.node.post(message_id, article(message_id, groups=GROUP, body=b"edited\r\n"),
                       group=GROUP, expect=EXIT.REFUSED)
        self.node.stop(EXIT.OK)
        if not executable(DEVELOPER):
            self.skipTest("the uncertain outcome is a developer-image cut: {}".format(DEVELOPER))
        self.node.start(image=DEVELOPER, env={"FN_NATIVE_CONTROL_FAULT": "postpublish"})
        unsure = "<outcome-unsure@example.invalid>"
        self.node.post(unsure, article(unsure, groups=GROUP), group=GROUP,
                       image=DEVELOPER, expect=EXIT.UNCERTAIN)
        self.node.exited(EXIT.UNCERTAIN)
        recovered = self.node.operator("recover", expect=EXIT.OK)
        self.assertIn(b"recovered transactions=", recovered.stdout)

    def test_group_capacity_peer_identity_and_principal_administration(self):
        """V0-GROUP-CREATE, -SERVED, -RETIRE, -UNKNOWN; V0-CAP-SET; V0-PEER-ADD,
        -LIST, -ABSENT, -REMOVE; V0-TRANSIT-IDENTITY; V0-AUTH-PASSWORD,
        V0-AUTH-LIST.  Offline, on a store no owner holds."""
        self.node.init(GROUP)
        verified = rb"configured generation=[0-9]+ record=[0-9]+\.cfg verification=VERIFIED"
        self.assertRegex(self.node.operator("group", "create", "fn.matrix",
                                            expect=EXIT.OK).stdout, verified)
        self.node.start()                                                    # GROUP-SERVED
        with self.node.session() as client:
            self.assertEqual(client.command(b"GROUP fn.matrix").split()[:2], [b"211", b"0"])
        self.node.stop(EXIT.OK)
        self.assertRegex(self.node.operator("group", "retire", "fn.matrix",
                                            expect=EXIT.OK).stdout, verified)
        unknown = self.node.operator("group", "retire", "fn.not.served", expect=EXIT.REFUSED)
        self.assertIn(b"NO-SUCH-GROUP", unknown.stdout + unknown.stderr)
        self.assertRegex(self.node.operator("capacity", "64", expect=EXIT.OK).stdout, verified)
        self.node.operator("peer", "add", "far", "far.example.invalid", "127.0.0.1", "11999",
                           "fn.*", "fn.*", "127.0.0.1", "true", expect=EXIT.OK)
        self.assertIn(b"far.example.invalid",
                      self.node.operator("peer", "list", expect=EXIT.OK).stdout)
        absent = self.node.operator("peer", "remove", "no-such-peer", expect=EXIT.REFUSED)
        self.assertIn(b"NO-SUCH-PEER", absent.stdout + absent.stderr)
        self.node.operator("peer", "remove", "far", expect=EXIT.OK)
        self.assertRegex(self.node.operator("policy", "set", "path-identity",
                                            "a.gate.example.invalid",
                                            expect=EXIT.OK).stdout, verified)
        enrolled = self.node.operator("principal", "set-password", "matrix",
                                      input=SECRET.encode(), expect=EXIT.OK)
        self.assertIn(b"posting=true", enrolled.stdout)
        self.assertIn(b"matrix principal=",
                      self.node.operator("principal", "list", expect=EXIT.OK).stdout)

    def test_an_article_past_the_capacity_is_refused_before_it_is_written(self):
        """V0-CAP-REFUSE."""
        self.node.init(GROUP)
        self.node.operator("capacity", "1", expect=EXIT.OK)
        self.node.start()
        message_id = "<capacity@example.invalid>"
        self.node.post(message_id, article(message_id, groups=GROUP), group=GROUP,
                       expect=EXIT.REFUSED)
        with self.node.session() as client:
            self.assertEqual(code(client.command(b"STAT " + message_id.encode())), "430")

    def test_live_administration_reaches_the_served_configuration(self):
        """V0-CFG-LIVE, V0-CFG-LIVE-REFUSE: the live verb goes to the running
        owner over `[control] path`; the same verb through a configuration
        whose control path nothing bound opens the store and is refused by the
        writer lock the owner holds."""
        self.node.init(GROUP)
        self.node.start()
        self.node.operator("group", "create", "fn.matrix.live", expect=EXIT.OK)
        with self.node.session() as client:
            self.assertEqual(code(client.command(b"GROUP fn.matrix.live")), "211")
        offline = self.node.root / "offline.toml"
        offline.write_text('[store]\npath = "{}"\n[control]\npath = "{}"\n'.format(
            self.node.store_path, self.node.root / "nothing.sock"))
        refused = self.node.invoke("operator", offline, "group", "create", "fn.matrix.off",
                                   expect=EXIT.REFUSED)
        self.assertIn(b"store-held", refused.stdout + refused.stderr)
        self.assertIsNone(self.node.process.poll(), "the owner died across the live verb")


@requires(IMAGE)
class ServedSurfaceRows(unittest.TestCase):
    """One served node holding one article POSTed over its socket: the POST
    rows, the reader profile and the capability pins."""

    @classmethod
    def setUpClass(cls):
        from tests.native_harness import class_case
        cls.node = Node(class_case(cls), IMAGE)
        # fn.side takes the other cases' articles, so the reader profile's
        # GROUP holds exactly the one article whatever order the cases run in.
        cls.node.init(GROUP, "fn.side")
        cls.node.start()
        cls.message_id = "<native-conformance@example.invalid>"
        with cls.node.session() as client:
            cls.group_before = client.command(b"GROUP " + GROUP.encode())
            cls.opened, cls.committed = post_over(
                client, article(cls.message_id, groups=GROUP, subject="conformance"))
            cls.group_after = client.command(b"GROUP " + GROUP.encode())

    def session(self):
        return self.node.session()

    def test_post_cycle(self):
        """V0-POST-OPEN, -COMMIT, -READBACK, -FRESH, -DUPLICATE, -CLOCK,
        -FROM-MAILBOX."""
        self.assertEqual(code(self.opened), "340")
        self.assertEqual(code(self.committed), "240", self.committed)
        self.assertEqual(self.group_before.split()[1], b"0")
        self.assertEqual(self.group_after.split()[1], b"1")
        with self.session() as client:
            self.assertEqual(code(client.multiline(
                b"ARTICLE " + self.message_id.encode())[0]), "220")
            _, duplicate = post_over(client, article(self.message_id, groups=GROUP,
                                                     subject="conformance"))
            self.assertEqual(code(duplicate), "441")
            self.assertIn(b"already stored", duplicate)
            self.assertEqual(code(client.command(b"DATE")), "111")
        with self.session() as client:
            yue = "<from-yue@example.invalid>"
            _, final = post_over(client, article(yue, groups="fn.side", sender="yue"))
            self.assertEqual(code(final), "441")
            self.assertIn(b"From", final)
            self.assertEqual(code(client.command(b"STAT " + yue.encode())), "430")

    def test_reader_profile(self):
        """V0-READ-*: every reader command against the one article (number 1)."""
        with self.session() as client:
            expected = {
                b"CAPABILITIES": "101", b"LIST ACTIVE": "215", b"LIST NEWSGROUPS": "215",
                b"LIST NEWSGROUPS " + GROUP.encode(): "215", b"LIST OVERVIEW.FMT": "215",
                b"LIST ACTIVE.TIMES": "215", b"LIST HEADERS": "215",
            }
            self.assertEqual(code(client.command(b"MODE READER")), "200")
            for command, want in expected.items():
                self.assertEqual(code(client.multiline(command)[0]), want, command)
            group = client.command(b"GROUP " + GROUP.encode())
            self.assertEqual(group.split()[:4], [b"211", b"1", b"1", b"1"])
            for command, want in (
                    (b"LISTGROUP " + GROUP.encode() + b" 1-1", "211"),
                    (b"ARTICLE 1", "220"), (b"HEAD 1", "221"), (b"BODY 1", "222"),
                    (b"ARTICLE " + self.message_id.encode(), "220"),
                    (b"ARTICLE <absent@example.invalid>", "430"),
                    (b"OVER 1", "224"), (b"OVER 1-1", "224"), (b"HDR Subject 1", "225"),
                    (b"XOVER 1-1", "224"), (b"XHDR Subject 1", "221"),
                    (b"XPAT Subject 1-1 *", "221"), (b"HELP", "100")):
                self.assertEqual(code(client.multiline(command)[0]), want, command)
            self.assertEqual(code(client.command(b"STAT 1")), "223")
            status, found = client.multiline(b"NEWNEWS " + GROUP.encode() + b" 19700101 000000 GMT")
            self.assertEqual(code(status), "230")
            self.assertIn(self.message_id.encode(), found)                   # NEWNEWS-STAMP
            status, future = client.multiline(b"NEWNEWS " + GROUP.encode()
                                              + b" 20990101 000000 GMT")
            self.assertEqual((code(status), future), ("230", b""))
            self.assertEqual(code(client.command(b"NEWNEWS [ 19700101 000000 GMT")), "501")
            client.command(b"STAT 1")
            self.assertEqual(code(client.command(b"NEXT")), "421")           # one article
            self.assertEqual(code(client.command(b"LAST")), "422")
            date = client.command(b"DATE")
            self.assertEqual(code(date), "111")
            self.assertEqual(code(client.command(b"FNBOGUS")), "500")
        with self.session() as split:                                        # FRAMING
            split.send(b"DAT")
            time.sleep(0.4)
            split.send(b"E\r\n")
            self.assertEqual(code(split.line()), "111")

    def test_capabilities_are_exactly_what_is_dispatched(self):
        """V0-PIN-DISPATCHED, V0-PIN-ADVERTISED (NNT-001, RFC 3977 5.2.2):
        every advertised label with a probe answers as available, and every
        RFC label whose command is available is advertised."""
        probes = {
            "READER": b"GROUP " + GROUP.encode(), "POST": b"POST",
            "IHAVE": b"IHAVE <pin.probe@example.invalid>", "STREAMING": b"MODE STREAM",
            "OVER": b"OVER 1", "HDR": b"HDR Subject 1", "LIST": b"LIST ACTIVE",
            "NEWNEWS": b"NEWNEWS * 20200101 000000 GMT", "XPAT": b"XPAT Subject 1 *",
        }
        unavailable = ("500", "501", "502", "440", "480", "483")
        with self.session() as client:
            advertised = capability_labels(client)
        answered = {}
        for label, command in probes.items():
            with self.session() as probe:
                reply = probe.command(command)
                answered[label] = code(reply)
                if reply[:1] in b"34" and label in ("POST", "IHAVE"):
                    probe.send(b".\r\n")
                    probe.line()
        dispatched = {label for label, reply in answered.items() if reply not in unavailable}
        self.assertEqual(sorted(set(advertised) & set(probes) - dispatched), [], answered)
        self.assertEqual(sorted(dispatched - set(advertised)), [], (advertised, answered))

    def test_a_reader_stays_live_across_another_connections_post(self):
        """V0-POST-CONCURRENT."""
        with self.session() as watcher, self.session() as poster:
            self.assertEqual(code(watcher.command(b"GROUP " + GROUP.encode())), "211")
            concurrent = "<concurrent@example.invalid>"
            self.assertEqual(code(poster.command(b"POST")), "340")
            self.assertEqual(code(watcher.command(b"GROUP " + GROUP.encode())), "211")
            poster.send(dot_stuff(article(concurrent, groups="fn.side")) + b".\r\n")
            self.assertEqual(code(poster.line()), "240")
            self.assertEqual(code(watcher.command(b"DATE")), "111")


@requires(IMAGE)
class AuthinfoRows(unittest.TestCase):
    """AUTHINFO (RFC 4643) on a node with one credential, and on one that
    requires authentication."""

    def node(self, required):
        node = Node(self, IMAGE)
        node.init(GROUP)
        if required:
            node.write_config(extra="[auth]\nrequired = true\n")
        node.operator("principal", "set-password", "matrix", input=SECRET.encode(),
                      expect=EXIT.OK)
        node.start()
        return node

    def login(self, client, secret="matrix-secret-8f21"):
        self.assertEqual(code(client.command(b"AUTHINFO USER matrix")), "381")
        return client.command(b"AUTHINFO PASS " + secret.encode())

    def test_advertised_login_withdrawn_post_and_wrong(self):
        """V0-AUTH-ADVERTISED, -LOGIN, -WITHDRAWN, -POST, -WRONG."""
        node = self.node(required=False)
        with node.session() as wrong:
            self.assertEqual(code(self.login(wrong, "not-the-secret")), "481")
            self.assertIn("AUTHINFO", capability_labels(wrong))
        with node.session() as client:
            self.assertIn("AUTHINFO", capability_labels(client))
            self.assertEqual(code(self.login(client)), "281")
            self.assertNotIn("AUTHINFO", capability_labels(client))
            message_id = "<auth-post@example.invalid>"
            _, final = post_over(client, article(message_id, groups=GROUP))
            self.assertEqual(code(final), "240")

    def test_post_before_a_login_is_refused_where_authentication_is_required(self):
        """V0-AUTH-GATED."""
        node = self.node(required=True)
        with node.session(greeting=(b"200", b"201")) as client:
            self.assertEqual(code(client.command(b"POST")), "480")
            self.assertEqual(code(self.login(client)), "281")


@requires(IMAGE)
class TransitCommandRows(unittest.TestCase):
    """The transit commands a peer's connection answers (RFC 3977 6.3.2, RFC
    4644, RFC 5537 3.5), offered by a raw client from the peer's address."""

    def setUp(self):
        self.node = Node(self, IMAGE)
        self.node.init(GROUP)
        self.node.operator("peer", "add", "source", "source.example.invalid", "127.0.0.1",
                           "11998", "fn.*", "-", "127.0.0.1", "true", expect=EXIT.OK)
        self.node.operator("policy", "set", "path-identity", "target.example.invalid",
                           expect=EXIT.OK)
        self.node.start()

    def offered(self, message_id, path="source.example.invalid!not-for-mail"):
        return (b"Path: " + path.encode() + b"\r\n"
                + article(message_id, groups=GROUP, subject="transit"))

    def test_ihave_duplicate_loop_and_streaming(self):
        """V0-TRANSIT-MODE-STREAM, V0-TRANSIT-LOOP, V0-TRANSIT-LOOP-ABSENT,
        V0-TRANSIT-CHECK-FRESH, V0-TRANSIT-TAKETHIS, V0-TRANSIT-CHECK-DUP,
        V0-TRANSIT-TAKETHIS-DUP (and OFFER/TRANSFER/DUPLICATE again)."""
        held = "<transit-held@example.invalid>"
        with Client(self.node.port) as peer:
            first, final = peer.post(self.offered(held), verb=b"IHAVE " + held.encode())
            self.assertEqual((code(first), code(final)), ("335", "235"))
            self.assertEqual(code(peer.command(b"IHAVE " + held.encode())), "435")
            loop = "<transit-loop@example.invalid>"
            first, final = peer.post(
                self.offered(loop, "target.example.invalid!source.example.invalid!not-for-mail"),
                verb=b"IHAVE " + loop.encode())
            self.assertEqual((code(first), code(final)), ("335", "437"))
            self.assertEqual(code(peer.command(b"STAT " + loop.encode())), "430")
            self.assertEqual(code(peer.command(b"MODE STREAM")), "203")
            fresh = "<transit-stream@example.invalid>"
            self.assertEqual(peer.command(b"CHECK " + fresh.encode()),
                             b"238 " + fresh.encode() + b"\r\n")
            peer.send(b"TAKETHIS " + fresh.encode() + b"\r\n"
                      + dot_stuff(self.offered(fresh)) + b".\r\n")
            self.assertEqual(peer.line(), b"239 " + fresh.encode() + b"\r\n")
            self.assertEqual(peer.command(b"CHECK " + held.encode()),
                             b"438 " + held.encode() + b"\r\n")
            peer.send(b"TAKETHIS " + held.encode() + b"\r\n"
                      + dot_stuff(self.offered(held)) + b".\r\n")
            self.assertEqual(peer.line(), b"439 " + held.encode() + b"\r\n")
        self.assertIsNone(self.node.process.poll())


if __name__ == "__main__":
    unittest.main()
