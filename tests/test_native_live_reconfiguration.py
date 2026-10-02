"""Live reconfiguration on a running owner (plan T8).

Subjects, in the order the live arm meets them:

* `operator CONFIG group create NAME` and `operator CONFIG peer add ...` while
  an owner holds the store go over its control socket to
  `fnn-owner-live-admin-serialized` (host/native/admin.lisp), which stages
  `fn-native-admin-plan-deltas` (books/native-admin.lisp) through
  `fn-ocfg-step`, publishes the record and completes it.
* A reader connection opened before the change keeps its archived domain and
  config pin; a new connection sees the live Store domain without a restart
  (`fn-ocl-complete-preserves-pinned-connection-histories`,
  books/config-owner-live-complete.lisp).
* The second of two live reconfigurations is published: the one the old
  `fn-ocfg-complete` could not publish after a live group creation.
* The durable history is what a restart reads: `peer list` after the owner
  stops shows the peer the live owner added
  (`fn-ocfg-crash-at-any-instant-recovers-the-live-generation`).

* The offline executor over the same store, reached through a configuration
  whose control path nothing has bound, is refused at the writer lock while
  the owner lives, and the owner is still serving afterwards (V0-CFG-LIVE-REFUSE).
* The live verb answers and the owner keeps serving: on the dabebb84 image
  every live request faulted the owner in `fnn-owner-live-admin-serialized'
  and the caller saw the lost reply as uncertain (V0-CFG-LIVE).

The source checks are always active.  The executable witnesses need the saved
image; when it is absent they skip and name the image they wanted, rather than
a source inspection being reported as runtime evidence.
"""
import unittest

from tests.campaign import native_cuts
from tests.native_harness import EXIT_OK, EXIT_REFUSED, ROOT, Node, native_image, requires


IMAGE = native_image("FN_NATIVE_HOST")

PEER_ADD = ("peer", "add", "far", "far.example.invalid", "192.0.2.44", "1119",
            "fn.*", "-", "192.0.2.44", "true")
PEER_ROW = ("far path-identity=far.example.invalid address=192.0.2.44 "
            "port=1119 security=clear inbound=fn.* outbound=- "
            "auth=source-address:192.0.2.44")


class LiveReconfigurationSourceTests(unittest.TestCase):
    """What the source says, whether or not an image was built."""

    def setUp(self):
        self.bridge = (ROOT / "host" / "native-admin-host.lisp").read_text(encoding="ascii")
        self.admin = (ROOT / "books" / "native-admin.lisp").read_text(encoding="ascii")
        self.owner_config = (ROOT / "books" / "owner-config.lisp").read_text(encoding="ascii")
        self.native_admin = (ROOT / "host" / "native" / "admin.lisp").read_text(encoding="ascii")

    def test_the_live_arm_stages_acls_delta_list_and_builds_none(self):
        start = self.bridge.index("(defun fn-native-admin-host-owner-reconfigure")
        end = self.bridge.index("(defun fn-native-admin-host-apply", start)
        body = self.bridge[start:end]
        # PRF-099: the delta list is built over the live owner's peer table
        # (`fn-native-admin-plan-deltas-over`), which is
        # `fn-native-admin-plan-deltas` for every plan but :extend-peer
        # (fn-native-admin-plan-deltas-over-other-plans-by-definition).
        self.assertIn("(fn-native-admin-plan-deltas-over plan "
                      "(fn-cfg-peers (fn-cfg-value (fn-owner-config state))))",
                      " ".join(body.split()))
        # (the arena threaded through since the records flip)
        self.assertIn("(fn-owner-reconfigure-deltas id deltas fn-arena state)", body)
        # No delta constructor and no octet/string conversion in the bridge:
        # the labels' type is decided once, in the book.
        for forbidden in ("fn-cfg-create-group", "fn-cfg-remove-group",
                          "fn-cfg-remove-peer-delta", "fn-cfg-set-peer-delta",
                          "fn-cfg-set-policy", "octets->string"):
            self.assertNotIn(forbidden, body)
        self.assertIn("(defun fn-native-admin-plan-deltas (plan)", self.admin)
        self.assertIn("(defun fn-native-admin-plan-deltas-over (plan peers)", self.admin)
        self.assertIn("(defthm fn-native-admin-plan-deltas-over-other-plans-by-definition",
                      self.admin)
        self.assertIn("(defthm fn-native-admin-live-group-delta-is-a-typed-delta", self.admin)

    def test_completion_publishes_what_recovery_replays(self):
        live = (ROOT / "books" / "config-owner-live-complete.lisp").read_text(encoding="ascii")
        start = live.index("(defun fn-ocl-complete (oc)")
        end = live.index("(defthm", start)
        body = live[start:end]
        self.assertIn("(fn-cpo-configure-durable old-store record)", body)
        self.assertIn("(fn-ocl-store-config new-store)", body)
        self.assertIn("(fn-ocfg-pins oc)", body)
        self.assertNotIn("fn-cnode-apply-config", body)
        for name in ("fn-ocl-complete-keeps-existing-served-table",
                     "fn-ocl-complete-preserves-pinned-connection-histories"):
            self.assertIn("(defthm " + name, live)

    def test_actual_native_open_and_completion_call_the_physical_history_model(self):
        owner = (ROOT / "host" / "owner-host.lisp").read_text(encoding="ascii")
        store = (ROOT / "host" / "store-node-host.lisp").read_text(encoding="ascii")
        live = (ROOT / "books" / "config-owner-live-complete.lisp").read_text(encoding="ascii")
        # Both Store opens extend a checkpoint once and open from it
        # (fn-sco-store-open-of-extended-capture: the full open
        # fn-cpo-open-observed); the owner installs from that open.
        # Over the held rows since the records flip: fn-rii-sco-extend, EQUAL
        # to fn-sco-extend (books/replay-identity-index.lisp
        # fn-rii-sco-extend-is-sco-extend).  Since snapshot-open-2 the full
        # open (fn-store-sn-recover-rows) calls the extension and its open as
        # one, fn-rii-sco-extend-open, which is that extension then
        # fn-rii-classified-open of it (KEYSTONE
        # fn-rii-sco-extend-open-is-extend-then-open).  The call is read from
        # the host function, not from the file's layout.
        recover_rows = " ".join(native_cuts.host_function(store, "fn-store-sn-recover-rows").split())
        self.assertIn("(fn-rii-sco-extend-open (fn-sco-capture config-records nil) "
                      "config-records rows frontier)", recover_rows)
        rii = (ROOT / "books" / "replay-identity-index.lisp").read_text(encoding="ascii")
        for name in ("fn-rii-sco-extend-is-sco-extend", "fn-rii-sco-extend-open-is-extend-then-open"):
            self.assertIn("(defthm " + name, rii)
        self.assertIn("(fn-rii-sco-extend ", native_cuts.book_function("fn-rii-sco-extend-open")[1])
        # Directly or through the book wrapper the host calls in its place
        # (fn-sopc-classified-open since 2e25e21b; since replay-identity the
        # host calls fn-rii-classified-open, EQUAL to it by the keystone
        # fn-rii-classified-open-is-classified-open, and it calls
        # fn-sco-store-open).
        self.assertTrue(native_cuts.calls_through_book(
            native_cuts.host_function(store, "fn-store-sn-open-extended"),
            "fn-rii-sco-store-open", "e config-records frontier"))
        self.assertIn("(defthm fn-rii-classified-open-is-classified-open",
                      (ROOT / "books" / "replay-identity-index.lisp").read_text(encoding="ascii"))
        self.assertIn("(fn-sco-store-open e configs frontier)",
                      native_cuts.book_function("fn-sopc-classified-open")[1])
        self.assertIn("(fn-ock-install (cadr opened) (caddr opened) max-conns)", owner)
        publish = (ROOT / "books" / "config-owner-publish.lisp").read_text(encoding="ascii")
        # The carried completion since PKT-827 (PRF-274): fn-oclc-publish,
        # fn-ocl-publish under the owner's invariant (fn-oclc-publish-is-publish)
        # and carrying it (fn-oclc-publish-carries-ocl-relation).
        self.assertIn("(fn-oclc-publish (fn-owner-ocfg state) generation", owner)
        carried = (ROOT / "books" / "config-owner-carried.lisp").read_text(encoding="ascii")
        for name in ("fn-oclc-publish-is-publish", "fn-oclc-publish-carries-ocl-relation"):
            self.assertIn("(defthm " + name, carried)
        self.assertIn("(fn-ocl-complete oc)", publish)
        self.assertIn("(fn-ocl-request-deltas kind name)", owner)
        self.assertNotIn("(defun fn-owner-config-deltas", owner)
        self.assertIn("(fn-own-refresh", live)

    def test_the_live_arm_is_the_event_sequence_the_theorem_names(self):
        # reconfigure, close the private connection, publish, complete.  The
        # sequence is `fnn-owner-live-reconfigure-locked' (shared with the
        # peering verbs, host/native/peer-invite.lisp); the admin arm stages
        # through it with `fn-native-admin-host-owner-reconfigure'.
        start = self.native_admin.index("(defun fnn-owner-live-reconfigure-locked")
        body = self.native_admin[start:self.native_admin.index(
            "(defun fnn-owner-live-admin-serialized", start)]
        order = [body.index(word) for word in (
            "'fn-owner-open", "(funcall stage cid)",
            "'fn-owner-close", "(fnn-admin-publish", "'fn-owner-reconfigure-complete")]
        self.assertEqual(order, sorted(order))
        start = self.native_admin.index("(defun fnn-owner-live-admin-serialized")
        arm = self.native_admin[start:self.native_admin.index("(defun fnn-admin-query", start)]
        self.assertIn("'fn-native-admin-host-owner-reconfigure", arm)
        self.assertIn("(fnn-owner-live-reconfigure-locked", arm)

    def test_the_live_arm_reads_the_open_connection_id_as_an_id(self):
        # `fn-owner-open' answers an integer id or NIL; `fnn-owner-action'
        # faults on anything but a keyword, so reading the id through it
        # stopped the owner on every live request (dabebb84, V0-CFG-LIVE).
        start = self.native_admin.index("(defun fnn-owner-live-reconfigure-locked")
        body = self.native_admin[start:self.native_admin.index("(defun fnn-admin-query", start)]
        self.assertIn("(fnn-owner-core 'fn-owner-open)", body)
        self.assertNotIn("(fnn-owner-action 'fn-owner-open)", body)
        def body_of(text, head):
            at = text.index(head)
            return text[at:text.index("(defun", at + 10)]
        bridge = (ROOT / "host" / "owner-host.lisp").read_text(encoding="ascii")
        # Since 1bf2ddcaf the host entry fn-owner-open is the guarded
        # callback of books/owner-connection-callbacks.lisp.
        self.assertIn("(fn-owner-callback-open state)",
                      body_of(bridge, "(defun fn-owner-open (state)"))
        book = (ROOT / "books" / "owner-connection-callbacks.lisp").read_text(encoding="ascii")
        # Since PKT-828 the open runs open-at at the reader view and puts the
        # working view back; the id is answered there.
        open_body = body_of(book, "(defun fn-owner-callback-open (state)")
        order = [open_body.index(word) for word in (
            "(fn-owner-callback-at-reader-view state)",
            "(fn-owner-callback-open-at state)",
            "(fn-owner-callback-at-working-view working state)")]
        self.assertEqual(order, sorted(order))
        self.assertIn("(value id)", body_of(book, "(defun fn-owner-callback-open-at (state)"))

    def test_publication_is_authorized_on_the_stores_own_lock_observation(self):
        start = self.native_admin.index("(defun fnn-admin-authorize")
        body = self.native_admin[start:self.native_admin.index("(defun", start + 10)]
        self.assertIn("(fnn-admin-lock-observation store)", body)
        self.assertIn(
            "(defthm fn-native-admin-publication-is-authorized-only-under-the-lock",
            self.admin)

    def test_a_request_being_answered_is_not_shut_by_the_stop_it_caused(self):
        control = (ROOT / "host" / "native" / "control.lisp").read_text(encoding="ascii")
        start = control.index("(defun fnn-control-handle-client")
        body = control[start:control.index("(defun fnn-control-client-done", start)]
        self.assertIn("(fnn-control-answering control socket)", body)
        self.assertLess(body.index("fnn-control-read-frame"),
                        body.index("(fnn-control-answering control socket)"))


@requires(IMAGE)
class LiveReconfigurationImageTests(unittest.TestCase):
    """The live arm runs only in a saved image with a control socket."""

    def setUp(self):
        self.node = Node(self, IMAGE)
        self.root, self.store = self.node.root, self.node.store_path
        self.node.init()

    def operator(self, *words, timeout=180):
        return self.node.operator(*words, timeout=timeout)

    def reader(self):
        client = self.node.session()
        self.addCleanup(client.close)
        return client

    def test_a_live_peer_add_leaves_a_pinned_reader_unchanged_and_is_durable(self):
        owner = self.node.start()
        client = self.reader()
        before = client.multiline("LIST ACTIVE")
        self.assertTrue(before[0].startswith(b"215"), before)

        # Two live reconfigurations: the group creation the octet labels used
        # to refuse, then the peer addition the old completion could not
        # publish after a group creation.
        created = self.operator("group", "create", "fn.live")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        added = self.operator(*PEER_ADD)
        self.assertEqual(added.returncode, EXIT_OK, added.stderr.decode())

        # The reader opened before both changes answers exactly as before.
        after = client.multiline("LIST ACTIVE")
        self.assertEqual(after, before)

        # A live `peer list` is answered by the running owner over its control
        # path (the selected contract since the live query verbs; qual-bbf52159
        # C3), not by a second process taking the store: it shows the peer
        # just added, and the owner keeps serving the pinned reader.
        live_list = self.operator("peer", "list")
        self.assertEqual(live_list.returncode, EXIT_OK, live_list.stderr.decode())
        self.assertEqual(live_list.stdout.decode("ascii").splitlines(), [PEER_ROW])
        self.assertEqual(client.multiline("LIST ACTIVE"), before)

        self.node.stop(process=owner)

        # What a restart reads: both records are durable.
        listed = self.operator("peer", "list")
        self.assertEqual(listed.returncode, EXIT_OK, listed.stderr.decode())
        self.assertEqual(listed.stdout.decode("ascii").splitlines(), [PEER_ROW])

        restarted = self.node.start()
        fresh_client = self.reader()
        status = fresh_client.command("GROUP fn.live")
        self.assertTrue(status.startswith(b"211"), status)
        self.node.stop(process=restarted)

    def config_files(self):
        directory = self.store / "config"
        return sorted(p.name for p in directory.iterdir()) if directory.is_dir() else []

    def test_the_live_verb_answers_and_the_owner_keeps_serving(self):
        # V0-CFG-LIVE on the dabebb84 image: exit 3, and GROUP on the socket
        # got a refused connection because the owner had stopped.
        owner = self.node.start()
        before = self.config_files()
        created = self.operator("group", "create", "fn.live")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.assertIsNone(owner.poll(), "the live verb stopped the owner")
        self.assertEqual(len(self.config_files()), len(before) + 1)
        client = self.reader()
        status = client.command("GROUP fn.test")
        self.assertTrue(status.startswith(b"211"), status)
        self.node.stop(process=owner)

    def test_an_offline_mutation_is_refused_at_the_lock_while_the_owner_lives(self):
        # V0-CFG-LIVE-REFUSE: a second configuration over the SAME store whose
        # control path nothing has bound takes the offline executor.
        offline = self.root / "offline.toml"
        offline.write_text(
            '[store]\npath = "{}"\n[control]\npath = "{}"\n'.format(
                self.store, self.root / "never-bound.sock"), encoding="ascii")

        def offline_create(name):
            return self.node.invoke("operator", offline, "group", "create", name)

        owner = self.node.start()
        before = self.config_files()
        refused = offline_create("fn.offline")
        self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
        # The named refusal (books/native-control.lisp, the :store-held
        # route): the lock is held and the configured control socket does
        # not reach its holder, so the offline executor is not started.
        self.assertIn(b"refused store-held", refused.stderr)
        self.assertEqual(self.config_files(), before)
        self.assertIsNone(owner.poll(), "the offline command disturbed the owner")
        self.node.stop(process=owner)
        # The separating witness: the same words over the same store, with
        # no owner, are accepted.  The refusal above was the lock's.
        accepted = offline_create("fn.offline")
        self.assertEqual(accepted.returncode, EXIT_OK, accepted.stderr.decode())
        self.assertEqual(len(self.config_files()), len(before) + 1)

    def test_a_group_created_live_is_served_before_restart(self):
        owner = self.node.start()
        old_client = self.reader()
        old_before = old_client.multiline("LIST ACTIVE")
        self.assertTrue(old_before[0].startswith(b"215"), old_before)
        created = self.operator("group", "create", "fn.live")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        old_after = old_client.multiline("LIST ACTIVE")
        self.assertEqual(old_after, old_before)
        client = self.reader()
        status = client.command("GROUP fn.live")
        fresh_list = client.multiline("LIST ACTIVE")
        self.node.stop(process=owner)
        self.assertTrue(status.startswith(b"211"), status)
        self.assertTrue(fresh_list[0].startswith(b"215"), fresh_list)
        self.assertIn(b"fn.live ", fresh_list[1], fresh_list)


if __name__ == "__main__":
    unittest.main()
