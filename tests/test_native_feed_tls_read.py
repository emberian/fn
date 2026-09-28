#!/usr/bin/env python3
"""Defect M3: the outbound feed over implicit TLS 1.3 with session tickets.

A TLS 1.3 server sends its NewSessionTicket records after the handshake and
before any application data.  An SSL_read that consumes only such a record
returns WANT_READ: that is "no data yet", never an I/O failure
(host/native/tls.lisp fnn-tls-read).  Before the fix the feed's zero-second
read turned it into fnn-tls-io-error, the pump dropped the link without a
line, and redialled at the peer record's constant backoff forever.

Three witnesses, each on scratch nodes over loopback:

* a scripted TLS 1.3 peer that sends its tickets and only then, 400 ms
  later, its greeting: the feed must keep the one connection and deliver;
* a scripted TLS 1.3 peer that closes every session after its tickets: every
  drop is logged by ACL2's line (books/feed-link-backoff.lisp
  fn-flb-drop-line) and the redial delay doubles (fn-flb-lost);
* two fn nodes peered over their implicit-TLS listeners with AUTHINFO, both
  directions (fn's own server issues TLS 1.3 tickets by default).
"""

from __future__ import annotations

import json
import re
import socket
import ssl
import threading
import time
import unittest

from tests import test_native_peering as peer
from tests import test_native_protected_peering as protected
from tools.wire_stream import whole_stream

IMAGE = peer.IMAGE
READY = peer.READY


class TicketingTlsPeer(peer.ScriptedTransitPeer):
    """ScriptedTransitPeer behind implicit TLS 1.3 with session tickets.

    GREETING_DELAY seconds pass between the end of the server handshake
    (when OpenSSL has written the tickets) and the 200 greeting.  With
    CLOSE_AFTER_TICKETS the session sends close_notify instead of a
    greeting.  Every accepted connection's monotonic time is recorded.
    """

    def __init__(self, certificate, key, greeting_delay=0.0,
                 close_after_tickets=False):
        self.context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        self.context.minimum_version = ssl.TLSVersion.TLSv1_3
        self.context.load_cert_chain(str(certificate), str(key))
        self.context.num_tickets = 2
        self.greeting_delay = greeting_delay
        self.close_after_tickets = close_after_tickets
        self.accepted = []
        self.handshakes = 0
        super().__init__("203 streaming permitted")

    def session(self, client, number):
        with self.lock:
            self.accepted.append(time.monotonic())
        try:
            tls = self.context.wrap_socket(client, server_side=True)
        except (ssl.SSLError, OSError):
            client.close()
            return
        with self.lock:
            self.handshakes += 1
        with tls:
            if self.close_after_tickets:
                time.sleep(0.2)
                try:
                    tls.unwrap()
                except (ssl.SSLError, OSError):
                    pass
                return
            time.sleep(self.greeting_delay)
            stream = whole_stream(tls)
            stream.write(b"200 ticketing transit peer\r\n")
            while True:
                try:
                    line = stream.readline()
                except (ssl.SSLError, OSError):
                    return
                if not line:
                    return
                text = line.rstrip(b"\r\n").decode("ascii", "replace")
                with self.lock:
                    self.commands.append((number, text))
                words = text.split()
                verb = words[0].upper() if words else ""
                if verb == "MODE":
                    stream.write(self.mode_reply.encode("ascii") + b"\r\n")
                elif verb == "CHECK":
                    stream.write(b"238 " + words[1].encode("ascii") + b"\r\n")
                elif verb == "TAKETHIS":
                    article = self.read_article(stream)
                    with self.lock:
                        self.articles[words[1]] = ("TAKETHIS", article)
                    stream.write(b"239 " + words[1].encode("ascii") + b"\r\n")
                elif verb == "IHAVE":
                    stream.write(b"335 send it\r\n")
                    article = self.read_article(stream)
                    with self.lock:
                        self.articles[words[1]] = ("IHAVE", article)
                    stream.write(b"235 article transferred OK\r\n")
                elif verb == "QUIT":
                    stream.write(b"205 bye\r\n")
                    return
                else:
                    stream.write(b"500 unknown command\r\n")


@unittest.skipUnless(READY, "set explicit native image/source and matching launcher/core SHA-256 values")
class NativeFeedTlsReadTests(unittest.TestCase):
    """Scratch nodes only; never the live nodes.  The protected module's
    helpers are borrowed, never its tests."""

    # Bound through the module, never as a module-level TestCase name, so
    # the loader does not collect the protected module's tests here.
    setUp = protected.NativeProtectedPeeringTests.setUp
    command = protected.NativeProtectedPeeringTests.command
    process_identity = protected.NativeProtectedPeeringTests.process_identity
    verify_process_identity = protected.NativeProtectedPeeringTests.verify_process_identity
    article = staticmethod(peer.NativePeeringTests.article)
    post = protected.NativeProtectedPeeringTests.post
    await_article = protected.NativeProtectedPeeringTests.await_article
    article_from = protected.NativeProtectedPeeringTests.article_from
    make_certificate = protected.NativeProtectedPeeringTests.make_certificate
    initialize = protected.NativeProtectedPeeringTests.initialize
    profile = protected.NativeProtectedPeeringTests.profile
    start = protected.NativeProtectedPeeringTests.start

    stop_all = protected.NativeProtectedPeeringTests.stop_all

    def plain_source(self, name):
        node = peer.NativePeeringTests.initialize(self, name, peer.free_port())
        return node

    def start_plain(self, node):
        peer.NativePeeringTests.start(self, node)

    def configure_tls_peer(self, source, target_name, port, anchor):
        self.command([
            IMAGE, "--fn", "operator", source["config"], "peer", "add",
            target_name, target_name + ".example.invalid", "127.0.0.1",
            str(port), "fn.*", "fn.*", "source-address", "127.0.0.1", "true",
            "implicit", "localhost", anchor,
        ])

    def scripted(self, name, **options):
        certificate, key = self.make_certificate(self.base, name)
        scripted = TicketingTlsPeer(certificate, key, **options)
        self.addCleanup(scripted.close)
        return scripted, certificate

    def stderr_text(self, node):
        return node["process"].stderr.since(0).decode("utf-8", "replace")

    def test_greeting_after_session_tickets_keeps_the_link(self):
        scripted, certificate = self.scripted("late-greeting", greeting_delay=0.4)
        source = self.plain_source("ticket-source")
        self.configure_tls_peer(source, "late", scripted.port, certificate)
        self.start_plain(source)
        message_id = "<tickets-then-greeting@example.invalid>"
        self.post(source, message_id, "tickets")
        got = scripted.await_article(message_id, timeout=30)
        with scripted.lock:
            commands = list(scripted.commands)
            handshakes = scripted.handshakes
        stderr = self.stderr_text(source)
        self.assertIsNotNone(got, "no delivery after tickets: handshakes={} "
                             "commands={} stderr={}".format(
                                 handshakes, commands, stderr[-4000:]))
        self.assertEqual(got[0], "TAKETHIS")
        # One connection carried MODE STREAM, CHECK and TAKETHIS.
        self.assertEqual({n for n, _ in commands}, {1}, commands)
        self.assertNotIn("link=dropped", stderr)
        print("NATIVE-FEED-TLS-READ-WITNESS " + json.dumps({
            "kind": "tickets-then-greeting", "handshakes": handshakes,
            "commands": commands}, sort_keys=True), flush=True)

    def test_a_failing_link_names_each_drop_and_backs_off(self):
        scripted, certificate = self.scripted("closing", close_after_tickets=True)
        source = self.plain_source("backoff-source")
        self.configure_tls_peer(source, "closing", scripted.port, certificate)
        self.start_plain(source)
        self.post(source, "<backoff@example.invalid>", "backoff")
        deadline = time.monotonic() + 40
        while time.monotonic() < deadline:
            with scripted.lock:
                if len(scripted.accepted) >= 5:
                    break
            time.sleep(0.1)
        with scripted.lock:
            accepted = list(scripted.accepted)
        stderr = self.stderr_text(source)
        self.assertGreaterEqual(len(accepted), 5, (accepted, stderr[-4000:]))
        gaps = [b - a for a, b in zip(accepted, accepted[1:])]
        # ACL2's delays after consecutive losses: 1000, 2000, 4000, 8000 ms
        # (base 1000 from `peer add`, fn-flb-lost doubling).  The gaps carry
        # the handshake and the worker's cadence on top.
        for gap, delay in zip(gaps, (1.0, 2.0, 4.0, 8.0)):
            self.assertGreaterEqual(gap, delay * 0.95, (gaps, stderr[-4000:]))
            self.assertLess(gap, delay + 1.5, (gaps, stderr[-4000:]))
        drops = re.findall(r"feed peer=closing link=dropped reason=(\S+) retry-ms=(\d+)",
                           stderr)
        self.assertGreaterEqual(len(drops), 4, stderr[-4000:])
        self.assertEqual([int(ms) for _, ms in drops[:4]], [1000, 2000, 4000, 8000],
                         drops)
        self.assertTrue(all(reason == "lost-eof" for reason, _ in drops[:4]), drops)
        print("NATIVE-FEED-TLS-READ-WITNESS " + json.dumps({
            "kind": "drop-lines-and-backoff", "gaps": [round(g, 3) for g in gaps],
            "drops": drops[:6]}, sort_keys=True), flush=True)

    def test_a_paused_feed_is_not_dialled_until_resumed(self):
        """`peer feed NAME pause' closes the peer's link and stops dialling
        it without removing the peer; `resume' delivers what queued."""
        scripted, certificate = self.scripted("pausable")
        source = self.plain_source("pause-source")
        self.configure_tls_peer(source, "pausable", scripted.port, certificate)
        self.start_plain(source)
        first = "<before-pause@example.invalid>"
        self.post(source, first, "before-pause")
        self.assertIsNotNone(scripted.await_article(first, timeout=30))
        self.command([IMAGE, "--fn", "operator", source["config"], "peer", "feed",
                      "pausable", "pause"])
        with scripted.lock:
            accepted = len(scripted.accepted)
        held = "<while-paused@example.invalid>"
        self.post(source, held, "while-paused")
        time.sleep(5)
        with scripted.lock:
            self.assertNotIn(held, scripted.articles)
            self.assertEqual(len(scripted.accepted), accepted, scripted.accepted)
        self.command([IMAGE, "--fn", "operator", source["config"], "peer", "feed",
                      "pausable", "resume"])
        got = scripted.await_article(held, timeout=30)
        self.assertIsNotNone(got, self.stderr_text(source)[-4000:])
        print("NATIVE-FEED-TLS-READ-WITNESS " + json.dumps({
            "kind": "feed-pause-resume", "held_delivered_after_resume": True,
            "connections": len(scripted.accepted)}, sort_keys=True), flush=True)

    def initialize_implicit(self, name, login, password):
        node = self.initialize(name, peer.free_port(), login, password)
        node["tls_port"] = peer.free_port()
        text = node["config"].read_text(encoding="ascii")
        text = text.replace("[control]", "tls_port = {}\n[control]".format(
            node["tls_port"]), 1)
        node["config"].write_text(text, encoding="ascii")
        return node

    def configure_implicit_peer(self, source, target, profile):
        self.command([
            IMAGE, "--fn", "operator", source["config"], "peer", "add",
            target["name"], target["name"] + ".example.invalid", "127.0.0.1",
            str(target["tls_port"]), "fn.*", "fn.*", "principal",
            source["principal"], profile, "false", "true", "implicit",
            "localhost", target["certificate"],
        ])

    def test_two_nodes_peer_both_ways_over_implicit_tls(self):
        a = self.initialize_implicit("implicit-a", "b-at-a", "b-secret")
        b = self.initialize_implicit("implicit-b", "a-at-b", "a-secret")
        self.configure_implicit_peer(a, b, self.profile(a, b))
        self.configure_implicit_peer(b, a, self.profile(b, a))
        self.start(a)
        self.start(b)
        transit = {}
        for source, target, label in ((a, b, "a-to-b"), (b, a, "b-to-a")):
            message_id = "<implicit-{}@example.invalid>".format(label)
            self.post(source, message_id, label)
            identical = (self.await_article(target, message_id)
                         == self.await_article(source, message_id))
            self.assertTrue(identical)
            transit[label] = identical
        for node in (a, b):
            text = node["stderr_path"].read_text(errors="replace")
            self.assertNotIn("link=dropped", text, text[-4000:])
        print("NATIVE-FEED-TLS-READ-WITNESS " + json.dumps({
            "kind": "implicit-tls-two-nodes", "transit": transit},
            sort_keys=True), flush=True)


if __name__ == "__main__":
    unittest.main()
