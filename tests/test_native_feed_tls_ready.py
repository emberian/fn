"""PKT-599(b): STARTTLS must install a non-streaming, unauthenticated feed.

Scratch loopback only. The scripted peer records the real native owner's
commands and transferred article; implicit TLS is the greeting-path control.
The peer offers no login and no MODE STREAM exchange to mask a missing install.
"""
from __future__ import annotations

import json
import ssl
import unittest

from tests import test_native_peering as peer
from tests import test_native_protected_peering as protected
from tests.native_harness import EXIT_OK
from tools.wire_stream import whole_stream


class NoLoginTlsPeer(peer.ScriptedTransitPeer):
    def __init__(self, certificate, key, mode):
        self.mode = mode
        self.context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        self.context.load_cert_chain(certificate, key)
        self.handshakes = 0
        self.errors = []
        super().__init__("500 streaming unavailable")

    def session(self, client, number):
        client.settimeout(20)
        try:
            if self.mode == "starttls":
                stream = whole_stream(client)
                stream.write(b"200 scratch TLS transit peer\r\n")
                line = stream.readline()
                with self.lock:
                    self.commands.append((number, line.decode("ascii").strip()))
                if line != b"STARTTLS\r\n":
                    raise AssertionError("expected STARTTLS, got {!r}".format(line))
                stream.write(b"382 continue with TLS\r\n")
            with self.context.wrap_socket(client, server_side=True) as tls:
                with self.lock:
                    self.handshakes += 1
                stream = whole_stream(tls)
                if self.mode == "implicit":
                    stream.write(b"200 scratch TLS transit peer\r\n")
                while True:
                    line = stream.readline()
                    if not line:
                        return
                    text = line.decode("ascii").rstrip("\r\n")
                    with self.lock:
                        self.commands.append((number, text))
                    words = text.split()
                    if len(words) != 2 or words[0] != "IHAVE":
                        raise AssertionError("expected IHAVE without login/MODE, got " + text)
                    stream.write(b"335 send article\r\n")
                    article = self.read_article(stream)
                    if not article:
                        raise AssertionError("empty transfer")
                    stream.write(b"235 article transferred\r\n")
                    with self.lock:
                        self.articles[words[1]] = ("IHAVE", article)
        except (OSError, AssertionError, UnicodeError) as error:
            with self.lock:
                self.errors.append(str(error))
        finally:
            client.close()


@unittest.skipUnless(peer.READY, "set explicit native image/source and matching hashes")
class NativeFeedTlsReadyTests(unittest.TestCase):
    setUp = peer.NativePeeringTests.setUp
    initialize = peer.NativePeeringTests.initialize
    start = peer.NativePeeringTests.start
    process_identity = peer.NativePeeringTests.process_identity
    verify_process_identity = peer.NativePeeringTests.verify_process_identity
    article = staticmethod(peer.NativePeeringTests.article)
    post = peer.NativePeeringTests.post
    make_certificate = protected.NativeProtectedPeeringTests.make_certificate

    def transfer(self, mode):
        certificate, key = self.make_certificate(self.base, mode)
        scripted = NoLoginTlsPeer(certificate, key, mode)
        self.addCleanup(scripted.close)
        source = self.initialize("source-" + mode)
        source.operator("peer", "add", "scratch", "scratch.example.invalid",
                        "127.0.0.1", str(scripted.port), "fn.*", "fn.*",
                        "source-address", "127.0.0.1", "false", mode,
                        "localhost", certificate, expect=EXIT_OK)
        self.start(source)
        message_id = "<tls-ready-{}@example.invalid>".format(mode)
        self.post(source, message_id, "tls-ready-" + mode)
        got = scripted.await_article(message_id, timeout=30)
        with scripted.lock:
            commands, handshakes, errors = (list(scripted.commands),
                                           scripted.handshakes, list(scripted.errors))
        diagnostics = {"mode": mode, "handshakes": handshakes,
                       "commands": commands, "peer_errors": errors,
                       "owner_exit": source.process.poll(),
                       "owner_stderr": source.process.stderr.tail().decode("utf-8", "replace")}
        self.assertIsNotNone(got, json.dumps(diagnostics, sort_keys=True))
        self.assertEqual(got[0], "IHAVE")
        self.assertIn(("Message-ID: " + message_id + "\r\n").encode(), got[1])
        self.assertIn(("\r\ntls-ready-" + mode + "\r\n").encode(), got[1])
        self.assertEqual(handshakes, 1, diagnostics)
        expected = (["STARTTLS"] if mode == "starttls" else []) + ["IHAVE " + message_id]
        self.assertEqual(commands, [(1, command) for command in expected], diagnostics)
        self.assertEqual(errors, [], diagnostics)
        self.assertIsNone(source.process.poll(), diagnostics)
        print("NATIVE-FEED-TLS-READY-WITNESS " + json.dumps({
            "mode": mode, "streaming": False, "auth": None, "commands": commands,
            "identity": source.identities[-1], "source": peer.SOURCE}, sort_keys=True), flush=True)

    def test_starttls_installs_ready_feed_without_login_or_streaming(self):
        self.transfer("starttls")

    def test_implicit_tls_installs_feed_after_greeting(self):
        self.transfer("implicit")
