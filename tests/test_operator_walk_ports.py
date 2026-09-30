"""Real socket regression for operator-walk fixture port ownership, no image."""
import errno
from pathlib import Path
import socket
import tempfile
import unittest
from unittest import mock

from tests import test_native_operator_walk as walk


class OperatorWalkPortTests(unittest.TestCase):
    def test_pending_nodes_keep_distinct_ports_until_their_own_start(self):
        real_socket = socket.socket
        preferred = []

        class ChoosingSocket:
            """Deterministically reuse the first port whenever it is released."""
            def __init__(self):
                self.socket = real_socket()

            def bind(self, address):
                if preferred and address[1] == 0:
                    try:
                        self.socket.bind((address[0], preferred[0]))
                        return
                    except OSError as error:
                        if error.errno != errno.EADDRINUSE:
                            raise
                self.socket.bind(address)
                if not preferred:
                    preferred.append(self.socket.getsockname()[1])

            def getsockname(self):
                return self.socket.getsockname()

            def close(self):
                self.socket.close()

            def __enter__(self):
                return self

            def __exit__(self, *_):
                self.close()

        class FixtureNode:
            # Only mission/process plumbing is replaced. Port selection,
            # reservation, operator-walk callbacks and kernel binds are real.
            def __init__(self, case, image, *, root, name, port, **_):
                self.name, self.port = name, port
                self.config = root / "fn.toml"
                self.config.touch()
                self.listener = None
                case.addCleanup(self.stop)

            def operator(self, *_words, **_options):
                pass

            def invoke(self, *_words, **_options):
                pass

            def start(self):
                self.listener = real_socket()
                self.listener.bind(("127.0.0.1", self.port))

            def stop(self):
                if self.listener is not None:
                    self.listener.close()

        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        case = walk.OperatorWalkTests("test_the_installed_image_is_the_production_image")
        case.tmp, case.fn = Path(temporary.name), Path("unused-fixture-launcher")
        case.setUp()
        self.addCleanup(case.doCleanups)
        with mock.patch.object(walk, "Node", FixtureNode), \
                mock.patch.object(walk.socket, "socket", ChoosingSocket):
            a, b = case.node("a"), case.node("b")
        self.assertNotEqual(a.port, b.port)
        for port in (a.port, b.port):
            with real_socket() as probe, self.assertRaises(OSError) as caught:
                probe.bind(("127.0.0.1", port))
            self.assertEqual(caught.exception.errno, errno.EADDRINUSE)
        a.start()
        with real_socket() as probe, self.assertRaises(OSError) as caught:
            probe.bind(("127.0.0.1", b.port))
        self.assertEqual(caught.exception.errno, errno.EADDRINUSE)
        b.start()
        a.stop()
        b.stop()
        # Start/stop reuse stays possible after the one-time reservation.
        a.start()
        a.stop()


if __name__ == "__main__":
    unittest.main()
