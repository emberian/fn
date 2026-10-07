import socket
import sys
import threading
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import msgid_measure as m  # noqa: E402


def serve_once(greeting):
    listener = socket.socket()
    listener.bind(("127.0.0.1", 0))
    listener.listen(1)

    def run():
        c, _ = listener.accept()
        c.sendall(greeting)
        c.close()
        listener.close()

    threading.Thread(target=run, daemon=True).start()
    return listener.getsockname()[1]


class ConnGreetingTests(unittest.TestCase):
    def test_a_refusal_greeting_raises_and_is_quoted(self):
        port = serve_once(b"400 too many connections; try again later\r\n")
        with self.assertRaises(ConnectionRefusedError) as cm:
            m.Conn(port)
        self.assertIn("too many connections", str(cm.exception))

    def test_a_200_greeting_connects(self):
        port = serve_once(b"200 ready\r\n")
        c = m.Conn(port)
        self.assertEqual(c.greeting, b"200 ready\r\n")
        c.sock.close()


if __name__ == "__main__":
    unittest.main()
