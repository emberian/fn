"""Process/NNTP fixture boundary checks, not native image evidence."""

import tempfile
from pathlib import Path
import unittest

from tests.bp_producer import post_articles


class BpProducerLifecycleTests(unittest.TestCase):
    def test_injected_core_record_and_stopped_owner_before_inspection(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            image = root / "fake-fn"
            image.write_text('''#!/usr/bin/env python3
import signal, socket, sys, tomllib
from pathlib import Path
args = sys.argv[2:]
if args[0] == "store":
    store = Path(args[1])
    if (store.parent / "owner-active").exists():
        sys.exit(99)
    sys.stdout.buffer.write(b"Path: core!not-for-mail\\r\\n\\r\\nstored source\\r\\n")
    sys.exit(0)
config = tomllib.loads(Path(args[1]).read_text())
if args[2] != "run":
    sys.exit(0)
marker = Path(config["store"]["path"]).parent / "owner-active"
marker.touch()
def stop(*unused):
    marker.unlink()
    sys.exit(0)
signal.signal(signal.SIGTERM, stop)
server = socket.socket()
server.bind(("127.0.0.1", config["listener"]["port"]))
server.listen()
print("LISTENING " + str(config["listener"]["port"]), flush=True)
while True:
    connection, _ = server.accept()
    with connection:
        connection.sendall(b"200 fake\\r\\n")
        stream = connection.makefile("rb")
        for line in stream:
            if line.startswith(b"ARTICLE "):
                connection.sendall(b"220 article\\r\\nXref: serving fn.test:1\\r\\nPath: core!not-for-mail\\r\\n\\r\\nstored source\\r\\n.\\r\\n")
            elif line.startswith(b"QUIT"):
                break
''')
            image.chmod(0o755)
            stored = post_articles(self, image, root / "store", [("<id>", b"input differs")])
            self.assertEqual(stored["<id>"], b"Path: core!not-for-mail\r\n\r\nstored source\r\n")
            self.assertFalse((root / "owner-active").exists())
            self.assertTrue((root / "store-producer" / "article-0.nntp").read_bytes()
                            .startswith(b"Xref: serving "))
