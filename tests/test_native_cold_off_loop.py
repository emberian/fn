"""r71 F7: a cold page is read off the I/O loop (lane served-live,
2026-10-03; ledger r71-F7, acceptance mux:no-cold-await).

A served line that needs a payload not in memory used to wait for the page
on the I/O loop thread that read it (fnn-owner-cold-await): every other
connection that loop served got no reads, writes or timers for up to the
dependency deadline (5 s).  Now the loop keeps the issued read on the
connection and returns to its poll (host/native/mux.lisp fnn-mux-cold-check).

The case restarts a node over stored articles with the pread stalled
(FN_NATIVE_TEST_READ_STALL_FILE), asks for one article (a cold read that
does not return), and while it is outstanding opens OTHERS connections, which
the accept spreads over every loop, the cold one's included: each one's
greeting and DATE must come within OTHER_SECONDS.  Released, the cold
article is answered (220) or named unavailable (403), never lost.
"""
import threading
import time
import unittest

from tests.native_harness import Client, Node, article, executable, native_image

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
OTHERS = 8
OTHER_SECONDS = 1.5


@unittest.skipUnless(executable(DEVELOPER), "an executable FN_NATIVE_DEVELOPER_HOST is required")
class NativeColdOffLoopTests(unittest.TestCase):
    def test_other_connections_are_served_while_a_page_is_owed(self):
        node = Node(self, DEVELOPER, name="cold-off-loop")
        node.init()
        owner = node.start()
        message_id = b"<cold-off-loop@example.invalid>"
        with Client(node.port, timeout=60) as poster:
            _, final = poster.post(article(message_id, body=b"owed\r\n"))
            self.assertTrue(final.startswith(b"240"), final)
        node.stop(process=owner)
        stall = node.root / "readstall"
        self.addCleanup(lambda: stall.unlink() if stall.exists() else None)
        owner = node.start(env={"FN_NATIVE_TEST_READ_STALL_FILE": str(stall)})
        with node.log_on_failure(owner):
            stall.write_bytes(b"")
            cold = Client(node.port, timeout=60)
            self.addCleanup(cold.close, False)
            answer = {}

            def ask():
                try:
                    answer["status"] = cold.command(b"ARTICLE " + message_id)
                except Exception as error:
                    answer["error"] = error

            asker = threading.Thread(target=ask)
            asker.start()
            time.sleep(0.5)
            waits = []
            for _ in range(OTHERS):
                started = time.monotonic()
                with Client(node.port, timeout=30) as other:
                    self.assertTrue(other.command("DATE").startswith(b"111"))
                waits.append(round(time.monotonic() - started, 3))
            print("COLD-OFF-LOOP waits={} asker-alive={}".format(waits, asker.is_alive()), flush=True)
            self.assertTrue(asker.is_alive() or "status" in answer, answer)
            self.assertTrue(all(w < OTHER_SECONDS for w in waits), waits)
            stall.unlink()
            asker.join(timeout=60)
            self.assertFalse(asker.is_alive())
            self.assertIn(answer.get("status", b"")[:3], (b"220", b"403"), answer)
            node.stop(process=owner)


if __name__ == "__main__":
    unittest.main()
