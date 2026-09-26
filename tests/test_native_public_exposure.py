"""SCN-091: a reader port facing strangers answers them within ACL2's limits.

The native gate of PRF-161 (books/public-exposure.lisp).  One owner on
127.0.0.1 with the exposure rows set through `fn operator CONFIG policy set'
(some before the start, some live); strangers are other loopback source
addresses (127.0.0.0/8 routes to lo on Linux, so no alias is configured).  A
legitimate authenticated client on 127.0.0.1 samples DATE every 100 ms for
the whole campaign; its latency per phase is the table the record quotes.

Phases: a flood of 500 connections from one address; 500 from 50 addresses
with the per-address limit lowered live to 1; a slowloris (silent and
trickling); oversized command lines; the anonymous policy (none, then open
live) and an anonymous ARTICLE loop against the step budget; credential
guessing at about 100 attempts a second.  Every outcome is classified by the
first line the stranger read; the owner must stay up and the legitimate
client must be answered throughout.  `health' must report the pressure.

Run on hbox: tools/hbox_native.sh . tests.test_native_public_exposure
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import socket
import statistics
import subprocess
import sys
import tempfile
import threading
import time
import unittest

from tests.native_process import wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST") or os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
READY = IMAGE.is_file() and os.access(IMAGE, os.X_OK)
LOGIN, PASSWORD = "legit", "correct-horse-battery"


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def first_line(sock, timeout):
    """The first line the server sends, b'' on a clean close, or a tag."""
    sock.settimeout(timeout)
    data = b""
    try:
        while not data.endswith(b"\n"):
            chunk = sock.recv(1)
            if not chunk:
                return data or b""
            data += chunk
    except socket.timeout:
        return b"<timeout>"
    except (ConnectionResetError, BrokenPipeError):
        return b"<reset>"
    return data


def classify(line):
    if line.startswith(b"200 ") or line.startswith(b"201 "):
        return "admitted"
    if line.startswith(b"400 too many connections from this address"):
        return "400-address"
    if line.startswith(b"400 too many connections"):
        return "400-busy"
    if line.startswith(b"400 too many authentication failures"):
        return "400-auth"
    if line == b"":
        return "closed"
    return line.decode("ascii", "replace").strip()[:40]


class Legit(threading.Thread):
    """An authenticated reader sampling DATE every 100 ms, per phase."""

    def __init__(self, port):
        super().__init__(daemon=True)
        self.port = port
        self.phase = "setup"
        self.samples = {}
        self.failures = []
        self.stop = threading.Event()
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=30)
        self.stream = self.sock.makefile("rwb", buffering=0)
        greeting = self.stream.readline()
        assert greeting[:3] in (b"200", b"201"), greeting
        for line, code in ((b"AUTHINFO USER " + LOGIN.encode() + b"\r\n", b"381"),
                           (b"AUTHINFO PASS " + PASSWORD.encode() + b"\r\n", b"281"),
                           (b"GROUP fn.test\r\n", b"211")):
            self.stream.write(line)
            reply = self.stream.readline()
            assert reply.startswith(code), (line, reply)

    def run(self):
        while not self.stop.is_set():
            started = time.monotonic()
            try:
                self.stream.write(b"DATE\r\n")
                reply = self.stream.readline()
            except OSError as error:
                self.failures.append((self.phase, repr(error)))
                return
            elapsed = time.monotonic() - started
            if not reply.startswith(b"111 "):
                self.failures.append((self.phase, reply))
            self.samples.setdefault(self.phase, []).append(elapsed)
            time.sleep(0.1)

    def table(self):
        rows = {}
        for phase, xs in self.samples.items():
            ordered = sorted(xs)
            rows[phase] = {
                "n": len(xs),
                "p50_ms": round(statistics.median(ordered) * 1000, 1),
                "p95_ms": round(ordered[max(0, int(len(ordered) * 0.95) - 1)] * 1000, 1),
                "max_ms": round(ordered[-1] * 1000, 1),
            }
        return rows


@unittest.skipUnless(READY, "no native image (FN_NATIVE_HOST or build/fn-host-developer)")
class NativePublicExposureTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-exposure-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.process = None
        self.addCleanup(self.stop)
        self.evidence = Path(os.environ.get(
            "FN_EXPOSURE_EVIDENCE", ROOT / "build" / "public-exposure-evidence"))
        self.evidence.mkdir(parents=True, exist_ok=True)

    def command(self, arguments, expected=0, stdin=None):
        result = subprocess.run(list(map(str, arguments)), cwd=ROOT, env=self.env,
                                input=stdin, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=180, check=False)
        if expected is not None:
            self.assertEqual(result.returncode, expected, result)
        return result

    def policy(self, slot, value):
        self.command([IMAGE, "--fn", "operator", self.config, "policy", "set",
                      slot, value])

    def stop(self):
        if self.process is not None and self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.communicate(timeout=60)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.communicate(timeout=60)
        for name in ("fn.log", "stderr.log"):
            source = self.base / name
            if source.exists():
                (self.evidence / name).write_bytes(source.read_bytes())

    def dump_report(self):
        print("EXPOSURE-REPORT " + json.dumps(self.report, sort_keys=True),
              file=sys.stderr)
        (self.evidence / "exposure-report.json").write_text(
            json.dumps(self.report, indent=1, sort_keys=True), encoding="ascii")

    def connect(self, source, timeout=10):
        return socket.create_connection(("127.0.0.1", self.port), timeout=timeout,
                                        source_address=(source, 0))

    def flood(self, sources, per_source):
        """Open per_source connections from each source at once; hold every
        admitted one; return (classified counts, held sockets)."""
        results, held, lock = [], [], threading.Lock()

        def one(source):
            try:
                sock = self.connect(source)
            except OSError as error:
                with lock:
                    results.append("connect-" + type(error).__name__)
                return
            line = first_line(sock, 30)
            kind = classify(line)
            with lock:
                results.append(kind)
                if kind == "admitted":
                    held.append(sock)
                else:
                    sock.close()

        threads = [threading.Thread(target=one, args=(source,))
                   for source in sources for _ in range(per_source)]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join(60)
        counts = {}
        for kind in results:
            counts[kind] = counts.get(kind, 0) + 1
        return counts, held

    def assert_alive(self):
        self.assertIsNone(self.process.poll(), "the owner exited")

    def test_flood_campaign(self):
        store = self.base / "store"
        self.port = free_port()
        self.command([IMAGE, "--fn", "store", store, "init", "fn.test"])
        self.config = self.base / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n[log]\npath = "{}"\n'
            '[auth]\nrequired = false\nprotected_only = false\npath = "{}"\n'.format(
                store, self.port, self.base / "control.sock", self.base / "fn.log",
                self.base / "auth.toml"), encoding="ascii")
        self.command([IMAGE, "--fn", "operator", self.config, "principal",
                      "set-password", LOGIN],
                     stdin=(PASSWORD + "\n" + PASSWORD + "\n").encode())
        # Rows before the start: the test's timers are short so the campaign
        # runs in minutes; the public defaults are the record's table.
        for slot, value in (("exposure-connections", "32"),
                            ("exposure-per-address", "8"),
                            ("exposure-steps-per-second", "20"),
                            ("exposure-idle-seconds", "8"),
                            ("exposure-first-seconds", "5"),
                            ("exposure-auth-failures", "10"),
                            ("anonymous", "none")):
            self.policy(slot, value)
        err = open(self.base / "stderr.log", "ab")
        self.process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=err)
        wait_for_announcement(self.process, b"LISTENING ")
        report = self.report = {"port": self.port}
        self.addCleanup(self.dump_report)

        legit = Legit(self.port)
        legit.start()
        self.addCleanup(legit.stop.set)
        legit.phase = "baseline"
        time.sleep(3)

        # --- one address, 500 connections
        legit.phase = "flood-one-address"
        counts, held = self.flood(["127.0.0.2"], 500)
        report["flood_one_address"] = counts
        self.assertLessEqual(counts.get("admitted", 0), 8, counts)
        self.assertGreater(counts.get("400-address", 0), 0, counts)
        self.assert_alive()
        # The admitted ones never send a command: the first-command timer
        # (5 s) closes them with no reply (RFC 3977 3.1).
        started = time.monotonic()
        closes = [first_line(sock, 15) for sock in held]
        report["flood_one_address_idle_close"] = {
            "held": len(held), "seconds": round(time.monotonic() - started, 1),
            "lines": sorted(set(line.decode("ascii", "replace") for line in closes))}
        self.assertTrue(all(line == b"" for line in closes), closes)
        for sock in held:
            sock.close()

        # --- 50 addresses, 10 each, per-address lowered LIVE to 1; the
        # first-command timer raised live to 30 s so the admitted ones are
        # still held when a fresh legit connection is tried.
        self.policy("exposure-per-address", "1")
        self.policy("exposure-first-seconds", "30")
        legit.phase = "flood-50-addresses"
        sources = ["127.0.1.{}".format(n) for n in range(1, 51)]
        counts, held = self.flood(sources, 10)
        report["flood_50_addresses"] = counts
        # 32 is the run's bound; one is the operator's, one the legit reader's.
        self.assertLessEqual(counts.get("admitted", 0), 30, counts)
        self.assertGreater(counts.get("400-address", 0), 0, counts)
        self.assert_alive()
        # 127.0.0.1 already holds the legit session, so per-address goes back
        # up (live) before a fresh legit connection is tried.  While the total
        # is exhausted it gets 400 busy (or is admitted if a slot is free);
        # the held legit session keeps working either way.
        self.policy("exposure-per-address", "8")
        with self.connect("127.0.0.1") as fresh:
            report["fresh_legit_during_total_flood"] = classify(first_line(fresh, 10))
        started = time.monotonic()
        for sock in held:
            first_line(sock, 45)
            sock.close()
        report["flood_50_addresses_idle_close_s"] = round(time.monotonic() - started, 1)
        with self.connect("127.0.0.1") as fresh:
            report["fresh_legit_after_idle_close"] = classify(first_line(fresh, 10))
        self.policy("exposure-first-seconds", "5")
        self.assertEqual(report["fresh_legit_after_idle_close"], "admitted")

        # --- slowloris: silent and trickling
        legit.phase = "slowloris"
        silent = [self.connect("127.0.0.4") for _ in range(4)]
        trickle = [self.connect("127.0.0.4") for _ in range(4)]
        for sock in silent + trickle:
            self.assertEqual(classify(first_line(sock, 10)), "admitted")
        started = time.monotonic()
        ended = {}

        def trickler(index, sock):
            for octet in b"DATE-SLOWLY-FOREVER":
                try:
                    sock.send(bytes([octet]))
                except OSError:
                    break
                time.sleep(1)
                sock.settimeout(0.01)
                try:
                    if sock.recv(1) == b"":
                        break
                except socket.timeout:
                    continue
                except OSError:
                    break
            ended[index] = round(time.monotonic() - started, 1)

        threads = [threading.Thread(target=trickler, args=(i, s))
                   for i, s in enumerate(trickle)]
        for thread in threads:
            thread.start()
        silent_lines = [first_line(sock, 20) for sock in silent]
        silent_seconds = round(time.monotonic() - started, 1)
        for thread in threads:
            thread.join(30)
        report["slowloris"] = {"silent_lines": [x.decode() for x in silent_lines],
                               "silent_closed_after_s": silent_seconds,
                               "trickle_closed_after_s": ended}
        self.assertTrue(all(line == b"" for line in silent_lines), silent_lines)
        self.assertLess(silent_seconds, 12)
        self.assertTrue(all(v < 16 for v in ended.values()), ended)
        for sock in silent + trickle:
            sock.close()
        self.assert_alive()

        # --- oversized command lines
        legit.phase = "oversized"
        oversized = {}
        for size in (600, 4096, 65536):
            with self.connect("127.0.0.5") as sock:
                self.assertEqual(classify(first_line(sock, 10)), "admitted")
                try:
                    sock.sendall(b"A" * size + b"\r\n")
                except OSError as error:
                    oversized[size] = "send-" + type(error).__name__
                    continue
                oversized[size] = first_line(sock, 10).decode("ascii", "replace").strip()
        report["oversized"] = oversized
        self.assert_alive()

        # --- the anonymous policy: none, then open (live)
        legit.phase = "anonymous"
        with self.connect("127.0.0.6") as sock:
            stream = sock.makefile("rwb", buffering=0)
            greeting = stream.readline()
            anonymous = {"greeting_none": greeting.decode().strip()}
            for command in (b"GROUP fn.test", b"ARTICLE 1", b"POST", b"LIST",
                            b"CAPABILITIES"):
                stream.write(command + b"\r\n")
                reply = stream.readline()
                if reply.startswith(b"101"):
                    while stream.readline() not in (b".\r\n", b""):
                        pass
                anonymous[command.decode()] = reply.decode().strip()
        self.assertTrue(anonymous["GROUP fn.test"].startswith("480"), anonymous)
        self.assertTrue(anonymous["POST"].startswith("480"), anonymous)
        self.assertTrue(anonymous["ARTICLE 1"].startswith("480"), anonymous)
        self.policy("anonymous", "open")
        with self.connect("127.0.0.6") as sock:
            stream = sock.makefile("rwb", buffering=0)
            stream.readline()
            stream.write(b"GROUP fn.test\r\n")
            anonymous["GROUP fn.test (open)"] = stream.readline().decode().strip()
            # The ARTICLE loop against the step budget (20 a second).
            started = time.monotonic()
            answered = 0
            for _ in range(120):
                stream.write(b"STAT 1\r\n")
                if stream.readline() == b"":
                    break
                answered += 1
            seconds = time.monotonic() - started
            anonymous["stat_loop"] = {"answered": answered,
                                      "seconds": round(seconds, 2),
                                      "per_second": round(answered / seconds, 1)}
        report["anonymous"] = anonymous
        self.assertTrue(anonymous["GROUP fn.test (open)"].startswith("211"), anonymous)
        self.assertEqual(anonymous["stat_loop"]["answered"], 120)
        self.assertLessEqual(anonymous["stat_loop"]["per_second"], 25.0, anonymous)
        self.policy("anonymous", "none")

        # --- credential guessing at about 100 a second
        legit.phase = "credential-guessing"
        guessing = {"481": 0, "attempts": 0}
        with self.connect("127.0.0.7") as sock:
            stream = sock.makefile("rwb", buffering=0)
            stream.readline()
            last = b""
            for n in range(200):
                try:
                    stream.write(b"AUTHINFO USER legit\r\n")
                    last = stream.readline()
                    if not last.startswith(b"381"):
                        break
                    stream.write("AUTHINFO PASS wrong{}\r\n".format(n).encode())
                except OSError:
                    break
                guessing["attempts"] += 1
                last = stream.readline()
                if last.startswith(b"481"):
                    guessing["481"] += 1
                    time.sleep(0.01)
                    continue
                break
            guessing["last"] = last.decode().strip()
            guessing["after_last"] = first_line(sock, 5).decode("ascii", "replace")
        with self.connect("127.0.0.7") as sock:
            guessing["next_connection"] = first_line(sock, 10).decode().strip()
        report["credential_guessing"] = guessing
        self.assertLessEqual(guessing["481"], 10, guessing)
        self.assertTrue(guessing["last"].startswith(
            "400 too many authentication failures"), guessing)
        self.assertTrue(guessing["next_connection"].startswith(
            "400 too many authentication failures from this address"), guessing)
        self.assert_alive()

        # --- health reports the pressure
        health = self.command([IMAGE, "--fn", "operator", self.config, "health"],
                              expected=None)
        text = health.stdout.decode("ascii", "replace")
        report["health"] = {"exit": health.returncode,
                            "exposure_lines": [line for line in text.splitlines()
                                               if line.startswith("exposure")]}
        self.assertIn("exposure pressure held", text)
        self.assertIn("refused-address=", text)

        legit.phase = "after"
        time.sleep(2)
        legit.stop.set()
        legit.join(10)
        report["legit_latency"] = legit.table()
        report["legit_failures"] = [(p, repr(x)) for p, x in legit.failures]
        self.assertEqual(legit.failures, [])
        for phase, row in report["legit_latency"].items():
            self.assertLess(row["max_ms"], 5000, (phase, row))
        self.assert_alive()


if __name__ == "__main__":
    unittest.main()
