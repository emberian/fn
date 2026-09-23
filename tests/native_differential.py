#!/usr/bin/env python3
"""Differential evidence: the native host against the Python host.

Runs one scripted command sequence through `tools/run_store.py` twice, once
per host (`FN_HOST=native` selects the explicit developer image for raw Store
diagnostics), and compares after every
step: the exit code, standard output, and every byte under the two store
directories.  Standard error is compared as text and reported, but only the
outcome class (exit code) is a hard criterion there, because Python's OSError
spelling is Python's.  Then it serves one store snapshot and the seeded archive
through both readers and compares the NNTP transcripts octet for octet.

A mismatch is a finding; this script reports it and exits 1.

    python3 tests/native_differential.py
"""
import os
from pathlib import Path
import select
import socket
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
HOSTS = ("python", "native")
LITERAL = b'Message-ID: <literal@example.invalid>\r\n\r\n#.(error "must not execute") \\ ()\r\n'


def env_for(host):
    env = dict(os.environ)
    env.pop("FN_HOST", None)
    if host == "native":
        env["FN_HOST"] = "native"
        env["FN_NATIVE_HOST"] = os.environ.get(
            "FN_NATIVE_DEVELOPER_HOST", str(ROOT / "build" / "fn-host-developer"))
    return env


def run_store(host, store, command, *args):
    return subprocess.run([sys.executable, "tools/run_store.py", "--store", str(store),
                           command, *map(str, args)], cwd=ROOT, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, env=env_for(host), check=False)


def tree(store):
    """Every regular file under STORE as {relative name: bytes}, with staging
    names normalized: they carry a pid and random octets by construction."""
    snapshot = {}
    for path in sorted(Path(store).rglob("*")):
        relative = path.relative_to(store)
        if path.is_symlink() or not path.is_file():
            continue
        key = str(relative)
        if relative.parts[0] == "staging":
            prefix = relative.name.split("-")[0]
            key = "staging/{}#{}".format(prefix, sum(1 for k in snapshot if k.startswith("staging/" + prefix)))
        snapshot[key] = (path.read_bytes(), oct(path.stat().st_mode & 0o777))
    return snapshot


class Differential:
    def __init__(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-native-diff-")
        self.base = Path(self.temp.name)
        self.stores = {host: self.base / host / "store" for host in HOSTS}
        for host in HOSTS:
            (self.base / host).mkdir()
        self.findings = []
        self.steps = 0
        self.stderr_diffs = 0

    def payload(self, name, data):
        path = self.base / name
        path.write_bytes(data)
        return path

    def step(self, label, command, *args, compare_disk=True, store=None):
        self.steps += 1
        results = {}
        for host in HOSTS:
            target = self.stores[host] if store is None else store(host)
            results[host] = run_store(host, target, command, *args)
        py, na = results["python"], results["native"]
        if py.returncode != na.returncode:
            self.findings.append("{}: exit python={} native={}\n  python stderr: {}\n  native stderr: {}".format(
                label, py.returncode, na.returncode, py.stderr.decode("utf-8", "replace").strip(),
                na.stderr.decode("utf-8", "replace").strip()))
        if py.stdout.replace(str(self.stores["python"]).encode(), b"STORE") != \
                na.stdout.replace(str(self.stores["native"]).encode(), b"STORE"):
            self.findings.append("{}: stdout python={!r} native={!r}".format(label, py.stdout, na.stdout))
        if py.stderr != na.stderr:
            self.stderr_diffs += 1
            print("  stderr differs at {}:\n    python: {}\n    native: {}".format(
                label, py.stderr.decode("utf-8", "replace").strip(),
                na.stderr.decode("utf-8", "replace").strip()))
        if compare_disk:
            left, right = tree(self.stores["python"]), tree(self.stores["native"])
            if left != right:
                detail = []
                for key in sorted(set(left) | set(right)):
                    if left.get(key) != right.get(key):
                        detail.append("    {}: python={} native={}".format(
                            key, (left.get(key) or (b"", ""))[1] + " " + repr((left.get(key) or (b"",))[0][:60]),
                            (right.get(key) or (b"", ""))[1] + " " + repr((right.get(key) or (b"",))[0][:60])))
                self.findings.append("{}: disk differs\n{}".format(label, "\n".join(detail)))
        print("step {:2d} {:<48} python={} native={}".format(self.steps, label, py.returncode, na.returncode))
        return results

    def run_store_sequence(self):
        first = self.payload("first", b"first")
        second = self.payload("second", b"second")
        literal = self.payload("literal", LITERAL)
        empty = self.payload("empty", b"")
        big = self.payload("big", b"x" * 32768)
        oversize = self.payload("oversize", b"x" * 32769)
        self.step("init", "init")
        self.step("init again", "init")
        self.step("status empty", "status")
        self.step("post first", "post", "--message-id", "<a@example.invalid>", "--payload", first,
                  "--group", "fn.letters")
        self.step("post duplicate", "post", "--message-id", "<a@example.invalid>", "--payload", first,
                  "--group", "fn.letters")
        self.step("post conflict", "post", "--message-id", "<a@example.invalid>", "--payload", second,
                  "--group", "fn.letters")
        self.step("post literal two groups", "post", "--message-id", "<literal@example.invalid>",
                  "--payload", literal, "--group", "fn.letters", "--group", "fn.test")
        self.step("post empty payload", "post", "--message-id", "<empty@example.invalid>",
                  "--payload", empty, "--group", "fn.test")
        self.step("post maximum payload", "post", "--message-id", "<big@example.invalid>",
                  "--payload", big, "--group", "fn.letters", "--charge", "7")
        self.step("post oversize payload", "post", "--message-id", "<over@example.invalid>",
                  "--payload", oversize, "--group", "fn.letters")
        self.step("post bad message-id", "post", "--message-id", "no-brackets", "--payload", first,
                  "--group", "fn.letters")
        self.step("post unknown group", "post", "--message-id", "<g@example.invalid>", "--payload", first,
                  "--group", "fn.nowhere")
        self.step("post duplicate group", "post", "--message-id", "<g@example.invalid>", "--payload", first,
                  "--group", "fn.letters", "--group", "fn.letters")
        self.step("post zero charge", "post", "--message-id", "<c@example.invalid>", "--payload", first,
                  "--group", "fn.letters", "--charge", "0")
        self.step("post missing payload", "post", "--message-id", "<m@example.invalid>",
                  "--payload", self.base / "absent", "--group", "fn.letters")
        self.step("post prepublish fault", "post", "--message-id", "<abort@example.invalid>",
                  "--payload", first, "--group", "fn.letters", "--inject-fault", "prepublish")
        self.step("post after abort", "post", "--message-id", "<after@example.invalid>",
                  "--payload", second, "--group", "fn.letters")
        self.step("post postpublish fault", "post", "--message-id", "<uncertain@example.invalid>",
                  "--payload", first, "--group", "fn.test", "--inject-fault", "postpublish")
        self.step("recover", "recover")
        self.step("status", "status")
        self.step("inspect literal", "inspect", "--message-id", "<literal@example.invalid>")
        self.step("inspect absent", "inspect", "--message-id", "<nobody@example.invalid>")
        self.step("inspect bad id", "inspect", "--message-id", "nobody")
        self.step("recover absent store", "recover", compare_disk=False,
                  store=lambda host: self.base / host / "absent")
        # Damage copies of the final store identically and reopen each.
        for name, damage in (
                ("truncated", lambda root: self.rewrite(root / "transactions" / "00000000000000000000.txn",
                                                        lambda raw: raw[:-1])),
                ("flipped trailer", lambda root: self.rewrite(root / "transactions" / "00000000000000000000.txn",
                                                              lambda raw: raw[:-1] + bytes([raw[-1] ^ 1]))),
                ("gap", lambda root: os.rename(root / "transactions" / "00000000000000000001.txn",
                                               root / "transactions" / "00000000000000000009.txn")),
                ("config truncated", lambda root: self.rewrite(root / "config.json",
                                                               lambda raw: raw[:-1])),
                ("config wrong kind", lambda root: self.rewrite(
                    root / "config.json", lambda raw: raw[:5] + bytes([2]) + raw[6:])),
                ("frontier truncated", lambda root: self.rewrite(
                    root / "allocation-frontier.json", lambda raw: raw[:-1])),
                ("frontier wrong kind", lambda root: self.rewrite(
                    root / "allocation-frontier.json",
                    lambda raw: raw[:5] + bytes([1]) + raw[6:])),
                ("frontier legacy JSON", lambda root: (root / "allocation-frontier.json").write_bytes(
                    b'{"format":"fn-store-allocation-frontier-1","next_txid":5}\n')),
                ("stray file", lambda root: (root / "transactions" / "stray").write_bytes(b"")),
                ("symlinked transaction", lambda root: (
                    (root / "transactions" / "00000000000000000000.txn").unlink(),
                    os.symlink(root / "config.json", root / "transactions" / "00000000000000000000.txn"))),
                ("missing staging", lambda root: os.rmdir(root / "staging") if not any(
                    (root / "staging").iterdir()) else None),
                ("lock symlink", lambda root: ((root / "writer.lock").unlink(),
                                               os.symlink(root / "config.json", root / "writer.lock"))),
        ):
            copies = {}
            for host in HOSTS:
                copy = self.base / host / ("damaged-" + name.replace(" ", "-"))
                subprocess.run(["cp", "-R", str(self.stores[host]), str(copy)], check=True)
                damage(copy)
                copies[host] = copy
            self.step("damaged: " + name, "status", compare_disk=False, store=lambda host: copies[host])

    @staticmethod
    def rewrite(path, transform):
        path.write_bytes(transform(path.read_bytes()))

    # -- reader -------------------------------------------------------------

    def reader_transcript(self, host, store, script):
        command = [sys.executable, "tools/run_reader.py", "--port", "0", "--once"]
        if store is not None:
            command.extend(["--store", str(store)])
        proc = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                env=env_for(host))
        try:
            deadline = time.monotonic() + 60
            port = None
            while time.monotonic() < deadline and port is None:
                ready, _, _ = select.select([proc.stdout], [], [], 0.2)
                if ready:
                    line = proc.stdout.readline()
                    if line.startswith(b"LISTENING "):
                        port = int(line.split()[1])
                if proc.poll() is not None:
                    break
            if port is None:
                return (None, proc.stderr.read())
            with socket.create_connection(("127.0.0.1", port), timeout=10) as sock:
                for chunk in script:
                    sock.sendall(chunk)
                    time.sleep(0.05)
                received = b""
                sock.settimeout(10)
                try:
                    while True:
                        piece = sock.recv(4096)
                        if not piece:
                            break
                        received += piece
                except (socket.timeout, ConnectionError):
                    pass
            proc.wait(timeout=20)
            return (received, proc.returncode)
        finally:
            if proc.poll() is None:
                proc.terminate()
                try:
                    proc.wait(timeout=8)
                except subprocess.TimeoutExpired:
                    proc.kill()
            proc.stdout.close()
            proc.stderr.close()

    def run_reader_sequence(self):
        scripts = {
            "store: group stat article quit": (
                b"GROUP fn.letters\r\nSTAT\r\nARTICLE <literal@example.invalid>\r\nHEAD 1\r\n"
                b"LIST\r\nQUIT\r\n",),
            "store: split command": (b"GRO", b"UP fn.test\r\nNEXT\r\nQUIT\r\n"),
            "store: over-long line": (b"X" * 600 + b"\r\n",),
            "seed: list and quit": (b"LIST ACTIVE fn.*\r\nGROUP fn.letters\r\nARTICLE 1\r\nQUIT\r\n",),
        }
        for label, script in scripts.items():
            self.steps += 1
            results = {}
            for host in HOSTS:
                store = None if label.startswith("seed") else self.stores[host]
                results[host] = self.reader_transcript(host, store, script)
            py, na = results["python"], results["native"]
            status = "match" if py == na else "MISMATCH"
            if py != na:
                self.findings.append("reader {}: python={!r} native={!r}".format(label, py, na))
            print("step {:2d} reader {:<41} {} (exit python={} native={})".format(
                self.steps, label, status, py[1], na[1]))

    def report(self):
        print()
        print("steps={} findings={} stderr-text-differences={}".format(
            self.steps, len(self.findings), self.stderr_diffs))
        for finding in self.findings:
            print("FINDING " + finding)
        return 1 if self.findings else 0


def main():
    differential = Differential()
    try:
        differential.run_store_sequence()
        differential.run_reader_sequence()
        return differential.report()
    finally:
        differential.temp.cleanup()


if __name__ == "__main__":
    sys.exit(main())
