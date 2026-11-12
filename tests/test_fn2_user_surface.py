#!/usr/bin/env python3
"""End-to-end black-box verification of the `./fn` user & operator CLI surface.

Exercises real TCP NNTP + `0600` FNCT Unix sockets across:
  1. `fn init` with custom `--size-mb` and `--group`s (+ existing-image refusal control)
  2. `fn serve` with `--control-sock` (+ mismatched-group genesis refusal control)
  3. `fn principal create`, `fn grant set`, `fn grant get` (+ unauthorized/duplicate controls)
  4. `fn stream register`, parked `fn stream wait` woken by `fn post`, `fn stream append`,
     `fn stream read`, `fn stream ack`, `fn stream status` (+ behind/beyond-frontier controls)
  5. `fn groups` and `fn article` (by group+number and by Message-ID, with dot-transparency)
  6. `SIGKILL` crash + restart on the same `--control-sock` preserving grants, cursors, and articles
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import selectors
import signal
import stat
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
FN = str(ROOT / "fn")


class LiveNode:
    def __init__(self, directory: Path, image: Path, label: str, extra_args: list[str]):
        self.log_path = directory / f"{label}.log"
        self.log = self.log_path.open("wb")
        self.pidfile = directory / f"{label}.node.pid"
        self.node_pid: int | None = None
        self.pending = b""
        cmd = ["timeout", "600", FN, "serve", str(image), *extra_args]
        self.proc = subprocess.Popen(
            cmd,
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        (directory / f"{label}.launcher.pid").write_text(f"{self.proc.pid}\n", encoding="ascii")
        self.selector = selectors.DefaultSelector()
        assert self.proc.stdout is not None
        self.selector.register(self.proc.stdout, selectors.EVENT_READ)

    def wait_marker(self, prefix: bytes, seconds: float = 480.0) -> bytes:
        deadline = time.monotonic() + seconds
        assert self.proc.stdout is not None
        while time.monotonic() < deadline:
            while b"\n" in self.pending:
                line, self.pending = self.pending.split(b"\n", 1)
                if line.startswith(b"NODE-PID "):
                    self.node_pid = int(line.split()[1])
                    self.pidfile.write_text(f"{self.node_pid}\n", encoding="ascii")
                if line.startswith(prefix):
                    return line
                if line.startswith(b"REFUSED "):
                    raise AssertionError(f"unexpected node refusal: {line.decode(errors='replace')}")
            events = self.selector.select(min(1.0, max(0.0, deadline - time.monotonic())))
            if events:
                chunk = os.read(self.proc.stdout.fileno(), 65536)
                if not chunk:
                    break
                self.log.write(chunk)
                self.log.flush()
                self.pending += chunk
        raise AssertionError(f"missing marker {prefix!r}; see {self.log_path}")

    def sigkill(self) -> None:
        assert self.node_pid and int(self.pidfile.read_text(encoding="ascii")) == self.node_pid
        os.kill(self.node_pid, signal.SIGKILL)
        rc = self.proc.wait(timeout=30)
        assert rc != 0, f"expected non-zero exit on SIGKILL, got {rc}"

    def close(self) -> None:
        if self.proc.poll() is None:
            if self.node_pid:
                try:
                    os.kill(self.node_pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            else:
                try:
                    os.killpg(self.proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            self.proc.wait(timeout=30)
        assert self.proc.stdout is not None
        self.log.write(self.proc.stdout.read())
        self.log.flush()
        self.selector.close()
        self.proc.stdout.close()
        self.log.close()


def run_fn(*args: str, expect_rc: int = 0, as_json: bool = False):
    cmd = [FN, *args]
    if as_json and "--json" not in args:
        cmd.append("--json")
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=60)
    if proc.returncode != expect_rc:
        raise AssertionError(
            f"cmd={cmd!r} rc={proc.returncode} expected={expect_rc}\n"
            f"stdout={proc.stdout}\nstderr={proc.stderr}"
        )
    if as_json:
        return json.loads(proc.stdout)
    return proc.stdout


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path)
    args = parser.parse_args()

    directory = (args.directory or ROOT / "build" / f"user-surface-{time.time_ns()}").resolve()
    directory.mkdir(parents=True, exist_ok=False)
    image = directory / "node.img"
    cursor_file = directory / "watcher.cursor"
    ctl_sock = Path(f"/tmp/fn2-us-{os.getpid()}-{time.time_ns()}.sock")

    try:
        # 1. Initialize custom image (8 MiB, two custom groups) & verify non-truncation refusal.
        init_out = run_fn(
            "init", str(image),
            "--size-mb", "8",
            "--group", "ops.alerts",
            "--group", "ops.audit",
            expect_rc=0,
        )
        assert "INITIALIZED" in init_out, init_out
        assert image.stat().st_size == 8 * 1024 * 1024

        refused_init = run_fn("init", str(image), "--size-mb", "4", expect_rc=2)
        assert "REFUSED image-exists" in refused_init, refused_init
        assert image.stat().st_size == 8 * 1024 * 1024

        # Control: serving with mismatched genesis group list is refused by ACL2 boot verification.
        bad_serve = subprocess.run(
            ["timeout", "120", FN, "serve", str(image), "--group", "wrong.group"],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        assert bad_serve.returncode == 2, (bad_serve.returncode, bad_serve.stdout)
        assert "REFUSED " in bad_serve.stdout, bad_serve.stdout

        # 2. Boot node serving TCP NNTP + 0600 local FNCT socket.
        node1 = LiveNode(
            directory, image, "epoch1",
            ["--port", "0", "--control-sock", str(ctl_sock)],
        )
        try:
            port1 = int(node1.wait_marker(b"LISTENING ").split()[1])
            local_line = node1.wait_marker(b"LISTENING-LOCAL ").decode("utf-8").strip()
            assert local_line == f"LISTENING-LOCAL {ctl_sock}", local_line
            assert stat.S_IMODE(os.lstat(ctl_sock).st_mode) == 0o600

            # 3. Verify `fn groups`.
            groups_res = run_fn("groups", "--port", str(port1), as_json=True)
            assert [g["name"] for g in groups_res["groups"]] == ["ops.alerts", "ops.audit"], groups_res

            # Negative control: ungranted anonymous TCP POST is refused (exit 1).
            denied_post = run_fn(
                "post", "ops.alerts",
                "--subject", "Denied",
                "--body", "must fail before grant",
                "--port", str(port1),
                expect_rc=1,
                as_json=True,
            )
            assert denied_post["outcome"] == "refused", denied_post

            # 4. Principal & grant lifecycle + access controls.
            created = run_fn("principal", "create", "watcher", "--control-sock", str(ctl_sock), as_json=True)
            assert created["outcome"] == "accepted" and created["id"] > 0, created

            dup = run_fn(
                "principal", "create", "watcher",
                "--control-sock", str(ctl_sock),
                expect_rc=1, as_json=True,
            )
            assert dup["outcome"] == "refused" and dup["reason"] == "exists", dup

            # Non-owner bound connection cannot create principals or issue grants.
            non_admin = run_fn(
                "principal", "create", "rogue",
                "--as", "watcher",
                "--control-sock", str(ctl_sock),
                expect_rc=1, as_json=True,
            )
            assert non_admin["outcome"] == "refused" and non_admin["reason"] == "access", non_admin

            # Before consume grant, watcher cannot register a consumer cursor.
            pre_reg = run_fn(
                "stream", "register",
                "--as", "watcher",
                "--consumer", "inbox1",
                "--control-sock", str(ctl_sock),
                expect_rc=1, as_json=True,
            )
            assert pre_reg["outcome"] == "refused" and pre_reg["reason"] == "access", pre_reg

            # Issue grants: watcher gets consume + read/append on ops.alerts; anonymous gets append on ops.alerts.
            g_consume = run_fn("grant", "set", "watcher", "consume", "--control-sock", str(ctl_sock), as_json=True)
            g_read = run_fn("grant", "set", "watcher", "read", "ops.alerts", "--control-sock", str(ctl_sock), as_json=True)
            g_append = run_fn("grant", "set", "watcher", "append", "ops.alerts", "--control-sock", str(ctl_sock), as_json=True)
            g_anon = run_fn("grant", "set", "anonymous", "append", "ops.alerts", "--control-sock", str(ctl_sock), as_json=True)
            assert all(r["outcome"] == "accepted" for r in (g_consume, g_read, g_append, g_anon))

            # Inspect grants via `fn grant get`.
            got_read = run_fn("grant", "get", "watcher", "read", "ops.alerts", "--control-sock", str(ctl_sock), as_json=True)
            assert got_read["found"] is True and got_read["enabled"] is True, got_read
            got_audit = run_fn("grant", "get", "watcher", "read", "ops.audit", "--control-sock", str(ctl_sock), as_json=True)
            assert got_audit["found"] is False and got_audit["enabled"] is False, got_audit

            # 5. Register consumer cursor, park `fn stream wait`, wake via `fn post`, then `fn stream append`.
            reg = run_fn(
                "stream", "register",
                "--as", "watcher",
                "--consumer", "inbox1",
                "--start", "history",
                "--cursor-file", str(cursor_file),
                "--control-sock", str(ctl_sock),
                as_json=True,
            )
            assert reg["outcome"] == "accepted" and cursor_file.is_file(), reg
            init_cursor_hex = reg["cursor"]

            wait_proc = subprocess.Popen(
                [
                    FN, "stream", "wait",
                    "--as", "watcher",
                    "--cursor-file", str(cursor_file),
                    "--seconds", "25",
                    "--control-sock", str(ctl_sock),
                    "--json",
                ],
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            time.sleep(0.4)
            assert wait_proc.poll() is None, "stream wait exited before article arrival"

            post1 = run_fn(
                "post", "ops.alerts",
                "--subject", "Alert One",
                "--from", "sensor@fn2.invalid",
                "--msgid", "<alert-1@fn2.invalid>",
                "--body", "first alert line\n.dot-prefixed line",
                "--port", str(port1),
                as_json=True,
            )
            assert post1["outcome"] == "accepted", post1

            wait_out, wait_err = wait_proc.communicate(timeout=30)
            assert wait_proc.returncode == 0, (wait_proc.returncode, wait_out, wait_err)
            woken = json.loads(wait_out)
            assert woken["outcome"] == "accepted" and woken["count"] == 1, woken
            assert woken["items"][0]["message_id"] == "<alert-1@fn2.invalid>", woken
            pos1 = woken["items"][0]["position"]

            # Append a second article directly over the FNCT stream carrier as `watcher`.
            app2 = run_fn(
                "stream", "append",
                "--as", "watcher",
                "--group", "ops.alerts",
                "--subject", "Alert Two",
                "--from", "watcher@fn2.invalid",
                "--msgid", "<alert-2@fn2.invalid>",
                "--body", "second alert via FNCT append",
                "--op", "101",
                "--control-sock", str(ctl_sock),
                as_json=True,
            )
            assert app2["outcome"] == "accepted" and app2["evidence"] == "committed", app2

            # Read full page from initial cursor, verify both items, and durably ack pos2.
            page = run_fn(
                "stream", "read",
                "--as", "watcher",
                "--cursor-file", str(cursor_file),
                "--control-sock", str(ctl_sock),
                as_json=True,
            )
            assert page["count"] == 2, page
            assert [it["message_id"] for it in page["items"]] == [
                "<alert-1@fn2.invalid>",
                "<alert-2@fn2.invalid>",
            ], page
            pos2 = page["items"][1]["position"]
            assert pos2 > pos1

            ack2 = run_fn(
                "stream", "ack", str(pos2),
                "--as", "watcher",
                "--consumer", "inbox1",
                "--cursor-file", str(cursor_file),
                "--control-sock", str(ctl_sock),
                as_json=True,
            )
            assert ack2["outcome"] == "accepted" and ack2["position"] == pos2, ack2

            # Negative controls on ack: regression (`behind`) and past frontier (`beyond-frontier`).
            behind = run_fn(
                "stream", "ack", str(pos1),
                "--as", "watcher",
                "--cursor", init_cursor_hex,
                "--control-sock", str(ctl_sock),
                expect_rc=1, as_json=True,
            )
            assert behind["outcome"] == "refused" and behind["reason"] == "behind", behind

            stat1 = run_fn(
                "stream", "status",
                "--as", "watcher",
                "--consumer", "inbox1",
                "--control-sock", str(ctl_sock),
                as_json=True,
            )
            assert stat1["position"] == pos2, stat1

            beyond = run_fn(
                "stream", "ack", str(stat1["frontier"] + 50),
                "--as", "watcher",
                "--cursor-file", str(cursor_file),
                "--control-sock", str(ctl_sock),
                expect_rc=1, as_json=True,
            )
            assert beyond["outcome"] == "refused" and beyond["reason"] == "beyond-frontier", beyond

            # Verify NNTP `fn article` by group+number and by Message-ID (dot-unstuffed).
            art1 = run_fn("article", "ops.alerts", "1", "--port", str(port1), as_json=True)
            assert art1["message_id"] == "<alert-1@fn2.invalid>", art1
            assert "\n.dot-prefixed line" in art1["text"] and "\n..dot-prefixed" not in art1["text"], art1

            art2 = run_fn("article", "<alert-2@fn2.invalid>", "--port", str(port1), as_json=True)
            assert "second alert via FNCT append" in art2["text"], art2

            # 6. Crash immediately with SIGKILL (leaving stale control socket on disk).
            node1.sigkill()
        finally:
            node1.close()

        # 7. Restart on the SAME image and SAME `--control-sock`; verify full durable state!
        node2 = LiveNode(
            directory, image, "epoch2",
            ["--port", "0", "--control-sock", str(ctl_sock)],
        )
        try:
            port2 = int(node2.wait_marker(b"LISTENING ").split()[1])
            node2.wait_marker(b"LISTENING-LOCAL ")

            # Groups & articles survived SIGKILL.
            groups2 = run_fn("groups", "--port", str(port2), as_json=True)
            alerts_meta = next(g for g in groups2["groups"] if g["name"] == "ops.alerts")
            assert alerts_meta["high"] == 2 and alerts_meta["low"] == 1, groups2

            art1_after = run_fn("article", "ops.alerts", "1", "--port", str(port2), as_json=True)
            art2_after = run_fn("article", "<alert-2@fn2.invalid>", "--port", str(port2), as_json=True)
            assert art1_after["text"] == art1["text"]
            assert art2_after["text"] == art2["text"]

            # Principals and grants survived SIGKILL.
            got_after = run_fn("grant", "get", "watcher", "read", "ops.alerts", "--control-sock", str(ctl_sock), as_json=True)
            assert got_after["outcome"] == "accepted" and got_after["found"] is True and got_after["enabled"] is True, got_after

            # Committed consumer cursor survived SIGKILL.
            stat_after = run_fn(
                "stream", "status",
                "--as", "watcher",
                "--consumer", "inbox1",
                "--control-sock", str(ctl_sock),
                as_json=True,
            )
            assert stat_after["outcome"] == "accepted" and stat_after["position"] == pos2, stat_after

            # Appending a 3rd article after recovery delivers ONLY item 3 from the persisted cursor!
            app3 = run_fn(
                "stream", "append",
                "--as", "watcher",
                "--group", "ops.alerts",
                "--subject", "Alert Three",
                "--from", "watcher@fn2.invalid",
                "--msgid", "<alert-3@fn2.invalid>",
                "--body", "post-recovery append",
                "--op", "102",
                "--control-sock", str(ctl_sock),
                as_json=True,
            )
            assert app3["outcome"] == "accepted", app3

            page_after = run_fn(
                "stream", "read",
                "--as", "watcher",
                "--consumer", "inbox1",
                "--control-sock", str(ctl_sock),
                as_json=True,
            )
            assert [it["message_id"] for it in page_after["items"]] == ["<alert-3@fn2.invalid>"], page_after

            # Revoke watcher's append grant and verify immediate enforcement.
            rev = run_fn(
                "grant", "set", "watcher", "append", "ops.alerts",
                "--revoke",
                "--control-sock", str(ctl_sock),
                as_json=True,
            )
            assert rev["outcome"] == "accepted" and rev["enabled"] is False, rev

            denied_app = run_fn(
                "stream", "append",
                "--as", "watcher",
                "--group", "ops.alerts",
                "--subject", "Blocked",
                "--body", "should be refused after revoke",
                "--control-sock", str(ctl_sock),
                expect_rc=1, as_json=True,
            )
            assert denied_app["outcome"] == "refused", denied_app

            node2.sigkill()
        finally:
            node2.close()

        print(
            f"FN2 USER SURFACE PASS: init/serve/principal/grant/stream/nntp + SIGKILL recovery verified in {directory}"
        )
        return 0
    finally:
        for p in (ctl_sock, Path(f"{ctl_sock}.groups")):
            if p.exists():
                p.unlink()


if __name__ == "__main__":
    sys.exit(main())
