#!/usr/bin/env python3
"""Opt-in native Store device-EIO witness on an owned tmpfs loop/ext4 map.

This injects a block write error, not a power cut. The backing file lives on
tmpfs, so the result cannot qualify hbox's ZFS or hardware write cache.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import time
import uuid


ROOT = Path(__file__).resolve().parent.parent.parent
ARTICLE = (b"From: block@campaign.invalid\r\nNewsgroups: fn.letters\r\n"
           b"Subject: block fault\r\nDate: Mon, 21 Sep 2026 08:00:00 +0000\r\n"
           b"Message-ID: <block-candidate@campaign.invalid>\r\n\r\ncandidate\r\n")
PRIOR = ARTICLE.replace(b"block-candidate", b"block-prior").replace(
    b"candidate\r\n", b"prior\r\n")


def run(words, *, timeout=30, check=True, env=None):
    result = subprocess.run([str(x) for x in words], timeout=timeout, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            check=False)
    if check and result.returncode:
        raise RuntimeError("{} -> {}: {}".format(words, result.returncode,
                           result.stderr.decode("utf-8", "replace")[-1000:]))
    return result


def root(*words, **kwargs):
    return run(["sudo", "-n", *words], **kwargs)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def single_mount(path):
    result = run(["findmnt", "--mountpoint", str(path), "-rn", "-o", "SOURCE,FSTYPE,OPTIONS"],
                 check=False)
    return result.stdout.decode().strip() if result.returncode == 0 else None


class PrivateExt4:
    def __init__(self, size_mib=128):
        if run(["findmnt", "-T", "/tmp", "-rn", "-o", "FSTYPE"]).stdout.strip() != b"tmpfs":
            raise RuntimeError("/tmp is not a separate tmpfs")
        root("dmsetup", "targets")
        root("losetup", "-f")
        self.base = Path(tempfile.mkdtemp(prefix="fn-t16-block-", dir="/tmp"))
        self.backing = self.base / "backing.img"
        self.mount = self.base / "mnt"
        self.mount.mkdir()
        self.mapping = "fn-t16-" + uuid.uuid4().hex[:12]
        self.loop = None
        self.sectors = None
        self.created_map = False
        self.mounted = False
        self.mode = "none"
        fd = os.open(self.backing, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
        try:
            os.ftruncate(fd, size_mib * 1024 * 1024)
        finally:
            os.close(fd)

    def verify_loop(self):
        if self.loop is None:
            raise RuntimeError("loop device has not been allocated")
        listed = root("losetup", "-j", str(self.backing)).stdout.decode()
        if not re.search(r"^{}:.*\({}\)".format(re.escape(self.loop),
                                                    re.escape(str(self.backing))), listed, re.M):
            raise RuntimeError("loop device is no longer bound to owned backing")

    def verify_map(self):
        if not self.created_map:
            raise RuntimeError("private mapper was not created")
        self.verify_loop()
        deps = root("dmsetup", "deps", "-o", "devname", self.mapping).stdout.decode()
        if Path(self.loop).name not in deps:
            raise RuntimeError("mapper no longer depends on owned loop: " + deps)

    def create(self):
        result = root("losetup", "--find", "--show", "--nooverlap", str(self.backing))
        self.loop = result.stdout.decode().strip()
        if not re.fullmatch(r"/dev/loop[0-9]+", self.loop):
            raise RuntimeError("unexpected loop path: " + self.loop)
        self.verify_loop()
        self.sectors = int(root("blockdev", "--getsz", self.loop).stdout)
        root("dmsetup", "create", self.mapping,
             "--table", "0 {} linear {} 0".format(self.sectors, self.loop))
        self.created_map = True
        self.mode = "linear"
        self.verify_map()
        root("mkfs.ext4", "-F", "-q", "/dev/mapper/" + self.mapping, timeout=60)
        root("mount", "-t", "ext4", "-o", "nodev,nosuid,noexec",
             "/dev/mapper/" + self.mapping, str(self.mount))
        observed = single_mount(self.mount)
        if not observed or not observed.startswith("/dev/mapper/{} ext4 ".format(self.mapping)):
            raise RuntimeError("owned ext4 mount was not observed: " + str(observed))
        self.mounted = True
        root("chown", "{}:{}".format(os.getuid(), os.getgid()), str(self.mount))
        return observed

    def switch(self, mode):
        if mode not in ("linear", "error-writes"):
            raise ValueError("unknown private mapper mode")
        self.verify_map()
        table = ("0 {} linear {} 0" if mode == "linear" else
                 "0 {} flakey {} 0 0 600 1 error_writes").format(self.sectors, self.loop)
        root("dmsetup", "suspend", "--noflush", self.mapping, timeout=15)
        try:
            root("dmsetup", "reload", self.mapping, "--table", table, timeout=15)
        finally:
            root("dmsetup", "resume", self.mapping, timeout=15)
        self.mode = mode
        self.verify_map()
        observed = root("dmsetup", "table", self.mapping).stdout.decode().strip()
        if ("flakey" if mode == "error-writes" else "linear") not in observed:
            raise RuntimeError("private mapper mode did not switch: " + observed)
        return observed

    def reopen(self):
        """Close and reopen only this owned mount after device error is removed."""
        self.verify_map()
        observed = single_mount(self.mount)
        if not observed or not observed.startswith("/dev/mapper/{} ext4 ".format(self.mapping)):
            raise RuntimeError("owned ext4 mount was not observed: " + str(observed))
        root("umount", str(self.mount), timeout=30)
        self.mounted = False
        root("mount", "-t", "ext4", "-o", "nodev,nosuid,noexec",
             "/dev/mapper/" + self.mapping, str(self.mount))
        reopened = single_mount(self.mount)
        if not reopened or not reopened.startswith("/dev/mapper/{} ext4 ".format(self.mapping)):
            raise RuntimeError("owned ext4 remount was not observed: " + str(reopened))
        self.mounted = True
        return reopened

    def close(self):
        problems = []
        if self.created_map and self.mode == "error-writes":
            try:
                self.switch("linear")
            except Exception as error:
                problems.append("restore linear: " + str(error))
        if self.mounted:
            try:
                observed = single_mount(self.mount)
                if not observed or not observed.startswith("/dev/mapper/{} ext4 ".format(self.mapping)):
                    raise RuntimeError("mount identity changed: " + str(observed))
                root("umount", str(self.mount), timeout=30)
                self.mounted = False
            except Exception as error:
                problems.append("unmount: " + str(error))
        if self.created_map and not self.mounted:
            try:
                self.verify_map()
                root("dmsetup", "remove", self.mapping, timeout=15)
                self.created_map = False
            except Exception as error:
                problems.append("remove mapper: " + str(error))
        if self.loop and not self.created_map and not self.mounted:
            try:
                self.verify_loop()
                root("losetup", "-d", self.loop, timeout=15)
                self.loop = None
            except Exception as error:
                problems.append("detach loop: " + str(error))
        if not self.mounted and not self.created_map and self.loop is None:
            if (self.base.parent == Path("/tmp") and self.base.name.startswith("fn-t16-block-")
                    and self.base.stat().st_uid == os.getuid()):
                # The only remaining files are the driver-created backing,
                # payloads and trace; callers copy evidence before close.
                import shutil
                shutil.rmtree(self.base)
            else:
                problems.append("owned temporary directory identity changed")
        if problems:
            raise RuntimeError("; ".join(problems) + "; retained " + str(self.base))


def stopped_core_processes(core):
    """Find only stopped SBCL processes using this campaign's unique core path.

    strace can make the tracee its own child rather than a child visible in
    /proc/<tracer>/task/<tracer>/children, so inspect the exact core argument.
    """
    matches = []
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit():
            continue
        try:
            args = (proc / "cmdline").read_bytes().split(b"\0")
            status = (proc / "status").read_text()
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
        if (b"--core" in args and str(core).encode() in args
                and re.search(r"^State:\s+[Tt]", status, re.M)):
            matches.append(int(proc.name))
    return matches


def stopped_tracee(tracer, core, seconds=30):
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        matches = stopped_core_processes(core)
        if len(matches) == 1:
            return matches[0]
        if len(matches) > 1:
            raise RuntimeError("multiple stopped processes use this core: " + str(matches))
        if tracer.poll() is not None:
            break
        time.sleep(.05)
    raise RuntimeError("native tracee did not stop at record-attempted")


def transaction_files(store):
    return {p.name: sha(p) for p in (store / "transactions").iterdir() if p.is_file()}


def native(image, store, *args, env=None):
    return run([image, "--fn", "store", store, *args], env=env, timeout=90)


def campaign(image, out):
    if not image.is_file() or not os.access(image, os.X_OK):
        raise RuntimeError("developer native image missing")
    if not (image.name.endswith("developer") and Path(str(image) + ".core").is_file()):
        raise RuntimeError("expected a developer launcher with sibling core")
    out.mkdir(parents=True, exist_ok=False)
    device = PrivateExt4()
    tracer = None
    tracee_pid = None
    report = {"schema": "fn-t16-private-block-error-v1", "image": str(image),
              "launcher_sha256": sha(image), "core_sha256": sha(str(image) + ".core"),
              "driver_sha256": sha(__file__), "backing": str(device.backing),
              "mapping": device.mapping, "result": "incomplete"}
    try:
        report["mount"] = device.create()
        report["loop"] = device.loop
        report["sectors"] = device.sectors
        store = device.mount / "store"
        prior_path, candidate_path = device.mount / "prior.eml", device.mount / "candidate.eml"
        prior_path.write_bytes(PRIOR)
        candidate_path.write_bytes(ARTICLE)
        native(image, store, "init", "fn.letters")
        native(image, store, "post", "<block-prior@campaign.invalid>", prior_path,
               "-", "-", "fn.letters")
        prior = transaction_files(store)
        if len(prior) != 1:
            raise RuntimeError("baseline did not create one durable transaction")
        report["prior_transactions"] = prior
        env = dict(os.environ, FN_NATIVE_POST_FAULT="record-attempted:stop")
        prefix = device.base / "strace"
        tracer = subprocess.Popen(["strace", "-f", "-ff", "-yy", "-e",
                                   "trace=fsync,fdatasync,link,linkat", "-o", str(prefix),
                                   str(image), "--fn", "store", str(store), "post",
                                  "<block-candidate@campaign.invalid>", str(candidate_path),
                                  "-", "-", "fn.letters"],
                                  env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  start_new_session=True)
        tracee_pid = stopped_tracee(tracer, str(image) + ".core")
        linked = transaction_files(store)
        new_names = set(linked) - set(prior)
        if len(new_names) != 1 or any(linked[name] != digest for name, digest in prior.items()):
            raise RuntimeError("record-attempted did not retain prior and link one exact candidate")
        report["linked_transaction"] = {name: linked[name] for name in new_names}
        report["stopped_pid"] = tracee_pid
        report["error_table"] = device.switch("error-writes")
        os.kill(tracee_pid, signal.SIGCONT)
        tracee_pid = None
        stdout, stderr = tracer.communicate(timeout=90)
        report["post_exit"] = tracer.returncode
        report["post_stdout"] = stdout.decode("utf-8", "replace")[-1000:]
        report["post_stderr"] = stderr.decode("utf-8", "replace")[-1000:]
        if report["post_exit"] != 3 or "indeterminate" not in report["post_stderr"]:
            raise RuntimeError("native post did not report uncertain publication")
        tracer = None
        traces = "\n".join(p.read_text(errors="replace") for p in device.base.glob("strace.*"))
        (out / "strace.txt").write_text(traces)
        report["strace_sha256"] = sha(out / "strace.txt")
        final_name = next(iter(new_names))
        report["link_syscall_success"] = bool(re.search(
            r"link\([^\n]*?/transactions/{}\"\)\s+=\s+0".format(
                re.escape(final_name)), traces))
        if not report["link_syscall_success"]:
            raise RuntimeError("no observed successful final transaction link")
        report["transaction_fsync_eio"] = bool(re.search(
            r"fsync\([^\n]*?/transactions[^\n]*?\)\s+=\s+-1 EIO", traces))
        if not report["transaction_fsync_eio"]:
            raise RuntimeError("no observed EIO return from transactions directory fsync")
        report["linear_table"] = device.switch("linear")
        report["post_transactions_same_mount"] = transaction_files(store)
        report["reopened_mount"] = device.reopen()
        report["post_transactions_reopened"] = transaction_files(store)
        reopened = report["post_transactions_reopened"]
        if any(reopened.get(name) != digest for name, digest in prior.items()):
            raise RuntimeError("reopen changed an older durable transaction")
        if set(reopened) == set(prior):
            report["reopened_outcome"] = "older-prefix"
        elif reopened == linked:
            report["reopened_outcome"] = "exact-candidate"
        else:
            raise RuntimeError("reopened transactions are neither older prefix nor exact candidate")
        result = run([image, "--fn", "store", store, "recover"],
                     check=False, timeout=90)
        report["recover"] = {
            "stdout": result.stdout.decode("utf-8", "replace")[-1000:],
            "stderr": result.stderr.decode("utf-8", "replace")[-1000:]}
        report["recover_exit"] = result.returncode
        if result.returncode != 0:
            raise RuntimeError("native recovery failed after owned filesystem reopen")
        report["result"] = "observed-eio"
    finally:
        cleanup_problems = []
        if tracer is not None:
            try:
                # This campaign created the process group. Resume stopped
                # members before killing it so no tracee is left orphaned.
                group_active = tracer.poll() is None
                if group_active:
                    os.killpg(tracer.pid, signal.SIGCONT)
                    os.killpg(tracer.pid, signal.SIGKILL)
                else:
                    matches = stopped_core_processes(str(image) + ".core")
                    if tracee_pid is None and len(matches) == 1:
                        tracee_pid = matches[0]
                if not group_active and tracee_pid is not None:
                    os.kill(tracee_pid, signal.SIGCONT)
                    os.kill(tracee_pid, signal.SIGKILL)
                tracer.communicate(timeout=5)
            except (ProcessLookupError, subprocess.TimeoutExpired) as error:
                cleanup_problems.append("tracee cleanup: " + str(error))
        try:
            device.close()
        except Exception as error:
            cleanup_problems.append("private device cleanup: " + str(error))
        if cleanup_problems:
            report["cleanup_error"] = "; ".join(cleanup_problems)
        (out / "result.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    if report.get("cleanup_error"):
        raise RuntimeError(report["cleanup_error"])
    return report


def probe(out):
    """Qualify the private mapping and cleanup before a native image is used."""
    out.mkdir(parents=True, exist_ok=False)
    device = PrivateExt4()
    report = {"schema": "fn-t16-private-block-probe-v1", "result": "incomplete",
              "driver_sha256": sha(__file__), "backing": str(device.backing),
              "mapping": device.mapping}
    try:
        report["mount"] = device.create()
        report["loop"] = device.loop
        test_file = device.mount / "probe.bin"
        with test_file.open("wb") as stream:
            stream.write(b"baseline" * 512)
            stream.flush()
            os.fsync(stream.fileno())
        report["error_table"] = device.switch("error-writes")
        with test_file.open("ab") as stream:
            try:
                stream.write(b"faulted" * 512)
                stream.flush()
                os.fsync(stream.fileno())
                report["write_error"] = None
            except OSError as error:
                report["write_error"] = {"errno": error.errno,
                                         "message": str(error)}
        report["linear_table"] = device.switch("linear")
        report["result"] = "observed-error" if report["write_error"] else "no-error"
    finally:
        try:
            device.close()
        except Exception as error:
            report["cleanup_error"] = str(error)
        (out / "result.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    if report.get("cleanup_error"):
        raise RuntimeError(report["cleanup_error"])
    return report


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--image", type=Path)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--probe", action="store_true")
    args = ap.parse_args()
    if args.probe:
        if args.image:
            ap.error("--probe does not use --image")
        report = probe(args.out.resolve())
    else:
        if not args.image:
            ap.error("--image is required for the native campaign")
        report = campaign(args.image.resolve(), args.out.resolve())
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
