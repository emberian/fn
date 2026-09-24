#!/usr/bin/env python3
"""Opt-in native Store publication fault profile on owned tmpfs loop/ext4.

Cases inject a block write error, kill a stopped process, or recover a copied
backing image after simulated volatile write loss. None is a physical power
cut. The backing files live on tmpfs, so results cannot qualify hbox's ZFS or
hardware write cache.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import shutil
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


def exact_dm_loop_dependency(output, expected_loop):
    match = re.fullmatch(r"\s*1 dependencies\s*:\s*\((loop[0-9]+)\)\s*", output)
    return bool(match and match.group(1) == Path(expected_loop).name)


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
        if not exact_dm_loop_dependency(deps, self.loop):
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

    def snapshot_without_volatile_writes(self):
        """Copy only this mapper's backing bytes while it admits no more I/O."""
        self.verify_map()
        snapshot = self.base / "cut-snapshot.img"
        if snapshot.exists():
            raise RuntimeError("owned snapshot already exists")
        root("dmsetup", "suspend", "--noflush", self.mapping, timeout=15)
        try:
            fd = os.open(snapshot, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                         0o600)
            with self.backing.open("rb") as source, os.fdopen(fd, "wb") as target:
                shutil.copyfileobj(source, target, length=1024 * 1024)
                target.flush()
                os.fsync(target.fileno())
        finally:
            root("dmsetup", "resume", self.mapping, timeout=15)
        if snapshot.stat().st_size != self.backing.stat().st_size:
            raise RuntimeError("private backing snapshot is incomplete")
        return snapshot

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


class OwnedSnapshotMount:
    """Mount only a copied backing file owned by the current private run."""

    def __init__(self, device, backing):
        if backing.parent != device.base or backing.name != "cut-snapshot.img":
            raise RuntimeError("snapshot is outside the owned device directory")
        if backing.stat().st_uid != os.getuid():
            raise RuntimeError("snapshot ownership changed")
        self.backing = backing
        self.mount = device.base / "snapshot-mnt"
        self.mount.mkdir()
        self.loop = None
        self.mounted = False

    def verify_loop(self):
        if not self.loop:
            raise RuntimeError("snapshot loop was not allocated")
        listed = root("losetup", "-j", str(self.backing)).stdout.decode()
        if not re.search(r"^{}:.*\({}\)".format(re.escape(self.loop),
                                                    re.escape(str(self.backing))), listed, re.M):
            raise RuntimeError("snapshot loop is no longer bound to owned bytes")

    def open(self):
        self.loop = root("losetup", "--find", "--show", "--nooverlap",
                         str(self.backing)).stdout.decode().strip()
        if not re.fullmatch(r"/dev/loop[0-9]+", self.loop):
            raise RuntimeError("unexpected snapshot loop: " + self.loop)
        self.verify_loop()
        root("mount", "-t", "ext4", "-o", "nodev,nosuid,noexec",
             self.loop, str(self.mount))
        self.mounted = True
        observed = single_mount(self.mount)
        if not observed or not observed.startswith(self.loop + " ext4 "):
            raise RuntimeError("owned snapshot mount was not observed: " + str(observed))
        root("chown", "{}:{}".format(os.getuid(), os.getgid()), str(self.mount))
        return observed

    def close(self):
        problems = []
        if self.mounted:
            try:
                observed = single_mount(self.mount)
                if not observed or not observed.startswith(self.loop + " ext4 "):
                    raise RuntimeError("snapshot mount identity changed: " + str(observed))
                root("umount", str(self.mount), timeout=30)
                self.mounted = False
            except Exception as error:
                problems.append("snapshot unmount: " + str(error))
        if self.loop and not self.mounted:
            try:
                self.verify_loop()
                root("losetup", "-d", self.loop, timeout=15)
                self.loop = None
            except Exception as error:
                problems.append("snapshot loop detach: " + str(error))
        if problems:
            raise RuntimeError("; ".join(problems) + "; retained " + str(self.backing))


@dataclass(frozen=True)
class ProcIdentity:
    pid: int
    group: int
    session: int
    start_time: int
    state: str
    argv: tuple[bytes, ...]


def read_proc_identity(pid):
    """Read Linux process identity; stat start_time defeats PID reuse."""
    proc = Path("/proc") / str(pid)
    try:
        stat = (proc / "stat").read_text()
        argv = tuple(x for x in (proc / "cmdline").read_bytes().split(b"\0") if x)
    except (FileNotFoundError, ProcessLookupError, PermissionError):
        return None
    close_comm = stat.rfind(")")
    if close_comm < 0:
        return None
    tail = stat[close_comm + 2:].split()
    if len(tail) < 20:
        return None
    return ProcIdentity(pid, int(tail[2]), int(tail[3]), int(tail[19]),
                        tail[0], argv)


def exact_core_arg(argv, core):
    return any(argv[i:i + 2] == (b"--core", str(core).encode())
               for i in range(len(argv) - 1))


def owned_tracee(identity, group_id, core):
    return (identity is not None and identity.group == group_id
            and identity.session == group_id and identity.state in ("T", "t")
            and exact_core_arg(identity.argv, core))


def stopped_core_processes(core, group_id):
    """Find stopped tracees only in this campaign-created process session."""
    matches = []
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit():
            continue
        identity = read_proc_identity(int(proc.name))
        if owned_tracee(identity, group_id, core):
            matches.append(identity)
    return matches


def stopped_tracee(tracer, core, seconds=30):
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        matches = stopped_core_processes(core, tracer.pid)
        if len(matches) == 1:
            return matches[0]
        if len(matches) > 1:
            raise RuntimeError("multiple stopped processes use this core: " + str(matches))
        if tracer.poll() is not None:
            break
        time.sleep(.05)
    raise RuntimeError("native tracee did not stop at selected model cut")


def signal_owned_process(expected, signum, *, session_id, core=None):
    """Signal one checked process through pidfd, never a core-path glob."""
    if expected.group != session_id or expected.session != session_id:
        raise RuntimeError("target is outside the campaign process session")
    try:
        fd = os.pidfd_open(expected.pid)
    except ProcessLookupError:
        return False
    try:
        current = read_proc_identity(expected.pid)
        if (current is None or current.start_time != expected.start_time
                or current.group != session_id
                or current.session != session_id
                or (core is not None and not exact_core_arg(current.argv, core))):
            raise RuntimeError("process identity changed before signal: " + str(expected.pid))
        try:
            signal.pidfd_send_signal(fd, signum)
        except ProcessLookupError:
            return False
        return True
    finally:
        os.close(fd)


def transaction_files(store):
    return {p.name: sha(p) for p in (store / "transactions").iterdir() if p.is_file()}


def native(image, store, *args, env=None):
    return run([image, "--fn", "store", store, *args], env=env, timeout=90)


SCENARIOS = ("record-dir-eio", "frontier-dir-eio", "record-dir-sigkill",
             "record-cut-snapshot")


def campaign(image, out, scenario="record-dir-eio"):
    if scenario not in SCENARIOS:
        raise ValueError("unknown private block scenario: " + scenario)
    if not image.is_file() or not os.access(image, os.X_OK):
        raise RuntimeError("developer native image missing")
    if not (image.name.endswith("developer") and Path(str(image) + ".core").is_file()):
        raise RuntimeError("expected a developer launcher with sibling core")
    out.mkdir(parents=True, exist_ok=False)
    device = PrivateExt4()
    tracer = None
    tracer_identity = None
    tracee = None
    snapshot_mount = None
    report = {"schema": "fn-t16-private-block-profile-v2", "scenario": scenario,
              "image": str(image),
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
        frontier = store / "allocation-frontier.json"
        report["prior_frontier_sha256"] = sha(frontier)
        cut = ("frontier-attempted" if scenario == "frontier-dir-eio"
               else "record-attempted")
        report["model_program"] = ("fn-bs-frontier-program" if cut.startswith("frontier")
                                   else "fn-bs-record-program")
        report["model_cut"] = cut
        env = dict(os.environ, FN_NATIVE_POST_FAULT=cut + ":stop")
        prefix = device.base / "strace"
        tracer = subprocess.Popen(["strace", "-f", "-ff", "-yy", "-e",
                                   "trace=fsync,fdatasync,link,linkat,rename,renameat",
                                   "-o", str(prefix),
                                   str(image), "--fn", "store", str(store), "post",
                                  "<block-candidate@campaign.invalid>", str(candidate_path),
                                  "-", "-", "fn.letters"],
                                  env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  start_new_session=True)
        tracer_identity = read_proc_identity(tracer.pid)
        if (tracer_identity is None or tracer_identity.group != tracer.pid
                or tracer_identity.session != tracer.pid):
            raise RuntimeError("tracer did not enter its own process session")
        tracee = stopped_tracee(tracer, str(image) + ".core")
        linked = transaction_files(store)
        new_names = set(linked) - set(prior)
        if any(linked.get(name) != digest for name, digest in prior.items()):
            raise RuntimeError("model cut changed a prior durable transaction")
        if cut == "record-attempted":
            if len(new_names) != 1:
                raise RuntimeError("record-attempted did not link one exact candidate")
            report["linked_transaction"] = {name: linked[name] for name in new_names}
        elif new_names:
            raise RuntimeError("frontier-attempted linked a candidate too early")
        report["attempted_frontier_sha256"] = sha(frontier)
        if (cut == "frontier-attempted"
                and report["attempted_frontier_sha256"] == report["prior_frontier_sha256"]):
            raise RuntimeError("frontier cut did not replace the allocator bytes")
        report["stopped_pid"] = tracee.pid
        report["stopped_start_time"] = tracee.start_time
        if scenario.endswith("eio"):
            report["error_table"] = device.switch("error-writes")
            sent = signal_owned_process(tracee, signal.SIGCONT, session_id=tracer.pid,
                                        core=str(image) + ".core")
        else:
            if scenario == "record-cut-snapshot":
                snapshot = device.snapshot_without_volatile_writes()
                report["snapshot_sha256"] = sha(snapshot)
            sent = signal_owned_process(tracee, signal.SIGKILL, session_id=tracer.pid,
                                        core=str(image) + ".core")
        if not sent:
            raise RuntimeError("owned native tracee disappeared before signal")
        stdout, stderr = tracer.communicate(timeout=90)
        report["post_exit"] = tracer.returncode
        report["post_stdout"] = stdout.decode("utf-8", "replace")[-1000:]
        report["post_stderr"] = stderr.decode("utf-8", "replace")[-1000:]
        if scenario.endswith("eio"):
            if report["post_exit"] != 3 or "indeterminate" not in report["post_stderr"]:
                raise RuntimeError("native post did not report uncertain publication")
        elif report["post_exit"] == 0:
            raise RuntimeError("SIGKILL case unexpectedly reported publication success")
        tracer = None
        traces = "\n".join(p.read_text(errors="replace") for p in device.base.glob("strace.*"))
        (out / "strace.txt").write_text(traces)
        report["strace_sha256"] = sha(out / "strace.txt")
        if cut == "record-attempted":
            final_name = next(iter(new_names))
            report["link_syscall_success"] = bool(re.search(
                r"link\([^\n]*?/transactions/{}\"\)\s+=\s+0".format(
                    re.escape(final_name)), traces))
            if not report["link_syscall_success"]:
                raise RuntimeError("no observed successful final transaction link")
        else:
            report["frontier_rename_success"] = bool(re.search(
                r"rename\([^\n]*?/allocation-frontier\.json\"\)\s+=\s+0", traces))
            if not report["frontier_rename_success"]:
                raise RuntimeError("no observed successful frontier replacement")
        if scenario.endswith("eio"):
            barrier = ("transactions" if cut == "record-attempted" else "store")
            report["directory_fsync_eio"] = bool(re.search(
                r"fsync\([^\n]*?/{0}[^\n]*?\)\s+=\s+-1 EIO".format(barrier), traces))
            if not report["directory_fsync_eio"]:
                raise RuntimeError("no observed EIO from authority directory fsync")
            report["linear_table"] = device.switch("linear")
        report["post_transactions_same_mount"] = transaction_files(store)
        if scenario == "record-cut-snapshot":
            # The original mount is closed first, so the duplicate ext4 UUID
            # is never mounted concurrently. The copied bytes alone supply
            # the reopened image; later original-mount flushes cannot alter it.
            observed = single_mount(device.mount)
            if not observed or not observed.startswith(
                    "/dev/mapper/{} ext4 ".format(device.mapping)):
                raise RuntimeError("owned original mount changed before snapshot reopen")
            root("umount", str(device.mount), timeout=30)
            device.mounted = False
            snapshot_mount = OwnedSnapshotMount(device, snapshot)
            report["reopened_mount"] = snapshot_mount.open()
            reopened_store = snapshot_mount.mount / "store"
        else:
            report["reopened_mount"] = device.reopen()
            reopened_store = store
        report["post_transactions_reopened"] = transaction_files(reopened_store)
        reopened = report["post_transactions_reopened"]
        if any(reopened.get(name) != digest for name, digest in prior.items()):
            raise RuntimeError("reopen changed an older durable transaction")
        if cut == "frontier-attempted":
            if reopened != prior:
                raise RuntimeError("frontier cut changed transaction history")
            reopened_frontier = sha(reopened_store / "allocation-frontier.json")
            report["reopened_frontier_sha256"] = reopened_frontier
            if reopened_frontier == report["prior_frontier_sha256"]:
                report["reopened_outcome"] = "older-frontier"
            elif reopened_frontier == report["attempted_frontier_sha256"]:
                report["reopened_outcome"] = "advanced-frontier"
            else:
                raise RuntimeError("reopened frontier is neither old nor exact candidate")
        elif set(reopened) == set(prior):
            report["reopened_outcome"] = "older-prefix"
        elif reopened == linked:
            report["reopened_outcome"] = "exact-candidate"
        else:
            raise RuntimeError("reopened transactions are neither older prefix nor exact candidate")
        result = run([image, "--fn", "store", reopened_store, "recover"],
                     check=False, timeout=90)
        report["recover"] = {
            "stdout": result.stdout.decode("utf-8", "replace")[-1000:],
            "stderr": result.stderr.decode("utf-8", "replace")[-1000:]}
        report["recover_exit"] = result.returncode
        if result.returncode != 0:
            raise RuntimeError("native recovery failed after owned filesystem reopen")
        report["result"] = ("observed-eio" if scenario.endswith("eio")
                            else "observed-simulated-write-loss" if snapshot_mount
                            else "observed-process-death")
    finally:
        cleanup_problems = []
        if tracer is not None:
            try:
                if tracee is None:
                    current_tracer = read_proc_identity(tracer.pid)
                    if (tracer_identity is not None and current_tracer is not None
                            and current_tracer.start_time == tracer_identity.start_time
                            and current_tracer.group == tracer.pid
                            and current_tracer.session == tracer.pid):
                        matches = stopped_core_processes(str(image) + ".core",
                                                         tracer.pid)
                        if len(matches) == 1:
                            tracee = matches[0]
                        elif len(matches) > 1:
                            raise RuntimeError("multiple stopped tracees in owned session")
                    else:
                        cleanup_problems.append("tracer identity unavailable; no tracee selected")
                if tracee is not None:
                    signal_owned_process(tracee, signal.SIGCONT, session_id=tracer.pid,
                                         core=str(image) + ".core")
                    signal_owned_process(tracee, signal.SIGKILL, session_id=tracer.pid,
                                         core=str(image) + ".core")
                if tracer_identity is not None:
                    signal_owned_process(tracer_identity, signal.SIGKILL,
                                         session_id=tracer.pid)
                tracer.communicate(timeout=5)
            except (RuntimeError, subprocess.TimeoutExpired) as error:
                cleanup_problems.append("tracee cleanup: " + str(error))
        snapshot_clean = True
        if snapshot_mount is not None:
            try:
                snapshot_mount.close()
            except Exception as error:
                snapshot_clean = False
                cleanup_problems.append("private snapshot cleanup: " + str(error))
        if snapshot_clean:
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
    ap.add_argument("--scenario", choices=SCENARIOS, default="record-dir-eio")
    args = ap.parse_args()
    if args.probe:
        if args.image:
            ap.error("--probe does not use --image")
        report = probe(args.out.resolve())
    else:
        if not args.image:
            ap.error("--image is required for the native campaign")
        report = campaign(args.image.resolve(), args.out.resolve(), args.scenario)
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
