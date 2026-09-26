#!/usr/bin/env python3
"""The service envelope of a native image for one named profile (PKT-335,
SCN-109; answers section 3, mandate section 15).

Runs ON hbox, each subcommand inside its own `systemd-run --user
--unit=senv-... -p MemoryMax=40G` unit (the throughput gate's quiet check
then names it), each under 30 minutes.  A store directory DIR holds the
store, the author's keys and DIR/state.json; the subcommands resume from it.

    load     init DIR once (the named profile below; one hybrid author
             enrolled through the control socket), then POST articles of
             about --octets over one connection until the store holds --to
             articles: every --signed-every-th a hybrid-signed carrier signed
             by the image's own `hybrid-sign-carrier`, the rest unsigned.
             Stops cleanly (owner stopped, state written) when --budget
             seconds have passed; the next `load` reopens and continues.
             The preload is not a measured row.
    clone    copy DIR to another filesystem (the ZFS rows: the store is
             loaded on tmpfs and copied, so the loading does not spend a
             unit's budget on the pool's commit latency; the measured rows
             then run against the copy).  The copy is recorded.
    measure  --steps, in order (default latency,restart,rate,checkpoint,
             restart); an owner starts when a step needs one and every start
             is an `opens` row (N, what preceded it, seconds to LISTENING,
             VmHWM): on a loaded store that row is the reopen.
               load      (with --load-to N) the preload above, on this
                         owner: the warm rows then follow on the process
                         that loaded the store (N = 100,000, whose reopen
                         is its own unit)
               latency   on the loaded store, one sequential client:
                         greeting  K fresh connections, connect to the 200
                         over40    K `OVER lo-hi` over a 40-article window
                         over100   K over a 100-article range (spread)
                         post      K unsigned POSTs of about --octets on one
                                   connection: command to reply, and the
                                   final terminator to the durable reply
                         signed    hybrid-signed POSTs (carriers signed
                                   before the owner started), both intervals
               restart   stop the owner (the next step starts one)
               rate      --rate-seconds of closed-loop POSTs on one
                         connection, then on --connections, while --readers
                         connections loop ARTICLE: POSTs a second, per 10 s
                         window (a growing queue shows as a falling rate)
               checkpoint  stop, offline `store checkpoint` (timed); the
                         next start is the checkpoint-assisted reopen
             Beside every row: the owner's CPU seconds (/proc), VmRSS and
             VmHWM, the store's disk octets and inodes before and after,
             the box load, the filesystem and, on ZFS, `zfs list` and
             `zpool list`.  Bytes consed and the live heap need the
             heap-hook image (rep_measure.py --heap-dir); the owner exposes
             no mutex-held accounting: both are recorded as not exposed
             rather than estimated.  The JSON is rewritten after every row,
             so a unit that dies (the 40G ceiling) keeps the rows before it.

The profile (named `scale-1m`): `operator init --profile scale
--max-transactions 1048576 --max-history-octets 4294967296
--max-article-octets 16384 fn.test`: the scale preset (the throughput
gate's and signed-history-index's) with the transaction count raised for
N = 100,000 plus the measured POSTs, the history bound raised to 4 GiB, and
A at 16 KiB so a hybrid carrier of a 2 KiB source fits.  One group, one
group per article, no pins, no relay debt, a loopback listener with no
exposure rows (loopback keeps them off).

A loopback scripted measurement: not a multi-machine result, not a human
study, not a power-loss qualification.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT))
import msgid_measure as m  # noqa: E402
import rep_measure as r  # noqa: E402
import signed_carriers as sc  # noqa: E402

OPENSSL = "/tank/fn/toolchains/openssl-3.5.8"
PROFILE_NAME = "scale-1m"
PROFILE = ["--profile", "scale", "--max-transactions", "1048576", "--max-history-octets", "4294967296",
           "--max-article-octets", "16384"]
GROUP = "fn.test"


def now():
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def image_env():
    env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env["LD_LIBRARY_PATH"] = OPENSSL + "/lib" + (":" + env["LD_LIBRARY_PATH"] if env.get("LD_LIBRARY_PATH") else "")
    return env


def write_config(d, port):
    config = d / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (d / "store", port, d / "c.sock"), encoding="ascii")
    return config


def load_state(d):
    return json.loads((d / "state.json").read_text())


def save_state(d, state):
    (d / "state.tmp").write_text(json.dumps(state, indent=2) + "\n")
    os.replace(d / "state.tmp", d / "state.json")


def owner_cpu(pid):
    fields = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1].split()
    return (int(fields[11]) + int(fields[12])) / os.sysconf("SC_CLK_TCK")


def disk(d):
    """Octets and inodes under the store directory (st_blocks, not length)."""
    octets = inodes = 0
    for root, dirs, files in os.walk(d / "store"):
        for name in dirs + files:
            st = os.lstat(os.path.join(root, name))
            octets += st.st_blocks * 512
            inodes += 1
    return {"octets": octets, "inodes": inodes}


def filesystem(d):
    out = subprocess.run(["stat", "-f", "-c", "%T", str(d)], stdout=subprocess.PIPE, text=True).stdout.strip()
    row = {"type": out}
    if out == "zfs":
        src = subprocess.run(["df", "--output=source", str(d)], stdout=subprocess.PIPE, text=True).stdout.split()[-1]
        row["dataset"] = src
        row["zfs_list"] = subprocess.run(["zfs", "list", "-H", "-p", "-o", "name,used,avail,refer,compression,recordsize,sync",
                                          src], stdout=subprocess.PIPE, text=True).stdout.strip()
        pool = src.split("/")[0]
        row["zpool_list"] = subprocess.run(["zpool", "list", "-H", "-o", "name,size,alloc,free,frag,cap,health", pool],
                                           stdout=subprocess.PIPE, text=True).stdout.strip()
        row["zpool_log_devices"] = "logs" in subprocess.run(["zpool", "status", pool], stdout=subprocess.PIPE,
                                                            text=True).stdout
    return row


def open_mode(stderr):
    """The owner's own account of how it opened the Store (its OWNER-OPEN
    line: `open=checkpoint:S suffix=K` or `open=full-replay reason=R`)."""
    lines = [l for l in stderr.decode("ascii", "replace").splitlines() if l.startswith("OWNER-OPEN ")]
    return lines[-1][len("OWNER-OPEN "):] if lines else None


def is_signed(i, every):
    return every > 0 and i % every == every // 2


class Owner:
    def __init__(self, image, d, env, label, timeout):
        self.port = m.free_port()
        self.config = write_config(d, self.port)
        stderr = d / ("owner-%s.stderr" % label)
        self.proc, self.open_s, self.err = r.start_owner(image, self.config, env, stderr, timeout=timeout)
        self.mode = open_mode(stderr.read_bytes())

    def cpu(self):
        return owner_cpu(self.proc.pid)

    def memory(self):
        return {"rss_kib": r.status_kib(self.proc.pid, "VmRSS"), "hwm_kib": r.status_kib(self.proc.pid, "VmHWM")}

    def stop(self):
        r.stop_owner(self.proc, self.err)


# ---------------------------------------------------------------------------

def init_dir(image, d, env, octets, signed_every):
    d.mkdir(parents=True, exist_ok=False)
    config = write_config(d, 1)
    init = subprocess.run([str(image), "--fn", "operator", str(config), "init"] + PROFILE + [GROUP],
                          env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if init.returncode:
        raise SystemExit("init rc=%d: %r" % (init.returncode, init.stdout[-600:]))
    sc.HybridAuthor(image, env, d / "author", OPENSSL + "/bin/openssl")
    state = {"profile": PROFILE_NAME, "init_args": PROFILE + [GROUP], "image": str(image),
             "core_sha256": m.digest(str(image) + ".core"), "octets": octets,
             "signed_every": signed_every, "count": 0, "loaded": 0, "signed": 0, "enrolled": False,
             "init_out": init.stdout.decode("ascii", "replace"), "loads": []}
    save_state(d, state)
    return state


def load_into(owner, author, d, state, to, deadline, session_posts=None):
    """POST the preload on OWNER until the store holds TO articles, the
    monotonic DEADLINE passes or SESSION_POSTS were posted; the run's row."""
    run = {"started_utc": now(), "from": state["count"]}
    if not state["enrolled"]:
        author.enroll(d / "c.sock")
        state["enrolled"] = True
        save_state(d, state)
    c = m.Conn(owner.port)
    # A resumed load after an owner that died mid-POST: that POST's outcome
    # was uncertain, and the store (not this file) says whether it is held.
    i = state["count"]
    if i and not is_signed(i, state["signed_every"]):
        if c.line("STAT %s" % m.msgid(i)).startswith(b"223"):
            run["uncertain_post_was_stored"] = i
            state["count"] = state["loaded"] = i + 1
    t0, c0 = time.perf_counter(), owner.cpu()
    posted = 0
    while state["count"] < to and time.monotonic() < deadline and (session_posts is None or posted < session_posts):
        posted += 1
        i = state["count"]
        if is_signed(i, state["signed_every"]):
            sc.post_octets(c, author.sign("senv-load-%d" % i, state["octets"]))
            state["signed"] += 1
        else:
            r.post(c, i, state["octets"])
        state["count"] = state["loaded"] = i + 1
        if state["count"] % 1000 == 0:
            save_state(d, state)
            print("loaded %d in %.1f s" % (state["count"], time.perf_counter() - t0), flush=True)
    c.close()
    run.update(to=state["count"], seconds=round(time.perf_counter() - t0, 3),
               owner_cpu_s=round(owner.cpu() - c0, 3), memory=owner.memory(), finished_utc=now())
    state["loads"].append(run)
    save_state(d, state)
    print(json.dumps(run), flush=True)
    return run


def load(a):
    image, d, env = Path(a.image).resolve(), Path(a.dir), image_env()
    deadline = time.monotonic() + a.budget
    state = load_state(d) if (d / "state.json").exists() else init_dir(image, d, env, a.octets, a.signed_every)
    if state["octets"] != a.octets or state["signed_every"] != a.signed_every:
        raise SystemExit("DIR was loaded with --octets %d --signed-every %d" % (state["octets"], state["signed_every"]))
    author = sc.HybridAuthor.existing(image, env, d / "author")
    owner = Owner(image, d, env, "load-%d" % state["count"], a.open_timeout)
    try:
        load_into(owner, author, d, state, a.to, deadline)
    finally:
        owner.stop()
        save_state(d, state)
    return 0 if state["count"] >= a.to else 75


def clone(a):
    src, dst = Path(a.dir), Path(a.to_dir)
    if dst.exists():
        raise SystemExit("%s exists" % dst)
    t0 = time.perf_counter()
    shutil.copytree(src, dst, symlinks=True)
    for stale in ("c.sock", "c.sock.lock", "fn.toml"):
        (dst / stale).unlink(missing_ok=True)
    dropped = None
    if a.drop_checkpoint:
        # The state checkpoint is derived (the full replay is authoritative
        # and decides): without it the next open is the full replay, which
        # is the row being measured.  Only ever on a copy.
        ck = dst / "store" / "store-checkpoint.fnsc"
        dropped = ck.stat().st_size if ck.exists() else 0
        ck.unlink(missing_ok=True)
    subprocess.run(["sync", "-f", str(dst)], check=False)
    state = load_state(dst)
    state["cloned_from"] = {"dir": str(src), "utc": now(), "seconds": round(time.perf_counter() - t0, 3),
                            "filesystem": filesystem(dst), "dropped_checkpoint_octets": dropped}
    save_state(dst, state)
    print(json.dumps(state["cloned_from"]))
    return 0


# ---------------------------------------------------------------------------

ROW_BUDGET = [120.0]


def timed_rows(fn, k):
    """K timings of FN, or as many as ROW_BUDGET seconds allow (at least 5):
    the row then says `capped` and its n is the samples taken."""
    started, times = time.monotonic(), []
    for i in range(k):
        times.append(fn(i))
        if len(times) >= 5 and time.monotonic() - started > ROW_BUDGET[0]:
            break
    out = m.summary(times)
    if len(times) < k:
        out["capped"] = "%d of %d samples within %.0f s" % (len(times), k, ROW_BUDGET[0])
    return out


def reader_loop(port, msgids, stop, counter, errors):
    try:
        c = m.Conn(port)
        i = 0
        while not stop.is_set():
            _, reply, _ = r.timed_multiline(c, "ARTICLE %s" % msgids[i % len(msgids)])
            if not reply.startswith(b"220"):
                errors.append(reply.decode("ascii", "replace"))
                break
            counter[0] += 1
            i += 1
        c.close()
    except Exception as e:  # noqa: BLE001 - reported
        errors.append(repr(e))


def present_msgids(state, k=64):
    """Up to K unsigned Message-IDs of the preload, spread over it."""
    n = state["loaded"]
    ids = [i for i in range(0, n, max(1, n // k)) if not is_signed(i, state["signed_every"])]
    return [m.msgid(i) for i in ids[:k]]


def rate_phase(owner, state, lock, connections, seconds, readers, octets):
    """Closed-loop POSTs on CONNECTIONS connections for SECONDS while READERS
    loop ARTICLE; POSTs a second overall and per 10 s window."""
    n0 = state["count"]
    present = present_msgids(state)
    stop, rcount, errors, threads = threading.Event(), [0], [], []
    for _ in range(readers):
        t = threading.Thread(target=reader_loop, args=(owner.port, present, stop, rcount, errors), daemon=True)
        t.start()
        threads.append(t)
    done, lat = [], []
    deadline = [None]
    # Every connection is open before the window starts: the rate is of
    # POSTs, and the cost of opening a connection is the greeting row's.
    opened, go = threading.Barrier(connections + 1), threading.Event()

    def poster():
        try:
            c = m.Conn(owner.port)
            opened.wait()
            go.wait()
            while time.perf_counter() < deadline[0]:
                with lock:
                    i = state["count"]
                    state["count"] = i + 1
                dt = r.post(c, i, octets)
                with lock:
                    done.append(time.perf_counter())
                    lat.append(dt)
            c.close()
        except BaseException as e:  # noqa: BLE001 - reported (SystemExit included)
            errors.append(repr(e))

    posters = [threading.Thread(target=poster, daemon=True) for _ in range(connections)]
    c_open = time.perf_counter()
    for t in posters:
        t.start()
    try:
        opened.wait(timeout=1800)
    except threading.BrokenBarrierError:
        errors.append("the posters' connections did not all open within 1800 s")
    connect_s = time.perf_counter() - c_open
    c0 = owner.cpu()
    t0 = time.perf_counter()
    deadline[0] = t0 + seconds
    go.set()
    for t in posters:
        t.join(timeout=seconds + 300)
    wall = time.perf_counter() - t0
    stop.set()
    for t in threads:
        t.join(timeout=120)
    windows = [0] * max(1, int(-(-seconds // 10)))
    for t in done:
        windows[min(len(windows) - 1, int((t - t0) // 10))] += 1
    row = {"connections": connections, "readers": readers, "connect_s": round(connect_s, 3),
           "seconds": round(wall, 3), "posts": len(done),
           "post_per_s": round(len(done) / wall, 3), "window_posts_per_10s": windows,
           "latency": m.summary(lat) if lat else None, "reader_articles": rcount[0],
           "owner_cpu_s": round(owner.cpu() - c0, 3), "n_before": n0, "n_after": state["count"],
           "errors": errors[:5]}
    row["owner_cpu_ms_per_post"] = round(1000.0 * row["owner_cpu_s"] / max(1, len(done)), 3)
    return row


def latency_rows(owner, author_probes, state, d, k, lock, rows, write):
    c0 = owner.cpu()

    def greet(_):
        t0 = time.perf_counter()
        c = m.Conn(owner.port)
        dt = time.perf_counter() - t0
        if not c.greeting.startswith(b"20"):
            raise SystemExit("greeting %r" % c.greeting)
        c.close()
        return dt
    rows["greeting"] = dict(timed_rows(greet, k), owner_cpu_s=round(owner.cpu() - c0, 3))
    write()
    c = m.Conn(owner.port)
    group = c.line("GROUP %s" % GROUP).decode("ascii", "replace").strip()
    rows["group_reply"] = group
    first, last = int(group.split()[2]), int(group.split()[3])
    for name, width in (("over40", 40), ("over100", 100)):
        span = max(1, last - first + 1 - width)
        starts = [first + (i * span) // max(1, k - 1) for i in range(k)]
        octets = [0]
        c0 = owner.cpu()

        def over(i):
            dt, reply, got = r.timed_multiline(c, "OVER %d-%d" % (starts[i], starts[i] + width - 1))
            if not reply.startswith(b"224"):
                raise SystemExit("OVER %r" % reply)
            octets[0] += got
            return dt
        rows[name] = dict(timed_rows(over, k), width=width, octets_read=octets[0],
                          owner_cpu_s=round(owner.cpu() - c0, 3))
        write()
    c.close()
    for name, samples in (("post", None), ("signed", author_probes)):
        c = m.Conn(owner.port)
        c0 = owner.cpu()
        whole, term = [], []
        started = time.monotonic()
        for i in range(len(samples) if samples else k):
            if len(whole) >= 5 and time.monotonic() - started > ROW_BUDGET[0]:
                break
            with lock:
                j = state["count"]
                state["count"] = j + 1
            if samples:
                w, t = sc.post_octets(c, samples[i])
                state["signed"] += 1
            else:
                w, t = sc.post_octets(c, r.article(j, state["octets"]))
            whole.append(w)
            term.append(t)
        c.close()
        cpu = owner.cpu() - c0
        wanted = len(samples) if samples else k
        rows[name] = {"n": len(whole), "command_to_reply": m.summary(whole),
                      "capped": None if len(whole) == wanted else "%d of %d samples within %.0f s"
                      % (len(whole), wanted, ROW_BUDGET[0]),
                      "terminator_to_reply": m.summary(term),
                      "owner_cpu_ms_per_post": round(1000.0 * cpu / max(1, len(whole)), 3),
                      "octets": len(samples[0]) if samples else len(r.article(0, state["octets"]))}
        save_state(d, state)
        write()
    rows["memory_after_latency_rows"] = owner.memory()


STEPS = ("load", "latency", "restart", "rate", "checkpoint")


def measure(a):
    image, d, env = Path(a.image).resolve(), Path(a.dir), image_env()
    steps = a.steps.split(",")
    if any(s not in STEPS for s in steps) or ("load" in steps) != (a.load_to is not None):
        raise SystemExit("--steps from %s; load exactly when --load-to" % ",".join(STEPS))
    deadline = time.monotonic() + a.budget
    fresh = not (d / "state.json").exists()
    state = init_dir(image, d, env, a.octets, a.signed_every) if fresh else load_state(d)
    import throughput_gate as tg
    out = {"schema": 1, "label": a.label, "revision": a.revision, "image": str(image),
           "core_sha256": m.digest(str(image) + ".core"), "launcher_sha256": m.digest(image),
           "client_sha256": {f: m.digest(ROOT / f) for f in ("tools/service_envelope.py", "tools/signed_carriers.py",
                                                            "tools/rep_measure.py", "tools/msgid_measure.py")},
           "host": os.uname().nodename, "unit": tg.own_unit(), "steps": steps,
           "profile": state["profile"], "init_args": state["init_args"], "store_dir": str(d),
           "filesystem": filesystem(d), "n_at_start": state["count"], "signed_every": state["signed_every"],
           "article_octets": state["octets"], "groups_per_article": 1, "pins": 0, "relay_debt": 0,
           "loaded_by_core_sha256": state["core_sha256"], "cloned_from": state.get("cloned_from"),
           "offered_load": "one sequential client for the latency rows; closed loop for the rate rows",
           "not_exposed": {"bytes_consed": "needs the heap-hook image (rep_measure.py --heap-dir)",
                           "mutex_held_fraction": "the owner exposes no mutex accounting"},
           "samples": a.samples, "started_utc": now(), "rows": {}, "opens": []}
    rows, path = out["rows"], Path(a.json)
    ROW_BUDGET[0] = float(a.row_budget)
    out["row_budget_s"] = a.row_budget

    def write():
        out["n"], out["signed_in_history"] = state["count"], state["signed"]
        out["written_utc"] = now()
        path.write_text(json.dumps(out, indent=2) + "\n")
    out["disk_before"] = disk(d)
    write()
    sampler = tg.LoadSampler()
    sampler.thread.start()
    author = sc.HybridAuthor.existing(image, env, d / "author")
    lock = threading.Lock()
    owner, after = None, "stop"
    code = 0
    try:
        for step in steps:
            if step in ("restart", "checkpoint") and owner is not None:
                owner.stop()
                owner = None
                save_state(d, state)
            if step == "checkpoint":
                t0 = time.perf_counter()
                ck = subprocess.run([str(image), "--fn", "operator", str(write_config(d, 1)), "store", "checkpoint"],
                                    env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                rows["checkpoint"] = {"seconds": round(time.perf_counter() - t0, 3), "rc": ck.returncode,
                                      "n": state["count"], "out": ck.stdout.decode("ascii", "replace")[-400:]}
                write()
                if ck.returncode:
                    code = 5
                    break
                after = "checkpoint"
                continue
            probes = []
            if step == "latency":
                probes = [author.sign("senv-probe-%s-%d-%d" % (a.label, state["count"], i), state["octets"])
                          for i in range(a.signed_samples)]
            if owner is None:
                n_open = state["count"]
                try:
                    owner = Owner(image, d, env, "%s-%d" % (a.label, len(out["opens"])), a.open_timeout)
                except AssertionError as e:
                    out["opens"].append({"n": n_open, "after": after, "ran": False,
                                         "why": "no LISTENING within %d s: %s" % (a.open_timeout, str(e)[:300])})
                    code = 4
                    break
                out["opens"].append({"n": n_open, "after": after, "mode": owner.mode,
                                     "seconds": round(owner.open_s, 3),
                                     "owner_cpu_s": round(owner.cpu(), 3), "memory": owner.memory()})
                write()
            if step == "load":
                rows.setdefault("load", []).append(load_into(owner, author, d, state, a.load_to, deadline,
                                                             a.session_posts))
                if state["count"] < a.load_to:
                    code = 75
                    break
            elif step == "latency":
                latency_rows(owner, probes, state, d, a.samples, lock, rows, write)
            elif step == "rate":
                for name, conns in (("rate1", 1), ("rate%d" % a.connections, a.connections)):
                    rows[name] = rate_phase(owner, state, lock, conns, a.rate_seconds, a.readers, state["octets"])
                    save_state(d, state)
                    write()
                rows["memory_after_rate"] = owner.memory()
            write()
    finally:
        if owner is not None:
            owner.stop()
        save_state(d, state)
        sampler.stop.set()
        sampler.thread.join()
        out["box_load"] = sampler.summary()
        out["disk_after"] = disk(d)
        out["finished_utc"] = now()
        out["exit"] = code
        write()
    print(json.dumps(summary_rows(out), indent=1))
    return code


def summary_rows(out):
    rows = out.get("rows", {})

    def p95(row, key=None):
        if not row:
            return None
        return round((row[key] if key else row)["p95_ms"], 3)
    hwm = [o.get("memory", {}).get("hwm_kib") or 0 for o in out.get("opens", [])]
    hwm += [(rows.get(k) or {}).get("hwm_kib") or 0 for k in ("memory_after_latency_rows", "memory_after_rate")]
    return {"n_at_start": out.get("n_at_start"), "n": out.get("n"),
            "filesystem": out.get("filesystem", {}).get("type"),
            "opens": [(o.get("n"), o.get("after"), o.get("mode"), o.get("seconds")) for o in out.get("opens", [])],
            "greeting_p95_ms": p95(rows.get("greeting")), "over40_p95_ms": p95(rows.get("over40")),
            "over100_p95_ms": p95(rows.get("over100")),
            "post_p95_ms": p95(rows.get("post"), "terminator_to_reply"),
            "signed_p95_ms": p95(rows.get("signed"), "terminator_to_reply"),
            "rates_post_per_s": {k: v.get("post_per_s") for k, v in rows.items() if k.startswith("rate")
                                 and isinstance(v, dict)},
            "checkpoint_s": (rows.get("checkpoint") or {}).get("seconds"), "peak_rss_kib": max(hwm or [0])}


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    lo = sub.add_parser("load")
    lo.add_argument("--image", required=True)
    lo.add_argument("--dir", required=True)
    lo.add_argument("--to", type=int, required=True)
    lo.add_argument("--octets", type=int, default=2048)
    lo.add_argument("--signed-every", type=int, default=256)
    lo.add_argument("--budget", type=int, default=1500, help="seconds of loading before a clean stop")
    lo.add_argument("--open-timeout", type=int, default=1200)
    cl = sub.add_parser("clone")
    cl.add_argument("--dir", required=True)
    cl.add_argument("--to-dir", required=True)
    cl.add_argument("--drop-checkpoint", action="store_true",
                    help="remove the copy's derived state checkpoint, so its first open is the full replay")
    me = sub.add_parser("measure")
    me.add_argument("--image", required=True)
    me.add_argument("--dir", required=True)
    me.add_argument("--json", required=True)
    me.add_argument("--label", required=True)
    me.add_argument("--revision", required=True)
    me.add_argument("--steps", default="latency,restart,rate,checkpoint,restart",
                    help="in order, from " + ",".join(STEPS) + "; an owner starts when a step needs one "
                         "(each start is an `opens` row: on a loaded store, the reopen)")
    me.add_argument("--load-to", type=int, default=None)
    me.add_argument("--octets", type=int, default=2048, help="a fresh DIR only")
    me.add_argument("--signed-every", type=int, default=256, help="a fresh DIR only")
    me.add_argument("--budget", type=int, default=1500, help="seconds the load step may spend")
    me.add_argument("--session-posts", type=int, default=None,
                    help="at most this many preload POSTs per owner process (then exit 75: the next unit resumes)")
    me.add_argument("--samples", type=int, default=100)
    me.add_argument("--signed-samples", type=int, default=50)
    me.add_argument("--rate-seconds", type=int, default=60)
    me.add_argument("--connections", type=int, default=8)
    me.add_argument("--readers", type=int, default=3)
    me.add_argument("--open-timeout", type=int, default=1200)
    me.add_argument("--row-budget", type=int, default=120,
                    help="seconds one latency row may take; past it (and 5 samples) the row is capped and says so")
    a = p.parse_args(argv)
    return {"load": load, "clone": clone, "measure": measure}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
