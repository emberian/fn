#!/usr/bin/env python3
"""The power-loss campaign: cut power to the block device under a committing
node, at recorded write boundaries, and check what the store keeps
(lane power-loss, 2026-09-26; planning/evidence/power-loss-2026-09-26.md).

The native crash campaign (tests/campaign/native_cuts.py) kills the PROCESS
at every named cut; the kernel's page cache survives it.  This one loses the
page cache and every write the device had not flushed.  It runs on hbox
(Linux, root through `sudo -n` for the block layer only; the node and the
client run as the invoking user):

  rig      /dev/shm/... data and log images on loop devices, dm-log-writes
           over them (Linux device-mapper: every write the file system sends
           the device, every flush and FUA, in completion order; the
           fstests generic/455 pattern), ext4 on the mapped device, mounted.
  workload the node's store on that mount: `operator CONFIG init`, `operator
           CONFIG run`, POSTs on connections of CONN posts; after every `240`
           the client writes a MARK into the log (`dmsetup message ... mark
           ack-I`).  A mark is queued behind every write whose completion the
           kernel had seen, and the POST's durable reply follows its fsyncs'
           flushes, so every write the acknowledged commit depended on is
           logged before its mark.  Midway the owner stops and `store
           compact` runs between marks; the owner restarts and posting goes
           on (the scale profile with a small open suffix, so the owner's
           automatic checkpoint capture runs concurrently with the POSTs);
           at the end the reference is read (ARTICLE of every Message-ID
           through a fresh owner), `retention set released-by-all-holders`
           and `store reclaim` run between marks, and the reclaimed
           reference is read.  Last, `store export` writes the archive to
           the same file system and `store import` publishes it as a second
           store beside the first (phase `import': fn-bs-imp-program; the
           `init' phase is fn-bs-init-pub-program, see publication_phases).
  index    the log device parsed (dm-log-writes' on-disk format: a super
           sector, then per entry a sector of {sector, nr_sectors, flags,
           data_len} and the data); the full replay must equal the data
           device byte for byte, or the rig's reading of the format is wrong
           and nothing is run.
  cuts     for each cut position P (an entry index): the device is the
           replay of every entry up to the last flush at or before P, every
           FUA write up to P, and, per the cut's mode, none (`flush`), all
           (`prefix`) or a seeded random subset (`subset`) of the other
           writes after that flush (completed but unflushed: a volatile
           cache may hold any of them).  The image is mounted (ext4 replays
           its journal), unmounted, `e2fsck -fn`, mounted again; then
           `operator CONFIG recover`, the owner, the ORACLE, `status`.

The ORACLE, for the Message-IDs attempted before P's phase ended:
  - acknowledged (its ack mark precedes P): ARTICLE answers the reference
    octets exactly (reply line with its article number, headers, body);
    in the reclaim phase, the reference or the reclaimed reference;
  - not acknowledged: the reference octets (committed, reply lost) or 430;
  - recover exits 0, the owner reaches LISTENING, status exits 0;
  - compact and reclaim cuts: a rerun of the verb exits 0 (or 1 with
    already-compact / nothing to reclaim) and a second owner answers the
    same.
Any other answer is a violation, recorded with the cut's position, mode,
seed and the kept write set; the log is kept.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import re
import shutil
import signal
import struct
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT))

MAGIC = 0x6A736677736872
FLUSH, FUA, DISCARD, MARK, METADATA = 1, 2, 4, 8, 16
GROUP = "fn.test"
DM = "fn-power-loss"
CKPT = re.compile(rb"CHECKPOINT auto sequence=(\d+)")


# The publication programs' phases (lane import-publication, PKT-647): the
# campaign config the `cuts' plan names (`init=N,import=N').  A block-level
# cut is a device position, not a process cut, so each record names the
# program whose window it fell in and that program's named cuts (the native
# kill campaign's, tests/campaign/native_cuts.py) with the oracle below.
def publication_phases():
    from tests.campaign import native_cuts
    return {
        "init": {"program": "fn-bs-init-pub-program",
                 "book": "books/store-init-publication.lisp",
                 "cuts": [c.name for c in native_cuts.INIT_PUB_CUTS],
                 "oracle": "ROOT absent (at most one ROOT.init-*, which the next "
                           "init names as interrupted-init; init succeeds once it "
                           "is removed) or ROOT the complete empty store (recover "
                           "0, status transactions=0)"},
        "import": {"program": "fn-bs-imp-program",
                   "book": "books/store-import-publication.lisp",
                   "cuts": [c.name for c in native_cuts.IMPORT_CUTS],
                   "oracle": "the source store keeps its reference; ROOT2 absent "
                             "(at most one ROOT2.import-*, which the next import "
                             "names as interrupted-import; import succeeds once it "
                             "is removed) or ROOT2 the complete imported store "
                             "(status 0, the source's transactions=N, every "
                             "sampled Message-ID's store inspect equal)"},
    }


def sh(*argv, check=True, **kw):
    return subprocess.run([str(a) for a in argv], check=check, **kw)


def sudo(*argv, check=True, **kw):
    return sh("sudo", "-n", *argv, check=check, **kw)


def out_line(path, **rec):
    rec["t"] = round(time.time(), 3)
    with open(path, "a") as f:
        f.write(json.dumps(rec, sort_keys=True) + "\n")
        f.flush()


# ---------------------------------------------------------------------------
# The rig.

def rig_up(work, data_mib, log_mib, mount_opts=""):
    work.mkdir(parents=True, exist_ok=True)
    data, log = work / "data.img", work / "log.img"
    for p, mib in ((data, data_mib), (log, log_mib)):
        if p.exists():
            p.unlink()
        sh("truncate", "-s", "%dM" % mib, p)
    sudo("modprobe", "dm-log-writes")
    dloop = sudo("losetup", "--show", "-f", data, stdout=subprocess.PIPE, text=True).stdout.strip()
    lloop = sudo("losetup", "--show", "-f", log, stdout=subprocess.PIPE, text=True).stdout.strip()
    sectors = sudo("blockdev", "--getsz", dloop, stdout=subprocess.PIPE, text=True).stdout.strip()
    sudo("dmsetup", "create", DM, "--table", "0 %s log-writes %s %s" % (sectors, dloop, lloop))
    dm = os.path.basename(os.path.realpath("/dev/mapper/" + DM))
    wc = Path("/sys/block/%s/queue/write_cache" % dm).read_text().strip()
    fua = Path("/sys/block/%s/queue/fua" % dm).read_text().strip()
    if wc != "write back":
        raise SystemExit("the mapped device is %r: flushes would be dropped" % wc)
    mark("mkfs-begin")
    sudo("mkfs.ext4", "-q", "-F", "/dev/mapper/" + DM)
    mark("mkfs-end")
    mnt = work / "mnt"
    mnt.mkdir(exist_ok=True)
    sudo("mount", "-t", "ext4", *(["-o", mount_opts] if mount_opts else []), "/dev/mapper/" + DM, mnt)
    sudo("chown", "%d:%d" % (os.getuid(), os.getgid()), mnt)
    mark("mounted")
    rig = {"data": str(data), "log": str(log), "data_loop": dloop, "log_loop": lloop,
           "dm": dm, "write_cache": wc, "fua": fua, "sectors": int(sectors), "mnt": str(mnt),
           "kernel": os.uname().release, "mount_opts": mount_opts,
           "mount": [l for l in Path("/proc/mounts").read_text().splitlines() if str(mnt) in l]}
    (work / "rig.json").write_text(json.dumps(rig, indent=1))
    return rig


def mark(text):
    sudo("dmsetup", "message", DM, "0", "mark", text)


def rig_down(work):
    rig = json.loads((work / "rig.json").read_text())
    sudo("umount", rig["mnt"], check=False)
    sudo("dmsetup", "remove", DM, check=False)
    sudo("losetup", "-d", rig["data_loop"], rig["log_loop"], check=False)
    sudo("chown", "%d:%d" % (os.getuid(), os.getgid()), rig["data"], rig["log"], check=False)


# ---------------------------------------------------------------------------
# The workload.

def config_for(work, store, port):
    cfg = work / "fn.toml"
    cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                   '[control]\npath = "%s"\n' % (store, port, work / "c.sock"), encoding="ascii")
    return cfg


def config2_for(work, store, port):
    cfg = work / "fn2.toml"
    cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                   '[control]\npath = "%s"\n' % (store, port, work / "c2.sock"), encoding="ascii")
    return cfg


def native(image, *argv, timeout=1800):
    r = subprocess.run([str(image), "--fn"] + [str(a) for a in argv], stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, timeout=timeout)
    return r.returncode, r.stdout.decode("utf-8", "replace"), r.stderr.decode("utf-8", "replace")


def start_owner(image, cfg, stderr_path, timeout=600):
    from tests.native_process import wait_for_announcement
    err = open(stderr_path, "ab")
    p = subprocess.Popen([str(image), "--fn", "operator", str(cfg), "run"],
                         stdout=subprocess.PIPE, stderr=err)
    try:
        wait_for_announcement(p, b"LISTENING ", timeout=timeout)
    except BaseException:
        p.kill()
        p.wait()
        err.close()
        raise
    return p, err


def stop_owner(p, err):
    p.send_signal(signal.SIGTERM)
    try:
        code = p.wait(timeout=600)
    except subprocess.TimeoutExpired:
        p.kill()
        code = p.wait()
    err.close()
    return code


def article_bytes(i, octets):
    import rep_measure as r
    return r.article(i, octets)


def msgid(i):
    import msgid_measure as m
    return m.msgid(i)


def read_article(c, mid):
    """The full answer to ARTICLE: the reply line and, for a 220, every line
    through the terminating dot."""
    first = c.line("ARTICLE " + mid)
    lines = [first]
    if first.startswith(b"220"):
        while True:
            l = c.readline()
            if not l:
                raise ConnectionError("closed inside ARTICLE " + mid)
            lines.append(l)
            if l == b".\r\n":
                break
    return b"".join(lines)


def read_all(port, n):
    import msgid_measure as m
    c = m.Conn(port)
    try:
        return [read_article(c, msgid(i)) for i in range(n)]
    finally:
        c.close()


def workload(a):
    import msgid_measure as m
    work = Path(a.work)
    rig = json.loads((work / "rig.json").read_text())
    store = Path(rig["mnt"]) / "store"
    port = m.free_port()
    cfg = config_for(work, store, port)
    log = work / "workload.jsonl"
    image = a.image
    init = ["--profile", "scale", "--max-transactions", "1048576", "--max-article-octets", "4096",
            "--max-open-suffix", str(a.open_suffix)]
    if a.history_octets:
        init += ["--max-groups-per-article", "16", "--max-record-octets", "262144", "--max-history-octets", str(a.history_octets)]
    init.append(GROUP)
    mark("phase:init")
    code, so, se = native(image, "operator", cfg, "init", *init)
    out_line(log, tag="init", exit=code, stdout=so[-400:], stderr=se[-400:], argv=init)
    if code:
        raise SystemExit("init failed")
    rng = random.Random(a.seed)
    sizes = [rng.choice(a.octets) for _ in range(a.posts)]
    # A known pre-publication refusal: every REFUSE_EVERY-th POST names only
    # a group this node does not carry (441 unknown-group, decided before
    # anything is published).  An over-size article would do too, but the
    # node closes the connection after it (it stops reading the body).
    refuse = {i for i in range(a.posts)
              if a.refuse_every and i % a.refuse_every == a.refuse_every // 2}
    attempted = 0

    import threading
    log_lock = threading.Lock()

    def post_range(lo, hi, errname):
        if a.posters > 1:
            return post_range_concurrent(lo, hi, errname)
        nonlocal attempted
        p, err = start_owner(image, cfg, work / errname)
        seen = 0
        try:
            i = lo
            while i < hi:
                mark("conn")
                c = m.Conn(port)
                for _ in range(a.conn):
                    if i >= hi:
                        break
                    attempted = i + 1
                    out_line(log, tag="attempt", i=i)
                    r = c.line("POST")
                    if not r.startswith(b"340"):
                        raise SystemExit("POST %d: %r" % (i, r))
                    art = article_bytes(i, sizes[i])
                    if i in refuse:
                        art = art.replace(b"Newsgroups: fn.test", b"Newsgroups: fn.not-carried")
                    c.stream.write(art + b".\r\n")
                    r = c.readline()
                    if r.startswith(b"240"):
                        mark("ack-%d" % i)
                        out_line(log, tag="ack", i=i)
                    elif r.startswith(b"441") or r.startswith(b"437"):
                        # A refusal the client knows: never acceptance later.
                        mark("refuse-%d" % i)
                        out_line(log, tag="refuse", i=i, reply=r.decode("ascii", "replace").strip())
                        i += 1
                        break                      # a fresh connection after a refusal
                    else:
                        raise SystemExit("POST %d body: %r" % (i, r))
                    now = CKPT.findall((work / errname).read_bytes())
                    if len(now) > seen:
                        mark("ckpt-seen-%s" % now[-1].decode())
                        out_line(log, tag="ckpt-seen", i=i, lines=[x.decode() for x in now[seen:]])
                        seen = len(now)
                    i += 1
                c.close()
        finally:
            out_line(log, tag="owner-stop", exit=stop_owner(p, err))

    def post_range_concurrent(lo, hi, errname):
        """POSTERS threads, thread t posting lo+t, lo+t+POSTERS, ...; each
        marks and logs after its own reply, under one lock (the mark follows
        the 240, as the sequential client's does)."""
        nonlocal attempted
        p, err = start_owner(image, cfg, work / errname)
        errors = []

        def poster(t):
            nonlocal attempted
            try:
                c = m.Conn(port)
                for i in range(lo + t, hi, a.posters):
                    with log_lock:
                        attempted = max(attempted, i + 1)
                        out_line(log, tag="attempt", i=i)
                    r = c.line("POST")
                    if not r.startswith(b"340"):
                        raise SystemExit("POST %d: %r" % (i, r))
                    art = article_bytes(i, sizes[i])
                    if i in refuse:
                        art = art.replace(b"Newsgroups: fn.test", b"Newsgroups: fn.not-carried")
                    c.stream.write(art + b".\r\n")
                    r = c.readline()
                    with log_lock:
                        if r.startswith(b"240"):
                            mark("ack-%d" % i)
                            out_line(log, tag="ack", i=i)
                        elif r.startswith(b"441") or r.startswith(b"437"):
                            mark("refuse-%d" % i)
                            out_line(log, tag="refuse", i=i, reply=r.decode("ascii", "replace").strip())
                        else:
                            raise SystemExit("POST %d body: %r" % (i, r))
                c.close()
            except BaseException as e:  # noqa: BLE001 - reported below
                errors.append(repr(e))
        try:
            mark("conn")
            ts = [threading.Thread(target=poster, args=(t,)) for t in range(a.posters)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            if errors:
                raise SystemExit("posters: %s" % errors[:3])
        finally:
            out_line(log, tag="owner-stop", exit=stop_owner(p, err))

    if a.log_route:
        # Three posting windows with a restart between them (each open
        # recovers the log: P-LOG-RECOVER's zeroing and fence); then the
        # reference.  No compact, reclaim or export: refused by name.
        bounds = [0, a.posts // 2, (3 * a.posts) // 4, a.posts]
        for k in range(3):
            mark("phase:post")
            post_range(bounds[k], bounds[k + 1], "owner-%d.stderr" % (k + 1))
        mark("phase:reference")
        p, err = start_owner(image, cfg, work / "owner-ref.stderr")
        try:
            ref = read_all(port, a.posts)
            c = m.Conn(port)
            ref_over = read_overview(c)
            c.close()
        finally:
            stop_owner(p, err)
        code, so, se = native(image, "operator", cfg, "status")
        out_line(log, tag="status", exit=code, stdout=so, stderr=se[-400:])
        mark("phase:end")
        refdir = work / "reference"
        refdir.mkdir(exist_ok=True)
        (refdir / "ref.json").write_text(json.dumps([x.decode("latin-1") for x in ref]))
        (refdir / "ref2.json").write_text(json.dumps([x.decode("latin-1") for x in ref]))
        (refdir / "over.json").write_text(json.dumps({mid: n for n, mid in ref_over}))
        out_line(log, tag="done", posts=a.posts, attempted=attempted, sizes=sizes, checkpoints=[],
                 ref_220=sum(1 for x in ref if x.startswith(b"220")), ref2_220=None,
                 ref2_heads=[], store_path=str(store), port=port, log_route=True,
                 posters=a.posters)
        return

    # Two compactions: the first packs the history, the second packs it again
    # with the records since (on this image: a new pack generation, the
    # selection moving from generation 0 to 1).
    bounds = [0, a.posts // 2, (3 * a.posts) // 4, a.posts]
    for k in range(3):
        mark("phase:post")
        post_range(bounds[k], bounds[k + 1], "owner-%d.stderr" % (k + 1))
        if k < 2:
            mark("phase:compact")
            t0 = time.time()
            code, so, se = native(image, "operator", cfg, "store", "compact")
            out_line(log, tag="compact", exit=code, stdout=so[-400:], stderr=se[-400:],
                     wall=round(time.time() - t0, 2))
    mark("phase:reference")
    p, err = start_owner(image, cfg, work / "owner-ref.stderr")
    try:
        ref = read_all(port, a.posts)
        c = m.Conn(port)
        ref_over = read_overview(c)
        c.close()
    finally:
        stop_owner(p, err)
    mark("phase:retention")
    code, so, se = native(image, "operator", cfg, "retention", "set", "released-by-all-holders")
    out_line(log, tag="retention", exit=code, stdout=so[-400:], stderr=se[-400:])
    mark("phase:reclaim")
    code, so, se = native(image, "operator", cfg, "store", "reclaim")
    out_line(log, tag="reclaim", exit=code, stdout=so[-400:], stderr=se[-400:])
    mark("phase:reference-reclaimed")
    p, err = start_owner(image, cfg, work / "owner-ref2.stderr")
    try:
        ref2 = read_all(port, a.posts)
    finally:
        stop_owner(p, err)
    code, so, se = native(image, "operator", cfg, "status")
    out_line(log, tag="status", exit=code, stdout=so, stderr=se[-400:])
    # The import publication (fn-bs-imp-program): export the store to the
    # same device, then import it as a second store beside the first.
    mark("phase:export")
    archive = Path(rig["mnt"]) / "archive"
    code, so, se = native(image, "operator", cfg, "store", "export", archive)
    out_line(log, tag="export", exit=code, stdout=so[-400:], stderr=se[-400:])
    if code:
        raise SystemExit("export failed")
    cfg2 = config2_for(work, Path(rig["mnt"]) / "store2", m.free_port())
    mark("phase:import")
    code, so, se = native(image, "operator", cfg2, "store", "import", archive)
    out_line(log, tag="import", exit=code, stdout=so[-400:], stderr=se[-400:])
    if code:
        raise SystemExit("import failed")
    mark("phase:end")
    refdir = work / "reference"
    refdir.mkdir(exist_ok=True)
    (refdir / "ref.json").write_text(json.dumps([x.decode("latin-1") for x in ref]))
    (refdir / "ref2.json").write_text(json.dumps([x.decode("latin-1") for x in ref2]))
    (refdir / "over.json").write_text(json.dumps({mid: n for n, mid in ref_over}))
    ckpt = [l for l in b"".join((work / f).read_bytes() for f in ("owner-1.stderr", "owner-2.stderr", "owner-3.stderr"))
            .decode("utf-8", "replace").splitlines() if "CHECKPOINT" in l]
    out_line(log, tag="done", posts=a.posts, attempted=attempted, sizes=sizes, checkpoints=ckpt,
             ref_220=sum(1 for x in ref if x.startswith(b"220")),
             ref2_220=sum(1 for x in ref2 if x.startswith(b"220")),
             ref2_heads=sorted(set(x.split(b"\r\n")[0][:3].decode() for x in ref2)),
             store_path=str(store), port=port)


# ---------------------------------------------------------------------------
# The log.

def parse_log(path):
    """Entries of a dm-log-writes log: (index, sector, nr_sectors, flags,
    data_offset, mark_text).  Sector and nr_sectors are in the log's
    sectorsize units (the data device's logical block size)."""
    entries = []
    with open(path, "rb") as f:
        sup = f.read(32)
        magic, version, nr, ss = struct.unpack("<QQQI", sup[:28])
        if magic != MAGIC:
            raise SystemExit("not a dm-log-writes log (magic %x)" % magic)
        pos = ss
        for idx in range(nr):
            f.seek(pos)
            hdr = f.read(ss)
            sector, nrs, flags, dlen = struct.unpack("<QQQQ", hdr[:32])
            text = hdr[32:32 + dlen].decode("latin-1") if flags & MARK else None
            pos += ss
            data_off = pos
            if not flags & DISCARD:
                pos += nrs * ss
            entries.append((idx, sector, nrs, flags, data_off, text))
    return {"version": version, "nr_entries": nr, "sectorsize": ss, "entries": entries}


def apply_entry(logf, dev, e, ss):
    _, sector, nrs, flags, off, _ = e
    if flags & MARK or nrs == 0:
        return
    if flags & DISCARD:
        dev.seek(sector * ss)
        dev.write(b"\0" * (nrs * ss))
        return
    logf.seek(off)
    dev.seek(sector * ss)
    dev.write(logf.read(nrs * ss))


def index(a):
    work = Path(a.work)
    rig = json.loads((work / "rig.json").read_text())
    L = parse_log(rig["log"])
    ss = L["sectorsize"]
    ents = L["entries"]
    marks = [(e[0], e[5]) for e in ents if e[3] & MARK]
    counts = {"writes": sum(1 for e in ents if not e[3] & (MARK | DISCARD) and e[2]),
              "flush": sum(1 for e in ents if e[3] & FLUSH),
              "fua": sum(1 for e in ents if e[3] & FUA),
              "discard": sum(1 for e in ents if e[3] & DISCARD),
              "marks": len(marks)}
    # Self-check: the full replay equals the data device.
    replay = work / "replay-full.img"
    shutil.copyfile(work / "zero.img", replay) if (work / "zero.img").exists() else sh(
        "truncate", "-s", str(os.path.getsize(rig["data"])), replay)
    with open(rig["log"], "rb") as lf, open(replay, "r+b") as dev:
        for e in ents:
            apply_entry(lf, dev, e, ss)
    same = sh("cmp", "-s", replay, rig["data"], check=False).returncode == 0
    replay.unlink()
    doc = {"version": L["version"], "nr_entries": L["nr_entries"], "sectorsize": ss,
           "counts": counts, "full_replay_equals_device": same, "marks": marks,
           "log_sha256": file_sha(rig["log"]), "data_sha256": file_sha(rig["data"])}
    (work / "index.json").write_text(json.dumps(doc))
    print(json.dumps({k: v for k, v in doc.items() if k != "marks"}, indent=1))
    if not same:
        raise SystemExit("the full replay differs from the device: the parser is wrong")


def file_sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 22), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# The cuts.

def phase_windows(marks, nr):
    """[(phase, first_entry, end_entry)] from the phase marks."""
    ph = [(i, t.split(":", 1)[1]) for i, t in marks if t.startswith("phase:")]
    wins = []
    for k, (i, name) in enumerate(ph):
        end = ph[k + 1][0] if k + 1 < len(ph) else nr
        wins.append((name, i, end))
    return wins


# flush: nothing after the last flush; prefix: every logged write before the
# cut; subset: each unflushed write kept or lost whole; torn: each unflushed
# write kept 4096-octet block by block (a device that persists a multi-block
# write partly).  FUA writes before the cut are always kept.
MODES = ("flush", "flush", "prefix", "subset", "subset", "torn", "torn")
TORN_BLOCK = 4096


def checkpoint_windows(marks):
    """The automatic capture's windows: from the last connection's accept
    (the owner decides to publish between accepts) before a `ckpt-seen'
    mark to that mark."""
    wins, last_conn = [], None
    for i, t in marks:
        if t == "conn":
            last_conn = i
        elif t.startswith("ckpt-seen") and last_conn is not None:
            wins.append(("checkpoint", last_conn, i))
    return wins


def choose_cuts(ents, marks, plan, seed):
    """Cut positions per phase: each is an entry index P (the device holds
    what was durable just before entry P is written... see module doc); the
    choice is uniform over the phase's write entries, so busy windows (the
    checkpoint's file, the pack) are cut in proportion to their writes."""
    rng = random.Random(seed)
    wins = phase_windows(marks, len(ents)) + checkpoint_windows(marks)
    cand = {}
    for name, lo, hi in wins:
        cand.setdefault(name, []).extend(e[0] for e in ents[lo:hi] if not e[3] & MARK)
    cuts = []
    for name in sorted(cand):
        want = plan.get(name, 0)
        pool = sorted(set(cand[name]))
        if not pool or not want:
            continue
        for p in sorted(rng.sample(pool, min(want, len(pool)))):
            cuts.append((p, name, rng.choice(MODES), rng.randrange(1 << 30)))
    cuts.sort()
    return cuts


def build_image(ents, logf, base, base_upto, cut, mode, seed, ss, img):
    """Advance BASE (a file holding the replay of entries [0, base_upto)) to
    the last flush before CUT, copy it to IMG and apply the tail by MODE.
    Returns (new base_upto, tail description)."""
    last_flush = base_upto
    for e in ents[base_upto:cut]:
        if e[3] & FLUSH:
            last_flush = e[0] + 1
    if last_flush > base_upto:
        with open(base, "r+b") as dev:
            for e in ents[base_upto:last_flush]:
                apply_entry(logf, dev, e, ss)
        base_upto = last_flush
    shutil.copyfile(base, img)
    rng = random.Random(seed)
    tail = [e for e in ents[base_upto:cut] if not e[3] & MARK and e[2]]
    kept = []
    for e in tail:
        if e[3] & FUA or mode == "prefix" or (mode == "subset" and rng.random() < 0.5):
            kept.append(e[0])
    keep = set(kept)
    torn = {}
    if mode == "torn":
        for e in tail:
            if e[0] in keep or e[3] & FUA:
                continue
            nblk = max(1, (e[2] * ss) // TORN_BLOCK)
            sel = [b for b in range(nblk) if rng.random() < 0.5]
            if sel:
                torn[e[0]] = sel
    with open(img, "r+b") as dev:
        for e in tail:
            if e[0] in keep:
                apply_entry(logf, dev, e, ss)
            elif e[0] in torn:
                logf.seek(e[4])
                data = logf.read(e[2] * ss)
                for b in torn[e[0]]:
                    dev.seek(e[1] * ss + b * TORN_BLOCK)
                    dev.write(data[b * TORN_BLOCK:(b + 1) * TORN_BLOCK])
    kept = kept + ["%d:%s" % (k, ",".join(map(str, v))) for k, v in sorted(torn.items())]
    return base_upto, {"durable_upto": base_upto, "tail": len(tail), "kept": kept}


def cuts(a):
    import msgid_measure as m
    work = Path(a.work)
    rig = json.loads((work / "rig.json").read_text())
    idx = json.loads((work / "index.json").read_text())
    L = parse_log(rig["log"])
    ents, ss = L["entries"], L["sectorsize"]
    marks = [tuple(x) for x in idx["marks"]]
    wl = [json.loads(l) for l in (work / "workload.jsonl").read_text().splitlines()]
    done = [r for r in wl if r["tag"] == "done"][0]
    posts = done["posts"]
    ref = [x.encode("latin-1") for x in json.loads((work / "reference" / "ref.json").read_text())]
    ref2 = [x.encode("latin-1") for x in json.loads((work / "reference" / "ref2.json").read_text())]
    over = work / "reference" / "over.json"
    if over.exists():
        REF_OVER.update(json.loads(over.read_text()))
    ack_at, refuse_at = {}, {}
    for i, t in marks:
        if t.startswith("ack-"):
            ack_at[int(t[4:])] = i
        elif t.startswith("refuse-"):
            refuse_at[int(t[7:])] = i
    plan = dict(x.split("=") for x in a.plan.split(","))
    plan = {k: int(v) for k, v in plan.items()}
    chosen = choose_cuts(ents, marks, {k: v for k, v in plan.items() if k != "control"}, a.seed)
    # The rig's teeth: a control cut is the device just after post I's ack
    # mark (flush mode), judged as if post I+1 were acknowledged too.  Post
    # I+1's writes all follow that mark (the client sends it after marking I),
    # so the oracle MUST report it absent; a control with no violation means
    # the oracle cannot see a lost acknowledged POST.
    crng = random.Random(a.seed + 1)
    post_wins = [(lo, hi) for name, lo, hi in phase_windows(marks, len(ents)) if name == "post"]
    ackable = [(at, i) for i, at in ack_at.items()
               if i + 1 in ack_at and any(lo <= at < hi and lo <= ack_at[i + 1] < hi for lo, hi in post_wins)]
    controls = {}
    for at, i in crng.sample(sorted(ackable), min(plan.get("control", 0), len(ackable))):
        controls[at + 1] = i + 1
        chosen.append((at + 1, "control", "flush", crng.randrange(1 << 30)))
    chosen.sort()
    if a.limit:
        chosen = chosen[:a.limit]
    results = work / ("cuts-%s.jsonl" % a.label)
    seen = set()
    if results.exists():
        seen = {json.loads(l)["cut"] for l in results.read_text().splitlines()}
    base = work / "base.img"
    sh("truncate", "-s", "0", base)
    sh("truncate", "-s", str(os.path.getsize(rig["data"])), base)
    base_upto = 0
    img = work / "cut.img"
    mnt = Path(rig["mnt"])
    store = Path(done["store_path"])
    port = done["port"]
    cfg = work / "fn.toml"
    image = a.image
    logf = open(rig["log"], "rb")
    print("cuts planned: %d" % len(chosen), flush=True)
    ctx = {"image": image, "cfg": cfg, "port": port, "work": work, "ref": ref, "ref2": ref2,
           "mnt": mnt, "store": store, "rig": rig}
    rrng = random.Random(a.seed + 2)
    for n, (cut, phase, mode, seed) in enumerate(chosen):
        base_upto, tail = build_image(ents, logf, base, base_upto, cut, mode, seed, ss, img)
        if cut in seen:
            continue
        acked = sorted(i for i, at in ack_at.items() if at < cut)
        refused = sorted(i for i, at in refuse_at.items() if at < cut)
        if phase == "control":
            acked.append(controls[cut])
        rec = {"cut": cut, "phase": phase, "mode": mode, "seed": seed, "acked": len(acked),
               "refused": len(refused),
               "durable_upto": tail["durable_upto"], "tail": tail["tail"], "kept": len(tail["kept"])}
        # The attempted bound: every i whose attempt could have begun by the
        # cut: the last answered + 1 (one POST in flight), never past the run.
        answered = acked + refused
        # With POSTERS concurrent clients up to POSTERS POSTs are in flight
        # past the last answered one.
        attempted = min(posts, (max(answered) + 1 + a.posters) if answered else a.posters)
        if phase in ("reference", "retention", "reclaim", "reference-reclaimed", "end",
                     "export", "import"):
            attempted = posts
        violations = []
        if phase == "recover-crash" or (a.recover_crash and rrng.random() < a.recover_crash
                                        and phase not in ("control", "init")):
            # Interrupted recovery followed by another crash: this cut's image
            # recovers under a second dm-log-writes device, and power is cut
            # again at a write of that recovery.
            rec["first_phase"], rec["phase"] = phase, "recover-crash"
            rec["second"] = second_cut(ctx, img, rrng, violations)
            phase = "recover-crash:" + phase
        if not violations:
            evaluate(ctx, img, rec, phase.split(":")[-1], acked, refused, attempted, violations)
        rec["violations"] = violations
        if phase == "control":
            rec["control_caught"] = bool(violations)
        elif violations:
            keep = work / "violations" / ("cut-%d" % cut)
            keep.mkdir(parents=True, exist_ok=True)
            # The image is not kept (1 GiB each): the log, the cut position,
            # the mode and the seed rebuild it (build_image is deterministic).
            (keep / "tail.json").write_text(json.dumps(dict(tail, cut=cut, mode=mode, seed=seed)))
        out_line(results, **rec)
        print("%d/%d cut=%d %s %s acked=%d v=%s" % (n + 1, len(chosen), cut, rec["phase"], mode,
                                                     len(acked), violations[:4]), flush=True)
    logf.close()


def evaluate(ctx, img, rec, phase, acked, refused, attempted, violations):
    mnt, store = ctx["mnt"], ctx["store"]
    loop = sudo("losetup", "--show", "-f", img, stdout=subprocess.PIPE, text=True).stdout.strip()
    try:
        r = sudo("mount", "-t", "ext4", loop, mnt, check=False, stderr=subprocess.PIPE, text=True)
        if r.returncode:
            rec["fs"] = "mount-failed: " + r.stderr[-300:]
            violations.append("fs-mount")
            return
        sudo("umount", mnt)
        fsck = sudo("e2fsck", "-fn", loop, check=False, stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT, text=True)
        rec["e2fsck"] = fsck.returncode
        if fsck.returncode:
            rec["e2fsck_out"] = fsck.stdout[-600:]
        sudo("mount", "-t", "ext4", loop, mnt)
        # The rig's own chown of the mount point may not have been durable
        # at an early cut; the node runs as this user either way.
        sudo("chown", "%d:%d" % (os.getuid(), os.getgid()), mnt)
        if phase in publication_phases():
            rec["program"] = publication_phases()[phase]["program"]
        if phase == "init":
            rec.update(check_init(ctx, violations))
            return
        if phase == "import":
            rec.update(check_import(ctx, violations))
        if not store.exists():
            rec["store"] = "absent"
            if acked:
                violations.append("store-absent-with-acks")
            return
        rec.update(check_store(ctx["image"], ctx["cfg"], ctx["port"], ctx["work"], phase, acked,
                               attempted, ctx["ref"], ctx["ref2"], violations, refused))
    except Exception as e:  # a harness failure is not a verdict
        rec["harness_error"] = repr(e)[-400:]
    finally:
        sudo("umount", mnt, check=False, stderr=subprocess.DEVNULL)
        sudo("losetup", "-d", loop, check=False)


def stages_beside(root, kind):
    return sorted(p for p in root.parent.iterdir() if p.name.startswith(root.name + "." + kind + "-"))


def check_init(ctx, violations):
    """A cut during `init` (fn-bs-init-pub-program): nothing was
    acknowledged.  The keystone: ROOT is absent or the complete empty store.
    Absent: at most one ROOT.init-*, which the next `init` names
    (interrupted-init) and after whose removal `init` succeeds; present: it
    opens (`recover` 0, `status` transactions=0) and no staged directory
    remains unless the rename's source removal did not land (then the next
    init refuses STORE-EXISTS, never a second store)."""
    image, cfg, root = ctx["image"], ctx["cfg"], ctx["store"]
    stages = stages_beside(root, "init")
    rec = {"store": "present" if root.exists() else "absent", "stages": len(stages)}
    if root.exists():
        code, so, se = native(image, "operator", cfg, "recover")
        rec["recover"], rec["recover_out"] = code, (so + se).strip()[-300:]
        code2, so2, se2 = native(image, "operator", cfg, "status")
        rec["status"] = code2
        if code or code2 or "transactions=0" not in so2:
            violations.append("init-partial-store:recover-%d:status-%d" % (code, code2))
        return rec
    if len(stages) > 1:
        violations.append("init-stages-%d" % len(stages))
        return rec
    code, so, se = native(image, "operator", cfg, "init", "--profile", "scale", GROUP)
    rec["reinit"], rec["reinit_out"] = code, (so + se).strip()[-300:]
    if stages:
        want = "reason=interrupted-init stage=%s" % stages[0]
        if code != 1 or want not in so + se:
            violations.append("init-leftover-not-named:init-%d" % code)
            return rec
        shutil.rmtree(stages[0])
        code, so, se = native(image, "operator", cfg, "init", "--profile", "scale", GROUP)
        rec["init_after_removal"] = code
    if code:
        violations.append("init-stuck:init-%d" % code)
        return rec
    code, so, se = native(image, "operator", cfg, "recover")
    rec["recover_after_init"] = code
    if code:
        violations.append("init-unopenable:recover-%d" % code)
    return rec


def check_import(ctx, violations):
    """A cut during `store import` (fn-bs-imp-program) onto ROOT2: ROOT2 is
    absent (at most one ROOT2.import-*, named by the next import, which
    succeeds once it is removed) or the complete imported store: it opens,
    `status` reports the source's transactions=N, and sampled Message-IDs'
    `store inspect` answers equal the source's.  The source store is checked
    by check_store as in the `end' phase."""
    image, cfg, work = ctx["image"], ctx["cfg"], ctx["work"]
    cfg2 = work / "fn2.toml"
    root2 = ctx["store"].parent / "store2"
    archive = ctx["store"].parent / "archive"
    stages = stages_beside(root2, "import")
    rec = {"store2": "present" if root2.exists() else "absent", "stages2": len(stages)}
    if not root2.exists():
        if len(stages) > 1:
            violations.append("import-stages-%d" % len(stages))
            return rec
        code, so, se = native(image, "operator", cfg2, "store", "import", archive)
        rec["reimport"], rec["reimport_out"] = code, (so + se).strip()[-300:]
        if stages:
            want = "reason=interrupted-import stage=%s" % stages[0]
            if code != 1 or want not in so + se:
                violations.append("import-leftover-not-named:import-%d" % code)
                return rec
            shutil.rmtree(stages[0])
            code, so, se = native(image, "operator", cfg2, "store", "import", archive)
            rec["import_after_removal"] = code
        if code:
            violations.append("import-stuck:import-%d" % code)
            return rec
    code, so, se = native(image, "operator", cfg, "status")
    code2, so2, se2 = native(image, "operator", cfg2, "status")
    rec["status2"] = code2
    count = re.search(r"transactions=(\d+)", so)
    count2 = re.search(r"transactions=(\d+)", so2)
    if code2 or not count or not count2 or count.group(1) != count2.group(1):
        violations.append("import-incomplete:status-%d" % code2)
        return rec
    rng = random.Random(len(so2))
    for i in sorted(rng.sample(range(len(ctx["ref"])), min(8, len(ctx["ref"])))):
        a = native(image, "operator", cfg, "store", "inspect", msgid(i))
        b = native(image, "operator", cfg2, "store", "inspect", msgid(i))
        if a[:2] != b[:2]:
            violations.append("import-inspect-differs:%d" % i)
            break
    return rec


def second_cut(ctx, img, rng, violations):
    """Run recovery (`operator recover`, then the owner's own open) on IMG
    under a second log-writes device, then rebuild IMG as a power cut at a
    random write of that recovery (random mode).  Returns the record."""
    work, mnt, image, cfg = ctx["work"], ctx["mnt"], ctx["image"], ctx["cfg"]
    orig = work / "second-orig.img"
    shutil.copyfile(img, orig)
    log2 = work / "second-log.img"
    sh("truncate", "-s", "0", log2)
    sh("truncate", "-s", "4G", log2)
    d = sudo("losetup", "--show", "-f", img, stdout=subprocess.PIPE, text=True).stdout.strip()
    l = sudo("losetup", "--show", "-f", log2, stdout=subprocess.PIPE, text=True).stdout.strip()
    rec = {}
    try:
        sectors = sudo("blockdev", "--getsz", d, stdout=subprocess.PIPE, text=True).stdout.strip()
        sudo("dmsetup", "create", DM + "-2", "--table", "0 %s log-writes %s %s" % (sectors, d, l))
        try:
            sudo("dmsetup", "message", DM + "-2", "0", "mark", "second-begin")
            r = sudo("mount", "-t", "ext4", "/dev/mapper/" + DM + "-2", mnt, check=False,
                     stderr=subprocess.PIPE, text=True)
            if r.returncode:
                rec["mount"] = r.stderr[-200:]
            elif ctx["store"].exists():
                code, so, se = native(image, "operator", cfg, "recover")
                rec["recover1"] = [code, (so + se).strip()[-200:]]
                try:
                    p, err = start_owner(image, cfg, work / "second-owner.stderr", timeout=300)
                    stop_owner(p, err)
                except Exception as e:
                    rec["owner1"] = repr(e)[-200:]
            sudo("umount", mnt, check=False, stderr=subprocess.DEVNULL)
        finally:
            sudo("dmsetup", "remove", DM + "-2", check=False)
    finally:
        sudo("losetup", "-d", d, l, check=False)
    sudo("chown", "%d:%d" % (os.getuid(), os.getgid()), log2, check=False)
    L2 = parse_log(log2)
    ents2 = L2["entries"]
    writes = [e[0] for e in ents2 if not e[3] & MARK and e[2]]
    rec["second_writes"] = len(writes)
    if not writes:
        shutil.copyfile(orig, img)
        return rec
    cut2 = rng.choice(writes) + rng.choice((0, 1))
    mode2 = rng.choice(MODES)
    seed2 = rng.randrange(1 << 30)
    with open(log2, "rb") as lf:
        _, tail2 = build_image(ents2, lf, orig, 0, cut2, mode2, seed2, L2["sectorsize"], img)
    rec.update({"cut2": cut2, "mode2": mode2, "seed2": seed2, "durable_upto2": tail2["durable_upto"],
                "tail2": tail2["tail"], "kept2": len(tail2["kept"])})
    return rec


def check_store(image, cfg, port, work, phase, acked, attempted, ref, ref2, violations, refused=()):
    rec = {}
    acked_set = set(acked)
    code, so, se = native(image, "operator", cfg, "recover")
    rec["recover"] = code
    rec["recover_out"] = (so + se).strip()[-300:]
    if code:
        violations.append("recover-exit-%d" % code)
    refused_set = set(refused)
    inflight = [i for i in range(attempted) if i not in acked_set and i not in refused_set]
    rec["inspect"] = {}
    for i in inflight:
        code, so, se = native(image, "operator", cfg, "store", "inspect", msgid(i))
        rec["inspect"][i] = [code, so.split(" ")[0] if so else se.strip()[-120:]]
    try:
        p, err = start_owner(image, cfg, work / "cut-owner.stderr", timeout=300)
    except Exception as e:
        violations.append("owner-no-listening")
        rec["owner"] = repr(e)[-300:]
        return rec
    try:
        got = read_all(port, attempted)
        rec["binding"] = bindings(port, got, acked, violations, attempted)
    finally:
        rec["owner_stop"] = stop_owner(p, err)
    rec.update(classify(got, phase, acked_set, ref, ref2, violations))
    for i in refused:
        if not got[i].startswith(b"430"):
            violations.append("refused-became-accepted:%d:%r" % (i, got[i][:40]))
    # The in-flight POST: `store inspect' (the store's own lookup) and the
    # served answer must agree: accepted (0) with a 220, absent (1) with 430.
    for i, (code, word) in rec["inspect"].items():
        served = got[i].startswith(b"220")
        if not ((code == 0 and word == "accepted" and served) or
                (code == 1 and word == "absent" and got[i].startswith(b"430"))):
            if phase not in ("reclaim", "reference-reclaimed", "end", "export", "import"):
                violations.append("inflight-unclassified:%d:%s:%s:%r" % (i, code, word, got[i][:40]))
    code, so, se = native(image, "operator", cfg, "status")
    rec["status"] = code
    rec["status_lines"] = [l for l in so.splitlines() if l.split() and l.split()[0] in
                           ("transactions", "pack-chain", "checkpoint", "headroom")]
    if code:
        violations.append("status-exit-%d" % code)
    # Outstanding retention work never disappears: every committed article
    # is reclaimable, held or reclaimed (the status line's three counts).
    counts = dict(re.findall(r"\b(articles|reclaimable|held|reclaimed)=(\d+)", so))
    rule = re.search(r"reclaim rule=(\S+)", so)
    if rule and rule.group(1) != "keep-forever" and "reclaimed" in counts and "articles" in counts:
        total = sum(int(counts[k]) for k in ("reclaimable", "held", "reclaimed"))
        rec["reclaim_accounting"] = [int(counts["articles"]), total]
        if total != int(counts["articles"]):
            violations.append("reclaim-accounting:%s" % counts)
    if phase in ("compact", "reclaim"):
        verb = "compact" if phase == "compact" else "reclaim"
        code, so, se = native(image, "operator", cfg, "store", verb)
        rec["rerun"] = [code, (so + se).strip()[-300:]]
        if code not in (0, 1) or (code == 1 and not re.search(r"already|nothing|no ", so + se)):
            violations.append("rerun-%s-exit-%d" % (verb, code))
        try:
            p, err = start_owner(image, cfg, work / "cut-owner2.stderr", timeout=300)
            try:
                got2 = read_all(port, attempted)
            finally:
                stop_owner(p, err)
            v2 = []
            rec["after_rerun"] = classify(got2, phase, acked_set, ref, ref2, v2)
            violations.extend("after-rerun:" + v for v in v2)
            if phase == "reclaim":
                diff = [i for i in range(attempted) if got2[i] != ref2[i]]
                if diff:
                    violations.append("reclaim-rerun-not-reference:%s" % diff[:5])
        except Exception as e:
            violations.append("owner2-no-listening")
            rec["owner2"] = repr(e)[-300:]
    return rec


REF_OVER = {}   # Message-ID -> local number in the uncut run (reference/over.json)


def read_overview(c):
    """(number, Message-ID) of every article GROUP/OVER lists (ARTICLE by
    Message-ID answers "220 0 <id>", RFC 3977 6.2.1.2, so the local number
    comes from the overview)."""
    r = c.line("GROUP " + GROUP)
    if not r.startswith(b"211"):
        return []
    r = c.line("OVER 1-")
    rows = []
    if r.startswith(b"224"):
        while True:
            l = c.readline()
            if not l or l == b".\r\n":
                break
            f = l.rstrip(b"\r\n").split(b"\t")
            if len(f) > 4 and f[0].isdigit():
                rows.append((int(f[0]), f[4].decode("latin-1")))
    return rows


def bindings(port, got, acked, violations, attempted=0):
    """Identity and number stability after the cut: the newest acknowledged
    Message-ID is refused if posted again (its binding survived), and a fresh
    article takes a local number above every number the recovered store
    serves (no allocated number is handed out twice)."""
    import msgid_measure as m
    c = m.Conn(port)
    rec = {}
    try:
        over = read_overview(c)
        nums = [n for n, _ in over]
        # Every number an acknowledged article ever held stays allocated,
        # reclaimed (unlisted) or not.
        held = nums + [REF_OVER[msgid(i)] for i in acked if msgid(i) in REF_OVER]
        rec["max_served"] = max(held) if held else 0
        rec["listed"] = len(over)
        if len(set(nums)) != len(nums):
            violations.append("number-shared")
        moved = [(mid, n, REF_OVER[mid]) for n, mid in over if mid in REF_OVER and REF_OVER[mid] != n]
        if moved:
            violations.append("number-changed:%s" % moved[:3])
        if acked:
            i = max(acked)
            r = c.line("POST")
            if r.startswith(b"340"):
                c.stream.write(article_bytes(i, 700) + b".\r\n")
                r = c.readline()
            rec["repost"] = r.decode("ascii", "replace").strip()
            if r.startswith(b"240"):
                violations.append("acked-id-rebound:%d" % i)
        fresh = "<pl-fresh-%d@power-loss.invalid>" % time.time_ns()
        art = article_bytes(0, 700).replace(msgid(0).encode(), fresh.encode())
        r = c.line("POST")
        if r.startswith(b"340"):
            c.stream.write(art + b".\r\n")
            r = c.readline()
        rec["fresh"] = r.decode("ascii", "replace").strip()
        if r.startswith(b"240"):
            after = dict((mid, n) for n, mid in read_overview(c))
            fn_ = after.get(fresh)
            rec["fresh_number"] = fn_
            if fn_ is None or fn_ <= rec["max_served"]:
                violations.append("number-reassigned:%s<=%d" % (fn_, rec["max_served"]))
            served_ids = {mid for _, mid in over}
            tried = {msgid(i) for i in range(attempted)}
            lost = [mid for mid, n in REF_OVER.items()
                    if n == fn_ and mid in tried and mid not in served_ids]
            if lost:
                # A lost unacknowledged POST's number, observed, not judged.
                rec["fresh_took_lost_number"] = lost[0]
    finally:
        c.close()
    return rec


def classify(got, phase, acked, ref, ref2, violations):
    """Acked: the reference octets (the reclaimed reference once the reclaim
    completed; either during it).  Unacked: those, or 430."""
    if phase in ("reference-reclaimed", "end"):
        allowed = lambda i, g: g == ref2[i]
    elif phase == "reclaim":
        allowed = lambda i, g: g == ref[i] or g == ref2[i]
    else:
        allowed = lambda i, g: g == ref[i]
    c = {"served_ref": 0, "served_reclaimed": 0, "absent": 0, "other": 0}
    for i, g in enumerate(got):
        if allowed(i, g):
            c["served_ref" if g == ref[i] else "served_reclaimed"] += 1
        elif g.startswith(b"430") and i not in acked:
            c["absent"] += 1
        else:
            c["other"] += 1
            violations.append("%s-mismatch:%d:%r" % ("acked" if i in acked else "unacked", i, g[:60]))
    return c


def summary(paths):
    """One row per campaign and phase: cuts, violations (controls apart),
    the in-flight outcomes, refusals checked, bindings checked, second cuts,
    file-system and harness counts.  The record's tables are this output."""
    import collections
    rows = []
    for path in paths:
        name = Path(path).parent.name
        by = collections.OrderedDict()
        for line in Path(path).read_text().splitlines():
            r = json.loads(line)
            c = by.setdefault(r["phase"], collections.Counter())
            c["cuts"] += 1
            c[r["mode"]] += 1
            if r["phase"] == "control":
                c["controls_caught"] += bool(r.get("control_caught"))
            elif r["violations"]:
                c["violations"] += 1
            c["acked_checked"] += r.get("acked", 0) if "served_ref" in r else 0
            c["refused_checked"] += r.get("refused", 0) if "served_ref" in r else 0
            for code, word in (r.get("inspect") or {}).values():
                c["inflight_committed" if code == 0 else "inflight_absent"] += 1
            b = r.get("binding") or {}
            if "fresh" in b:
                c["bindings_checked"] += 1
            if r.get("second", {}).get("second_writes"):
                c["second_cuts"] += 1
            c["e2fsck_nonzero"] += bool(r.get("e2fsck"))
            c["harness_error"] += bool(r.get("harness_error"))
        for ph, c in by.items():
            rows.append((name, ph, dict(c)))
    cols = ["cuts", "violations", "controls_caught", "flush", "prefix", "subset", "torn",
            "acked_checked", "refused_checked", "inflight_committed", "inflight_absent",
            "bindings_checked", "second_cuts", "e2fsck_nonzero", "harness_error"]
    print("| campaign | phase | " + " | ".join(cols) + " |")
    print("| --- | --- | " + " | ".join("---:" for _ in cols) + " |")
    tot = collections.Counter()
    for name, ph, c in rows:
        print("| %s | %s | %s |" % (name, ph, " | ".join(str(c.get(k, 0)) for k in cols)))
        tot.update(c)
    print("| all | all | %s |" % " | ".join(str(tot.get(k, 0)) for k in cols))


# ---------------------------------------------------------------------------
# The record log's workload (lane w6-log-core; books/store-log-programs.lisp,
# host/native/io.lisp fnn-log-*).  The developer image's `fn log append`
# recovers the segment (fn-lg-recover-program) and appends batches of PER
# workload records, each written (fn-lg-append-program: one positioned write
# at the frontier) and fenced (fn-lg-fence-program: fdatasync on the
# preallocated segment); it prints one `ACK' line after each fence, and the
# client marks the device then (`logack-N', N the records acknowledged).
# Three runs: append (it creates the segment), a bare `fn log recover` of the
# populated segment, append again; each run's recovery lies between the
# marks `rec-begin-K' and `rec-end-K'.  A cut position is named by its window
# (LOG_CUTS, tests/campaign/native_cuts.py): in a batch window, `log-written'
# before the window's first flush (the batch's write may be torn) and
# `log-fenced' after it; in a recovery window, `log-truncated' before its
# last flush and `log-recovered' after it (run 1's window also holds the
# segment's creation and preallocation).
#
# The ORACLE, outside the device (the client's own record of the ACK lines):
# the image is mounted (journal replay), unmounted, `e2fsck -fn`, mounted;
# `fn log recover` exits 0 and reads R records that are the workload records
# 1..R (`workload=t', ACL2's check), next txid R + 1, every octet of the
# segment past the frontier zero; `fn log scan` then reads the same line.
# R >= the records acknowledged before the cut (ACKED) and R <= ACKED + PER
# (at most the batch in flight); in a recovery window R = the records the
# previous run acknowledged (recovery changes no record).  A control cut (the
# rig's teeth) is the device just after `logack-N' judged as if the next
# batch were acknowledged too: the oracle must report it.

LOG_LINE = re.compile(r"^(\S+)(?: batch=\d+)? records=(\d+) frontier=(\d+) next=(\d+) "
                      r"last=([0-9a-f]+) workload=(t|nil)$")
LOG_UNIT, LOG_MAX = 4096, 65536


def log_segment(rig):
    return Path(rig["mnt"]) / "log" / "segment"


def log_argv(seg, extent, size):
    return [str(seg), str(extent), str(LOG_UNIT), str(LOG_MAX), str(size)]


def log_parse(text):
    out = []
    for line in text.splitlines():
        m = LOG_LINE.match(line.strip())
        if m:
            out.append({"what": m.group(1), "records": int(m.group(2)),
                        "frontier": int(m.group(3)), "next": int(m.group(4)),
                        "workload": m.group(6) == "t"})
    return out


def log_run(image, argv, k, wl):
    """One `fn log` process; mark the device at its RECOVERED and ACK lines."""
    mark("rec-begin-%d" % k)
    p = subprocess.Popen([str(image), "--fn", "log"] + argv, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True)
    last = None
    for text in p.stdout:
        (line,) = log_parse(text) or [None]
        if line is None:
            continue
        if line["what"] == "RECOVERED":
            mark("rec-end-%d" % k)
        elif line["what"] == "ACK":
            mark("logack-%d" % line["records"])
        out_line(wl, tag="line", run=k, **line)
        last = line
    rc = p.wait()
    err = p.stderr.read()
    out_line(wl, tag="exit", run=k, rc=rc, stderr=err[-400:])
    if rc != 0:
        raise SystemExit("fn log %s exited %d: %s" % (argv[0], rc, err[-400:]))
    return last


def log_workload(a):
    work = Path(a.work)
    rig = json.loads((work / "rig.json").read_text())
    seg = log_segment(rig)
    seg.parent.mkdir(exist_ok=True)
    wl = work / "workload.jsonl"
    if wl.exists():
        wl.unlink()
    mark("phase:log")
    base = log_argv(seg, a.extent, a.size)
    r1 = log_run(a.image, ["append"] + base + [str(a.batches), str(a.per)], 1, wl)
    r2 = log_run(a.image, ["recover"] + base, 2, wl)
    r3 = log_run(a.image, ["append"] + base + [str(a.batches), str(a.per)], 3, wl)
    mark("log-done")
    out_line(wl, tag="done", extent=a.extent, size=a.size, per=a.per, batches=a.batches,
             records=r3["records"], segment=str(seg))
    if not (r1["records"] == r2["records"] == a.batches * a.per
            and r3["records"] == 2 * a.batches * a.per):
        raise SystemExit("workload counts wrong: %r %r %r" % (r1, r2, r3))
    print(json.dumps({"records": r3["records"], "frontier": r3["frontier"]}))


def log_windows(ents, marks):
    """[(name, lo, hi, acked_before, recovery)] over the entry indices."""
    order = [(i, t) for i, t in marks
             if t.startswith(("rec-begin-", "rec-end-", "logack-")) or t == "log-done"]
    wins, acked = [], 0
    for (i, t), (j, u) in zip(order, order[1:]):
        if t.startswith("rec-begin-"):
            wins.append(("recovery", i, j, acked))
        else:
            if t.startswith("logack-"):
                acked = int(t[len("logack-"):])
            if not u.startswith("rec-begin-"):
                wins.append(("batch", i, j, acked))
    return wins


def log_cut_name(ents, kind, lo, p, hi):
    flushes = [e[0] for e in ents[lo:hi] if e[3] & FLUSH]
    if kind == "batch":
        return "log-written" if not flushes or p <= flushes[0] else "log-fenced"
    return "log-recovered" if flushes and p > flushes[-1] else "log-truncated"


def log_cuts(a):
    work = Path(a.work)
    rig = json.loads((work / "rig.json").read_text())
    idx = json.loads((work / "index.json").read_text())
    L = parse_log(rig["log"])
    ents, ss = L["entries"], L["sectorsize"]
    marks = [tuple(x) for x in idx["marks"]]
    wl = [json.loads(l) for l in (work / "workload.jsonl").read_text().splitlines()]
    done = [r for r in wl if r["tag"] == "done"][0]
    per = done["per"]
    rng = random.Random(a.seed)
    chosen = []
    wins = log_windows(ents, marks)
    for kind, lo, hi, acked in wins:
        for e in ents[lo:hi]:
            if not e[3] & MARK:
                chosen.append((e[0], kind, lo, hi, acked))
    rng.shuffle(chosen)
    chosen = sorted(chosen[:a.count])
    # Controls: just after an ack mark, judged as if PER more were acknowledged.
    acks = [(i, int(t[len("logack-"):])) for i, t in marks if t.startswith("logack-")]
    controls = []
    for i, n in rng.sample(acks, min(a.controls, len(acks))):
        controls.append((i + 1, "control", i, i + 1, n + per))
    plan = sorted([(p, kind, lo, hi, acked,
                    "flush" if kind == "control" else rng.choice(MODES), rng.randrange(1 << 30))
                   for p, kind, lo, hi, acked in chosen + controls])
    results = work / ("log-cuts-%s.jsonl" % a.label)
    base = work / "base.img"
    sh("truncate", "-s", "0", base)
    sh("truncate", "-s", str(os.path.getsize(rig["data"])), base)
    base_upto, img = 0, work / "cut.img"
    logf = open(rig["log"], "rb")
    print("log cuts planned: %d (%d controls)" % (len(plan), len(controls)), flush=True)
    for n, (p, kind, lo, hi, acked, mode, seed) in enumerate(plan):
        base_upto, tail = build_image(ents, logf, base, base_upto, p, mode, seed, ss, img)
        name = "control" if kind == "control" else log_cut_name(ents, kind, lo, p, hi)
        rec = {"cut": p, "window": kind, "name": name, "mode": mode, "seed": seed,
               "acked": acked, "durable_upto": tail["durable_upto"], "tail": tail["tail"],
               "kept": len(tail["kept"])}
        violations = []
        log_evaluate(a.image, rig, img, rec, kind, acked, per, done, violations)
        rec["violations"] = violations
        if kind == "control":
            rec["control_caught"] = bool(violations)
        out_line(results, **rec)
        print("%d/%d cut=%d %s %s acked=%d R=%s v=%s" % (n + 1, len(plan), p, name, mode, acked,
                                                         rec.get("records"), violations[:3]),
              flush=True)
    logf.close()


def log_evaluate(image, rig, img, rec, kind, acked, per, done, violations):
    mnt = Path(rig["mnt"])
    seg = log_segment(rig)
    loop = sudo("losetup", "--show", "-f", img, stdout=subprocess.PIPE, text=True).stdout.strip()
    try:
        r = sudo("mount", "-t", "ext4", loop, mnt, check=False, stderr=subprocess.PIPE, text=True)
        if r.returncode:
            rec["fs"] = "mount-failed: " + r.stderr[-300:]
            violations.append("fs-mount")
            return
        sudo("umount", mnt)
        fsck = sudo("e2fsck", "-fn", loop, check=False, stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT, text=True)
        rec["e2fsck"] = fsck.returncode
        sudo("mount", "-t", "ext4", loop, mnt)
        sudo("chown", "%d:%d" % (os.getuid(), os.getgid()), mnt)
        if seg.parent.exists():
            sudo("chown", "-R", "%d:%d" % (os.getuid(), os.getgid()), seg.parent)
        else:
            seg.parent.mkdir()
        argv = log_argv(seg, done["extent"], done["size"])
        rr = subprocess.run([str(image), "--fn", "log", "recover"] + argv,
                            capture_output=True, text=True, timeout=600)
        rec["recover_rc"] = rr.returncode
        if rr.returncode != 0:
            violations.append("recover-exit-%d" % rr.returncode)
            rec["recover_err"] = rr.stderr[-400:]
            return
        (line,) = log_parse(rr.stdout)
        R = line["records"]
        rec.update(records=R, frontier=line["frontier"])
        if not line["workload"]:
            violations.append("not-the-workload-records")
        if line["next"] != R + 1:
            violations.append("next-txid")
        if R < acked:
            violations.append("acknowledged-lost")
        if kind == "batch" and R > acked + per:
            violations.append("more-than-attempted")
        if kind == "recovery" and R != acked:
            violations.append("recovery-changed-records")
        data = seg.read_bytes()
        if len(data) != done["extent"] or any(data[line["frontier"]:]):
            violations.append("tail-not-zero")
        ss = subprocess.run([str(image), "--fn", "log", "scan"] + argv,
                            capture_output=True, text=True, timeout=600)
        if ss.returncode != 0 or [(l["records"], l["frontier"]) for l in log_parse(ss.stdout)] \
                != [(R, line["frontier"])]:
            violations.append("scan-differs")
    except Exception as e:  # a harness failure is not a verdict
        rec["harness_error"] = repr(e)[-400:]
    finally:
        sudo("umount", mnt, check=False, stderr=subprocess.DEVNULL)
        sudo("losetup", "-d", loop, check=False)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("rig-up")
    r.add_argument("work")
    r.add_argument("--data-mib", type=int, default=1024)
    r.add_argument("--log-mib", type=int, default=16384)
    r.add_argument("--mount-opts", default="",
                   help="ext4 options for the workload's mount (the cuts mount with the defaults)")
    r = sub.add_parser("rig-down")
    r.add_argument("work")
    w = sub.add_parser("workload")
    w.add_argument("work")
    w.add_argument("--image", required=True)
    w.add_argument("--posts", type=int, default=400)
    w.add_argument("--conn", type=int, default=10)
    w.add_argument("--open-suffix", type=int, default=64)
    w.add_argument("--octets", type=lambda s: [int(x) for x in s.split(",")], default=[2048])
    w.add_argument("--seed", type=int, default=1)
    w.add_argument("--history-octets", type=int, default=0, help="a near-full store's bound")
    w.add_argument("--refuse-every", type=int, default=0)
    # Lane commit-onto-log: a format-9 store (the record log).  Its compact,
    # reclaim and export are refused by name until w6-log-recovery (PKT-750),
    # so those phases are skipped; POSTERS concurrent connections post (the
    # owner commits them in batches), each client marking after its own 240.
    w.add_argument("--log-route", action="store_true")
    w.add_argument("--posters", type=int, default=1)
    i = sub.add_parser("index")
    i.add_argument("work")
    c = sub.add_parser("cuts")
    c.add_argument("work")
    c.add_argument("--image", required=True)
    c.add_argument("--plan", default="post=150,compact=30,reclaim=30,init=20,import=20")
    c.add_argument("--seed", type=int, default=7)
    c.add_argument("--label", default="main")
    c.add_argument("--limit", type=int, default=0)
    c.add_argument("--recover-crash", type=float, default=0.0,
                   help="the fraction of cuts whose recovery is itself cut")
    c.add_argument("--posters", type=int, default=1,
                   help="the workload's concurrent posters: POSTs in flight at a cut")
    lw = sub.add_parser("log-workload", help="the record log's workload (lane w6-log-core)")
    lw.add_argument("work")
    lw.add_argument("--image", required=True, help="the developer image")
    lw.add_argument("--extent", type=int, default=8 << 20)
    lw.add_argument("--size", type=int, default=600)
    lw.add_argument("--batches", type=int, default=150)
    lw.add_argument("--per", type=int, default=4)
    lc = sub.add_parser("log-cuts")
    lc.add_argument("work")
    lc.add_argument("--image", required=True)
    lc.add_argument("--count", type=int, default=240)
    lc.add_argument("--controls", type=int, default=10)
    lc.add_argument("--seed", type=int, default=7)
    lc.add_argument("--label", default="log")
    sm = sub.add_parser("summary")
    sm.add_argument("results", nargs="+", help="cuts-*.jsonl files")
    a = ap.parse_args(argv)
    global DM
    DM = "fn-power-loss-" + Path(getattr(a, "work", "x")).name   # one mapping per campaign
    if a.cmd == "rig-up":
        print(json.dumps(rig_up(Path(a.work), a.data_mib, a.log_mib, a.mount_opts), indent=1))
    elif a.cmd == "rig-down":
        rig_down(Path(a.work))
    elif a.cmd == "workload":
        workload(a)
    elif a.cmd == "index":
        index(a)
    elif a.cmd == "cuts":
        cuts(a)
    elif a.cmd == "log-workload":
        log_workload(a)
    elif a.cmd == "log-cuts":
        log_cuts(a)
    elif a.cmd == "summary":
        summary(a.results)


if __name__ == "__main__":
    main()
