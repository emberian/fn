#!/usr/bin/env python3
"""The content-reclamation lifecycle on the native image (STO-017, SCN-065).

    reclaim_lifecycle_native.py IMAGE WORK N BODY_OCTETS HISTORY_OCTETS [--cuts]

A Python client and harness only: every decision is the image's (ACL2's).
It builds a store of N articles through NNTP POST, then walks the lifecycle
and prints one JSON line per observation:

  keep-forever        `store reclaim' writes nothing (bounded, no release)
  release-after 1     `store reclaim --dry-run' reclaims nothing (too recent)
  released-by-all-holders
    dry-run           names every article, writes nothing
    compact + cuts    (--cuts) a copy per cut: kill (SIGSTOP then SIGKILL,
                      FN_CHECKPOINT_TEST_STOP) at every publication,
                      selection and retirement cut, kill and EIO at every
                      reclaim cut (FN_NATIVE_RECLAIM_FAULT); each copy
                      reopens (`status' exit 0), a rerun of `store reclaim'
                      exits 0, and the copy ends byte-identical to the clean
                      run's selected pack
    clean run           disk octets and inodes before and after, `status'
                      headroom before and after
  served              ARTICLE by id 430, by number 423, OVER 423, NEWNEWS
                      skips, GROUP unchanged, re-POST of the old article 441
  headroom            (HISTORY_OCTETS chosen tight) a POST refused before the
                      reclaim is accepted after it
"""
import hashlib, json, os, shutil, signal, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(HERE / "tools"))
import msgid_measure as m  # noqa: E402

image, work = sys.argv[1], Path(sys.argv[2])
N, BODY, HIST = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
CUTS = "--cuts" in sys.argv
ENV = dict(os.environ); ENV["ACL2_CUSTOMIZATION"] = "NONE"; ENV.pop("ACL2_SYSTEM_BOOKS", None)
GROUP = "fn.letters"


def out(**rec):
    print(json.dumps(rec), flush=True)


def native(*args, env=None, expected=None, timeout=3600):
    r = subprocess.run([image, "--fn", *map(str, args)], env=env or ENV,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    res = (r.returncode, r.stdout.decode(errors="replace"), r.stderr.decode(errors="replace"))
    if expected is not None and r.returncode != expected:
        raise SystemExit("native %r exit %d\n%s\n%s" % (args, r.returncode, res[1][-2000:], res[2][-2000:]))
    return res


def msgid(i):
    return "<rl-%06d@reclaim.example.invalid>" % i


def article(i, body=BODY):
    head = ("From: r@example.invalid\r\nNewsgroups: %s\r\nSubject: reclaim %d\r\n"
            "Date: Thu, 24 Sep 2026 12:00:00 +0000\r\nMessage-ID: %s\r\n\r\n"
            % (GROUP, i, msgid(i))).encode()
    line = b"y" * 62 + b"\r\n"
    return head + line * max(1, body // 64)


def config_for(store, name):
    port = m.free_port()
    cfg = work / (name + ".toml")
    cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                   '[control]\npath = "%s"\n' % (store, port, work / (name + ".sock")))
    return cfg, port


def owner(cfg):
    p = subprocess.Popen([image, "--fn", "operator", str(cfg), "run"], env=ENV,
                         stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    m.wait_for_announcement(p, b"LISTENING ", timeout=3600)
    return p


def stop(p):
    p.send_signal(signal.SIGTERM)
    p.wait(timeout=3600)


def post(c, i, body=BODY):
    r = c.line("POST")
    if not r.startswith(b"340"):
        return r
    c.stream.write(article(i, body) + b".\r\n")
    return c.readline()


def footprint(store):
    files = octets = 0
    for d, _, fs in os.walk(store):
        for f in fs:
            files += 1
            octets += os.lstat(os.path.join(d, f)).st_size
    du = subprocess.run(["du", "-sB1", str(store)], stdout=subprocess.PIPE).stdout.split()[0]
    return {"files": files, "octets": octets, "du": int(du)}


def status(cfg):
    code, so, se = native("operator", cfg, "status")
    lines = {l.split()[0]: l for l in so.splitlines() if l.split()}
    return code, lines.get("headroom", ""), lines.get("reclaim", ""), so


def selected_pack(store):
    """The content of every pack generation file present, by digest.  The
    generation number (the file name and the selection marker) is not
    compared: a rerun after a cut before the selection publishes the next
    number over the same bytes."""
    packs = Path(store) / "packs"
    if not packs.exists():
        return []
    files = [p for p in packs.iterdir() if p.is_file()]
    sizes = sorted((p.stat().st_size, p) for p in files)
    marker = sizes[0][1] if len(sizes) > 1 else None
    return sorted(hashlib.sha256(p.read_bytes()).hexdigest() for p in files if p != marker)


def build(name, n, body=BODY, hist=HIST):
    store = work / name
    cfg, port = config_for(store, name)
    flags = os.environ.get("RL_INIT_FLAGS", "--max-record-octets 262144 --max-article-octets 131072 --max-groups-per-article 16").split()
    native("operator", cfg, "init", *flags, "--max-history-octets", hist, GROUP, expected=0)
    p = owner(cfg)
    t0 = time.perf_counter(); refused = []
    try:
        c = m.Conn(port)
        for i in range(n):
            r = post(c, i, body)
            if not r.startswith(b"240"):
                refused.append((i, r.decode(errors="replace").strip()))
                break
        c.close()
    finally:
        stop(p)
    out(tag="built", name=name, n=n, posted=n - len(refused), refused=refused[:1],
        wall_s=round(time.perf_counter() - t0, 1))
    return store, cfg, port


def answer(c, text):
    first = c.line(text)
    if first[:3] in (b"220", b"221", b"222", b"224", b"225", b"230"):
        while c.readline() not in (b".\r\n", b""):
            pass
    return first.decode(errors="replace").strip()


def served(cfg, port, reclaimed_ids, first_number=1):
    p = owner(cfg)
    try:
        c = m.Conn(port)
        rec = {"group": c.line("GROUP " + GROUP).decode().strip()}
        rid = reclaimed_ids[0]
        rec["article_by_id"] = answer(c, "ARTICLE " + rid)
        rec["article_by_number"] = answer(c, "ARTICLE %d" % first_number)
        rec["over_number"] = answer(c, "OVER %d" % first_number)
        rec["stat_by_id"] = answer(c, "STAT " + rid)
        rec["article_live"] = answer(c, "STAT %d" % (first_number + 1))
        nn = c.line("NEWNEWS %s 20000101 000000 GMT" % GROUP)
        listed = []
        if nn.startswith(b"230"):
            while True:
                l = c.readline()
                if l == b".\r\n":
                    break
                listed.append(l.decode().strip())
        rec["newnews_head"] = nn.decode().strip()
        rec["newnews_lists_reclaimed"] = sum(1 for x in listed if x in set(reclaimed_ids))
        rec["newnews_listed"] = len(listed)
        idx = int(rid.split("-")[1].split("@")[0])
        rec["repost_same"] = post(c, idx).decode().strip()
        c.close()
    finally:
        stop(p)
    return rec


def run():
    work.mkdir(parents=True, exist_ok=True)
    store, cfg, port = build("base", N)
    ids = [msgid(i) for i in range(N)]
    # 1. The default keep-forever: nothing is released, nothing is written.
    code, so, se = native("operator", cfg, "store", "reclaim")
    out(tag="keep-forever", exit=code, stdout=so.strip()[-300:], stderr=se.strip()[-300:])
    # 2. release-after 1 day: every article is too recent.
    code, so, se = native("operator", cfg, "retention", "set", "release-after", "1")
    out(tag="retention-set", rule="release-after 1", exit=code, stderr=se.strip()[-300:])
    code, so, se = native("operator", cfg, "store", "reclaim", "--dry-run")
    out(tag="release-after-dry-run", exit=code, stdout=so.strip()[-300:])
    # 3. released-by-all-holders.
    code, so, se = native("operator", cfg, "retention", "set", "released-by-all-holders")
    out(tag="retention-set", rule="released-by-all-holders", exit=code, stderr=se.strip()[-300:])
    code, so, se = native("operator", cfg, "store", "reclaim", "--dry-run")
    out(tag="dry-run", exit=code, head=so.splitlines()[:1], stdout_lines=len(so.splitlines()))
    # Compact first (the ordinary verb), so the cut copies isolate reclaim.
    out(tag="before-compact", footprint=footprint(store))
    code, so, se = native("operator", cfg, "store", "compact")
    out(tag="compact", exit=code, stdout=so.strip()[-300:], stderr=se.strip()[-200:])
    before = footprint(store)
    sc, head_before, rec_before, _ = status(cfg)
    out(tag="before", footprint=before, status_exit=sc, headroom=head_before, reclaim=rec_before)
    if CUTS:
        cuts(store)
    t0 = time.perf_counter()
    code, so, se = native("operator", cfg, "store", "reclaim")
    out(tag="reclaim", exit=code, wall_s=round(time.perf_counter() - t0, 1),
        head=so.splitlines()[:1], stderr=se.strip()[-300:])
    after = footprint(store)
    sc, head_after, rec_after, _ = status(cfg)
    out(tag="after", footprint=after, status_exit=sc, headroom=head_after, reclaim=rec_after,
        freed_files=before["files"] - after["files"], freed_octets=before["octets"] - after["octets"])
    global CLEAN
    CLEAN = selected_pack(store)
    code, so, se = native("operator", cfg, "store", "reclaim")
    out(tag="rerun", exit=code, stdout=so.strip()[-200:], same_pack=selected_pack(store) == CLEAN)
    out(tag="served", **served(cfg, port, ids))
    headroom()


CLEAN = None
RECLAIM_CUTS = [("stop", "candidate-file"), ("stop", "candidate-link"),
                ("stop", "candidate-directory"), ("stop", "selection-file"),
                ("stop", "selection-replace"), ("stop", "selection-directory"),
                ("stop", "pack-retire-unlink"), ("stop", "pack-retire-directory")] + \
    [(a, c) for c in ("reclaim-state-checkpoint-unlink", "reclaim-state-checkpoint-directory",
                      "reclaim-pack-published", "reclaim-pack-selected", "reclaim-retired")
     for a in ("kill", "eio")]


def cuts(base):
    # The clean reference first, on its own copy.
    ref = work / "cut-ref"; shutil.rmtree(ref, ignore_errors=True); shutil.copytree(base, ref)
    rcfg, _ = config_for(ref, "cut-ref")
    native("operator", rcfg, "store", "reclaim", expected=0)
    reference = selected_pack(ref)
    for action, point in RECLAIM_CUTS:
        name = "cut-%s-%s" % (action, point)
        copy = work / name; shutil.rmtree(copy, ignore_errors=True); shutil.copytree(base, copy)
        ccfg, _ = config_for(copy, name)
        env = dict(ENV)
        if action == "stop":
            env["FN_CHECKPOINT_TEST_STOP"] = point
            p = subprocess.Popen([image, "--fn", "operator", str(ccfg), "store", "reclaim"],
                                 env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            stopped = False
            for _ in range(36000):
                st = open("/proc/%d/stat" % p.pid).read().split(")")[-1].split()[0]
                if st == "T":
                    stopped = True; break
                if p.poll() is not None:
                    break
                time.sleep(0.05)
            p.kill(); p.wait()
            first = "stopped" if stopped else "exit-%s" % p.returncode
        else:
            env["FN_NATIVE_RECLAIM_FAULT"] = "%s:%s" % (point, action)
            code, so, se = native("operator", ccfg, "store", "reclaim", env=env)
            first = "exit-%d" % code
        sc, _, rline, _ = status(ccfg)
        code, so, se = native("operator", ccfg, "store", "reclaim")
        final = selected_pack(copy)
        out(tag="cut", action=action, point=point, first=first, reopen_status=sc,
            reopen_reclaim=rline, rerun_exit=code, rerun_head=so.splitlines()[:1],
            converged=final == reference)
        shutil.rmtree(copy, ignore_errors=True)
    shutil.rmtree(ref, ignore_errors=True)


def headroom():
    # A tight history bound: fill to the first refused POST, reclaim, retry.
    n = int(os.environ.get("RL_HEADROOM_N", "400"))
    hist = int(os.environ.get("RL_HEADROOM_HIST", "300000"))
    store, cfg, port = build("tight", n, 1024, hist)
    native("operator", cfg, "retention", "set", "released-by-all-holders")
    _, h0, _, _ = status(cfg)
    p = owner(cfg)
    try:
        c = m.Conn(port); refused = post(c, 900001, 1024).decode().strip(); c.close()
    finally:
        stop(p)
    code, so, se = native("operator", cfg, "store", "compact")
    out(tag="tight-compact", exit=code, stdout=so.strip()[-200:], stderr=se.strip()[-300:])
    code, so, se = native("operator", cfg, "store", "reclaim")
    out(tag="tight-reclaim", exit=code, head=so.splitlines()[:2], stderr=se.strip()[-300:])
    _, h1, _, _ = status(cfg)
    p = owner(cfg)
    try:
        c = m.Conn(port); accepted = post(c, 900002, 1024).decode().strip(); c.close()
    finally:
        stop(p)
    out(tag="headroom", before=h0, refused_before=refused, after=h1, post_after=accepted)


if __name__ == "__main__":
    run()
