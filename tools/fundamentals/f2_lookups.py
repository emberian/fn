#!/usr/bin/env python3
"""F2's lookup count (lane sca-join-4; maintained here since lane join-f2,
tools/fundamentals.py's F2 judges its output): catalog and index lookups per served
command, on the served path the host calls, at a store of N articles.

A fresh default-profile store of N ~2 KiB articles in fn.test (loaded by
POST, as sr_measure.py loads it) is served by one `operator run` of IMAGE (a
DEVELOPER image) with FN_NATIVE_COUNT_LOOKUPS=1: the owner prints, at every
served read, `lookups window K: NAME=N ...`, the counts since the previous
read (host/native/io.lisp +fnn-lookup-functions+).  After the load settles,
each measured command is sent on one connection, its whole reply read, then
DATE: the window printed when DATE's read begins is the command's own work,
its render included.  Every command runs twice (the counts must agree), and
DATE alone once (the window of a command that reads nothing).

  f2_lookups.py --image build/fn-host-developer --work DIR --articles N --json OUT
  f2_lookups.py ... --store-from FIXTURE/store --articles N   (lane sca-join-5)

--store-from copies a fixture store (tools/fixtures.py, e.g. syn100k-2k) in
place of the POST load; N is then the fixture's article count.  The
Message-ID measured is read from HEAD of the middle number, so either store
works.  Lane sca-join-5 added HEAD/STAT by number, ARTICLE of the current
article and LIST COUNTS to the measured commands.
"""
import argparse, json, os, re, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from sr_measure import Conn, free_port, cpu_ms
import sr_measure

WINDOW = re.compile(rb"^lookups window (\d+):(.*)$")

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--image", required=True); p.add_argument("--work", required=True)
    p.add_argument("--articles", type=int, required=True); p.add_argument("--json", required=True)
    p.add_argument("--store-from", default=None)
    a = p.parse_args()
    sr_measure.BULK = True
    work = Path(a.work); work.mkdir(parents=True, exist_ok=False)
    store = work / "store"; port = free_port(); cfg = work / "fn.toml"
    cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n'
                   % (store, port, work / "control.sock"))
    env = dict(os.environ); env["ACL2_CUSTOMIZATION"] = "NONE"; env.pop("ACL2_SYSTEM_BOOKS", None)
    img = str(Path(a.image).resolve())
    if a.store_from:
        subprocess.run(["cp", "-a", a.store_from, str(store)], check=True)
        (store / "writer.lock").touch(mode=0o600)
        subprocess.run([img, "--fn", "store", str(store), "rebind-filesystem"], env=env, check=True,
                       stdout=subprocess.PIPE)
    else:
        subprocess.run([img, "--fn", "operator", str(cfg), "init", "--profile", "default", "--max-transactions",
                        "16384", "--max-history-octets", str(256 << 20), "fn.test"],
                       env=env, check=True, stdout=subprocess.PIPE)
    env["FN_NATIVE_COUNT_LOOKUPS"] = "1"
    errpath = work / "owner.stderr"; err = open(errpath, "wb")
    proc = subprocess.Popen([img, "--fn", "operator", str(cfg), "run"], env=env,
                            stdout=subprocess.PIPE, stderr=err)
    out = {"image": img, "articles": a.articles, "commands": {}}
    try:
        while True:
            l = proc.stdout.readline()
            if not l: raise SystemExit("owner exited before LISTENING")
            if l.startswith(b"LISTENING "): break
        body = ("x" * 76 + "\r\n") * 24
        c = Conn(port); t1 = time.perf_counter()
        for i in range(0 if a.store_from else a.articles):
            r = c.line("POST"); assert r.startswith(b"340"), (i, r)
            art = ("From: cs7@example.invalid\r\nNewsgroups: fn.test\r\nSubject: cs7 %d\r\n"
                   "Date: Thu, 24 Sep 2026 12:00:00 +0000\r\nMessage-ID: <cs7-%06d@example.invalid>\r\n\r\n%s"
                   % (i, i, body))
            c.f.write(art.encode() + b".\r\n"); r = c.readline(); assert r.startswith(b"240"), (i, r)
        c.line("QUIT"); c.sock.close(); out["load_s"] = round(time.perf_counter() - t1, 1)
        t_settle = time.perf_counter()
        while time.perf_counter() - t_settle < 600:
            c_a = cpu_ms(proc.pid); time.sleep(2); c_b = cpu_ms(proc.pid)
            if c_b - c_a < 40: break
        n = a.articles; mid = n // 2
        c = Conn(port); c.line("GROUP fn.test")
        c.f.write(b"HEAD %d\r\n" % mid); first = c.readline(); assert first.startswith(b"221"), first
        hl = []
        while True:
            l = c.readline()
            if l in (b".\r\n", b""): break
            hl.append(l)
        msgid = [l.split(b":", 1)[1].strip().decode() for l in hl
                 if l.lower().startswith(b"message-id:")][0]
        c.line("QUIT"); c.sock.close()
        cmds = [("DATE", "DATE"),
                ("GROUP", "GROUP fn.test"),
                ("LISTGROUP whole", "LISTGROUP fn.test"),
                ("LISTGROUP 40", "LISTGROUP fn.test %d-%d" % (mid, mid + 39)),
                ("ARTICLE number", "ARTICLE %d" % mid),
                ("HEAD number", "HEAD %d" % mid),
                ("STAT number", "STAT %d" % mid),
                ("ARTICLE current", "ARTICLE"),
                ("ARTICLE msgid", "ARTICLE %s" % msgid),
                ("LIST COUNTS", "LIST COUNTS"),
                ("OVER 40", "OVER %d-%d" % (mid, mid + 39)),
                ("OVER 1-2000", "OVER 1-2000")]
        c = Conn(port); c.line("GROUP fn.test"); c.line("DATE")
        for label, cmd in cmds:
            runs = []
            for rep in range(1 if label == "DATE" else 2):
                pos = errpath.stat().st_size
                _, first, lines, _ = c.multi(cmd); c.line("DATE")
                deadline = time.time() + 30
                while True:
                    new = errpath.read_bytes()[pos:]
                    ws = [m for m in (WINDOW.match(x) for x in new.splitlines()) if m]
                    if len(ws) >= 2: break
                    assert time.time() < deadline, (cmd, new[-400:]); time.sleep(0.05)
                # ws[0] closes the previous DATE's window (printed when CMD's read
                # began); every later window up to DATE's is CMD's (a command split
                # over reads prints one per read).
                counts = {}
                for m in ws[1:]:
                    for kv in m.group(2).split():
                        k, v = kv.split(b"=")
                        counts[k.decode()] = counts.get(k.decode(), 0) + int(v)
                runs.append({"reply": first.decode().strip(), "reply_lines": lines,
                             "windows": len(ws) - 1, "counts": counts})
            out["commands"][label] = {"command": cmd, "runs": runs,
                                      "stable": all(r["counts"] == runs[0]["counts"] for r in runs)}
        c.line("QUIT"); c.sock.close()
    finally:
        proc.terminate()
        try: proc.wait(timeout=60)
        except subprocess.TimeoutExpired: proc.kill()
    head = [l for l in errpath.read_bytes().splitlines() if l.startswith(b"lookups ") and b"counted" in l]
    out["installed"] = [l.decode() for l in head]
    Path(a.json).write_text(json.dumps(out, indent=1)); print(json.dumps(out))

if __name__ == "__main__":
    main()
