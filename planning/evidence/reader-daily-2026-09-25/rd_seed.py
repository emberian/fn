#!/usr/bin/env python3
"""reader-daily walk seed: signed articles and a signed cancel by ember, through
the scratch node's control socket (hybrid-sign, hybrid-author), on hbox.

    python3 rd_seed.py IMAGE TREE NODEDIR STEM MESSAGE-ID SUBJECT [--refs R] [--cancel TARGET]
"""
import argparse, os, subprocess, sys
from pathlib import Path

p = argparse.ArgumentParser()
for name in ("image", "tree", "node", "stem", "msgid", "subject"):
    p.add_argument(name)
p.add_argument("--refs", default="")
p.add_argument("--cancel", default="")
p.add_argument("--group", default="fn.agents")
a = p.parse_args()
node = Path(a.node); keys = node / "keys" / "ember"; work = node / "seed"
work.mkdir(exist_ok=True)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
lines = ["From: ember <ember@fn.example.invalid>",
         "Newsgroups: " + ("control.cancel" if a.cancel else a.group),
         "Subject: " + a.subject, "Date: Fri, 25 Sep 2026 23:00:00 +0000",
         "Message-ID: " + a.msgid]
if a.refs:
    lines.append("References: " + a.refs)
if a.cancel:
    lines.append("Control: cancel " + a.cancel)
source = work / (a.stem + ".eml")
source.write_bytes(("\r\n".join(lines) + "\r\n\r\n" +
                    ("cancel\r\n" if a.cancel else "Signed by ember for the reader-daily walk.\r\n")).encode())
signed = subprocess.run([a.image, "--fn", "hybrid-sign", keys / "principal.bin",
                         keys / "ed-public.bin", keys / "ed-secret.bin",
                         keys / "ml-public.pem", keys / "ml-private.pem", source],
                        cwd=a.tree, env=env, stdout=subprocess.PIPE, check=True, timeout=180)
parts = dict(line.split() for line in signed.stdout.decode().splitlines() if " " in line)
(work / (a.stem + ".ed")).write_bytes(bytes.fromhex(parts["ed25519"]))
(work / (a.stem + ".ml")).write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
done = subprocess.run([a.image, "--fn", "hybrid-author", str(node / "control.sock"), "1",
                       str(source), str(work / (a.stem + ".ed")), str(work / (a.stem + ".ml")),
                       str(keys / "ml-public.pem")], cwd=a.tree, env=env,
                      stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
print("hybrid-author", a.stem, "rc", done.returncode, done.stdout.decode().strip(),
      done.stderr.decode().strip()[-300:])
sys.exit(done.returncode)
