#!/usr/bin/env python3
"""Reopen a kept violation store (a campaign's `violation-NNNN/store.qcow2`)
in configuration NAME's VM: `recover` at the launcher's heap, then at
--heap MB through libexec/fn/fn-host, then `status` (lane
power-loss-openbsd-2, PKT-686: is a store that recover cannot open in its
figured heap intact?).  NAME's store disk is overwritten with the copy.

  python3 power_loss_openbsd_reopen.py --fn BIN NAME STORE_QCOW2 EP
"""
import argparse, json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import power_loss_openbsd as P

ap = argparse.ArgumentParser()
ap.add_argument("--base", default="/tank/fn/scratch/power-loss-openbsd")
ap.add_argument("--fn", required=True)
ap.add_argument("--heap", type=int, default=1800)
ap.add_argument("name")
ap.add_argument("store")
ap.add_argument("ep")
a = ap.parse_args()
B = Path(a.base)
cfg = json.loads((B / a.name / "cfg.json").read_text())
store_path = Path(a.store).resolve().relative_to(B)
print(P.qemu_img(B, "convert", "-O", "raw", "/pl/%s" % store_path, "/pl/%s/store.img" % a.name))
vm = P.VM(B, cfg)
vm.boots = 900
vm.start()
host = str(Path(a.fn).parent.parent / "libexec" / "fn" / "fn-host")
cmd = ("fsck -y /dev/rsd1a | tail -2; mount /dev/sd1a /pl; printf %s > /var/pl/%s.toml; cd /var/pl; "
       "%s operator /var/pl/%s.toml recover 2>&1 | head -3; echo recover-exit=$?; "
       "env SBCL_USER_ARGS='--dynamic-space-size %d' %s --fn operator /var/pl/%s.toml recover 2>&1 | tail -3; "
       "env SBCL_USER_ARGS='--dynamic-space-size %d' %s --fn operator /var/pl/%s.toml status 2>&1 | grep -E '^transactions|^heap|accepted|refused'"
       % (P.shlex.quote(P.cfg_text(a.ep)), a.ep, a.fn, a.ep, a.heap, host, a.ep, a.heap, host, a.ep))
code, so, se = vm.ssh(cmd, timeout=1800)
print(so, se)
vm.shutdown()
