# fn2 on dregg-forge: the quiet measurement and sweep box

dregg-forge is a Hetzner cpx62 (16 vCPU, 30 GiB, 534 GB disk, Debian 13, glibc 2.41, x86-64). It exists so fn2 certify times and long sweeps are measured on a machine whose load is not seven seats (the laptop sits at load 40-240; the box at 1.5-3). Whole fn2 closure, fresh: 175 s at -j 8, wall equal to CPU (`certify-times-forge.md`). Set up 2026-10-29; the box row in `~/.config/fn/boxes.json` is `forge`, `until 2026-11-30`.

## Other tenants: leave them alone
The box is shared with the dregg demo (an nspawn container `demo-dry` behind `ssh demo-dry`, `nd-testground`, the `vu-*` users). They use about 2 GB and one core. Nothing of theirs is ours to stop, restart or reconfigure, and `ssh dregg-forge` is the root door that `ProxyJump` for those hosts goes through. Our footprint is the user `fn`, `/tank/fn`, `/build`, one systemd user slice, and nothing else. Docker is deliberately NOT installed (it rewrites the FORWARD iptables policy the container's veth depends on) and the hostname is unchanged.

## Names and paths
| | |
|---|---|
| `ssh forge` | user `fn`, key `~/.ssh/id_portable`; use this one. Alias in `~/.ssh/fn-boxes.conf` |
| `ssh dregg-forge` | root; the demo's door; do not use for fn work |
| toolchain | `/tank/fn/sbcl`, `/tank/fn/acl2-8.7` (system books `/tank/fn/acl2-8.7/books`), `/tank/fn/toolchains/w28/acl2-literal-4g-tls64k` (the launcher; `~/.config/fn/acl2` on the box names it, so `tools/acl2` and the slot pool use it). Seeded from hbox; the toolchain identity equals hbox's, so certificates are interchangeable |
| bare repo | `/build/fn.git` (the box has no GitHub access; branches arrive by push from the laptop) |
| trees | `/build/lanes/<name>`, one clone per seat or lane. `/build/lanes/fn2-dev` is dev at `615dfde78`, certified, drivers run |
| wrapper | `swarm-build <cmd>`: a systemd user scope under `swarm.slice`, MemoryMax 25 G for the slice, `taskset` on all 16 cores, `nice 15` |
| disk | 530 GB free on `/`; fill it freely (it is ours); the laptop's disk is not |
| `ACL2_SYSTEM_BOOKS` | `/tank/fn/acl2-8.7/books` (the scripts below set it) |

What was not seeded: hbox's native image sets and certificate cache (about 12 GB compressed, 3 MB/s from hbox, and fn2's certify uses neither). `tools/box_qualify.sh forge --quick` therefore reads: arch, both toolchain identities (= hbox), python 3.13, dilithium-py, OpenSSL 3.5.8, the tools table PASS; docker and the image-set check FAIL by design. `boxq` and `farm.py` (fn1's native campaigns) will not place work here; fn2 does not use them. `tools/boxes.sh` does list it, and `reserve` works.

Bootstrap, for the record: `tools/box_bootstrap.sh` was run from a scratch copy with five edits (no docker, no hostname change, no images/certcache seed, a `useradd` before the first `su - fn`, a `|| true` on an authorized_keys glob), seeded from hbox with host-key checking off for the one hbox-to-box rsync (hbox's `known_hosts` holds a stale key for this IP and I did not touch hbox). The log is `build/cloud/forge-bootstrap.log` (and four earlier attempts) in the main tree.

## Getting a tree onto the box
From the laptop, in the main tree (or any worktree whose objects contain the commit):
```sh
git push fn@forge:/build/fn.git <ref>:refs/heads/<branch>        # dev: origin/dev:refs/heads/dev
ssh forge 'git clone -q -b <branch> /build/fn.git /build/lanes/<name>'      # first time
ssh forge 'git -C /build/lanes/<name> pull -q --ff-only /build/fn.git <branch>'   # later
```
Uncommitted edits: `rsync -a <worktree>/fn2/ forge:/build/lanes/<name>/fn2/` (no `--delete`). One clone per seat, because `certify.sh` takes one lock per tree (`build/fn2-certify.lock`) and cert.pl writes `.cert` files in the tree.

## Certify
On the box, in a tree (the scripts are in `fn2/tools/`, so a tree older than this commit gets them by `scp`):
```sh
cd /build/lanes/<name>
swarm-build sh fn2/tools/forge-certify.sh                     # the whole closure, -j 8, fresh if no .cert files: 175 s
swarm-build sh fn2/tools/forge-certify.sh books/executor.lisp tests/sched-unit.lisp    # these books plus what they need
swarm-build sh fn2/tools/forge-certify.sh -j 4 books/executor.lisp
python3 fn2/tools/certify-times.py                            # per-book table from build/certify-closure.log (or ... . build/certify-named.log)
```
`forge-certify.sh` sets `FN_ACL2`, `ACL2_SYSTEM_BOOKS` and `TIME_CERT=1`, then runs `fn2/tools/certify.sh -k` (keep going; the exit is 1 if any book failed). With no books named it certifies every `.lisp` under `books/`, `sim/`, `tests/` except the LD-only drivers and raw-Lisp files listed in `EXCLUDED` in the script. Anything over a minute: detach it with a PID file, `(nohup swarm-build sh fn2/tools/forge-certify.sh > build/run.out 2>&1 & echo $! > build/run.pid)`, and poll `build/certify-closure.log` (cert.pl output appears when it finishes) or `ls build/`. Stop a run only by the PID in its PID file.

The slot pool (`~/.cache/fn-acl2-slots`, 16 slots) is shared by every seat on the box, as on hbox. The slice cap is 25 G for everything run under `swarm-build`.

## Measuring
A measurement needs a quiet box. Reserve it: `tools/boxes.sh reserve forge --for 30 --why "fn2 closure timing" --as <seat>` from the laptop, `tools/boxes.sh release forge --as <seat>` after, `tools/boxes.sh check forge`. Routine certification does not reserve. Check `ssh forge uptime` first: baseline load is 1.5-3 (the tenants); a number measured at load above 6 is suspect. Report wall and CPU together (`certify-times.py` prints both); CPU is machine-independent, wall on the box equals it.

## Acceptance drivers (A's six, B's sweep)
The LD drivers `include-book` certified books, so certify the tree first. `fn2/tools/forge-driver.sh NAME` starts one detached under `swarm-build` with a timeout, `build/NAME.pid` and `build/NAME.log` in the tree:
```sh
cd /build/lanes/<name>
sh fn2/tools/forge-driver.sh                       # lists the names
sh fn2/tools/forge-driver.sh sim-layer-a-a4-driver  # layer A's fixed gate (FN2_SWARM unset)
tail -f build/sim-layer-a-a4-driver.log; kill -0 $(cat build/sim-layer-a-a4-driver.pid) && echo running
```
Layer A: `sim-layer-a-a4-driver` (the fixed gate), `core-allocation-driver`, `sim-allocation-driver`, `executor-allocation-driver`, `sim-acquisition-driver`, `sim-layer-a-a4-smoke`. Layer B on dev: `crash-model-differential` (the concrete differential sweep, B1) and `blake3-vectors`. The B3b-2 concrete sweep (`sim-layer-b`, 20,000 cases, 2,400-2,600 s on the laptop) is not on dev yet; when it lands, `SECS=7200 sh fn2/tools/forge-driver.sh sim-layer-b-driver` (any `fn2/tests/NAME.lsp` runs the same way) is its recipe, and its table row goes in the next section. Swarm mode of the A gate: `FN2_SWARM=1 FN_ACL2=... nohup swarm-build timeout -k 5 3600 tools/acl2 < fn2/tests/sim-layer-a-a4-driver.lsp > build/r5d-swarm.log 2>&1 &` with its own PID file; the script leaves it unset on purpose.

Measured 2026-10-29 on the box, all seven started together at `615dfde78` (they ran in parallel; each is single-threaded):

| driver | ended | tail of the log |
|---|---|---|
| core-allocation-driver | under 5 s | `CORE HOT LOOP: 100000 cycles, 0 bytes`, `:PASSED` |
| sim-acquisition-driver | under 5 s | `SIM-ACQUISITION PASS` |
| sim-allocation-driver | 14 s | `LIVE: 50000 strict successful operations`, `:PASSED` |
| sim-layer-a-a4-smoke | 14 s | `OWN READS SMOKE ... total=69357` |
| executor-allocation-driver | 69 s | `STEADY ECHO TURN CPU ... turns=25111 mean-us=22.577` |
| sim-layer-a-a4-driver | 91 s (last log write) | `OWN READS ECHO+LIVENESS ... total=53257` |
| crash-model-differential | 12 s of evaluation (3 min wall with startup) | ends after the timing block |

## Ending
The row expires 2026-11-30 (`~/.config/fn/boxes.json`). The box is the dregg demo's, so nothing here tears it down; when the work ends, delete `/build/lanes/*`, `/build/fn.git`, `/tank/fn` and the `fn` user's slice, and remove the `Host forge` block from `~/.ssh/fn-boxes.conf`. Nothing on the box is a record: certificates are rebuilt by a closure run, and there is nothing to pull back to hbox.
