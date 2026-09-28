#!/usr/bin/env python3
"""The registered hbox fixtures, rebuilt from their recipes with one image (PKT-705).

    python3 tools/fixtures.py list
    python3 tools/fixtures.py rebuild --image IMAGE --rev REV [--only NAME ...]
                                      [--root ROOT] [--work DIR] [--jobs N]
    python3 tools/fixtures.py check [--root ROOT] [--rev REV]
    python3 tools/fixtures.py opens --image IMAGE [--only NAME ...] [--root ROOT] [--work DIR]

A fixture is a store (or a BP journal holding one) built once and copied by
every run that needs it; nothing opens a fixture in place.  D34 keeps one
store format and translates nothing, so a fixture made before a store-format
change (a new format word, or a profile layout that grew, as batch AS's did)
no longer opens: the open refuses it by name (`reason=store-format`,
`reason=older-release`).  The batch therefore runs `rebuild` after any
store-format change (build/coordinator/NIGHT.md's batch routine,
BRIEF-COMMON.md's fixture note), and no fixture is kept past its format.

Run ON hbox, from a tree tools/hbox_native.sh shipped
(/tank/fn/scratch/LANE/native-LABEL/tree: this file's tree is TREE, its
recipes are TREE's), with IMAGE that tree's build/fn-host-developer and REV
the revision it was built from.  Each fixture:

  1. its recipe (REGISTRY below: the script and arguments that built it
     first, kept in the repository) runs in WORK/NAME (tmpfs by default),
     inside `systemd-run --user --scope -p MemoryMax=SIZE` when systemd-run
     exists;
  2. the result is assembled in ROOT/.staging/NAME with FIXTURE.json (name,
     recipe, image, the image core's SHA-256, REV, UTC, seconds), README and
     SHA256SUMS (every file);
  3. only then ROOT/NAME is replaced: the old directory moves to
     ROOT/.previous/NAME (one previous kept) and the staged one is renamed in;
  4. ROOT/MANIFEST.json gets the fixture's row (REV, core SHA-256, UTC, the
     SHA-256 of its SHA256SUMS).  A failed recipe leaves ROOT/NAME and its row
     as they were and makes the exit status 1.

A static fixture (a corpus, no store) is not rebuilt: `rebuild` and `check`
verify its SHA256SUMS.  `check` verifies every registered fixture's
SHA256SUMS and names each one whose MANIFEST row is missing or (with --rev)
was built from another revision; exit 1 if any is missing or mismatched.
`opens` copies each store a fixture holds, rebinds the copy
(`store COPY rebind-filesystem`, as every consumer's copy must be) and runs
`store COPY recover`
with IMAGE (the second image of a batch, or a later one): exit 1 unless every
copy recovers.  Names in RETIRED are fixtures the rebuild replaces or D34 removed; `rebuild`
moves any still present to ROOT/.previous.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

TREE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TREE / "tools"))
import native_env  # noqa: E402
ROOT = Path("/tank/fn/scratch/fixtures")
WORK = Path("/dev/shm/fn-fixtures")
PY = sys.executable or "python3"
EVIDENCE = "planning/evidence"
OPENSSL_TEST = "/tank/fn/toolchains/openssl-3.5.8"
# The capacity the posting recipes init with: `--profile default` was the
# old defaults (T = 2^32-1); the preset now holds 128 transactions, and its
# record and article bounds (R 64 MiB, A 16 MiB) charge each connection more
# than an owner admits; H is 512 MiB, room for 10,000 articles of 32 KiB.
# So: the presets' R, A and G with room for the recipes' N.  Every recipe
# runs in a 40 GB unit, as tools/service_envelope.py's do: in a 24 GB unit
# the owner of a scale-sized profile refuses to start
# (`connections-exceed-memory ... holds=0`, books/connection-budget.lisp).
CAPACITY = ("--max-transactions", "1048576", "--max-history-octets", "536870912",
            "--max-open-suffix", "65536", "--max-record-octets", "17138486",
            "--max-article-octets", "32768", "--max-groups-per-article", "65535")
# rep_measure.py's articles of "about 32 KiB" exceed A = 32768: A 64 KiB, R
# 32 MiB (the article record's bound for it), H 1 GiB.
CAPACITY_32K = ("--max-transactions", "1048576", "--max-history-octets", "1073741824",
                "--max-open-suffix", "65536", "--max-record-octets", "33554432",
                "--max-article-octets", "65536", "--max-groups-per-article", "65535")

# Fixtures a rebuild replaces under a stable name, or that D34 retired.
RETIRED = {
    "chain-20000-8cc3cd4c": "replaced by chain-20000 (the same recipe; the name no longer carries a revision)",
    "format-7-store": "retired (PKT-695): the store-format refusal is tested on a synthesized store "
                      "(tests/older_release_store.py)",
}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def write_sums(root: Path) -> None:
    lines = []
    for path in sorted(p for p in root.rglob("*") if p.is_file() and not p.is_symlink()):
        rel = path.relative_to(root)
        if str(rel) == "SHA256SUMS":
            continue
        lines.append("{}  {}\n".format(sha256_file(path), rel))
    (root / "SHA256SUMS").write_text("".join(lines), encoding="utf-8")


def verify_sums(root: Path) -> list[str]:
    """The SHA256SUMS lines of ROOT that do not match; ['SHA256SUMS'] if absent."""
    sums = root / "SHA256SUMS"
    if not sums.is_file():
        return ["SHA256SUMS"]
    bad = []
    for line in sums.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        digest, rel = line.split(None, 1)
        rel = rel.lstrip("*").strip()
        path = root / rel
        if not path.is_file() or sha256_file(path) != digest:
            bad.append(rel)
    return bad


def copy_entries(src: Path, dest: Path, names, skip=()) -> None:
    """Copy the named entries of SRC into DEST (a store directory keeps its
    symlinks; sockets and the SKIP names are left behind)."""
    dest.mkdir(parents=True, exist_ok=True)
    for name in names:
        s = src / name
        if not s.exists():
            raise RuntimeError("recipe did not write {}".format(s))
        if s.is_dir():
            shutil.copytree(s, dest / name, symlinks=True,
                            ignore=lambda d, entries: [e for e in entries
                                                       if e in skip or e.endswith(".sock")])
        else:
            shutil.copy2(s, dest / name)


class Context:
    def __init__(self, image: Path, rev: str, work: Path, dest: Path, mem: str):
        self.image, self.rev, self.work, self.dest, self.mem = image, rev, work, dest, mem
        self.commands: list[list[str]] = []
        # Lane membership-budget (ember, 2026-09-27): `init' refuses a profile
        # whose full store the budget (the recipe's unit) cannot hold, unless
        # a target budget is named; the fixtures are stores made for hbox and
        # their recipes run the image directly: tools/native_env.py names the
        # target once (harness_store_env).
        self.env = native_env.harness_store_env(dict(
            os.environ, ACL2_CUSTOMIZATION="NONE",
            FN_NATIVE_DEVELOPER_HOST=str(image), FN_FIXTURE_REV=rev))
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        # The ACL2 bridge the BP recipe's harness starts (as hbox_native.sh
        # exports it).
        for name, value in (("FN_ACL2", "/tank/fn/toolchains/w28/acl2-literal-4g"),
                            ("FN_CERT_CACHE", "/tank/fn/certcache")):
            if name not in self.env and Path(value).exists():
                self.env[name] = value
        self.log = work.parent / (work.name + ".log")

    def run(self, argv, env=None, ok=(0,), timeout=4 * 3600) -> int:
        argv = [str(a) for a in argv]
        self.commands.append(argv)
        wrapped = argv
        if shutil.which("systemd-run"):
            wrapped = ["systemd-run", "--user", "--scope", "--quiet", "-p",
                       "MemoryMax=" + self.mem, "-p", "MemorySwapMax=0", "--"] + argv
        with open(self.log, "ab") as log:
            log.write(("$ " + " ".join(argv) + "\n").encode())
            log.flush()
            proc = subprocess.run(wrapped, cwd=TREE, env=env or self.env, stdout=log,
                                  stderr=subprocess.STDOUT, timeout=timeout)
        if proc.returncode not in ok:
            raise RuntimeError("{} exited {} (log {})".format(argv[:3], proc.returncode, self.log))
        return proc.returncode


# -----------------------------------------------------------------------------
# The recipes: each writes its fixture's files into ctx.dest.

def recipe_chain(ctx: Context, n: int) -> None:
    """planning/evidence/pack-chain-open-2026-09-26/chain_fixture.py build:
    the scale store of N probe articles, the served BEFORE view, the retention
    listing and `operator CONFIG store compact` (format 9: rotation and drop);
    the test copies it
    (tests.test_native_pack_chain, FN_P5_FIXTURE)."""
    ctx.run([PY, TREE / EVIDENCE / "pack-chain-open-2026-09-26/chain_fixture.py", "build",
             ctx.work / "chain", ctx.dest, n])


def recipe_posted(ctx: Context, script: str, n: int) -> None:
    """N POSTs of 2,048 octets into fn.test (default profile) over NNTP."""
    work = ctx.work / "load"
    env = dict(ctx.env, FN_FIXTURE_INIT_FLAGS=" ".join(CAPACITY))
    if script == "measure":
        ctx.run([PY, TREE / EVIDENCE / "over-number-index-2026-09-26/measure.py", "load",
                 TREE, ctx.image, work, n], env=env)
    else:
        ctx.run([PY, TREE / EVIDENCE / "post-identity-index-2026-09-26/postmeasure.py", "load",
                 ctx.image, work, n], env=env)
    check_load(work, n)
    copy_entries(work, ctx.dest, ["store"])
    shutil.copy2(work / "load.json", ctx.dest / "origin.json")


def recipe_signed(ctx: Context, n: int) -> None:
    """planning/evidence/signed-post-linear-2026-09-26/prof_signed.py load:
    profile scale, one hybrid author enrolled, N POSTs with 32 signed, 40
    signed and 40 unsigned probes."""
    work = ctx.work / "signed"
    # The test OpenSSL (ML-DSA-65 keys made independently of the node) needs
    # its own libraries, as tools/service_envelope.py gives them.
    lib = OPENSSL_TEST + "/lib"
    env = dict(ctx.env, LD_LIBRARY_PATH=lib + (":" + ctx.env["LD_LIBRARY_PATH"]
                                                if ctx.env.get("LD_LIBRARY_PATH") else ""))
    ctx.run([PY, TREE / EVIDENCE / "signed-post-linear-2026-09-26/prof_signed.py", "load",
             TREE, ctx.image, work, "--n", n, "--signed", 32, "--probes", 40], env=env)
    copy_entries(work, ctx.dest, ["store", "keys", "probes"])


def recipe_envelope(ctx: Context, n: int) -> None:
    """tools/service_envelope.py load --to N (the scale-1m profile, 2 KiB
    articles, one in 256 hybrid-signed), resumed until the store holds N."""
    work = ctx.work / "envelope"
    for _ in range(12):
        rc = ctx.run([PY, TREE / "tools/service_envelope.py", "load", "--image", ctx.image,
                      "--dir", work, "--to", n, "--budget", 1500], ok=(0, 75))
        if rc == 0:
            break
    else:
        raise RuntimeError("service_envelope load did not reach {} in 12 rounds".format(n))
    copy_entries(work, ctx.dest, ["fn.toml", "state.json", "store"], skip=("writer.lock",))


def recipe_rep_store(ctx: Context, n: int, octets: int) -> None:
    """tools/rep_measure.py (rep-wave-d's run.sh without the profiling
    image): N articles of OCTETS; the fixture is the store directory itself,
    without its state checkpoint, so its first open is the full replay."""
    work = ctx.work / "rep"
    work.mkdir(parents=True)
    ctx.run([PY, TREE / "tools/rep_measure.py", "--image", ctx.image, "--work", work / "m",
             "--articles", n, "--octets", octets, "--samples", 32, "--readers", 3,
             "--json", work / "rep.json", "--skip-reopen", "--skip-checkpoint",
             *("--init-flag=" + w for w in CAPACITY_32K)])
    store = work / "m" / "store"
    copy_entries(store, ctx.dest, sorted(p.name for p in store.iterdir()
                                         if not p.name.startswith("store-checkpoint")
                                         and not p.name.endswith(".sock")))


# The synthesized stores' seeds: profiles with room for N x 2 KiB articles
# whose init reservation (books/heap-reservation.lisp fn-heap-init-decide: the
# FULL store's run at T and H) the fixture's scope holds; the old single
# CAPACITY_SYNTH (T 4,000,000, H 8 GB, R 17 MB) asks 188,365 MB since the init
# budget check (ax-fix-init-budget) and init refuses it, which left the
# recipe with no store (extract-2, 2026-09-27).  Measured on hbox with the
# dev image ea2cc5121 (lane-tools-1-fx): SYNTH_100K reserves 10,078 MB
# (a 24 GiB scope holds it), SYNTH_1M 57,158 MB (an 80 GiB scope; a consumer opens a copy in
# one at least that size).  R 196,608 is the small preset's record bound (a
# 2 KiB article's record is about 2.9 KB); H holds N records with margin.
# K stays 65,536: the owner's automatic checkpoint rotates the log every K
# records, and synth_log_store needs the seed's whole history in one
# segment (K 128 left the seed's journal at 000007.log; the reservation is
# the same either way).
SYNTH_SMALL_BOUNDS = ("--max-record-octets", "196608", "--max-article-octets", "32768",
                      "--max-groups-per-article", "16", "--max-open-suffix", "65536")
SYNTH_100K = ("--max-transactions", "131072", "--max-history-octets", "536870912",
              *SYNTH_SMALL_BOUNDS)
SYNTH_1M = ("--max-transactions", "1048576", "--max-history-octets", "2800000000",
            *SYNTH_SMALL_BOUNDS)


def check_load(work: Path, n: int) -> dict:
    """The load phase's load.json, refused unless init succeeded and N posted."""
    try:
        load = json.loads((work / "load.json").read_text())
    except (OSError, ValueError) as error:
        raise RuntimeError("load.json unreadable in {}: {}".format(work, error))
    if load.get("init_rc") != 0 or load.get("n") != n:
        raise RuntimeError("load.json: init_rc={} n={} init: {}".format(
            load.get("init_rc"), load.get("n"), (load.get("init_tail") or "").strip()))
    return load


def recipe_synth(ctx: Context, n: int, flags: tuple) -> None:
    """tools/synth_log_store.py: a seed of 1,000 POSTed 2 KiB articles (the
    n1k-2k recipe under FLAGS, then capacity 2 N + 4,000 units: a 2 KiB
    article is charged 2; lane fitness), renumbered
    to N article records written as the log directly (batch-8 entries, no
    checkpoint): the first open is a full replay of N records
    (planning/evidence/snapshot-open-2-2026-09-27.md section 5)."""
    work = ctx.work / "seed"
    env = dict(ctx.env, FN_FIXTURE_INIT_FLAGS=" ".join(flags))
    ctx.run([PY, TREE / EVIDENCE / "post-identity-index-2026-09-26/postmeasure.py", "load",
             ctx.image, work, 1000], env=env)
    check_load(work, 1000)
    ctx.run([PY, TREE / EVIDENCE / "snapshot-open-3-2026-09-27/capseed.py", ctx.image,
             work / "store", 2 * n + 4000])
    # The seed's history is its journal: no checkpoint goes into the copy.
    for path in (work / "store").glob("store-checkpoint*"):
        path.unlink()
    ctx.dest.mkdir(parents=True)
    ctx.run([PY, TREE / "tools/synth_log_store.py", work / "store", ctx.dest / "store", n,
             "--batch", 8])
    (ctx.dest / "store" / "writer.lock").unlink(missing_ok=True)
    shutil.copy2(work / "load.json", ctx.dest / "seed-load.json")


def recipe_synth_lz(ctx: Context, n: int, threshold: int = 64) -> None:
    """recipe_synth's store with its records COMPRESSED (lane
    compression-extents-2): the synthesized store (built in WORK/plain) is
    exported and imported by the developer image with
    FN_NATIVE_IMPORT_COMPRESS_MIN_TEST=THRESHOLD, so every article record goes
    through the compressed append (ACL2's plan, the LZ4 candidate, the proved
    decoder's check) exactly as a POST under `policy set compress-min-octets'
    would; then that configuration row is set, so an owner started on a copy
    keeps compressing.  A function of recipe_synth: rebuilt after any format
    change with it."""
    plain = Context(ctx.image, ctx.rev, ctx.work / "plain-work", ctx.work / "plain", ctx.mem)
    plain.work.mkdir(parents=True, exist_ok=True)
    plain.log = ctx.log
    # The registered plain fixture when it is present (its bytes are
    # recipe_synth's; rebuilding it costs the seed's init and the synthesis
    # again), else the recipe.
    registered = ROOT / "syn100k-2k" / "store"
    if n == 100000 and (registered / "journal").is_dir():
        plain.dest.mkdir(parents=True)
        shutil.copytree(registered, plain.dest / "store", symlinks=True)
    else:
        recipe_synth(plain, n, SYNTH_100K if n == 100000 else SYNTH_1M)
    lock = plain.dest / "store" / "writer.lock"
    lock.touch()
    os.chmod(lock, 0o600)
    archive = ctx.work / "archive"
    ctx.run([ctx.image, "--fn", "store", plain.dest / "store", "export", archive], env=ctx.env)
    ctx.dest.mkdir(parents=True)
    store = ctx.dest / "store"
    ctx.run([ctx.image, "--fn", "store", store, "import", archive],
            env=dict(ctx.env, FN_NATIVE_IMPORT_COMPRESS_MIN_TEST=str(threshold)))
    config = ctx.work / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 1\n'
                      '[control]\npath = "%s"\n' % (store, ctx.work / "c.sock"))
    ctx.run([ctx.image, "--fn", "operator", config, "policy", "set", "compress-min-octets",
             threshold], env=ctx.env)
    ctx.run([ctx.image, "--fn", "store", store, "compression"], env=ctx.env)
    (store / "writer.lock").unlink(missing_ok=True)
    shutil.rmtree(plain.dest, ignore_errors=True)
    shutil.rmtree(archive, ignore_errors=True)


def recipe_bp_open(ctx: Context) -> None:
    """planning/evidence/bp-checkpoint-open-2026-09-26/fixture.py: SCN-077's
    first half (1,311 held rows), the journal before and after the rotation
    as tars; measure.py beside it reads them."""
    here = TREE / EVIDENCE / "bp-checkpoint-open-2026-09-26"
    env = dict(ctx.env, FIXTURE_DIR=str(ctx.dest))
    ctx.dest.mkdir(parents=True)
    ctx.run([PY, here / "fixture.py"], env=env)
    shutil.rmtree(ctx.dest / "t", ignore_errors=True)
    for name in ("fixture.py", "measure.py"):
        shutil.copy2(here / name, ctx.dest / name)


class Fixture:
    def __init__(self, name, recipe=None, mem="40G", readme="", static=False,
                 stores=("store",), tar=None):
        self.name, self.recipe, self.mem, self.readme, self.static = name, recipe, mem, readme, static
        # The stores it holds (relative paths; "." is the directory itself),
        # inside TAR when it has one.
        self.stores, self.tar = stores, tar


REGISTRY = [
    Fixture("chain-20000", lambda c: recipe_chain(c, 20000), mem="40G",
            readme="20,000 probe articles (scale profile, --max-transactions 1048576, "
                   "--max-article-octets 2048) compacted over the record log (format 9: a "
                   "checkpoint with the log rotated, segment 1 dropped), with the served "
                   "before-view, retention and compact output. FN_P5_FIXTURE for "
                   "tests.test_native_pack_chain; scenario steps name it."),
    Fixture("n10k-2k", lambda c: recipe_posted(c, "measure", 10000),
            readme="N = 10,000 x 2,048-octet articles in fn.test (--profile default with "
                   "CAPACITY: T 1048576, H 512 MiB, K 65536, the presets' R, A, G), POSTed by "
                   "over-number-index measure.py load; msgids as msgid_measure.msgid."),
    Fixture("n1k-2k", lambda c: recipe_posted(c, "postmeasure", 1000),
            readme="N = 1,000 x 2,048-octet articles in fn.test (--profile default with "
                   "CAPACITY), POSTed by "
                   "post-identity-index postmeasure.py load; msgids as rep_measure.article(i)."),
    Fixture("signed-n1000-2k-32", lambda c: recipe_signed(c, 1000),
            readme="prof_signed.py load --n 1000 --signed 32 --probes 40: store (profile scale, "
                   "group fn.test, one hybrid author enrolled), keys, probes. Use: prof_signed.py "
                   "run TREE IMAGE <a copy of this dir> TAG."),
    Fixture("signed-n10000-2k-32", lambda c: recipe_signed(c, 10000),
            readme="prof_signed.py load --n 10000 --signed 32 --probes 40 (as signed-n1000-2k-32)."),
    Fixture("t40k-2k-cp5", lambda c: recipe_envelope(c, 40000), mem="40G",
            readme="40,000 x 2 KiB articles, one in 256 hybrid-signed (scale-1m profile), loaded by "
                   "tools/service_envelope.py load; fn.toml and state.json are the loader's "
                   "(their paths name the build directory: rewrite them in a copy)."),
    Fixture("checkpoint-pipeline-n10k-32k", lambda c: recipe_rep_store(c, 10000, 32768),
            stores=(".",),
            readme="10,000 articles of 32 KiB (--profile default with CAPACITY_32K) by "
                   "tools/rep_measure.py; the "
                   "directory is the store, with no state checkpoint (the first open is a full "
                   "replay). Copy it before use: the verbs write writer.lock and a checkpoint."),
    Fixture("bp-checkpoint-open-1311", recipe_bp_open, stores=("t/store",),
            tar="pre-rotation.tar",
            readme="SCN-077's first half (1,311 held rows): pre-rotation.tar and post-rotation.tar "
                   "of the BP journal t/, built by fixture.py; measure.py LABEL TREE IMAGE times "
                   "the three opens."),
    Fixture("syn100k-2k", lambda c: recipe_synth(c, 100000, SYNTH_100K), mem="24G",
            readme="100,000 x 2 KiB article records synthesized as the log (tools/synth_log_store.py "
                   "from a 1,000-article seed initialized with SYNTH_100K: T 131072, H 512 MiB, "
                   "R 196608, A 32768, G 16, K 65536; init reservation 10,078 MB; capacity "
                   "204,000, batch-8 entries, no checkpoint): the open is a full replay "
                   "(OWNER-OPEN open=full-replay). Copy store/ and touch writer.lock (mode 600) "
                   "before use; seed-load.json is the seed's init line."),
    Fixture("syn100k-2k-lz", lambda c: recipe_synth_lz(c, 100000), mem="40G",
            readme="syn100k-2k with every article record COMPRESSED (LZ4-HC block frames, "
                   "dictionary 0, threshold 64; tools/fixtures.py recipe_synth_lz: the "
                   "synthesized store exported and imported through the compressed append), "
                   "and the `compress-min-octets 64' configuration row. `store ROOT compression' "
                   "reports it. Copy store/ and touch writer.lock (mode 600) before use."),
    Fixture("syn1m-2k", lambda c: recipe_synth(c, 1000000, SYNTH_1M), mem="80G",
            readme="1,000,000 x 2 KiB article records, as syn100k-2k (2.56 GB of entries), seed "
                   "initialized with SYNTH_1M: T 1048576, H 2,800,000,000, the same R A G K; its "
                   "init reservation is 57,158 MB, so open a copy under MemoryMax 80G (a 40G or "
                   "24G scope refuses it: machine-cannot-hold-profile)."),
    Fixture("usenet-20news-19997", static=True,
            readme="The 20 Newsgroups corpus (a corpus, not a store): verified, never rebuilt."),
]
BY_NAME = {f.name: f for f in REGISTRY}


def manifest_update(root: Path, name: str, row) -> None:
    lock = open(root / ".manifest.lock", "a")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX)
        path = root / "MANIFEST.json"
        data = json.loads(path.read_text()) if path.exists() else {
            "description": "The registered fixtures and the image each was built with "
                           "(tools/fixtures.py).", "fixtures": {}}
        if row is None:
            data["fixtures"].pop(name, None)
        else:
            data["fixtures"][name] = row
        tmp = path.with_suffix(".tmp")
        tmp.write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
        os.replace(tmp, path)
    finally:
        fcntl.flock(lock, fcntl.LOCK_UN)
        lock.close()


def retire(root: Path, name: str) -> None:
    """Move ROOT/NAME to ROOT/.previous/NAME, replacing an older previous."""
    current = root / name
    if not current.exists():
        return
    previous = root / ".previous" / name
    previous.parent.mkdir(exist_ok=True)
    if previous.exists():
        shutil.rmtree(previous)
    os.rename(current, previous)


def rebuild_one(fixture: Fixture, args, core_sha: str) -> tuple[str, str]:
    root = Path(args.root)
    if fixture.static:
        bad = verify_sums(root / fixture.name)
        return fixture.name, ("static, verified" if not bad else "static, MISMATCH " + ",".join(bad[:5]))
    work = Path(args.work) / fixture.name
    staging = root / ".staging" / fixture.name
    for path in (work, staging):
        if path.exists():
            shutil.rmtree(path)
    work.mkdir(parents=True)
    staging.parent.mkdir(exist_ok=True)
    ctx = Context(Path(args.image), args.rev, work, staging, fixture.mem)
    started = time.time()
    try:
        fixture.recipe(ctx)
    except Exception as ex:  # noqa: BLE001 -- the fixture's failure is reported, the rest go on
        return fixture.name, "FAILED: {}".format(ex)
    seconds = round(time.time() - started, 1)
    record = {"name": fixture.name, "rev": args.rev, "image": str(args.image),
              "image_core_sha256": core_sha,
              "built_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
              "seconds": seconds, "recipe": ctx.commands, "tree": str(TREE)}
    (staging / "FIXTURE.json").write_text(json.dumps(record, indent=1) + "\n")
    (staging / "README").write_text(
        "{}\n\n{}\nBuilt by tools/fixtures.py rebuild from revision {} (FIXTURE.json). "
        "Never open it in place: copy it, and run `fn store COPY rebind-filesystem` on a "
        "copy that is on another filesystem than the one it was built on (PKT-579).\n".format(fixture.name, fixture.readme, args.rev))
    write_sums(staging)
    retire(root, fixture.name)
    os.rename(staging, root / fixture.name)
    manifest_update(root, fixture.name, {
        "rev": args.rev, "image_core_sha256": core_sha, "built_utc": record["built_utc"],
        "seconds": seconds, "sha256sums_sha256": sha256_file(root / fixture.name / "SHA256SUMS")})
    shutil.rmtree(work, ignore_errors=True)
    return fixture.name, "rebuilt in {} s".format(seconds)


def cmd_rebuild(args) -> int:
    names = args.only or [f.name for f in REGISTRY]
    unknown = [n for n in names if n not in BY_NAME]
    if unknown:
        raise SystemExit("unknown fixture(s): {} (registered: {})".format(
            ", ".join(unknown), ", ".join(BY_NAME)))
    image = Path(args.image)
    if not os.access(image, os.X_OK):
        raise SystemExit("{} is not an executable image".format(image))
    core = Path(str(image) + ".core")
    core_sha = sha256_file(core) if core.is_file() else None
    root = Path(args.root)
    root.mkdir(parents=True, exist_ok=True)
    if not args.only:
        for name in RETIRED:
            if (root / name).exists():
                retire(root, name)
                manifest_update(root, name, None)
                print("{}: moved to .previous ({})".format(name, RETIRED[name]), flush=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda f: rebuild_one(f, args, core_sha),
                                [BY_NAME[n] for n in names]))
    failed = 0
    for name, verdict in results:
        print("{}: {}".format(name, verdict), flush=True)
        failed += verdict.startswith("FAILED") or "MISMATCH" in verdict
    return 1 if failed else 0


def cmd_check(args) -> int:
    root = Path(args.root)
    path = root / "MANIFEST.json"
    manifest = json.loads(path.read_text())["fixtures"] if path.exists() else {}
    status = 0
    for fixture in REGISTRY:
        where = root / fixture.name
        if not where.is_dir():
            print("{}: MISSING".format(fixture.name))
            status = 1
            continue
        bad = verify_sums(where)
        row = manifest.get(fixture.name)
        if bad:
            status = 1
        note = "static" if fixture.static else (
            "no MANIFEST row" if row is None else "rev {} core {}".format(
                row["rev"], (row.get("image_core_sha256") or "?")[:12]))
        stale = (not fixture.static and args.rev and (row is None or row["rev"] != args.rev))
        print("{}: {}{}{}".format(fixture.name, "SHA256SUMS ok" if not bad else
                                  "MISMATCH " + ",".join(bad[:5]), "; " + note,
                                  "; built from another revision" if stale else ""))
    for name in RETIRED:
        if (root / name).exists():
            print("{}: retired but present ({})".format(name, RETIRED[name]))
    return status


def cmd_opens(args) -> int:
    root, image = Path(args.root), Path(args.image)
    names = args.only or [f.name for f in REGISTRY if not f.static]
    status = 0
    for name in names:
        fixture = BY_NAME[name]
        work = Path(args.work) / ("opens-" + name)
        if work.exists():
            shutil.rmtree(work)
        work.mkdir(parents=True)
        source = root / name
        if fixture.tar:
            subprocess.run(["tar", "-C", str(work), "-xf", str(source / fixture.tar)], check=True)
            source = work
        for rel in fixture.stores:
            copy = work / "copy" / rel.replace("/", "-").replace(".", "self")
            shutil.copytree(source / rel, copy, symlinks=True)
            # A fixture made without a lock file (syn100k-2k, syn1m-2k) is
            # used as its README says: the copy gets writer.lock, mode 600.
            lock = copy / "writer.lock"
            if not lock.exists():
                lock.touch(mode=0o600)
            ctx = Context(image, "", work / "ctx", copy, fixture.mem)
            started = time.time()
            try:
                # A copy is a store placed elsewhere deliberately (PKT-579):
                # it is rebound to its filesystem before use, as a consumer's
                # copy must be.
                ctx.run([image, "--fn", "store", copy, "rebind-filesystem"])
                ctx.run([image, "--fn", "store", copy, "recover"])
                verdict = "recovers in {:.1f} s: {}".format(
                    time.time() - started,
                    [l for l in ctx.log.read_text(errors="replace").splitlines()
                     if l.startswith("recovered")][-1:])
            except Exception as ex:  # noqa: BLE001
                verdict = "FAILED: {}: {}".format(ex, ctx.log.read_text(errors="replace")[-600:])
                status = 1
            print("{} {}: {}".format(name, rel, verdict), flush=True)
        shutil.rmtree(work, ignore_errors=True)
    return status


def cmd_list(_args) -> int:
    for fixture in REGISTRY:
        print("{:32} {:6} {}".format(fixture.name, "static" if fixture.static else fixture.mem,
                                     fixture.readme))
    for name, why in RETIRED.items():
        print("{:32} {:6} {}".format(name, "retired", why))
    return 0


def _terminated(signum, _frame):
    # A SIGTERM (earlyoom, a stopped unit) unwinds through subprocess.run,
    # which kills the recipe's process instead of leaving it orphaned.
    raise SystemExit(128 + signum)


def main(argv=None) -> int:
    signal.signal(signal.SIGTERM, _terminated)
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("list")
    rb = sub.add_parser("rebuild")
    rb.add_argument("--image", required=True, help="the tree's build/fn-host-developer")
    rb.add_argument("--rev", required=True, help="the revision the image was built from")
    rb.add_argument("--only", nargs="+", default=None)
    rb.add_argument("--root", default=str(ROOT))
    rb.add_argument("--work", default=str(WORK))
    rb.add_argument("--jobs", type=int, default=4)
    ck = sub.add_parser("check")
    ck.add_argument("--root", default=str(ROOT))
    ck.add_argument("--rev", default=None)
    op = sub.add_parser("opens")
    op.add_argument("--image", required=True)
    op.add_argument("--only", nargs="+", default=None)
    op.add_argument("--root", default=str(ROOT))
    op.add_argument("--work", default=str(WORK))
    args = p.parse_args(argv)
    return {"list": cmd_list, "rebuild": cmd_rebuild, "check": cmd_check,
            "opens": cmd_opens}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
