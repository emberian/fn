#!/usr/bin/env python3
"""Run fn's certification on a farm box and bring the evidence home.

The laptop is the wrong machine for a wide certification: it has four ACL2
slots and other work on it.  persvati and hbox are the farm.  Because every
tool sets ``ACL2_BOOK_HASH_ALISTP=NIL``, certificates produced there are valid
here, so a farm run is not a separate world: it is the same certification with
the evidence and the certificate pairs rsynced back and published to the local
cache.

    python3 tools/farm.py submit persvati --jobs 12 --affected-by books/wire.lisp
    python3 tools/farm.py wait persvati run-20260919T101500Z-4f2a
    python3 tools/farm.py status hbox --remote-root /tank/fn/gates/my-run

``submit`` mirrors this worktree to the requested absolute path on the host,
installs from the box's cache into the mirrored tree, starts the runner
detached with its own log and status file, and returns a run id.  The
installer first computes the runner's exact selected roots.  By default it
then installs every book of their closure, roots included, that the cache
holds at its current digest and this ACL2 toolchain, each from its own
newest usable origin (``certs.py install-partial``; the measurement that ACL2
accepts a closure composed from several origins is
``planning/evidence/certificate-cache-2026-09-23.md``), and the runner, given
``--incremental``, certifies only the rest in dependency order.  A miss is
work, not a refusal.  ``--require-origin`` demands one complete dependency
set from one origin and refuses a miss before ACL2 starts; ``--closure`` is
root's from-scratch recertification.  The install is
the difference between certifying what changed and certifying a whole dependency closure: on 2026-09-20 a lane's
``--closure`` run on an empty remote root spent 30 minutes re-certifying the
substrate for four new books.  ``wait`` blocks on that id, printing progress
every poll and never spinning; it returns the runner's own exit code.  hbox's
runner is wrapped in ``swarm-build``, which enforces a memory cap there: the
containment is structural, not courtesy to another tenant (there is none).
``status`` takes one read-only remote snapshot. Before a terminal status exists,
it reports exited and active *records*; these records are not a process-liveness
check and may outlive a child. ACL2 can exit zero after a failed theorem. Only
the terminal manifest supplies passed and failed book counts. Missing activity
is shown as unknown, never as zero progress.

**The box cache is seeded by the runner, one book at a time.**  The runner
publishes each pair as that book certifies, so what the box holds tracks what
has actually been certified at every moment -- including for a run that then
fails, is killed, or is never waited on.  A wide run on this tree exits
non-zero while any root carries an open theorem, and publishing on the run's
verdict meant no lane seeded the box at all: measured on persvati 2026-09-20,
a run that certified 21 of 22 books left 0 entries and the next submit into
the same root reported ``installed 0, kept 0, uncached 267``; with the
per-book publish it reports ``installed 21``
(``planning/evidence/farm-cache-failed-run-2026-09-20.md``).  ``wait`` sweeps
the box once more when it returns, on every exit code and on its timeout
path, and a sweep that printed nothing says so rather than passing for a
sweep that found nothing.
"""

from __future__ import annotations

import argparse
from collections.abc import Callable
import datetime as dt
import json
import os
from pathlib import Path
import re
import secrets
import shlex
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import certs
import evidence_manifests

HOSTS = {
    "persvati": {
        "acl2": "/home/ember/fn-gates/toolchains/w25/acl2-literal",
        "cache": "~/fn-certcache",
        "wrap": "",
    },
    "hbox": {
        "acl2": "/tank/fn/toolchains/w28/acl2-literal-4g",
        "cache": "/tank/fn/certcache",
        # hbox is shared with another project's build; swarm-build is the
        # cgroup with the enforced memory cap.
        "wrap": "swarm-build",
    },
}
EXCLUDES = ("build/", ".git/", "__pycache__/", ".venv/", "*.pyc")
POLL_SECONDS = 30
DEFAULT_WAIT_SECONDS = 6 * 60 * 60
EVIDENCE = re.compile(r"Certification evidence: (build/acl2/[A-Za-z0-9._-]+)")
# `certs.py install-set` prints the identity and counts of the one set it
# selected.  A missing identity means there was no coherent input set.
INSTALLED_SET = re.compile(
    r"artifact-set (\S+) origin (\S+) source (\S+) toolchain (\S+); "
    r"installed (\d+), kept (\d+), missing (\d+), removed (\d+)"
    r"(?:; origins (\S+))?")
# What `certs.py install-partial` prints: the closure size, then the counts.
INSTALLED_PARTIAL = re.compile(
    r"install-partial: (\d+) books.*\n\s*toolchain (\S+); installed (\d+), "
    r"kept (\d+), missing (\d+), removed (\d+); roots installed (\d+) of (\d+)"
    r"(?:; origins (\S+))?")

# Seams: the tests drive the real command construction through these.
RUN = subprocess.run
SLEEP = time.sleep


class FarmError(Exception):
    """A farm run that did not start, reported instead of returned as a run id."""


def refuse_unmerged_source(root: Path) -> None:
    """Refuse unresolved Git operations before any remote side effect.

    Ordinary uncommitted lane edits and exported source archives remain valid
    inputs. This check does not freeze a mutable checkout: image qualification
    must submit from its own pinned checkout or immutable export.
    """
    if not (root / ".git").exists():
        return
    result = run(["git", "-C", str(root), "diff", "--name-only",
                  "--diff-filter=U", "-z"], check=False)
    if result.returncode:
        raise FarmError(f"cannot inspect source index under {root}: "
                        f"{result.stdout.strip()}")
    paths = [path for path in result.stdout.split("\0") if path]
    if paths:
        raise FarmError("unmerged source; no farm run started: "
                        + ", ".join(repr(path) for path in paths))


def host_settings(host: str, cache: str | None = None,
                  acl2: str | None = None) -> dict:
    """What this host needs, with explicit cache and ACL2 overrides.

    An override is how a measurement isolates itself from the shared cache:
    the pairs a probe run publishes must not be mixed into what the next
    lane installs, and a lane reading counts out of the shared cache cannot
    tell its own run's effect from another lane's.
    """
    settings = dict(HOSTS.get(host, {"acl2": "acl2", "cache": "~/fn-certcache",
                                     "wrap": ""}))
    if cache:
        settings["cache"] = cache
    if acl2:
        settings["acl2"] = acl2
    return settings


def acl2_shell_word(host: str, acl2: str | None = None) -> str:
    """The configured default expression, or one quoted literal override."""
    if acl2 is not None:
        return remote_quote(acl2)
    return str(host_settings(host)["acl2"])


def run(command: list[str], check: bool = True) -> subprocess.CompletedProcess:
    return RUN(command, check=check, stdout=subprocess.PIPE,
               stderr=subprocess.STDOUT, text=True)


def ssh(host: str, script: str, check: bool = True) -> subprocess.CompletedProcess:
    return run(["ssh", "-n", host, script], check=check)


def remote_quote(path: Path | str) -> str:
    """A remote-shell word for `path`, with a leading `~` left to the shell.

    `shlex.quote("~/fn-lanes/x")` is `'~/fn-lanes/x'`, which no shell expands:
    the remote `cd` then lands nowhere and the run produces no log at all.
    `submit` resolves the tilde before it records anything, so this is the
    second line of defence, for a path that reaches a script unresolved.
    """
    text = str(path)
    if text == "~":
        return '"$HOME"'
    if text.startswith("~/"):
        return '"$HOME"/' + shlex.quote(text[2:])
    return shlex.quote(text)


def expand_remote(host: str, path: Path | str) -> Path:
    """`path` with a leading `~` resolved to the host's own $HOME, in one ssh.

    The resolved path is also what is recorded as the certificates' origin,
    and a certificate's post-alist names its sub-books by absolute path, so
    the origin has to be the absolute path the run really used.
    """
    text = str(path)
    if text != "~" and not text.startswith("~/"):
        return Path(text)
    answer = ssh(host, "echo $HOME", check=False)
    home = answer.stdout.strip().splitlines()[-1].strip() if answer.stdout.strip() else ""
    if answer.returncode != 0 or not home.startswith("/"):
        raise FarmError(f"{host}: cannot resolve $HOME for {text}: "
                        f"ssh exited {answer.returncode}: {answer.stdout.strip()}")
    return Path(home) if text == "~" else Path(home) / text[2:]


def certs_script(host: str, root: Path, action: str,
                 origin_kind: str | None = None,
                 cache: str | None = None) -> str:
    """Drive the box's own certificate cache inside the mirrored tree.

    The cache lives on the box (``HOSTS[host]["cache"]``), not here, and a
    pair in it is usable only if this tree's books hash to the same closure,
    which ``certs.py`` checks.  `install-set` runs before the runner; `publish
    --origin-kind run` runs after it, so the next lane on the box finds the
    pairs this run made and `install` accepts them: a finished run root is a
    snapshot, not a live worktree.
    """
    where = host_settings(host, cache)["cache"]
    kind = f"--origin-kind {origin_kind} " if origin_kind else ""
    return (f"cd {remote_quote(root)} || exit 9; "
            f"python3 tools/certs.py --cache {remote_quote(where)} "
            f"{kind}{action}")


def parse_origins(words: str) -> dict[str, int]:
    """`/a=3,/b=5`: which origins a set drew from, and how many books each."""
    return {where: int(count) for where, _, count in
            (word.rpartition("=") for word in words.split(","))}


def parse_installed(output: str) -> dict[str, object]:
    """The identity/count line `certs.py install-set` or `install-partial` prints."""
    partial = INSTALLED_PARTIAL.search(output)
    if partial:
        books, toolchain, *numbers, origins = partial.groups()
        installed, kept, missing, removed, roots_installed, roots = (
            int(number) for number in numbers)
        parsed: dict[str, object] = {
            "mode": "incremental",
            "books": int(books),
            "toolchain_identity": toolchain,
            "installed": installed, "kept": kept, "missing": missing,
            "removed": removed, "roots_installed": roots_installed,
            "roots": roots,
            # Every book the cache lacked is certified, roots included.
            "certify": missing,
        }
        if origins:
            parsed["origins"] = parse_origins(origins)
        return parsed
    found = INSTALLED_SET.search(output)
    if not found:
        return {}
    artifact_set, origin, source, toolchain, *numbers, origins = found.groups()
    parsed: dict[str, object] = {
        "artifact_set": None if artifact_set == "NONE" else artifact_set,
        "origin": None if origin == "NONE" else origin,
        "source_identity": None if source == "NONE" else source,
        "toolchain_identity": None if toolchain == "NONE" else toolchain,
        **dict(zip(("installed", "kept", "missing", "removed"),
                   (int(number) for number in numbers))),
    }
    if origins:
        parsed["origins"] = parse_origins(origins)
    return parsed


def selection_words(books: list[str], affected_by: list[str],
                    closure: bool) -> list[str]:
    """The runner arguments that select its exact requested book list."""
    words = ["python3", "tools/certify_books.py", "--dry-run"]
    for path in affected_by:
        words.extend(["--affected-by", path])
    if closure:
        words.append("--closure")
    words.extend(books)
    return words


def incremental(closure: bool, require_origin: str | None) -> bool:
    """Whether a run is the default incremental plan.

    Every run is, except root's from-scratch ``--closure`` and a run that
    demands one origin with ``--require-origin``.
    """
    return not closure and require_origin is None


def cache_preflight_script(host: str, remote: Path, books: list[str],
                           affected_by: list[str], closure: bool,
                           cache: str | None = None,
                           acl2: str | None = None,
                           require_origin: str | None = None) -> str:
    """Install from the box's cache before ACL2 starts, by the run's plan.

    The default, incremental plan (``certs.py install-partial``) installs
    every book of the selected roots' closure whose pair is cached at its
    current digest and ACL2 toolchain, selecting compatible certificate
    post-alists from available origins; the runner (``--incremental``)
    certifies the remainder.  It never refuses for a cache miss.  ACL2
    compares sub-books by familiar name, annotations and book-hash, never
    by full-book-name
    (``planning/evidence/certificate-cache-2026-09-23.md``).
    ``--require-origin`` demands one complete dependency set from that one
    origin and refuses otherwise.  ``--closure`` is root's explicit
    recertification plan and keeps the single-origin rule: it purges the
    closure on a miss and certifies it under ``remote``.
    """
    settings = host_settings(host, cache, acl2)
    select = " ".join(shlex.quote(word) for word in
                      selection_words(books, affected_by, closure))
    if closure:
        mode = (f"--require-origin {remote_quote(remote)} --purge-on-miss "
                "install-set")
    elif require_origin is not None:
        mode = (f"--require-origin {remote_quote(require_origin)} "
                "--dependencies-only install-set")
    else:
        mode = 'install-partial'
    return (
        f"cd {remote_quote(remote)} || exit 9; "
        f"roots=$({select}) || exit 13; "
        f"if [ -z \"$roots\" ]; then "
        "echo 'artifact-set EMPTY origin NONE source NONE toolchain NONE; "
        "installed 0, kept 0, missing 0, removed 0'; exit 0; fi; "
        f"acl2={acl2_shell_word(host, acl2)}; "
        "toolchain=$(python3 tools/acl2_toolchain.py identity \"$acl2\") "
        "|| exit 14; "
        f"python3 tools/certs.py --cache {remote_quote(settings['cache'])} "
        f"--toolchain-identity \"$toolchain\" --acl2 \"$acl2\" "
        f"{mode} $roots")


def install_from_cache(host: str, remote: Path, books: list[str],
                       affected_by: list[str], closure: bool,
                       cache: str | None = None,
                       acl2: str | None = None,
                       require_origin: str | None = None) -> dict[str, object]:
    """Install what the run's plan takes from the cache, or say why not.

    An incremental install refuses only when it did not run (no count line
    came back): a miss is what the runner certifies.
    """
    answer = ssh(host, cache_preflight_script(
        host, remote, books, affected_by, closure, cache, acl2,
        require_origin), check=False)
    counts = parse_installed(answer.stdout)
    if counts and answer.returncode == 0:
        return counts
    if closure and counts and answer.returncode == 1:
        # `--closure` is the explicit recertification plan.  install-set has
        # removed stale pairs for the exact closure; the dependency-ordered
        # runner will now author every pair under this one remote root.
        return counts | {"recertify_closure": True}
    detail = (answer.stdout.strip() or
              f"ssh exited {answer.returncode}")[-800:]
    if incremental(closure, require_origin):
        raise FarmError(
            f"{host}: installing from the cache did not complete under "
            f"{remote}; ACL2 was not started. Cache preflight: {detail}")
    raise FarmError(
        f"{host}: the cache holds no complete certificate set for the selected "
        f"roots' dependencies with this ACL2 toolchain, from one origin or "
        f"from {require_origin or 'this run root'}; ACL2 was not started "
        f"under {remote}. Without --require-origin the run installs what is "
        f"cached and certifies the rest. Cache preflight: {detail}")


def run_id() -> str:
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    return f"run-{stamp}-{secrets.token_hex(2)}"


def record_path(root: Path, identifier: str) -> Path:
    return root / "build" / "farm" / f"{identifier}.json"


def run_record(root: Path, identifier: str) -> dict:
    """What `submit` recorded for this run, or an empty mapping."""
    try:
        record = json.loads(record_path(root, identifier).read_text())
    except (OSError, ValueError):
        return {}
    return record if isinstance(record, dict) else {}


def remote_root(root: Path, identifier: str, override: str | None = None) -> Path:
    """Where the run lives on the box: the recorded path, or this one.

    Certificates name their sub-books by absolute path, so the path the run
    used on the box is what `certs.py` records as their origin.  When it is
    not a path on this machine, the pairs install into any worktree here.
    """
    if override:
        return Path(override)
    return Path(run_record(root, identifier).get("remote_path", str(root)))


def push(host: str, root: Path, remote: Path) -> None:
    """Mirror the worktree to `remote`, making the path first.

    rsync creates the last component of a destination and no more, so a
    `--remote-root` whose parent does not exist on the box fails with exit 11
    ("error in file IO") and nothing else.  One `mkdir -p` costs one ssh.
    """
    made = ssh(host, f"mkdir -p {remote_quote(remote)}", check=False)
    if made.returncode != 0:
        raise FarmError(f"{host}: cannot create {remote}: "
                        f"ssh exited {made.returncode}: {made.stdout.strip()}")
    command = ["rsync", "-a", "--delete"]
    for pattern in EXCLUDES:
        command.append(f"--exclude={pattern}")
    command.extend([f"{root}/", f"{host}:{remote}/"])
    mirrored = run(command, check=False)
    if mirrored.returncode != 0:
        raise FarmError(f"{host}: rsync to {remote} exited "
                        f"{mirrored.returncode}: {mirrored.stdout.strip()}")


def publishes(script: str) -> bool:
    """Would this runner script put certificates into a cache?

    The runner publishes each pair as it certifies unless `--no-publish` is
    on its command line, so that word is the whole difference between a run
    that seeds the box and one that does not.  `submit` checks this against
    the script it is about to start rather than against its own argument,
    which is the check `tools/triage.py` needs: a triage run certifies a
    tree whose sources have been substituted, and a pair from it is about a
    tree nobody has.
    """
    return "--no-publish" not in script


def remote_script(host: str, root: Path, identifier: str, books: list[str],
                  jobs: int, timeout_seconds: int, affected_by: list[str],
                  closure: bool = False, cache: str | None = None,
                  acl2: str | None = None, no_publish: bool = False,
                  pcert: bool = False, budget_seconds: int | None = None,
                  require_origin: str | None = None) -> str:
    """The submit script: every step that can fail exits with its own code.

    `cd X && ... &` backgrounds the whole list, so ssh returned 0 whatever
    happened -- a missing directory, a tree with no runner in it, a runner
    that died on its first line -- and `submit` printed a run id for a run
    that did not exist.  Each guard here is a distinct non-zero exit.

    `no_publish` passes `--no-publish` to the runner, which is what stops the
    per-book publication into the box's cache.  `pcert` runs the closure as
    ACL2's three provisional waves, whose Convert wave is where the proofs
    are and what `budget_seconds` bounds.
    """
    settings = host_settings(host, cache, acl2)
    runner = ["python3", "tools/certify_books.py", "--jobs", str(jobs)]
    for path in affected_by:
        runner.extend(["--affected-by", path])
    if closure:
        runner.append("--closure")
    elif incremental(closure, require_origin):
        runner.append("--incremental")
    if no_publish:
        runner.append("--no-publish")
    if pcert:
        runner.append("--pcert")
    if budget_seconds is not None:
        runner.extend(["--budget-seconds", str(budget_seconds)])
    runner.extend(books)
    if settings["wrap"]:
        runner = [settings["wrap"]] + runner
    log = f"build/farm/{identifier}.log"
    status_file = f"build/farm/{identifier}.status"
    inner = (
        f"FN_ACL2={acl2_shell_word(host, acl2)} "
        f"FN_ACL2_TIMEOUT_SECONDS={timeout_seconds} "
        f"FN_CERT_CACHE={settings['cache']} "
        # The runner publishes into the box's cache after each root.  This
        # run's tree is a snapshot: the pairs are shareable with the next
        # lane on the box, and saying so at publish time is what lets its
        # `install` take them.
        f"FN_CERT_ORIGIN_KIND=run "
        + " ".join(shlex.quote(word) for word in runner)
        + f" > {log} 2>&1; echo $? > {status_file}"
    )
    where = remote_quote(root)
    return (
        f"cd {where} || {{ echo \"fn-farm: no directory {root} on {host}\" >&2; exit 9; }}; "
        f"test -f tools/certify_books.py || "
        f"{{ echo \"fn-farm: no tools/certify_books.py under {root}\" >&2; exit 10; }}; "
        f"mkdir -p build/farm || "
        f"{{ echo \"fn-farm: cannot write build/farm under {root}\" >&2; exit 11; }}; "
        f"nohup sh -c {shlex.quote(inner)} >/dev/null 2>&1 & "
        f"pid=$!; sleep 2; "
        f"if ! kill -0 $pid 2>/dev/null && [ ! -s {status_file} ]; then "
        f"echo \"fn-farm: the runner for {identifier} did not start\" >&2; "
        f"tail -c 400 {log} >&2 2>/dev/null; exit 12; fi; "
        f"echo FN_FARM_STARTED {identifier} $pid"
    )


def submit(host: str, root: Path, books: list[str], jobs: int,
           timeout_seconds: int, affected_by: list[str],
           remote: Path | None = None, closure: bool = False,
           cache: str | None = None, acl2: str | None = None,
           no_publish: bool = False,
           prepare: Callable[[str, Path], None] | None = None,
           pcert: bool = False, budget_seconds: int | None = None,
           require_origin: str | None = None) -> str:
    """Mirror, install from the box's cache, and start the detached runner.

    `prepare(host, remote)` runs between the mirror and ACL2, on the box's
    copy only.  `tools/triage.py` substitutes a red book's last green source
    through this seam: the substitution has to be in the tree the runner
    reads, it must never be in this worktree, and `push`'s `--delete` would
    undo anything written before the mirror.

    `no_publish` is checked against the script that is about to run, not
    against the argument, so a runner invocation that would seed the box's
    cache cannot start under a caller that asked for no publication.
    """
    refuse_unmerged_source(root)
    identifier = run_id()
    remote = expand_remote(host, remote) if remote else root
    push(host, root, remote)
    if prepare is not None:
        prepare(host, remote)
    cached = install_from_cache(
        host, remote, books, affected_by, closure, cache, acl2, require_origin)
    print(f"{identifier}: from {host}'s cache, "
          + ", ".join(f"{name} {len(value)}" if name == "origins"
                      else f"{name} {value}" for name, value in cached.items()),
          file=sys.stderr)
    if cached.get("mode") == "incremental":
        print(f"{identifier}: installed {cached['installed'] + cached['kept']} "
              f"of {cached['books']} books from "
              f"{len(cached.get('origins') or {})} origin(s); certifying "
              f"{cached['certify']} ({cached['roots_installed']} of "
              f"{cached['roots']} roots already certified at these bytes)",
              file=sys.stderr)
    script = remote_script(host, remote, identifier, books, jobs,
                           timeout_seconds, affected_by, closure, cache, acl2,
                           no_publish, pcert, budget_seconds, require_origin)
    if no_publish and publishes(script):
        raise FarmError(
            f"{host}: {identifier} was asked not to publish and its runner "
            f"command would publish anyway; ACL2 was not started")
    started = ssh(host, script, check=False)
    if started.returncode != 0:
        raise FarmError(f"{host}: {identifier} did not start under {remote}: "
                        f"ssh exited {started.returncode}: "
                        f"{started.stdout.strip() or '(no output)'}")
    record = {
        "run_id": identifier,
        "host": host,
        "path": str(root),
        "remote_path": str(remote),
        "books": books,
        "affected_by": affected_by,
        "closure": closure,
        "incremental": incremental(closure, require_origin),
        "require_origin": require_origin,
        "no_publish": no_publish,
        "pcert": pcert,
        "budget_seconds": budget_seconds,
        # What the box's cache already held: the run certifies the rest.
        "cache_install": cached,
        "cache": host_settings(host, cache)["cache"],
        "acl2": acl2 or host_settings(host)["acl2"],
        "jobs": jobs,
        "timeout_seconds": timeout_seconds,
        "submitted_at": dt.datetime.now(dt.timezone.utc).isoformat(),
    }
    path = record_path(root, identifier)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n",
                    encoding="utf-8")
    return identifier


SUCCESS_LINE = r"^(ACL2 [^[:space:]]*>)?FN_CERTIFY_SUCCESS [0-9a-f]{32} [0-9a-f]{12}$"


def progress_script(root: Path, identifier: str) -> str:
    """The run's status file, its success count, its started count, its tail.

    The runner streams each ACL2's output into that book's own log under
    the run directory, `build/acl2/certify-<stamp>-<pid>/<book>.certify.log`,
    with a matching `.active.json` mapping the live child PID to its book;
    the farm log carries nothing per book until the end. Until 2026-09-22 this
    counted markers in the farm log and every progress line read "0 books certified" (three real runs
    checked, all 0).  The running run's directory is the newest one.
    """
    log = f"build/farm/{identifier}.log"
    newest = "$(ls -td build/acl2/certify-*/ 2>/dev/null | head -1)"
    return (
        f"cd {remote_quote(root)} 2>/dev/null || exit 9; "
        f"printf 'STATUS %s\\n' \"$(cat build/farm/{identifier}.status "
        f"2>/dev/null || echo running)\"; "
        f"d={newest}; "
        f"printf 'MARKERS %s\\n' \"$(grep -lE '{SUCCESS_LINE}' \"$d\"*.certify.log "
        f"2>/dev/null | wc -l | tr -d ' ')\"; "
        f"printf 'STARTED %s\\n' \"$(ls \"$d\"*.certify.log 2>/dev/null | wc -l "
        f"| tr -d ' ')\"; "
        f"printf 'TAIL %s\\n' \"$(tail -c 300 {log} 2>/dev/null | tr '\\n' ' ')\""
    )


def parse_progress(output: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for line in output.splitlines():
        for key in ("STATUS", "MARKERS", "STARTED", "TAIL"):
            if line.startswith(key + " "):
                fields[key] = line[len(key) + 1:].strip()
    return fields


def wait(host: str, identifier: str, root: Path, poll: int = POLL_SECONDS,
         timeout_seconds: int = DEFAULT_WAIT_SECONDS,
         cache: str | None = None,
         collect: Callable[[str, str, Path, Path, str | None], None] | None = None,
         remote: str | None = None,
         ) -> int:
    """Block until the remote run writes its status file, then fetch evidence.

    The timeout path fetches too.  Returning 3 without fetching loses every
    pair the run had already produced: the run keeps going on the box, and
    the next lane there re-certifies what this one had finished.  So the
    timeout brings home what exists at that moment and says what it left
    running, and the run id stays usable for a second `wait`.

    `collect` is what "fetch evidence" means for this caller, and it defaults
    to `fetch`.  `tools/triage.py` passes `fetch_logs`, which brings home the
    logs and the manifest and publishes nothing: the same wait, over a run
    whose output is not evidence.
    """
    collect = collect or fetch
    started = time.monotonic()
    # `--remote-root` names the gate the run lives in; without it the run
    # record's remote path decides.  Until 2026-09-23 this line ignored the
    # override and every wait on a run under another gate read a status file
    # that did not exist there, so it reported the run running forever.
    remote = remote_root(root, identifier, remote)
    cache = cache or run_record(root, identifier).get("cache")
    while True:
        progress = parse_progress(ssh(host, progress_script(remote, identifier),
                                      check=False).stdout)
        state = progress.get("STATUS", "running")
        if state != "running":
            break
        elapsed = int(time.monotonic() - started)
        print(f"{identifier} on {host}: running, {progress.get('MARKERS', '0')} "
              f"books certified of {progress.get('STARTED', '0')} started, "
              f"{elapsed}s elapsed", flush=True)
        if time.monotonic() - started >= timeout_seconds:
            print(f"{identifier} on {host}: still running after "
                  f"{timeout_seconds}s; not waiting further", file=sys.stderr)
            collect(host, identifier, root, remote, cache)
            print(f"{identifier} on {host}: left running under {remote}; "
                  f"{progress.get('MARKERS', '0')} books were certified when "
                  f"this wait gave up, and their pairs are fetched and "
                  f"published.  Run `farm.py wait {host} {identifier}` again "
                  f"for the rest.", file=sys.stderr)
            return 3
        SLEEP(poll)
    try:
        code = int(state)
    except ValueError:
        code = 1
    collect(host, identifier, root, remote, cache)
    print(f"{identifier} on {host}: finished with exit code {code}")
    return code


def fetch(host: str, identifier: str, root: Path,
          remote: Path | None = None, cache: str | None = None) -> None:
    """Bring back the evidence directory, the new pairs, and cache the pairs."""
    remote = remote or remote_root(root, identifier)
    cache = cache or run_record(root, identifier).get("cache")
    log = ssh(host, f"cat {remote_quote(remote)}/build/farm/{identifier}.log",
              check=False).stdout
    (root / "build" / "farm").mkdir(parents=True, exist_ok=True)
    (root / "build" / "farm" / f"{identifier}.log").write_text(log, encoding="utf-8")
    archived: dict[str, int] = {}
    for directory in sorted(set(EVIDENCE.findall(log))):
        local = root / directory
        local.mkdir(parents=True, exist_ok=True)
        run(["rsync", "-a", f"{host}:{remote}/{directory}/", f"{local}/"], check=False)
        # The fetched copy lands under `build/`, which is ignored and which a
        # worktree removal takes with it, so the manifest is also filed under
        # `planning/evidence/manifests/`.  Its `archived_from` names the box
        # and the remote directory, because that is where the log stayed.
        outcome = evidence_manifests.archive_run(
            local, root, f"{host}:{remote}/{directory}")
        archived[outcome] = archived.get(outcome, 0) + 1
    if archived:
        print("manifests archived under {}: {}".format(
            evidence_manifests.ARCHIVE_REL,
            ", ".join(f"{key} {value}" for key, value in sorted(archived.items()))))
    for directory in certs.BOOK_DIRECTORIES:
        run(["rsync", "-a", "--update", "--include=*/", "--include=*.cert",
             "--include=*.port", "--exclude=*",
             f"{host}:{remote}/{directory}/", f"{root}/{directory}/"], check=False)
    # The box keeps its own copy: the next lane there installs these instead
    # of certifying them again.  The runner publishes after each root, so this
    # is the sweep for a run whose last root, or whose own publish, failed.
    shared = ssh(host, certs_script(host, remote, "publish", "run", cache),
                 check=False)
    for line in shared.stdout.strip().splitlines():
        print(f"{host}: {line}")
    if shared.returncode != 0 or not shared.stdout.strip():
        # A `cd` that misses (exit 9) or an ssh that dies prints nothing, and
        # a silent sweep reads exactly like a sweep that found nothing to do.
        print(f"{host}: the cache sweep under {remote} exited "
              f"{shared.returncode} with no report; the run's pairs are NOT "
              f"in this box's cache", file=sys.stderr)
    # The pairs were produced under the *remote* path, which is what their
    # sub-book entries name; record that as their origin.
    manifests = certs.load_manifests(root)
    if not manifests:
        print(f"{identifier}: no certification manifest came back under "
              f"{root}/build/acl2; nothing to publish into the local cache",
              file=sys.stderr)
    report = certs.publish(root, certs.cache_directory(), manifests,
                           origin=str(remote), origin_host=host,
                           origin_kind="run")
    for line in report.lines():
        print(line)


def fetch_logs(host: str, identifier: str, root: Path, remote: Path,
               into: Path) -> list[Path]:
    """One run's per-book logs and manifest, brought home and nothing else.

    `fetch` is the evidence path: it archives the manifest under
    `planning/evidence/manifests/`, rsyncs the run's new certificate pairs
    into this worktree and publishes them to the box's cache and to the local
    one.  None of that may happen for a triage run, which certifies a tree
    whose sources have been substituted: its pairs are about a tree nobody
    has, and its manifest is not a claim about this revision.  This brings
    back the two files a triage round reads -- `manifest.json` and the
    `<book>.certify.log` per book -- into a directory the caller names, and
    touches neither cache.  The combined `certify.log` is excluded: it is the
    same bytes again, concatenated, and on a wide run it is hundreds of
    megabytes.
    """
    log = ssh(host, f"cat {remote_quote(remote)}/build/farm/{identifier}.log",
              check=False).stdout
    into.mkdir(parents=True, exist_ok=True)
    (into / f"{identifier}.log").write_text(log, encoding="utf-8")
    brought: list[Path] = []
    for directory in sorted(set(EVIDENCE.findall(log))):
        local = into / Path(directory).name
        local.mkdir(parents=True, exist_ok=True)
        run(["rsync", "-a", "--include=*/", "--include=manifest.json",
             "--include=*.certify.log", "--exclude=*",
             f"{host}:{remote}/{directory}/", f"{local}/"], check=False)
        brought.append(local)
    return brought


STATUS_SNAPSHOT = r'''
import datetime as dt
import json
from pathlib import Path
import re

root = Path.cwd()
farm = root / "build/farm"
stamp = re.compile(r"(?:run|certify)-(\d{8}T\d{6}Z)-")

def read_json(path):
    try:
        value = json.loads(path.read_text())
    except (OSError, ValueError):
        return None
    return value if isinstance(value, dict) else None

def time_of(path):
    found = stamp.match(path.name)
    return (dt.datetime.strptime(found.group(1), "%Y%m%dT%H%M%SZ")
            .replace(tzinfo=dt.timezone.utc) if found else None)

logs = sorted(farm.glob("run-*.log"))
dirs = sorted((path for path in (root / "build/acl2").glob("certify-*")
               if path.is_dir()), key=lambda path: path.name)
now = dt.datetime.now(dt.timezone.utc)
rows = []
for log in logs:
    started = time_of(log)
    if started is None:
        continue
    next_starts = [value for value in (time_of(other) for other in logs)
                   if value is not None and value > started]
    cutoff = min(next_starts) if next_starts else started + dt.timedelta(minutes=15)
    cutoff = min(cutoff, started + dt.timedelta(minutes=15))
    # The runner creates one certify directory soon after submit. Do not
    # borrow an old directory or guess when concurrent directories overlap.
    matching = [path for path in dirs if (when := time_of(path)) is not None
                and started <= when < cutoff]
    directory = matching[0] if len(matching) == 1 else None
    status_file = log.with_suffix(".status")
    state = status_file.read_text().strip() if status_file.exists() else "unfinalized"
    row = {"run_id": log.stem, "state": state, "data": "missing"}
    if directory is not None and state != "unfinalized":
        manifest = read_json(directory / "manifest.json")
        if manifest is not None:
            row.update(data="manifest", manifest=manifest.get("status", "unknown"),
                       active=0, age_seconds=None)
            results = manifest.get("book_results")
            if isinstance(results, dict):
                row.update(passed=sum(value == "passed" for value in results.values()),
                           failed=sum(value == "failed" for value in results.values()))
    elif directory is not None:
        activities = [value for path in directory.glob("*.active.json")
                      if (value := read_json(path)) is not None]
        if activities:
            ages = []
            for activity in activities:
                if activity.get("status") == "running":
                    try:
                        began = dt.datetime.fromisoformat(activity["started_utc"])
                        ages.append(max(0, int((now - began).total_seconds())))
                    except (KeyError, TypeError, ValueError):
                        pass
            row.update(data="observed",
                       exited=sum(value.get("status") in ("exited", "timed-out")
                                  for value in activities),
                       active=sum(value.get("status") == "running" for value in activities),
                       age_seconds=max(ages) if ages else None)
    rows.append(row)
print(json.dumps(rows))
'''


def status_script(root: Path) -> str:
    """Read one remote snapshot; never start a proof or publish a pair."""
    return f"cd {remote_quote(root)} && python3 -c {shlex.quote(STATUS_SNAPSHOT)}"


def status(host: str, remote: Path, local_root: Path | None = None) -> int:
    result = ssh(host, status_script(remote), check=False)
    if result.returncode != 0:
        raise FarmError(f"{host}: cannot read status under {remote}: "
                        f"{result.stdout.strip() or f'ssh exited {result.returncode}'}")
    try:
        rows = json.loads(result.stdout)
    except ValueError as error:
        raise FarmError(f"{host}: invalid status snapshot under {remote}: {error}") from error
    print(f"{host}:{remote}")
    print("run-id state data manifest-passed manifest-failed observed-exited "
          "observed-active oldest-observed-active cache-installed+kept/origins")
    for row in rows:
        identifier = row["run_id"]
        cache = cache_summary(run_record(local_root or remote, identifier)) or "-"
        age = (f"{row['age_seconds']}s" if row.get("age_seconds") is not None
               else "-")
        counts = [str(row.get(key, "-")) for key in
                  ("passed", "failed", "exited", "active")]
        label = row["data"]
        if label == "manifest":
            label += f"({row['manifest']})"
        print(" ".join([identifier, row["state"], label, *counts, age, cache]))
    return 0


def cache_summary(record: dict) -> str:
    """What `submit` installed for a run, from its local record, in one word.

    ``installed+kept/origins`` -- e.g. ``230+4/3`` is 234 dependency pairs
    taken from the cache, composed from three origins.  A run with no local
    record (another worktree submitted it) prints nothing.
    """
    found = record.get("cache_install")
    if not isinstance(found, dict):
        return ""
    origins = found.get("origins")
    count = len(origins) if isinstance(origins, dict) else (1 if found.get("origin") else 0)
    return f"{found.get('installed', 0)}+{found.get('kept', 0)}/{count}"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("action", choices=("submit", "wait", "status"))
    parser.add_argument("host")
    parser.add_argument("rest", nargs="*",
                        help="submit: book roots; wait: the run id")
    parser.add_argument("--jobs", type=int,
                        default=int(os.environ.get("FN_CERTIFY_JOBS", "8")))
    parser.add_argument("--affected-by", action="append", default=[],
                        help="certify the Makefile roots whose closure contains "
                             "this book (repeatable)")
    parser.add_argument("--closure", action="store_true",
                        help="also certify what those roots include, in "
                             "dependency order: the box then needs no "
                             "certificate of its own")
    parser.add_argument("--require-origin", default=None, metavar="ORIGIN",
                        help="install the roots' dependencies as one complete "
                             "set from this one origin (an absolute run root on "
                             "the host) and refuse if it lacks any, instead of "
                             "the default: install what is cached from any "
                             "snapshot origin and certify the rest")
    parser.add_argument("--timeout-seconds", type=int, default=1800,
                        help="per-ACL2-invocation timeout on the host")
    parser.add_argument("--wait-seconds", type=int, default=DEFAULT_WAIT_SECONDS,
                        help="how long `wait` blocks before giving up")
    parser.add_argument("--poll-seconds", type=int, default=POLL_SECONDS)
    parser.add_argument("--cache", default=None,
                        help="the certificate cache to use ON THE HOST "
                             "(default: the box's own; `submit` records it "
                             "and `wait` reuses what was recorded)")
    parser.add_argument("--acl2", default=None,
                        help="exact ACL2 executable path ON THE HOST for submit "
                             "(default: the host's configured executable)")
    parser.add_argument("--root", default=str(ROOT))
    parser.add_argument("--remote-root", default=None,
                        help="the path to use on the host (default: --root); a "
                             "path that does not exist here makes the resulting "
                             "certificates installable in any local worktree")
    arguments = parser.parse_args(argv)
    root = Path(arguments.root).resolve()
    try:
        if arguments.action == "submit":
            identifier = submit(arguments.host, root, list(arguments.rest),
                                arguments.jobs, arguments.timeout_seconds,
                                list(arguments.affected_by),
                                Path(arguments.remote_root) if arguments.remote_root
                                else None,
                                arguments.closure, arguments.cache,
                                arguments.acl2,
                                require_origin=arguments.require_origin)
            print(identifier)
            return 0
        if arguments.action == "wait":
            if len(arguments.rest) != 1:
                parser.error("wait takes exactly one run id")
            return wait(arguments.host, arguments.rest[0], root,
                        arguments.poll_seconds, arguments.wait_seconds,
                        arguments.cache,
                        remote=(str(expand_remote(arguments.host, arguments.remote_root))
                                if arguments.remote_root else None))
        remote = (expand_remote(arguments.host, arguments.remote_root)
                  if arguments.remote_root else root)
        return status(arguments.host, remote, root)
    except FarmError as error:
        print(str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
