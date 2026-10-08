#!/usr/bin/env python3
"""Is this book certified AT ITS CURRENT CLOSURE KEY, on the record toolchain?

"Certified" means one thing: the record box's certificate cache holds an entry
at the book's current closure key (`certs.closure_key`: the read forms of the
book and everything it includes, plus the world it was certified in) whose
`toolchain_identity` is the record toolchain's.  The record toolchain is
hbox's `w28` launcher; persvati shares it byte for byte (`farm.HOSTS`), so it
answers identically and is the fallback.  A laptop (darwin arm64) entry never
counts: its identity is a different toolchain's.

    python3 tools/green_check.py --summary   # the lines `make check` prints
    python3 tools/green_check.py --table     # every book, not certified first
    python3 tools/green_check.py --json      # the same records, machine-readable
    python3 tools/green_check.py --strict    # exit 1 unless every book is certified
    python3 tools/green_check.py --profile default --strict
                                             # the release gate: every book in the
                                             # native image profile's include
                                             # closure, exit 1 unless all are
    python3 tools/green_check.py --changed-since dev --strict
                                             # the merge gate: the books this
                                             # branch changed, every book that
                                             # includes one, and each verdict
    --cache DIR [--identity ID]              # answer from a local cache (a box
                                             # asking itself) instead of ssh
    --box hbox|persvati                      # which box to ask (default hbox;
                                             # persvati when hbox is unreachable,
                                             # said on stderr)

WHAT IT MEASURES.  Every root in the Makefile's `ACL2_BOOKS` and every book in
those roots' local include closure, read through the one closure walker
(`tools/certs.py`) and the one root list (`tools/ledger.py`) that the
certification runner uses.  For each book it computes the closure key in every
world a certificate of it may have been made in (`certs.book_entries`' loop)
and asks the cache, in ONE ssh call per process, which of those keys hold an
entry at the record identity.  An entry counts when its `book.cert` still
hashes to the `cert_sha256` its `meta.json` names.

  green          such an entry exists.
  uncertified    none does: the book, or something it includes, changed since
                 it was last certified, or it never was.  The cache keys by
                 content, so it cannot say which; a convergence report with
                 the farm log can.

WHAT IT DOES NOT SHOW.  An entry is a certificate made on the record
toolchain, not a certificate in this worktree (`certs.py install` does that),
and it says nothing about images or saved cores.  The `.fasl`, `.port` and
the other entry files are not re-hashed here; install does.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import inspect
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import acl2_toolchain  # noqa: E402
import cert_images  # noqa: E402
import certs  # noqa: E402
import unhooked  # noqa: E402
import ledger  # noqa: E402

ORDER = {"uncertified": 0, "unknown": 0, "absent": 1, "green": 2}

# The record toolchain's launcher: tools/farm.py HOSTS["hbox"]["acl2"] (a test
# pins them equal; farm is not imported here because it is heavy).
RECORD_LAUNCHER = "/tank/fn/toolchains/w28/acl2-literal-4g-tls64k"
# Local mirrors without that launcher require --identity. A hardcoded digest
# silently became stale when :FN changed the proof-environment contract.
RECORD_BOX = "hbox"
FALLBACK_BOX = "persvati"
SSH = ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=10"]
SSH_SECONDS = 300


class CacheUnavailable(RuntimeError):
    """No cache could answer: the record boxes are unreachable, or the local
    cache or identity is unusable.  Never read as `uncertified`."""


def scan(cache: str, keys: list[str], identity: str | None) -> dict:
    """For each closure key, the newest entry at IDENTITY whose cert verifies.

    Stdlib only and self-contained: `Cache` ships this function's source to
    the record box.  Entries live at `<cache>/<key>/<origin>/meta.json`; an
    entry counts when `meta.json` names IDENTITY as its toolchain and
    `book.cert` hashes to the `cert_sha256` it records (certs.entry_matches_meta
    without the fasl and port, which install re-checks).  Returns
    {key: {meta fields}} for keys with a hit.
    """
    import hashlib
    import json
    import os

    found = {}
    base = os.path.expanduser(cache)
    for key in keys:
        directory = os.path.join(base, key)
        try:
            origins = sorted(os.listdir(directory))
        except OSError:
            continue
        best = None
        for origin in origins:
            entry = os.path.join(directory, origin)
            try:
                with open(os.path.join(entry, "meta.json"), encoding="utf-8") as handle:
                    meta = json.load(handle)
                if not isinstance(meta, dict) or meta.get("toolchain_identity") != identity:
                    continue
                digest = hashlib.sha256()
                with open(os.path.join(entry, "book.cert"), "rb") as cert:
                    for chunk in iter(lambda: cert.read(1 << 20), b""):
                        digest.update(chunk)
                if meta.get("cert_sha256") and digest.hexdigest() != meta["cert_sha256"]:
                    continue
            except (OSError, ValueError):
                continue
            row = {"toolchain_identity": identity, "origin": origin,
                   "published_at": str(meta.get("published_at", "")),
                   "origin_host": meta.get("origin_host"),
                   "cert_sha256": meta.get("cert_sha256"), "book": meta.get("book")}
            if best is None or row["published_at"] >= best["published_at"]:
                best = row
        if best is not None:
            found[key] = best
    return found


def remote_script(cache: str, launcher: str, keys: list[str]) -> str:
    """The program the record box runs: compute its own record identity from
    its launcher (acl2_toolchain, shipped verbatim), then `scan`."""
    toolchain = Path(inspect.getsourcefile(acl2_toolchain)).read_text(encoding="utf-8")
    return "\n".join([
        "from __future__ import annotations",
        "import json, sys, types",
        "from pathlib import Path",
        "tc = types.ModuleType('acl2_toolchain')",
        "sys.modules['acl2_toolchain'] = tc",
        f"exec(compile({toolchain!r}, 'acl2_toolchain.py', 'exec'), tc.__dict__)",
        inspect.getsource(scan),
        f"identity = tc.fingerprint(Path({launcher!r})).identity",
        f"hits = scan({cache!r}, json.loads({json.dumps(keys)!r}), identity)",
        "print(json.dumps({'identity': identity, 'hits': hits}))",
    ])


class Cache:
    """One cache answering `which of these keys are certified on the record
    toolchain`.  `local` is a directory (a box asking its own cache, or a test
    fixture) read with `identity`; otherwise the record box is asked over ssh,
    hbox first and persvati when hbox cannot be reached.  Answers are
    remembered, so a process asks each key once."""

    def __init__(self, box: str | None = None, local: Path | str | None = None,
                 identity: str | None = None) -> None:
        self.box, self.local, self.identity = box, local, identity
        self.answered: dict[str, dict | None] = {}
        self.source = ""

    def describe(self) -> str:
        return self.source or (f"local cache {self.local}" if self.local
                               else f"{self.box or RECORD_BOX} (not yet asked)")

    def ask(self, keys: list[str]) -> None:
        wanted = sorted(set(keys) - self.answered.keys())
        if not wanted:
            return
        if self.local is not None:
            hits = scan(str(self.local), wanted, self.local_identity())
            self.source = f"local cache {self.local}"
        else:
            hits = self.ask_box(wanted)
        for key in wanted:
            self.answered[key] = hits.get(key)

    def local_identity(self) -> str:
        if self.identity is None:
            found = acl2_toolchain.fingerprint(Path(RECORD_LAUNCHER))
            if found.identity is None:
                raise CacheUnavailable("local mirror needs --identity from the record "
                                       "toolchain; its launcher is unavailable here")
            self.identity = found.identity
        return self.identity

    def ask_box(self, keys: list[str]) -> dict:
        boxes = [self.box] if self.box else [RECORD_BOX, FALLBACK_BOX]
        failures = []
        for box in boxes:
            script = remote_script(certs.REMOTE_CACHES[box], RECORD_LAUNCHER, keys)
            try:
                done = subprocess.run([*SSH, box, "python3", "-"], input=script,
                                      capture_output=True, text=True, timeout=SSH_SECONDS)
            except subprocess.TimeoutExpired:
                failures.append(f"{box}: no answer in {SSH_SECONDS}s")
                continue
            if done.returncode != 0:
                failures.append(f"{box}: ssh exit {done.returncode}: "
                                f"{done.stderr.strip().splitlines()[-1:] or ['']}")
                continue
            answer = json.loads(done.stdout.splitlines()[-1])
            if not answer.get("identity"):
                failures.append(f"{box}: {RECORD_LAUNCHER} is not a qualified launcher there")
                continue
            self.source = f"{box} certcache, record identity {answer['identity'][:12]}"
            if failures:
                print(f"green-check: {'; '.join(failures)}; answered by {box}",
                      file=sys.stderr)
            self.identity = answer["identity"]
            return answer["hits"]
        raise CacheUnavailable("no record box answered: " + "; ".join(failures))

    def hit(self, key: str) -> dict | None:
        return self.answered.get(key)


_DEFAULT: Cache | None = None


def configure(box: str | None = None, cache: str | None = None,
              identity: str | None = None) -> Cache:
    """Set the cache every `audit` without an explicit `cache=` asks."""
    global _DEFAULT
    _DEFAULT = Cache(box=box, local=cache, identity=identity)
    return _DEFAULT


def default_cache() -> Cache:
    return _DEFAULT if _DEFAULT is not None else configure()


def add_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--cache", metavar="DIR", default=None,
                        help="answer from this local cache directory instead of "
                             "asking a record box over ssh")
    parser.add_argument("--identity", metavar="ID", default=None,
                        help="with --cache: the record toolchain identity "
                             "(default: this machine's own record launcher)")
    parser.add_argument("--box", metavar="BOX", default=None,
                        choices=sorted(certs.REMOTE_CACHES),
                        help="the record box to ask (default hbox, persvati "
                             "when hbox is unreachable)")


def configure_from(args: argparse.Namespace) -> Cache:
    return configure(box=args.box, cache=args.cache, identity=args.identity)


def green_at_these_bytes(record: dict | None) -> bool:
    """THE meaning of "certified": the record box's cert cache holds an entry
    at the book's current closure key made on the record toolchain.
    planning/proofs.json's status is computed from it (tools/ledger.py
    derived_status); no other rule says "certified"."""
    return standing(record) == "green"


def standing(record: dict | None) -> str:
    """Every gate's answer for one book: `green`, `uncertified`, or `absent`
    (no record: unmeasured is not clean, S009)."""
    if not record:
        return "absent"
    return record.get("verdict") or "absent"


def standing_counts(records) -> dict[str, int]:
    counted: dict[str, int] = {}
    for record in records:
        name = standing(record)
        counted[name] = counted.get(name, 0) + 1
    return counted


@dataclass
class Record:
    """One book's standing: what it hashes to now and the cache entry for it."""

    book: str
    digest: str
    keys: list[str]
    verdict: str = "uncertified"
    hit: dict | None = None
    hit_key: str | None = None
    problem: str = ""

    def note(self) -> str:
        if self.verdict == "green":
            return (f"cache entry {self.hit_key[:12]} published "
                    f"{self.hit.get('published_at') or 'unknown-time'} from "
                    f"{self.hit.get('origin_host') or 'unknown-host'}")
        return self.problem or "no record-toolchain cache entry at the current closure key"


def audit(root: Path = ROOT, roots: list[str] | None = None,
          include_local: bool = True, cache: Cache | None = None,
          unknown_ok: bool = False) -> dict:
    """Every root and every book those roots include, judged at its closure key.

    `roots` defaults to the Makefile's `ACL2_BOOKS`; scoped queries pass
    explicit roots and every selected root's complete include closure is still
    judged.  `include_local` is accepted for old callers and ignored: nothing
    local is read any more.
    """
    cache = cache or default_cache()
    roots = list(roots) if roots is not None else ledger.makefile_roots()
    digests: dict[str, str] = {}
    for name in roots:
        digests.update(certs.closure(root, name))
    records: dict[str, Record] = {}
    for book, digest in digests.items():
        try:
            keys = [certs.closure_key(root, book, world)[0]
                    for world in cert_images.worlds(root.resolve(), book)]
            records[book] = Record(book=book, digest=digest, keys=keys)
        except (certs.UnreadableBook, cert_images.UnreadableSource) as error:
            records[book] = Record(book=book, digest=digest, keys=[],
                                   problem=f"cannot compute a closure key: {error}")
    unknown = ""
    try:
        cache.ask([key for record in records.values() for key in record.keys])
    except CacheUnavailable as error:
        if not unknown_ok:
            raise
        unknown = str(error)
        for record in records.values():
            record.verdict, record.problem = "unknown", f"cache unavailable: {error}"
    for record in records.values():
        for key in ([] if unknown else record.keys):
            if cache.hit(key) is not None:
                record.verdict, record.hit, record.hit_key = "green", cache.hit(key), key
                break
    counts = {name: sum(1 for record in records.values() if record.verdict == name)
              for name in ("green", "uncertified", "unknown")}
    return {
        "schema": "fn-green-check-v2",
        "roots": len(roots),
        "books": len(records),
        "cache": f"UNKNOWN ({unknown})" if unknown else cache.describe(),
        "record_identity": cache.identity,
        "counts": counts,
        "standing_counts": standing_counts(
            {"verdict": record.verdict} for record in records.values()),
        "books_by_verdict": {
            record.book: {
                "verdict": record.verdict,
                "digest_sha256": record.digest,
                "note": record.note(),
                "closure_key": record.hit_key,
                "cache_entry": record.hit,
            }
            for record in sorted(records.values(),
                                 key=lambda r: (ORDER[r.verdict], r.book))
        },
    }


# Every directory whose `.lisp` files can sit in a book's include closure:
# books include host files (books/image-world-dtn includes
# ../host/page-read-host), so a host edit moves their certificate key (S056).
CLOSURE_DIRS = ("books", "tests/acl2", "host")
ROOT_DIRS = ("books/", "tests/acl2/")


def changed_books(root: Path, rev: str) -> list[str]:
    """Every closure source (book, test book or host include) whose bytes
    differ from `rev`'s merge base, untracked new files included.

    Working tree against the merge base, so an uncommitted edit counts: the
    question is what a merge would carry, and a lane's tree is what it has.
    `git diff` does not list an untracked file, so a new book nobody `git
    add`ed is read from `git ls-files --others` (S056).
    """
    def git(*words: str) -> list[str]:
        return subprocess.run(["git", *words], cwd=root, capture_output=True,
                              text=True, check=True).stdout.splitlines()
    base = git("merge-base", rev, "HEAD")[0].strip()
    names = git("diff", "--name-only", base, "--", *CLOSURE_DIRS)
    names += git("ls-files", "--others", "--exclude-standard", "--", *CLOSURE_DIRS)
    return sorted({name[:-5] for name in names if name.endswith(".lisp")})


def certifiable(changed: list[str]) -> list[str]:
    """The changed sources a certification run can request as roots; a host
    include is judged only through the books whose closure reaches it."""
    return [name for name in changed if name.startswith(ROOT_DIRS)]


def dependents(root: Path, report: dict, changed: list[str]) -> dict[str, list[str]]:
    """Every audited book whose include closure reaches a changed book.

    Read through the one closure walker the runner uses, so "depends on" here
    is exactly what `include-book` will ask a certificate for.
    """
    wanted = set(changed)
    found: dict[str, list[str]] = {}
    for book in report["books_by_verdict"]:
        # Host include files contribute dependency bytes to a certifiable
        # book, but certify_books cannot request them as independent roots.
        if not book.startswith(("books/", "tests/acl2/")):
            continue
        if book in wanted:
            continue
        reached = sorted(wanted & set(certs.closure(root, book)))
        if reached:
            found[book] = reached
    return found


def changed_scope(root: Path, changed: list[str], roots: list[str]) -> tuple[list[str], dict]:
    """Select affected rooted books before evidence/form-hash auditing."""
    if not changed:
        return [], {}
    graph = certs.include_graph(root, roots)
    reverse = {}
    for parent, children in graph.items():
        for child in children:
            reverse.setdefault(child, set()).add(parent)
    wanted = set(changed)
    affected = set(wanted & graph.keys())
    pending = list(wanted)
    while pending:
        for parent in reverse.get(pending.pop(), ()):
            if parent not in affected:
                affected.add(parent)
                pending.append(parent)
    selected = sorted(book for book in affected if book.startswith(ROOT_DIRS))
    deps = {}
    for book in selected:
        if book in wanted:
            continue
        seen, todo = set(), [book]
        while todo:
            item = todo.pop()
            if item not in seen:
                seen.add(item)
                todo.extend(graph.get(item, ()))
        deps[book] = sorted(wanted & seen)
    return selected, deps



def gate(report: dict, changed: list[str], deps: dict[str, list[str]],
         unhooked_books: dict[str, str] | None = None) -> dict:
    """The merge gate's answer: each changed book and dependent with its verdict.

    Finding F4 of planning/review-2026-09-22-proof-engineering.md: on
    2026-09-21 five commits changed the machine under invariant books nobody
    recertified, and `git log` read as green.  A branch that touched a book
    merges when that book and everything that includes it are green at the
    bytes the merge will carry, or it waits.  A book not in the audit's
    closure (a test book no root names) is reported as `unaudited`, which is
    not green, unless planning/unhooked.json lists it: then it is
    `unhooked (Dnn)`, the decision's, and is not counted as not green.
    """
    verdicts = report["books_by_verdict"]
    listed = unhooked.load(ROOT) if unhooked_books is None else unhooked_books

    def verdict(book: str) -> str:
        entry = verdicts.get(book)
        if entry is None:
            if book in listed:
                return f"unhooked ({listed[book]})"
            return "unaudited"
        return standing(entry)

    rows = [{"book": book, "role": "changed", "verdict": verdict(book), "via": []}
            for book in changed]
    rows += [{"book": book, "role": "dependent", "verdict": verdict(book), "via": via}
             for book, via in sorted(deps.items())]
    not_green = [row["book"] for row in rows
                 if row["verdict"] != "green" and not row["verdict"].startswith("unhooked (")]
    return {"schema": "fn-green-gate-v1", "changed": changed,
            "dependents": len(deps), "rows": rows, "not_green": not_green}


def gate_lines(answer: dict) -> list[str]:
    lines = [f"green-gate: {len(answer['changed'])} changed books, "
             f"{answer['dependents']} books include one; "
             f"{len(answer['not_green'])} not green at the bytes a merge would carry."]
    width = max((len(row["book"]) for row in answer["rows"]), default=4)
    for row in answer["rows"]:
        via = (" <- " + " ".join(row["via"])) if row["via"] else ""
        lines.append(f"  {row['verdict']:9} {row['role']:9} {row['book']:{width}}{via}")
    for name in answer.get("changed_host", []):
        lines.append(f"  {'host':9} {'changed':9} {name} (judged through the books "
                     f"that include it)")
    if not answer["rows"] and not answer.get("changed_host"):
        lines.append("  no book, test book or host include differs from the merge base")
    return lines


def profile_gate(report: dict, profile: str, root: Path = ROOT,
                 roots: list[str] | None = None) -> dict:
    """The release gate: the standing of every book in the include closure of
    a native image profile's roots (tools/proof_artifacts.py's roots, the same
    closure its acquire loads).  Green means `green_at_these_bytes`:
    `uncertified` and `absent` both fail it (S009).
    `roots` is passed only by a test standing up a synthetic tree."""
    if roots is None:
        import proof_artifacts  # noqa: E402  (same directory)
        roots = proof_artifacts.profile_roots(root, profile)
    closure = sorted(name.removesuffix(".lisp")
                     for name in certs.required_closure(root, roots))
    by = report["books_by_verdict"]
    rows = [{"book": book, "verdict": standing(by.get(book))} for book in closure]
    not_green = [row["book"] for row in rows if row["verdict"] != "green"]
    return {"schema": "fn-green-profile-v1", "profile": profile, "roots": len(roots),
            "books": len(rows), "not_green": not_green, "rows": rows}


def by_standing(rows: list[dict]) -> str:
    """`uncertified=3 absent=2 ...` over the rows that are not green."""
    counted: dict[str, int] = {}
    for row in rows:
        if row["verdict"] != "green":
            counted[row["verdict"]] = counted.get(row["verdict"], 0) + 1
    return " ".join(f"{name}={count}" for name, count in sorted(counted.items())) or "none"


def profile_lines(answer: dict) -> list[str]:
    shown = " ".join(answer["not_green"][:8]) or "none"
    more = (f" (+{len(answer['not_green']) - 8} more)"
            if len(answer["not_green"]) > 8 else "")
    return [f"green-check profile={answer['profile']}: {answer['books']} books in the "
            f"closure of {answer['roots']} roots, "
            f"{answer['books'] - len(answer['not_green'])} green at their current "
            f"closure key on the record toolchain; not green "
            f"({by_standing(answer['rows'])}): {shown}{more}"]


def strict_rows(report: dict) -> list[dict]:
    """Every audited book under `standing`: what bare `--strict` judges."""
    return [{"book": book, "verdict": standing(entry)}
            for book, entry in report["books_by_verdict"].items()]


def strict_lines(rows: list[dict]) -> list[str]:
    bad = [row["book"] for row in rows if row["verdict"] != "green"]
    shown = " ".join(bad[:8]) or "none"
    more = f" (+{len(bad) - 8} more; --table for all)" if len(bad) > 8 else ""
    return [f"green-check strict: {len(bad)} of {len(rows)} books not green at "
            f"their closure key on the record toolchain "
            f"({by_standing(rows)}): {shown}{more}"]


def worklist(report: dict) -> list[str]:
    """The books the certification lanes owe a run."""
    return [book for book, entry in report["books_by_verdict"].items()
            if standing(entry) in ("uncertified", "absent", "unknown")]


def summary(report: dict) -> list[str]:
    counts = report["standing_counts"]
    owed = worklist(report)
    shown = " ".join(owed[:8]) or "none"
    more = f" (+{len(owed) - 8} more; --table for all)" if len(owed) > 8 else ""
    return [
        f"green-check: {report['books']} books in the closure of "
        f"{report['roots']} Makefile roots -- {counts.get('green', 0)} certified "
        f"at their current closure key, {counts.get('uncertified', 0)} not, "
        f"{counts.get('unknown', 0)} unknown (no cache reachable).",
        f"green-check: owed a certification: {shown}{more}",
        f"green-check: asked {report['cache']}.  An entry is a certificate made "
        f"on the record toolchain, not one in this tree, and says nothing about images.",
    ]


def table(report: dict) -> list[str]:
    width = max((len(book) for book in report["books_by_verdict"]), default=4)
    lines = [f"{'VERDICT':7}  {'BOOK':{width}}  DIGEST    EVIDENCE"]
    for book, entry in report["books_by_verdict"].items():
        lines.append(f"{entry['verdict']:7}  {book:{width}}  "
                     f"{entry['digest_sha256'][:8]}  {entry['note']}")
    return lines


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Which books have a record-toolchain cache entry at their current closure key.")
    parser.add_argument("--summary", action="store_true",
                        help="the lines `make check` prints")
    parser.add_argument("--table", action="store_true",
                        help="every book, not certified first")
    parser.add_argument("--json", action="store_true",
                        help="the whole audit as one JSON object")
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 unless every audited book is green at its "
                             "current closure key on the record toolchain "
                             "(uncertified and absent fail); with --changed-since "
                             "or --profile, the same rule over that gate's books")
    add_arguments(parser)
    parser.add_argument("--changed-since", metavar="REV", default=None,
                        help="the merge gate: the books this tree changed since "
                             "its merge base with REV, the books that include "
                             "them, and each one's verdict")
    parser.add_argument("--profile", metavar="NAME", default=None,
                        help="the release gate: every book in the include closure "
                             "of this native image profile (default, dtn); with "
                             "--strict, exit 1 unless every one is green")
    args = parser.parse_args(argv)

    configure_from(args)
    changed, deps = [], {}
    try:
        if args.profile:
            import proof_artifacts
            report = audit(root=ROOT, roots=proof_artifacts.profile_roots(ROOT, args.profile),
                           unknown_ok=True)
        elif args.changed_since:
            changed = changed_books(ROOT, args.changed_since)
            selected, deps = changed_scope(ROOT, changed, ledger.makefile_roots())
            report = audit(root=ROOT, roots=selected, unknown_ok=True) if selected else {"books_by_verdict": {}}
        else:
            report = audit(root=ROOT, unknown_ok=True)
    except subprocess.CalledProcessError as error:
        print(f"green-check: git cannot resolve {args.changed_since}: "
              f"{error.stderr.strip()}", file=sys.stderr)
        return 2
    except CacheUnavailable as error:
        print(f"green-check: no answer from the cert cache: {error}", file=sys.stderr)
        return 2
    except (certs.UnreadableBook, ValueError, OSError) as error:
        print(f"green-check: cannot read this tree: {error}", file=sys.stderr)
        return 2

    if any(entry.get("verdict") == "unknown"
           for entry in report.get("books_by_verdict", {}).values()):
        # Uncertain stays distinct from red (1) and from usage errors (2):
        # an unreachable box never turns a certification step green.
        print("green-check: UNKNOWN: no record cache reachable (tried hbox, persvati); "
              "pass --cache DIR for a local mirror", file=sys.stderr)
        return 3

    if args.profile:
        answer = profile_gate(report, args.profile, root=ROOT)
        print(json.dumps(answer, indent=1, sort_keys=True) if args.json
              else "\n".join(profile_lines(answer)))
        return 1 if args.strict and answer["not_green"] else 0

    if args.changed_since:
        answer = gate(report, certifiable(changed), deps)
        answer["changed_host"] = [name for name in changed
                                  if name not in answer["changed"]]
        if args.json:
            print(json.dumps(answer, indent=1, sort_keys=True))
        else:
            print("\n".join(gate_lines(answer)))
        return 1 if args.strict and answer["not_green"] else 0

    if args.json:
        print(json.dumps(report, indent=1, sort_keys=True))
    elif args.table:
        print("\n".join(table(report)))
    if args.summary or not (args.json or args.table):
        print("\n".join(summary(report)))
    if not args.strict:
        return 0
    rows = strict_rows(report)
    if not args.json:
        print("\n".join(strict_lines(rows)))
    return 1 if any(row["verdict"] != "green" for row in rows) else 0


if __name__ == "__main__":
    raise SystemExit(main())
