#!/usr/bin/env python3
"""Render the current view of each capability (prints it; --write saves build/current.md).

The review of 2026-09-24 (planning/review-2026-09-24-gpt6-direction.md, "A
small evidence-maintenance repair") asks for a short current view beside the
immutable evidence records. This writes one record per capability from
planning/current-view.json and the tree, and keeps four evidence coordinates
apart:

- implemented: the host-called subject is called on this revision
  (file:line found in host/) and the keystone exists (ledger parser);
- proved: the record box's cert cache holds an entry for the keystone's book
  at its current closure key, made on the record toolchain
  (green_check.green_at_these_bytes);
- qualified: the tested image's pinned digests (`--pin-image`, read from its
  source revision) hold the keystone's book (and the bridge's book and the
  host file) at the same source digest as this revision, i.e. the qualified
  image carries the source this view describes;
- deployed: the same comparison against the deployed node's image, and the
  capability's profile is one the node runs. A node image that is a release
  build rather than a qualified image is pinned the same way, and the view
  says it is unqualified: deployed never implies qualified.

The sidecar holds only what a person decides: the capability's contract, its
keystone, bridge and host function names, which image or lab record tested
it, and three prose lines (latest positive result, remaining obstruction,
next positive gate). Everything else is computed. The view is not
committed: with no flag the tool prints it, `--write` saves it as
build/current.md. `--check` (run by `make check`) fails when the view cannot be
built: when a named function, theorem, record or manifest is absent, or when a record does
not mention the image source or manifest it is cited for. It reads files
only; it runs no ACL2 and no image.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import certs  # noqa: E402
import commit_map
import green_check  # noqa: E402
import ledger  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]
SIDECAR = "planning/current-view.json"
OUTPUT = "build/current.md"
FIELDS = ("id", "name", "contract", "host", "keystone", "tested",
          "profile", "latest", "obstruction", "next")


class ViewError(Exception):
    pass


def host_call(root: Path, function: str, file: str) -> int:
    """First line of `file` that calls `function` outside a comment or its definition."""
    path = root / file
    if not path.is_file():
        raise ViewError(f"host file {file} is absent")
    call = re.compile(r"[('#]" + re.escape(function) + r"(?=[\s)]|$)")
    definition = re.compile(r"\(def[a-z-]*\*?\s+" + re.escape(function) + r"(?=[\s)]|$)")
    for number, line in enumerate(path.read_text(encoding="utf-8",
                                                 errors="replace").splitlines(), 1):
        code = line.split(";", 1)[0]
        if call.search(code) and not definition.search(code):
            return number
    raise ViewError(f"{file} does not call {function}")


def pending_bridge_verdicts(reason: str, proved: str, qualified: str, deployed: str) -> tuple[str, str, str]:
    """A matching component coordinate cannot establish an unproved caller bridge."""
    if not isinstance(reason, str) or not reason.strip():
        raise ViewError("pending_bridge must name the missing caller bridge")
    return ("no: caller bridge pending",) * 3


def theorem(tree: ledger.Tree, name: str) -> ledger.Theorem:
    found = tree.theorems.get(name)
    if found is None:
        raise ViewError(f"theorem {name} is absent from the tree")
    return found


class Evidence:
    """Each book's current digest and closure listing, and the cache's verdict."""

    def __init__(self, root: Path, report: dict) -> None:
        self.root = root
        self.states: dict[str, tuple[str, list[str]]] = {}
        self.records: dict = report.get("books_by_verdict", {})

    def state(self, book: str) -> tuple[str, list[str]]:
        if book not in self.states:
            closure = certs.closure(self.root, book)
            self.states[book] = (closure[book], certs.closure_listing(closure))
        return self.states[book]

    def certified(self, book: str) -> dict | None:
        """The book's cache record when it is green at its current closure key."""
        record = self.records.get(book)
        return record if green_check.green_at_these_bytes(record) else None


def record_link(root: Path, rel: str, *mentions: str) -> str:
    path = root / rel
    if not path.exists():
        if rel.startswith("planning/evidence/"):
            return f"`{path.stem}` (retired record)"  # left the tree with D71; not resolved
        raise ViewError(f"record {rel} is absent")
    text = path.read_text(encoding="utf-8")
    for mention in mentions:
        if mention and mention not in text:
            raise ViewError(f"record {rel} does not mention {mention}")
    return f"[{path.stem}](../{Path(rel).as_posix()})"


def carried(evidence: Evidence, image: dict, files: list[str]) -> tuple[bool, str]:
    """Whether an image holds each file at this revision's digest.

    Books and host files are compared with the digests `--pin-image` read out
    of the image's source revision.
    """
    sources: dict[str, str] = {}
    sources.update(image.get("book_sha256") or {})
    sources.update(image.get("host_sha256") or {})
    changed, absent = [], []
    for rel in files:
        recorded = sources.get(rel)
        if recorded is None:
            if rel in (image.get("host_absent") or []):
                absent.append(rel)
                continue
            if not rel.startswith("books/"):
                raise ViewError(f"image {image['source'][:8]} has no digest for {rel}; "
                                "run `python3 tools/current_view.py --pin-image NAME`")
            absent.append(rel)
            continue
        current = (evidence.state(rel.removesuffix(".lisp"))[0] if rel.startswith("books/")
                   else certs.content_hash(evidence.root / rel))
        if recorded != current:
            changed.append(rel)
    if absent:
        return False, "absent from it: " + ", ".join(f"`{x}`" for x in absent)
    if changed:
        return False, "changed since it: " + ", ".join(f"`{x}`" for x in changed)
    return True, "it carries this source"


def tested_coordinate(root: Path, cap: dict, images: dict, evidence: Evidence,
                      files: list[str]) -> tuple[str, str]:
    """Render an explicit no-image, qualified-image or historical lab coordinate."""
    ident = cap["id"]
    if "tested" not in cap:
        raise ViewError(f"{ident}: sidecar lacks tested")
    tested = cap["tested"]
    if tested is not None:
        if not isinstance(tested, dict):
            raise ViewError(f"{ident}: tested must be null or an image/lab coordinate")
        expected = {"image", "profile"} if "image" in tested else {"record", "source", "profile"}
        if not expected <= tested.keys() or ("image" in tested and "source" in tested):
            raise ViewError(f"{ident}: invalid tested coordinate")
        if any(not isinstance(tested[k], str) or not tested[k].strip() for k in expected):
            raise ViewError(f"{ident}: tested coordinates must be nonempty strings")
        if "image" in tested and tested["image"] not in images:
            raise ViewError(f"{ident}: unknown tested image {tested['image']}")
    if tested is None:
        qualified = "no: no matching image evidence"
        tested_line = "no matching image; source proof experiments are recorded separately below"
    elif "image" in tested:
        image = images[tested["image"]]
        if not image.get("qualification"):
            raise ViewError(f"{ident}: tested image {tested['image']} is unqualified")
        ok, how = carried(evidence, image, files)
        qual_link = record_link(root, image["qualification"])
        qualified = f"yes: {tested['image']}" if ok else f"no: source changed since {tested['image']}"
        tested_line = (f"image `{tested['image']}` ({qual_link}), profile "
                       f"{tested['profile']}; {how}")
    else:
        lab_link = record_link(root, tested["record"], tested["source"])
        qualified = f"lab only: `{tested['source']}`"
        tested_line = (f"lane image of `{tested['source']}` ({lab_link}), profile "
                       f"{tested['profile']}; not a shared qualification")
    return qualified, tested_line


def build(root: Path = ROOT) -> str:
    view = json.loads((root / SIDECAR).read_text(encoding="utf-8"))
    tree = ledger.load_tree()
    proofs = json.loads((root / "planning/proofs.json").read_text(encoding="utf-8"))["proofs"]
    keystone_books = {theorem(tree, cap["keystone"]).book.removesuffix(".lisp")
                      for cap in view["capabilities"]}
    event_books = ledger.event_books(tree, ledger.load_proof_events())
    cited = [p for p in proofs
             if any(cap["keystone"] in (p.get("events") or []) for cap in view["capabilities"])]
    # ONE cache question for every book this view judges.
    wanted = keystone_books.union(*(event_books.get(p["id"], set()) for p in cited))
    green_state: dict = {"__green__": green_check.audit(root, roots=sorted(wanted))}
    evidence = Evidence(root, green_state["__green__"])

    def status_of(proof: dict) -> str:
        """The row's status, computed from the cache (it is not stored)."""
        return ledger.derived_status(proof, proof.get("events") or [],
                                     event_books.get(proof["id"], set()),
                                     green_state, root)

    images = view["images"]
    node = view["deployment"]
    node_image = images[node["image"]]
    for name, image in images.items():
        if image.get("qualification") is None:
            if name != node["image"]:
                raise ViewError(f"image {name} has no qualification record; only the "
                                "node's release image may be unqualified")
        else:
            record_link(root, image["qualification"], image["source"])
        if not image.get("book_sha256"):
            raise ViewError(f"image {name} has no pinned book digests; run "
                            f"`python3 tools/current_view.py --pin-image {name}`")
    node_link = record_link(root, node["record"], node["image"])
    node_qualified = ("" if node_image.get("qualification") else
                      "; its image is a release build of that source, not a qualified image")
    earlier_nodes = [f"{n['where']} on `{n['image']}` ({record_link(root, n['record'], n['image'])}), "
               f"{n['state']}" for n in view.get("earlier_deployments", [])]
    # Further live nodes beside the one the deployed column is computed against
    # (node #2 on hbox, planning/evidence/hbox-node-2026-09-28.md).
    other_nodes = [f"{n['where']} on `{n['image']}` ({record_link(root, n['record'], n['image'])}), "
                   f"{n['state']}" for n in view.get("other_deployments", [])]

    summary, records = [], []
    for cap in view["capabilities"]:
        missing = [field for field in FIELDS if field not in cap]
        if missing:
            raise ViewError(f"{cap.get('id')}: sidecar lacks {', '.join(missing)}")
        ident = cap["id"]
        host = cap["host"]
        line = host_call(root, host["function"], host["file"])
        key = theorem(tree, cap["keystone"])
        key_book = key.book.removesuffix(".lisp")
        bridge = theorem(tree, cap["bridge"]) if cap.get("bridge") else None
        rows = [f"{p['id']} ({status_of(p)})" for p in proofs
                if cap["keystone"] in (p.get("events") or [])]
        certifier = evidence.certified(key_book)
        books = sorted({key.book} | ({bridge.book} if bridge else set()))
        files = books + [host["file"]]

        qualified, tested_line = tested_coordinate(root, cap, images, evidence, files)
        if cap["profile"] not in node["profiles"]:
            deployed, deployed_line = "no: profile not deployed", (
                f"no: the node runs {', '.join(node['profiles'])}, this needs {cap['profile']}")
        else:
            ok, how = carried(evidence, node_image, files)
            deployed = f"yes: {node['image']}" if ok else "no: dev source not on the node"
            deployed_line = f"{'yes' if ok else 'no'}: node image `{node['image']}`; {how}"
        proved = "yes: cert cache" if certifier else "no: not certified"

        if cap.get("pending_bridge") is not None:
            proved, qualified, deployed = pending_bridge_verdicts(
                cap["pending_bridge"], proved, qualified, deployed)
            tested_line = deployed_line = "no: " + cap["pending_bridge"]

        summary.append(f"| [{ident}](#{ident.lower()}) {cap['name']} | `{cap['keystone']}` "
                       f"| yes | {proved} | {qualified} | {deployed} |")
        subject = f"`{host['function']}` at {host['file']}:{line}"
        if cap.get("pending_bridge"):
            subject += ", caller bridge pending: " + cap["pending_bridge"]
        if bridge:
            subject += (f", equated by `{cap['bridge']}` "
                        f"({bridge.book}:{bridge.line})")
        cert = (f"certified at the current source and closure (record-toolchain cert-cache "
                f"entry at closure key `{certifier['closure_key'][:12]}`)"
                if certifier else
                f"no record-toolchain cert-cache entry at the current closure key of `{key.book}`")
        records.append("\n".join([
            f"### {ident}",
            "",
            f"**{cap['name']}.** {cap['contract']}",
            "",
            f"- Host-called subject: {subject}.",
            f"- Keystone: `{cap['keystone']}` ({key.book}:{key.line}"
            + (f"; {', '.join(rows)}" if rows else "; in no registry row") + f"); {cert}.",
            f"- Tested: {tested_line}.",
            f"- Deployed: {deployed_line}.",
            f"- Latest positive result: {cap['latest']}",
            f"- Remaining obstruction: {cap['obstruction']}",
            f"- Next positive gate: {cap['next']}",
            "",
        ]))

    superseded = ", ".join(record_link(root, rel) for rel in view["superseded"])
    head = [
        "# Current view",
        "",
        "Generated by `python3 tools/current_view.py --write` from",
        f"[`current-view.json`](../planning/current-view.json) and the tree; not",
        "committed. Edit the sidecar, never this file. The four coordinates are",
        "computed: **implemented** (the host line below calls the subject on this",
        "revision), **proved** (the record box's cert cache holds an entry for the",
        "keystone's book at its current closure key), **qualified** (the tested",
        "image's pinned digests hold the keystone, bridge and host sources as they",
        "are here), **deployed** (the same against the live node's image and profile).",
        "The prose lines are hand-maintained and name their record. The history",
        "stays in [`evidence/`](../planning/evidence/), immutable.",
        "Every image above is the SBCL image. An EXTRACTED image (`tools/extract`:",
        "the same world's functions compiled by bare SBCL into fn-core) is a different qualified",
        "image: its qualification rests on A-EXTRACT ([failures](../specs/failures.md))",
        "and is `make extract-check` on hbox; none is qualified or deployed.",
        "",
        f"Live node: {node['where']} on `{node['image']}` ({node_link}), "
        f"{node['profile_text']}{node_qualified}.",
        *([f"Also live: {line}." for line in other_nodes]),
        *([f"Earlier node: {line}." for line in earlier_nodes]),
        f"Superseded image records: {superseded}.",
        "",
        "| capability | keystone | implemented | proved | qualified | deployed |",
        "| --- | --- | --- | --- | --- | --- |",
        *summary,
        "",
        "## Records",
        "",
    ]
    return "\n".join(head + records)


def pin_image(name: str, root: Path = ROOT) -> int:
    """Store the host-file digests of an image's source revision in the sidecar."""
    import hashlib
    import subprocess
    path = root / SIDECAR
    view = json.loads(path.read_text(encoding="utf-8"))
    image = view["images"][name]
    files = sorted({cap["host"]["file"] for cap in view["capabilities"]})
    # Pin the keystone and bridge books from the image's source revision too.
    cited = [name_ for cap in view["capabilities"]
             for name_ in (cap.get("keystone"), cap.get("bridge")) if name_]
    tree = ledger.load_tree() if cited else None
    books = sorted({theorem(tree, name_).book for name_ in cited})
    revision = commit_map.resolve(image["source"], root)
    digests, missing = {}, []
    for rel in files:
        # A host file the revision does not have (a capability newer than
        # the image) is pinned as absent, so the view says "absent from it"
        # instead of refusing the sidecar.
        exists = subprocess.run(["git", "-C", str(root), "cat-file", "-e", f"{revision}:{rel}"],
                                capture_output=True).returncode == 0
        if not exists:
            missing.append(rel)
            continue
        blob = subprocess.run(["git", "-C", str(root), "show", f"{revision}:{rel}"],
                              check=True, capture_output=True).stdout
        digests[rel] = hashlib.sha256(blob).hexdigest()
    image["host_sha256"] = digests
    if missing:
        image["host_absent"] = missing
    else:
        image.pop("host_absent", None)
    if books:
        pinned = {}
        for rel in books:
            found = subprocess.run(["git", "-C", str(root), "show", f"{revision}:{rel}"],
                                   capture_output=True)
            if found.returncode == 0:
                pinned[rel] = hashlib.sha256(found.stdout).hexdigest()
        image["book_sha256"] = pinned
    path.write_text(json.dumps(view, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"pinned {len(digests)} host files"
          + (f" and {len(image.get('book_sha256', {}))} books" if books else "")
          + f" for image {name}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true", help=f"write {OUTPUT}")
    group.add_argument("--check", action="store_true", help="fail when the view cannot be built")
    green_check.add_arguments(parser)
    group.add_argument("--pin-image", metavar="NAME",
                       help="record in the sidecar the SHA-256 of each named host file "
                            "at image NAME's source revision (reads git objects)")
    args = parser.parse_args(argv)
    if args.pin_image:
        return pin_image(args.pin_image)
    green_check.configure_from(args)
    try:
        text = build()
    except green_check.CacheUnavailable as error:
        if args.check:
            print(f"current view: UNKNOWN: no record cache reachable ({error}); "
                  f"pass --cache DIR for a local mirror", file=sys.stderr)
            return 3
        print(f"current view: no answer from the cert cache: {error}", file=sys.stderr)
        return 2
    except (ViewError, KeyError) as error:
        print(f"current view: {error}", file=sys.stderr)
        return 1
    if args.write:
        target = ROOT / OUTPUT
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")
        print(f"wrote {OUTPUT}")
    elif args.check:
        print(f"Current view OK: {SIDECAR} and the tree build.")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
