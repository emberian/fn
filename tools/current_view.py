#!/usr/bin/env python3
"""Generate planning/current.md, the current view of each capability.

The review of 2026-09-24 (planning/review-2026-09-24-gpt6-direction.md, "A
small evidence-maintenance repair") asks for a short current view beside the
immutable evidence records. This writes one record per capability from
planning/current-view.json and the tree, and keeps four evidence coordinates
apart:

- implemented: the host-called subject is called on this revision
  (file:line found in host/) and the keystone exists (ledger parser);
- proved: an archived certify manifest under planning/evidence/manifests/
  recorded the keystone's book `passed` at its current source digest with an
  undrifted include closure (certified_claims' pass rule);
- qualified: the tested image's closure manifest recorded the keystone's
  book (and the bridge's book and the host file, when it lists them) at the
  same source digest as this revision, i.e. the qualified image carries the
  source this view describes;
- deployed: the same comparison against the deployed node's image, and the
  capability's profile is one the node runs.

The sidecar holds only what a person decides: the capability's contract, its
keystone, bridge and host function names, which image or lab record tested
it, and three prose lines (latest positive result, remaining obstruction,
next positive gate). Everything else is computed. `--check` (run by
`make check`) fails when planning/current.md differs from the output, when a
named function, theorem, record or manifest is absent, or when a record does
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
import certified_claims  # noqa: E402
import green_check  # noqa: E402
import ledger  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]
SIDECAR = "planning/current-view.json"
OUTPUT = "planning/current.md"
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


def theorem(tree: ledger.Tree, name: str) -> ledger.Theorem:
    found = tree.theorems.get(name)
    if found is None:
        raise ViewError(f"theorem {name} is absent from the tree")
    return found


class Evidence:
    """The archived manifests, read once, and each book's current state."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.runs = [(run, manifest) for run, manifest in green_check.manifests(root)
                     if run.archived]
        self.by_id = {run.run_id: manifest for run, manifest in self.runs}
        self.states: dict[str, tuple[str, list[str]]] = {}

    def state(self, book: str) -> tuple[str, list[str]]:
        if book not in self.states:
            self.states[book] = certified_claims.current_state(self.root, book)
        return self.states[book]

    def first_certifier(self, book: str) -> str | None:
        """The earliest archived run that certified the current source and closure.

        The earliest, not the newest, so that archiving a later run does not
        change the view; the answer moves only when the book or its closure does.
        """
        digest, listing = self.state(book)
        for run, manifest in self.runs:
            if certified_claims.certifies(manifest, book, digest, listing)[0]:
                return run.run_id
        return None

    def first_installer(self, book: str) -> str | None:
        """The earliest archived run that installed a pair for the current source and closure.

        A cache install validates a certificate made by an earlier run, which
        may not be archived; it is weaker than a `passed` verdict and is
        reported as such.
        """
        digest, listing = self.state(book)
        for run, manifest in self.runs:
            sources = manifest.get("source_digests_sha256") or {}
            if (book in (manifest.get("installed_books") or {})
                    and sources.get(book + ".lisp") == digest
                    and not certified_claims.certs.closure_drift(listing, sources)):
                return run.run_id
        return None

    def first_at_digest(self, book: str) -> tuple[str, list[str]] | None:
        """The earliest archived run that passed the book's current source, and the closure drift since."""
        digest, listing = self.state(book)
        for run, manifest in self.runs:
            sources = manifest.get("source_digests_sha256") or {}
            if ((manifest.get("book_results") or {}).get(book) == "passed"
                    and sources.get(book + ".lisp") == digest):
                return run.run_id, certified_claims.certs.closure_drift(listing, sources)
        return None

    def manifest(self, run_id: str) -> dict:
        found = self.by_id.get(run_id)
        if found is None:
            raise ViewError(f"manifest {run_id} is not archived under "
                            "planning/evidence/manifests/")
        return found


def record_link(root: Path, rel: str, *mentions: str) -> str:
    path = root / rel
    if not path.is_file():
        raise ViewError(f"record {rel} is absent")
    text = path.read_text(encoding="utf-8")
    for mention in mentions:
        if mention and mention not in text:
            raise ViewError(f"record {rel} does not mention {mention}")
    return f"[{path.stem}]({Path(rel).relative_to('planning').as_posix()})"


def carried(evidence: Evidence, image: dict, files: list[str]) -> tuple[bool, str]:
    """Whether an image holds each file at this revision's digest.

    Books come from the image's closure manifest; host files from the
    digests `--pin-image` read out of the image's source revision.
    """
    sources = dict(evidence.manifest(image["closure_manifest"]).get("source_digests_sha256")
                   or {})
    sources.update(image.get("host_sha256") or {})
    changed, absent = [], []
    for rel in files:
        recorded = sources.get(rel)
        if recorded is None:
            if not rel.startswith("books/"):
                raise ViewError(f"image {image['source'][:8]} has no digest for {rel}; "
                                "run `python3 tools/current_view.py --pin-image NAME`")
            absent.append(rel)
            continue
        current = (evidence.state(rel.removesuffix(".lisp"))[0] if rel.startswith("books/")
                   else certified_claims.certs.content_hash(evidence.root / rel))
        if recorded != current:
            changed.append(rel)
    if absent:
        return False, "absent from it: " + ", ".join(f"`{x}`" for x in absent)
    if changed:
        return False, "changed since it: " + ", ".join(f"`{x}`" for x in changed)
    return True, "it carries this source"


def build(root: Path = ROOT) -> str:
    view = json.loads((root / SIDECAR).read_text(encoding="utf-8"))
    tree = ledger.load_tree()
    proofs = json.loads((root / "planning/proofs.json").read_text(encoding="utf-8"))["proofs"]
    evidence = Evidence(root)
    images = view["images"]
    node = view["deployment"]
    node_image = images[node["image"]]
    for name, image in images.items():
        record_link(root, image["qualification"], image["source"])
        evidence.manifest(image["closure_manifest"])
    node_link = record_link(root, node["record"], node["image"], node_image["closure_manifest"])

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
        rows = [f"{p['id']} ({p.get('status')})" for p in proofs
                if cap["keystone"] in (p.get("events") or [])]
        certifier = evidence.first_certifier(key_book)
        installer = None if certifier else evidence.first_installer(key_book)
        earlier = None if certifier or installer else evidence.first_at_digest(key_book)
        books = sorted({key.book} | ({bridge.book} if bridge else set()))
        files = books + [host["file"]]

        tested = cap["tested"]
        if "image" in tested:
            image = images[tested["image"]]
            ok, how = carried(evidence, image, files)
            qual_link = record_link(root, image["qualification"])
            qualified = f"yes: {tested['image']}" if ok else f"no: source changed since {tested['image']}"
            tested_line = (f"image `{tested['image']}` ({qual_link}, closure "
                           f"`{image['closure_manifest']}`), profile {tested['profile']}; {how}")
        else:
            lab_link = record_link(root, tested["record"], tested["source"])
            qualified = f"lab only: `{tested['source']}`"
            tested_line = (f"lane image of `{tested['source']}` ({lab_link}), profile "
                           f"{tested['profile']}; not a shared qualification")
        if cap["profile"] not in node["profiles"]:
            deployed, deployed_line = "no: profile not deployed", (
                f"no: the node runs {', '.join(node['profiles'])}, this needs {cap['profile']}")
        else:
            ok, how = carried(evidence, node_image, files)
            deployed = f"yes: {node['image']}" if ok else "no: dev source not on the node"
            deployed_line = f"{'yes' if ok else 'no'}: node image `{node['image']}`; {how}"
        proved = (f"yes: `{certifier}`" if certifier else
                  f"cache only: `{installer}`" if installer else
                  "no: closure moved" if earlier else "no: source uncertified")

        summary.append(f"| [{ident}](#{ident.lower()}) {cap['name']} | `{cap['keystone']}` "
                       f"| yes | {proved} | {qualified} | {deployed} |")
        subject = f"`{host['function']}` at {host['file']}:{line}"
        if bridge:
            subject += (f", equated by `{cap['bridge']}` "
                        f"({bridge.book}:{bridge.line})")
        cert = (f"certified at the current source and closure by `{certifier}` (earliest archived)"
                if certifier else
                f"no archived manifest records it passed at the current source and closure; "
                f"`{installer}` installed a cached pair for them, made by a run not archived"
                if installer else
                f"no archived manifest certifies the current closure; `{earlier[0]}` "
                f"passed this source of `{key.book}`, and since then "
                + ", ".join(f"`{x}`" for x in earlier[1][:3])
                + (f" and {len(earlier[1]) - 3} more" if len(earlier[1]) > 3 else "")
                + " changed"
                if earlier else
                f"no archived manifest records `{key.book}` passed at its current source")
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
        f"[`current-view.json`](current-view.json) and the tree; `make check` fails when",
        "it is stale. Edit the sidecar, never this file. The four coordinates are",
        "computed: **implemented** (the host line below calls the subject on this",
        "revision), **proved** (an archived manifest certified the keystone's book at",
        "its current source digest and closure), **qualified** (the tested image's",
        "closure manifest holds the keystone, bridge and host sources as they are",
        "here), **deployed** (the same against the live node's image and profile).",
        "The prose lines are hand-maintained and name their record. The history",
        "stays in [`evidence/`](evidence/), immutable.",
        "",
        f"Live node: {node['where']} on `{node['image']}` ({node_link}), {node['profile_text']}.",
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
    digests = {}
    for rel in files:
        blob = subprocess.run(["git", "-C", str(root), "show", f"{image['source']}:{rel}"],
                              check=True, capture_output=True).stdout
        digests[rel] = hashlib.sha256(blob).hexdigest()
    image["host_sha256"] = digests
    path.write_text(json.dumps(view, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"pinned {len(digests)} host files for image {name}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true", help=f"regenerate {OUTPUT}")
    group.add_argument("--check", action="store_true", help=f"fail when {OUTPUT} is stale")
    group.add_argument("--pin-image", metavar="NAME",
                       help="record in the sidecar the SHA-256 of each named host file "
                            "at image NAME's source revision (reads git objects)")
    args = parser.parse_args(argv)
    if args.pin_image:
        return pin_image(args.pin_image)
    try:
        text = build()
    except (ViewError, KeyError) as error:
        print(f"current view: {error}", file=sys.stderr)
        return 1
    target = ROOT / OUTPUT
    if args.write:
        target.write_text(text, encoding="utf-8")
        print(f"wrote {OUTPUT}")
        return 0
    if not target.is_file() or target.read_text(encoding="utf-8") != text:
        print(f"current view: {OUTPUT} is stale; run `python3 tools/current_view.py --write`",
              file=sys.stderr)
        return 1
    print(f"Current view OK: {OUTPUT} matches {SIDECAR} and the tree.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
