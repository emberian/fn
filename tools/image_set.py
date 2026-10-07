#!/usr/bin/env python3
"""Prebuilt native image sets on hbox: publish once per merged head, link into a tree.

    python3 tools/image_set.py publish TREE SHA [--base DIR]
    python3 tools/image_set.py link SHA TREE IMAGE... [--base DIR]
    python3 tools/image_set.py check SHA [--base DIR]
    python3 tools/image_set.py link-run RUN TREE IMAGE...
    python3 tools/image_set.py stamp TREE

An image build is the long pole of a native run (~25 min; python-diet-2 and
others, 2026-09-28), and a lane that changed only tests or tools rebuilt the
images dev's batch had already built.  The batch runner publishes the images
it builds for a merged head; `tools/hbox_native.sh --image-set SHA` links them
into its tree instead of certifying and building.

The layout, BASE/SHA/ (BASE /tank/fn/images; SHA the full commit the images
were built from):

    fn-host, fn-host.core                      production   (optional each,
    fn-host-developer, fn-host-developer.core  developer     at least one)
    fn-host-dtn, fn-host-dtn.core              dtn
    fn-host-dtn-developer, ...core             dtn-developer
    *.world-deps                               beside their image, when built
    lib/                                       the image's foreign libraries
    TREE_SHA                                   SHA, one line
    MANIFEST.json                              sha, images (name -> launcher,
                                               core), files (path -> sha256),
                                               published_utc, source tree
    SHA256SUMS                                 every file above but itself

`publish` refuses unless every image in TREE/build is the tree's own build
(no build/REUSED_SOURCE, no symlinked launcher, core, world-deps or lib/)
and records `commit SHA` as its source (FILE.source, which
tools/build_native_host.sh writes from the tree it built: S057/S063, the
label is the build's record, never the caller's word).  It then
copies TREE/build's images into BASE/SHA.partial, rewrites each
launcher's absolute `--core` path to the published core (a launcher names
its core by absolute path), writes the manifest and sums and renames the
directory into place; an existing BASE/SHA is left alone (refused, exit 1).
`link` verifies the set's SHA256SUMS and symlinks the named images (their
cores, world-deps, and lib/) into TREE/build; a named image the set lacks is
refused by name (exit 1).  `check` verifies the sums.

`stamp` writes the same TREE_SHA and MANIFEST.json into TREE/build itself,
for a run that builds and tests without publishing (a convergence batch):
tests/native_image_provenance.py binds a composed fixture's launchers to
them.  The sha is the images' own `commit SHA` record; a build without one
common commit record is left unstamped (any earlier stamp removed), and
tools/build_native_host.sh removes the stamp before it rebuilds an image.

`link-run` (`hbox_native.sh --reuse-image RUN`) links the images an earlier
hbox_native run built, RUN/tree/build, the same way, and writes
TREE/build/REUSED_SOURCE: the source RUN's run.log names (`== source commit
X` / `== source worktree X`), which is the images' identity source.  A run
without that line, or without a named image's launcher and core, is refused
by name: python-diet-3 and correctness-remainder reran modules against
another run's images by hand (2026-09-29).
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile

BASE = Path("/tank/fn/images")
IMAGES = {
    "production": "fn-host",
    "developer": "fn-host-developer",
    "dtn": "fn-host-dtn",
    "dtn-developer": "fn-host-dtn-developer",
}
SHA = re.compile(r"[0-9a-f]{40}")
CORE = re.compile(r'--core "([^"]+)"')


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def files_of(directory: Path) -> list[Path]:
    return sorted(p for p in directory.rglob("*")
                  if p.is_file() and p.name not in ("SHA256SUMS",))


def write_sums(directory: Path) -> None:
    lines = [f"{sha256(p)}  {p.relative_to(directory)}\n" for p in files_of(directory)]
    atomic_write(directory / "SHA256SUMS", "".join(lines))


def atomic_write(path: Path, text: str) -> None:
    temporary = None
    mode = path.stat().st_mode & 0o777 if path.exists() else 0o644
    try:
        with tempfile.NamedTemporaryFile(mode="w", dir=path.parent,
                                         prefix=f".{path.name}.", delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(text)
        temporary.chmod(mode)
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def verify(directory: Path) -> list[str]:
    sums = directory / "SHA256SUMS"
    if not sums.is_file():
        return ["SHA256SUMS"]
    bad = []
    for line in sums.read_text().splitlines():
        digest, _, name = line.partition("  ")
        path = directory / name
        if not path.is_file() or sha256(path) != digest:
            bad.append(name)
    return bad


def catalog_of(build: Path, file: str) -> str:
    """Read the builder's catalog evidence; absent evidence is unknown."""
    record = build / f"{file}.catalog"
    if not record.is_file():
        return "unknown"
    return record.read_text(encoding="utf-8").strip()


def source_of(build: Path, file: str) -> str:
    """The source identity the builder recorded beside the image
    (tools/build_native_host.sh writes FILE.source: `commit SHA` for a
    clean commit, `worktree ...` otherwise); absent evidence is unknown."""
    record = build / f"{file}.source"
    if not record.is_file() or record.is_symlink():
        return "unknown"
    return record.read_text(encoding="utf-8").strip() or "unknown"


def not_built_here(build: Path, found: dict[str, str]) -> list[str]:
    """Why TREE/build's images are not this tree's own build: a reused run's
    record, or a launcher, core, world-deps or lib/ that is a symlink placed
    by `link`/`link-run` (S063: publishing those relabels another set's
    cores under a new sha)."""
    why = []
    if (build / "REUSED_SOURCE").exists():
        why.append("build/REUSED_SOURCE (its images were linked from an earlier run)")
    names = ["lib"] + [name for file in found.values()
                       for name in (file, f"{file}.core", f"{file}.world-deps")]
    why += [f"{name} is a symlink to {os.readlink(build / name)}"
            for name in names if (build / name).is_symlink()]
    return why


def wrong_source(build: Path, found: dict[str, str], sha: str) -> list[str]:
    """The images whose recorded source is not exactly `commit SHA` (S057:
    the set's label is the build's own record, never the caller's word)."""
    return [f"{name} ({source_of(build, file)})" for name, file in sorted(found.items())
            if source_of(build, file) != f"commit {sha}"]


def wrong_catalog(found: dict[str, str]) -> list[str]:
    """The images, by name, whose recorded catalog is not the paged one: the
    paged catalog is the only executable catalog, and an image that predates
    the flip (or has no record) is not published or linked."""
    return [f"{name} ({catalog})" for name, catalog in sorted(found.items()) if catalog != "paged"]


def write_manifest(directory: Path, sha: str, images: dict, tree: Path,
                   files: list[Path] | None, when: str) -> None:
    """TREE_SHA and MANIFEST.json for a directory of images: the one writer of
    the coordinates tests/native_image_provenance.py binds a launcher to
    (sha, images name -> launcher/core, files path -> sha256).  `publish`
    writes them into a set (`when` published_utc; files None: every file of
    the set, TREE_SHA included), `stamp` into a run tree's own build (`when`
    stamped_utc; files: its images' own)."""
    atomic_write(directory / "TREE_SHA", sha + "\n")
    files = files_of(directory) if files is None else files
    manifest = {"sha": sha, "images": images, "source_tree": str(tree),
                when: dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                "files": {str(p.relative_to(directory)): sha256(p) for p in files}}
    atomic_write(directory / "MANIFEST.json", json.dumps(manifest, indent=1) + "\n")


def stamp(tree: Path) -> int:
    """Stamp TREE/build's own images with TREE_SHA and MANIFEST.json, so a
    composed fixture can bind an unpublished build (a convergence run builds
    and tests without publishing; CONVERGE-20261007-1 red #3).  The sha is the
    builder's record, never the caller's word: every image must record the
    same `commit SHA` (FILE.source).  A build with another record (a lane's
    `worktree SHA+dirty`, mixed commits, unknown) is left unstamped, with any
    earlier stamp removed, and the fixture refuses it by name.  A build that
    holds linked images is refused (exit 1): those carry their set's own
    manifest."""
    build = tree / "build"
    found = {name: file for name, file in IMAGES.items()
             if (build / file).is_file() and (build / f"{file}.core").is_file()}
    linked = not_built_here(build, found)
    if linked:
        print(f"image_set: {build} holds images it did not build: {'; '.join(linked)}; "
              "not stamped", file=sys.stderr)
        return 1
    for name in ("MANIFEST.json", "TREE_SHA"):
        (build / name).unlink(missing_ok=True)
    if not found:
        print(f"image_set: no image in {build}; not stamped", file=sys.stderr)
        return 0
    records = {name: source_of(build, file) for name, file in sorted(found.items())}
    commits = {record.removeprefix("commit ") for record in records.values()}
    sha = next(iter(commits))
    if len(commits) != 1 or not SHA.fullmatch(sha):
        print(f"image_set: {build} not stamped: its images do not record one source "
              f"commit ({', '.join(f'{name}: {record}' for name, record in records.items())})",
              file=sys.stderr)
        return 0
    images, files = {}, []
    for name, file in found.items():
        images[name] = {"launcher": file, "core": f"{file}.core",
                        "catalog": catalog_of(build, file), "source": f"commit {sha}"}
        files += [build / file, build / f"{file}.core"]
        if (build / f"{file}.world-deps").is_file():
            files.append(build / f"{file}.world-deps")
    write_manifest(build, sha, images, tree, files, "stamped_utc")
    print(f"image_set: stamped {', '.join(sorted(images))} in {build} as commit {sha}")
    return 0


def publish(tree: Path, sha: str, base: Path = BASE) -> int:
    if not SHA.fullmatch(sha):
        print(f"image_set: {sha!r} is not a full commit sha", file=sys.stderr)
        return 2
    target = base / sha
    if target.exists():
        print(f"image_set: {target} exists; a set is published once", file=sys.stderr)
        return 1
    build = tree / "build"
    found = {name: file for name, file in IMAGES.items()
             if (build / file).is_file() and (build / f"{file}.core").is_file()}
    if not found:
        print(f"image_set: no image in {build}", file=sys.stderr)
        return 1
    catalogs = {name: catalog_of(build, file) for name, file in found.items()}
    bad = wrong_catalog(catalogs)
    if bad:
        print(f"image_set: {build} has images without an affirmative paged catalog: {', '.join(bad)}; "
              "not published; rebuild with tools/build_native_host.sh, which writes FILE.catalog",
              file=sys.stderr)
        return 1
    linked = not_built_here(build, found)
    if linked:
        print(f"image_set: {build} holds images it did not build: {'; '.join(linked)}; "
              "not published (publish from the tree that built them)", file=sys.stderr)
        return 1
    sources = wrong_source(build, found, sha)
    if sources:
        print(f"image_set: {build}'s images do not record source commit {sha}: "
              f"{', '.join(sources)}; not published (build from `git archive {sha}`, "
              "tools/hbox_native.sh REV, or a clean checkout at it: "
              "tools/build_native_host.sh writes FILE.source)", file=sys.stderr)
        return 1
    partial = base / f"{sha}.partial"
    shutil.rmtree(partial, ignore_errors=True)
    partial.mkdir(parents=True)
    images = {}
    for name, file in found.items():
        core = partial / f"{file}.core"
        shutil.copy2(build / f"{file}.core", core)
        text = (build / file).read_text()
        if not CORE.search(text):
            print(f"image_set: {build / file} names no --core", file=sys.stderr)
            shutil.rmtree(partial)
            return 1
        launcher = partial / file
        launcher.write_text(CORE.sub(lambda _: f'--core "{base / sha / core.name}"', text))
        launcher.chmod(0o755)
        deps = build / f"{file}.world-deps"
        if deps.is_file():
            shutil.copy2(deps, partial / deps.name)
        images[name] = {"launcher": file, "core": core.name, "catalog": catalogs[name],
                        "source": f"commit {sha}"}
    if (build / "lib").is_dir():
        shutil.copytree(build / "lib", partial / "lib")
    write_manifest(partial, sha, images, tree, None, "published_utc")
    write_sums(partial)
    os.rename(partial, target)
    print(f"image_set: published {', '.join(sorted(images))} at {target}")
    return 0


def link(sha: str, tree: Path, wanted: list[str], base: Path = BASE) -> int:
    directory = base / sha
    try:
        manifest = json.loads((directory / "MANIFEST.json").read_text())
    except (OSError, ValueError) as error:
        print(f"image_set: no image set {directory}: {error}", file=sys.stderr)
        return 1
    missing = [name for name in wanted if name not in manifest.get("images", {})]
    if missing:
        print(f"image_set: {directory} has no {', '.join(missing)} image (it holds "
              f"{', '.join(sorted(manifest.get('images', {})))}); build it with --images",
              file=sys.stderr)
        return 1
    bad = verify(directory)
    if bad:
        print(f"image_set: {directory} fails its SHA256SUMS: {', '.join(bad[:5])}",
              file=sys.stderr)
        return 1
    # A set published since S057 records each image's source; one that says
    # another commit is refused (older sets carry no source and are judged
    # by their TREE_SHA, as before).
    bad = [f"{name} ({manifest['images'][name]['source']})" for name in wanted
           if "source" in manifest["images"][name]
           and manifest["images"][name]["source"] != f"commit {sha}"]
    if bad:
        print(f"image_set: {directory} records another source for {', '.join(bad)}; not linked",
              file=sys.stderr)
        return 1
    bad = wrong_catalog({name: manifest["images"][name].get("catalog", "unknown") for name in wanted})
    if bad:
        print(f"image_set: {directory} does not record a paged catalog for {', '.join(bad)}; "
              "not linked; rebuild with tools/build_native_host.sh, which writes FILE.catalog, "
              "and publish a new image set",
              file=sys.stderr)
        return 1
    build = tree / "build"
    build.mkdir(parents=True, exist_ok=True)
    names = ["lib"] if (directory / "lib").is_dir() else []
    for name in wanted:
        file = manifest["images"][name]["launcher"]
        names += [file, f"{file}.core"]
        if (directory / f"{file}.world-deps").is_file():
            names.append(f"{file}.world-deps")
    place_links(directory, build, names)
    for name in wanted:
        record = build / f"{manifest['images'][name]['launcher']}.catalog"
        record.unlink(missing_ok=True)
        record.write_text(manifest["images"][name]["catalog"] + "\n")
    print(f"image_set: linked {', '.join(wanted)} from {directory} into {build}")
    return 0


def place_links(directory: Path, build: Path, names: list[str]) -> None:
    for name in names:
        place = build / name
        if place.is_symlink() or place.is_file():
            place.unlink()
        elif place.is_dir():
            shutil.rmtree(place)
        place.symlink_to(directory / name)


SOURCE_LINE = re.compile(r"^== source (?:commit|worktree) (\S+)\s*$", re.MULTILINE)


def link_run(run: Path, tree: Path, wanted: list[str]) -> int:
    directory = run / "tree" / "build"
    try:
        log = (run / "run.log").read_text(encoding="utf-8", errors="replace")
    except OSError as error:
        print(f"image_set: no earlier run at {run}: {error}", file=sys.stderr)
        return 1
    found = SOURCE_LINE.search(log)
    if not found:
        print(f"image_set: {run}/run.log names no `== source` line: the images' source "
              "is unknown, so they are not reused", file=sys.stderr)
        return 1
    missing = [name for name in wanted
               if not (directory / IMAGES[name]).is_file()
               or not (directory / f"{IMAGES[name]}.core").is_file()]
    if missing:
        print(f"image_set: {directory} has no {', '.join(missing)} image (launcher and "
              "core); that run did not build it", file=sys.stderr)
        return 1
    catalogs = {name: catalog_of(directory, IMAGES[name]) for name in wanted}
    bad = wrong_catalog(catalogs)
    if bad:
        print(f"image_set: {directory} has images without an affirmative paged catalog: {', '.join(bad)}; "
              "not reused; rebuild with tools/build_native_host.sh, which writes FILE.catalog",
              file=sys.stderr)
        return 1
    build = tree / "build"
    build.mkdir(parents=True, exist_ok=True)
    names = ["lib"] if (directory / "lib").is_dir() else []
    for name in wanted:
        file = IMAGES[name]
        names += [file, f"{file}.core"]
        if (directory / f"{file}.world-deps").is_file():
            names.append(f"{file}.world-deps")
    place_links(directory, build, names)
    for name in wanted:
        record = build / f"{IMAGES[name]}.catalog"
        record.unlink(missing_ok=True)
        record.write_text(catalogs[name] + "\n")
    (build / "REUSED_SOURCE").write_text(found.group(1) + "\n")
    print(f"image_set: linked {', '.join(wanted)} from the run {run} "
          f"(source {found.group(1)}) into {build}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="action", required=True)
    one = sub.add_parser("publish")
    one.add_argument("tree")
    one.add_argument("sha")
    two = sub.add_parser("link")
    two.add_argument("sha")
    two.add_argument("tree")
    two.add_argument("images", nargs="+", choices=sorted(IMAGES))
    three = sub.add_parser("check")
    three.add_argument("sha")
    for each in (one, two, three):
        each.add_argument("--base", default=str(BASE))
    four = sub.add_parser("link-run")
    four.add_argument("run")
    four.add_argument("tree")
    four.add_argument("images", nargs="+", choices=sorted(IMAGES))
    five = sub.add_parser("stamp")
    five.add_argument("tree")
    args = parser.parse_args(argv)
    if args.action == "stamp":
        return stamp(Path(args.tree).resolve())
    if args.action == "link-run":
        return link_run(Path(args.run), Path(args.tree).resolve(), args.images)
    base = Path(args.base)
    if args.action == "publish":
        return publish(Path(args.tree).resolve(), args.sha, base)
    if args.action == "link":
        return link(args.sha, Path(args.tree).resolve(), args.images, base)
    bad = verify(base / args.sha)
    print("image_set: " + ("OK" if not bad else "BAD " + ", ".join(bad)))
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
