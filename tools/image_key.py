#!/usr/bin/env python3
"""Content-keyed native images: a gate whose image inputs are unchanged links
the images an earlier run built instead of certifying, acquiring and saving.

    python3 tools/image_key.py keys    --tree T --acl2 A [--image-acl2 B] --images production,dtn,...
    python3 tools/image_key.py reuse   --store S --tree T --acl2 A [--image-acl2 B] --images ... --record FILE
    python3 tools/image_key.py publish --store S --tree T --record FILE --source SHA

An image is a function of its inputs, so each image has a KEY: SHA-256 over

  * the image's spec (profile, session script, world flavour) and this
    tool's KEY_VERSION;
  * every host file the session script loads (the `ld' and host-sibling
    `include-book' closure of host/native/build*.lisp, tools/extract/world.py's
    `lds_followed'), and everything else under host/ and third_party/ (the
    raw host files and the vendored foreign-library sources), by bytes;
  * the source bytes of every book in the include closure of the session
    script, of the generated world files and of the image umbrellas (the
    certificate and compiled file of a book are a function of those bytes,
    the toolchain and ACL2's certification; tools/extract/world.py `digest'
    keys the installed artifacts themselves, which exist only after install);
  * the build scripts and the launcher's rewrite inputs: tools/build_native_host.sh,
    build_mldsa65.sh, build_deflate.sh, build_blake3.sh, packaging/fn,
    packaging/launcher-decide.sh, tools/acl2_projects.py;
  * the toolchain: tools/acl2_toolchain.py's identity of the certifying
    launcher and of the launcher the image is saved under (launcher chain,
    saved core, runtime), the OpenSSL libcrypto/libssl pair the build loads,
    the C compiler's version and the machine type;
  * the environment the build script reads (FN_TLS_LIMIT, FN_TLS_BUDGET_PERCENT,
    FN_NATIVE_DEFAULT_HEAP_MB).

A SET key names the images a run needs together (a composed fixture binds its
launchers to one MANIFEST.json, tests/native_image_provenance.py), so the store
is BASE/<set key>/, tools/image_set.py's published layout, and a run reuses it
only when every needed image's key is the set's.  Saved SBCL cores are NOT
byte-reproducible (two builds of the same inputs differ in ~15% of their bytes
-- heap layout), so the key's completeness is judged by what a build reads
(the strace control in docs/testing.md), not by comparing cores.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "extract"))

import acl2_toolchain  # noqa: E402
import certs  # noqa: E402
import image_set  # noqa: E402

KEY_VERSION = "fn-image-key-1"

# image -> (profile, session script, world flavour): hbox_native.sh's triples.
SPECS = {
    "production": ("production", "host/native/build.lisp", "stripped"),
    "developer": ("developer", "host/native/build.lisp", "full"),
    "reference": ("production", "host/native/build.lisp", "full"),
    "developer-stripped": ("developer", "host/native/build.lisp", "stripped"),
    "dtn": ("production", "host/native/build-dtn.lisp", "stripped"),
    "dtn-developer": ("developer", "host/native/build-dtn.lisp", "full"),
}
BUILD_FILES = (
    "tools/build_native_host.sh", "tools/build_mldsa65.sh", "tools/build_deflate.sh",
    "tools/build_blake3.sh", "tools/acl2_projects.py", "packaging/fn",
    "packaging/launcher-decide.sh",
)
TREE_DIRECTORIES = ("host", "third_party")
ENVIRONMENT = ("FN_TLS_LIMIT", "FN_TLS_BUDGET_PERCENT", "FN_NATIVE_DEFAULT_HEAP_MB")
INCLUDE = re.compile(r'^\s*\(include-book "([^"]+)"([^)]*)\)', re.M)


def followed_files(root: Path, build: str) -> list[Path]:
    """BUILD and every host file its ld / host include-book chain loads."""
    import world
    return world.lds_followed(root, build)


def book_names(root: Path, files: list[Path]) -> list[str]:
    """The books under ROOT that FILES include, and everything those include."""
    names: list[str] = []
    for path in files:
        for target, options in INCLUDE.findall(path.read_text(encoding="utf-8")):
            if ":dir" in options:
                continue
            resolved = (path.parent / target).resolve()
            if resolved.suffix == ".lisp":
                resolved = resolved.with_suffix("")
            try:
                name = resolved.relative_to(root.resolve()).as_posix()
            except ValueError:
                continue
            if (root / f"{name}.lisp").is_file():
                for one in certs.closure(root, name):
                    if one not in names:
                        names.append(one)
    return names


def tree_files(root: Path) -> list[Path]:
    found: list[Path] = []
    for directory in TREE_DIRECTORIES:
        base = root / directory
        if base.is_dir():
            found += sorted(path for path in base.rglob("*")
                            if path.is_file() and not path.is_symlink()
                            and "__pycache__" not in path.parts)
    return found


def openssl_libraries() -> list[Path]:
    prefix = os.environ.get("FN_OPENSSL_PREFIX")
    if not prefix:
        return []
    found = []
    for directory in ("lib64", "lib"):
        for name in ("libcrypto.so.3", "libssl.so.3"):
            path = Path(prefix) / directory / name
            if path.is_file():
                found.append(path.resolve())
    return found


def compiler_version() -> str:
    try:
        return subprocess.run(["cc", "--version"], capture_output=True, text=True,
                              check=False).stdout.splitlines()[0]
    except (OSError, IndexError):
        return "no cc"


def toolchain_part(acl2: Path | None, image_acl2: Path | None) -> list[tuple[str, str]]:
    out = []
    for label, launcher in (("acl2", acl2), ("image-acl2", image_acl2)):
        if launcher is None:
            continue
        found = acl2_toolchain.fingerprint(Path(launcher))
        if not found.qualified or found.identity is None:
            print(f"image_key: unqualified {label} launcher {launcher}: " + found.reason,
                  file=sys.stderr)
            raise SystemExit(2)
        out.append((label, found.identity))
    return out


def shared_inputs(root: Path, acl2: Path | None, image_acl2: Path | None
                  ) -> list[tuple[str, str]]:
    """The inputs every image shares (computed once per run)."""
    parts = [("version", KEY_VERSION), ("machine", platform.machine()),
             ("cc", compiler_version())]
    parts += toolchain_part(acl2, image_acl2)
    parts += [(f"env {name}", os.environ.get(name, "")) for name in ENVIRONMENT]
    parts += [(f"openssl {path.name}", certs.content_hash(path))
              for path in openssl_libraries()]
    for name in BUILD_FILES:
        path = root / name
        parts.append((f"file {name}", certs.content_hash(path) if path.is_file()
                      else "<missing>"))
    for path in tree_files(root):
        parts.append((f"file {path.relative_to(root).as_posix()}", certs.content_hash(path)))
    return parts


def image_inputs(root: Path, image: str, shared: list[tuple[str, str]]
                 ) -> list[tuple[str, str]]:
    import world
    profile, build, flavour = SPECS[image]
    variant = "dtn" if build.endswith("-dtn.lisp") else "default"
    worlds = [root / rel for rel in world.world_paths(variant)]
    files = followed_files(root, build)
    files += [path for path in worlds if path.is_file() and path not in files]
    umbrellas = sorted((root / "books").glob("image-world*.lisp"))
    parts = [("image", image), ("profile", profile), ("build", build), ("world", flavour)]
    parts += [(f"book {name}", certs.closure(root, name)[name])
              for name in book_names(root, files + umbrellas)]
    parts += [(f"world {path.relative_to(root).as_posix()}", certs.content_hash(path))
              for path in worlds if path.is_file()]
    return shared + parts


def digest(parts: list[tuple[str, str]]) -> str:
    hasher = hashlib.sha256()
    for label, value in parts:
        hasher.update(label.encode() + b"\0" + value.encode() + b"\0")
    return hasher.hexdigest()


def image_keys(root: Path, images: list[str], acl2: Path | None,
               image_acl2: Path | None) -> dict[str, str]:
    shared = shared_inputs(root, acl2, image_acl2)
    with certs.closure_scope():  # one walk of each book's closure, not one per image
        return {image: digest(image_inputs(root, image, shared)) for image in images}


def set_key(keys: dict[str, str]) -> str:
    return digest(sorted(keys.items()))


def reuse(store: Path, root: Path, images: list[str], acl2, image_acl2, record: Path | None,
          link: bool = True) -> int:
    keys = image_keys(root, images, acl2, image_acl2)
    name = set_key(keys)
    if record is not None:
        record.parent.mkdir(parents=True, exist_ok=True)
        record.write_text(json.dumps({"set": name, "images": keys}, sort_keys=True) + "\n")
    print(f"image_key: set {name} images "
          + " ".join(f"{image}={key[:12]}" for image, key in sorted(keys.items())))
    directory = store / name
    try:
        manifest = json.loads((directory / "MANIFEST.json").read_text())
    except (OSError, ValueError):
        print(f"image_key: no stored set at {directory}: the full path runs")
        return 1
    if not link:
        print(f"image_key: HIT {directory} (built from commit {manifest['sha']})")
        return 0
    if image_set.link(manifest["sha"], root, images, store, name=name) != 0:
        return 1
    # The images' identity source is the commit that built them.
    (root / "build" / "KEYED_SOURCE").write_text(manifest["sha"] + "\n")
    return 0


def unlink(store: Path, root: Path) -> int:
    """Remove the links into STORE that a refused or abandoned reuse left in
    ROOT/build (a symlink only; a file this tree built is never touched)."""
    build = root / "build"
    for path in sorted(build.iterdir()) if build.is_dir() else ():
        if path.is_symlink() and store.resolve() in Path(os.readlink(path)).resolve().parents:
            path.unlink()
    return 0


def publish(store: Path, root: Path, record: Path, source: str) -> int:
    saved = json.loads(record.read_text())
    return image_set.publish(root, source, store, name=saved["set"])


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("action", choices=("keys", "reuse", "publish", "unlink"))
    parser.add_argument("--no-link", action="store_true",
                        help="reuse: say whether the set is stored, link nothing")
    parser.add_argument("--tree", default=str(HERE.parent))
    parser.add_argument("--acl2")
    parser.add_argument("--image-acl2")
    parser.add_argument("--images", default="")
    parser.add_argument("--store", default=str(image_set.BASE / "keyed"))
    parser.add_argument("--record")
    parser.add_argument("--source")
    args = parser.parse_args(argv)
    root = Path(args.tree).resolve()
    images = [one for one in args.images.split(",") if one]
    unknown = [one for one in images if one not in SPECS]
    if unknown:
        print(f"image_key: no key for {', '.join(unknown)}", file=sys.stderr)
        return 2
    acl2 = Path(args.acl2) if args.acl2 else None
    image_acl2 = Path(args.image_acl2) if args.image_acl2 else acl2
    if args.action == "keys":
        keys = image_keys(root, images, acl2, image_acl2)
        print(json.dumps({"set": set_key(keys), "images": keys}, indent=1, sort_keys=True))
        return 0
    if args.action == "unlink":
        return unlink(Path(args.store), root)
    if args.action == "reuse":
        return reuse(Path(args.store), root, images, acl2, image_acl2,
                     Path(args.record) if args.record else None, not args.no_link)
    return publish(Path(args.store), root, Path(args.record), args.source)


if __name__ == "__main__":
    raise SystemExit(main())
