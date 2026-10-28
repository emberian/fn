#!/usr/bin/env python3
"""The completeness control for tools/image_key.py: what a build reads, against what its key covers.

    python3 tools/image_key_control.py analyze --tree T --image NAME --trace strace.txt

TRACE is `strace -f -e trace=openat,open,execve -o FILE` over one
tools/build_native_host.sh build in tree T.  Every file the build opened for
reading (or executed) is placed in one class:

  covered     a file the image's key hashes (tools/image_key.py covered_files),
              or the certificate, port or compiled file of a book whose source
              it hashes;
  output      under T/build, T/tmp or the log: written by the build itself;
  system-book a file of the ACL2 installation's books/ below a system book the
              world includes (the certificate chain ACL2 checks at include);
  toolchain   under the ACL2/SBCL toolchain directory or OpenSSL prefix (the
              key hashes the launcher chain, the saved core, the runtime,
              libcrypto/libssl, the ACL2 system books the world includes and
              SBCL's contribs; a file of those not so covered is listed);
  system      the operating system's own (/usr, /lib, /etc, /proc, /sys, /dev,
              /var, /tmp): the key records the machine type and the C
              compiler's version, and nothing else;
  UNCOVERED   a file under T that the key does not cover.

The exit status is 1 when anything is UNCOVERED.  Saved SBCL cores are not
byte-reproducible (two builds of identical inputs differ in a sixth of their
bytes), so this -- the read set -- is how the key's completeness is judged.
"""
from __future__ import annotations

import argparse
from collections import Counter
import os
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import image_key  # noqa: E402

OPEN = re.compile(r'^(?:\d+\s+)?(?:openat|open)\((?:AT_FDCWD|\d+<[^>]*>), "((?:[^"\\]|\\.)*)", ([A-Z_|]+)')
EXEC = re.compile(r'^(?:\d+\s+)?execve\("((?:[^"\\]|\\.)*)"')
SYSTEM = ("/usr", "/lib", "/lib64", "/etc", "/proc", "/sys", "/dev", "/var", "/tmp", "/run", "/bin",
          "/sbin", "/opt")
WRITE_FLAGS = ("O_WRONLY", "O_RDWR", "O_CREAT")


def reads(trace: Path, tree: Path) -> tuple[set[str], set[str]]:
    opened, executed = set(), set()
    for line in trace.read_text(errors="replace").splitlines():
        if " = -1 " in line or " ENOENT" in line:
            continue
        match = EXEC.match(line)
        if match:
            executed.add(match.group(1))
            continue
        match = OPEN.match(line)
        if match and not any(flag in match.group(2) for flag in WRITE_FLAGS):
            path = match.group(1)
            opened.add(path if path.startswith("/") else str(tree / path))
    return opened, executed


def classify(paths: set[str], tree: Path, covered: set[Path], toolchains: list[str],
             books: Path | None = None) -> dict[str, list[str]]:
    classes: dict[str, list[str]] = {"covered": [], "output": [], "system-book": [],
                                     "toolchain": [], "system": [], "UNCOVERED": [],
                                     "other": []}
    for text in sorted(paths):
        path = Path(os.path.normpath(text))
        try:
            real = path.resolve()
        except OSError:
            real = path
        try:
            relative = real.relative_to(tree)
        except ValueError:
            relative = None
        if relative is not None:
            if real in covered:
                classes["covered"].append(text)
            elif relative.parts[:1] in (("build",), ("tmp",)) or "__pycache__" in relative.parts:
                classes["output"].append(text)
            elif real.is_dir():
                classes["covered"].append(text)  # a directory listing; its files are judged by name
            else:
                classes["UNCOVERED"].append(text)
        elif real in covered:
            classes["covered"].append(text)
        elif books is not None and books in real.parents:
            # Reached through the included system books' certificates, which
            # ACL2 checks against the books they include.
            classes["system-book"].append(text)
        elif any(text.startswith(prefix) for prefix in toolchains):
            classes["toolchain"].append(text)
        elif text.startswith(SYSTEM):
            classes["system"].append(text)
        else:
            classes["other"].append(text)
    return classes


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("action", choices=("analyze",))
    parser.add_argument("--tree", required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--trace", required=True)
    parser.add_argument("--acl2", required=True)
    parser.add_argument("--image-acl2")
    parser.add_argument("--toolchain", action="append",
                        default=["/tank/fn/toolchains/", "/tank/fn/sbcl"])
    args = parser.parse_args(argv)
    tree = Path(args.tree).resolve()
    opened, executed = reads(Path(args.trace), tree)
    image_key.toolchain_part(Path(args.acl2), Path(args.image_acl2 or args.acl2))
    covered = image_key.covered_files(tree, args.image)
    books = image_key._INSTALL["books"]
    classes = classify(opened | executed, tree, covered, args.toolchain, books)
    print(f"image_key_control: {args.image}: {len(opened)} files opened, {len(executed)} executed")
    for name, found in classes.items():
        print(f"  {name:10} {len(found)}")
    for name in ("UNCOVERED", "other"):
        for text in classes[name]:
            print(f"    {name}: {text}")
    tools = Counter(Path(t).parent.as_posix() for t in classes["toolchain"])
    for directory, count in tools.most_common(12):
        print(f"    toolchain {count:5} {directory}")
    system = Counter("/".join(Path(t).parts[:3]) for t in classes["system"])
    for directory, count in system.most_common(12):
        print(f"    system    {count:5} {directory}")
    return 1 if classes["UNCOVERED"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
