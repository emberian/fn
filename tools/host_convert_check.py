#!/usr/bin/env python3
"""The gates a host-code conversion must pass, as ONE command, before any image build.

    make host-convert-check [FILE=host/native/x.lisp]
    python3 tools/host_convert_check.py [FILE ...]          # on a box
    tools/remote_check.sh auto --cmd 'make host-convert-check FILE=host/native/x.lisp'

A lane that moves host code into a book, or adds a host include-book or a
host-called entry, met three gates one image build at a time (obstructions-5
item 34): limits-live-5 lost an image build to the umbrellas
(books/image-world*) that `tools/extract/world.py` regenerates, and
decision-keystones-3 one to a `definterface` whose :class the image build's
world refused (`::ideal` against a :common-lisp-compliant entry).  Each gate
is cheap on its own; what cost the build was learning them in sequence.
This runs all of them, in order, and reports every verdict (it does not stop
at the first red):

  world       tools/extract/world.py --check: the umbrellas are what the
              build scripts include (fix: python3 tools/extract/world.py,
              then certify books/image-world*);
  interfaces  tools/interface_emit.py --check: the registry, the extraction
              roots and the host binding agree with the definterface forms
              (fix: python3 tools/interface_emit.py --write, on a box);
  forward     tools/host_check.py --forward: no ld host file calls a name
              only a later form defines;
  names       tools/host_check.py --world: every name a raw file hands to
              fnn-core*/fnn-call is in its image's world;
  load        tools/host_check.py --load [FILE]: the raw files, in build
              order through FILE, in one bare ACL2 (errors, arity, macro
              order, names nothing defines);
  class       tools/host_check.py (its default): each image's ACL2-mode
              prefix -- every include-book and host `ld`, through
              `(ld "host/interfaces.lisp")` -- in the CERTIFIED world, which
              is where definterface checks each :class, :kinds and
              :delegates and admits the generated `-by-definition`
              equations.  Needs the umbrellas' certificates installed; NOT
              RUN without them, and NOT RUN is red here.

Exit 0 when every gate is green; 1 when any is red or did not run.  It reads
the whole tree and starts ACL2, so it refuses the laptop (FN_LAPTOP_OK=1
overrides).
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

FIXES = {
    "world": "python3 tools/extract/world.py (writes the umbrellas), then certify "
             "books/image-world, -dtn and -store-test",
    "interfaces": "python3 tools/interface_emit.py --write on a box, and commit what it writes",
    "forward": "move the definition above its first use in build order",
    "names": "define the name in a book the image includes, or stop calling it",
    "load": "tools/host_check.py --load --log-dir build/host-load FILE names the form",
    "class": "build/host-translate/build.log names the refused definterface; a certified "
             "umbrella is needed (tools/certs.py install, or certify books/image-world*)",
}


def gates(files: list[str]) -> list[tuple[str, list[str]]]:
    python = sys.executable
    return [
        ("world", [python, "tools/extract/world.py", "--check"]),
        ("interfaces", [python, "tools/interface_emit.py", "--check"]),
        ("forward", [python, "tools/host_check.py", "--forward"]),
        ("names", [python, "tools/host_check.py", "--world"]),
        ("load", [python, "tools/host_check.py", "--load", *files]),
        ("class", [python, "tools/host_check.py"]),
    ]


def verdict(code: int) -> str:
    return {0: "ok", 2: "NOT RUN"}.get(code, "FAIL")


def run(files: list[str], runner=None) -> int:
    if runner is None:
        def runner(command):
            return subprocess.run(command, cwd=ROOT).returncode
    results = []
    for name, command in gates(files):
        print(f"== host-convert-check: {name}: {' '.join(command[1:])}", flush=True)
        code = runner(command)
        results.append((name, code))
        print(f"== host-convert-check: {name} {verdict(code)}", flush=True)
    red = [(name, code) for name, code in results if code != 0]
    print("host-convert-check: " + ", ".join(f"{name} {verdict(code)}" for name, code in results))
    for name, code in red:
        print(f"  {name} {verdict(code)}: {FIXES[name]}")
    print("host-convert-check: " + ("GREEN: build the images" if not red else
                                     f"RED ({len(red)} of {len(results)}): no image build yet"))
    return 1 if red else 0


def main(argv: list[str] | None = None) -> int:
    files = [word for word in (sys.argv[1:] if argv is None else argv) if word]
    import acl2_slots  # noqa: E402
    acl2_slots.refuse_on_laptop("tools/host_convert_check.py")
    return run(files)


if __name__ == "__main__":
    raise SystemExit(main())
