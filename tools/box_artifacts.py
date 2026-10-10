#!/usr/bin/env python3
"""The box step's artifacts: generated on a build box, never committed.

specs/wire-grammar.json (tools/protocol_emit.py --wire --write) needs the
certified wire-export world, so it is made by the box step
(tools/train.py boxstep, or its certify path) and fetched into build/box/
with stamp.json naming the sha they were made at (coordinator ruling
2026-10-09 19:50 on Builder D's registers DECISION; COORDINATION section 5:
generated files are regenerated into build/, never committed).  The
interface registry, once planning/interfaces.json, is not one of them: it is
a function of the source alone, rendered on read (tools/interface_emit.py
registry), so no tree waits on a box step for it (train 81's regen did).

Every reader takes them through `load` (or `path`), which refuses by name:
  * a committed copy at the old path (it would be read in preference by a
    tool that was not converted, and it goes stale silently);
  * an absent artifact (run the box step: `python3.12 tools/train.py boxstep
    BOX` in a train, or `python3 tools/box_artifacts.py fetch BOX` in a lane);
  * a stamp whose sha is not an ancestor of HEAD (another history's emit).
An artifact whose stamp is an ancestor of HEAD with books/, specs/ or
tests/acl2/ changed since is still read (as the committed copy was before),
and `load` says so on stderr; the train's box_step gate is what refuses it.

    python3 tools/box_artifacts.py status          # each artifact and its stamp
    python3 tools/box_artifacts.py fetch BOX       # certify and emit on BOX, fetch here
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIR = Path("build") / "box"
STAMP = "stamp.json"
# artifact name -> the committed path it replaced
ARTIFACTS = {
    "wire-grammar.json": "specs/wire-grammar.json",
}
# what the emitted artifacts depend on (tools/train.py BOX_PATHS)
SOURCE_PATHS = ("books", "specs", "tests/acl2")


class Refused(RuntimeError):
    """A box artifact cannot be read; the message names it and the remedy."""


def path(name: str, root: Path = ROOT) -> Path:
    """build/box/NAME after the committed-copy check; it need not exist."""
    if name not in ARTIFACTS:
        raise Refused(f"{name} is not a box artifact ({', '.join(ARTIFACTS)})")
    committed = root / ARTIFACTS[name]
    if committed.exists():
        raise Refused(f"{ARTIFACTS[name]} is committed again; it is a box-step artifact read "
                      f"from {DIR / name} (tools/box_artifacts.py): delete the committed copy")
    return root / DIR / name


def stamp(root: Path = ROOT) -> dict | None:
    p = root / DIR / STAMP
    return json.loads(p.read_text(encoding="utf-8")) if p.exists() else None


def _git(root: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True,
                          check=False)


def currency(root: Path = ROOT) -> tuple[str | None, list[str]]:
    """(refusal or None, the source files changed since the stamp)."""
    st = stamp(root)
    if st is None:
        return f"{DIR / STAMP} is absent: no box step has been fetched into this tree", []
    sha = str(st.get("sha", ""))
    if _git(root, "rev-parse", "--git-dir").returncode != 0:
        return None, []  # an exported tree (a release stage): the stamp is the record
    if _git(root, "merge-base", "--is-ancestor", sha, "HEAD").returncode != 0:
        return (f"the box artifacts in {DIR} were made at {sha[:12]}, which is not an ancestor "
                f"of HEAD: fetch them again (tools/box_artifacts.py fetch BOX)"), []
    changed = _git(root, "diff", "--name-only", sha, "HEAD", "--", *SOURCE_PATHS).stdout.split()
    return None, changed


def load(name: str, root: Path = ROOT) -> dict:
    p = path(name, root)
    if not p.exists():
        raise Refused(f"{DIR / name} is absent: it is made by the box step "
                      f"(python3.12 tools/train.py boxstep BOX, or "
                      f"python3 tools/box_artifacts.py fetch BOX)")
    refusal, changed = currency(root)
    if refusal:
        raise Refused(refusal)
    if changed:
        print(f"box_artifacts: {DIR / name} predates {len(changed)} change(s) under "
              f"{', '.join(SOURCE_PATHS)} (first: {changed[0]}); the train's box step remakes it",
              file=sys.stderr)
    return json.loads(p.read_text(encoding="utf-8"))


def write_stamp(root: Path, sha: str, box: str, ran_at: str) -> None:
    (root / DIR).mkdir(parents=True, exist_ok=True)
    (root / DIR / STAMP).write_text(json.dumps({"sha": sha, "box": box, "ran_at": ran_at},
                                               indent=2, sort_keys=True) + "\n")


def fetch(box: str, root: Path = ROOT) -> int:
    """The box step's certify and emits on BOX at HEAD (tools/train.py BOX_CMD),
    the artifacts fetched into build/box/ and stamped with HEAD."""
    sys.path.insert(0, str(root / "tools"))
    import train  # noqa: E402  (BOX_CMD is the box step's one definition)
    if _git(root, "status", "--porcelain", "--untracked-files=no").stdout.strip():
        print("box_artifacts: the tree is dirty; the box step ships HEAD", file=sys.stderr)
        return 1
    head = _git(root, "rev-parse", "HEAD").stdout.strip()
    argv = ["sh", "tools/remote_check.sh", box]
    for name in ARTIFACTS:
        argv += ["--fetch", str(DIR / name)]
    argv += ["--cmd", train.BOX_CMD]
    rc = subprocess.run(argv, cwd=root).returncode
    if rc == 0:
        write_stamp(root, head, box, head)
    return rc


def main(argv: list[str]) -> int:
    if argv[:1] == ["fetch"] and len(argv) == 2:
        return fetch(argv[1])
    if argv[:1] == ["status"]:
        print(json.dumps(stamp() or {}, sort_keys=True))
        for name in ARTIFACTS:
            try:
                p = path(name)
                print(f"{name}: {'present' if p.exists() else 'absent'} at {p.relative_to(ROOT)}")
            except Refused as error:
                print(f"{name}: REFUSED {error}")
        refusal, changed = currency()
        print(f"currency: {refusal or 'ok'}; {len(changed)} source change(s) since the stamp")
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
