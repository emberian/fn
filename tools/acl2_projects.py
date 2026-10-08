"""The portable book namespace shared by certification and image loading.

ACL2 resolves the relative directory against the projects file, not cwd.
Its own reader/writer represents full book names as (:FN . "books/x.lisp")
and rebinds :FN at startup, including save-exec restarts. No certificates
are edited by the cache. Changing this contract requires a new cache key.
"""
from pathlib import Path
import json
from acl2_toolchain import PROJECT_DIRECTORIES as DIRECTORIES

ROOT = Path(__file__).resolve().parents[1]
FILENAME = "acl2-projects"
CONTENTS = "".join(f"{key} {json.dumps(path)}\n" for key, path in DIRECTORIES.items())


def projects_file(root: Path | None = None) -> Path:
    """Return this tree's checked project file, overriding ambient mappings."""
    path = (ROOT if root is None else root).resolve() / FILENAME
    if path.read_text(encoding="utf-8") != CONTENTS:
        raise ValueError(f"{path}: expected the fn project-directory contract {CONTENTS.strip()}")
    return path
