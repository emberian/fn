#!/usr/bin/env python3
"""Build boxes beyond hbox and persvati, read from one small config file.

hbox and persvati are fixed rows (tools/farm.py HOSTS, tools/native_box.sh,
tools/remote_check.sh, tools/boxes.sh).  A box rented for a while -- the
fn-burst cloud boxes of 2026-10-04 -- is a row in a file instead, so adding
or removing it touches no code and no commit:

    ~/.config/fn/boxes.json          ($FN_BOXES_FILE overrides the path)

    {"boxes": {"cloud1": {"like": "hbox", "until": "2026-10-04T19:57:00Z",
                          "cores": 8}}}

The name is the ssh host (an ~/.ssh/config alias) and, on the box itself,
its hostname, so the box answers acl2_slots.apply_box_defaults like hbox
does.  `like` names the fixed row whose toolchain the box holds byte for
byte at the same absolute paths (tools/acl2_toolchain.py then computes the
same identity there, so the two caches are interchangeable); every other
field defaults to that row's and may be given:

    cache, wrap        the certificate cache and build wrapper (farm HOSTS)
    scratch            the scratch base (native runs, remote_check trees)
    gates              the proof_repl / gate tree root
    images             where published image sets live ("" for none)
    openssl            bundled (/tank/fn/toolchains/openssl-3.5.8) or system
    check_jobs         remote_check's default make -j ("" for none)
    pick               false keeps the box out of tools/boxes.sh --pick
    until              UTC expiry; a row past it is ignored, so a torn-down
                       box drops out even when the file outlives it

    python3 tools/box_table.py names       the live extra boxes, one per line
    python3 tools/box_table.py pick        the live boxes --pick may choose
    python3 tools/box_table.py row BOX     shell assignments for one box:
                                           BASE CACHE WRAP IMAGES_BASE OPENSSL
                                           GATES CHECK_JOBS (exit 2 unknown)
    python3 tools/box_table.py env BOX     the `export FN_ACL2=... FN_CERT_CACHE=...
                                           [FN_IMAGE_ACL2=...]` a remote command
                                           runs under, for any box (hbox,
                                           persvati or a live row); a leading ~
                                           becomes $HOME for the box's shell
"""
from __future__ import annotations

import datetime as dt
import json
import os
from pathlib import Path
import re
import sys

DEFAULT_FILE = "~/.config/fn/boxes.json"
NAME = re.compile(r"[a-z][a-z0-9-]{0,30}")
PATH = re.compile(r"[A-Za-z0-9_./~-]*")
# What each fixed row holds beyond tools/farm.py HOSTS.
FIXED = {
    "hbox": {"scratch": "/tank/fn/scratch", "gates": "/tank/fn/gates",
             "images": "/tank/fn/images", "openssl": "bundled", "check_jobs": "6"},
    "persvati": {"scratch": "~/fn-gates", "gates": "fn-gates", "images": "",
                 "openssl": "system", "check_jobs": ""},
}
FARM_FIELDS = ("acl2", "image_acl2", "load_acl2", "sbcl", "cache", "wrap")


def config_path(environ=None) -> Path:
    environ = os.environ if environ is None else environ
    return Path(os.path.expanduser(environ.get("FN_BOXES_FILE") or DEFAULT_FILE))


def _farm_literal() -> dict:
    import ast  # noqa: E402
    tree = ast.parse((Path(__file__).resolve().parent / "farm.py").read_text(encoding="utf-8"))
    for node in tree.body:
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and getattr(node.targets[0], "id", None) == "HOSTS"):
            return ast.literal_eval(node.value)
    raise SystemExit("box_table: tools/farm.py has no HOSTS table")


def extra_boxes(fixed: dict | None = None, environ=None, now: dt.datetime | None = None) -> dict:
    """{name: full row} for each live box in the config file; {} without one.

    A row carries the farm fields (FARM_FIELDS, from its `like` box unless
    given) and scratch, gates, images, openssl, check_jobs, pick, cores."""
    path = config_path(environ)
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {}
    except (OSError, ValueError) as error:
        raise SystemExit(f"box_table: {path}: {error}") from None
    fixed = _farm_literal() if fixed is None else fixed
    now = now or dt.datetime.now(dt.timezone.utc)
    rows = {}
    for name, given in (data.get("boxes") or {}).items():
        if not NAME.fullmatch(name) or name in FIXED or name == "laptop":
            raise SystemExit(f"box_table: {path}: bad box name {name!r}")
        like = given.get("like", "hbox")
        if like not in FIXED or like not in fixed:
            raise SystemExit(f"box_table: {path}: {name}: like {like!r} is not hbox or persvati")
        until = given.get("until")
        if until:
            expiry = dt.datetime.fromisoformat(until.replace("Z", "+00:00"))
            if expiry <= now:
                continue
        row = {field: fixed[like][field] for field in FARM_FIELDS if field in fixed[like]}
        row.update(FIXED[like])
        row.update({"pick": True, "cores": None, "like": like, "until": until})
        row.update({key: value for key, value in given.items() if key != "like"})
        row["check_jobs"] = str(row["check_jobs"] or "")
        for field in ("acl2", "image_acl2", "load_acl2", "sbcl", "cache", "wrap",
                      "scratch", "gates", "images"):
            if not PATH.fullmatch(str(row.get(field, ""))):
                raise SystemExit(f"box_table: {path}: {name}: bad {field} {row[field]!r}")
        if row["openssl"] not in ("bundled", "system"):
            raise SystemExit(f"box_table: {path}: {name}: openssl is bundled or system")
        rows[name] = row
    return rows


def farm_rows(fixed: dict, environ=None) -> dict:
    """The extra boxes as tools/farm.py HOSTS rows (farm fields only)."""
    return {name: {field: row[field] for field in FARM_FIELDS if field in row}
            for name, row in extra_boxes(fixed, environ).items()}


def env_line(box: str, environ=None) -> str | None:
    """The toolchain exports for BOX, resolved HERE (where the box table
    lives), so the box needs no copy of it: remote_check's run script used
    to read the box tree's farm.py HOSTS literal, which names only hbox and
    persvati, and refused every rented box with "no FN_ACL2"."""
    fixed = _farm_literal()
    hosts = dict(fixed)
    hosts.update(farm_rows(fixed, environ))
    row = hosts.get(box)
    if not row or not row.get("acl2"):
        return None
    def shell(path: str) -> str:
        return "$HOME/" + path[2:] if path.startswith("~/") else path
    words = [f"FN_ACL2={shell(row['acl2'])}", f"FN_CERT_CACHE={shell(row.get('cache', ''))}"]
    if row.get("image_acl2"):
        words.append(f"FN_IMAGE_ACL2={shell(row['image_acl2'])}")
    return "export " + " ".join(words)


def main(argv: list[str]) -> int:
    if argv and argv[0] == "env":
        line = env_line(argv[1]) if len(argv) == 2 else None
        if line is None:
            print(f"box_table: no toolchain row for box {argv[1] if len(argv) > 1 else ''!r}",
                  file=sys.stderr)
            return 2
        print(line)
        return 0
    if not argv or argv[0] not in ("names", "pick", "row"):
        sys.stderr.write(__doc__.split("\n\n")[-1] + "\n")
        return 2
    rows = extra_boxes()
    if argv[0] == "names":
        print("\n".join(rows))
        return 0
    if argv[0] == "pick":
        print("\n".join(name for name, row in rows.items() if row.get("pick", True)))
        return 0
    if len(argv) != 2 or argv[1] not in rows:
        known = ", ".join(sorted(rows)) or "none configured"
        print(f"box_table: no live row for box {argv[1] if len(argv) > 1 else ''!r} "
              f"(extra boxes: {known}; {config_path()})", file=sys.stderr)
        return 2
    row = rows[argv[1]]
    for var, field in (("BASE", "scratch"), ("CACHE", "cache"), ("WRAP", "wrap"),
                       ("IMAGES_BASE", "images"), ("OPENSSL", "openssl"),
                       ("GATES", "gates"), ("CHECK_JOBS", "check_jobs")):
        print(f"{var}='{row.get(field) or ''}'")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
