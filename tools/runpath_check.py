#!/usr/bin/env python3
"""No Python on the path a deployed fn node executes (D35).

A deployed node runs `bin/fn` (packaging/fn, /bin/sh), which execs the frozen
launcher `libexec/fn/fn-host` (/bin/sh, written by
packaging/freeze-native-image.sh), which execs the copied SBCL runtime on the
saved core.  The core loads libsodium and the OpenSSL 3.5 pair by dlopen and
starts other programs only where host/ calls a process primitive.  The
service manager starts `bin/fn operator CONFIG run` (the systemd unit, the
launchd plist, the OpenBSD rc.d script).  Python stays for clients and tests.

Two modes:

  runpath_check.py                  static: the tree (make check)
  runpath_check.py --tree DIR       an unpacked release (fn-REV12/)
  runpath_check.py --tarball FILE   a release tarball, unpacked to a temp dir

Static mode lists and checks
  * every process-starting form in host/**/*.lisp (run-program, spawn, exec,
    popen, fork, system): each must be in PROCESS_SITES below with its
    reason, and each listed site must still exist;
  * every shared-object name the image may dlopen (string literals in the
    candidate functions of host/native/crypto.lisp and tls.lisp);
  * the shipped packaging: the launcher, the frozen-launcher template, the
    service files.  A shell script must be `#!/bin/sh`; every external
    command it names is listed and must be neither Python nor, where it
    resolves on this machine, a script whose interpreter is Python.

Tree mode walks every file of the release (HST-018): no *.py/*.pyc, no
Python shebang; every executable is a /bin/sh script or an ELF object; the
scripts' external commands are checked as above, and a command named by an
absolute path must be the platform's shell or rc.subr; a symbolic link must
stay inside the release; every ELF object's program interpreter must be the
platform's C library loader, its DT_RPATH/DT_RUNPATH may not name a
directory outside the release, and each DT_NEEDED name must be a file the
release carries or the platform's C library (PLATFORM_LIBC); every shared
object name the saved core may dlopen (the lib*.so strings in the core) must
be carried by the release, the C library, or the system TLS library D35
chose (SYSTEM_TLS); each service file (template) must start `PREFIX/bin/fn`.

It cannot decide what an operator-supplied program is (the ION helper path
is an argument), what a shell variable holds at run time (it lists
`$var` commands as such), or what the dynamic loader of the target system
resolves a DT_NEEDED name to.  Exit 0 clean, 1 a finding, 2 usage.
"""
from __future__ import annotations

import argparse
import os
import re
import shutil
import struct
import sys
import tarfile
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Every form in host/ that starts another program, by (file, enclosing defun).
PROCESS_SITES = {
    ("host/native/workflow.lisp", "fnn-workflow-ion-run-helper"):
        "the operator-named pinned ION helper of `fn --fn app-journal "
        "workflow-ion-submit ... PINNED_HELPER ...` (experimental offline "
        "ION/LTP; docs/operator.md); :search nil, so only the absolute path "
        "the operator gives; not on the NNTP service or operator path",
}

PROCESS_RE = re.compile(
    r"(?<![\w:-])(?:sb-ext:|sb-ext::|uiop:|sb-impl::|sb-posix:)?"
    r"(run-program|launch-program|spawn|posix-spawn|execv|execvp|execve|"
    r"popen|fork)(?![\w-])", re.IGNORECASE)
ALIEN_CALL_RE = re.compile(r'"(system|popen|execv|execvp|execve|fork|posix_spawn)"')
DEFUN_RE = re.compile(r"^\((?:defun|defmacro|defmethod)\s+([^\s()]+)", re.MULTILINE)
LIB_LITERAL_RE = re.compile(r'"([^"\s]*lib[^"\s]*\.(?:so[.\d]*|dylib)[^"\s]*)"')
LIB_SOURCES = ("host/native/crypto.lisp", "host/native/tls.lisp")

# Files a release ships whose commands run on the deployed path.
SHIPPED_SCRIPTS = ("packaging/fn", "packaging/install.sh")
SHIPPED_SERVICES = ("packaging/fn-native.service.in", "packaging/net.fn.native.plist.in",
                    "packaging/fn.rc.in")
FREEZE_SCRIPT = "packaging/freeze-native-image.sh"

SH_BUILTINS = {
    "cd", "pwd", "echo", "printf", "export", "unset", "set", "[", "test", "exit",
    ":", "return", "shift", "trap", "read", "local", "exec", "eval", "true",
    "false", "command", "type", "wait", "umask", "readonly", ".", "break",
    "continue", "getopts", "hash", "kill", "ulimit",
    "rc_cmd",  # OpenBSD rc.subr's dispatcher, a /bin/ksh function
}
SH_KEYWORDS = {"if", "then", "elif", "else", "fi", "case", "esac", "do", "done",
               "for", "while", "until", "in", "!", "{", "}", "function"}
PYTHON_RE = re.compile(r"(?:^|/)(?:python[\d.]*|pip[\d.]*|py)$|libpython", re.IGNORECASE)
# rc.subr is OpenBSD's /bin/sh library; its variables name the daemon.
RC_VARIABLES = {"daemon", "daemon_flags", "daemon_user", "daemon_logger",
                "daemon_timeout", "daemon_execdir", "rc_bg", "rc_reload",
                "rc_usercheck", "rc_cmd", "pexp"}


# The platform's C library, the one thing outside the release an ELF object
# may name (ld.so resolves it): glibc on Linux, libc on OpenBSD.
PLATFORM_LIBC = re.compile(
    r"^(?:libc\.so(?:\.[\d.]+)?|libm\.so(?:\.[\d.]+)?|libdl\.so\.2|libpthread\.so(?:\.[\d.]+)?|"
    r"librt\.so\.1|ld-linux-x86-64\.so\.2|libutil\.so(?:\.[\d.]+)?|libc\+\+abi\.so[\d.]*)$")
LIBC_LOADERS = {"/lib64/ld-linux-x86-64.so.2", "/usr/libexec/ld.so"}
# The system TLS library the image loads by dlopen: D35 as ember confirmed it
# on 2026-09-26 ("no OpenSSL 3.5, the system libssl"; lane crypto-deps).
SYSTEM_TLS = re.compile(r"^lib(?:ssl|crypto)\.so(?:\.[\d.]+)?$")
# Absolute paths a shipped script may run: the shell and OpenBSD's rc.subr.
SYSTEM_SCRIPTS = {"/bin/sh", "/bin/ksh", "/etc/rc.d/rc.subr"}
CORE_WIDE_RE = re.compile(rb"(?:[A-Za-z0-9_+./-]\x00\x00\x00){6,256}")
CORE_LIB_RE = re.compile(rb"lib[A-Za-z0-9_+-][A-Za-z0-9_+.-]*?\.so(?:\.\d+)*")


class Findings:
    def __init__(self) -> None:
        self.problems: list[str] = []
        self.lines: list[str] = []

    def fail(self, message: str) -> None:
        self.problems.append(message)

    def note(self, message: str) -> None:
        self.lines.append(message)


def strip_lisp_comments(text: str) -> str:
    """Blank `;` comments and #| |# blocks, keeping string literals and line numbers."""
    out = []
    i, n = 0, len(text)
    in_string = False
    while i < n:
        c = text[i]
        if in_string:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if c == '"':
                in_string = False
            i += 1
            continue
        if c == '"':
            in_string = True
            out.append(c)
        elif c == ";":
            while i < n and text[i] != "\n":
                i += 1
            continue
        elif c == "#" and i + 1 < n and text[i + 1] == "|":
            end = text.find("|#", i + 2)
            end = n if end < 0 else end + 2
            out.append("".join(ch if ch == "\n" else " " for ch in text[i:end]))
            i = end
            continue
        elif c == "#" and i + 1 < n and text[i + 1] == "\\":
            out.append(text[i:i + 3])
            i += 3
            continue
        else:
            out.append(c)
        i += 1
    return "".join(out)


def enclosing_defun(text: str, offset: int) -> str:
    name = "<toplevel>"
    for match in DEFUN_RE.finditer(text):
        if match.start() > offset:
            break
        name = match.group(1).lower()
    return name


def scan_process_sites(root: Path, findings: Findings) -> None:
    seen = set()
    for path in sorted((root / "host").rglob("*.lisp")):
        rel = path.relative_to(root).as_posix()
        text = strip_lisp_comments(path.read_text(encoding="utf-8", errors="replace"))
        code = re.sub(r'"(?:[^"\\]|\\.)*"', lambda m: '"' + " " * (len(m.group(0)) - 2) + '"', text)
        hits = [(m.start(), m.group(0)) for m in PROCESS_RE.finditer(code)]
        hits += [(m.start(), m.group(0)) for m in ALIEN_CALL_RE.finditer(text)]
        for offset, form in hits:
            line = text.count("\n", 0, offset) + 1
            key = (rel, enclosing_defun(text, offset))
            seen.add(key)
            if key in PROCESS_SITES:
                findings.note(f"process site {rel}:{line} {form} in {key[1]}: {PROCESS_SITES[key]}")
            else:
                findings.fail(f"unlisted process site {rel}:{line} {form} in {key[1]} "
                              "(add it to PROCESS_SITES with what it runs, or remove it)")
    for key in PROCESS_SITES:
        if key not in seen:
            findings.fail(f"PROCESS_SITES lists {key[0]} {key[1]}, which no longer starts a program")


def scan_libraries(root: Path, findings: Findings) -> None:
    for rel in LIB_SOURCES:
        path = root / rel
        if not path.exists():
            findings.fail(f"library source missing: {rel}")
            continue
        text = strip_lisp_comments(path.read_text(encoding="utf-8"))
        names = sorted(set(LIB_LITERAL_RE.findall(text)))
        for name in names:
            if PYTHON_RE.search(Path(name).name):
                findings.fail(f"{rel} may dlopen {name}")
        findings.note(f"dlopen candidates in {rel}: {' '.join(names)}")


def split_commands(line: str) -> list[str]:
    """The first word of each simple command on one shell line (crude, for
    the small shipped scripts; quoted separators are not special)."""
    out = []
    line = re.sub(r"'[^']*'", "''", line)
    # An arithmetic expansion runs no command: `$(( (n + 1) / 2 ))'.
    line = re.sub(r"\$\(\((?:[^()]|\([^()]*\))*\)\)", "ARITH", line)
    # A double-quoted word is data unless it is one expansion ("$image") or
    # holds a command substitution, whose words are commands.
    line = re.sub(r'"([^"]*)"', lambda m: m.group(0) if "$(" in m.group(1) else (
        m.group(1) if re.fullmatch(r"\$[\w{}/.-]*", m.group(1)) else "STR"), line)
    pieces = re.split(r"(\$\(|`|\|\||&&|;|\||\(|\))", line)
    for index in range(0, len(pieces), 2):
        part = pieces[index]
        # A word glued to a closing parenthesis continues it: `$(pwd)/fn-host'.
        if index and pieces[index - 1] == ")" and part[:1] not in ("", " ", "\t"):
            continue
        words = part.strip().split()
        while words and (re.match(r"^[A-Za-z_][A-Za-z0-9_]*=", words[0])
                         or words[0] in SH_KEYWORDS):
            words = words[1:]
        if words and words[0] == "exec":
            words = words[1:]
        if words:
            out.append(words[0].strip('"'))
    return out


def resolve_python_script(command: str) -> str | None:
    """If COMMAND resolves on this machine to a script run by Python, say so."""
    path = command if "/" in command else shutil.which(command)
    if not path or not os.path.isfile(path):
        return None
    try:
        with open(path, "rb") as handle:
            head = handle.read(256)
    except OSError:
        return None
    if head.startswith(b"#!"):
        interp = head[2:].split(b"\n", 1)[0].decode("latin-1")
        if re.search(r"python", interp, re.IGNORECASE):
            return f"{path} is run by {interp.strip()}"
    return None


def check_shell_script(label: str, text: str, findings: Findings) -> list[str]:
    first = text.split("\n", 1)[0]
    if first.strip() not in ("#!/bin/sh", "#!/bin/ksh"):
        findings.fail(f"{label}: interpreter is {first.strip()!r}, not /bin/sh")
    commands = []
    body = re.sub(r"\\\n", " ", text)
    for line in body.splitlines()[1:]:
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        stripped = re.sub(r"\s#.*$", "", stripped)
        for word in split_commands(stripped):
            if word in SH_BUILTINS or not word:
                continue
            commands.append(word)
    external = []
    for word in dict.fromkeys(commands):
        if word.startswith("$") or word.startswith('"$'):
            external.append(word)
            continue
        if PYTHON_RE.search(word):
            findings.fail(f"{label}: runs {word}")
        why = None if word.startswith("$") else resolve_python_script(word)
        if why:
            findings.fail(f"{label}: {word} needs Python ({why})")
        if re.match(r"^[A-Za-z0-9_./-]+$", word) and not re.match(r"^[0-9]", word):
            external.append(word)
    findings.note(f"{label}: /bin/sh; commands: {' '.join(external) or '(builtins only)'}")
    return external


def freeze_launcher_template(root: Path) -> str:
    """The launcher text packaging/freeze-native-image.sh echoes, as shipped."""
    text = (root / FREEZE_SCRIPT).read_text(encoding="utf-8")
    lines = []
    for match in re.finditer(r"^\s*echo '([^']*)'$", text, re.MULTILINE):
        lines.append(match.group(1))
    lines.append('exec "$here/runtime/sbcl" --core "$here/fn-host.core"')
    return "\n".join(lines) + "\n"


def check_service(label: str, text: str, findings: Findings, prefix: str | None) -> None:
    starts = re.findall(r"^ExecStart=(\S+)", text, re.MULTILINE)
    starts += re.findall(r"<key>ProgramArguments</key>\s*<array>\s*<string>([^<]+)</string>", text)
    starts += re.findall(r"^daemon=\"?([^\"\s]+)", text, re.MULTILINE)
    if not starts:
        findings.fail(f"{label}: names no program it starts")
    for program in starts:
        if PYTHON_RE.search(program):
            findings.fail(f"{label}: starts {program}")
        if not program.endswith("/bin/fn"):
            findings.fail(f"{label}: starts {program}, not PREFIX/bin/fn")
        if prefix is not None and not program.startswith(prefix):
            findings.fail(f"{label}: starts {program}, outside the release prefix {prefix}")
        findings.note(f"{label}: starts {program}")
    if "rc.subr" in text or label.endswith(".rc.in") or "/rc.d/" in label:
        for match in re.finditer(r"^\s*([A-Za-z_]+)=", text, re.MULTILINE):
            if match.group(1) not in RC_VARIABLES:
                findings.fail(f"{label}: unexpected rc variable {match.group(1)}")


def static_check(root: Path) -> Findings:
    findings = Findings()
    scan_process_sites(root, findings)
    scan_libraries(root, findings)
    for rel in SHIPPED_SCRIPTS:
        check_shell_script(rel, (root / rel).read_text(encoding="utf-8"), findings)
    check_shell_script(f"{FREEZE_SCRIPT} (frozen launcher)", freeze_launcher_template(root),
                       findings)
    for rel in SHIPPED_SERVICES:
        path = root / rel
        if path.exists():
            check_service(rel, path.read_text(encoding="utf-8"), findings, None)
        else:
            findings.fail(f"shipped service file missing: {rel}")
    return findings


def elf_needed(data: bytes) -> list[str] | None:
    """DT_NEEDED names of a 64-bit little-endian ELF object, or None if not ELF64LE."""
    facts = elf_facts(data)
    return None if facts is None else facts["needed"]


def elf_facts(data: bytes) -> dict | None:
    """DT_NEEDED, DT_RPATH/DT_RUNPATH and PT_INTERP of an ELF64LE object."""
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        return None
    interp = None
    phoff, = struct.unpack_from("<Q", data, 0x20)
    phentsize, phnum = struct.unpack_from("<HH", data, 0x36)
    for i in range(phnum):
        base = phoff + i * phentsize
        if base + 56 > len(data):
            break
        p_type, = struct.unpack_from("<I", data, base)
        if p_type == 3:  # PT_INTERP
            p_offset, = struct.unpack_from("<Q", data, base + 8)
            p_filesz, = struct.unpack_from("<Q", data, base + 32)
            interp = data[p_offset:p_offset + p_filesz].rstrip(b"\0").decode("latin-1")
    shoff, = struct.unpack_from("<Q", data, 0x28)
    shentsize, shnum = struct.unpack_from("<HH", data, 0x3A)
    sections = []
    for i in range(shnum):
        base = shoff + i * shentsize
        if base + 64 > len(data):
            break
        sh_type, = struct.unpack_from("<I", data, base + 4)
        sh_offset, sh_size = struct.unpack_from("<QQ", data, base + 0x18)
        sh_link, = struct.unpack_from("<I", data, base + 0x28)
        sections.append((sh_type, sh_offset, sh_size, sh_link))
    needed, rpaths = [], []
    for sh_type, offset, size, link in sections:
        if sh_type != 6 or link >= len(sections):  # SHT_DYNAMIC
            continue
        str_offset = sections[link][1]
        for pos in range(offset, offset + size, 16):
            tag, val = struct.unpack_from("<qQ", data, pos)
            if tag == 0:
                break
            if tag in (1, 15, 29):  # DT_NEEDED, DT_RPATH, DT_RUNPATH
                end = data.index(b"\0", str_offset + val)
                text = data[str_offset + val:end].decode("latin-1")
                (needed if tag == 1 else rpaths).append(text)
    return {"needed": needed, "rpaths": rpaths, "interp": interp}


def core_dlopen_names(path: Path) -> set[str]:
    """The lib*.so names a saved core carries as strings (what it may dlopen)."""
    names: set[str] = set()
    tail = b""
    with open(path, "rb") as handle:
        while True:
            chunk = handle.read(1 << 24)
            if not chunk:
                break
            block = tail + chunk
            names.update(m.group(0).decode("latin-1") for m in CORE_LIB_RE.finditer(block))
            # SBCL keeps a (simple-array character) as UTF-32: 4 octets a character.
            for run in CORE_WIDE_RE.finditer(block):
                text = run.group(0).decode("utf-32-le").encode("latin-1")
                names.update(m.group(0).decode("latin-1") for m in CORE_LIB_RE.finditer(text))
            tail = block[-512:]
    return names


def tree_check(top: Path) -> Findings:
    findings = Findings()
    if not (top / "bin" / "fn").is_file():
        findings.fail(f"{top}: no bin/fn")
        return findings
    fasls = 0
    carried = {p.name for p in top.rglob("*") if p.is_file()}
    for path in sorted(p for p in top.rglob("*") if p.is_file() or p.is_symlink()):
        rel = path.relative_to(top).as_posix()
        if path.is_symlink():
            target = os.readlink(path)
            if PYTHON_RE.search(target):
                findings.fail(f"{rel}: links to {target}")
            resolved = os.path.normpath(os.path.join(os.path.dirname(str(path)), target))
            if os.path.isabs(target) or not (resolved + "/").startswith(str(top.resolve()) + "/") \
                    and not (resolved + "/").startswith(str(top) + "/"):
                findings.fail(f"{rel}: links outside the release to {target}")
            continue
        if path.suffix in (".py", ".pyc", ".pyo") or "__pycache__" in rel:
            findings.fail(f"{rel}: Python source or bytecode in the release")
            continue
        with open(path, "rb") as handle:
            head = handle.read(4096)
        executable = os.access(path, os.X_OK)
        if head.startswith(b"#!"):
            interp = head[2:].split(b"\n", 1)[0].decode("latin-1").strip()
            if re.search(r"python", interp, re.IGNORECASE):
                findings.fail(f"{rel}: interpreter {interp}")
                continue
            if rel.startswith("share/doc/"):
                continue
            if re.fullmatch(r"/bin/k?sh", interp):
                for word in check_shell_script(rel, path.read_text(encoding="utf-8",
                                                                    errors="replace"), findings):
                    if word.startswith("/") and word not in SYSTEM_SCRIPTS \
                            and not word.startswith("@PREFIX@/"):
                        findings.fail(f"{rel}: runs {word}, outside the release")
            elif path.suffix == ".fasl" and re.search(r"/sbcl --script$", interp):
                fasls += 1  # SBCL's fasl header line: loaded by the runtime
            else:
                findings.fail(f"{rel}: interpreter {interp} is neither /bin/sh nor SBCL")
            continue
        if head[:4] == b"\x7fELF":
            facts = elf_facts(path.read_bytes())
            if facts is None:
                findings.fail(f"{rel}: ELF object that is not ELF64 little-endian")
                continue
            needed = facts["needed"]
            for name in needed:
                if PYTHON_RE.search(name):
                    findings.fail(f"{rel}: DT_NEEDED {name}")
                elif not (PLATFORM_LIBC.match(name) or name in carried):
                    findings.fail(f"{rel}: DT_NEEDED {name} is neither carried by the "
                                  "release nor the platform C library")
            for rpath in facts["rpaths"]:
                for entry in rpath.split(":"):
                    if entry and not entry.startswith("$ORIGIN"):
                        findings.fail(f"{rel}: DT_RPATH/RUNPATH {entry} outside the release")
            if facts["interp"] is not None and facts["interp"] not in LIBC_LOADERS:
                findings.fail(f"{rel}: program interpreter {facts['interp']} is not the "
                              "platform C library loader")
            findings.note(f"{rel}: ELF; needs {' '.join(needed) or '(none)'}"
                          + (f"; interpreter {facts['interp']}" if facts["interp"] else ""))
            continue
        if path.suffix == ".core" and rel.startswith("libexec/"):
            names = core_dlopen_names(path)
            outside = sorted(n for n in names if not (
                n in carried or PLATFORM_LIBC.match(n) or SYSTEM_TLS.match(n)
                or any(c.startswith(n + ".") for c in carried)))
            for name in outside:
                findings.fail(f"{rel}: may dlopen {name}, which the release does not carry")
            findings.note(f"{rel}: dlopen names {' '.join(sorted(names)) or '(none)'}; "
                          "the system's: " + (" ".join(sorted(n for n in names if SYSTEM_TLS.match(n)))
                                             or "(none)"))
            continue
        if executable and not rel.startswith("share/"):
            findings.fail(f"{rel}: executable that is neither a /bin/sh script nor ELF")
    if fasls:
        findings.note(f"{fasls} SBCL contrib fasls (#!.../sbcl --script headers, loaded by the runtime)")
    services = [p for p in top.rglob("*") if p.is_file() and (
        p.suffix in (".service", ".plist") or p.name.endswith(".service.in")
        or p.parent.name == "rc.d")]
    if not services:
        findings.fail("the release carries no service file")
    for path in services:
        text = path.read_text(encoding="utf-8")
        check_service(path.relative_to(top).as_posix(), text, findings, None)
    return findings


def unpack(tarball: Path, into: Path) -> Path:
    with tarfile.open(tarball) as archive:
        members = archive.getmembers()
        for member in members:
            name = member.name
            if name.startswith("/") or ".." in Path(name).parts:
                raise SystemExit(f"runpath_check: unsafe member {name}")
        archive.extractall(into, filter="tar") if hasattr(tarfile, "data_filter") \
            else archive.extractall(into)
    tops = [p for p in into.iterdir() if p.is_dir()]
    if len(tops) != 1:
        raise SystemExit("runpath_check: the tarball must hold one top directory")
    return tops[0]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--tree", type=Path, help="an unpacked release directory")
    group.add_argument("--tarball", type=Path, help="a release tarball")
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root (static mode)")
    parser.add_argument("--quiet", action="store_true", help="print only findings")
    args = parser.parse_args(argv)
    if args.tarball:
        with tempfile.TemporaryDirectory(prefix="fn-runpath.") as tmp:
            findings = tree_check(unpack(args.tarball, Path(tmp)))
            label = str(args.tarball)
    elif args.tree:
        findings = tree_check(args.tree)
        label = str(args.tree)
    else:
        findings = static_check(args.root)
        label = "static"
    if not args.quiet:
        for line in findings.lines:
            print(f"runpath: {line}")
    for problem in findings.problems:
        print(f"runpath: FAIL {problem}", file=sys.stderr)
    if findings.problems:
        print(f"runpath_check {label}: {len(findings.problems)} finding(s)", file=sys.stderr)
        return 1
    print(f"runpath_check {label}: no Python on the deployed path")
    return 0


if __name__ == "__main__":
    sys.exit(main())
