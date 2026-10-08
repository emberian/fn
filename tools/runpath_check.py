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
platform's C library loader, it may need no GLIBC_x.y symbol version above
GLIBC_FLOOR (the oldest glibc a Linux release supports), its
DT_RPATH/DT_RUNPATH may not name a directory outside the release, and each DT_NEEDED name must be a file the
release carries or the platform's C library (PLATFORM_LIBC); every shared
object name the saved core may dlopen (the lib*.so strings in the core) must
be carried by the release, the C library, or the system TLS library D35
chose (SYSTEM_TLS); each service file (template) must start `PREFIX/bin/fn`.

The release's `clients/` (packaging/install-clients.sh: fn-client and the
other client programs, which are Python; the web face is the node's own,
[web] in fn.toml) is checked under its own rule, `clients_check': Python
source there and nowhere else, no object code, launchers that run only
python3 on clients/lib/, and no service template (a client is never a
service); and the separation: no script, launcher or service of the node's
names `clients/`, so nothing the node runs can start a client.  The node's
own walk skips clients/.

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
        "ION/LTP; docs/operator-internals.md); :search nil, so only the absolute path "
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
# The clients (packaging/install-clients.sh): the launcher every clients/bin/
# program is, the commands it may run, and the reader's service templates.
CLIENTS = "clients"
CLIENT_LAUNCHER = "packaging/fn-client-launcher"
CLIENT_LAUNCHER_COMMANDS = {"readlink", "dirname", "basename", "tr", "python3"}
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
# may name (ld.so resolves it): glibc on Linux, libc on OpenBSD.  A tree is
# checked against its target's rules (PKT-723): `--platform', or the program
# interpreter of the release's runtime (`detect_platform'); a tree whose
# platform is unknown gets the union, as before.
PLATFORM_LIBC_BY = {
    "linux": re.compile(
        r"^(?:libc\.so\.6|libm\.so\.6|libdl\.so\.2|libpthread\.so\.0|librt\.so\.1|"
        r"ld-linux-x86-64\.so\.2|libutil\.so\.1)$"),
    # OpenBSD's base libraries are libNAME.so.MAJOR.MINOR (ld.so(1)).
    "openbsd": re.compile(r"^(?:libc|libm|libpthread|libutil|libc\+\+abi|libc\+\+)\.so\.\d+\.\d+$"),
}
PLATFORM_LIBC = re.compile(
    r"^(?:libc\.so(?:\.[\d.]+)?|libm\.so(?:\.[\d.]+)?|libdl\.so\.2|libpthread\.so(?:\.[\d.]+)?|"
    r"librt\.so\.1|ld-linux-x86-64\.so\.2|libutil\.so(?:\.[\d.]+)?|libc\+\+abi\.so[\d.]*)$")
LIBC_LOADERS_BY = {"linux": {"/lib64/ld-linux-x86-64.so.2"}, "openbsd": {"/usr/libexec/ld.so"}}
LIBC_LOADERS = {"/lib64/ld-linux-x86-64.so.2", "/usr/libexec/ld.so"}
PLATFORMS = ("linux", "openbsd")
# The system TLS library the image loads by dlopen: D35 as ember confirmed it
# on 2026-09-26 ("no OpenSSL 3.5, the system libssl"; lane crypto-deps):
# OpenSSL 3's sonames on Linux; on OpenBSD LibreSSL in the base system (the
# core names it unversioned; ld.so resolves the installed major) or the
# OpenSSL 3 pair under an operator's FN_OPENSSL_PREFIX (host/native/tls.lisp
# `fnn-tls-configured-library-pair', an absolute path the operator names).
SYSTEM_TLS_BY = {
    "linux": re.compile(r"^lib(?:ssl|crypto)\.so\.3$"),
    "openbsd": re.compile(r"^lib(?:ssl|crypto)\.so(?:\.3|\.\d+\.\d+)?$"),
}
SYSTEM_TLS = re.compile(r"^lib(?:ssl|crypto)\.so(?:\.[\d.]+)?$")
OPENBSD_LIB_RE = re.compile(r"^(lib[A-Za-z0-9_+-][A-Za-z0-9_+.-]*?)\.so\.(\d+)\.(\d+)$")
# Absolute paths a shipped script may run: the shell and OpenBSD's rc.subr.
SYSTEM_SCRIPTS = {"/bin/sh", "/bin/ksh", "/etc/rc.d/rc.subr"}
# The oldest glibc a Linux release runs on: Debian 12's 2.36 (lane
# release-glibc-floor, 2026-09-26; dregg-infra's edge boxes).  Every bundled
# ELF object's GLIBC_x.y version needs must be at or below it; the release
# build runs this check before packing (docs/operator-internals.md, "From the release
# tarball"; docs/install.md's requirements line).  The one place it is set.
GLIBC_FLOOR = (2, 36)
GLIBC_VERSION_RE = re.compile(r"^GLIBC_(\d+)\.(\d+)(?:\.(\d+))?$")
CORE_WIDE_RE = re.compile(rb"(?:[A-Za-z0-9_+./-]\x00\x00\x00){6,256}")
CORE_LIB_RE = re.compile(rb"lib[A-Za-z0-9_+-][A-Za-z0-9_+.-]*?\.so(?:\.\d+)*")


class Findings:
    def __init__(self) -> None:
        self.problems: list[str] = []
        self.lines: list[str] = []
        self.platform: str | None = None

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
        # A candidate list is chosen at read time (#+linux, #+openbsd, ...), so
        # the saved core carries only its platform's names and the tree check
        # may read every lib*.so string in the core as one it may dlopen
        # (PKT-723).  A run-time `(member :os *features*)' would put every
        # platform's names in every core.
        for match in LIB_LITERAL_RE.finditer(text):
            defun = enclosing_defun(text, match.start())
            if not defun.endswith("-library-candidates"):
                continue
            start = max(m.start() for m in DEFUN_RE.finditer(text, 0, match.start() + 1))
            body = text[start:match.start()]
            if "*features*" in body or not re.search(r"#[+-]", body):
                findings.fail(f"{rel}: {defun} names {match.group(1)} without a read-time "
                              "platform conditional (#+linux, #+openbsd, #+darwin)")
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
            text = path.read_text(encoding="utf-8")
            check_service(rel, text, findings, None)
            if CLIENTS + "/" in text:
                findings.fail(f"{rel}: the node's service names {CLIENTS}/")
        else:
            findings.fail(f"shipped service file missing: {rel}")
    for rel in SHIPPED_SCRIPTS:
        if (root / rel).exists() and runs_a_client(
                check_shell_script(rel, (root / rel).read_text(encoding="utf-8"), Findings())):
            findings.fail(f"{rel}: runs a program under {CLIENTS}/")
    check_client_launcher(CLIENT_LAUNCHER, (root / CLIENT_LAUNCHER).read_text(encoding="utf-8"),
                          findings)
    return findings


def runs_a_client(commands: list[str]) -> bool:
    return any(CLIENTS + "/" in word for word in commands)


def check_client_launcher(label: str, text: str, findings: Findings) -> None:
    """A clients/bin/ launcher: /bin/sh, running python3 and a few file-name
    tools, nothing else (the node's scripts may run none of them)."""
    first = text.split("\n", 1)[0]
    if first.strip() != "#!/bin/sh":
        findings.fail(f"{label}: interpreter is {first.strip()!r}, not /bin/sh")
    commands = []
    for line in re.sub(r"\\\n", " ", text).splitlines()[1:]:
        stripped = re.sub(r"\s#.*$", "", line.strip())
        if not stripped or stripped.startswith("#"):
            continue
        commands += [w for w in split_commands(stripped) if w and w not in SH_BUILTINS]
    for word in dict.fromkeys(commands):
        if word not in CLIENT_LAUNCHER_COMMANDS:
            findings.fail(f"{label}: runs {word}, not one of "
                          f"{' '.join(sorted(CLIENT_LAUNCHER_COMMANDS))}")
    findings.note(f"{label}: client launcher; commands: {' '.join(dict.fromkeys(commands))}")


def clients_check(top: Path, findings: Findings) -> None:
    """The release's clients/ under its own rule (the module's docstring)."""
    root = top / CLIENTS
    if not root.is_dir():
        findings.note(f"no {CLIENTS}/ in this release")
        return
    python = 0
    for path in sorted(p for p in root.rglob("*") if p.is_file() or p.is_symlink()):
        rel = path.relative_to(top).as_posix()
        if path.is_symlink():
            findings.fail(f"{rel}: a symbolic link in {CLIENTS}/")
            continue
        with open(path, "rb") as handle:
            head = handle.read(4096)
        executable = os.access(path, os.X_OK)
        if head[:4] == b"\x7fELF":
            findings.fail(f"{rel}: object code in {CLIENTS}/")
        elif path.suffix in (".pyc", ".pyo") or "__pycache__" in rel:
            findings.fail(f"{rel}: Python bytecode in {CLIENTS}/ (the source is shipped)")
        elif rel.startswith(CLIENTS + "/lib/"):
            if path.suffix != ".py" or executable:
                findings.fail(f"{rel}: {CLIENTS}/lib/ holds Python source, mode 0644")
            python += 1
        elif rel.startswith(CLIENTS + "/bin/"):
            check_client_launcher(rel, path.read_text(encoding="utf-8", errors="replace"),
                                  findings)
        elif executable:
            findings.fail(f"{rel}: executable outside {CLIENTS}/bin/")
        elif path.name.endswith(".service.in") or path.parent.name == "rc.d":
            findings.fail(f"{rel}: a service template in {CLIENTS}/ (a client is never a "
                          "service; the web face is the node's [web] table)")
    findings.note(f"{CLIENTS}/: {python} Python programs (Python 3.9+, {CLIENTS}/README.txt); "
                  "none on the node's path")


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
    versions: dict[int, str] = {}   # vna_other index -> version name (DT_VERNEED)
    for sh_type, offset, size, link in sections:
        if sh_type != 0x6FFFFFFE or link >= len(sections):  # SHT_GNU_verneed
            continue
        str_offset = sections[link][1]
        pos = offset
        while pos + 16 <= offset + size:
            _vn_version, vn_cnt, _vn_file, vn_aux, vn_next = struct.unpack_from("<HHIII", data, pos)
            aux = pos + vn_aux
            for _ in range(vn_cnt):
                _hash, _flags, other, name, vna_next = struct.unpack_from("<IHHII", data, aux)
                end = data.index(b"\0", str_offset + name)
                versions[other] = data[str_offset + name:end].decode("latin-1")
                if not vna_next:
                    break
                aux += vna_next
            if not vn_next:
                break
            pos += vn_next
    symbol_versions: list[tuple[str, str]] = []  # (undefined symbol, version it needs)
    versym = next((s for s in sections if s[0] == 0x6FFFFFFF), None)  # SHT_GNU_versym
    dynsym = next((s for s in sections if s[0] == 11), None)          # SHT_DYNSYM
    if versym and dynsym and dynsym[3] < len(sections):
        str_offset = sections[dynsym[3]][1]
        for i in range(dynsym[2] // 24):
            st_name, _info, _other, st_shndx = struct.unpack_from("<IBBH", data, dynsym[1] + 24 * i)
            index, = struct.unpack_from("<H", data, versym[1] + 2 * i)
            index &= 0x7FFF
            if st_shndx == 0 and index in versions:
                end = data.index(b"\0", str_offset + st_name)
                symbol_versions.append((data[str_offset + st_name:end].decode("latin-1"),
                                        versions[index]))
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
    return {"needed": needed, "rpaths": rpaths, "interp": interp,
            "versions": sorted(set(versions.values())), "symbol_versions": symbol_versions}


def glibc_version(name: str) -> tuple[int, ...] | None:
    """(2, 38) for GLIBC_2.38, (2, 3, 4) for GLIBC_2.3.4; None for any other name."""
    match = GLIBC_VERSION_RE.match(name)
    return None if match is None else tuple(int(g) for g in match.groups() if g is not None)


def glibc_above_floor(facts: dict) -> tuple[tuple[int, ...] | None, list[str]]:
    """The highest GLIBC version an object needs, and each need above GLIBC_FLOOR
    (`symbol@GLIBC_x.y`, or the bare version when no symbol names it)."""
    needs = [v for v in (glibc_version(n) for n in facts["versions"]) if v is not None]
    highest = max(needs) if needs else None
    above = sorted({f"{sym}@{ver}" for sym, ver in facts["symbol_versions"]
                    if (glibc_version(ver) or (0,)) > GLIBC_FLOOR})
    named = {a.rsplit("@", 1)[1] for a in above}
    above += sorted(n for n in facts["versions"]
                    if (glibc_version(n) or (0,)) > GLIBC_FLOOR and n not in named)
    return highest, above


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


def detect_platform(top: Path) -> str | None:
    """The target of an unpacked release: its runtime's program interpreter
    (glibc's loader on Linux, /usr/libexec/ld.so on OpenBSD), or None."""
    runtime = top / "libexec" / "fn" / "runtime" / "sbcl"
    if not runtime.is_file():
        return None
    facts = elf_facts(runtime.read_bytes())
    interp = facts and facts["interp"]
    return next((p for p, loaders in LIBC_LOADERS_BY.items() if interp in loaders), None)


def carried_satisfies(name: str, carried: set[str], platform: str | None) -> bool:
    """Whether the dynamic loader of PLATFORM resolves NAME to a carried file.
    OpenBSD's ld.so resolves libX.so and libX.so.MAJOR to a libX.so.MAJOR.MINOR
    file, and a file not named so is no library to it; elsewhere a carried
    NAME or NAME.VERSION (libX.so.23 for libX.so.23.3.0)."""
    if name in carried:
        return True
    if platform == "openbsd":
        for c in carried:
            m = OPENBSD_LIB_RE.match(c)
            if m and (name == f"{m.group(1)}.so" or name == f"{m.group(1)}.so.{m.group(2)}"):
                return True
        return False
    return any(c.startswith(name + ".") for c in carried)


def tree_check(top: Path, platform: str | None = None) -> Findings:
    findings = Findings()
    if not (top / "bin" / "fn").is_file():
        findings.fail(f"{top}: no bin/fn")
        return findings
    detected = detect_platform(top)
    if platform is not None and detected is not None and detected != platform:
        findings.fail(f"the release's runtime is for {detected}, not {platform}")
    platform = platform or detected
    findings.platform = platform
    libc = PLATFORM_LIBC_BY.get(platform, PLATFORM_LIBC)
    loaders = LIBC_LOADERS_BY.get(platform, LIBC_LOADERS)
    system_tls = SYSTEM_TLS_BY.get(platform, SYSTEM_TLS)
    findings.note(f"platform {platform or 'unknown (the union of every platform rule)'}")
    fasls = 0
    carried = {p.name for p in top.rglob("*") if p.is_file()}
    for path in sorted(p for p in top.rglob("*") if p.is_file() or p.is_symlink()):
        rel = path.relative_to(top).as_posix()
        if rel.startswith(CLIENTS + "/"):
            continue        # clients_check, below
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
                words = check_shell_script(rel, path.read_text(encoding="utf-8",
                                                               errors="replace"), findings)
                for word in words:
                    if word.startswith("/") and word not in SYSTEM_SCRIPTS \
                            and not word.startswith("@PREFIX@/"):
                        findings.fail(f"{rel}: runs {word}, outside the release")
                if runs_a_client(words):
                    findings.fail(f"{rel}: runs a program under {CLIENTS}/")
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
                elif not (libc.match(name) or carried_satisfies(name, carried, platform)):
                    findings.fail(f"{rel}: DT_NEEDED {name} is neither carried by the "
                                  "release nor the platform C library")
            for rpath in facts["rpaths"]:
                for entry in rpath.split(":"):
                    if entry and not entry.startswith("$ORIGIN"):
                        findings.fail(f"{rel}: DT_RPATH/RUNPATH {entry} outside the release")
            if facts["interp"] is not None and facts["interp"] not in loaders:
                findings.fail(f"{rel}: program interpreter {facts['interp']} is not the "
                              "platform C library loader")
            highest, above = glibc_above_floor(facts)
            floor = "GLIBC_" + ".".join(map(str, GLIBC_FLOOR))
            for need in above:
                findings.fail(f"{rel}: needs {need}, above the release's floor {floor}")
            findings.note(f"{rel}: ELF; needs {' '.join(needed) or '(none)'}"
                          + (f"; interpreter {facts['interp']}" if facts["interp"] else "")
                          + (f"; highest GLIBC_{'.'.join(map(str, highest))} (floor {floor})"
                             if highest else ""))
            continue
        if path.suffix == ".core" and rel.startswith("libexec/"):
            names = core_dlopen_names(path)
            outside = sorted(n for n in names if not (
                libc.match(n) or system_tls.match(n)
                or carried_satisfies(n, carried, platform)))
            for name in outside:
                findings.fail(f"{rel}: may dlopen {name}, which the release does not carry")
            findings.note(f"{rel}: dlopen names {' '.join(sorted(names)) or '(none)'}; "
                          "the system's: " + (" ".join(sorted(n for n in names if system_tls.match(n)))
                                             or "(none)"))
            continue
        if executable and not rel.startswith("share/"):
            findings.fail(f"{rel}: executable that is neither a /bin/sh script nor ELF")
    if fasls:
        findings.note(f"{fasls} SBCL contrib fasls (#!.../sbcl --script headers, loaded by the runtime)")
    services = [p for p in top.rglob("*") if p.is_file() and (
        p.suffix in (".service", ".plist") or p.name.endswith(".service.in")
        or p.parent.name == "rc.d")
        and not p.relative_to(top).as_posix().startswith(CLIENTS + "/")]
    if not services:
        findings.fail("the release carries no service file")
    for path in services:
        text = path.read_text(encoding="utf-8")
        check_service(path.relative_to(top).as_posix(), text, findings, None)
        if CLIENTS + "/" in text:
            findings.fail(f"{path.relative_to(top).as_posix()}: the node's service names "
                          f"{CLIENTS}/")
    for launcher in (top / "bin" / "fn", top / "libexec" / "fn" / "fn-host"):
        if launcher.is_file() and (CLIENTS + "/").encode() in launcher.read_bytes()[:65536]:
            findings.fail(f"{launcher.relative_to(top).as_posix()}: names {CLIENTS}/")
    clients_check(top, findings)
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
    parser.add_argument("--platform", choices=PLATFORMS,
                        help="the release's target (default: from its runtime's interpreter)")
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root (static mode)")
    parser.add_argument("--quiet", action="store_true", help="print only findings")
    args = parser.parse_args(argv)
    if args.tarball:
        with tempfile.TemporaryDirectory(prefix="fn-runpath.") as tmp:
            findings = tree_check(unpack(args.tarball, Path(tmp)), args.platform)
            label = str(args.tarball)
    elif args.tree:
        findings = tree_check(args.tree, args.platform)
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
    floor = "" if label == "static" or findings.platform == "openbsd" else \
        f"; no bundled ELF object needs more than GLIBC_{'.'.join(map(str, GLIBC_FLOOR))}"
    print(f"runpath_check {label}: no Python on the deployed path{floor}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
