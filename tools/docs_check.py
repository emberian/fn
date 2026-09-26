#!/usr/bin/env python3
"""Every command the docs name exists, with the grammar the docs give.

Three checks over docs/*.md and docs/nodes/*.md (NNT-032):

1. Operator invocations.  Every `fn operator CONFIG VERB ...` (and the other
   spellings of the same entry: `packaging/fn`, `packaging/fn-native`,
   `PREFIX/bin/fn`, `fn-native`, `fn-host --fn`) quoted in a code block or
   an inline code span is reduced to its argv words after CONFIG, with each
   placeholder replaced by a sample value (PLACEHOLDERS).  The list is
   written into the generated book tests/acl2/docs-operator-grammar-tests.lisp,
   which asserts at certification that
   ACL2's own grammar (`fn-native-operator-run', the function
   host/native-operator-host.lisp's fn-native-operator-host-run calls, and
   `fn-native-operator-mission-run' for `mission') accepts each one.  This
   book cites each row by the heading it sits under and its ordinal among
   that section's invocations (`("docs/operator.md#install" 2 ...)`), never
   a line number, so prose moved or inserted leaves the book byte-identical
   and costs no certification (PKT-493).  This
   script decides nothing about the operator grammar: `--check` only fails
   when the committed book is not what the docs say now, so the ACL2
   verdict certified is the verdict for these docs.

2. Python tools.  Every `bin/fn`/`fn --config`, `fn_client.py`,
   `fn_consumer.py` and `fn_web.py` invocation is parsed by that tool's own
   argparse parser (`build_parser()`), without running it.

3. Reply lines.  Every line a doc presents as fn's output in a code block
   (`accepted ...`, `refused ...`, `usage ...`, `uncertain ...`, `fault ...`,
   a numbered NNTP reply) is matched against the source: the line's fixed
   prefix (up to its first placeholder or variable token) must occur in
   books/, host/, tools/ or bin/.  A line the code cannot print fails.

A code block or span that is a template (`VERB ...`, `A|B` choice lists
whose words are not all verbs) is expanded or reported as a template, and
lines marked with a trailing `# docs-check: skip (reason)` are skipped with
the reason printed.

    python3 tools/docs_check.py            # report
    python3 tools/docs_check.py --write    # regenerate the argv file
    python3 tools/docs_check.py --check    # make check: fail on any mismatch
"""

import argparse
import contextlib
import importlib.machinery
import importlib.util
import io
import re
import shlex
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DOCS = sorted(list((ROOT / "docs").glob("*.md")) + list((ROOT / "docs" / "nodes").glob("*.md")))
ARGV_FILE = ROOT / "tests" / "acl2" / "docs-operator-grammar-tests.lisp"

# One sample value per placeholder word the docs use.  A placeholder is an
# all-caps word (with digits, `-`, `_`, `/`), or `<...>`.  The value is one
# the grammar would receive from an operator following the page.
PLACEHOLDERS = {
    "NAME": "peer1", "PEER": "peer1", "PATH": "news.example.invalid",
    "PATH-ID": "news.example.invalid", "HOST": "127.0.0.1", "PORT": "1119",
    "OTHER-PORT": "1120", "INBOUND": "fn.*", "OUTBOUND": "fn.*",
    "SOURCE": "127.0.0.1", "N": "1000", "GROUP": "fn.letters",
    "CONTROL": "/srv/fn/control.sock", "PRINCIPAL": "alice", "USER": "alice",
    "MSGID": "<a1@example.invalid>", "MESSAGE-ID": "<a1@example.invalid>",
    "SECONDS": "30", "BYTES": "1048576", "OCTETS": "1048576",
    "IDENTITY": "news.example.invalid", "KEY": "listener", "TABLE": "listener",
    "AUTH-KIND": "source-address", "AUTH-VALUE": "127.0.0.1",
    "PRINCIPAL-HEX": "9261767a" * 8, "FILE": "/tmp/article.txt",
    "PAYLOAD": "/tmp/article.txt", "ARTICLE": "/tmp/article.txt",
    "EID": "dtn://node/", "NODE": "dtn://node/", "LIMIT": "1048576",
    "SNAPSHOT/store": "/srv/snapshot/store",
    "KEPT/config.json.format-7": "/srv/kept/config.json.format-7",
    "KEPT": "/srv/kept/config.json", "INVITE": "/srv/invite.fninv",
    "HEX": "9261767a" * 8, "<path>": "/etc/fn/fn.toml",
}

OPERATOR = re.compile(
    r"^(?:\$\s+)?(?:\S*/)?(?:fn|fn-native|fn-host)(?:\s+--fn)?\s+operator\s+(\S+)(?:\s+(.*))?$")
BIN_FN = re.compile(r"^(?:\$\s+)?(?:\S*/)?(?:bin/)?fn\s+(--config\s+\S+.*)$")
PY_TOOL = re.compile(
    r"^(?:\$\s+)?(?:[A-Z_]+=\S+\s+)*(?:python3\s+)?(?:\S*/)?(fn_client|fn_consumer|fn_web)\.py(?:\s+(.*))?$")
REPLY = re.compile(
    r"^(?:\$\s+)?((?:accepted|refused|usage|uncertain|fault)\s+operator\s+\S.*"
    r"|[1-5][0-9][0-9]\s+\S.*)$")
SKIP = re.compile(r"#\s*docs-check:\s*skip\s*\((.+)\)\s*$")


def code_lines(text):
    """(line number, text) of every code-block line and inline code span."""
    fenced = False
    pending, start = "", 0
    for number, line in enumerate(text.splitlines(), 1):
        if line.lstrip().startswith("```"):
            fenced = not fenced
            continue
        if fenced:
            if pending:
                line = pending + " " + line.strip()
                number = start
                pending = ""
            if line.rstrip().endswith("\\"):
                pending, start = line.rstrip()[:-1].rstrip(), number
                continue
            yield number, line.strip(), True
        else:
            for span in re.findall(r"`([^`]+)`", line):
                yield number, span.strip(), False


def strip_comment(line):
    skip = SKIP.search(line)
    if skip:
        return None, skip.group(1)
    return re.sub(r"\s+#(?:\s.*)?$", "", line).strip(), None


def placeholder(word):
    if word in PLACEHOLDERS:
        return PLACEHOLDERS[word]
    if re.fullmatch(r"<[a-z0-9-]+>", word):
        return PLACEHOLDERS.get(word[1:-1].upper(), None)
    return None


def is_placeholder(word):
    return (word in PLACEHOLDERS or re.fullmatch(r"<[a-z0-9-]+>", word) is not None
            or re.fullmatch(r"[A-Z][A-Z0-9_/.-]*[A-Z0-9]", word) is not None)


def shell_words(text, arrays):
    """The argv a shell would pass: quotes removed, `"${NAME[@]}"` spread from
    the doc's own `NAME=(...)` line, cut at a pipe, redirection or heredoc."""
    try:
        tokens = shlex.split(text)
    except ValueError:
        tokens = text.split()
    words = []
    for token in tokens:
        if token in ("|", "<", ">", ">>", "&&", ";", "||") or token.startswith(("<<", "2>")):
            break
        array = re.fullmatch(r"\$\{([A-Za-z_]+)\[@\]\}", token)
        if array and array.group(1) in arrays:
            words.extend(arrays[array.group(1)])
        else:
            words.append(token)
    return words


def expand(words):
    """Concrete argv from a doc's words, or (None, why) for a template."""
    out = []
    for word in words:
        if word in ("...", "…") or "..." in word:
            return None, "names a family of commands (`...`)"
        if "|" in word and not word.startswith("<"):
            word = word.split("|")[0]
        if word.startswith("[") and word.endswith("]"):
            word = word[1:-1].split("|")[0]
        if is_placeholder(word):
            value = placeholder(word)
            if value is None:
                return None, "placeholder %s has no sample value (docs_check PLACEHOLDERS)" % word
            out.append(value)
        else:
            out.append(word)
    return out, None


def inventory():
    """Every recognized invocation: (kind, doc, line, text, argv or None, why)."""
    found = []
    for path in DOCS:
        rel = path.relative_to(ROOT).as_posix()
        arrays = {}
        for number, line, block in code_lines(path.read_text(encoding="utf-8")):
            line, skipped = strip_comment(line)
            if line is None:
                found.append(("skip", rel, number, "", None, skipped))
                continue
            array = re.fullmatch(r"([A-Za-z_]+)=\((.*)\)", line)
            if block and array:
                arrays[array.group(1)] = shell_words(array.group(2), {})
                continue
            match = OPERATOR.match(line)
            if match:
                argv, why = expand(shell_words(match.group(2) or "", arrays))
                found.append(("operator", rel, number, line, argv, why))
                continue
            match = BIN_FN.match(line)
            if match:
                argv, why = expand(shell_words(match.group(1), arrays))
                found.append(("bin/fn", rel, number, line, argv, why))
                continue
            match = PY_TOOL.match(line)
            if match:
                if not match.group(2) and not block:
                    continue            # the tool's name in prose, not an invocation
                argv, why = expand(shell_words(match.group(2) or "", arrays))
                found.append((match.group(1), rel, number, line, argv, why))
                continue
            match = REPLY.match(line)
            if match:
                found.append(("reply", rel, number, match.group(1), None, None))
    return found


# ---------------------------------------------------------------------------
# 1. the operator argv file

def lisp_string(text):
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"') + '"'


BOOK_HEAD = """\
; Generated by tools/docs_check.py --write from docs/*.md and docs/nodes/*.md;
; do not edit (NNT-032).  Every operator invocation the docs quote, reduced
; to the argv after `operator CONFIG' with each placeholder given a sample
; value, is accepted by ACL2's own grammar: `fn-native-operator-run', which
; host/native-operator-host.lisp fn-native-operator-host-run calls for every
; `fn operator CONFIG ...', and `fn-native-operator-mission-run' for
; `mission'.  make check (tools/docs_check.py --check) fails when this file
; is not what the docs say now, so the verdict certified here is the verdict
; for the docs at these bytes.
(in-package "ACL2")
(include-book "../../books/native-operator")
(include-book "../../books/codec-attach")

(defun fn-docs-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words)) (fn-docs-argv (cdr words)))
    nil))

(defun fn-docs-lines (lines)
  (if (consp lines)
      (append (fn-record-string-octets (car lines)) (list 10)
              (fn-docs-lines (cdr lines)))
    nil))

; The smallest configuration an operator following the pages writes.
(defconst *fn-docs-config*
  (fn-docs-lines '("[store]" "path = \\"/srv/fn/store\\"")))

(defun fn-docs-operator-status (words)
  (fn-native-operator-result-status
   (if (equal (car words) "mission")
       (fn-native-operator-mission-run (fn-record-string-octets "/srv/fn/fn.toml")
                                       (fn-docs-argv words))
     (fn-native-operator-run *fn-docs-config* (fn-docs-argv words)))))

; Rows are (DOC#SECTION ORDINAL WORD...): the heading an invocation sits under
; and its place among that section's operator invocations, never a line number;
; the rows whose argv the grammar does not accept.
(defun fn-docs-operator-rejected (rows)
  (if (consp rows)
      (if (equal (fn-docs-operator-status (cddr (car rows))) :accepted)
          (fn-docs-operator-rejected (cdr rows))
        (cons (list (car (car rows)) (cadr (car rows))
                    (fn-docs-operator-status (cddr (car rows))))
              (fn-docs-operator-rejected (cdr rows))))
    nil))

"""

BOOK_TAIL = """
(assert-event (null (fn-docs-operator-rejected *fn-docs-operator-argv*))
              :msg (msg "The grammar refuses these documented invocations: ~x0"
                        (fn-docs-operator-rejected *fn-docs-operator-argv*)))

; Teeth: the same verdict refuses a documented row with a word dropped, a
; placeholder left unfilled and an unknown verb, so the assertion above is
; not satisfied by a verdict that accepts everything.
(assert-event (equal (fn-docs-operator-status '("peer" "remove")) :usage))
(assert-event (equal (fn-docs-operator-status '("capacity" "N")) :usage))
(assert-event (equal (fn-docs-operator-status '("store" "inspekt")) :usage))
"""


def lisp_string(text):
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"') + '"'


def slug(heading):
    """GitHub's anchor for a heading: lower case, punctuation dropped,
    spaces to hyphens."""
    text = re.sub(r"[^\w\- ]", "", heading.strip().lower())
    return text.replace(" ", "-")


def section_slugs(text):
    """{line number: the anchor of the heading it sits under} for one doc.
    Fence-aware (a `# comment` in a code block is not a heading); a repeated
    heading gets GitHub's `-1`, `-2` suffix; lines before the first heading
    sit under `top`."""
    sections, seen = {}, {}
    current, fenced = "top", False
    for number, line in enumerate(text.splitlines(), 1):
        if line.lstrip().startswith("```"):
            fenced = not fenced
        elif not fenced and re.match(r"#{1,6}\s", line):
            base = slug(line.lstrip("#"))
            current = base if base not in seen else "%s-%d" % (base, seen[base])
            seen[base] = seen.get(base, 0) + 1
        sections[number] = current
    return sections


def anchors(found):
    """{(doc, line): (doc#section, ordinal)}: each operator invocation's
    stable citation, the heading it sits under and its place among the
    operator invocations under that heading.  A line number would change
    the generated book (and need a certification) whenever prose is
    inserted above an invocation anywhere in the doc; this changes only
    when that section's own invocations change (PKT-493)."""
    slugs, counts, out = {}, {}, {}
    for kind, rel, number, line, argv, why in found:
        if kind != "operator" or argv is None:
            continue
        if rel not in slugs:
            slugs[rel] = section_slugs((ROOT / rel).read_text(encoding="utf-8"))
        section = "%s#%s" % (rel, slugs[rel].get(number, "top"))
        counts[section] = counts.get(section, 0) + 1
        out[(rel, number)] = (section, counts[section])
    return out


def argv_file(found):
    rows = []
    seen = set()
    cite = anchors(found)
    for kind, rel, number, line, argv, why in found:
        if kind != "operator" or argv is None:
            continue
        key = tuple(argv)
        if key in seen:
            continue
        seen.add(key)
        section, ordinal = cite[(rel, number)]
        rows.append("    (%s %d %s)" % (lisp_string(section), ordinal,
                                         " ".join(lisp_string(w) for w in argv)))
    return (BOOK_HEAD + "(defconst *fn-docs-operator-argv*\n  '(\n" + "\n".join(rows) +
            "))\n" + BOOK_TAIL)


# ---------------------------------------------------------------------------
# 2. the Python tools' own parsers

def load_tool(name):
    path = ROOT / ("bin/fn" if name == "bin/fn" else "tools/%s.py" % name)
    sys.path.insert(0, str(ROOT / "tools"))
    loader = importlib.machinery.SourceFileLoader("docs_check_" + name.replace("/", "_"), str(path))
    spec = importlib.util.spec_from_loader(loader.name, loader)
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    return module


def parse_python(found):
    failures = []
    parsers = {}
    for kind, rel, number, line, argv, why in found:
        if kind not in ("bin/fn", "fn_client", "fn_consumer", "fn_web") or argv is None:
            continue
        if kind not in parsers:
            parsers[kind] = load_tool(kind).build_parser()
        parser = parsers[kind]
        err = io.StringIO()
        try:
            with contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
                parser.parse_args(argv)
        except SystemExit as stop:
            if stop.code not in (0, None):
                failures.append("%s:%d: %s: %s" % (rel, number, line,
                                                   err.getvalue().strip().splitlines()[-1:]))
    return failures


# ---------------------------------------------------------------------------
# 3. reply lines

SOURCES = None


def source_text():
    global SOURCES
    if SOURCES is None:
        parts = []
        for pattern in ("books/*.lisp", "host/*.lisp", "host/native/*.lisp",
                        "tools/*.py", "bin/fn"):
            for path in sorted(ROOT.glob(pattern)):
                if path.name != "docs_check.py":
                    parts.append(path.read_text(encoding="utf-8", errors="replace"))
        SOURCES = "\n".join(parts)
    return SOURCES


def fixed_prefix(line):
    """The words of a reply line before its first variable token."""
    words = []
    for word in line.split():
        if (is_placeholder(word) or re.search(r"[=<>0-9/@:(]", word) and words
                or word in ("...", "…")):
            break
        words.append(word)
    return " ".join(words)


# Reply lines a doc quotes from other software, never as fn's own output.
FOREIGN_REPLIES = {
    ("docs/interop-inn.md", "437 Unwanted site"): "innd's reply (innd/art.c), quoted",
}


def check_replies(found):
    failures = []
    text = source_text()
    lowered = None
    for kind, rel, number, line, argv, why in found:
        if kind != "reply":
            continue
        prefix = fixed_prefix(line)
        head = prefix.split(" ", 1)
        if head[0] in ("accepted", "refused", "usage", "uncertain", "fault"):
            # `STATUS operator VERB REASON': ACL2 renders the status word and
            # the command separately (fnn-operator-emit-result); the verb and
            # a REASON in capitals are the grammar's words, looked up alone.
            words = [w.strip("()").lower() for w in line.split()[2:]
                     if w not in ("...", "…") and not re.search(r"[=0-9]", w)]
            missing = [w for w in words
                       if not re.search(r"(?i)[\"(:'` ]" + re.escape(w.lower()) + r"[\"): ']",
                                        text)]
            if missing:
                failures.append("%s:%d: `%s`: no source spells %s" % (
                    rel, number, line, ", ".join(missing)))
            continue
        if len(prefix) < 5 or (rel, prefix) in FOREIGN_REPLIES:
            continue
        if prefix not in text:
            if lowered is None:
                lowered = text.lower()
            if prefix.lower() not in lowered:
                failures.append("%s:%d: `%s`: no source prints %r" % (rel, number, line, prefix))
    return failures


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="regenerate the argv file")
    mode.add_argument("--check", action="store_true", help="fail on any mismatch")
    parser.add_argument("--verbose", action="store_true", help="list every invocation")
    args = parser.parse_args(argv)
    found = inventory()
    generated = argv_file(found)
    failures = []
    templates = [(rel, number, line, why) for kind, rel, number, line, argv, why in found
                 if kind not in ("reply", "skip") and argv is None]
    for rel, number, line, why in templates:
        print("template %s:%d: %s -- %s" % (rel, number, line, why))
    for kind, rel, number, line, argv, why in found:
        if kind == "skip":
            print("skipped %s:%d -- %s" % (rel, number, why))
        elif args.verbose and argv is not None:
            print("%s %s:%d: %s" % (kind, rel, number, " ".join(argv)))
    if args.write:
        ARGV_FILE.write_text(generated, encoding="utf-8")
        print("wrote %s" % ARGV_FILE.relative_to(ROOT))
    elif not ARGV_FILE.exists() or ARGV_FILE.read_text(encoding="utf-8") != generated:
        failures.append("%s is not what the docs say now: run tools/docs_check.py --write "
                        "and certify it"
                        % ARGV_FILE.relative_to(ROOT))
    failures += parse_python(found)
    failures += check_replies(found)
    counts = {}
    for kind, *_ in found:
        counts[kind] = counts.get(kind, 0) + 1
    for failure in failures:
        print("FAIL " + failure)
    print("docs_check: %s; %d template(s), %d failure(s)" % (
        ", ".join("%s=%d" % kv for kv in sorted(counts.items())), len(templates), len(failures)))
    return 1 if failures and (args.check or not args.write) else 0


if __name__ == "__main__":
    sys.exit(main())
