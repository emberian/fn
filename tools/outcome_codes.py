"""fn's exit classes, read from ACL2's table: the one place Python names them.

books/outcome-class.lisp `*fn-outcome-codes*` maps each class to its code
(specs/host.md "CLI exit codes"); the native host's `+fnn-exit-*+`
constants are built from it (host/native/io.lisp).  Python reads the same
alist here, by a pattern that admits nothing else (no Lisp reader, no
evaluation), and fails at import if the table changes shape or loses a
class.  Tests take it through tests/native_harness.py; tools import it.
"""
import enum
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
OUTCOME_BOOK = ROOT / "books" / "outcome-class.lisp"
_CODES = re.compile(r"\(defconst \*fn-outcome-codes\*\s*'\(((?:\s*\(:[a-z-]+ \. \d+\))+)\s*\)\)")


def outcome_codes(book=OUTCOME_BOOK):
    """ACL2's class-to-code table, `*fn-outcome-codes*`, as {class: code}.

    Read from the book's one quoted alist by a pattern that admits nothing
    else (no Lisp reader, no evaluation); a book whose table no longer has
    that shape, or loses a class, fails every native module at import."""
    found = _CODES.search(Path(book).read_text(encoding="utf-8"))
    if not found:
        raise RuntimeError("{}: *fn-outcome-codes* is not a quoted alist of codes".format(book))
    table = {name: int(code) for name, code in
             re.findall(r"\(:([a-z-]+) \. (\d+)\)", found.group(1))}
    wanted = {"accepted", "refused", "fenced", "fault", "usage", "interrupted", "not-connected"}
    if set(table) != wanted or len(set(table.values())) != len(table):
        raise RuntimeError("{}: *fn-outcome-codes* is {!r}".format(book, table))
    return table


_TABLE = outcome_codes()


class EXIT(enum.IntEnum):
    """The exit classes by the names the tests use (specs/host.md's table)."""
    OK = _TABLE["accepted"]
    REFUSED = _TABLE["refused"]
    UNCERTAIN = _TABLE["fenced"]
    FAULT = _TABLE["fault"]
    USAGE = _TABLE["usage"]
    INTERRUPTED = _TABLE["interrupted"]
    NOT_CONNECTED = _TABLE["not-connected"]


EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, EXIT_FAULT, EXIT_USAGE = (
    EXIT.OK, EXIT.REFUSED, EXIT.UNCERTAIN, EXIT.FAULT, EXIT.USAGE)


def outcome_name(code):
    try:
        return EXIT(code).name
    except ValueError:
        return "code {}".format(code)
