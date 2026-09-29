#!/usr/bin/env python3
"""Re-take a test book's pinned figures by evaluation (batch AZ, 2026-09-28;
zero-copy-commit's ask).  A merge of two lanes that both move a figure leaves
every `(assert! (equal EXPR PINNED))` in the heap test books wrong; this
rewrites them from ACL2's own values, never by hand arithmetic.

    retake_pins.py emit BOOK OUT
        writes OUT: BOOK with each (assert! (equal A B)) replaced by a form
        that prints `PIN n T|NIL <A's value>` and every other assert! by
        `HOLD n T|NIL`.  Run it where BOOK's includes are certified:
          cd tests/acl2; printf '(ld "OUT" :ld-error-action :continue)\n' | acl2 > LOG
    retake_pins.py apply BOOK LOG
        rewrites BOOK in place: each failing PIN's numbers are replaced by
        the value's numbers when the two differ only in numbers; anything
        else (a structural difference, a failing HOLD) is listed for a
        person to decide.  Exit 0 when nothing is left, 1 otherwise.

The value is ACL2's; the tool only moves digits.  A witness whose
hypotheses fail (HOLD NIL) needs new inputs, not new numbers.
"""
import argparse
import os
from pathlib import Path
import re
import subprocess
import sys



def read_form(s, i):
    """end index of the form starting at s[i] == '('"""
    depth = 0; j = i
    while j < len(s):
        c = s[j]
        if c == '"':
            j += 1
            while s[j] != '"':
                if s[j] == '\\': j += 1
                j += 1
        elif c == ';':
            while j < len(s) and s[j] != '\n': j += 1
            continue
        elif c == '#' and s[j+1] == '\\':
            j += 3; continue
        elif c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0: return j + 1
        j += 1
    raise ValueError("unbalanced")

def top_args(form):
    """split the inner of (head a b ...) into its top-level parts"""
    inner = form[1:-1].strip()
    parts = []; j = 0
    while j < len(inner):
        c = inner[j]
        if c.isspace(): j += 1; continue
        if c == ';':
            while j < len(inner) and inner[j] != '\n': j += 1
            continue
        if c == '(':
            e = read_form(inner, j); parts.append(inner[j:e]); j = e; continue
        if c == "'" and j + 1 < len(inner) and inner[j+1] == '(':
            e = read_form(inner, j + 1); parts.append(inner[j:e]); j = e; continue
        if c == '"':
            k = j + 1
            while inner[k] != '"':
                if inner[k] == '\\': k += 1
                k += 1
            parts.append(inner[j:k+1]); j = k + 1; continue
        k = j
        while k < len(inner) and not inner[k].isspace() and inner[k] not in '()': k += 1
        parts.append(inner[j:k]); j = k
    return parts



ASSERT_HEADS = ('(assert!', '(assert-event')


def must_fail_spans(src):
    """(start, end) of each (must-fail ...) form: an assert inside one is
    expected to fail and is never a pin (heap-pool's ask)."""
    spans = []; i = 0
    while True:
        k = src.find('(must-fail', i)
        if k < 0:
            return spans
        line_start = src.rfind('\n', 0, k) + 1
        if ';' in src[line_start:k]:
            i = k + 10
            continue
        e = read_form(src, k); spans.append((k, e)); i = e


def asserts(src):
    """(start, end, index) of each assert! / assert-event outside a comment
    and outside a must-fail."""
    spans = must_fail_spans(src)
    i = 0; n = 0
    while True:
        found = [(k, head) for head in ASSERT_HEADS if (k := src.find(head, i)) >= 0
                 and not src[k + len(head):k + len(head) + 1].strip('-*!').isalnum()]
        if not found:
            return
        k, head = min(found)
        line_start = src.rfind('\n', 0, k) + 1
        if ';' in src[line_start:k] or any(a < k < b for a, b in spans):
            i = k + len(head)
            continue
        e = read_form(src, k); n += 1
        yield k, e, n
        i = e


def literal(value):
    """ACL2's printed VALUE as a form that evaluates to it."""
    text = value.strip()
    if re.fullmatch(r'-?\d+(/\d+)?|:[^\s()]+|T|NIL|"(?:[^"\\]|\\.)*"', text, re.I):
        return text.lower() if text.upper() in ('T', 'NIL') or text.startswith(':') else text
    return "'" + text.lower() if not text.startswith('"') else text


def emit(book, out):
    src = open(book).read(); res = []; last = 0; count = 0
    for k, e, n in asserts(src):
        body = top_args(src[k:e])[1]
        res.append(src[last:k])
        if body.startswith('(equal '):
            a, b = top_args(body)[1:3]
            res.append('(value-triple (let ((got %s)) (cw "PIN %d ~x0 ~x1~%%" (equal got %s) got)))'
                       % (a, n, b))
        else:
            res.append('(value-triple (cw "HOLD %d ~x0~%%" (if %s t nil)))' % (n, body))
        last = e; count = n
    res.append(src[last:])
    open(out, 'w').write(''.join(res))
    print(count, "asserts")
    return 0


def apply(book, log, flip_ok=None):
    """Move the numbers; name every other difference per witness.

    A witness whose decision flips (a pinned :refused whose value is now
    :heap at a boundary, chunked-body-2) differs beyond numbers: it is a
    FLIP, said per witness, and moved only under --flip-ok REASON, which
    prints the commit-message lines that carry the reason.
    """
    src = open(book).read(); text = open(log).read()
    got = {int(m.group(1)): m.group(2).strip()
           for m in re.finditer(r'PIN (\d+) NIL (.*?)\n NIL\n', text, re.S)}
    holds = [int(x) for x in re.findall(r'HOLD (\d+) NIL', text)]
    num = re.compile(r'-?\d+')
    shape = lambda x: re.sub(r'\s+', ' ', num.sub('N', x.upper().lstrip("'"))).strip()
    res = []; last = 0; manual = []; done = 0; moved = []
    for k, e, n in asserts(src):
        form = src[k:e]
        line = src[:k].count('\n') + 1
        if n in got:
            b = top_args(top_args(form)[1])[2]
            g = got[n]
            if len(num.findall(b)) == len(num.findall(g)) and shape(b) == shape(g):
                it = iter(num.findall(g))
                form = form.replace(b, num.sub(lambda m: next(it), b), 1); done += 1
            elif flip_ok:
                form = form.replace(b, literal(g), 1)
                moved.append((n, line, b, literal(g)))
            else:
                manual.append((n, line, b, g[:160]))
        res.append(src[last:k]); res.append(form); last = e
    res.append(src[last:])
    open(book, 'w').write(''.join(res))
    print("re-took", done)
    for n, line, b, g in manual:
        print("FLIP assert %d (line %d): pinned %s, ACL2's value %s -- differs beyond "
              "numbers (a decision that flipped, or a shape change); not moved: decide, "
              "or rerun with --flip-ok REASON" % (n, line, b[:80], g))
    for n in holds:
        print("DECIDE assert %d: it does not hold (a witness's inputs)" % n)
    if moved:
        print("moved %d witness(es) beyond numbers under --flip-ok; for the commit message:"
              % len(moved))
        for n, line, b, g in moved:
            print("  %s assert %d (line %d): %s -> %s: %s" % (book, n, line, b[:60], g[:60],
                                                             flip_ok))
    return 1 if manual or holds else 0


def acl2_command():
    """FN_ACL2, else this farm box's own (farm HOSTS), else tools/acl2 (the
    laptop's slot wrapper).  chunked-body-2: on persvati `acl2` is not on
    PATH and FN_ACL2 had to be set by hand."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import acl2_slots  # noqa: E402
    acl2_slots.apply_box_defaults()
    return os.environ.get("FN_ACL2") or str(Path(__file__).resolve().parent / "acl2")


def run(book, flip_ok=None, runner=subprocess.run):
    """emit, evaluate in BOOK's directory with the box's ACL2, apply."""
    path = Path(book).resolve()
    out = path.with_name(path.stem + ".retake-pins.lisp")
    log = path.with_name(path.stem + ".retake-pins.log")
    emit(str(path), str(out))
    acl2 = acl2_command()
    with open(log, "w") as handle:
        runner([acl2], input='(ld "%s" :ld-error-action :continue)\n' % out.name,
               stdout=handle, stderr=subprocess.STDOUT, text=True, cwd=path.parent,
               check=False)
    print("evaluated with %s; log %s" % (acl2, log))
    code = apply(str(path), str(log), flip_ok)
    out.unlink(missing_ok=True)
    return code


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="action", required=True)
    one = sub.add_parser("emit"); one.add_argument("book"); one.add_argument("out")
    one = sub.add_parser("apply"); one.add_argument("book"); one.add_argument("log")
    one.add_argument("--flip-ok", metavar="REASON", default=None,
                     help="also move witnesses whose value differs beyond numbers")
    one = sub.add_parser("run", help="emit, evaluate with this box's ACL2, apply")
    one.add_argument("book")
    one.add_argument("--flip-ok", metavar="REASON", default=None)
    args = parser.parse_args(argv)
    if args.action == "emit":
        return emit(args.book, args.out)
    if args.action == "apply":
        return apply(args.book, args.log, args.flip_ok)
    return run(args.book, args.flip_ok)


if __name__ == "__main__":
    sys.exit(main())
