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
import re
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



def asserts(src):
    """(start, end, index) of each top-level assert! outside a comment."""
    i = 0; n = 0
    while True:
        k = src.find('(assert!', i)
        if k < 0:
            return
        line_start = src.rfind('\n', 0, k) + 1
        if ';' in src[line_start:k]:
            i = k + 8
            continue
        e = read_form(src, k); n += 1
        yield k, e, n
        i = e


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


def apply(book, log):
    src = open(book).read(); text = open(log).read()
    got = {int(m.group(1)): m.group(2).strip()
           for m in re.finditer(r'PIN (\d+) NIL (.*?)\n NIL\n', text, re.S)}
    holds = [int(x) for x in re.findall(r'HOLD (\d+) NIL', text)]
    num = re.compile(r'-?\d+')
    shape = lambda x: re.sub(r'\s+', ' ', num.sub('N', x.upper().lstrip("'"))).strip()
    res = []; last = 0; manual = []; done = 0
    for k, e, n in asserts(src):
        form = src[k:e]
        if n in got:
            b = top_args(top_args(form)[1])[2]
            g = got[n]
            if len(num.findall(b)) == len(num.findall(g)) and shape(b) == shape(g):
                it = iter(num.findall(g))
                form = form.replace(b, num.sub(lambda m: next(it), b), 1); done += 1
            else:
                manual.append((n, src[:k].count('\n') + 1, g[:160]))
        res.append(src[last:k]); res.append(form); last = e
    res.append(src[last:])
    open(book, 'w').write(''.join(res))
    print("re-took", done)
    for n, line, g in manual:
        print("DECIDE assert %d (line %d): its value %s differs beyond numbers" % (n, line, g))
    for n in holds:
        print("DECIDE assert %d: it does not hold (a witness's inputs)" % n)
    return 1 if manual or holds else 0


if __name__ == "__main__":
    if len(sys.argv) != 4 or sys.argv[1] not in ("emit", "apply"):
        sys.exit(__doc__)
    sys.exit((emit if sys.argv[1] == "emit" else apply)(sys.argv[2], sys.argv[3]))
