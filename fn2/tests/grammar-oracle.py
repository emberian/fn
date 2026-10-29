#!/usr/bin/env python3
"""Check the declared NNTP grammar table against layer H's spec-derived model.

Usage: python3 fn2/tests/grammar-oracle.py [MODEL_DIR] [--table build/nntp-grammar-table.txt]

The table is written by `tools/acl2 < fn2/tests/grammar-export.lsp >
build/nntp-grammar-table.txt` (from the certified tests/grammar-unit). Checks:
the declared keyword set equals the model's KEYWORDS; the declared HELP text
equals the model's HELP; every keyword's citation is the model's SPECS entry;
and the grammar's Message-ID, range and wildmat validators agree with the
model's MSGID, number_range and wildmat on the exported sample. Every
disagreement is printed; the exit status is the number of disagreements
(capped at 1). A disagreement is resolved by reading the spec, never by
bending the table to the model.
"""
import importlib, os, re, sys

def parse_sexpr(text, i=0):
    """Minimal reader for ACL2's printed rows: lists, strings, symbols, numbers."""
    def skip(i):
        while i < len(text) and text[i] in " \t\r\n":
            i += 1
        return i
    i = skip(i)
    c = text[i]
    if c == "(":
        out, i = [], i + 1
        while True:
            i = skip(i)
            if text[i] == ")":
                return out, i + 1
            v, i = parse_sexpr(text, i)
            out.append(v)
    if c == '"':
        out, i = [], i + 1
        while text[i] != '"':
            if text[i] == "\\":
                i += 1
            out.append(text[i]); i += 1
        return "".join(out), i + 1
    j = i
    while j < len(text) and text[j] not in " \t\r\n()":
        j += 1
    tok = text[i:j]
    return (int(tok) if re.fullmatch(r"-?\d+", tok) else tok.lower()), j

def main(argv):
    table_path = "build/nntp-grammar-table.txt"
    args = [a for a in argv[1:]]
    if "--table" in args:
        k = args.index("--table"); table_path = args[k + 1]; del args[k:k + 2]
    model_dir = args[0] if args else ("fn2/tests/model" if os.path.isdir("fn2/tests/model")
                                      else "/Users/ember/dev/fn/build/lanes/fn2/h-harness/fn2/tests/model")
    sys.path.insert(0, os.path.dirname(os.path.abspath(model_dir)))
    model = importlib.import_module(os.path.basename(os.path.abspath(model_dir)) + ".nntp_model")
    text = open(table_path, encoding="latin-1").read().replace("ACL2 !>", "")
    rows, samples, help_text = [], [], None
    for line in text.splitlines():
        if line.startswith("GRAMMAR-ROW "):
            rows.append(parse_sexpr(line, len("GRAMMAR-ROW "))[0])
        elif line.startswith("GRAMMAR-SAMPLE "):
            samples.append(parse_sexpr(line, len("GRAMMAR-SAMPLE "))[0])
    m = re.search(r'GRAMMAR-HELP "((?:[^"\\]|\\.)*)"', text, re.S)
    if m:
        help_text = re.sub(r"\\(.)", r"\1", m.group(1))
    bad = []
    keywords = {r[0] for r in rows}
    if keywords != model.KEYWORDS:
        bad.append(f"keywords: declared-only {sorted(keywords - model.KEYWORDS)}, model-only {sorted(model.KEYWORDS - keywords)}")
    if help_text is None or help_text.replace("\n", "\r\n").replace("\r\r\n", "\r\n").encode() != model.HELP:
        bad.append(f"HELP text differs: declared {help_text!r} vs model {model.HELP!r}")
    def norm(s): return s.replace("§§", "sections ").replace("§", "section ")
    for r in rows:
        kw, spec = r[0], r[5]
        if kw not in model.SPECS:
            bad.append(f"{kw}: no SPECS citation in the model")
        elif norm(model.SPECS[kw]) != spec:
            bad.append(f"{kw}: citation {spec!r} vs model {model.SPECS[kw]!r}")
    def model_verdict(kind, s):
        try:
            if kind == ":msgid":
                return model.msgid(s)
            if kind == ":range":
                model.number_range(s, 2147483647); return True
            model.wildmat(s, ""); return True
        except ValueError:
            return False
    for kind, s, verdict in samples:
        ours = verdict == "t"
        if ours != model_verdict(kind, s):
            bad.append(f"{kind} {s!r}: grammar {'accepts' if ours else 'refuses'}, model {'accepts' if not ours else 'refuses'}")
    for b in bad:
        print("DISAGREE", b)
    print(f"GRAMMAR-ORACLE {len(rows)} commands, {len(samples)} validator samples, {len(bad)} disagreements")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv))
