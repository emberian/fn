#!/usr/bin/env python3
"""tools/nontail_recursions.py -- the non-tail recursions an executable closure runs.

Reads the extractor's JSON (tools/extract/frontend.lisp `xt-extract' on lane
extract-2: every function of the closure with its EXECUTABLE body, mbe
resolved to :exec where the function runs raw) and lists every function in a
recursive strongly connected component that calls a member of its component
outside tail position.  Each such call is one control-stack frame per
recursion step, so its depth is the thread-stack figure the path needs
(PKT-693, lane thread-stacks).

Tail position: the body; both branches of an IF whose IF is in tail position;
a lambda body whose application is in tail position; the last argument of a
RETURN-LAST (prog2$ and friends).  Everything else (an argument, an IF test,
a lambda actual) is not.

    python3 tools/nontail_recursions.py served.json [--json]
"""
import json
import sys


def calls(term, tail, out):
    """Append (callee, tailp) for every call in TERM."""
    tag = term[0]
    if tag in ("v", "q"):
        return
    if tag == "l":
        _, formals, body, actuals = term
        for a in actuals:
            calls(a, False, out)
        calls(body, tail, out)
        return
    _, fn, args = term
    out.append((fn, tail))
    if fn == "COMMON-LISP::IF":
        calls(args[0], False, out)
        calls(args[1], tail, out)
        calls(args[2], tail, out)
    elif fn == "ACL2::RETURN-LAST":
        for a in args[:-1]:
            calls(a, False, out)
        calls(args[-1], tail, out)
    else:
        for a in args:
            calls(a, False, out)


def sccs(graph):
    index, low, stack, on, out, n = {}, {}, [], set(), [], [0]
    sys.setrecursionlimit(100000)

    def visit(v):
        index[v] = low[v] = n[0]
        n[0] += 1
        stack.append(v)
        on.add(v)
        for w in graph.get(v, ()):
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            out.append(comp)

    for v in graph:
        if v not in index:
            visit(v)
    return out


def main(argv):
    data = json.load(open(argv[1]))
    bodies = {f["name"]: f["body"] for f in data["functions"]
              if f["kind"] == "defun"}
    # ACL2's own functions (len, binary-append, ...) run as Common Lisp's
    # raw definitions, not their logical bodies: listed apart.
    predefined = {f["name"] for f in data["functions"] if f.get("predefined")}
    sites = {}
    for name, body in bodies.items():
        out = []
        calls(body, True, out)
        sites[name] = out
    graph = {n: sorted({c for c, _ in s if c in bodies}) for n, s in sites.items()}
    rows = []
    for comp in sccs(graph):
        members = set(comp)
        if len(comp) == 1 and comp[0] not in graph[comp[0]]:
            continue
        for fn in sorted(comp):
            bad = sorted({c for c, tail in sites[fn] if c in members and not tail})
            if bad:
                rows.append({"function": fn, "component": sorted(comp),
                             "nontail_calls": bad,
                             "predefined": fn in predefined})
    if "--json" in argv:
        json.dump(rows, sys.stdout, indent=1)
        print()
    else:
        for r in rows:
            print("predefined" if r["predefined"] else "fn",
                  r["function"].split("::")[-1].lower(), "->",
                  " ".join(c.split("::")[-1].lower() for c in r["nontail_calls"]))
        print("non-tail recursive functions:", len(rows), "of", len(bodies),
              "defuns;", sum(r["predefined"] for r in rows), "predefined",
              file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
