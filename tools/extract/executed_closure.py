#!/usr/bin/env python3
"""Conservative path-sensitive closure of frontend.lisp's world-derived IR.

The frontend resolves MBE, attachments and raw/logic routes. This checker
interprets only immutable constructors, selectors, and decidable tests.
Unknown IFs visit BOTH arms. Recursive SCCs are inspected with unconstrained
arguments and return opaque terms; they are never assumed cost-free. Unknown
functions, mutable operations, extraction blockers and budget exhaustion fail.
This is a checked call-reachability gate, not a time or allocation theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


class Unresolved(ValueError):
    pass


def calls(term):
    if term[0] == "c":
        return {term[1]} | set().union(*(calls(t) for t in term[2]))
    if term[0] == "l":
        return calls(term[2]) | set().union(*(calls(t) for t in term[3]))
    if term[0] in ("q", "v"):
        return set()
    raise Unresolved(f"unknown IR term {term[0]}")


def recursive_functions(graph):
    """Tarjan SCCs, including mutual recursion and self calls."""
    indices, low, stack, active, recursive = {}, {}, [], set(), set()

    def visit(v):
        indices[v] = low[v] = len(indices)
        stack.append(v)
        active.add(v)
        for w in graph.get(v, ()):
            if w not in indices:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in active:
                low[v] = min(low[v], indices[w])
        if low[v] == indices[v]:
            component = []
            while True:
                w = stack.pop()
                active.remove(w)
                component.append(w)
                if w == v:
                    break
            if len(component) > 1 or v in graph.get(v, ()):
                recursive.update(component)

    for v in graph:
        if v not in indices:
            visit(v)
    return recursive


class Closure:
    def __init__(self, world, forbidden, budget=200000):
        self.functions = {f["name"]: f for f in world["functions"]}
        self.forbidden = set(forbidden)
        self.graph = {n: calls(f["body"]) if "body" in f else set()
                      for n, f in self.functions.items()}
        self.recursive = recursive_functions(self.graph)
        self.inspected_recursive = set()
        self.memo = {}
        self.nodes, self.interned = [], {}
        self.reached, self.violations, self.pruned = set(), {}, []
        self.path = []
        self.active_args = []
        self.budget = budget
        self.nil = self.node("atom", "y", "COMMON-LISP::NIL")
        self.true = self.node("atom", "y", "COMMON-LISP::T")

    def node(self, *parts):
        if parts not in self.interned:
            self.interned[parts] = len(self.nodes)
            self.nodes.append(parts)
        return self.interned[parts]

    def datum(self, datum):
        if isinstance(datum, int):
            return self.node("atom", "i", datum)
        if datum[0] == "L":
            tail = self.datum(datum[2])
            for head in reversed(datum[1]):
                tail = self.node("cons", self.datum(head), tail)
            return tail
        if datum[0] in ("y", "s", "i", "r", "ch"):
            return self.node("atom", *datum)
        raise Unresolved(f"unsupported datum {datum[0]}")

    def truth(self, value):
        if value == self.nil:
            return False
        if self.nodes[value][0] in ("cons", "atom"):
            return True
        return None

    def term(self, t, env):
        self.budget -= 1
        if self.budget < 0:
            raise Unresolved("symbolic analysis budget exhausted")
        if t[0] == "v":
            return env[t[1]]
        if t[0] == "q":
            return self.datum(t[1])
        if t[0] == "l":
            values = [self.term(x, env) for x in t[3]]
            return self.term(t[2], dict(zip(t[1], values, strict=True)))
        if t[0] != "c":
            raise Unresolved(f"unknown term {t[0]}")
        fn, args = t[1:]
        if fn == "COMMON-LISP::IF":
            self.reached.add(fn)
            condition = self.term(args[0], env)
            known = self.truth(condition)
            if known is not None:
                self.pruned.append((tuple(self.path), known))
                return self.term(args[1 if known else 2], env)
            yes = self.term(args[1], env)
            no = self.term(args[2], env)
            return yes if yes == no else self.node("if", condition, yes, no)
        return self.call(fn, tuple(self.term(x, env) for x in args))

    def call(self, fn, args):
        self.reached.add(fn)
        if fn in self.forbidden:
            self.violations.setdefault(fn, tuple(self.path + [fn]))
            return self.node("call", fn, *args)
        f = self.functions.get(fn)
        if f is None:
            raise Unresolved(f"missing world definition: {fn}")
        if len(args) != len(f["formals"]):
            raise Unresolved(f"arity mismatch: {fn}")
        if any(f.get("stobjs_in", [])) or any(f.get("stobjs_out", [])):
            raise Unresolved(f"mutable/stobj function: {fn}")
        if f["kind"] == "prim":
            return self.primitive(fn, args)
        if (f["kind"] != "defun" or f.get("invariant_risk") or
                f.get("class") != "common-lisp-compliant"):
            raise Unresolved(f"unresolved executed route: {fn} ({f['kind']})")
        previous = next((a for n, a in reversed(self.active_args) if n == fn), None)
        # Finite unrolling of a concrete decreasing natural (e.g. a record's
        # nth selector). No function name or user-supplied cost contract is used.
        decreasing = any(self.integer(a) is not None and 0 <= self.integer(a) <= 16
                         and (previous is None or
                              (self.integer(previous[i]) is not None and
                               self.integer(a) < self.integer(previous[i])))
                         for i, a in enumerate(args))
        if fn in self.recursive and not decreasing:
            if fn not in self.inspected_recursive:
                self.inspected_recursive.add(fn)
                # No facts from this call may hide a branch of a later call.
                generic = tuple(self.node("unknown", fn, formal) for formal in f["formals"])
                self.expand(fn, generic)
            return self.node("call", fn, *args)
        key = (fn, args)
        if key not in self.memo:
            self.memo[key] = self.expand(fn, args)
        return self.memo[key]

    def expand(self, fn, args):
        self.path.append(fn)
        self.active_args.append((fn, args))
        try:
            f = self.functions[fn]
            return self.term(f["body"], dict(zip(f["formals"], args, strict=True)))
        finally:
            self.path.pop()
            self.active_args.pop()

    def integer(self, value):
        node = self.nodes[value]
        return node[2] if node[:2] == ("atom", "i") else None

    def primitive(self, fn, args):
        name = fn.split("::")[-1]
        if name == "CONS":
            return self.node("cons", *args)
        if name in ("CAR", "CDR"):
            value = self.nodes[args[0]]
            if value[0] == "cons":
                return value[1 if name == "CAR" else 2]
            if value[0] == "atom":
                return self.nil
        if name == "CONSP":
            value = self.nodes[args[0]]
            if value[0] in ("atom", "cons"):
                return self.true if value[0] == "cons" else self.nil
        ints = [self.integer(a) for a in args]
        if name in ("INTEGERP", "RATIONALP", "ACL2-NUMBERP") and ints[0] is not None:
            return self.true
        if all(x is not None for x in ints):
            if name in ("<", "EQUAL"):
                yes = ints[0] < ints[1] if name == "<" else ints[0] == ints[1]
                return self.true if yes else self.nil
            if name in ("BINARY-+", "BINARY-*", "UNARY--"):
                value = (ints[0] + ints[1] if name == "BINARY-+" else
                         ints[0] * ints[1] if name == "BINARY-*" else -ints[0])
                return self.node("atom", "i", value)
        if name == "EQUAL":
            if args[0] == args[1]:
                return self.true
            a, b = (self.nodes[x] for x in args)
            if a[0] == b[0] == "atom":
                # Numeric representations need normalization; stay unknown.
                if a[1] in ("y", "s", "ch") and b[1] in ("y", "s", "ch"):
                    return self.nil
            if {a[0], b[0]} == {"atom", "cons"}:
                return self.nil
        # The exported ACL2 primitive set is pure; no hidden user callees.
        return self.node("primitive", fn, *args)

    def check(self, root, constants=None):
        f = self.functions[root]
        constants = constants or {}
        args = tuple(self.datum(constants[x]) if x in constants
                     else self.node("unknown", root, x) for x in f["formals"])
        self.call(root, args)
        return {"root": root, "reached": sorted(self.reached),
                "violations": {k: list(v) for k, v in sorted(self.violations.items())},
                "resolved_branches": len(self.pruned)}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("world", type=Path)
    p.add_argument("root", nargs="?")
    p.add_argument("--forbid", action="append", default=[])
    p.add_argument("--constants", default="{}", help="formal -> frontend datum JSON")
    p.add_argument("--catchup", action="store_true", help="K2a and its reference control")
    p.add_argument("--report", type=Path, help="save the complete derived closures")
    a = p.parse_args()
    if a.catchup and (a.root or a.forbid or a.constants != "{}"):
        p.error("--catchup has fixed subjects and forbidden predicates")
    if not a.catchup and not a.root:
        p.error("provide a root or --catchup")
    try:
        raw = a.world.read_bytes()
        world = json.loads(raw)
        result = catchup(world) if a.catchup else Closure(world, a.forbid).check(
            a.root, json.loads(a.constants))
    except (Unresolved, KeyError, RecursionError) as e:
        print(f"executed_closure: UNRESOLVED: {e}")
        return 2
    result["world_sha256"] = hashlib.sha256(raw).hexdigest()
    if a.report:
        a.report.write_text(json.dumps(result, indent=2) + "\n")
    if a.catchup:
        for r in result["subjects"]:
            print(f"executed_closure: {r['root']}: {len(r['reached'])} reachable functions, "
                  f"{len(r['violations'])} forbidden")
        print("executed_closure: reference tooth: " +
              ", ".join(result["reference_leaves"]["violations"]))
        print(f"executed_closure: K2a {'PASS' if result['passed'] else 'FAIL'}; "
              f"world sha256 {result['world_sha256']}")
        return int(not result["passed"])
    print(json.dumps(result, indent=2))
    return int(bool(result["violations"]))


def catchup(world):
    # This is the forbidden set from the contract, never a declared closure.
    forbidden = {"ACL2::" + name for name in (
        "FN-STATEP", "FN-NODE-STATEP", "FN-NNTP-PROJECTIONP", "FN-PEER-SESSIONP",
        "FN-OWN-CONN-BOUNDEDP", "FN-ARTICLES-FRESHP", "FN-ARTICLE-LISTP")}
    subjects = [Closure(world, forbidden).check("ACL2::" + root)
                for root in ("FN-OOP-ADVANCE", "FN-OCT-TRANSIT")]
    reference = Closure(world, forbidden).check("ACL2::FN-OCFG-ADVANCE")
    # Also expose the validator leaves beyond enclosing forbidden recognizers.
    leaves = {"ACL2::FN-STATEP", "ACL2::FN-NODE-STATEP"}
    reference_leaves = Closure(world, leaves).check("ACL2::FN-OCFG-ADVANCE")
    return {"subjects": subjects, "reference": reference, "reference_leaves": reference_leaves,
            "passed": not any(r["violations"] for r in subjects)
                      and bool(reference["violations"])
                      and bool(leaves & reference_leaves["violations"].keys())}


if __name__ == "__main__":
    raise SystemExit(main())
