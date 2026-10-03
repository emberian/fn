"""Prepare owner-carrier function threading in a NEW output directory.

The snapshot supplies loaded-world signatures, effect-closure classifications,
and exact input-file hashes. Input files are never overwritten. Every original
STATE result is retained: an owner writer adds FN-OWNER-ST immediately before
it, including single-STATE-returning functions. Unknown binding/output syntax
refuses the whole plan. Theorem events are preserved, not guessed, weakened or
deleted; callers must migrate their statements and provide boundary proofs.
This produces source for review/admission, never a certificate or migration claim.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from . import sexp

ST = "fn-owner-st"
READERS = {"fn-owner-ocfg", "fn-owner-core", "fn-owner-store",
           "fn-owner-retain-carry", "fn-owner-retain-statep"}
INSTALLERS = {"fn-owner-install-ocfg", "fn-owner-install-open-ocfg",
              "fn-owner-retain-carry-put"}
PRIVATE = READERS | INSTALLERS
GLOBALS = {"fn-owner": "fn-owner-ocfg", "fn-owner-retain-carry": "fn-owner-retain-carry"}

class Refused(ValueError):
    pass

def sym(node, name):
    return node.kind == "atom" and node.val.lower() == name

def quoted_symbol(node):
    if node.kind == "quote" and node.val == "'" and node.kids[0].kind == "atom":
        return node.kids[0].val.lower()
    if node.head() == "quote" and len(node.kids) == 2 and node.kids[1].kind == "atom":
        return node.kids[1].val.lower()
    return None

def splice(node, source, children):
    if len(children) != len(node.kids):
        raise Refused("internal splice arity mismatch")
    result = source[node.start:node.kids[0].start]
    for i, kid in enumerate(node.kids):
        end = node.kids[i + 1].start if i + 1 < len(node.kids) else node.end
        result += children[i] + source[kid.end:end]
    return result

class Threader:
    def __init__(self, signatures, source):
        self.signatures = signatures
        self.source = source
        self.function = ""
        self.writer = False

    def text(self, node):
        return self.source[node.start:node.end]

    def signature(self, node):
        return self.signatures.get(node.head()) if node.kind == "list" else None

    def owner_call(self, node):
        sig = self.signature(node)
        return bool(sig and sig.get("touch"))

    def writer_call(self, node):
        sig = self.signature(node)
        return bool(sig and sig.get("writer")) or node.head() in INSTALLERS

    def expr(self, node, tail=False):
        if node.kind == "quote":
            if node.val != "'":
                raise Refused(f"{self.function}: reader/template syntax needs explicit treatment")
            return self.text(node)
        if node.kind == "atom":
            if tail and self.writer:
                if sym(node, "state"):
                    return f"(mv {ST} state)"
                raise Refused(f"{self.function}: scalar tail in owner writer")
            return self.text(node)
        k, h = node.kids, node.head()
        if not k:
            return self.text(node)
        if not h:
            return splice(node, self.source, [self.expr(x) for x in k])
        if h in ("f-get-global", "get-global", "boundp-global", "f-boundp-global") and len(k) == 3:
            key = quoted_symbol(k[1])
            if key in GLOBALS:
                if not sym(k[2], "state"):
                    raise Refused(f"{self.function}: nonliteral owner-global state")
                reader = "fn-owner-boundp" if "boundp" in h else GLOBALS[key]
                if key == "fn-owner-retain-carry" and "boundp" in h:
                    raise Refused(f"{self.function}: binding test of retention global needs explicit migration")
                return f"({reader} {ST})"
        if h in ("put-global", "f-put-global") and len(k) == 4 and quoted_symbol(k[1]) in GLOBALS:
            raise Refused(f"{self.function}: direct authoritative global write needs installer boundary")
        if h == "declare":
            raise Refused(f"{self.function}: nested declaration needs explicit treatment")
        if h in ("let", "let*"):
            if len(k) < 3 or k[1].kind != "list":
                raise Refused(f"{self.function}: malformed {h}")
            bindings = k[1].kids
            if h == "let" and any(b.kind == "list" and len(b.kids) == 2 and
                                  self.writer_call(b.kids[1]) for b in bindings):
                raise Refused(f"{self.function}: parallel owner-writer bindings")
            bodies = [self.expr(x, tail and i == len(k) - 1) for i, x in enumerate(k[2:], 2)]
            # Sequential expansion preserves LET* evaluation order, including
            # unrelated global writes after an authoritative installer.
            rest = " ".join(bodies)
            for binding in reversed(bindings):
                if binding.kind != "list" or len(binding.kids) != 2:
                    raise Refused(f"{self.function}: unsupported binding")
                var, value = binding.kids
                rhs = self.expr(value)
                if sym(var, "state") and value.head() in INSTALLERS:
                    rest = f"(let (({ST} {rhs})) {rest})"
                elif self.writer_call(value):
                    sig = self.signature(value)
                    if not sym(var, "state") or sig["outs"] != ["state"]:
                        raise Refused(f"{self.function}: owner writer requires explicit MV binding")
                    rest = f"(mv-let ({ST} state) {rhs} {rest})"
                else:
                    rest = f"(let (({self.text(var)} {rhs})) {rest})"
            if h == "let*":
                return rest
            return splice(node, self.source, [self.text(k[0]),
                splice(k[1], self.source, [splice(b, self.source,
                    [self.text(b.kids[0]), self.expr(b.kids[1])]) for b in bindings]), *bodies])
        if h == "mv-let":
            if len(k) < 4 or k[1].kind != "list":
                raise Refused(f"{self.function}: malformed mv-let")
            names = [self.text(x) for x in k[1].kids]
            if self.writer_call(k[2]):
                sig = self.signature(k[2])
                if not sig or len(names) != len(sig["outs"]) or "state" not in sig["outs"]:
                    raise Refused(f"{self.function}: wrong original MV signature")
                pos = sig["outs"].index("state")
                if names[pos].lower() != "state":
                    raise Refused(f"{self.function}: aliased returned state")
                names.insert(pos, ST)
            return splice(node, self.source, [self.text(k[0]), "(" + " ".join(names) + ")",
                self.expr(k[2]), *[self.expr(x, tail and i == len(k) - 1)
                                  for i, x in enumerate(k[3:], 3)]])
        if h == "if":
            return splice(node, self.source, [self.text(k[0]), self.expr(k[1]),
                                              *[self.expr(x, tail) for x in k[2:]]])
        if h == "cond":
            rows = []
            for row in k[1:]:
                if row.kind != "list" or len(row.kids) < 2:
                    raise Refused(f"{self.function}: unsupported cond clause")
                rows.append(splice(row, self.source, [self.expr(x, tail and i == len(row.kids)-1)
                                                    for i, x in enumerate(row.kids)]))
            return splice(node, self.source, [self.text(k[0]), *rows])
        if h in ("case", "stobj-let", "with-local-stobj", "return-last", "progn$", "er"):
            raise Refused(f"{self.function}: {h} needs explicit output treatment")
        if h == "value":
            if not tail or not self.writer or len(k) != 2:
                raise Refused(f"{self.function}: unexpected value")
            return f"(mv nil {self.expr(k[1])} {ST} state)"
        if h == "mv":
            children = [self.text(k[0]), *[self.expr(x) for x in k[1:]]]
            if tail and self.writer:
                positions = [i for i, x in enumerate(k) if sym(x, "state")]
                if positions != [len(k)-1]:
                    raise Refused(f"{self.function}: MV state must be the final original output")
                children[-1] = f"{ST} state"
            return splice(node, self.source, children)
        sig = self.signature(node)
        args = [self.expr(x) for x in k[1:]]
        if h in PRIVATE or (sig and sig.get("touch")):
            if not sig or len(args) != len(sig["formals"]) or "state" not in sig["formals"]:
                raise Refused(f"{self.function}: absent or wrong signature for {h}")
            pos = sig["formals"].index("state")
            if not sym(k[pos+1], "state"):
                raise Refused(f"{self.function}: nonliteral state argument of {h}")
            if h in PRIVATE:
                args[pos] = ST
            else:
                args.insert(pos, ST)
        result = "(" + " ".join([self.text(k[0]), *args]) + ")"
        if tail and self.writer:
            if h in INSTALLERS:
                return f"(let (({ST} {result})) (mv {ST} state))"
            if sig and sig.get("writer"):
                return result
            if sig and sig["outs"] == ["state"] or h in ("put-global", "f-put-global"):
                return f"(let ((state {result})) (mv {ST} state))"
            raise Refused(f"{self.function}: unknown tail outputs for {h}")
        return result

    def definition(self, node):
        k = node.kids
        name = k[1].val.lower()
        sig = self.signatures[name]
        self.function, self.writer = name, sig.get("writer", False)
        if name in PRIVATE:
            raise Refused(f"{name}: primitive wrappers require explicit physical-carrier definitions")
        formals = [x.val.lower() for x in k[2].kids]
        if formals != sig["formals"] or formals.count("state") != 1:
            raise Refused(f"{name}: loaded-world/source formal mismatch")
        if self.writer and (not sig["outs"] or sig["outs"][-1] != "state"):
            raise Refused(f"{name}: original writer does not return trailing state")
        formals.insert(formals.index("state"), ST)
        declarations = []
        for decl in k[3:-1]:
            if decl.head() != "declare":
                raise Refused(f"{name}: non-declaration before body")
            children = [self.text(decl.kids[0])]
            for part in decl.kids[1:]:
                if part.head() == "xargs":
                    values = ["xargs"]
                    had_stobjs = False
                    if len(part.kids) % 2 != 1:
                        raise Refused(f"{name}: malformed xargs")
                    for i in range(1, len(part.kids), 2):
                        key, value = part.kids[i:i+2]
                        if sym(key, ":stobjs"):
                            had_stobjs = True
                            names = [value.val.lower()] if value.kind == "atom" else [x.val.lower() for x in value.kids]
                            expected = [x for x in sig["ins"] if x]
                            if sorted(names) != sorted(expected) or names.count("state") != 1:
                                raise Refused(f"{name}: loaded-world/source stobj mismatch")
                            names.insert(names.index("state"), ST)
                            values += [":stobjs", "("+" ".join(names)+")"]
                        elif sym(key, ":guard"):
                            values += [self.text(key), self.expr(value)]
                        elif sym(key, ":guard-hints"):
                            raise Refused(f"{name}: guard hints need explicit migrated substitutions")
                        else:
                            values += [self.text(key), self.text(value)]
                    if not had_stobjs:
                        raise Refused(f"{name}: source omits explicit stobj declaration")
                    children.append("("+" ".join(values)+")")
                else:
                    children.append(self.text(part))
            declarations.append("("+" ".join(children)+")")
        return "("+" ".join([self.text(k[0]), self.text(k[1]), "("+" ".join(formals)+")",
                              *declarations, "(declare (ignorable state))", self.expr(k[-1], True)])+")"


def prepare(root, snapshot, destination):
    root, destination = Path(root).resolve(), Path(destination).resolve()
    if destination.exists():
        raise Refused("output must not exist; inputs and earlier work are never overwritten")
    if destination == root or destination in root.parents:
        raise Refused("output cannot replace the source tree or an ancestor")
    if snapshot.get("schema") != "fn-owner-carrier-world-v1" or not snapshot.get("world_coordinate"):
        raise Refused("a source-bound loaded-world snapshot is required")
    signatures = snapshot["functions"]
    rendered = {}
    seen = set()
    # Validate and render EVERY file before creating any output.
    for relative, expected in snapshot["source_files"].items():
        named = Path(relative)
        if named.is_absolute() or ".." in named.parts or relative == "owner-carrier-input.json":
            raise Refused("source file names must be normalized relative input paths")
        unnormalized = root / relative
        path = unnormalized.resolve()
        if root not in path.parents or unnormalized.is_symlink():
            raise Refused("source path escapes the input tree")
        raw = path.read_bytes()
        if hashlib.sha256(raw).hexdigest() != expected:
            raise Refused(f"source digest mismatch: {relative}")
        source = raw.decode()
        edits = []
        threader = Threader(signatures, source)
        for node in sexp.read_all(source):
            if node.head() in ("defun", "defund") and node.kids[1].val.lower() in signatures:
                if signatures[node.kids[1].val.lower()].get("touch"):
                    name = node.kids[1].val.lower()
                    if name in seen:
                        raise Refused(f"{name}: multiple source definitions need an explicit loaded-world selection")
                    seen.add(name)
                    edits.append((node.start, node.end, threader.definition(node)))
        for a, b, replacement in reversed(edits):
            source = source[:a]+replacement+source[b:]
        rendered[relative] = source
    expected = {name for name, sig in signatures.items() if sig.get("touch") and name not in PRIVATE}
    if seen != expected:
        raise Refused("snapshot functions absent from selected source: " + ", ".join(sorted(expected-seen)))
    destination.mkdir(parents=True)
    for relative, source in rendered.items():
        path = destination / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
    (destination / "owner-carrier-input.json").write_text(json.dumps(snapshot, indent=2)+"\n")
    return sorted(rendered)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--snapshot", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        paths = prepare(args.source_root, json.loads(args.snapshot.read_text()), args.output)
    except (Refused, ValueError, OSError, KeyError) as error:
        parser.exit(2, f"owner-carrier: refused: {error}\n")
    print(f"prepared {len(paths)} files in {args.output}; admission and proof migration remain owed")

if __name__ == "__main__":
    main()
