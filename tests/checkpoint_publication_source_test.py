#!/usr/bin/env python3
"""Publication syntax/ABI controls, not execution, recovery or durability proof."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from lisp_source import forms, read_sexp


def walk(tree):
    if isinstance(tree, list):
        yield tree
        for child in tree:
            yield from walk(child)


def parsed(text):
    return [read_sexp(form) for form in forms(text)]


def function(text, name):
    return next(node for form in parsed(text) for node in walk(form) if node[:2] == ["defun", name])


def contract(publication, boot, ops, writer):
    binding = function(boot, "fn2-checkpoint-publication-bind-boot")
    assert not any(node and node[0] in ("has-base", "active-bank") for node in walk(binding)), "geometry bind may not erase actual live base"
    begin = function(publication, "fn2-checkpoint-publication-begin")
    for field in ("packet-mask", "len0", "len1", "stage0", "stage1", "checker-live", "op-slot", "op-gen"):
        assert [field, "0"] in list(walk(begin)), "attempt field not reset"
    begin_nodes = list(walk(begin))
    assert ["fn2-checkpoint-publication-previous-matchesp", "0", "previous-hash", "fn2-checkpoint-publication", "fn2-digests"] in begin_nodes
    for index in range(8):
        assert ["attempt-hash-" + str(index), ["fn2-checkpoint-descriptor-identity-word", "c", str(index), "fn2-checkpoint-bytes"]] in begin_nodes
    harvest = function(publication, "fn2-checkpoint-publication-harvest")
    promoted = next(node for node in walk(harvest) if node[:2] == ["if", ["and", "fence", "success"]])
    assert promoted[-1] == "fn2-checkpoint-publication"
    for index in range(8):
        assert ["base-hash-" + str(index), ["fn2-checkpoint-publication-attempt-hash-" + str(index), "0", "fn2-checkpoint-publication"]] in list(walk(promoted[2]))
    actual_begin = function(ops, "fn2-checkpoint-writer-begin-children")
    assert ["fn2-checkpoint-publication-previous-load", "0", "previous", "fn2-checkpoint-publication", "fn2-digests"] in list(walk(actual_begin))
    assert not any(node and node[0] == "fn2-rec-zero-digest" for node in walk(actual_begin))
    release = function(ops, "fn2-checkpoint-writer-release-children")
    nodes = list(walk(release))
    assert ["equal", "pending", "0"] in nodes
    assert ["equal", ["fn2-checkpoint-publication-phase", "0", "fn2-checkpoint-publication"], "*fn2-checkpoint-publication-phase-complete*"] in nodes
    assert ["equal", ["fn2-checkpoint-publication-bundle-released", "0", "fn2-checkpoint-publication"], "0"] in nodes
    bindings = release[-1][1]
    assert not any(node and node[0] in ("fn2-core-release-children", "fn2-pool-release") for node in nodes), "writer returns borrowed leases; central cleanup frees"
    handbacks = [node for node in nodes if node and node[0] == "fn2-checkpoint-future-return-anchor"]
    assert len(handbacks) == 1 and handbacks[0][1:8] == ["token", "master-kind", "master-slot", "master-gen", "kind", "owner", "generation"]
    reserve = function(ops, "fn2-checkpoint-writer-reserve-children")
    reserve_nodes = list(walk(reserve))
    assert ["fn2-checkpoint-future-no-loansp", "1", "5", "fn2-checkpoint-future-windows"] in reserve_nodes, "settlement does not imply journal handback"
    assert any(node and node[0] == "fn2-checkpoint-future-borrow-anchor" for node in reserve_nodes)
    assert not any(node and node[0] in ("fn2-pool-reserve", "fn2-core-reserve") for node in reserve_nodes), "no post-cut pool acquisition"
    for candidate in (nodes, reserve_nodes):
        assert ["fn2-checkpoint-builder-claimp", "c", "token", "master-kind", "master-slot", "master-gen", "fn2-checkpoints"] in candidate
    assert bindings[-1] == ["fn2-checkpoint-publication", ["fn2-checkpoint-publication-set-bundle-released", "0", "1", "fn2-checkpoint-publication"]]
    start = function(writer, "fn2-checkpoint-writer-start-children")
    assert start[2][0] == "c" and all(arg.startswith("fn2-") for arg in start[2][1:]), "no caller closure/owner/target flags"
    nodes = list(walk(start))
    for callee in ("fn2-checkpoint-builder-claimp", "fn2-checkpoint-production-roots-p", "fn2-checkpoint-retainedp", "fn2-checkpoint-installation-seal-row"):
        assert any(node and node[0] == callee for node in nodes), "missing actual admission source"
    assert ["equal", ["fn2-alloc-freeze-phase", "fn2-extents"], "2"] in nodes
    assert ["equal", ["fn2-checkpoint-publication-bundle-released", "0", "fn2-checkpoint-publication"], "1"] in nodes
    assert ["target", ["fn2-machines-kind-basesi", "*fn2-checkpoint-writer-kind*", "fn2-machines"]] in nodes
    assert ["generation", ["fn2-checkpoint-writer-generation", "0", "fn2-checkpoint-writer"]] in nodes
    assert ["requester-gen", "requestgen"] in nodes and ["requester-slot", "requester"] in nodes
    arms = next(form for form in parsed(writer) if form[:3] == ["defmachine-arms", "fn2-checkpoint-writer", ":declare"])
    arms = arms[arms.index(":arms") + 1]
    wait = next(arm for arm in arms if arm[0] == ":wait")
    assert ["member-equal", "phase", ["list", "*fn2-checkpoint-publication-phase-write-second*", "*fn2-checkpoint-publication-phase-fence*"]] in list(walk(wait))
    assert ["pending", "0"] in list(walk(wait))
    notify = next(arm for arm in arms if arm[0] == ":notify")
    assert ["eq", ["fn2-machine-generation-read-code", "requester"], ":ok"] in list(walk(notify))
    assert ["equal", ["fn2-machine-generation", "requester"], "requestgen"] in list(walk(notify))
    assert [":wake-row", "requester"] in list(walk(notify))
    for operation, child in (("fn2-checkpoint-writer-begin", "fn2-checkpoint-writer-begin-children"), ("fn2-checkpoint-writer-release", "fn2-checkpoint-writer-release-children")):
        target = function(ops, child)
        scalars = [arg for arg in target[2] if not arg.startswith("fn2-")]
        calls = [node for arm in arms for node in walk(arm) if node and node[0] == operation]
        assert calls and all(len(call) - 1 == len(scalars) for call in calls), "actual writer scalar ABI mismatch"
    # Every explicit multi-child preservation package uses actual projection
    # positions, exact row frames and all read-only input carrier guards.
    for source in (publication, boot, ops, writer):
        for form in parsed(source):
            for proof in walk(form):
                if not proof or not isinstance(proof[0], str) or not proof[0].endswith("-preserves"):
                    continue
                definition = function(source, proof[1])
                assert proof[2] == definition[2]
                declaration = definition[3][1]
                inputs = declaration[declaration.index(":stobjs") + 1]
                if isinstance(inputs, str):
                    inputs = [inputs]
                hyps = proof[proof.index(":hyps") + 1]
                assert all([obj + "p", obj] in hyps and [obj + "-wfp", obj] in hyps for obj in inputs)
                specs = proof[proof.index(":specs") + 1]
                for spec in specs:
                    if spec and spec[0].endswith("-wfp"):
                        obj = spec[0].removesuffix("-wfp")
                        assert [obj + "p", spec[1]] in specs
                        assert [obj + "-rows", spec[1], ":frame", obj] in specs


def main():
    paths = [ROOT / "books" / (name + ".lisp") for name in ("checkpoint-publication", "checkpoint-boot", "checkpoint-writer-ops", "checkpoint-writer")]
    source = [path.read_text() for path in paths]
    contract(*source)
    cases = (
        (1, '(groups (fn2-boot-config-count fn2-boot-config))', '(groups (fn2-boot-config-count fn2-boot-config)) (has-base 0)'),
        (2, '(equal pending 0)', 't'),
        (3, '(equal (fn2-checkpoint-publication-bundle-released 0 fn2-checkpoint-publication) 1)', 't'),
        (3, '(equal (fn2-machine-generation requester) requestgen)', 't'),
        (0, '(if (and fence success)', '(if success'),
        (2, '(fn2-checkpoint-publication-previous-load 0 previous fn2-checkpoint-publication fn2-digests)', '(fn2-rec-zero-digest previous fn2-digests)'),
        (2, '(fn2-checkpoint-future-no-loansp 1 5 fn2-checkpoint-future-windows)', 't'),
        (2, '(fn2-checkpoint-future-return-anchor token master-kind master-slot master-gen kind owner generation', '(fn2-checkpoint-future-borrow-anchor token master-kind master-slot master-gen kind owner generation'),
    )
    for index, before, after in cases:
        changed = source.copy()
        changed[index] = changed[index].replace(before, after, 1)
        assert changed != source
        try:
            contract(*changed)
        except (AssertionError, StopIteration):
            continue
        raise AssertionError("source controls accepted an unsafe publication mutant")
    print("publication source/ABI contracts and 8 rejection controls pass; no ACL2 execution or startup-selection claim")


if __name__ == "__main__":
    main()
