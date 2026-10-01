#!/usr/bin/env python3
"""Independent cbor2 vectors for the explicit fn commit codec v2 component.

Not a native, authenticated transport, or universal CBOR conformance verdict.
Only generated decimal data and fixed test forms enter ACL2. Peer bytes never
become executable forms. Run with the optional cbor2 dependency installed.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import importlib.metadata
import io
import json
from pathlib import Path
import platform
import re
import subprocess
import sys

import cbor2

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def octets(value):
    return "(" + " ".join(map(str, value)) + ")"


def sequence(values):
    wire = b"".join(cbor2.dumps(v, canonical=True) for v in values)
    stream = io.BytesIO(wire)
    decoder = cbor2.CBORDecoder(stream)
    assert [decoder.decode() for _ in values] == values
    assert stream.tell() == len(wire)
    return wire


def fixtures():
    # The five-field grammar/opcodes come from the profile, not fn's encoder.
    for base in (0, 23, 24, 255, 256, 65535, 65536, 2**32-1, 2**32, 2**64-1):
        for op, name in enumerate((":add", ":remove", ":rotate")):
            yield f"base-{base}-{name[1:]}", [b"\x00\xff", base, b"actor", op, b"subject"], name
    for size in (0, 1, 23, 24, 255, 256, 512, 513, 65535, 65536):
        data = bytes(i % 256 for i in range(size))
        yield f"length-{size}", [data, 2**32, b"a", 2, b"s"], ":rotate"


HELPERS = r'''
(in-package "ACL2")
(include-book "books/substrate-commit-profile-codec")
(defun interop-stcp-run (encode p c rounds)
 (declare (xargs :mode :program))
 (if (fn-stcp-terminalp c)
  (mv-let (again used)
   (if encode (fn-stcp-encode-resume p c) (fn-stcp-decode-resume p c))
   (if (and (equal again c) (equal used 0))
    (if encode (fn-stcp-enc-result c) (fn-stcp-dec-result c))
    '(:harness-error :terminal-instability)))
  (if (zp rounds) '(:harness-error :nontermination)
   (mv-let (next used)
    (if encode (fn-stcp-encode-resume p c) (fn-stcp-decode-resume p c))
    (if (and (natp used) (< 0 used) (<= used (nth 3 p)))
     (interop-stcp-run encode p next (1- rounds))
     '(:harness-error :quantum))))))
'''


def driver():
    forms = [HELPERS]
    cases = []

    def check(name, condition):
        ident = len(cases)
        cases.append({"id": ident, "name": name})
        forms.append(f'(assert-event (if {condition} '
                     f'(prog2$ (cw "~%STCP-CBOR2-PASS {ident}~%") t) nil))')

    def run(encode, p, data, rounds):
        start = "encode" if encode else "decode"
        return (f"(interop-stcp-run {'t' if encode else 'nil'} {p} "
                f"(fn-stcp-{start}-start {p} {data}) {rounds})")

    for name, values, op in fixtures():
        wire = sequence(values)
        commit = f"(:fn-me-commit {octets(values[0])} {values[1]} {octets(values[2])} {op} {octets(values[4])})"
        # Large fixtures still exercise repeated yields, without huge q=1 logs.
        for quantum in ((1, 17, 64) if len(wire) < 2000 else (17, 64)):
            p = f"'(:fn-stcp-v2 {len(wire)} {max(map(len, (values[0], values[2], values[4])))} {quantum})"
            rounds = 5 * len(wire) + 100
            check(f"{name}/q{quantum}/encode", f"(equal {run(True,p,chr(39)+commit,rounds)} '(:ok {octets(wire)}))")
            for borrowed in (False, True):
                source = "'" + octets(wire)
                if borrowed:
                    source = f"(fn-record-octets-string {source})"
                check(f"{name}/q{quantum}/decode-{'string' if borrowed else 'list'}",
                      f"(equal {run(False,p,source,rounds)} '(:ok {commit}))")

    good = sequence([b"i", 0, b"a", 0, b"s"])
    bad = [(f"truncated-{i}", good[:i], ":truncated") for i in range(len(good))]
    bad += [("trailing", good+b"\x00", ":trailing"),
            ("nonminimal-base", good[:2]+b"\x18\x00"+good[3:], ":noncanonical"),
            ("nonminimal-wide-base", good[:2]+b"\x1b"+bytes(8)+good[3:], ":noncanonical"),
            ("wrong-field-type", b"\x01"+good[2:], ":field"),
            ("unknown-op", sequence([b"i",0,b"a",3,b"s"]), ":op"),
            # Legal generic CBOR features deliberately outside this profile.
            ("indefinite-bytes", b"\x5f\x41i\xff"+good[2:], ":unsupported-format"),
            ("wide-bytes-head", b"\x5b"+bytes(7)+b"\x01i"+good[2:], ":unsupported-format")]
    for name, wire, reason in bad:
        for borrowed in (False, True):
            source = "'" + octets(wire)
            if borrowed:
                source = f"(fn-record-octets-string {source})"
            result = run(False, "'(:fn-stcp-v2 100 100 1)", source, 1000)
            check(name+("/string" if borrowed else "/list"), f"(equal {result} '(:error {reason}))")
    for name, p, reason in (("wire-budget", f"'(:fn-stcp-v2 {len(good)-1} 10 17)", ":profile-limit"),
                            ("field-budget", "'(:fn-stcp-v2 100 0 17)", ":profile-limit"),
                            ("unsupported-field-width", "'(:fn-stcp-v2 100 4294967296 17)", ":unsupported-format"),
                            ("zero-quantum", "'(:fn-stcp-v2 100 10 0)", ":invalid-quantum")):
        for encode in (False, True):
            data = "'(:fn-me-commit (105) 0 (97) :add (115))" if encode else "'"+octets(good)
            check(name+("/encode" if encode else "/decode"), f"(equal {run(encode,p,data,1000)} '(:error {reason}))")
    forms.append('(good-bye)')
    return "\n".join(forms)+"\n", cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tree", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    tree = args.tree.resolve()
    args.output.mkdir(parents=True, exist_ok=False)
    sys.path.insert(0, str(tree / "tools"))
    import certs
    import acl2_slots
    closure = certs.closure(tree, "books/substrate-commit-profile-codec")
    sources = {name+".lisp": digest(tree/(name+".lisp")) for name in closure}
    text, cases = driver()
    source = args.output / "driver.lsp"
    source.write_text(text)
    log = args.output / "acl2.log"
    with source.open("rb") as inp, log.open("wb") as out:
        result = subprocess.run([sys.executable, str(tree/"tools/acl2"), "--timeout", "240"],
                                stdin=inp, stdout=out, stderr=subprocess.STDOUT, cwd=tree)
    output = log.read_text(errors="replace")
    passed = [int(n) for n in re.findall(r"^STCP-CBOR2-PASS (\d+)\s*$", output, re.M)]
    unchanged = all(digest(tree/p) == value for p, value in sources.items())
    ok = (result.returncode == 0 and passed == list(range(len(cases))) and unchanged
          and not re.search(r"ACL2 Error|HARD ACL2 ERROR|\*\*\*\* FAILED", output, re.I))
    report = {"status": "PASS" if ok else "FAIL", "scope": "source component execution; not native qualification",
              "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "tree": str(tree), "cbor2": importlib.metadata.version("cbor2"),
              "platform": platform.platform(), "python": sys.version,
              "acl2_launcher": acl2_slots.configured_acl2(),
              "acl2_version": re.findall(r"ACL2 Version ([^\s]+)", output),
              "certificate_sha256": {name+".cert": digest(tree/(name+".cert"))
                                     for name in closure if (tree/(name+".cert")).is_file()},
              "runner_tools_sha256": {name: digest(tree/name)
                                      for name in ("tools/acl2", "tools/acl2_slots.py")},
              "source_revision": subprocess.check_output(["git","rev-parse","HEAD"],cwd=tree,text=True).strip(),
              "source_sha256": sources, "sources_unchanged": unchanged,
              "driver_sha256": digest(source), "log_sha256": digest(log),
              "script_sha256": digest(Path(__file__)), "exit_code": result.returncode,
              "expected_checks": len(cases), "passed_checks": len(passed), "cases": cases}
    (args.output/"manifest.json").write_text(json.dumps(report, indent=2)+"\n")
    print(f"{report['status']}: {len(passed)}/{len(cases)} independent-vector checks; {args.output}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
