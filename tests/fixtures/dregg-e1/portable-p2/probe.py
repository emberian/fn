"""Run the compiled fn/Mini portable boundary on the public E1 fixture.

This is a process/byte comparison harness. It derives no fn identity, signature
verdict, Mini receipt, or operation decision; the native images own those.
"""

import argparse
import json
import subprocess
import tempfile
from pathlib import Path


SOURCE_ID = "666e2f7375626a6563742f7631000101db8d0b5a12a710cbf1640087047eab7b685013c77082b9ecf6aa7e0340784a5c"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mini-host", type=Path, required=True)
    parser.add_argument("--origin-pin", type=Path, required=True)
    parser.add_argument("--fn-binary", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    fixture = Path(__file__).resolve().parent.parent
    public = Path(__file__).resolve().parent
    args.out.mkdir(parents=True, exist_ok=False)
    pin = {
        "fnBinary": str(args.fn_binary.resolve()),
        "mlPublicKey": str((fixture / "fn-ml-public.pem").resolve()),
        "principal": (fixture / "fn-principal.bin").read_bytes().hex(),
        "edPublicKey": (fixture / "fn-ed-public.bin").read_bytes().hex(),
        "mlPublicKeyHex": (public / "fn-ml-public.raw").read_bytes().hex(),
    }
    claim = json.loads((public / "source-claim.json").read_text())
    assert claim["sourceIdentity"] == SOURCE_ID
    carrier = (fixture / "signed.eml").read_bytes()
    results = []

    def run(name, *, changed_pin=None, changed_claim=None,
            changed_carrier=None, changed_origin=None, expect=1):
        directory = args.out / name
        directory.mkdir()
        (directory / "pin.json").write_text(json.dumps(changed_pin or pin) + "\n")
        (directory / "claim.json").write_text(json.dumps(changed_claim or claim) + "\n")
        (directory / "carrier.eml").write_bytes(changed_carrier or carrier)
        source = directory / "source.bin"
        package = directory / "package.bin"
        result = directory / "result.json"
        proc = subprocess.run(
            [str(args.mini_host), str(changed_origin or args.origin_pin),
             "portable-verify-fn", str(directory / "pin.json"),
             str(directory / "claim.json"), str(directory / "carrier.eml"),
             str(source), str(package), str(result)],
            capture_output=True, text=True, check=False,
        )
        assert proc.returncode == expect, (name, proc.returncode, proc.stderr)
        if expect == 0:
            assert source.read_bytes() == (fixture / "source.eml").read_bytes()
            assert package.read_bytes() == (fixture / "package.bin").read_bytes()
            assert json.loads(result.read_text())["storeAdmission"] == "unestablished"
        else:
            assert not any(path.exists() for path in (source, package, result)), name
        results.append({"case": name, "exit": proc.returncode,
                        "stderr": proc.stderr.strip()})

    run("valid", expect=0)
    changed = dict(claim)
    changed["sourceIdentity"] = "00" * 48
    run("wrong-source-id", changed_claim=changed)
    changed = dict(claim)
    changed["messageId"] = "<other@example.invalid>"
    run("wrong-message-id", changed_claim=changed)
    changed = dict(claim)
    changed["groups"] = "fn.other"
    run("wrong-groups", changed_claim=changed)
    changed = dict(pin)
    changed["principal"] = "00" * 32
    run("wrong-principal", changed_pin=changed)
    changed = dict(pin)
    changed["edPublicKey"] = "00" * 32
    run("wrong-ed-key", changed_pin=changed)
    changed = dict(pin)
    changed["mlPublicKeyHex"] = "00" * 1952
    run("wrong-ml-key", changed_pin=changed)
    with tempfile.TemporaryDirectory(prefix="fn-p2-other-ml-") as temp:
        private = Path(temp) / "private.pem"
        public_key = Path(temp) / "public.pem"
        subprocess.run(["openssl", "genpkey", "-algorithm", "ML-DSA-65",
                        "-out", str(private)], check=True, capture_output=True)
        subprocess.run(["openssl", "pkey", "-in", str(private), "-pubout",
                        "-out", str(public_key)], check=True, capture_output=True)
        changed = dict(pin)
        changed["mlPublicKey"] = str(public_key)
        run("wrong-ml-pem", changed_pin=changed)
    changed = bytearray(carrier)
    body_start = changed.index(b"RFJFR0cv")
    changed[body_start] = ord("S")
    run("changed-authored-source", changed_carrier=bytes(changed))
    changed = json.loads(args.origin_pin.read_text())
    changed["domain"] += 1
    other_pin = args.out / "wrong-origin-pin.json"
    other_pin.write_text(json.dumps(changed) + "\n")
    run("wrong-mini-origin-pin", changed_origin=other_pin)
    changed = dict(claim)
    changed["storeAdmission"] = "verified"
    run("untrusted-store-claim", changed_claim=changed)
    oversized = args.out / "oversize-verifier.sh"
    oversized.write_text(
        "#!/bin/sh\n"
        "python3 -c 'import sys; sys.stdout.write(\"x\"*70002); "
        "sys.stdout.flush()'\n"
        "sleep 5\n"
    )
    oversized.chmod(0o700)
    changed = dict(pin)
    changed["fnBinary"] = str(oversized)
    run("oversize-verifier-output", changed_pin=changed)
    (args.out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"portable E1: {len(results)} cases passed")


if __name__ == "__main__":
    main()
