"""Cross-image pre-stamp checkpoint and selected-pack migration probe.

Run with FN_PRE_T2_IMAGE and FN_T2_IMAGE pointing to exact frozen developer
launchers. Stores live only in an isolated temporary directory under
FN_T2_PROBE_ROOT; this script never operates on a live node.
"""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tests.campaign import model_images


OLD = Path(os.environ["FN_PRE_T2_IMAGE"])
NEW = Path(os.environ["FN_T2_IMAGE"])
BASE = Path(os.environ["FN_T2_PROBE_ROOT"])


def call(image, *args, expected=0):
    result = subprocess.run([str(image), "--fn", *map(str, args)],
                            capture_output=True, text=True, timeout=60)
    print(image.name, " ".join(map(str, args)), "rc", result.returncode,
          "out", result.stdout.strip(), "err", result.stderr.strip())
    if result.returncode != expected:
        raise AssertionError("unexpected exit code")
    return result


def scenario(root, packed):
    payload = root.parent / "prior.art"
    payload.write_bytes(b"pre-T2 retained checkpoint article")
    call(OLD, "store", root, "init", "fn.letters")
    call(OLD, "store", root, "post", "<legacy-checkpoint@example.invalid>",
         payload, "-", "-", "fn.letters")
    if packed:
        call(OLD, "checkpoint", "pack", root, "select")
        suffix = root.parent / "suffix.art"
        suffix.write_bytes(b"pre-T2 retained suffix article")
        call(OLD, "store", root, "post", "<legacy-suffix@example.invalid>",
             suffix, "-", "-", "fn.letters")
        call(OLD, "checkpoint", "pack-reclaim", root)
    else:
        call(OLD, "checkpoint", "publish", root, "select")
    source = root.parent / (root.name + "-source")
    shutil.copytree(root, source)
    print("source transaction names", sorted(p.name for p in
                                              (source / "transactions").iterdir()))
    if not packed:
        frame = (source / "checkpoints" / "generation-0.fncp").read_bytes()
        bridge = model_images.ModelBridge()
        try:
            bridge.call('(include-book "books/checkpoint-codec")')
            bridge.call('(include-book "books/crypto-attach")')
            bridge.call('(include-book "books/codec-attach")')
            result = bridge.value(
                "(let* ((decoded (fn-cpc-frame-open '({}) '(\"fn.letters\")"
                " 1048576 1 1)))"
                " (list (fn-cpc-result-okp decoded)"
                " (fn-article-stamp (car (fn-state-articles"
                " (fn-node-acceptance (fn-checkpoint-node"
                " (fn-cpc-result-value decoded))))))))".format(
                    " ".join(map(str, frame))))
            print("ACL2 migrated selected checkpoint", result)
            assert "(T :LEGACY)" in result
        finally:
            bridge.close()
    recovered = call(NEW, "store", root, "recover")
    status = call(NEW, "checkpoint", "status", root)
    if packed:
        assert "transactions=2 articles=2" in recovered.stdout
        assert "checkpoint=none" in status.stdout
    else:
        assert "transactions=1 articles=1" in recovered.stdout
        assert "checkpoint=ok generation=0" in status.stdout
        assert "differential=equal" in status.stdout
    prior = call(NEW, "store", root, "inspect",
                 "<legacy-checkpoint@example.invalid>")
    assert prior.stdout.encode() == payload.read_bytes()
    if packed:
        suff = call(NEW, "store", root, "inspect",
                    "<legacy-suffix@example.invalid>")
        assert suff.stdout.encode() == suffix.read_bytes()


def main():
    assert OLD.is_file() and NEW.is_file()
    BASE.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="t2-checkpoint-", dir=BASE) as tmp:
        scratch = Path(tmp)
        scenario(scratch / "reclaimed", True)
        scenario(scratch / "selected", False)


if __name__ == "__main__":
    main()
