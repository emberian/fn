#!/usr/bin/env python3
"""Launch the native host image with the Python hosts' command-line surface.

`build/fn-host` (tools/build_native_host.sh) is one SBCL image holding ACL2,
the certified books and host/native/io.lisp.  This launcher validates the
command line with exactly the parsers tools/run_store.py and tools/run_reader.py
use, then replaces itself with the image, so exit codes and usage errors are the
image's or the shared parser's, never a second table.

    python3 tools/fn_native.py store --store DIR init|post|recover|status|config|inspect ...
    python3 tools/fn_native.py reader --port N [--once] [--store DIR]
    python3 tools/fn_native.py sha256-selftest

With `FN_HOST=native` in the environment, `tools/run_store.py` and
`tools/run_reader.py` delegate here after parsing, so the existing tests run
against either host without edits.  `FN_NATIVE_HOST` overrides the image path.
"""
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
IMAGE = ROOT / "build" / "fn-host"
EXIT_USAGE = 5


def image_path():
    return Path(os.environ.get("FN_NATIVE_HOST", str(IMAGE)))


def image_environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    return env


def launch(protocol):
    """Replace this process with the image; returns only when it cannot."""
    image = image_path()
    if not os.access(image, os.X_OK):
        print("fn_native: native host image missing: {} (run tools/build_native_host.sh)"
              .format(image), file=sys.stderr)
        return EXIT_USAGE
    sys.stdout.flush()
    sys.stderr.flush()
    os.execve(str(image), [str(image), "--fn", *protocol], image_environment())


def store_protocol(args):
    """run_store's parsed arguments as the image's positional protocol."""
    root = str(args.store)
    if args.command == "post":
        args.message_id.encode("ascii")
        return ["store", root, "post", args.message_id, str(args.payload),
                "-" if args.charge is None else str(args.charge),
                args.inject_fault or "-", *args.group]
    if args.command == "inspect":
        # run_store encodes this one after opening the store; the image does too.
        if getattr(args, "provenance", False):
            # The image has no provenance surface yet.  Say so rather than
            # dropping the flag and printing the payload as if it had been
            # asked for (w10/provenance; the seam is fn-store-prov-for-msgid).
            raise ValueError("the native image does not implement "
                             "`inspect --provenance` yet")
        return ["store", root, "inspect", args.message_id]
    if args.command == "init":
        # The groups of the store's first configuration record.  The image
        # holds no default table: it passes these names to the core, which
        # builds and admits generation 1 from them.
        return ["store", root, "init", *(args.group or [])]
    return ["store", root, args.command]


def reader_protocol(args):
    return ["reader", str(args.port), "1" if args.once else "0",
            str(args.store) if args.store else "-"]


def exec_store(args):
    return launch(store_protocol(args))


def exec_reader(args):
    return launch(reader_protocol(args))


def sha256_selftest():
    """Compare the image's SHA-256 with hashlib on standard and random vectors."""
    vectors = [b"", b"abc", b"a" * 1000000,
               b"The quick brown fox jumps over the lazy dog",
               os.urandom(55), os.urandom(56), os.urandom(64), os.urandom(65),
               os.urandom(65538), os.urandom(200001)]
    failures = 0
    with tempfile.TemporaryDirectory(prefix="fn-sha256-") as temporary:
        for index, data in enumerate(vectors):
            path = Path(temporary) / "v{}".format(index)
            path.write_bytes(data)
            result = subprocess.run([str(image_path()), "--fn", "sha256", str(path)],
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    env=image_environment(), check=False)
            expected = hashlib.sha256(data).hexdigest()
            actual = result.stdout.decode("ascii", "replace").strip()
            status = "ok" if (result.returncode == 0 and actual == expected) else "MISMATCH"
            failures += status != "ok"
            print("sha256 len={:<7d} {} {}".format(len(data), status, expected))
    return 1 if failures else 0


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv and argv[0] == "sha256-selftest":
        return sha256_selftest()
    if argv and argv[0] in ("store", "reader"):
        os.environ["FN_HOST"] = "native"
        sys.path.insert(0, str(ROOT / "tools"))
        if argv[0] == "store":
            import run_store
            return run_store.main(argv[1:])
        import run_reader
        sys.argv = [sys.argv[0], *argv[1:]]
        return run_reader.main()
    print(__doc__, file=sys.stderr)
    return EXIT_USAGE


if __name__ == "__main__":
    sys.exit(main())
