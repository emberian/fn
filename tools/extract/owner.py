#!/usr/bin/env python3
"""E1: real owner completion after its barrier stall deadline, image vs core.

Run IMAGE CORE OUT. Both developer executables receive the same request and
stall/un-stall ordering. Compare wire replies and durable reads, not elapsed
clock readings (each side records those separately). A timed-out POST must be
uncertain and close exactly once while the device is still held; after the
late completion its article must survive a restart. No skips count as passes.
This complements stateful.py's offline crash/restart cases; it does not claim
all scheduler interleavings or replace the production-profile qualification.
"""
import hashlib
import json
import re
from pathlib import Path
import socket
import sys
import time
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tests.native_harness import Node, executable  # noqa: E402

CASE = "stalled-owner-late-completion"
OBSERVATIONS = ("uncertain", "closed", "stored", "body", "next_post", "restart_stored", "restart_body")


def fingerprint(program):
    """Pin executable bytes, the reference core/runtime, and adjacent FFI files.

    The source marker is a claim from the build, not inferred from a mutable
    scratch directory's name. Missing markers remain explicitly unknown.
    """
    paths = [program]
    with program.open("rb") as stream:
        header = stream.read(16384)
    if header.startswith(b"#!"):
        text = header.decode("utf-8")
        cores = re.findall(r'--core "([^"\n]+)"', text)
        runtimes = re.findall(r'^exec "([^"\n]+)"', text, re.M)
        if len(cores) != 1 or len(runtimes) != 1:
            raise AssertionError("reference launcher must name one core and runtime")
        def resolve_reference(value):
            if value.startswith("$here/"):
                return program.parent / value[len("$here/"):]
            path = Path(value)
            if not path.is_absolute():
                raise AssertionError("unsupported relative product reference: " + value)
            return path
        paths += [resolve_reference(cores[0]), resolve_reference(runtimes[0])]
    library_dir = program.parent / "lib"
    if library_dir.is_dir():
        paths += sorted(path for path in library_dir.iterdir() if path.is_file())
    artifacts = {}
    for path in paths:
        digest = hashlib.sha256()
        with path.open("rb") as stream:
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(block)
        artifacts[str(path)] = digest.hexdigest()
    marker = program.parent / "source-revision"
    return {"artifacts": artifacts,
            "build_source_marker": marker.read_text().strip() if marker.is_file() else None,
            "source_provenance": "build marker only" if marker.is_file() else "unknown"}


def exercise(image, directory):
    case = unittest.TestCase()
    node = Node(case, image, root=directory, env={"FN_NATIVE_TEST_CLOCK": "73000:1759000000:250000",
                                               "FN_NATIVE_TEST_ENTROPY": "17"})
    stall = node.root / "stall"
    case.addCleanup(lambda: stall.unlink(missing_ok=True))
    trace = {}
    timings = {}

    def connect():
        conn = socket.create_connection(("127.0.0.1", node.port), timeout=60)
        stream = conn.makefile("rwb")
        case.addCleanup(conn.close)
        case.addCleanup(stream.close)
        case.assertTrue(stream.readline().startswith(b"200"))
        return conn, stream

    def command(stream, line):
        stream.write(line + b"\r\n")
        stream.flush()
        return stream.readline()

    def post(stream, message_id):
        case.assertTrue(command(stream, b"POST").startswith(b"340"))
        stream.write(b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                     b"Subject: extraction late completion\r\nMessage-ID: <" + message_id
                     + b">\r\n\r\nlate completion body\r\n.\r\n")
        stream.flush()

    def inspect(stream, prefix):
        stat = command(stream, b"STAT <extract-late@example.invalid>")
        case.assertTrue(stat.startswith(b"223"), stat)
        trace[prefix + "stored"] = stat.hex()
        first = command(stream, b"BODY <extract-late@example.invalid>")
        case.assertTrue(first.startswith(b"222"), first)
        body = bytearray(first)
        for _ in range(16):
            line = stream.readline()
            case.assertTrue(line, "body ended before its terminator")
            body.extend(line)
            if line == b".\r\n":
                break
        else:
            case.fail("unexpectedly long body")
        case.assertIn(b"late completion body\r\n", body)
        trace[prefix + "body"] = bytes(body).hex()

    try:
        node.operator("init", "--profile", "default", "--max-article-octets", "65536", "fn.test", expect=0)
        node.start(env={"FN_NATIVE_TEST_DISK_STALL_FILE": str(stall)})
        for name, value in (("barrier-deadline-ms", "2000"), ("barrier-stall-ms", "6000"),
                            ("clock-event-ms", "250")):
            node.operator("policy", "set", name, value, expect=0)
        _, warm = connect()
        post(warm, b"extract-warm@example.invalid")
        case.assertTrue(warm.readline().startswith(b"240"))
        conn, writer = connect()
        stall.touch()
        started = time.monotonic()
        post(writer, b"extract-late@example.invalid")
        conn.settimeout(30)
        uncertain = writer.readline()
        timings["uncertain_seconds"] = time.monotonic() - started
        case.assertTrue(uncertain.startswith(b"441"), uncertain)
        case.assertIn(b"uncertain", uncertain.lower())
        case.assertNotIn(b"try again later", uncertain)
        case.assertEqual(writer.readline(), b"", "uncertain poster received another reply")
        case.assertTrue(stall.exists(), "device must still be stalled at the timeout")
        health = node.operator("health")
        case.assertEqual(health.returncode, 28, (health.stdout, health.stderr))
        case.assertIn(b"disk stalled: barrier", health.stdout)
        trace["uncertain"], trace["closed"] = uncertain.hex(), True
        stall.unlink()
        deadline = time.monotonic() + 60
        while True:
            health = node.operator("health")
            if health.returncode == 0 and b"disk ok:" in health.stdout:
                break
            case.assertLess(time.monotonic(), deadline, (health.stdout, health.stderr))
            time.sleep(0.1)
        timings["completed_seconds"] = time.monotonic() - started
        _, reader = connect()
        inspect(reader, "")
        post(warm, b"extract-after@example.invalid")
        after = warm.readline()
        case.assertTrue(after.startswith(b"240"), after)
        trace["next_post"] = after.hex()
        for stream in (warm, reader):
            case.assertTrue(command(stream, b"QUIT").startswith(b"205"))
        node.stop()
        node.start()
        _, reopened = connect()
        inspect(reopened, "restart_")
        case.assertTrue(command(reopened, b"QUIT").startswith(b"205"))
        node.stop()
        case.assertEqual(set(trace), set(OBSERVATIONS))
        return {"observations": trace, "timings": timings}
    finally:
        stall.unlink(missing_ok=True)
        cleaned = case.doCleanups()
        for index, process in enumerate(node.processes):
            (directory / ("owner-%d.stderr" % index)).write_bytes(process.stderr.since(0))
        if not cleaned:
            raise AssertionError("owner cleanup failed")


def main(argv):
    if len(argv) != 4:
        raise SystemExit("owner.py IMAGE CORE OUT")
    image, core, out = Path(argv[1]).absolute(), Path(argv[2]).absolute(), Path(argv[3])
    out.mkdir(parents=True, exist_ok=False)
    report = {"status": "RUNNING", "case": CASE, "observations_expected": list(OBSERVATIONS), "sides": {}}
    def save():
        (out / "owner.json").write_text(json.dumps(report, indent=2) + "\n")
    save()
    try:
        report["products_before"] = {label: fingerprint(program)
                                     for label, program in (("image", image), ("core", core))}
        save()
        for label, program in (("image", image), ("core", core)):
            if not executable(program):
                raise AssertionError("missing executable: %s" % program)
            report["sides"][label] = exercise(program, out / label)
            save()
        if report["sides"]["image"]["observations"] != report["sides"]["core"]["observations"]:
            raise AssertionError("owner replies or durable reads differ")
        report["products_after"] = {label: fingerprint(program)
                                    for label, program in (("image", image), ("core", core))}
        if report["products_before"] != report["products_after"]:
            raise AssertionError("product bytes changed during the differential")
        report["status"] = "PASS"
    except Exception as ex:
        report.update(status="FAIL", reason=repr(ex))
    save()
    print("owner: %s %s%s" % (report["status"], CASE, ": " + report["reason"] if "reason" in report else ""))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
