#!/usr/bin/env python3
"""Certify fn's local ACL2 books and retain machine-readable run evidence.

This runner deliberately requires a real ACL2 executable.  In particular, an
ACL2 process exiting zero is insufficient evidence: each requested book must
emit the success marker from the successful branch of `certify-book`, and the
log must not contain an ACL2 certification/error marker.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
BUILD_ROOT = ROOT / "build" / "acl2"
SUCCESS_PREFIX = "FN_CERTIFY_SUCCESS "
FAILURE_MARKERS = (
    "CERTIFICATION FAILED",
    "ACL2 Error",
    "HARD ACL2 ERROR",
)
BOOK_NAME = re.compile(r"(?:books|tests/acl2)/(?:[A-Za-z0-9_-]+/)*[A-Za-z0-9_-]+$")
DEFAULT_BOOKS = (
    "books/acceptance",
    "tests/acl2/acceptance-tests",
    "books/wire",
    "tests/acl2/wire-tests",
    "books/cbor",
    "tests/acl2/cbor-tests",
    "books/retention",
    "tests/acl2/retention-tests",
)
INCLUDE_BOOK = re.compile(r'\(\s*include-book\s+"([^"\\]+)"([^)]*)\)', re.IGNORECASE)


def digest(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def resolve_executable(value: str) -> Path | None:
    candidate = Path(value).expanduser()
    if os.sep in value:
        return candidate.resolve() if candidate.is_file() else None
    found = shutil.which(value)
    return Path(found).resolve() if found else None


def book_source(book: str) -> Path:
    source = (ROOT / f"{book}.lisp").resolve()
    if not source.is_relative_to(ROOT) or not source.is_file():
        raise ValueError(f"missing requested source book: {book}.lisp")
    return source


def local_include_books(book: str, source: Path) -> list[str]:
    dependencies: list[str] = []
    for match in INCLUDE_BOOK.finditer(source.read_text(encoding="utf-8")):
        reference, suffix = match.groups()
        # :dir selects an ACL2 system/project book, which is outside the local
        # source closure.  A bare include-book is local and must be pinned.
        if re.search(r"\b:dir\b", suffix, re.IGNORECASE):
            continue
        dependency_source = (source.parent / reference).with_suffix(".lisp").resolve()
        if not dependency_source.is_relative_to(ROOT):
            raise ValueError(f"local include-book escapes the repository: {reference} in {book}.lisp")
        if not dependency_source.is_file():
            raise ValueError(f"missing local include-book: {reference} in {book}.lisp")
        dependencies.append(dependency_source.relative_to(ROOT).with_suffix("").as_posix())
    return dependencies


def collect_book_sources(roots: list[str]) -> dict[str, str]:
    pending = list(roots)
    sources: dict[str, str] = {}
    while pending:
        book = pending.pop()
        if book in sources:
            continue
        source = book_source(book)
        sources[book] = digest(source)
        pending.extend(local_include_books(book, source))
    return {f"{book}.lisp": sources[book] for book in sorted(sources)}


def make_driver(book: str) -> str:
    # `certify-book` must run at the top level of an ACL2 ld.  On an error,
    # the inner ld returns before it reaches the marker; this catches ACL2
    # failures even when the surrounding process eventually exits zero.
    return f'''(ld '((certify-book "{book}" 0 t)
      (value-triple (cw "{SUCCESS_PREFIX}{book}~%")))
    :ld-error-action :return
    :ld-error-triples t)
(quit)
'''


def acl2_version_driver() -> str:
    return '''(ld '((value-triple (cw "FN_ACL2_VERSION ~s0~%" (@ acl2-version))))
    :ld-error-action :return
    :ld-error-triples t)
(quit)
'''


def run_acl2(
    executable: Path, driver: str, timeout_seconds: int
) -> subprocess.CompletedProcess[bytes]:
    environment = os.environ.copy()
    # A user customization can alter the ACL2 world before certification.  Do
    # not allow such ambient state into project evidence.
    environment["ACL2_CUSTOMIZATION"] = "NONE"
    environment.pop("ACL2_SYSTEM_BOOKS", None)
    return subprocess.run(
        [str(executable)],
        cwd=ROOT,
        input=driver.encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        env=environment,
        check=False,
        timeout=timeout_seconds,
    )


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def timeout_output(error: subprocess.TimeoutExpired) -> bytes:
    output = error.stdout or b""
    return output if isinstance(output, bytes) else output.encode("utf-8", errors="replace")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "books",
        nargs="*",
        default=list(DEFAULT_BOOKS),
        help=(
            "repository-relative ACL2 book names without .lisp "
            "(default: acceptance, wire, cbor, and retention books with their tests)"
        ),
    )
    parser.add_argument(
        "--timeout-seconds",
        type=int,
        default=int(os.environ.get("FN_ACL2_TIMEOUT_SECONDS", "600")),
        help="per-ACL2-invocation timeout in seconds (default: 600, or FN_ACL2_TIMEOUT_SECONDS)",
    )
    args = parser.parse_args()

    invalid = [book for book in args.books if not BOOK_NAME.fullmatch(book)]
    if invalid:
        parser.error(
            "book names must be repository-relative paths below books/ or tests/acl2/ "
            "without .lisp: " + ", ".join(invalid)
        )
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")

    configured = os.environ.get("FN_ACL2", "acl2")
    acl2 = resolve_executable(configured)
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run_dir = BUILD_ROOT / f"certify-{stamp}-{os.getpid()}"
    run_dir.mkdir(parents=True, exist_ok=False)

    manifest: dict[str, Any] = {
        "command": [configured],
        "environment": {"ACL2_CUSTOMIZATION": "NONE", "ACL2_SYSTEM_BOOKS": None},
        "platform": platform.platform(),
        "python": platform.python_version(),
        "requested_books": args.books,
        "timeout_seconds": args.timeout_seconds,
        "runner_sha256": digest(Path(__file__).resolve()),
        "status": "failed",
    }

    if acl2 is None or not os.access(acl2, os.X_OK):
        manifest["failure"] = (
            "ACL2 executable is unavailable. Install the pinned project toolchain "
            "or set FN_ACL2 to an executable ACL2 path."
        )
        write_json(run_dir / "manifest.json", manifest)
        print(manifest["failure"], file=sys.stderr)
        print(f"Certification evidence: {run_dir.relative_to(ROOT)}", file=sys.stderr)
        return 2

    try:
        source_digests = collect_book_sources(args.books)
    except ValueError as error:
        manifest["acl2_executable"] = str(acl2)
        manifest["acl2_executable_sha256"] = digest(acl2)
        manifest["failure"] = str(error)
        write_json(run_dir / "manifest.json", manifest)
        print(manifest["failure"], file=sys.stderr)
        print(f"Certification evidence: {run_dir.relative_to(ROOT)}", file=sys.stderr)
        return 2
    manifest["source_digests_sha256"] = source_digests

    manifest["acl2_executable"] = str(acl2)
    manifest["acl2_executable_sha256"] = digest(acl2)
    try:
        version_result = run_acl2(acl2, acl2_version_driver(), args.timeout_seconds)
    except subprocess.TimeoutExpired as error:
        (run_dir / "version.log").write_bytes(timeout_output(error))
        manifest["failure"] = f"ACL2 version probe timed out after {args.timeout_seconds} seconds."
        write_json(run_dir / "manifest.json", manifest)
        print(manifest["failure"], file=sys.stderr)
        print(f"Certification evidence: {run_dir.relative_to(ROOT)}", file=sys.stderr)
        return 1
    version_log = version_result.stdout.decode("utf-8", errors="replace")
    (run_dir / "version.log").write_text(version_log, encoding="utf-8")
    version_lines = [
        line.split("FN_ACL2_VERSION ", 1)[1]
        for line in version_log.splitlines()
        if "FN_ACL2_VERSION " in line
    ]
    manifest["acl2_version"] = version_lines[-1] if version_lines else None
    host_lisp_lines = [line.strip() for line in version_log.splitlines() if line.startswith("This is ")]
    manifest["host_lisp_banner"] = host_lisp_lines[0] if host_lisp_lines else None
    manifest["acl2_version_probe_exit_code"] = version_result.returncode

    log_parts: list[str] = []
    markers: list[str] = []
    exit_codes: dict[str, int | str] = {}
    driver_digests: dict[str, str] = {}
    for book in args.books:
        driver = make_driver(book)
        driver_path = run_dir / (Path(book).name + ".certify.lsp")
        driver_path.write_text(driver, encoding="utf-8")
        driver_digests[book] = digest(driver_path)
        try:
            result = run_acl2(acl2, driver, args.timeout_seconds)
            output = result.stdout.decode("utf-8", errors="replace")
            exit_codes[book] = result.returncode
        except subprocess.TimeoutExpired as error:
            output_bytes = timeout_output(error)
            output = output_bytes.decode("utf-8", errors="replace")
            exit_codes[book] = f"timed out after {args.timeout_seconds} seconds"
        (run_dir / (Path(book).name + ".certify.log")).write_text(output, encoding="utf-8")
        log_parts.append(output)
        markers.extend(
            SUCCESS_PREFIX + line.split(SUCCESS_PREFIX, 1)[1].strip()
            for line in output.splitlines()
            if SUCCESS_PREFIX in line
        )

    combined_log = "\n".join(log_parts)
    (run_dir / "certify.log").write_text(combined_log, encoding="utf-8")
    expected_markers = [SUCCESS_PREFIX + book for book in args.books]
    marker_ok = markers == expected_markers
    found_failures = [marker for marker in FAILURE_MARKERS if marker in combined_log]
    certificates = {
        book: digest(ROOT / f"{book}.cert")
        for book in args.books
        if (ROOT / f"{book}.cert").is_file()
    }
    certificates_ok = len(certificates) == len(args.books)
    try:
        source_digests_after = collect_book_sources(args.books)
    except ValueError as error:
        source_digests_after = {"closure-error": str(error)}
    sources_unchanged = source_digests_after == manifest["source_digests_sha256"]
    manifest.update(
        {
            "acl2_exit_codes": exit_codes,
            "expected_success_markers": expected_markers,
            "observed_success_markers": markers,
            "failure_markers": found_failures,
            "driver_digests_sha256": driver_digests,
            "certificate_digests_sha256": certificates,
            "source_digests_sha256_after": source_digests_after,
        }
    )
    success = (
        version_result.returncode == 0
        and manifest["acl2_version"] is not None
        and all(code == 0 for code in exit_codes.values())
        and marker_ok
        and certificates_ok
        and sources_unchanged
        and not found_failures
    )
    if success:
        manifest["status"] = "passed"
    else:
        manifest["failure"] = "ACL2 did not produce complete clean certification evidence. See certify.log."
    write_json(run_dir / "manifest.json", manifest)

    if not success:
        print(manifest["failure"], file=sys.stderr)
        print(f"Certification evidence: {run_dir.relative_to(ROOT)}", file=sys.stderr)
        return 1

    print("ACL2 certification passed: " + ", ".join(args.books))
    print(f"Certification evidence: {run_dir.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
