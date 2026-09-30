#!/usr/bin/env python3
"""Emit an identity binding from existing product artifacts and capsule export.

This does not produce a capsule, qualify units, or attest compilation. The
builder must supply the export from the same compiled installation. Capture
the emitted digest in trusted installer metadata outside the mutable package.
"""
import argparse
import json
import os
from pathlib import Path
import sys
import tempfile

import bound_launch


def assignments(items):
    result = {}
    for item in items:
        key, separator, value = item.partition("=")
        if not separator or not key or key in result:
            raise bound_launch.BindingError("invalid or duplicate selector assignment")
        result[key] = value
    return result


def emit_binding(output, artifacts, environment, libraries):
    """Validate before publishing; exclusive creation never replaces a binding."""
    output = Path(output).absolute()
    if output.exists() or output.is_symlink():
        raise bound_launch.BindingError("output binding already exists")
    if set(artifacts) != bound_launch.ROLES:
        raise bound_launch.BindingError("all six existing artifacts are required")
    records = {}
    for role, raw_path in artifacts.items():
        path = Path(raw_path).resolve(strict=True)
        records[role] = {"path": str(path), "sha256": bound_launch.digest(path)}
    # The validator checks these same bytes again before the output appears.
    launcher = bound_launch.checked_bytes(Path(records["launcher"]["path"]),
                                           records["launcher"]["sha256"]).decode()
    _, _, _, geometry, _ = bound_launch.parse_launcher(launcher)
    binding = {"schema": 1, "artifacts": records, "options": geometry}
    if environment:
        binding["environment"] = environment
    if libraries:
        binding["foreign_libraries"] = {}
        for selector, raw_path in libraries.items():
            path = Path(raw_path).resolve(strict=True)
            binding["foreign_libraries"][selector] = {
                "path": str(path), "sha256": bound_launch.digest(path)}
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8",
                                         dir=output.parent, prefix=".fn-binding-",
                                         delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(json.dumps(binding, sort_keys=True, indent=2) + "\n")
            stream.flush()
            os.fsync(stream.fileno())
        pin = bound_launch.digest(temporary)
        # Build environments may have unrelated FN/allocator settings. They
        # are not the launch environment; only explicit selectors are bound.
        bound_launch.resolve_plan(temporary, pin, environment={})
        # Same-directory hard link publishes the fully validated bytes and
        # refuses even a racing creator. No overwrite or partial target file.
        os.link(temporary, output)
        return {"binding": str(output), "sha256": pin,
                "identity": "matched", "qualification": "not-established"}
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    for role in sorted(bound_launch.ROLES):
        parser.add_argument("--" + role.replace("_", "-"), type=Path, required=True)
    parser.add_argument("--environment", action="append", default=[], metavar="FN_NAME=VALUE")
    parser.add_argument("--library", action="append", default=[], metavar="FN_NAME_LIBRARY=PATH")
    args = parser.parse_args()
    try:
        result = emit_binding(args.output,
                              {role: getattr(args, role) for role in bound_launch.ROLES},
                              assignments(args.environment), assignments(args.library))
        print(json.dumps(result))
        return 0
    except (bound_launch.BindingError, OSError, ValueError, KeyError, TypeError) as error:
        print("package binding refused: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
