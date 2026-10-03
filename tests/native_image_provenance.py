"""Source coordinates for a composed fixture using published native images.

The runner verifies image_set SHA256SUMS before invoking the fixture.  This
check binds each selected launcher to that published set and compares source
coordinates; it does not certify images or rehash their large cores per case.
"""

import hashlib
import json
import os
from pathlib import Path
import re


def _published_source(image):
    launcher = Path(image).resolve(strict=True)
    directory = launcher.parent
    manifest_path = directory / "MANIFEST.json"
    manifest = json.loads(manifest_path.read_text())
    source = manifest.get("sha")
    if not isinstance(source, str) or not re.fullmatch(r"[0-9a-f]{40}", source):
        raise ValueError(f"{manifest_path}: no immutable source commit")
    if (directory / "TREE_SHA").read_text().strip() != source:
        raise ValueError(f"{directory}: TREE_SHA differs from manifest source")
    entries = [entry for entry in manifest.get("images", {}).values()
               if entry.get("launcher") == launcher.name]
    if len(entries) != 1:
        raise ValueError(f"{launcher}: not exactly one published image entry")
    core_name = entries[0].get("core")
    if not isinstance(core_name, str) or Path(core_name).name != core_name:
        raise ValueError(f"{launcher}: invalid published core path")
    core = directory / core_name
    if not core.is_file() or core.resolve().parent != directory:
        raise ValueError(f"{launcher}: published core missing or outside set")
    digest = hashlib.sha256(launcher.read_bytes()).hexdigest()
    if manifest.get("files", {}).get(launcher.name) != digest:
        raise ValueError(f"{launcher}: launcher differs from published manifest")
    return source


def assert_same_published_source(case, *images):
    """Require a same-source published NNTP/BP image pair before mutation.

    Symlinked launchers are resolved to their actual sets.  Environment labels
    alone do not establish the pair's source.  Missing/unpublished launchers,
    inconsistent manifests and mixed source commits fail the fixture.  The
    returned source commit is suitable for its observation record.
    """
    case.assertGreaterEqual(len(images), 2, "a composed fixture needs an image pair")
    try:
        sources = [_published_source(image) for image in images]
    except (OSError, ValueError, TypeError, AttributeError) as error:
        case.fail(f"composed native image source unavailable: {error}")
    case.assertEqual(len(set(sources)), 1,
                     f"composed native images have different source commits: {sources}")
    return sources[0]


def _digest(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def _execution_source(image, binding):
    """Validate the inputs actually reloaded by an initialized source process.

    The fixture supplies an explicit launcher/manifest binding, rather than
    inferring current source from a mutable checkout or an old core's version.
    This is an execution coordinate and confers no image qualification.
    """
    launcher = Path(image).resolve(strict=True)
    if _digest(launcher) != binding["launcher_sha256"]:
        raise ValueError(f"{launcher}: source launcher changed")
    manifest_path = Path(binding["manifest"]).resolve(strict=True)
    manifest_digest = _digest(manifest_path)
    if manifest_digest != binding["manifest_sha256"]:
        raise ValueError(f"{manifest_path}: source execution manifest changed")
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != "fn-native-source-runner-v1":
        raise ValueError(f"{manifest_path}: unsupported source execution schema")
    for field in ("source_revision", "world_revision"):
        if not re.fullmatch(r"[0-9a-f]{40}", manifest.get(field, "")):
            raise ValueError(f"{manifest_path}: missing immutable {field}")
    hashes = manifest.get("execution_sha256")
    if not isinstance(hashes, dict) or not hashes:
        raise ValueError(f"{manifest_path}: missing loaded execution hashes")
    required = [manifest["execution_core"], manifest["sbcl"],
                *manifest.get("raw_overlays", ()),
                *manifest.get("logical_files", ())]
    if manifest.get("logical_files"):
        required.append(manifest["source_loader"])
    for path in required:
        if str(Path(path).resolve()) not in hashes:
            raise ValueError(f"{manifest_path}: loaded input not bound: {path}")
    for path, expected in hashes.items():
        if not re.fullmatch(r"[0-9a-f]{64}", expected) or _digest(path) != expected:
            raise ValueError(f"{manifest_path}: loaded execution input changed: {path}")
    return manifest["source_revision"], manifest_digest


def assert_same_native_source(case, *images):
    """Require one exact source execution, or the existing published pair.

    FN_NATIVE_SOURCE_EXECUTIONS is a JSON object keyed by resolved launcher
    path. Each value names manifest, manifest_sha256 and launcher_sha256.
    All composed launchers must use the same execution manifest bytes. The
    absence of this explicit binding retains the published-image check.
    """
    encoded = os.environ.get("FN_NATIVE_SOURCE_EXECUTIONS")
    if encoded is None:
        return assert_same_published_source(case, *images)
    case.assertGreaterEqual(len(images), 2, "a composed fixture needs a producer/consumer pair")
    try:
        bindings = json.loads(encoded)
        coordinates = {}
        for image in images:
            path = str(Path(image).resolve(strict=True))
            if path not in coordinates:
                coordinates[path] = _execution_source(path, bindings[path])
    except (OSError, ValueError, TypeError, AttributeError, KeyError) as error:
        case.fail(f"composed native source execution unavailable: {error}")
    case.assertEqual(len(set(coordinates.values())), 1,
                     f"composed native processes load different executions: {coordinates}")
    return next(iter(coordinates.values()))[0]
