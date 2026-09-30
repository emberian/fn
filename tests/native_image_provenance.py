"""Source coordinates for a composed fixture using published native images.

The runner verifies image_set SHA256SUMS before invoking the fixture.  This
check binds each selected launcher to that published set and compares source
coordinates; it does not certify images or rehash their large cores per case.
"""

import hashlib
import json
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
