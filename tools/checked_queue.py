#!/usr/bin/env python3
"""Publish a checked script/data bundle to a consume-by-rename shell queue.

Manifest: {"argv": ["bash", "{retry}", "{candidate}"], "files": {
  "retry": {"path": "/tmp/retry.sh", "sha256": "..."},
  "candidate": {"path": "/tmp/candidate.lisp", "sha256": "..."}}}
Every dependency is explicit and passed by placeholder. Scripts must use those
arguments, never refer back to ephemeral queue/staging filenames. This is not a
shell/Python dependency scanner. Publication changes neither executor nor limits.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import sys
import tempfile

# Self-contained queue payload: no dependency on this tool's future pathname.
RUNNER = '''import hashlib,json,pathlib,subprocess,sys
bundle=pathlib.Path(sys.argv[1])
encoded=(bundle/'manifest.json').read_bytes()
if hashlib.sha256(encoded).hexdigest()!=bundle.name: raise SystemExit('bundle manifest SHA256 mismatch')
manifest=json.loads(encoded)
paths={}
for name,row in manifest['files'].items():
    artifact=bundle/row['file']
    if hashlib.sha256(artifact.read_bytes()).hexdigest()!=row['sha256']: raise SystemExit('artifact SHA256 mismatch: '+name)
    paths['{'+name+'}']=str(artifact)
argv=[paths.get(arg,arg) for arg in manifest['argv']]
sys.exit(subprocess.run(argv).returncode)
'''



def digest(data):
    return hashlib.sha256(data).hexdigest()


def prepare(manifest, bundles):
    """Verify all expected bytes before creating an immutable execution bundle."""
    argv = manifest['argv']
    files = manifest['files']
    if not isinstance(argv, list) or not argv or not all(isinstance(x, str) for x in argv):
        raise ValueError('argv must be a nonempty string list')
    executable = shutil.which(argv[0])
    if executable is None:
        raise ValueError('executable is unavailable: ' + argv[0])
    snapshots = {}
    rows = {}
    for name, row in files.items():
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_-]*', name):
            raise ValueError('invalid artifact name: ' + name)
        expected = row['sha256']
        if not isinstance(expected, str) or not re.fullmatch(r'[0-9a-f]{64}', expected):
            raise ValueError('expected SHA256 required: ' + name)
        data = Path(row['path']).read_bytes()  # missing/truncated copies fail before publication
        if digest(data) != expected:
            raise ValueError('artifact SHA256 mismatch: ' + name)
        snapshots[name] = data
        rows[name] = {'file': name, 'sha256': expected}
    placeholders = {'{' + name + '}' for name in files}
    referenced = {arg for arg in argv if arg.startswith('{') or arg.endswith('}')}
    if not files or referenced != placeholders or argv[0] in placeholders:
        raise ValueError('each declared artifact must be a standalone argv placeholder; no unknown placeholders')
    specification = {'argv': [executable, *argv[1:]], 'files': rows}
    encoded = json.dumps(specification, sort_keys=True).encode()
    bundles = Path(bundles).resolve()
    bundles.mkdir(mode=0o700, parents=True, exist_ok=True)
    if bundles.stat().st_mode & 0o077:
        raise ValueError('bundle root must be private (mode 0700)')
    bundle = bundles / digest(encoded)
    if not bundle.exists():
        ready = Path(tempfile.mkdtemp(prefix='.ready-', dir=bundles))
        try:
            for name, data in snapshots.items():
                path = ready / name
                with path.open('xb') as output:
                    output.write(data)
                    output.flush()
                    os.fsync(output.fileno())
                path.chmod(0o444)
            (ready / 'manifest.json').write_bytes(encoded)
            (ready / 'manifest.json').chmod(0o444)
            ready.chmod(0o555)
            try:
                ready.rename(bundle)
            except FileExistsError:
                pass  # another publisher prepared the identical content-addressed bundle
        finally:
            if ready.exists():
                ready.chmod(0o700)
                shutil.rmtree(ready)  # only this call's uniquely created private staging directory
    if (bundle / 'manifest.json').read_bytes() != encoded:
        raise ValueError('existing bundle manifest differs')
    for name, data in snapshots.items():
        if (bundle / name).read_bytes() != data:
            raise ValueError('existing bundle artifact differs: ' + name)
    return bundle


def publish(manifest, bundles, queue):
    queue = Path(queue)
    with queue.with_name('.' + queue.name + '.publisher.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if queue.exists():
            raise FileExistsError('a command is already queued: ' + str(queue))
        bundle = prepare(manifest, bundles)
        payload = ('#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' -c '
                   + shlex.quote(RUNNER) + ' ' + shlex.quote(str(bundle)) + '\n').encode()
        fd, temporary = tempfile.mkstemp(prefix='.' + queue.name + '-ready-', dir=queue.parent)
        ready = Path(temporary)
        try:
            with os.fdopen(fd, 'wb') as output:
                output.write(payload)
                output.flush()
                os.fsync(output.fileno())
            # Atomic no-clobber publication also protects against a writer
            # that does not participate in the single-publisher lock.
            os.link(ready, queue)
        finally:
            ready.unlink()  # this call's own staging pathname only
    return bundle


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path)
    parser.add_argument('--bundles', required=True, type=Path)
    parser.add_argument('--queue', required=True, type=Path)
    args = parser.parse_args()
    print(publish(json.loads(args.manifest.read_text()), args.bundles, args.queue))
