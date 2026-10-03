#!/usr/bin/env python3
"""Emit the current host/native build over an explicitly admitted source world.

Only includes named by the logical-world inventory are removed. Host definitions,
proofs, guards, declarations and raw installation retain their actual source
order; successful emission is not admission or native execution.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import proof_repl
from proof_repl import forms

LD = re.compile(r'^\(ld\s+"([^"\\]+)"', re.I)


def generate(source: Path, world_manifest: Path, output: Path,
             build='host/native/build.lisp') -> Path:
    source = source.resolve()
    world_manifest = world_manifest.resolve()
    world = json.loads(world_manifest.read_text())
    inventory = {name.removesuffix('.lisp') for name in world['repository_books']}
    admitted = {name.removesuffix('.lisp') for name in
                world.get('exported_books', world['repository_books'])}
    repository = world.get('repository_sha256', {})
    if Path(world['source']).resolve() != source and set(repository) != set(world['repository_books']):
        raise ValueError('different source roots require the complete logical source inventory')
    for name, expected in repository.items():
        path = (source / name).resolve()
        if not path.is_relative_to(source) or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError('host logical dependency differs from admitted source: ' + name)
    proof_repl.ROOT = source
    inputs = {str(world_manifest): hashlib.sha256(world_manifest.read_bytes()).hexdigest()}
    hosts = []
    active = set()

    def remember(path):
        inputs[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()

    def local_input(target):
        """A local proof input is not an exported rule from a cached parent."""
        expected = repository.get(target + '.lisp')
        recorded = world.get('inputs_sha256', {})
        for name, digest in recorded.items():
            path = Path(name)
            if not name.endswith('/' + target + '.lisp') or digest != expected:
                continue
            siblings = [path, path.with_suffix('.cert'), path.with_suffix('.port')]
            if not all(str(p) in recorded and p.is_file() for p in siblings):
                continue
            if not all(hashlib.sha256(p.read_bytes()).hexdigest() == recorded[str(p)] for p in siblings):
                raise ValueError('local proof input changed: ' + target)
            for suffix in ('.lisp', '.cert', '.port', '.fasl'):
                candidate = path.with_suffix(suffix)
                if str(candidate) in recorded:
                    if not candidate.is_file() or hashlib.sha256(candidate.read_bytes()).hexdigest() != recorded[str(candidate)]:
                        raise ValueError('local proof input changed: ' + target)
                    remember(candidate)
            return '(include-book ' + json.dumps(str(path.with_suffix(''))) + ')'
        raise ValueError('host proof dependency is not exported and has no bound cached input: ' + target)

    def transform(form, directory):
        match = re.match(r'^\(\s*([^\s()]+)', form)
        head = match.group(1).lower() if match else ''
        if head == 'in-package':
            if not re.fullmatch(r'\(in-package\s+"ACL2"\)', form, re.I):
                raise ValueError('host package needs explicit handling: ' + form)
            return ''
        if head == 'include-book':
            target = proof_repl.include_target(form, directory)
            if target not in inventory:
                raise ValueError('host include absent from admitted world: ' + form)
            return '' if target in admitted else local_input(target)
        if head == 'ld':
            match = LD.match(form)
            if not match:
                raise ValueError('nonliteral host LD needs explicit handling: ' + form)
            local = (directory / match.group(1)).resolve()
            path = local if local.is_file() else (source / match.group(1)).resolve()
            if not path.is_relative_to(source) or not path.is_file():
                raise ValueError('host LD outside current source: ' + form)
            return load_host(path)
        # Includes/LD may occur in embedded event lists, but quoted function
        # data and macro bodies are left byte-for-byte intact.
        if head in ('local', 'progn', 'encapsulate'):
            children = forms(form[1:-1])
            prefix = 2 if head == 'encapsulate' else 1
            kept = [transform(child, directory) for child in children[prefix:]]
            kept = [child for child in kept if child]
            return ('(' + '\n'.join(children[:prefix] + kept) + ')') if kept else ''
        return form

    def load_host(path):
        if path in active:
            raise ValueError('recursive host LD: ' + str(path))
        active.add(path)
        remember(path)
        hosts.append(str(path.relative_to(source)))
        body = [transform(form, path.parent) for form in forms(path.read_text())]
        active.remove(path)
        body = [form for form in body if form]
        # A newly needed nonlocal cached input must be outside encapsulate.
        # LOCAL wrappers stay inside, so proof-only rules never leak outward.
        hoisted = [form for form in body if LD.match(form) is None and form.lower().startswith('(include-book ')]
        body = [form for form in body if form not in hoisted]
        # A host LD exports its nonlocal events. Its LOCAL proof setup must
        # not leak into a dependent host file during source execution.
        prefix = '\n'.join(hoisted)
        if not body:
            return prefix
        return prefix + '\n(value-triple (cw "FN_SOURCE_HOST ' + str(path.relative_to(source)) + '~%"))\n' + \
               '(encapsulate ()\n' + '\n\n'.join(body) + '\n)'

    path = source / build
    remember(path)
    output_forms = ['(in-package "ACL2")']
    native = False
    boundary = None
    for form in forms(path.read_text()):
        if form.lower() == ':q':
            output_forms.append(':q')
            break
        if form.lower().startswith('(defttag :fn-native-host'):
            boundary = len(output_forms)
            native = True
        if native:
            output_forms.append(form)
            continue
        transformed = transform(form, source)
        if transformed:
            output_forms.append(transformed)
    if not native:
        raise ValueError('current build lacks normal/native boundary')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text('\n\n'.join(output_forms) + '\n')
    remember(output.resolve())
    # The retained logical REPL can admit host definitions without crossing
    # the trusted raw boundary or leaving its loop. The complete build remains
    # the fresh-entry input, with exactly the same ordered events.
    normal = output.with_name(output.stem + '.normal.lisp')
    native_path = output.with_name(output.stem + '.native.lisp')
    normal.write_text('\n\n'.join(output_forms[:boundary]) + '\n')
    native_path.write_text('(in-package "ACL2")\n' +
                           '\n\n'.join(output_forms[boundary:]) + '\n')
    remember(normal.resolve())
    remember(native_path.resolve())
    manifest = output.with_suffix('.json')
    manifest.write_text(json.dumps({
        'kind': 'current host source and trusted native loads; not admission or qualification',
        'source': str(source), 'logical_world': str(world_manifest),
        'logical_source': world['source'], 'logical_source_revision': world.get('source_revision'),
        'host_files': hosts, 'inputs_sha256': inputs,
        'build': str(output.resolve()), 'normal_host': str(normal.resolve()),
        'native_installation': str(native_path.resolve()),
    }, indent=2) + '\n')
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--world-manifest', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--build', default='host/native/build.lisp')
    args = parser.parse_args()
    print(generate(args.source_root, args.world_manifest, args.output, args.build))


if __name__ == '__main__':
    main()
