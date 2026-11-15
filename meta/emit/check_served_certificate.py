#!/usr/bin/env python3
"""Run kernel gates and report exact, current per-root coverage.

ACL2 evidence is a record-toolchain cache entry at the current closure key.
Lean evidence is a successful compiler invocation plus the named theorem's
axiom census. Neither emitter output nor a pre-existing .olean is counted.
"""
from concurrent.futures import ThreadPoolExecutor
from contextlib import ExitStack, contextmanager
import fcntl
import tempfile
from datetime import date
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading

sys.path.insert(0, str(Path(__file__).parent))
from emit_served_certificate import BASE, digest

LEAN_CACHE_POLICY = 'external-artifacts-exact-batch-import-view-v2'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ROOT_THEOREMS = ('validated', 'accepted_entry_positive', 'omitted_child_rejected')


def current(report, root=BASE):
    if digest(root / report['package']) != report['package_sha256']:
        raise ValueError('canonical package changed; regenerate coverage')
    for name, sha in report['inputs'].items():
        if not (root / name).is_file() or digest(root / name) != sha:
            raise ValueError('certificate input changed: ' + name)
    for key in ['roots', 'functions']:
        names = [r['name'] for r in report[key]]
        if len(names) != len(set(names)):
            raise ValueError('duplicate ' + key + ' denominator')


def census(output, theorem):
    if 'sorryAx' in output or "declaration uses 'sorry'" in output:
        return False
    found = re.search(
        r"'" + re.escape(theorem) + r"' (does not depend on any axioms|depends on axioms: \[([^]]*)\])",
        output,
    )
    return bool(found and (not found[2] or set(x.strip() for x in found[2].split(',')) <= ALLOWED))


def local_imports(text):
    ds = []
    for line in re.findall(r'^(?:public\s+)?import\s+(?:all\s+)?(.+)$', text, re.M):
        ds += [x for x in line.split() if x == 'Fn2' or x.startswith('Fn2.')]
    return ds


def parse_module_slice(text):
    """Extract (public_imports, all_imports, body) from an `as_module(..., expose=True)` file.
    Returns None if the file uses custom structure or declares any `axiom`.
    """
    if re.search(r'^\s*axiom\b', text, re.M):
        return None
    marker = '\n@[expose] public section\n'
    if marker not in text:
        return None
    hdr, rest = text.split(marker, 1)
    rest_s = rest.rstrip()
    if rest_s == 'end':
        body = ''
    elif rest_s.endswith('\nend'):
        body = rest_s[:-4]
    else:
        return None
    pub_imps, all_imps = [], []
    for line in hdr.splitlines():
        s = line.strip()
        if not s or s.startswith('--') or s == 'module':
            continue
        m_all = re.match(r'^(?:public\s+)?import\s+all\s+(.+)$', s)
        if m_all:
            all_imps.extend(m_all.group(1).split())
            continue
        m_pub = re.match(r'^(?:public\s+)?import\s+(.+)$', s)
        if m_pub:
            pub_imps.extend(m_pub.group(1).split())
            continue
        return None
    return pub_imps, all_imps, body


def build_batch_source(slices):
    """Build a single Lean module checking multiple independent proof slices.
    `slices` is a list of `(root_index, pub_imps, all_imps, body)`.
    Returns `(source_text, line_ranges)` where `line_ranges` maps `root_index -> (start_line, end_line)`.
    """
    pubs = list(dict.fromkeys(m for _, p, _, _ in slices for m in p))
    alls = [m for m in dict.fromkeys(m for _, _, a, _ in slices for m in a) if m not in set(pubs)]
    both = set(pubs) & {m for _, _, a, _ in slices for m in a}
    lines = ['module', '']
    for m in pubs:
        lines.append(('public import all ' if m in both else 'public import ') + m)
    for m in alls:
        lines.append('import all ' + m)
    lines += ['', '@[expose] public section']
    ranges = {}
    for idx, _, _, body in slices:
        sec = f'Batch_Root{idx}Proof'
        lines.append(f'section {sec}')
        start = len(lines)
        body_lines = body.splitlines()
        lines.extend(body_lines)
        end = len(lines)
        lines.append(f'end {sec}')
        ranges[idx] = (start, max(start, end))
    lines += ['', 'end', '']
    return '\n'.join(lines), ranges


def transitive_dependencies(names, graph):
    result = set()
    def visit(name):
        if name in result:
            return
        if name not in graph:
            raise ValueError('unqualified local import ' + name)
        result.add(name)
        for dep in graph[name]:
            visit(dep)
    for name in names:
        visit(name)
    return result


@contextmanager
def local_dependency_view(lib, modules):
    """Prevent external packages from importing undeclared/stale local artifacts."""
    with tempfile.TemporaryDirectory(prefix='served-lean-imports-') as td:
        view = Path(td)
        # Lean chooses the first package directory, even when a module is absent.
        (view / 'Fn2').mkdir()
        for module in sorted(modules):
            relative = Path(*module.split('.')).with_suffix('.olean')
            artifact = lib / relative
            if not artifact.is_file():
                raise ValueError('missing qualified local artifact ' + module)
            for suffix in ['.olean', '.olean.private', '.olean.server', '.ir']:
                source = lib / relative.with_suffix(suffix)
                if source.is_file():
                    target = view / relative.with_suffix(suffix)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.symlink_to(source.resolve())
        yield view


def compile_one(source, lib, seconds, logname, root=BASE, write_olean=True, allowed_modules=()):
    src_path = Path(source)
    abs_src = src_path if src_path.is_absolute() else (root / src_path)
    meta_dir = root / 'meta'
    lean_arg = str(abs_src.relative_to(meta_dir)) if abs_src.is_relative_to(meta_dir) else str(abs_src)
    cmd = ['lean', '-j1', lean_arg]
    if write_olean:
        out = lib / abs_src.relative_to(meta_dir).with_suffix('.olean')
        out.parent.mkdir(parents=True, exist_ok=True)
        cmd += ['-o', str(out)]
    log = root / 'build/served-certificate-gates' / logname
    log.parent.mkdir(parents=True, exist_ok=True)
    env = lean_environment(lib)
    try:
        with local_dependency_view(lib, allowed_modules) as view:
            env['LEAN_PATH'] = str(view) + os.pathsep + env['LEAN_PATH']
            result = subprocess.run(
                cmd, cwd=meta_dir, env=env, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=seconds,
            )
        log.write_text(result.stdout)
        return result.returncode, result.stdout, str(log.relative_to(root))
    except subprocess.TimeoutExpired as e:
        output = e.stdout or b''
        if isinstance(output, bytes):
            output = output.decode(errors='replace')
        log.write_text(output + '\nTIMEOUT\n')
        return 124, output, str(log.relative_to(root))


def lean_environment(lib):
    env = os.environ.copy()
    env['LEAN_PATH'] = str(lib.resolve()) + (os.pathsep + env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    return env


def artifact_signature(artifact):
    """Bind the complete import artifact, including Lean's private/server sidecars."""
    paths = [artifact, Path(str(artifact) + '.private'), Path(str(artifact) + '.server'),
             artifact.with_suffix('.ir')]
    return ''.join(str(p) + ':' + (digest(p) if p.is_file() else '<absent>') for p in paths)


def external_library_fingerprint(paths, owned_lib=None, owned_modules=()):
    """Conservative transitive import inventory, including shadowing directories.

    Lean resolves a package at its first search root, not each module separately.
    Hash all external artifacts rather than guessing their transitive imports from
    local source. Only exact outputs of the checked local closure are excluded.
    Other Fn2 artifacts remain bound even when an external module imports them.
    Directory symlinks are followed; cycles fail closed.
    """
    hashed = hashlib.sha256()
    owned = owned_lib.resolve() if owned_lib is not None else None
    outputs = set()
    ancestors_owned = set()
    for name in owned_modules:
        artifact = owned / Path(*name.split('.')).with_suffix('.olean')
        outputs.update([artifact, Path(str(artifact)+'.private'), Path(str(artifact)+'.server'),
                        artifact.with_suffix('.ir')])
        ancestors_owned.update(artifact.parents)

    def add(value):
        hashed.update(json.dumps(value, ensure_ascii=True).encode() + b'\n')

    def walk(path, ancestors):
        if path in outputs:
            return
        resolved = path.resolve()
        if path.is_dir():
            if resolved in ancestors:
                raise ValueError('cycle in Lean library path: ' + str(path))
            if path not in ancestors_owned or path == owned:
                add(['directory', str(path), str(resolved)])
            for child in sorted(path.iterdir()):
                walk(child, ancestors | {resolved})
        elif path.is_file() and (path.name.endswith(('.olean', '.olean.private', '.olean.server',
                                                     '.ir', '.so', '.dylib', '.dll')) or '.so.' in path.name):
            add(['artifact', str(path), str(resolved), digest(path)])
        elif path.is_symlink() and not path.exists():
            add(['dangling', str(path), str(resolved)])

    for path in paths:
        path = path.resolve()
        add(['search-root', str(path)])
        if path.exists():
            walk(path, set())
        else:
            add(['missing', str(path)])
    return hashed.hexdigest()


def toolchain_fingerprint(root=BASE, lib=None, owned_modules=()):
    lean_bin = shutil.which('lean')
    if not lean_bin:
        raise RuntimeError('lean executable not found in PATH')
    # An elan proxy's bytes do not identify the compiler selected by a local
    # override. Query from the same cwd as compile_one, then hash that compiler
    # and its shared runtime as well as the launcher.
    prefix = Path(subprocess.check_output(
        [lean_bin, '--print-prefix'], cwd=root / 'meta', text=True, timeout=15).strip())
    compiler = prefix / 'bin/lean'
    if not compiler.is_file():
        raise RuntimeError('selected Lean compiler missing: ' + str(compiler))
    version = subprocess.check_output(
        [lean_bin, '--version'], cwd=root / 'meta', text=True, timeout=15)
    files = [Path(lean_bin).resolve(), compiler.resolve(),
             root / 'meta/lean-toolchain', root / 'meta/lake-manifest.json']
    runtime = prefix / 'lib/lean'
    files.extend(sorted(runtime.glob('*.so')))
    files.extend(sorted(runtime.glob('*.dylib')))
    env = lean_environment(lib) if lib is not None else os.environ
    search = env.get('LEAN_PATH', '').split(os.pathsep) if env.get('LEAN_PATH') else []
    paths = [(Path(p) if Path(p).is_absolute() else root / 'meta' / p).resolve() for p in search]
    paths.append(runtime.resolve())
    external = external_library_fingerprint(paths, lib, owned_modules)
    return hashlib.sha256((LEAN_CACHE_POLICY + version + external + ''.join(
        str(p) + ':' + digest(p) for p in files)).encode()).hexdigest()


def dep_signature(deps, done, lib):
    parts = []
    for d in sorted(set(deps)):
        art = lib / Path(*d.split('.')).with_suffix('.olean')
        parts.append(f'{d}:{done[d]}:{artifact_signature(art)}')
    return ''.join(parts)


def atomic_cache_checkpoint(path, cache):
    """Replace a cache atomically; caller holds the gate's writer lock."""
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode='w', dir=path.parent,
                                         prefix=path.name + '.', suffix='.tmp',
                                         delete=False) as stream:
            temporary = Path(stream.name)
            json.dump(cache, stream, indent=2)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        temporary = None
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


@contextmanager
def lean_cache_session(root, lib=None):
    """One writer owns cache and library mutation until all its workers exit."""
    path = root / 'build/served-lean-cache.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    locks = [path.with_suffix('.lock')]
    if lib is not None:
        lib = lib.resolve()
        lib.mkdir(parents=True, exist_ok=True)
        locks.append(lib / '.served-lean-library.lock')
    # Keep lock inodes: unlinking one would let a second writer lock a new file.
    with ExitStack() as stack:
        for lock_path in sorted(locks):
            lock = stack.enter_context(lock_path.open('a+b'))
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                raise RuntimeError('another served Lean gate owns ' + str(lock_path)) from None
        cache = json.loads(path.read_text()) if path.exists() else {}
        checkpoint = lambda: atomic_cache_checkpoint(path, cache)
        try:
            yield cache, checkpoint
        finally:
            checkpoint()


def local_module_closure(roots, root):
    deps = {}

    def visit(module):
        if module in deps:
            return
        path = root / 'meta' / Path(*module.split('.')).with_suffix('.lean')
        if not path.is_file():
            raise ValueError('missing local Lean import ' + module)
        ds = local_imports(path.read_text())
        deps[module] = ds
        for d in ds:
            visit(d)

    for r in roots:
        visit(r)

    return deps


def compile_closure(roots, lib, seconds, jobs, root=BASE, cache=None, tool=None, checkpoint=None):
    """Recheck every local import, then reuse only this checker's bound cache.
    An olean copied from a warm lane is not evidence for changed dependencies.
    """
    deps = local_module_closure(roots, root)

    if cache is None:
        with lean_cache_session(root, lib) as (owned_cache, save):
            return compile_closure(roots, lib, seconds, jobs, root=root,
                                   cache=owned_cache, tool=tool, checkpoint=save)
    if tool is None:
        lib.mkdir(parents=True, exist_ok=True)
        with stable_toolchain(root, lib, deps, cache, checkpoint or (lambda: None)) as bound_tool:
            return compile_closure(roots, lib, seconds, jobs, root=root, cache=cache,
                                   tool=bound_tool, checkpoint=checkpoint)

    done = {}
    pending = set(deps)
    try:
        while pending:
            ready = sorted(n for n in pending if all(d in done for d in deps[n]))
            if not ready:
                raise ValueError('cycle in local Lean imports')

            def build(n):
                source = 'meta/' + n.replace('.', '/') + '.lean'
                key = hashlib.sha256(
                    (tool + digest(root / source) + dep_signature(deps[n], done, lib)).encode()
                ).hexdigest()
                artifact = lib / Path(*n.split('.')).with_suffix('.olean')
                old = cache.get(n, {})
                if old.get('key') == key and artifact.is_file() and old.get('olean') == artifact_signature(artifact):
                    return n, key, old, None
                rc, out, log = compile_one(source, lib, seconds, 'dependency-' + n + '.log', root=root, write_olean=True,
                                               allowed_modules=transitive_dependencies(deps[n], deps))
                if rc:
                    return n, key, None, log
                rec = {
                    'key': key,
                    'olean': artifact_signature(artifact),
                    'log': log,
                    'log_sha256': digest(root / log),
                }
                return n, key, rec, None

            errors = []
            with ThreadPoolExecutor(max_workers=jobs) as pool:
                for n, key, record, error in pool.map(build, ready):
                    if error:
                        cache.pop(n, None)
                        errors.append(error)
                    else:
                        cache[n] = record
                        done[n] = key
                        pending.remove(n)
                    if checkpoint is not None:
                        checkpoint()
            if errors:
                raise RuntimeError('Lean dependency refused: ' + ', '.join(errors))
    finally:
        if checkpoint is not None:
            checkpoint()
    return done


def extract_root_census_lines(output, root_idx):
    prefix = f"'Fn2.Arms.Served.Root{root_idx}Proof."
    kept = [line for line in output.splitlines() if line.startswith(prefix)]
    return '\n'.join(kept) + ('\n' if kept else '')


def root_census_ok(output, root_idx):
    return all(census(output, f'Fn2.Arms.Served.Root{root_idx}Proof.{t}') for t in ROOT_THEOREMS)


def gate_plan(report, root, only):
    selected_indices = [
        i for i, r in enumerate(report['roots'])
        if not only or (only in r['name'] or only == f'Root{i}' or only == r.get('kind', ''))
    ]
    selected_set = set(selected_indices)

    own = {
        '.'.join(Path(r[k]).relative_to('meta').with_suffix('').parts)
        for i, r in enumerate(report['roots']) if i in selected_set
        for k in ('contract', 'proof') if k in r
    }
    extra = set()
    for i in selected_indices:
        r = report['roots'][i]
        for k in ('contract', 'proof'):
            if k not in r or not (root / r[k]).is_file():
                continue
            extra.update(x for x in local_imports((root / r[k]).read_text()) if x not in own)

    base_closure = {'Fn2.Arms.Wrapper', *['Fn2.Instances.LayerAEqns' + str(i) for i in range(1, 5)]}
    if not only or report.get('commit_words', 0):
        if (root / 'meta/Fn2/Instances/ServedCommit.lean').is_file():
            base_closure.add('Fn2.Instances.ServedCommit')

    return selected_indices, base_closure | extra


@contextmanager
def stable_toolchain(root, lib, owned_modules, cache, checkpoint):
    """Keep standalone closure checks and complete gates in one external world."""
    tool = toolchain_fingerprint(root, lib, owned_modules)
    try:
        yield tool
    finally:
        try:
            stable = toolchain_fingerprint(root, lib, owned_modules) == tool
        except Exception:
            cache.clear()
            checkpoint()
            raise
        if not stable:
            cache.clear()
            checkpoint()
            raise RuntimeError('Lean compiler or external libraries changed during gate')


def lean_gates(report, lib, seconds, jobs, root=BASE, batch_size=4, only=None):
    with lean_cache_session(root, lib) as (cache, checkpoint):
        selected, closure = gate_plan(report, root, only)
        owned_modules = set(local_module_closure(closure, root))
        owned_modules.update('.'.join(Path(report['roots'][i]['contract']).relative_to('meta').with_suffix('').parts)
                             for i in selected)
        with stable_toolchain(root, lib, owned_modules, cache, checkpoint) as tool:
            return lean_gates_locked(report, lib, seconds, jobs, root, batch_size, only, cache, checkpoint, tool)


def proof_batch_scope(row, deps, graph):
    return row.get('kind', ''), tuple(sorted(transitive_dependencies(deps, graph)))


def lean_gates_locked(report, lib, seconds, jobs, root, batch_size, only, cache, checkpoint, tool):
    # The caller starts this process under swarm-build/lake env. Install each
    # changed dependency into this lane's own library, never another lane's.
    cache_lock = threading.Lock()

    selected_indices, base_closure = gate_plan(report, root, only)
    graph = local_module_closure(base_closure, root)
    for i in selected_indices:
        path = Path(report['roots'][i]['contract'])
        graph['.'.join(path.relative_to('meta').with_suffix('').parts)] = local_imports((root / path).read_text())

    try:
        done = compile_closure(sorted(base_closure), lib, seconds, jobs, root=root, cache=cache, tool=tool, checkpoint=checkpoint)

        if not only and report.get('commit_words', 0):
            sc_rec = cache.get('Fn2.Instances.ServedCommit', {})
            sc_log = sc_rec.get('log', '')
            if sc_log and (root / sc_log).is_file() and digest(root / sc_log) == sc_rec.get('log_sha256'):
                out = (root / sc_log).read_text()
                rc, log = 0, sc_log
            else:
                rc, out, log = compile_one(
                    'meta/Fn2/Instances/ServedCommit.lean', lib, seconds, 'commit-words.log',
                    root=root, write_olean=True,
                    allowed_modules=transitive_dependencies(graph['Fn2.Instances.ServedCommit'], graph),
                )
            if rc or not all(
                census(out, 'Fn2.Instances.ServedCommit.word' + str(i) + '_translation')
                for i in range(report['commit_words'])
            ):
                raise RuntimeError('commit word kernel/census gate refused: ' + log)
            report['gates']['commit_words_lean'] = report['commit_words']

        # Phase 1: Deduplicated, content-addressed contract gates (writes .olean for proof imports).
        unique_contracts = sorted({report['roots'][i]['contract'] for i in selected_indices})
        contract_results = {}

        def check_contract(c_rel):
            c_mod = '.'.join(Path(c_rel).relative_to('meta').with_suffix('').parts)
            c_src = root / c_rel
            c_deps = local_imports(c_src.read_text())
            c_key = hashlib.sha256(
                (tool + digest(c_src) + dep_signature(c_deps, done, lib)).encode()
            ).hexdigest()
            artifact = lib / Path(*c_mod.split('.')).with_suffix('.olean')
            ck = 'contract:' + c_mod
            with cache_lock:
                old = dict(cache.get(ck, {}))
            log_name = f'contract-{c_mod.split(".")[-1]}.log'
            old_log = old.get('log', '')
            if (
                old.get('key') == c_key
                and artifact.is_file()
                and old.get('olean') == artifact_signature(artifact)
                and old_log
                and (root / old_log).is_file()
                and old.get('log_sha256') == digest(root / old_log)
            ):
                return c_rel, c_mod, c_key, 0, old_log, None
            rc, out, log = compile_one(c_rel, lib, seconds, log_name, root=root, write_olean=True,
                                        allowed_modules=transitive_dependencies(c_deps, graph))
            if rc == 0:
                rec = {
                    'key': c_key,
                    'olean': artifact_signature(artifact),
                    'log': log,
                    'log_sha256': digest(root / log),
                }
                return c_rel, c_mod, c_key, 0, log, rec
            return c_rel, c_mod, c_key, rc, log, None

        with ThreadPoolExecutor(max_workers=jobs) as pool:
            for c_rel, c_mod, c_key, rc, log, rec in pool.map(check_contract, unique_contracts):
                contract_results[c_rel] = (rc, log)
                if rc == 0:
                    done[c_mod] = c_key
                    if rec is not None:
                        cache['contract:' + c_mod] = rec
                else:
                    cache.pop('contract:' + c_mod, None)
                checkpoint()

        # Phase 2: Check proof cache; group uncached proofs into per-kind batches.
        uncached_by_scope = {}
        solo_items = []

        for i in selected_indices:
            row = report['roots'][i]
            row.pop('lean_gate', None)
            c_rc, c_log = contract_results[row['contract']]
            row['contract_gate'] = {'exit': c_rc, 'log': c_log}
            if c_rc:
                row.update(status='unvalidated', reason='Lean rejected contract: ' + c_log)
                continue
            if 'proof' not in row:
                continue
            p_src = root / row['proof']
            p_txt = p_src.read_text()
            p_deps = local_imports(p_txt)
            p_key = hashlib.sha256(
                (tool + digest(p_src) + dep_signature(p_deps, done, lib)).encode()
            ).hexdigest()
            pk = f'proof:{i}'
            old = cache.get(pk, {})
            old_log = old.get('log', '')
            if (
                old.get('key') == p_key
                and old_log
                and (root / old_log).is_file()
                and old.get('log_sha256') == digest(root / old_log)
            ):
                cached_out = (root / old_log).read_text()
                if root_census_ok(cached_out, i):
                    row.update(
                        status='validated',
                        reason='',
                        lean_gate={
                            'log': old_log,
                            'theorem': f'Fn2.Arms.Served.Root{i}Proof.validated',
                            'log_sha256': old['log_sha256'],
                        },
                    )
                    continue
            parsed = parse_module_slice(p_txt) if batch_size > 1 else None
            item = (i, row, p_key, parsed)
            if parsed is None:
                solo_items.append([item])
            else:
                # A batch may not lend one slice another slice's local imports.
                scope = proof_batch_scope(row, p_deps, graph)
                uncached_by_scope.setdefault(scope, []).append(item)

        batches = list(solo_items)
        for kind_name in sorted(uncached_by_scope):
            items = uncached_by_scope[kind_name]
            for pos in range(0, len(items), max(1, batch_size)):
                batches.append(items[pos:pos + max(1, batch_size)])

        batch_seq = [0]

        def record_solo(item):
            i, row, p_key, _ = item
            rc, out, log = compile_one(row['proof'], lib, seconds, f'{i}-proof.log', root=root, write_olean=False,
                                        allowed_modules=transitive_dependencies(local_imports((root / row['proof']).read_text()), graph))
            theorem = f'Fn2.Arms.Served.Root{i}Proof.validated'
            if rc == 0 and root_census_ok(out, i):
                sha = digest(root / log)
                row.update(status='validated', reason='', lean_gate={'log': log, 'theorem': theorem, 'log_sha256': sha})
                with cache_lock:
                    cache[f'proof:{i}'] = {'key': p_key, 'log': log, 'log_sha256': sha}
            else:
                row.update(
                    status='unvalidated',
                    reason=('Lean proof timed out: ' if rc == 124 else 'Lean rejected proof/census: ') + log,
                )
                with cache_lock:
                    cache.pop(f'proof:{i}', None)

        def run_batch(group):
            try:
                return run_batch_inner(group)
            finally:
                with cache_lock:
                    checkpoint()

        def run_batch_inner(group):
            if not group:
                return
            if len(group) == 1 or any(it[3] is None for it in group):
                for it in group:
                    record_solo(it)
                return
            with cache_lock:
                batch_seq[0] += 1
                bid = batch_seq[0]
            slices = [(i, parsed[0], parsed[1], parsed[2]) for i, _, _, parsed in group]
            batch_src, ranges = build_batch_source(slices)
            gates_dir = root / 'build/served-certificate-gates'
            gates_dir.mkdir(parents=True, exist_ok=True)
            batch_file = gates_dir / f'batch-proof-{bid}.lean'
            batch_file.write_text(batch_src)
            batch_timeout = min(seconds * len(group), max(seconds, 240))
            try:
                rc, out, _ = compile_one(
                    batch_file, lib, batch_timeout, f'batch-proof-{bid}.log',
                    root=root, write_olean=False,
                    allowed_modules=transitive_dependencies(local_imports(batch_src), graph),
                )
            finally:
                batch_file.unlink(missing_ok=True)

            if (
                rc == 0
                and 'sorryAx' not in out
                and "declaration uses 'sorry'" not in out
                and all(root_census_ok(out, i) for i, _, _, _ in group)
            ):
                for i, row, p_key, _ in group:
                    indiv_out = extract_root_census_lines(out, i)
                    if not root_census_ok(indiv_out, i):
                        record_solo((i, row, p_key, None))
                        continue
                    indiv_log = gates_dir / f'{i}-proof.log'
                    indiv_log.write_text(indiv_out)
                    log_rel = str(indiv_log.relative_to(root))
                    sha = digest(indiv_log)
                    theorem = f'Fn2.Arms.Served.Root{i}Proof.validated'
                    row.update(
                        status='validated',
                        reason='',
                        lean_gate={'log': log_rel, 'theorem': theorem, 'log_sha256': sha},
                    )
                    with cache_lock:
                        cache[f'proof:{i}'] = {'key': p_key, 'log': log_rel, 'log_sha256': sha}
                return

            # Fallback on timeout or error: isolate faulty slice(s) and re-batch healthy ones.
            if rc == 124 and len(group) > 1:
                mid = len(group) // 2
                run_batch(group[:mid])
                run_batch(group[mid:])
                return

            err_lines = [int(m) for m in re.findall(r'batch-proof-' + str(bid) + r'\.lean:(\d+):\d+:\s*error:', out)]
            bad_ids = {
                i for i, (lo, hi) in ranges.items()
                if any(lo <= ln <= hi for ln in err_lines) or (rc == 0 and not root_census_ok(out, i))
            }
            if 0 < len(bad_ids) < len(group):
                for it in group:
                    if it[0] in bad_ids:
                        record_solo(it)
                good = [it for it in group if it[0] not in bad_ids]
                run_batch(good)
            else:
                for it in group:
                    record_solo(it)

        if batches:
            with ThreadPoolExecutor(max_workers=jobs) as pool:
                list(pool.map(run_batch, batches))

        report['gates']['lean'] = {'compiler': subprocess.check_output(['lean', '--version'], text=True).strip()}
    finally:
        with cache_lock:
            checkpoint()


def acl2_gate(report, launcher):
    sys.path.insert(0, str(BASE / 'tools'))
    import acl2_toolchain, certs
    found = acl2_toolchain.fingerprint(launcher)
    if not found.qualified:
        raise ValueError('unqualified record ACL2 toolchain')
    entries = certs.book_entries(
        BASE, certs.cache_directory(), 'meta/emit/served-export',
        metadata_filter=lambda m: m.get('toolchain_identity') == found.identity,
    )
    entry = certs.choose_entry(entries, str(BASE.resolve()))
    if entry is None:
        raise ValueError('no record-toolchain certificate at current served-export closure key')
    directory, meta = entry
    report['gates']['acl2'] = {
        'cache_entry': str(directory),
        'toolchain': found.identity,
        'certificate_sha256': meta['cert_sha256'],
    }
    for f in report['functions']:
        f['canonical_export'] = 'validated'


def reconcile(report):
    for r in report['roots']:
        if 'lean_gate' in r:
            if 'acl2' in report['gates']:
                r.update(status='validated', reason='')
            else:
                r.update(status='unvalidated', reason='Lean proof checked; live ACL2 metadata gate missing')


def summary(report):
    fs = report['functions']
    rs = report['roots']
    fv = sum(f['canonical_export'] == 'validated' for f in fs)
    rv = sum(r['status'] == 'validated' for r in rs)
    lines = [
        f'Canonical live exports: {fv}/{len(fs)} validated.',
        f'Whole-arm interpretation: {rv}/{len(rs)} validated.',
        'These counts do not assert exported-body evaluation or primitive-domain adequacy for the entire closure.',
        '',
        'Unvalidated whole roots:',
    ]
    lines += [r['name'] + ': ' + r['reason'] for r in rs if r['status'] != 'validated']
    if fv != len(fs):
        lines += ['', 'Unvalidated canonical exports:']
        lines += [
            f['name'] + ': current record-toolchain served-export gate missing'
            for f in fs if f['canonical_export'] != 'validated'
        ]
    lines += ['', 'Unresolved exported names:'] + [
        n + ': no logical body or attachment in the live world' for n in report['unresolved']
    ]
    lines += [
        '',
        'Native boundary (primitive-domain proofs are a separate gate):',
        ', '.join(report.get('native_boundary', [])),
    ]
    return '\n'.join(lines) + '\n'


def extract_contract_display(contract_text, root_idx):
    ns = f'Fn2.Arms.Served.Root{root_idx}'
    start_pat = f'namespace {ns}'
    end_pat = f'end {ns}'
    lines = contract_text.splitlines()
    block = []
    inside = False
    for line in lines:
        if line == start_pat:
            inside = True
        if inside:
            block.append(line)
            if line == end_pat:
                break
    if not block:
        raise ValueError(f'missing contract section {ns}')
    return ['import Fn2.Arms.Core', 'import Fn2.Instances.ServedMetadata', *block]


def write_snapshots(report, out_dir, stamp=None, root=BASE):
    stamp = stamp or date.today().isoformat()
    out_dir = Path(out_dir)
    cov_txt = summary(report)
    cov_out = (
        f'Generated served bridge coverage — {stamp}\n'
        + f"Canonical packet SHA256: {report['package_sha256']}\n"
        + f"ACL2 record evidence: {json.dumps(report['gates']['acl2'], sort_keys=True)}\n\n"
        + cov_txt
    )
    (out_dir / 'BRIDGE-GENERATED-COVERAGE.txt').write_text(cov_out)

    stmt_lines = [
        f'Validated whole-arm statements — {stamp}',
        f"Canonical packet SHA256: {report['package_sha256']}",
        '',
        'Verbatim generated contracts and theorem signatures; proofs are emitted by the shared templates.',
    ]
    for ri, r in enumerate(report['roots']):
        if r.get('status') != 'validated':
            continue
        c_txt = (root / r['contract']).read_text()
        psrc = (root / r['proof']).read_text().splitlines()
        stmt_lines.append('')
        stmt_lines.append(f"=== {r['name']} ===")
        stmt_lines.extend(extract_contract_display(c_txt, ri))
        stmt_lines.append('')
        for idx, line in enumerate(psrc):
            if line.startswith('theorem validated '):
                sig = [line]
                k = idx + 1
                while k < len(psrc):
                    sig.append(psrc[k])
                    if ':= by' in psrc[k]:
                        break
                    k += 1
                sig[-1] = re.sub(r'\s*:=\s*by\s*$', '', sig[-1])
                stmt_lines.extend(sig)
                break
    (out_dir / 'BRIDGE-GENERATED-STATEMENTS.txt').write_text('\n'.join(stmt_lines) + '\n')


def main():
    a = argparse.ArgumentParser()
    a.add_argument('--report', type=Path, default=BASE / 'build/served-certificate-coverage.json')
    a.add_argument('--lean', action='store_true')
    a.add_argument('--acl2', type=Path)
    a.add_argument('--lib', type=Path, default=BASE / 'build/lean-lib')
    a.add_argument('--timeout', type=int, default=120)
    a.add_argument('-j', type=int, default=4)
    a.add_argument('--batch-size', type=int, default=4)
    a.add_argument('--only', type=str, default=None, help='Developer filter (kind/root); never writes coverage report')
    a.add_argument('--snapshots', type=Path, default=None, help='Directory to write BRIDGE-GENERATED-*.txt snapshots')
    a.add_argument('--stamp', type=str, default=None, help='Date stamp for snapshots')
    args = a.parse_args()
    report = json.loads(args.report.read_text())
    current(report)
    if args.only:
        if not args.lean:
            raise ValueError('--only requires --lean')
        matched = [r for i, r in enumerate(report['roots'])
                   if args.only in r['name'] or args.only == f'Root{i}' or args.only == r.get('kind', '')]
        if not matched:
            print(f'FILTERED LEAN PROBE ({args.only}): no matching roots')
            return 1
        lean_gates(report, args.lib.resolve(), args.timeout, args.j, batch_size=args.batch_size, only=args.only)
        candidates = [r for r in matched if 'proof' in r]
        passed = sum('lean_gate' in r for r in candidates)
        print(f'  {len(candidates)} proof candidates; {len(matched)-len(candidates)} roots without generated proofs')
        print(f'FILTERED LEAN PROBE ({args.only}): {passed}/{len(matched)} roots passed Lean census (report NOT modified)')
        for r in matched:
            if 'lean_gate' not in r and 'proof' in r:
                print('  FAIL', r['name'], r.get('reason', ''))
        return 0 if candidates and passed == len(candidates) else 1
    if args.acl2:
        acl2_gate(report, args.acl2)
    if args.lean:
        lean_gates(report, args.lib.resolve(), args.timeout, args.j, batch_size=args.batch_size)
    current(report)
    reconcile(report)
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    text = summary(report)
    args.report.with_suffix('.txt').write_text(text)
    if args.snapshots:
        write_snapshots(report, args.snapshots, stamp=args.stamp)
    print('\n'.join(text.splitlines()[:3]))
    if args.lean:
        candidates = [r for r in report['roots'] if 'proof' in r]
        failures = [r for r in candidates if 'lean_gate' not in r]
        print(f'LEAN CANDIDATES: {len(candidates)-len(failures)}/{len(candidates)} passed; '
              f'{len(report["roots"])-len(candidates)} roots without generated proofs')
        for r in failures:
            print('  FAIL', r['name'], r.get('reason', ''))
        return 1 if failures or not candidates else 0
    return 0


if __name__ == '__main__':
    sys.exit(main())
