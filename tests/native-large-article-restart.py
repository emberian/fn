#!/usr/bin/env python3
"""Accepted 96 KiB APPENDs, observed rolling resets, process death and exact FETCH.

Requires the qualified coherent rolling producer and explicit profile admission.
Reset observation establishes executed control/counter changes, not physical
persistence refinement or power-loss durability. This is a separate native gate.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('large_refusal', ROOT / 'tests/native-large-article-refusal.py')
large = importlib.util.module_from_spec(spec)
spec.loader.exec_module(large)
base = large.base


def reset_evidence(path, operations):
    groups = {}
    for line in path.read_text().splitlines():
        record = json.loads(line)
        before, after = record.get('before'), record.get('after')
        assert isinstance(before, list) and isinstance(after, list) and len(before) == len(after) == 7, record
        assert all(type(x) is int and x >= 0 for x in before + after), record
        assert before[:-1] == after[:-1], 'reset changed upload identity'
        if after[-1] == before[-1]:
            continue  # A call without an actual change is no reset witness.
        assert record['result'] == 'OK' and after[-1] == before[-1] + 1, record
        identity = tuple(before[:-1])  # id/gen, owner/gen, request, operation
        history = groups.setdefault(identity, [])
        if history:
            assert before[-1] == history[-1][1], 'noncontiguous reset evidence'
        history.append((before[-1], after[-1]))
    result = []
    for operation in operations:
        matching = [(identity, history) for identity, history in groups.items() if identity[-1] == operation]
        assert len(matching) == 1, (operation, 'expected one actual upload identity', matching)
        identity, history = matching[0]
        assert len(history) >= 2, (operation, 'no multiple rolling counter changes', history)
        result.append(dict(identity=identity, changes=history))
    return result



def selected_launchers():
    real = Path(os.environ['FN_ACL2']).resolve(strict=True)
    observer = (ROOT / 'tests/native-rolling-launcher.py').resolve(strict=True)
    for path in (real, observer):
        if not path.is_file() or not os.access(path, os.X_OK):
            raise PermissionError(f'Native test launcher is not executable: {path}')
    if real == observer:
        raise ValueError('FN_ACL2 must select the qualified real launcher, not the observer')
    return real, observer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, required=True)
    args = parser.parse_args()
    real_launcher, observer_launcher = selected_launchers()
    directory = args.directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    startup = ('--article-max', '100000')
    image = directory / 'node.img'
    control = Path(f'/tmp/fn2-large-accepted-{os.getpid()}-{time.time_ns()}.sock')
    principal = 'large-accepted-reader'
    submissions = []
    for index, marker in enumerate((b'first', b'other')):
        mid = f'<large-accepted-{index}@example.invalid>'
        article = large.large_article(mid, marker)
        path = directory / f'submitted-{index}.article'
        path.write_bytes(article)
        submissions.append((mid, article, path))
    base.initialize(directory, image, startup_args=startup)
    evidence = directory / 'upload-resets.jsonl'
    env = base.environment()
    env.update(FN_ACL2=str(observer_launcher),
               FN2_TEST_REAL_ACL2=str(real_launcher), FN2_TEST_UPLOAD_RESETS=str(evidence))
    node = base.restart.Node(directory, image, 'serve', 'append', control_sock=control,
                             env=env, startup_args=startup)
    accepted = []
    receipts = []
    try:
        node.marker(b'LISTENING-LOCAL ')
        created = base.run_fn(directory, 'principal', 'principal', 'create', principal, '--control-sock', control)
        assert created['outcome'] == 'accepted', created
        large.grant_append_fetch(directory, principal, control)
        for index, (mid, article, path) in enumerate(submissions):
            reply = base.run_fn(directory, f'accepted-{index}', 'stream', 'append', '--as', principal,
                               '--file', path, '--op', str(91 + index), '--control-sock', control)
            assert reply['outcome'] == 'accepted' and reply['evidence'] == 'committed', reply
            assert reply['message_id'] == mid and reply['position'] > 0, reply
            accepted.append(reply)
        assert len({(reply['domain'], reply['position']) for reply in accepted}) == 2
        node.kill()  # The parent received both committed replies before killing its own PID.
        resets = reset_evidence(evidence, (91, 92))
        receipts.append(dict(phase='accepted', node_pid=node.node_pid, exit=node.proc.returncode,
                             octets=[98304, 98304], reset_evidence=resets))
    finally:
        node.close()
    (directory / 'processes.json').write_text(json.dumps(receipts, indent=2) + '\n')
    # No observation wrapper on recovery: the actual selected launcher opens anew.
    node = base.restart.Node(directory, image, 'serve', 'fetch', control_sock=control,
                             env=base.environment(), startup_args=startup)
    try:
        node.marker(b'LISTENING-LOCAL ')
        for index, ((mid, article, _), reply) in enumerate(zip(submissions, accepted)):
            fetched = base.run_fn(directory, f'fetched-{index}', 'stream', 'fetch', mid, '--as', principal,
                                 '--domain', reply['domain'], '--position', reply['position'], '--control-sock', control)
            (directory / f'fetched-{index}.article').write_bytes(base.exact_fetch(fetched, article))
        refused = base.run_fn(directory, 'cross-identity', 'stream', 'fetch', submissions[0][0], '--as', principal,
                             '--domain', accepted[1]['domain'], '--position', accepted[1]['position'],
                             '--control-sock', control, expected=1)
        assert refused == {'outcome': 'refused', 'reason': 'unavailable'}, refused
        node.kill()
        receipts.append(dict(phase='recovered', node_pid=node.node_pid, exit=node.proc.returncode))
    finally:
        node.close()
    (directory / 'processes.json').write_text(json.dumps(receipts, indent=2) + '\n')
    print('NATIVE LARGE RESTART PASS: two accepted96KiB articles, actual repeated resets, exact fresh FETCH/cross-identity refusal')


if __name__ == '__main__':
    main()
