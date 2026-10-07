#!/usr/bin/env python3
"""Exercise `fn operator CONFIG eval' on a real developer owner, using an existing executable.

Run under the build host's resource wrapper. --root must be a new scratch coordinate; logs and
Store are retained.  No image construction or qualification.  --executable is the DEVELOPER image
(a production image has no such verb: tests/test_developer_surface_absent.py).

What it checks (RP-3 of the observability program, build/coordinator/OBSERVABILITY-PROGRAM-20261007.md):
  * normal: values and a retained definition over the control socket, ACL2 events admitted and
    refused with the owner still serving, the prover limit; the service log holds
    `developer-eval begin ...' before and `developer-eval end ...' after each form, and the
    decision journal holds one developer-eval entry (op 8) per form, written before its effects;
  * fault: a form that faults the owner fences it (exit 4) and the log still holds its begin line
    and no end line;
  * mutation (labelled): the same fault with FN_NATIVE_TEST_EVAL_BEGIN_LATE=1 -- the begin line and
    the journal entry written after the form -- leaves NO begin line, which is what the fault phase's
    assertion refuses: the assertion has teeth.
"""
import argparse
import os
import re
import signal
import socket
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import fn_dev

BEGIN = re.compile(r'^developer-eval begin uid=(\d+) form-octets=(\d+) form-digest=([0-9a-f]{64}) '
                   r'time=\S+$', re.M)
END = re.compile(r'^developer-eval end status=(ok|error) output-octets=(\d+) duration-ms=(\d+)$', re.M)


def lines_of(log):
    return [line for line in log.read_text().splitlines() if line.startswith('developer-eval ')]


def journal_entries(root):
    path = root / 'store' / 'journal' / 'decisions.fnj'
    if not path.exists():
        return []
    return [[int(word) for word in line.split()] for line in path.read_text().splitlines() if line]


def start_owner(wrapper, config, log, env):
    with log.open('w') as sink:
        return subprocess.Popen([str(wrapper), '--fn', 'operator', str(config), 'run'],
                                env=env, stdout=sink, stderr=sink)


def wait_for_socket(owner, path, log):
    until = time.monotonic() + 45
    while not path.exists():
        assert owner.poll() is None, (owner.returncode, log.read_text())
        assert time.monotonic() < until, 'owner startup timeout'
        time.sleep(.05)


def stop(owner):
    if owner.poll() is None:
        owner.terminate()
        try:
            owner.wait(timeout=10)
        except subprocess.TimeoutExpired:
            owner.kill()
            owner.wait()


def prepare(wrapper, root):
    """A fresh store, configuration and control path under ROOT."""
    root.mkdir(parents=True, exist_ok=False)
    with socket.socket() as sock:
        sock.bind(('127.0.0.1', 0))
        port = sock.getsockname()[1]
    config = root / 'fn.toml'
    control = root / 'control.sock'
    config.write_text(f'[store]\npath = "{root}/store"\n[listener]\nhost = "127.0.0.1"\nport = {port}\n'
                      f'[control]\npath = "{control}"\n')
    init = subprocess.run([str(wrapper), '--fn', 'operator', str(config), 'init', '--budget', '2048',
                           'fn.test'], capture_output=True, text=True, timeout=60)
    (root / 'init.log').write_text(init.stdout + init.stderr)
    assert init.returncode == 0, (init.returncode, init.stdout, init.stderr)
    return config, control


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--executable', type=Path, required=True)
    parser.add_argument('--root', type=Path, required=True)
    args = parser.parse_args()
    top = args.root.resolve()
    top.mkdir(parents=True, exist_ok=False)
    wrapper = args.executable.resolve()
    command = '%s --fn' % wrapper
    base = {k: v for k, v in os.environ.items() if k != 'FN_NATIVE_TEST_EVAL_BEGIN_LATE'}
    for phase in ('normal', 'fault', 'mutation'):
        root = top / phase
        config, control = prepare(wrapper, root)
        print(phase, 'INIT PASS', flush=True)

        def ev(form, timeout=10):
            return fn_dev.evaluate(config, form, timeout, command)

        log = root / (phase + '.log')
        env = dict(base)
        if phase == 'mutation':
            env['FN_NATIVE_TEST_EVAL_BEGIN_LATE'] = '1'
        owner = start_owner(wrapper, config, log, env)
        try:
            wait_for_socket(owner, control, log)
            assert control.stat().st_mode & 0o777 == 0o600
            if phase == 'normal':
                assert ev('(+ 1 2)', 5) == (True, '3\n')
                print('ACTUAL OWNER EVAL PASS', flush=True)
                ok, text = ev("(fnn-dev-admit '((defun fn-dev-native-id (x) x)))")
                assert ok and ':ADMITTED' in text, (ok, text)
                ok, text = ev("(fnn-dev-admit '((defthm fn-dev-native-false nil)))")
                assert not ok and 'admission incomplete' in text, (ok, text)
                assert ev('(+ 20 22)', 5) == (True, '42\n')
                assert owner.poll() is None
                print('ACTUAL OWNER LD REFUSAL/CONTINUATION PASS', flush=True)
                ok, text = ev("(fnn-dev-admit '((defthm fn-dev-native-limited (equal (append (append x y) z) "
                              "(append x (append y z))))) :step-limit 0)")
                assert not ok and 'ACL2 Error [Step-limit]' in text, (ok, text)
                assert ev('(+ 20 22)', 5) == (True, '42\n')
                ok, text = ev("(fnn-dev-admit '((defthm fn-dev-native-after-limit "
                              "(equal (fn-dev-native-id x) x))))")
                assert ok and ':ADMITTED' in text, (ok, text)
                assert owner.poll() is None
                print('ACTUAL OWNER PROVER LIMIT/RECOVERY PASS', flush=True)
                # a form that is not a form, and a reader evaluation, fail and the owner serves on
                assert not ev('(+ 1 2) (+ 3 4)', 5)[0]
                assert not ev('#.(error "reader eval")', 5)[0]
                assert ev('(+ 1 2)', 5) == (True, '3\n')
                owner.send_signal(signal.SIGTERM)
                code = owner.wait(timeout=20)
                assert code == 0, (code, log.read_text())
                # RP-3: every form logged around its evaluation, begin before end
                seen = lines_of(log)
                begins = [i for i, line in enumerate(seen) if BEGIN.match(line)]
                ends = [i for i, line in enumerate(seen) if END.match(line)]
                assert len(begins) == len(ends) >= 10, seen
                assert all(b < e for b, e in zip(begins, ends)) and \
                    all(begins[i + 1] > ends[i] for i in range(len(begins) - 1)), seen
                assert all(int(BEGIN.match(seen[i]).group(1)) == os.getuid() for i in begins), seen
                assert any(END.match(seen[i]).group(1) == 'error' for i in ends), seen
                # the journal: one op-8 entry per form, carrying the peer's uid and the form's length,
                # in the sequence the begin lines were written in
                eight = [e for e in journal_entries(root) if len(e) == 7 and e[1] == 8]
                assert len(eight) == len(begins), (eight, seen)
                assert all(e[3] == os.getuid() for e in eight), eight
                assert [e[4] for e in eight] == [int(BEGIN.match(seen[i]).group(2)) for i in begins], \
                    (eight, seen)
                print('LOGGED BEGIN/END AND JOURNAL ENTRY PASS', flush=True)
            else:
                try:
                    ok, text = ev('(error "intentional developer fence test")', 10)
                    assert not ok, (ok, text)
                except ValueError:
                    # Fault fencing may close the client before a reply is sent.
                    pass
                code = owner.wait(timeout=20)
                assert code == 4, (code, log.read_text())
                seen = lines_of(log)
                begun = [line for line in seen if BEGIN.match(line)]
                ended = [line for line in seen if END.match(line)]
                if phase == 'fault':
                    assert len(begun) == 1 and not ended, seen
                    print('ACTUAL OWNER FAULT/FENCE LEAVES THE BEGIN LINE PASS', flush=True)
                else:
                    # MUTATION witness: the begin line after the form leaves none, so the fault
                    # phase's assertion (one begin line, no end line) is red on it.
                    assert not begun and not ended, seen
                    print('MUTATION (begin line late) LEAVES NO BEGIN LINE: THE FAULT ASSERTION HAS TEETH',
                          flush=True)
            assert not control.exists(), 'control socket survived owner shutdown'
            print(phase, 'CLEANUP PASS', flush=True)
        finally:
            stop(owner)
    print('DEV-REPL-NATIVE-OWNER-PASS', flush=True)


if __name__ == '__main__':
    main()
