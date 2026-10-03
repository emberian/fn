#!/usr/bin/env python3
"""Save an idle, owned Linux ACL2 REPL, without repeating its admitted prefix.

SAVE-EXEC on SBCL terminates the child. Restart the resulting launcher in a
new proof_repl session and check ordinary events before consuming this cache.
This is an internal logical execution cache, never a certificate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import socket
import time


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def literal(value):
    return '"' + str(value).replace('\\', '\\\\').replace('"', '\\"') + '"'


def checkpoint(directory, output, inputs, timeout=120):
    directory, output = Path(directory).resolve(), Path(output).resolve()
    state = json.loads((directory / 'state.json').read_text())
    if not state.get('ready'):
        raise ValueError('session is not ready')
    if output.exists() or Path(str(output) + '.core').exists():
        raise ValueError('choose a fresh checkpoint coordinate')
    hashes = {str(Path(p).resolve()): digest(p) for p in inputs}
    if not hashes:
        raise ValueError('bind the admitted source inputs explicitly')
    pid = state['acl2_pgid']
    command = Path(f'/proc/{pid}/cmdline').read_bytes()
    if b'/tools/acl2' not in command:
        raise ValueError('session child is not the owned ACL2 pool wrapper')
    stdin = Path(f'/proc/{pid}/fd/0')
    if not os.readlink(stdin).startswith('pipe:'):
        raise ValueError('ACL2 child stdin is not the server pipe')
    output.parent.mkdir(parents=True, exist_ok=True)
    # Holding an accepted connection prevents the existing server from
    # delivering another form while this explicit handoff exits LP. No
    # general proof send is allowed to escape the ordinary event loop.
    with socket.socket(socket.AF_UNIX) as control:
        control.settimeout(timeout)
        control.connect(str(directory / 'sock'))
        time.sleep(0.1)
        saved = '(acl2::save-exec ' + literal(output) + ' "internal retained logical source cache" :inert-args t :host-lisp-args "--noinform" :toplevel-args "--disable-debugger")'
        raw = ':q\n(handler-case ' + saved + ' (error (e) (format t "~%FN-REPL-CHECKPOINT-REFUSED ~a~%" e)))\n(acl2::lp)\n'
        log = directory / 'log'
        offset = log.stat().st_size if log.exists() else 0
        descriptor = os.open(stdin, os.O_WRONLY)
        try:
            os.write(descriptor, raw.encode())
        finally:
            os.close(descriptor)
        deadline = time.monotonic() + timeout
        refused = False
        while Path(f'/proc/{pid}').exists():
            if Path(f'/proc/{pid}/stat').read_text().split(') ', 1)[1].startswith('Z '):
                break
            if log.exists():
                with log.open() as stream:
                    stream.seek(offset)
                    refused = 'FN-REPL-CHECKPOINT-REFUSED' in stream.read()
            if refused:
                break
            if time.monotonic() >= deadline:
                # Release the server on timeout; do not kill the child or
                # retry a possibly consumed save operation.
                control.sendall(json.dumps({'op': 'touch'}).encode())
                control.shutdown(socket.SHUT_WR)
                raise TimeoutError('checkpoint outcome unresolved; retained files/process require inspection')
            time.sleep(0.1)
        request = ({'form': '(value-triple :checkpoint-refusal-returned-to-lp)', 'limit': 0}
                   if refused else {'op': 'status'})
        control.sendall(json.dumps(request).encode())
        control.shutdown(socket.SHUT_WR)
        answer = b''
        while chunk := control.recv(65536):
            answer += chunk
        if refused:
            raise ValueError('save refused; ordinary LP retained: ' + answer.decode())
    core = Path(str(output) + '.core')
    if not output.is_file() or not core.is_file():
        raise ValueError('child exited without complete launcher and core')
    for path, expected in hashes.items():
        if digest(path) != expected:
            raise ValueError('checkpoint input changed during save: ' + path)
    manifest = output.with_suffix('.execution.json')
    manifest.write_text(json.dumps({'kind': 'retained logical execution cache; ordinary restart verification required',
                                   'session': str(directory), 'source_inputs': hashes,
                                   'launcher': str(output), 'core': str(core),
                                   'sha256': {str(output): digest(output), str(core): digest(core)},
                                   'prior_acl2_pgid': pid}, indent=2) + '\n')
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('session_dir', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--input', action='append', type=Path, required=True)
    args = parser.parse_args()
    print(checkpoint(args.session_dir, args.output, args.input))


if __name__ == '__main__':
    main()
