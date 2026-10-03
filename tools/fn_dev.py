#!/usr/bin/env python3
"""Interactive operator commands and an explicit trusted development REPL."""
import argparse
import shlex
import socket
import subprocess
import sys

try:
    import readline  # in-memory editing/history; no persistent command log
except ImportError:
    pass

MAX_CODE = 65536
MAX_REPLY = 4 * 65536 + 1024


def evaluate(path, source, timeout=None):
    data = source.encode('utf-8')
    if len(data) > MAX_CODE:
        raise ValueError('developer form exceeds 65536 UTF-8 bytes; load a source file instead')
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
        sock.settimeout(timeout)
        sock.connect(str(path))
        sock.sendall(data)
        sock.shutdown(socket.SHUT_WR)
        reply = bytearray()
        while True:
            part = sock.recv(min(65536, MAX_REPLY + 1 - len(reply)))
            if not part:
                break
            reply.extend(part)
            if len(reply) > MAX_REPLY:
                raise ValueError('developer reply exceeds bounded protocol output')
    status, separator, text = reply.decode('utf-8').partition('\n')
    if not separator or status not in ('OK', 'ERROR'):
        raise ValueError('incomplete developer REPL reply; execution outcome is unknown')
    return status == 'OK', text


def repl(args):
    """Each connection evaluates one form in the same running Lisp world."""
    if args.eval is not None:
        ok, text = evaluate(args.socket, args.eval, args.timeout)
        sys.stdout.write(text)
        return 0 if ok else 1
    print('Live developer Lisp; :help for commands. Forms execute in the owner quantum.')
    while True:
        try:
            line = input('fn> ')
            if not line.strip():
                continue
            if line in (':quit', ':exit'):
                return 0
            if line == ':help':
                print(':operation, :threads, :apropos TEXT, :describe FORM, :load PATH,\n:acl2 FORM, :acl2-file PATH, :paste, :trace on|timing|report|hotspots [N]|off, :quit\n'
                      'Enter one Common Lisp form, or PROGN for a batch.\n'
                      '*fnn-dev-service* is the current owner; fnn-core calls the core.\n'
                      'Reader evaluation (#.) is disabled. File paths name server source.\n'
                      ':load and :acl2-file preserve completed prefixes on reader refusal.\n'
                      f':acl2 uses at most {args.prover_steps} prover steps per form; '
                      'this is not a wall-time or arbitrary Lisp limit.')
                continue
            if line == ':paste':
                print('Paste one form or PROGN; finish with :end on its own line.')
                lines = []
                while True:
                    part = input('... ')
                    if part == ':end':
                        break
                    lines.append(part)
                line = '\n'.join(lines)
            if line == ':operation':
                line = '(princ (fn-record-octets-string (fn-native-operation-host-report *the-live-state*)))'
            elif line == ':threads':
                line = '(mapcar (function sb-thread:thread-name) (sb-thread:list-all-threads))'
            elif line == ':trace on':
                line = '(progn (fnn-trace-start :allocation :process) :tracing)'
            elif line == ':trace timing':
                line = '(progn (fnn-trace-start) :tracing)'
            elif line == ':trace report':
                line = '(fnn-trace-report *standard-output*)'
            elif line == ':trace hotspots' or line.startswith(':trace hotspots '):
                count = 10 if line == ':trace hotspots' else int(line[len(':trace hotspots '):])
                if count <= 0:
                    raise ValueError('trace hotspot count must be positive')
                line = f'(fnn-trace-hotspots *standard-output* {count})'
            elif line == ':trace off':
                line = '(setf *fnn-trace-state* nil)'
            elif line.startswith(':describe '):
                line = '(describe ' + line[10:] + ')'
            elif line.startswith(':apropos '):
                line = '(apropos ' + lisp_string(line[9:]) + ')'
            elif line.startswith(':load '):
                line = '(fnn-dev-load ' + lisp_string(line[6:]) + ')'
            elif line.startswith(':acl2-file '):
                line = '(fnn-dev-admit-file ' + lisp_string(line[11:]) + f' :step-limit {args.prover_steps})'
            elif line.startswith(':acl2 '):
                line = "(fnn-dev-admit '(" + line[6:] + f') :step-limit {args.prover_steps})'
            ok, text = evaluate(args.socket, line, args.timeout)
            sys.stdout.write(text)
            if not ok:
                print('[evaluation failed]', file=sys.stderr)
        except EOFError:
            return 0
        except KeyboardInterrupt:
            print('\nConnection closed; an already submitted form may still be running.', file=sys.stderr)
        except (OSError, ValueError) as error:
            print(str(error), file=sys.stderr)


def lisp_string(text):
    return '"' + text.replace('\\', '\\\\').replace('"', '\\"') + '"'


def shell(args):
    print('Live operator shell; help lists operator commands; :quit exits.')
    while True:
        try:
            line = input('operator> ')
            if line.strip() in (':quit', ':exit'):
                return 0
            words = shlex.split(line)
            if words:
                result = subprocess.run([args.executable, 'operator', args.config, *words])
                if result.returncode:
                    print(f'[exit {result.returncode}]', file=sys.stderr)
        except EOFError:
            return 0
        except KeyboardInterrupt:
            print('\nInterrupted; submitted work may still have completed.', file=sys.stderr)
        except (OSError, ValueError) as error:
            print(str(error), file=sys.stderr)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('shell', help='interactive access to the complete operator command set')
    p.add_argument('--executable', default='fn')
    p.add_argument('--config', required=True)
    p.set_defaults(run=shell)
    p = sub.add_parser('repl', help='attach to an opted-in running developer process')
    p.add_argument('--socket', required=True)
    p.add_argument('--eval', help='evaluate one form without an interactive prompt')
    p.add_argument('--timeout', type=float, help='client observation timeout; does not cancel evaluation')
    p.add_argument('--prover-steps', type=int, default=200000,
                   help='ACL2 prover steps per :acl2 form (default: 200000; not a wall-time limit)')
    p.set_defaults(run=repl)
    args = parser.parse_args(argv)
    if args.command == 'repl' and args.prover_steps < 0:
        parser.error('--prover-steps must be nonnegative')
    try:
        return args.run(args)
    except (OSError, ValueError) as error:
        print(error, file=sys.stderr)
        return 2

if __name__ == '__main__':
    sys.exit(main())
