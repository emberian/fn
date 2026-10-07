#!/usr/bin/env python3
"""Interactive operator commands and a trusted development REPL into a running developer node."""
import argparse
import shlex
import subprocess
import sys

try:
    import readline  # in-memory editing/history; no persistent command log
except ImportError:
    pass

# One form goes to a developer node as one `fn operator CONFIG eval' (host/native/developer-eval.lisp):
# the form on standard input, the output on standard output.  ACL2 decides what is admitted
# (books/developer-eval.lisp fn-deval-admit): the client computes no bound of its own.
EVAL_OK, EVAL_FAILED, EVAL_REFUSED, EVAL_NO_REPLY = 0, 1, 2, 3


def evaluate(config, source, timeout=None, executable='fn'):
    """Evaluate SOURCE in the node CONFIG names; (True, output), or (False, output) when the form
    failed.  A refusal (by name) raises ValueError; so does a missing reply, whose form may have run.
    EXECUTABLE is the developer image's command line (a word, or `IMAGE --fn')."""
    command = shlex.split(executable) + ['operator', str(config), 'eval']
    try:
        done = subprocess.run(command, input=source.encode('utf-8'), capture_output=True,
                              timeout=timeout)
    except subprocess.TimeoutExpired:
        raise ValueError('no answer in time; the form may still be running')
    text = done.stdout.decode('utf-8', 'replace')
    note = done.stderr.decode('utf-8', 'replace').strip()
    if done.returncode == EVAL_OK:
        return True, text
    if done.returncode == EVAL_FAILED:
        return False, text
    if done.returncode == EVAL_REFUSED:
        raise ValueError(note or 'refused')
    if done.returncode == EVAL_NO_REPLY:
        raise ValueError('no reply; execution outcome is unknown: ' + note)
    raise ValueError('eval exited %d: %s' % (done.returncode, note))


def repl(args):
    """Each request evaluates one form in the same running Lisp world."""
    if args.eval is not None:
        ok, text = evaluate(args.config, args.eval, args.timeout, args.executable)
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
            ok, text = evaluate(args.config, line, args.timeout, args.executable)
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
                result = subprocess.run([*shlex.split(args.executable), 'operator', args.config, *words])
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
    p = sub.add_parser('repl', help='evaluate forms in a running developer node (a developer image only)')
    p.add_argument('--config', required=True, help='the node\'s fn.toml: its control socket is the channel')
    p.add_argument('--executable', default='fn',
                   help='the developer image\'s command line (default: fn; an image is "IMAGE --fn")')
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
