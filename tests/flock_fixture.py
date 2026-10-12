"""Exercise farm's shell scripts with kernel flock on hosts without flock(1)."""
from pathlib import Path
import shlex
import sys
import tempfile


class LocalFlock:
    def __init__(self):
        self.temporary = None
        if Path('/usr/bin/flock').is_file():
            self.path = Path('/usr/bin/flock')
            self.description = '/usr/bin/flock'
        else:
            self.temporary = tempfile.TemporaryDirectory(prefix='farm-flock-')
            self.path = Path(self.temporary.name) / 'flock'
            self.path.write_text('#!' + sys.executable + '\n' + '''import fcntl, os, sys
args = sys.argv[1:]
flag = args.pop(0)
if flag not in ('-x', '-n'):
    raise SystemExit('flock fixture supports -x FD and -n FILE COMMAND')
if flag == '-x':
    fd = int(args.pop(0))
else:
    fd = os.open(args.pop(0), os.O_CREAT | os.O_RDWR, 0o600)
    os.set_inheritable(fd, True)
try:
    fcntl.flock(fd, fcntl.LOCK_EX | (fcntl.LOCK_NB if flag == '-n' else 0))
except BlockingIOError:
    raise SystemExit(1)
if args:
    os.execvp(args[0], args)
''')
            self.path.chmod(0o755)
            self.description = 'fcntl.flock stand-in (/usr/bin/flock absent)'

    def script(self, script):
        return script.replace('/usr/bin/flock', shlex.quote(str(self.path)))

    def close(self):
        if self.temporary is not None:
            self.temporary.cleanup()
