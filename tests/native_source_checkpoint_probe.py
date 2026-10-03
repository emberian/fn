"""Exercise the actual checkpoint LP driver without constructing a native owner."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import native_source_cache as cache


def main():
    with tempfile.TemporaryDirectory(prefix='fn-source-checkpoint-') as directory:
        root = Path(directory)
        for fails in (False, True):
            original = root / ('bad.lisp' if fails else 'good.lisp')
            original.write_text('(in-package "ACL2")\n'
                                '(defun checkpoint-before (x) x)\n'
                                + ('(defun checkpoint-bad (x) (undefined-checkpoint-call x))\n' if fails else '')
                                + '(value-triple (cw "CHECKPOINT_TERMINAL_REACHED~%"))\n'
                                + cache.ENTRY + '\n')
            manifest = root / ('bad.json' if fails else 'good.json')
            manifest.write_text(json.dumps({'sha256': {}, 'bootstrap': str(original)}))
            prepared = json.loads(cache.prepare(manifest, root / ('bad-out' if fails else 'good-out')).read_text())
            # Use the actual emitted driver; replace only SAVE-EXEC with a
            # marker so this test creates no cache or native process.
            after = prepared['after_acl2_loop'].split(' (acl2::save-exec', 1)[0]
            after += ' (format t "~%CHECKPOINT_SAVE_ALLOWED~%"))'
            command = [os.environ['FN_CHECKPOINT_SBCL'], '--tls-limit', '65536',
                       '--dynamic-space-size', '2000', '--core', os.environ['FN_CHECKPOINT_CORE'],
                       '--noinform', '--disable-debugger', '--no-userinit',
                       '--eval', '(with-open-file (input ' + cache.runner.literal(prepared['bootstrap'])
                       + ') (let ((*standard-input* input) (*terminal-io* (make-two-way-stream input *error-output*))) (acl2::sbcl-restart)))',
                       '--eval', after, '--quit']
            result = subprocess.run(command, env=dict(os.environ, ACL2_CUSTOMIZATION='NONE'),
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
            print(result.stdout)
            lines = {line.strip() for line in result.stdout.splitlines()}
            if fails:
                assert result.returncode != 0, result.stdout
                assert 'CHECKPOINT_TERMINAL_REACHED' not in lines, result.stdout
                assert 'CHECKPOINT_SAVE_ALLOWED' not in lines, result.stdout
                assert 'checkpoint refused' in result.stdout.lower(), result.stdout
            else:
                assert result.returncode == 0, result.stdout
                assert 'CHECKPOINT_TERMINAL_REACHED' in lines, result.stdout
                assert 'CHECKPOINT_SAVE_ALLOWED' in lines, result.stdout
    print('SOURCE CHECKPOINT PROBE PASS: actual ordered admission gates outside-LP save')


if __name__ == '__main__':
    main()
