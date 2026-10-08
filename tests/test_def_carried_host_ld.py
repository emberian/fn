"""The def-carried host-ld manifest, in an actual ACL2 world (local cert needed)."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = '''
(include-book "{book}")
(defstobj cd-s (cd-n :type integer :initially 0))
(defun cd-inv (cd-s) (declare (xargs :stobjs cd-s)) (equal (cd-n cd-s) 1))
(defun cd-open (cd-s) (declare (xargs :stobjs cd-s)) (update-cd-n 1 cd-s))
(defthm cd-open-establishes (cd-inv (cd-open cd-s)))
{before}
(def-carried cd-row :invariant cd-inv
 :established ((cd-open cd-open-establishes :witness ('(0))))
 :incomplete (A-TEST-OWED (cd-later)) :trace nil)
{after}
(def-carried-host-check "{manifest}")
(value-triple (cw "CD_HOST_LD_FINISHED~%"))
'''
VALID = '(defun cd-later (cd-s) (declare (xargs :stobjs cd-s)) cd-s)'
STALE = '(defun cd-later (x) x)'


class CarriedHostLd(unittest.TestCase):
    def run_world(self, before='', after=''):
        with tempfile.TemporaryDirectory(prefix='carried-host-ld-', dir=ROOT / 'build') as tmp:
            manifest = Path(tmp) / 'manifest.lsp'
            driver = Path(tmp) / 'host.lisp'
            driver.write_text(FIXTURE.format(before=before, after=after,
                                             manifest=manifest, book=ROOT / 'books/def-carried'))
            env = dict(os.environ, ACL2_CUSTOMIZATION='NONE', ACL2_BOOK_HASH_ALISTP='NIL')
            proc = subprocess.run(
                [sys.executable, str(ROOT / 'tools/acl2'), '--timeout', '60',
                 '--label', 'carried-host-ld-test'], cwd=ROOT, env=env,
                input=f'(ld "{driver}" :ld-error-action :error)\n(good-bye)\n',
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=90)
            self.assertEqual(proc.returncode, 0, proc.stdout[-4000:])
            self.assertNotIn('Warning [Uncertified]', proc.stdout)
            return proc.stdout, manifest.read_text() if manifest.exists() else None

    def test_absent_writer_is_deferred_but_host_ld_refuses(self):
        output, manifest = self.run_world()
        self.assertIn('left to host-ld (CD-LATER)', output)
        self.assertIn('stale owed names', output)
        self.assertNotIn('CD_HOST_LD_FINISHED', output)
        self.assertIn('ACL2 Error', output)
        self.assertIn(':LEFT-TO-HOST-LD (CD-LATER)', ' '.join(manifest.split()))

    def test_deferred_writer_with_wrong_result_is_refused(self):
        output, manifest = self.run_world(after=STALE)
        self.assertIn('stale owed names', output)
        self.assertNotIn('CD_HOST_LD_FINISHED', output)
        self.assertIn('ACL2 Error', output)
        self.assertIsNotNone(manifest)

    def test_valid_deferred_writer_passes_both(self):
        output, manifest = self.run_world(after=VALID)
        self.assertIn('left to host-ld (CD-LATER)', output)
        self.assertNotIn('ACL2 Error', output)
        self.assertIn(':CARRIED-HOST-LD-CHECKED', output)
        self.assertIn('CD_HOST_LD_FINISHED', output)
        self.assertIn(':LEFT-TO-HOST-LD (CD-LATER)', ' '.join(manifest.split()))

    def test_in_world_stale_writer_fails_declaration(self):
        output, _ = self.run_world(before=STALE)
        self.assertIn('a stale owed name', output)
        self.assertIn('ACL2 Error', output)
        self.assertNotIn('def-carried CD-ROW: left to host-ld', output)


if __name__ == '__main__':
    unittest.main()
