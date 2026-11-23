"""Actual init/serve forward text; admission remains in ACL2."""
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import fn_admin as admin


class ArticleLimitStartup(unittest.TestCase):
    def test_explicit_option_overrides_ambient_text(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'tools').mkdir()
            (root / 'tools/image-node.lsp').write_text('; no runtime\n')
            args = admin.build_parser().parse_args(['init', str(root / 'node.img'), '--article-max', '00098304'])
            with mock.patch.dict(os.environ, {'FN2_ARTICLE_MAX': '100000'}, clear=True), \
                 mock.patch.object(admin, 'prepare_native_crypto'), \
                 mock.patch.object(admin, 'prepare_native_tls'), \
                 mock.patch.object(admin.subprocess, 'call', return_value=1) as initial:
                admin.cmd_init(args, root)
                self.assertEqual(initial.call_args.kwargs['env']['FN2_ARTICLE_MAX'], '00098304')
            args.article_max = None
            with mock.patch.dict(os.environ, {'FN2_ARTICLE_MAX': '100000'}, clear=True), \
                 mock.patch.object(admin, 'prepare_native_crypto'), \
                 mock.patch.object(admin, 'prepare_native_tls'), \
                 mock.patch.object(admin.subprocess, 'call', return_value=1) as initial:
                admin.cmd_init(args, root)
                self.assertEqual(initial.call_args.kwargs['env']['FN2_ARTICLE_MAX'], '100000')

    def test_raw_text_and_omitted_default_on_both_launch_paths(self):
        for value in (None, '00098304', 'invalid-limit', '4294967296', ''):
            for mode in ('init', 'serve'):
                with self.subTest(value=value, mode=mode), tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    (root / 'tools').mkdir()
                    (root / 'tools/image-node.lsp').write_text('; no runtime\n')
                    image = root / 'node.img'
                    argv = [mode, str(image)] + ([] if value is None else ['--article-max', value])
                    args = admin.build_parser().parse_args(argv)
                    self.assertEqual(args.article_max, value)
                    if mode == 'serve':
                        image.touch()
                    with mock.patch.dict(os.environ, {}, clear=True), \
                         mock.patch.object(admin, 'prepare_native_crypto'), \
                         mock.patch.object(admin, 'prepare_native_tls'), \
                         mock.patch.object(admin.subprocess, 'call', return_value=1) as initial, \
                         mock.patch.object(admin.os, 'chdir'), mock.patch.object(admin.os, 'dup2'), \
                         mock.patch.object(admin.os, 'execve') as served:
                        getattr(admin, 'cmd_' + mode)(args, root)
                        env = initial.call_args.kwargs['env'] if mode == 'init' else served.call_args.args[2]
                    if value is None:
                        self.assertNotIn('FN2_ARTICLE_MAX', env)
                    else:
                        self.assertEqual(env['FN2_ARTICLE_MAX'], value)


if __name__ == '__main__':
    unittest.main()
