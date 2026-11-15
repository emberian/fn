"""Source controls only; no claim that the full SIM exchange has executed."""
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'tests/checkpoint-live-network-prefix-support.lisp'

class NetworkPrefix(unittest.TestCase):
    def test_real_external_network_io(self):
        source = SOURCE.read_text()
        for call in ('fn2-network-client-byte', 'fn2-network-client-read',
                     'fn2-sim-next-flight', 'fn2-sim-advance-selected',
                     'fn2-sim-take-prefix', 'fn2-b-turn'):
            self.assertIn('(' + call + ' ', source)
        self.assertIn('(fn2-sim-advance-selected nil accept', source)
        self.assertNotIn('fn2-sim-client-drain', source)
        advance = source.index('(fn2-sim-advance-selected nil accept')
        following = source[advance:source.index('(defun fn2-cln-exchange')]
        self.assertIn('(fn2-b-turn fn2-core)', following)

    def test_reply_derived_subject_and_order(self):
        source = SOURCE.read_text()
        begin = source.index('(defun fn2-cln-register-append ')
        end = source.index('(defun fn2-cln-prefix-to-held ')
        body = source[begin:end]
        self.assertLess(body.index('(fnc-register consumer 1)'), body.index('(fnc-append op article)'))
        self.assertIn("(fnc-reply-cursor 'register registered)", body)
        self.assertIn("(result (fnc-reply 'append appended))", body)
        wrapper = source[end:]
        self.assertLess(wrapper.index('(fn2-cln-register-append '), wrapper.index('(fn2-clc-prefix-to-held '))
        self.assertIn('((unless (eq prefix :complete))', wrapper)

    def test_no_internal_authority_or_store_copy(self):
        source = SOURCE.read_text()
        for forbidden in ('fn2-core-put', 'fn2-cw-', 'fn2-idc-', 'fn2-run-install',
                          'fn2-sim-crash', 'update-fn2-', 'fn2-machine-put', 'fn2-commit-admit'):
            self.assertNotIn(forbidden, source)
        self.assertIn('((unless unused) (mv :cap nil 0 0', source)
        self.assertIn('((when (and (posp nonce) (not (= nonce actual))))', source)

if __name__ == '__main__':
    unittest.main()
