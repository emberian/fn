"""Unit tests for the web face's HTTP fuzzer: the independent fake agrees on every case, every plant is caught."""
import json
import random
import tempfile
import unittest
from pathlib import Path

from fn2.tests.surface import http_fuzz


def run(plant=None, seeds='0..999'):
    with tempfile.TemporaryDirectory() as directory:
        code = http_fuzz.main(['--target', 'fake', '--seeds', seeds, '--out', directory] +
                              (['--plant', plant] if plant else []))
        return code, json.loads(Path(directory, 'summary.json').read_text())


class HttpFuzzUnit(unittest.TestCase):
    def test_unmutated_fake_agrees_on_every_case(self):
        code, summary = run()
        self.assertEqual((code, summary['findings']), (0, 0))
        self.assertEqual(set(summary['by_case']), set(http_fuzz.CASES))

    def test_each_plant_is_caught(self):
        for plant in http_fuzz.PLANTS:
            code, summary = run(plant, '0..499')
            self.assertEqual(code, 1, plant)

    def test_requests_carry_one_deviation(self):
        for seed in range(400):
            kind, expected, octets = http_fuzz.request(random.Random(seed), '127.0.0.1:1')
            if kind == 'bare-lf':
                self.assertIn(b'\r\n\r\n', octets)
                self.assertEqual(octets.replace(b'\r\n', b'').count(b'\n'), 1)
            if kind == 'unframed-lf':
                self.assertNotIn(b'\r', octets)
            if kind in ('get-health', 'head-health'):
                self.assertTrue(octets.endswith(b'\r\n\r\n'))


if __name__ == '__main__':
    unittest.main()
