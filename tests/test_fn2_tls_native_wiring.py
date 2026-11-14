#!/usr/bin/env python3
"""The served image must load the actual TLS controller before its raw caller."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import certs


class NativeTLSWiring(unittest.TestCase):
    def test_served_image_includes_actual_transport_and_ownership(self):
        books = certs.closure(ROOT, 'books/node-profile')
        self.assertTrue({'books/tls-transport-state', 'books/tls-transport-ops',
                         'books/tls-transport', 'books/tls-transport-reservation'} <= books.keys())


if __name__ == '__main__':
    unittest.main()
