"""Batched pair reads preserve the per-pair verdicts and fail-closed path."""

import hashlib
from pathlib import Path
import sqlite3
import tempfile
import unittest
from unittest import mock

from tests.test_certs import certs


class PairLookupTests(unittest.TestCase):
    def test_batch_matches_scalar_queries_with_duplicates_misses_and_other_prover(self):
        with tempfile.TemporaryDirectory() as directory:
            connection = certs._pair_index(Path(directory))
            self.addCleanup(connection.close)
            prover = certs._pair_prover(connection, "acl2")
            other = certs._pair_prover(connection, "other-acl2")
            digests = [hashlib.sha256(str(i).encode()).digest() for i in range(10)]
            rows = [(prover, digests[0], digests[i + 1], required, equal)
                    for i, (required, equal) in enumerate(((0, 0), (0, 1), (1, 0), (1, 1)))]
            rows += [(other, digests[0], digests[5], 1, 1),
                     (prover, digests[8], digests[9], 1, 1)]
            connection.executemany("INSERT INTO facts VALUES (?, ?, ?, ?, ?)", rows)
            keys = [(digests[0], digests[i]) for i in (5, 4, 3, 2, 1, 1, 6)]
            expected = {}
            for key in keys:
                row = connection.execute(
                    "SELECT required, equal FROM facts WHERE prover=? AND parent=? AND child=?",
                    (prover, *key)).fetchone()
                if row is not None:
                    expected[key] = tuple(map(bool, row))
            statements = []
            connection.set_trace_callback(statements.append)
            self.assertEqual(certs._pair_lookup(connection, prover, iter(keys)), expected)
            self.assertEqual(sum(s.startswith("SELECT ") for s in statements), 1)
            self.assertFalse(connection.in_transaction)
            self.assertEqual(certs._pair_lookup(connection, prover, []), {})
            self.assertEqual(connection.execute("SELECT count(*) FROM facts").fetchone(), (6,))

    def test_failed_batch_rolls_back_and_connection_can_be_reused(self):
        with tempfile.TemporaryDirectory() as directory:
            connection = certs._pair_index(Path(directory))
            self.addCleanup(connection.close)
            def interrupted():
                yield (b"a", b"b")
                raise sqlite3.OperationalError("fixture interrupted request")
            with self.assertRaises(sqlite3.OperationalError):
                certs._pair_lookup(connection, 1, interrupted())
            self.assertFalse(connection.in_transaction)
            self.assertEqual(certs._pair_lookup(connection, 1, []), {})

    def test_memo_keeps_candidate_indices_misses_and_log_fallback(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cache = root / "cache"
            paths = [root / f"{i}.cert" for i in range(4)]
            for path, content in zip(paths, (b"parent", b"parent", b"child", b"other")):
                path.write_bytes(content)
            calls = []
            def probe(paths, pairs, acl2, root):
                calls.append(list(pairs))
                # No read transaction may survive into the ACL2 probe.
                connection = sqlite3.connect(cache / certs.PAIR_DB, timeout=0)
                try:
                    connection.execute("BEGIN IMMEDIATE")
                    connection.rollback()
                finally:
                    connection.close()
                return {pair: (True, pair[1] == 2) for pair in pairs}
            checker = certs.memoized_pair_checker(cache, probe)
            acl2 = root / "acl2"
            self.assertEqual(checker(paths, [(0, 2)], acl2, root), {(0, 2): (True, True)})
            pairs = [(0, 2), (1, 2), (1, 3)]
            expected = {(0, 2): (True, True), (1, 2): (True, True), (1, 3): (True, False)}
            self.assertEqual(checker(paths, pairs, acl2, root), expected)
            self.assertEqual((checker.hits, checker.probed), (2, 1))
            self.assertEqual(calls, [[(0, 2)], [(1, 3)]])
            with mock.patch.object(certs, "_pair_lookup", side_effect=sqlite3.OperationalError):
                self.assertEqual(checker(paths, pairs, acl2, root), expected)
            self.assertEqual((checker.hits, checker.probed), (3, 0))
            self.assertEqual(len(calls), 2)


if __name__ == "__main__":
    unittest.main()
