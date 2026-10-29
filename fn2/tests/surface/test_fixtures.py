"""Unit tests for the E fixture drivers' parsing and comparators (no node; the live replay runs on hbox)."""
import json
import tempfile
import unittest
from pathlib import Path

from fn2.tests.surface import ROOT, fixtures

RFC = ROOT / 'fn2/tests/model/fixtures/rfc3977'
ARTICLE = (b'From: "Demo User" <nobody@example.net>\r\nNewsgroups: misc.test\r\n'
           b'Subject: I am just a test article\r\nDate: 6 Oct 1998 04:38:40 -0500\r\n'
           b'Organization: An Example Net, Uncertain, Texas\r\nMessage-ID: <45223423@example.com>\r\n'
           b'\r\nThis is just a test article.\r\n')


def expected(name):
    return fixtures.exchanges(fixtures.transcript(RFC / name))[1][0][1]


class FixtureDriverUnit(unittest.TestCase):
    def test_every_transcript_parses(self):
        files = sorted(RFC.glob('*.txt'))
        self.assertEqual(len(files), 17)
        for path in files:
            greeting, steps = fixtures.exchanges(fixtures.transcript(path))
            self.assertTrue(greeting or steps, path.name)
            for command, reply in steps:
                self.assertTrue(reply, (path.name, command))

    def test_example_article_drops_path_only(self):
        article = fixtures.example_article(fixtures.transcript(RFC / 'article-msgid.txt'))
        self.assertEqual(article, ARTICLE)

    def test_article_compare_and_its_controls(self):
        setup = {'groups': fixtures.SETUP_GROUPS}
        served = b'Path: node!not-for-mail\r\nXref: node misc.test:1\r\n' + ARTICLE
        status = b'220 0 <45223423@example.com> article follows\r\n'
        self.assertTrue(fixtures._compare(expected('article-msgid.txt'), status, served, setup)[0])
        for wrong_status, wrong_block in [
                (b'220 1 <45223423@example.com>\r\n', served),                 # number by Message-ID is 0
                (b'220 0 <other@example.com>\r\n', served),                    # echo
                (status, served.replace(b'Subject: I am', b'Subject: We are')),  # a header value
                (status, served.replace(b'test article.\r\n', b'test article!\r\n')),  # body octets
                (b'430 no\r\n', b'')]:
            self.assertFalse(fixtures._compare(expected('article-msgid.txt'), wrong_status, wrong_block, setup)[0],
                             (wrong_status, wrong_block))
        body = b'This is just a test article.\r\n'
        self.assertTrue(fixtures._compare(expected('body-msgid.txt'), b'222 0 <45223423@example.com>\r\n', body, setup)[0])
        self.assertFalse(fixtures._compare(expected('body-msgid.txt'), b'222 0 <45223423@example.com>\r\n', body + b'x\r\n', setup)[0])

    def test_empty_group_rule_and_listings(self):
        setup = {'groups': fixtures.SETUP_GROUPS}
        rows = expected('empty-group.txt')
        self.assertTrue(fixtures._compare(rows, b'211 0 1 0 example.currently.empty.newsgroup\r\n', b'', setup)[0])
        self.assertFalse(fixtures._compare(rows, b'211 0 1 1 example.currently.empty.newsgroup\r\n', b'', setup)[0])
        self.assertFalse(fixtures._compare(rows, b'211 0 1 0 other.group\r\n', b'', setup)[0])
        block = b''.join(g.encode() + b' 0 1 y\r\n' for g in fixtures.SETUP_GROUPS)
        self.assertTrue(fixtures._compare(expected('newgroups-empty.txt'), b'231 list\r\n', block, setup)[0])
        self.assertFalse(fixtures._compare(expected('newgroups-empty.txt'), b'231 list\r\n', block + b'x.y 0 1 y\r\n', setup)[0])
        ids = b'<i.am.another.new.article@example.com>\r\n<i.am.a.new.article@example.com>\r\n'
        self.assertTrue(fixtures._compare(expected('newnews.txt'), b'230 ok\r\n', ids, setup)[0])
        self.assertFalse(fixtures._compare(expected('newnews.txt'), b'230 ok\r\n', ids.split(b'\r\n')[0] + b'\r\n', setup)[0])
        self.assertTrue(fixtures._compare(expected('newnews-empty.txt'), b'230 ok\r\n', b'', setup)[0])

    def test_rfc7677_vector_and_a_wrong_one(self):
        rows = fixtures.scram_vectors(ROOT / 'fn2/tests/fixtures/scram')
        self.assertEqual([r['ok'] for r in rows], [True, True, True])
        with tempfile.TemporaryDirectory() as directory:
            v = json.loads((ROOT / 'fn2/tests/fixtures/scram/rfc7677.json').read_text())
            v['password'] = 'pencils'
            (Path(directory) / 'wrong.json').write_text(json.dumps(v))
            self.assertEqual([r['ok'] for r in fixtures.scram_vectors(Path(directory))], [True, False, False])

    def test_absent_fixture_is_a_named_skip_and_unknown_is_an_error(self):
        case = unittest.TestCase()
        with self.assertRaisesRegex(unittest.SkipTest, 'fixture absent'):
            fixtures.fixture(case=case, target='fn1', family='web', out='/nonexistent',
                             path=ROOT / 'fn2/tests/fixtures/web', contract='E5')
        with self.assertRaisesRegex(ValueError, 'no fixture driver'):
            fixtures.fixture(case=case, target='fn1', family='web', out='/nonexistent',
                             path=ROOT / 'nowhere', contract='-')


if __name__ == '__main__':
    unittest.main()
