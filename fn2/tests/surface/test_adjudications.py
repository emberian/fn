"""Class adjudication controls; a known policy is not a wildcard exemption."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from fn2.tests import surface
from fn2.tests.surface.adjudication_predicates import PREDICATES


class TestAdjudications(unittest.TestCase):
    @staticmethod
    def row(command=b'.\r\n', reply=b'501 syntax error\r\n', **kwargs):
        return dict(command_hex=command.hex(), reply_hex=reply.hex(), rule='unknown',
                    detail='code 501; permitted [500]', **kwargs)

    @staticmethod
    def exchange(index, command, reply, **kwargs):
        return dict(command_index=index, command_hex=command.hex(), status_hex=reply.hex(),
                    body_hex=None, **kwargs)

    def test_three_new_dot_rows_are_recorded_A13(self):
        rows = [self.row(cut=cut) for cut in ('whole', 'byte', 'random')]
        for target in ('fn1', 'fn2'):
            judged = surface.adjudicate_differences(rows, target)
            self.assertEqual([r['disposition'] for r in judged], ['recorded'] * 3)
            self.assertEqual([r['match'] for r in judged], ['A13-invalid-keyword'] * 3)

    def test_A13_keyword_grammar_and_planted_new_class(self):
        for command in (b'.\r\n', b'X:\r\n', b'A\r\n', b'AB\r\n', b'9NEW\r\n', b'X_ABC\r\n'):
            with self.subTest(command=command):
                self.assertEqual(surface.adjudicate_differences([self.row(command)], 'fn1')[0]['disposition'], 'recorded')
        for command in (b'XNEW\r\n', b'ABC\r\n', b'X-7.2\r\n', b' x:y\r\n', b'X:\n', b'X:\0\r\n'):
            with self.subTest(command=command):
                self.assertEqual(surface.adjudicate_differences([self.row(command)], 'fn1')[0]['disposition'], 'new')
        for delta in (dict(rule='DATE'), dict(detail='new reason'), dict(reply_hex=b'502 forbidden\r\n'.hex())):
            self.assertEqual(surface.adjudicate_differences([dict(self.row(), **delta)], 'fn1')[0]['disposition'], 'new')

    def test_H7_01_arguments_past_497_within_512(self):
        reply = b'381 password required\r\n'
        def judged(arg):
            row = dict(self.row(b'AUTHINFO user ' + arg + b'\r\n', reply), rule='syntax',
                       detail='code 381; permitted [501]')
            return surface.adjudicate_differences([row], 'fn2')[0]['disposition']
        self.assertEqual(judged(b'x' * 495), 'recorded')     # 500 octets of arguments in a 511-octet line
        self.assertEqual(judged(b'x' * 492), 'new')          # 497 octets of arguments: not this class
        self.assertEqual(judged(b'x' * 497), 'new')          # a 513-octet line: past the line bound

    def test_H7_02_to_05_examples_recorded_and_controls_new(self):
        import json
        groups = {g['group']: g for g in json.loads(
            (Path(surface.__file__).parents[1] / 'model/adjudications.json').read_text())['groups']}
        def judged(group, command, target='fn1', reply=None):
            g = groups[group]
            row = dict(command_hex=command.hex(), reply_hex=reply.hex() if reply else g['reply_patterns'][0],
                       rule=g['rule'], detail=g['detail'], mode='peer')
            return surface.adjudicate_differences([row], target)[0]['disposition']
        for group in ('H7-02', 'H7-03', 'H7-04', 'H7-05'):
            self.assertEqual(judged(group, bytes.fromhex(groups[group]['command_example'])), 'recorded', group)
        self.assertEqual(judged('H7-03', bytes.fromhex(groups['H7-03']['command_example']), 'fn2'), 'new')  # fn1-bug
        self.assertEqual(judged('H7-02', b'GROUP fn.test\r\n'), 'new')
        self.assertEqual(judged('H7-04', b'IHAVE <a@b.c>\r\n'), 'new')
        self.assertEqual(judged('H7-05', b'Path: x\r\n\r\nclean\r\n.\r\n'), 'new')
        self.assertEqual(judged('H7-03', b'TAKETHIS <a@b>\r\n'), 'new')

    def test_H7_07_needs_its_preceding_exchange(self):
        def row(previous, previous_status, command, reply, rule, detail):
            exchanges = [self.exchange(0, previous, previous_status), self.exchange(1, command, reply)]
            return dict(command_index=1, command_hex=command.hex(), reply_hex=reply.hex(), rule=rule,
                        detail=detail, exchanges=exchanges)
        r481 = b'481 authentication failed\r\n'
        xr = row(b'XREDEEM code code\r\n', b'381 send the password with XREDEEM PASS\r\n',
                 b'AUTHINFO PASS fuzz-password\r\n', r481, 'AUTHINFO', 'code 481; permitted [482]')
        self.assertEqual(surface.adjudicate_differences([xr], 'fn1')[0]['disposition'], 'recorded')
        self.assertEqual(surface.adjudicate_differences([xr], 'fn2')[0]['disposition'], 'new')      # fn1-bug
        user = row(b'AUTHINFO USER fuzz\r\n', b'381 password required\r\n',
                   b'AUTHINFO PASS fuzz-password\r\n', r481, 'AUTHINFO', 'code 481; permitted [482]')
        self.assertEqual(surface.adjudicate_differences([user], 'fn1')[0]['disposition'], 'new')

    def test_H7_08_bytewise_early_refusal_only(self):
        article = b'Path: not-for-mail\r\nX-Long: ' + b'v' * 40000 + b'\r\n\r\nx\r\n.\r\n'
        def row(cut, eof=True, body=article):
            return dict(command_hex=body.hex(), reply_hex='', rule='TAKETHIS', cut=cut, wire_eof=eof,
                        detail='wrong number of status lines (including closing 400)')
        self.assertEqual(surface.adjudicate_differences([row('bytewise')], 'fn1')[0]['disposition'], 'recorded')
        self.assertEqual(surface.adjudicate_differences([row('bytewise')], 'fn2')[0]['disposition'], 'new')
        self.assertEqual(surface.adjudicate_differences([row('whole')], 'fn1')[0]['disposition'], 'new')
        self.assertEqual(surface.adjudicate_differences([row('bytewise', False)], 'fn1')[0]['disposition'], 'new')
        self.assertEqual(surface.adjudicate_differences([row('bytewise', body=article[:2000])], 'fn1')[0]['disposition'], 'new')

    def test_A15_requires_reader_and_malformed_transit_argument(self):
        def row(command, mode):
            return dict(self.row(command, b'502 transit is not permitted on this connection\r\n', mode=mode),
                        rule='syntax', detail='code 502; permitted [501]')
        for mode in ('reader', 'node'):
            for verb in (b'IHAVE', b'CHECK', b'TAKETHIS'):
                judged = surface.adjudicate_differences([row(verb + b' <bad\r\n', mode)], 'fn2')[0]
                self.assertEqual((judged['disposition'], judged['match']), ('recorded', 'A15-malformed-reader-transit'))
        for command, mode in ((b'TAKETHIS <bad\r\n', 'peer'), (b'CHECK <a@b>\r\n', 'reader'),
                              (b'DATE x\r\n', 'reader'), (b'CHECK <bad\r\n', None)):
            self.assertEqual(surface.adjudicate_differences([row(command, mode)], 'fn1')[0]['disposition'], 'new')

    def close_row(self):
        command = b'CAPABILITIES\r\n'
        exchanges = [self.exchange(0, b'DATE ' + b'x' * 520 + b'\r\n', b'501 syntax error\r\n'),
                     self.exchange(1, command, b'', wire_eof=True, wire_timeout=False,
                                   wire_reset=None, client_half_closed=False)]
        return dict(command_hex=command.hex(), reply_hex='', rule='CAPABILITIES',
                    detail='wrong number of status lines (including closing 400)',
                    command_index=1, mode='reader', exchanges=exchanges)

    def test_close_class_requires_causal_command_and_clean_eof(self):
        row = self.close_row()
        judged = surface.adjudicate_differences([row], 'fn1')[0]
        self.assertEqual((judged['disposition'], judged['match']), ('recorded', 'H2d-preceding-501-close'))
        self.assertEqual(surface.adjudicate_differences([row], 'fn2')[0]['disposition'], 'new')
        for command in (b'HEAD <a\rb>\r\n', b'DATE \xff\r\n', b'DATE \0\r\n'):
            row['exchanges'][0]['command_hex'] = command.hex()
            self.assertEqual(surface.adjudicate_differences([row], 'fn1')[0]['disposition'], 'recorded')
        for command in (b'DATE extra\r\n', b'BODY -1\r\n'):
            row['exchanges'][0]['command_hex'] = command.hex()
            self.assertEqual(surface.adjudicate_differences([row], 'fn1')[0]['disposition'], 'new')
        for delta in (dict(wire_eof=False), dict(wire_eof=None), dict(wire_timeout=True),
                      dict(wire_timeout=None), dict(wire_reset='reset'), dict(client_half_closed=True)):
            row = self.close_row()
            row['exchanges'][-1].update(delta)
            self.assertEqual(surface.adjudicate_differences([row], 'fn1')[0]['disposition'], 'new')

    def test_no_context_does_not_fall_back_to_superseded_H2c(self):
        row = self.close_row()
        row.pop('exchanges')
        judged = surface.adjudicate_differences([row], 'fn2')[0]
        self.assertEqual((judged['disposition'], judged['group']), ('new', None))

    def test_malformed_takethis_prefix_timeout_is_not_eof(self):
        row = dict(command_hex=b'TAKETHIS <fresh\r\n'.hex(), reply_hex='', rule='syntax',
                   detail='wrong number of status lines (including closing 400)', mode='peer',
                   wire=dict(reply_timeout=True, reply_eof=False, reply_reset=None))
        self.assertEqual(surface.adjudicate_differences([row], 'fn1')[0]['match'], 'H2d-malformed-takethis-wait')
        for delta in (dict(reply_eof=True), dict(reply_timeout=False), dict(reply_reset='reset')):
            changed = dict(row, wire=dict(row['wire'], **delta))
            self.assertEqual(surface.adjudicate_differences([changed], 'fn1')[0]['disposition'], 'new')
        self.assertEqual(surface.adjudicate_differences([dict(row, mode='reader')], 'fn1')[0]['disposition'], 'new')

    def test_rejected_article_may_continue_but_QUIT_may_not(self):
        row = dict(command_hex=b'LAST\r\n'.hex(), reply_hex=b'412 no newsgroup selected\r\n'.hex(),
                   rule='closed', detail='expected no reply and no framing', command_index=1,
                   exchanges=[self.exchange(0, b'From: x\0\r\n\r\n.\r\n', b'439 rejected\r\n', rule='TAKETHIS'),
                              self.exchange(1, b'LAST\r\n', b'412 no newsgroup selected\r\n')])
        self.assertEqual(surface.adjudicate_differences([row], 'fn1')[0]['match'], 'H2d-rejected-article-continuation')
        row['exchanges'].insert(0, self.exchange(-1, b'QUIT\r\n', b'205 closing\r\n'))
        self.assertEqual(surface.adjudicate_differences([row], 'fn1')[0]['disposition'], 'new')
        row['exchanges'].pop(0)
        row['exchanges'][0]['command_hex'] = b'From: x\0\r\n'.hex()
        self.assertEqual(surface.adjudicate_differences([row], 'fn1')[0]['disposition'], 'new')

    def test_reproducer_context_is_bound_to_row_and_directory(self):
        saved = self.close_row()
        row = {k: v for k, v in saved.items() if k != 'exchanges'}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'repro.json'
            path.write_text(json.dumps(saved))
            row['reproducer'] = path.name
            self.assertEqual(surface.adjudicate_differences([row], 'fn1', directory)[0]['disposition'], 'recorded')
            for name in (str(path), '../repro.json'):
                self.assertEqual(surface.adjudicate_differences([dict(row, reproducer=name)], 'fn1', directory)[0]['disposition'], 'new')
            saved['mode'] = 'peer'
            path.write_text(json.dumps(saved))
            self.assertEqual(surface.adjudicate_differences([row], 'fn1', directory)[0]['disposition'], 'new')

    def test_schema_rejects_unknown_or_competing_matchers(self):
        ledger = json.loads((surface.ROOT / 'fn2/tests/model/adjudications.json').read_text())
        for change in (dict(match='typo'), dict(command_pattern='00')):
            group = dict(next(g for g in ledger['groups'] if 'match' in g), **change)
            with mock.patch.object(surface.json, 'loads', return_value=dict(schema_version=2, groups=[group])):
                with self.assertRaises(ValueError):
                    surface.adjudicate_differences([], 'fn1')

    def test_exact_classes_remain_exact_and_table_is_covered(self):
        ledger = json.loads((surface.ROOT / 'fn2/tests/model/adjudications.json').read_text())
        self.assertEqual({g['match'] for g in ledger['groups'] if 'match' in g}, set(PREDICATES))
        for group in ledger['groups']:
            self.assertNotEqual('match' in group, 'command_pattern' in group)
        group = next(g for g in ledger['groups'] if g['group'] == 'H2d-24')
        row = dict(rule=group['rule'], detail=group['detail'], command_hex=group['command_pattern'], reply_hex=group['reply_patterns'][0])
        self.assertEqual(surface.adjudicate_differences([row], 'fn1')[0]['disposition'], 'recorded')
        self.assertEqual(surface.adjudicate_differences([dict(row, command_hex='00')], 'fn1')[0]['disposition'], 'new')


if __name__ == '__main__':
    unittest.main()
