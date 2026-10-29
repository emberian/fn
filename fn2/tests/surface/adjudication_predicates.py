"""Named, fail-closed predicates for adjudicated NNTP difference classes.

Rule, detail and recorded reply bytes are still checked by the ledger loader.
A closure classification additionally needs the exchange that caused it: the
unanswered command alone says nothing about whether closing was permitted.
"""
import re

from fn2.tests.model import framing
from fn2.tests.model.nntp_model import msgid


def _octets(row, key):
    try:
        return bytes.fromhex(row[key])
    except (KeyError, TypeError, ValueError):
        return None


def _command(row):
    data = _octets(row, 'command_hex')
    if data is None:
        return None
    try:
        return framing.command_line(data)
    except ValueError:
        return None


def invalid_keyword(row):
    """RFC 3977 section 9.8: ALPHA 2*(ALPHA / DIGIT / '.' / '-')."""
    command = _command(row)
    if command is None or command[:1] in b' \t':
        return False
    token = re.split(rb'[ \t]+', command, maxsplit=1)[0]
    return re.fullmatch(rb'[A-Za-z][A-Za-z0-9.-]{2,}', token) is None


def _malformed_transit(row, verbs):
    command = _command(row)
    if command is None or command[:1] in b' \t':
        return False
    parts = re.split(rb'[ \t]+', command)
    if parts[0].upper() not in verbs:
        return False
    try:
        valid = len(parts) == 2 and msgid(parts[1].decode('utf-8'))
    except UnicodeError:
        valid = False
    return not valid


def malformed_reader_transit(row):
    return (row.get('mode', row.get('role')) in ('reader', 'node')
            and _malformed_transit(row, (b'IHAVE', b'CHECK', b'TAKETHIS')))


def _exchanges(row):
    """Only accept a prefix whose final exchange is this difference."""
    exchanges = row.get('exchanges')
    if not isinstance(exchanges, list):
        return []
    for index, exchange in enumerate(exchanges):
        if not isinstance(exchange, dict):
            return []
        if (exchange.get('command_index') == row.get('command_index')
                and exchange.get('command_hex') == row.get('command_hex')):
            status = _octets(exchange, 'status_hex')
            body = _octets(exchange, 'body_hex') if exchange.get('body_hex') else b''
            if status is None or body is None or (status + body)[:1024] != _octets(row, 'reply_hex'):
                return []
            return exchanges[:index + 1]
    return []


def _wire(row, exchange, name, default=None):
    keys = {'eof': 'wire_eof', 'timeout': 'wire_timeout', 'reset': 'wire_reset',
            'client_half_closed': 'client_half_closed'}
    return exchange.get(keys[name], row.get('wire', {}).get('reply_' + name, default))


def _structurally_malformed(command):
    try:
        framing.command_line(command).decode('utf-8')
    except (ValueError, UnicodeError):
        return True
    return False


def preceding_501_close(row):
    exchanges = _exchanges(row)
    if len(exchanges) < 2 or _octets(row, 'reply_hex') != b'':
        return False
    previous, current = exchanges[-2:]
    command = _octets(previous, 'command_hex')
    status = _octets(previous, 'status_hex')
    return bool(command and status and status.startswith(b'501 ')
                and status.endswith(b'\r\n') and _structurally_malformed(command)
                and _wire(row, current, 'eof') is True
                and _wire(row, current, 'timeout') is False
                and _wire(row, current, 'reset') is None
                and not _wire(row, current, 'client_half_closed', False))


def malformed_takethis_wait(row):
    exchanges = _exchanges(row)
    current = exchanges[-1] if exchanges else {}
    return (row.get('mode', row.get('role')) == 'peer'
            and _malformed_transit(row, (b'TAKETHIS',))
            and _octets(row, 'reply_hex') == b''
            and _wire(row, current, 'timeout') is True
            and _wire(row, current, 'eof') is False
            and _wire(row, current, 'reset') is None
            and not _wire(row, current, 'client_half_closed', False))


def rejected_article_continuation(row):
    exchanges = _exchanges(row)
    if len(exchanges) < 2:
        return False
    for exchange in exchanges[:-1]:
        command = _octets(exchange, 'command_hex')
        status = _octets(exchange, 'status_hex')
        if command is None or status is None:
            return False
        if (command.upper().startswith(b'QUIT\r\n') or status[:3] == b'205'
                or exchange.get('wire_eof') or exchange.get('wire_reset')):
            return False
    previous = exchanges[-2]
    block = _octets(previous, 'command_hex')
    status = _octets(previous, 'status_hex')
    # These H2d rows concern NUL in a complete, rejected article, not every
    # reason a peer might close, and never an unterminated TLS half-close.
    return (b'\0' in block and block.endswith(b'\r\n.\r\n')
            and status[:3] == {'POST': b'441', 'IHAVE': b'437', 'TAKETHIS': b'439'}.get(previous.get('rule'))
            and not previous.get('client_half_closed', False))


PREDICATES = {
    'A13-invalid-keyword': invalid_keyword,
    'A15-malformed-reader-transit': malformed_reader_transit,
    'H2d-preceding-501-close': preceding_501_close,
    'H2d-malformed-takethis-wait': malformed_takethis_wait,
    'H2d-rejected-article-continuation': rejected_article_continuation,
}
