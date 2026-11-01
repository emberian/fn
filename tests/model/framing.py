"""Pure octet framing; RFC 3977 §§3.1, 3.1.1 and specs/nntp.md:512-537.

stuff/unstuff are byte transforms even for non-protocol binary data. The
encode/decode_block functions additionally enforce the protocol's line grammar.
No normalization of bare LF, bare CR, NUL, or missing final CRLF is performed.
"""
import re

CRLF = b"\r\n"
TERMINATOR = b".\r\n"
COMMAND_LIMIT = 512


class FramingError(ValueError):
    pass


def stuff(data: bytes) -> bytes:
    return re.sub(rb"(^|\r\n)\.", rb"\1..", data)


def unstuff(data: bytes) -> bytes:
    return re.sub(rb"(^|\r\n)\.\.", rb"\1.", data)


def lines(data: bytes) -> list[bytes]:
    """Split complete, unstuffed protocol lines, rejecting non-line octets."""
    if not data:
        return []
    if not data.endswith(CRLF):
        raise FramingError("missing CRLF")
    result = data[:-2].split(CRLF)
    if any(b"\r" in x or b"\n" in x or b"\0" in x for x in result):
        raise FramingError("bare CR, bare LF or NUL")
    return result


def encode_block(data: bytes) -> bytes:
    lines(data)
    return stuff(data) + TERMINATOR


def decode_block(block: bytes) -> bytes:
    rows = lines(block)
    if not rows or rows[-1] != b".":
        raise FramingError("missing dot terminator")
    if any(x == b"." for x in rows[:-1]):
        raise FramingError("octets after dot terminator")
    if any(x.startswith(b".") and not x.startswith(b"..") for x in rows[:-1]):
        raise FramingError("unescaped leading dot")
    return unstuff(block[:-3])


def command_line(line: bytes) -> bytes:
    if len(line) > COMMAND_LIMIT:
        raise FramingError("command exceeds 512 octets including CRLF")
    rows = lines(line)
    if len(rows) != 1 or not rows[0]:
        raise FramingError("expected exactly one nonempty command line")
    return rows[0]


def split_commands(data: bytes) -> tuple[list[bytes], bytes]:
    """Pure chunk splitter; caller stops consuming at QUIT/TLS/body boundary.

    Incomplete suffix is retained, including a trailing CR. Validation belongs
    to command_line, so arbitrary socket fragmentation has no semantic effect.
    """
    pieces = data.split(CRLF)
    return [x + CRLF for x in pieces[:-1]], pieces[-1]
