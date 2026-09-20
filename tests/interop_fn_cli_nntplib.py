"""Read one article back through a live `fn run`, with the standard library.

nntplib was removed in Python 3.13, so this probe runs under an explicitly
named older interpreter and is skipped when it is absent (the pattern
tests/interop_post_nntplib.py established).  It imports no fn module: the
framing and response parsing here are nntplib's, not fn's.
"""
import argparse
import nntplib


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("port", type=int)
    parser.add_argument("group")
    parser.add_argument("message_id")
    args = parser.parse_args()
    with nntplib.NNTP("127.0.0.1", port=args.port, timeout=20) as client:
        assert client.getwelcome().startswith("201 "), client.getwelcome()
        _, count, first, last, name = client.group(args.group)
        assert name == args.group and count >= 1, (count, first, last, name)
        _, number, found = client.stat(str(last))
        assert found == args.message_id, (number, found)
        _, info = client.article(str(last))
        text = b"\r\n".join(info.lines)
        assert args.message_id.encode("ascii") in text, text
        assert client.quit().startswith("205 ")
    print("read {} from {}".format(args.message_id, args.group))


if __name__ == "__main__":
    main()
