"""Independent NNTP client probe (requires Python <=3.12's stdlib nntplib).

Start tools/run_reader.py separately, then pass its printed loopback port. This
is reader-only interoperability evidence, not a full RFC conformance audit.
"""
import argparse
import json
import nntplib
import platform


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("port", type=int)
    args = parser.parse_args()
    if not 0 < args.port <= 65535:
        parser.error("port must be from 1 through 65535")
    message_id = "<reader@example.invalid>"
    with nntplib.NNTP("127.0.0.1", port=args.port, timeout=10) as client:
        assert client.getwelcome().startswith("201 "), client.getwelcome()
        caps = client.getcapabilities()
        assert caps["VERSION"] == ["2"], caps
        assert "READER" not in caps and "POST" not in caps, caps
        response, count, first, last, name = client.group("fn.letters")
        assert (count, first, last, name) == (1, 1, 1, "fn.letters")
        response, number, msgid = client.stat()
        assert (number, msgid) == (1, message_id)
        response, info = client.head()
        assert info.lines == [b"Message-ID: <reader@example.invalid>"], info
        response, info = client.body(message_id)
        assert info.lines == [b"Hello"], info
        response, info = client.article("1")
        assert info.lines == [b"Message-ID: <reader@example.invalid>", b"", b"Hello"], info
        response, groups = client.list()
        assert [g.group for g in groups] == ["fn.letters"], groups
        response = client.quit()
        assert response.startswith("205 "), response
    print(json.dumps({"status": "passed", "client": "stdlib nntplib",
                      "python": platform.python_version(),
                      "commands": ["CAPABILITIES", "GROUP", "STAT", "HEAD", "BODY",
                                   "ARTICLE", "LIST", "QUIT"]}, sort_keys=True))


if __name__ == "__main__":
    main()
