"""Independent stored-reader probe; run with Python 3.9–3.12 and a live port.

The fixture is <stored@example.invalid>, cross-posted to fn.letters and fn.test,
with the exact three-line article asserted below. No fn modules are imported.
"""
import argparse
import json
import nntplib
import platform


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("port", type=int)
    args = parser.parse_args()
    message_id = "<stored@example.invalid>"
    with nntplib.NNTP("127.0.0.1", port=args.port, timeout=10) as client:
        assert client.getwelcome().startswith("201 ")
        caps = client.getcapabilities()
        assert caps["VERSION"] == ["2"]
        assert "READER" not in caps and "POST" not in caps
        for group in ("fn.letters", "fn.test"):
            _, count, first, last, name = client.group(group)
            assert (count, first, last, name) == (1, 1, 1, group)
            _, number, found_id = client.stat()
            assert (number, found_id) == (1, message_id)
            _, info = client.article("1")
            assert info.lines == [b"Message-ID: <stored@example.invalid>",
                                  b"", b"A stored letter."]
        _, info = client.body(message_id)
        assert info.lines == [b"A stored letter."]
        # nntplib has no public LISTGROUP helper. Its generic multiline command
        # parser still supplies independent framing/response decoding here.
        response, numbers = client._longcmdstring("LISTGROUP fn.letters 2-")
        assert response.startswith("211 1 1 1 fn.letters ") and numbers == []
        _, number, found_id = client.stat()
        assert (number, found_id) == (1, message_id)
        _, numbers = client._longcmdstring("LISTGROUP")
        assert numbers == ["1"]
        _, groups = client.list()
        assert {g.group for g in groups} == {"fn.letters", "fn.test"}
        assert client.quit().startswith("205 ")
    print(json.dumps({"status": "passed", "client": "stdlib nntplib",
                      "python": platform.python_version(), "mode": "recovered-store",
                      "commands": ["CAPABILITIES", "GROUP", "STAT", "ARTICLE",
                                   "BODY", "LISTGROUP", "LIST", "QUIT"]}, sort_keys=True))


if __name__ == "__main__":
    main()
