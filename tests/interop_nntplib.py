"""Independent NNTP client probe (requires Python <=3.12's stdlib nntplib).

Point it at a running native owner (`operator CONFIG run`, posting enabled,
group GROUP configured) by its loopback port; tools/deploy_gate.py runs it
on the box.  The client's framing and parsing are nntplib's, not fn's: this
is interoperability evidence for the commands listed in its output, not an
RFC conformance audit.
"""
import argparse
import json
import nntplib
import platform


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("port", type=int)
    parser.add_argument("--group", default="fn.letters")
    parser.add_argument("--message-id", default="<nntplib-probe@example.invalid>")
    args = parser.parse_args()
    if not 0 < args.port <= 65535:
        parser.error("port must be from 1 through 65535")
    message_id = args.message_id
    with nntplib.NNTP("127.0.0.1", port=args.port, timeout=30) as client:
        assert client.getwelcome().startswith("200 "), client.getwelcome()
        caps = client.getcapabilities()
        assert caps["VERSION"] == ["2"], caps
        assert "READER" in caps and "POST" in caps, caps
        # POST through nntplib's own encoder (dot-stuffing, CRLF, terminator).
        lines = ["From: probe@example.invalid", "Newsgroups: " + args.group,
                 "Subject: nntplib probe", "Message-ID: " + message_id, "",
                 "Hello from nntplib", ".leading dot"]
        response = client.post([line.encode() + b"\r\n" for line in lines])
        assert response.startswith("240"), response
        response, count, first, last, name = client.group(args.group)
        assert name == args.group and count >= 1 and first <= last, response
        response, number, msgid = client.stat(message_id)
        assert msgid == message_id, (number, msgid)
        response, info = client.body(message_id)
        assert info.lines == [b"Hello from nntplib", b".leading dot"], info
        response, info = client.head(message_id)
        assert b"Message-ID: " + message_id.encode() in info.lines, info
        response, overviews = client.over((first, last))
        assert any(f["message-id"] == message_id for _, f in overviews), overviews
        response, legacy = client.xover(first, last)
        assert legacy == overviews, (legacy, overviews)
        response, ids = client.xhdr("message-id", "{}-{}".format(first, last))
        assert any(value == message_id for _, value in ids), ids
        assert client.date()[1].year >= 2026
        response, groups = client.list()
        assert args.group in [g.group for g in groups], groups
        response = client.quit()
        assert response.startswith("205 "), response
    print(json.dumps({"status": "passed", "client": "stdlib nntplib",
                      "python": platform.python_version(),
                      "commands": ["CAPABILITIES", "POST", "GROUP", "STAT", "BODY",
                                   "HEAD", "OVER", "XOVER", "XHDR", "DATE", "LIST",
                                   "QUIT"]}, sort_keys=True))


if __name__ == "__main__":
    main()
