"""Independent NNTP client probe (requires Python <=3.12's stdlib nntplib).

Start tools/run_reader.py separately, then pass its printed loopback port. This
is reader-only interoperability evidence, not a full RFC conformance audit.
"""
import argparse
import datetime
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
        assert caps["READER"] == [], caps
        assert caps["OVER"] == ["MSGID"], caps
        assert caps["LIST"] == ["ACTIVE", "ACTIVE.TIMES", "HEADERS",
                                "NEWSGROUPS", "OVERVIEW.FMT"], caps
        assert caps["HDR"] == [], caps
        assert "POST" not in caps and "IHAVE" not in caps, caps
        assert "MODE-READER" not in caps and "NEWNEWS" not in caps, caps
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

        # RFC 3977 section 7.1: the server clock as yyyymmddhhmmss.  nntplib
        # parses that field itself, so a malformed one raises here.
        stamp = client.date()[1]
        assert stamp.year >= 2026, stamp

        # Section 7.3: group creation facts, in LIST ACTIVE format.  The
        # served connection carries no persisted creation facts yet
        # (books/nntp-post.lisp builds its environment with an empty fact
        # list), so both queries answer the empty block rather than a date
        # the reader invented.
        response, new_groups = client.newgroups(datetime.date(1970, 1, 1))
        assert [g.group for g in new_groups] == [], new_groups
        response, none_new = client.newgroups(datetime.date(2099, 1, 1))
        assert none_new == [], none_new

        # Sections 8.3 and 8.4.  nntplib reads LIST OVERVIEW.FMT and keys the
        # OVER result by those field names, so a disagreement between the two
        # commands shows up as a KeyError or a shifted value here.
        # nntplib exposes LIST OVERVIEW.FMT only through the private
        # _getoverviewfmt (over() calls it to key its dictionaries); there is
        # no public accessor.
        fmt = client._getoverviewfmt()
        assert fmt == ["subject", "from", "date", "message-id", "references",
                       ":bytes", ":lines"], fmt
        response, overviews = client.over((1, 1))
        assert [number for number, _ in overviews] == [1], overviews
        fields = overviews[0][1]
        assert fields["message-id"] == message_id, fields
        assert fields["subject"] == "" and fields["from"] == "", fields
        assert fields[":bytes"] == "47" and fields[":lines"] == "1", fields
        response, by_id = client.over(message_id)
        assert [number for number, _ in by_id] == [0], by_id

        # RFC 2980 section 2.8.  nntplib sends XOVER when the server does not
        # advertise OVER; xover() is the public entry point for the legacy
        # spelling and parses the same seven fields, so a drift between the
        # two renderers shows up as a mismatch here.
        response, legacy = client.xover(1, 1)
        assert legacy == overviews, (legacy, overviews)

        # Section 2.6 / RFC 3977 section 8.5.  nntplib's xhdr() sends XHDR and
        # returns (label, value) pairs; the label is the article number for a
        # range and the message-id for the message-id form.
        response, subjects = client.xhdr("subject", "1-1")
        assert subjects == [("1", "")], subjects
        response, ids = client.xhdr("message-id", "1-1")
        assert ids == [("1", message_id)], ids
        # nntplib's xhdr() strips a LEADING ARTICLE NUMBER only (its pattern is
        # ^([0-9]+) ?(.*)); RFC 2980 section 2.6 labels the message-id form
        # with the message-id, so the client hands that line back unsplit.
        # That is the legacy label arriving intact, not a parse failure.
        response, by_msgid = client.xhdr("message-id", message_id)
        assert by_msgid == [message_id + " " + message_id], by_msgid
        response, counts = client.xhdr(":lines", "1-1")
        assert counts == [("1", "1")], counts

        # Section 8.6: any header is retrievable, so the list is the single
        # colon plus the two metadata items.
        # nntplib's list() sends LIST ACTIVE <wildmat>, never a LIST variant
        # keyword, so these two go through _longcmdstring as MODE READER does.
        response, fields = client._longcmdstring("LIST HEADERS")
        assert fields == [":", ":bytes", ":lines"], fields

        # Section 7.6.6.  The group table carries no description, so every
        # group carries the same fixed marker.  This call is why the marker
        # is not the empty string: nntplib strips the line and then requires
        # name + white space + text, so "fn.letters TAB" alone drops the
        # group from this dictionary instead of mapping it to "".
        response, descriptions = client.descriptions("fn.*")
        assert descriptions == {"fn.letters": "(no description)"}, descriptions

        # Section 7.6.4.  The served connection carries no persisted creation
        # facts, so the list is empty rather than a fabricated stamp.
        response, times = client._longcmdstring("LIST ACTIVE.TIMES")
        assert times == [], times

        # nntplib has no public MODE READER call (it sends one itself only
        # when constructed with readermode=True); _shortcmd returns the
        # status line as every public command does.
        response = client._shortcmd("MODE READER")
        assert response.startswith("201 "), response
        response = client.quit()
        assert response.startswith("205 "), response
    print(json.dumps({"status": "passed", "client": "stdlib nntplib",
                      "python": platform.python_version(),
                      "commands": ["CAPABILITIES", "GROUP", "STAT", "HEAD", "BODY",
                                   "ARTICLE", "LIST", "LIST ACTIVE.TIMES",
                                   "LIST HEADERS", "LIST NEWSGROUPS", "DATE",
                                   "NEWGROUPS", "LIST OVERVIEW.FMT", "OVER",
                                   "XOVER", "XHDR", "MODE READER",
                                   "QUIT"]}, sort_keys=True))


if __name__ == "__main__":
    main()
