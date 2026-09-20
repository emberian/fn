"""Post through the standard library's nntplib, which fn does not control.

nntplib was removed in Python 3.13; this probe therefore runs under an
explicitly named 3.12 interpreter and is skipped when it is absent.
"""
import sys
import nntplib

BODY = [b"From: probe@example.invalid", b"Subject: nntplib probe",
        b"Newsgroups: fn.letters", b"", b"Posted by nntplib."]


def main():
    port = int(sys.argv[1])
    with nntplib.NNTP("127.0.0.1", port=port, timeout=10) as client:
        client.post(iter([line + b"\r\n" for line in BODY]))
        print("posted")
    # The posting connection stays pinned at the version it opened with
    # (the owner's pinned-prefix discipline); a new connection pins the
    # version the post advanced to and reads the article back.
    with nntplib.NNTP("127.0.0.1", port=port, timeout=10) as client:
        resp, count, first, last, name = client.group("fn.letters")
        resp, info = client.article(last)
        text = b"\r\n".join(info.lines)
        if b"Posted by nntplib." not in text:
            raise SystemExit("the posted body did not come back: %r" % text)
        if b"Injection-Info:" not in text:
            raise SystemExit("no Injection-Info in %r" % text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
