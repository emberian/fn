import sys
body = 2048
import msgid_measure as m
def article(i):
    head = ("From: s@example.invalid\r\nNewsgroups: fn.test\r\nSubject: spike %d\r\n"
            "Date: Thu, 24 Sep 2026 12:00:00 +0000\r\nMessage-ID: %s\r\n\r\n" % (i, m.msgid(i))).encode()
    line = b"x" * 62 + b"\r\n"
    return head + line * max(1, (body - len(head)) // 64)
