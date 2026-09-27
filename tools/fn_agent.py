#!/usr/bin/env python3
"""fn agent: sleep until there is news, read it as JSON, reply, ack.

A small client for an agent -- a script, or an LLM's tool call -- that wants
the news on its fn node without speaking NNTP or holding cursor bytes.  It
adds no authority: every fact comes from the node, through two paths that
already exist.

  next    `fn consumer bound-wait` (or `wait` for an unbound consumer) over
          the owner's 0600 control socket: it sleeps until an event the
          consumer can read is committed, or the timeout passes, and answers
          exactly what a poll would then (PRF-252).  The article is decoded
          by the native image (`fn consumer-article`, ACL2's decoder) and
          printed as ONE JSON line: Message-ID, groups, From, Subject,
          References, body.  The cursor is kept in the state directory for
          `ack`.  A timeout prints {"kind": "empty"}.
  reply   posts a follow-up over NNTP as the consumer's own account (the
          password in `secret_file`, the account's; STARTTLS and AUTHINFO by
          tools/fn_client.py), to the article's groups, with References set
          to its References and Message-ID.  The exact article is kept as a
          draft first, so an uncertain post is settled with
          `fn_client.py reconcile DRAFT`, never by posting again.
  ack     `fn consumer bound-ack` (or `ack`) of the kept cursor: the
          consumer's position moves past the event.  Until then `next`
          answers the same event again (at-least-once delivery): ack after
          your own work is durable, not before.

    fn_agent.py CONFIG next [--timeout S]
    fn_agent.py CONFIG reply --subject 'Re: ...' < body.txt
    fn_agent.py CONFIG ack

CONFIG is a JSON file:

    {"image": "/usr/local/bin/fn",          the fn launcher
     "control": "/var/lib/fn/control.sock",  the owner's control socket
     "consumer": "bob-inbox",                the consumer's name
     "secret_file": "/home/bob/.fn-pw",      mode 0600: the account's password
     "login": "bob",                         the account (for reply)
     "from": "bob <bob@node.example>",       the From of a reply
     "node": "127.0.0.1:1119",               NNTP, for reply
     "cafile": "/etc/fn/cert.pem",           the node's certificate
     "state": "/home/bob/.fn-agent"}         the cursor and drafts

Without "secret_file" the consumer is the operator's unbound one (plain
`wait`/`ack`), and `reply` is unavailable.  Exit codes are the node's
words: 0 done, 1 refused, 3 uncertain, 4 fault, 2 usage.  One JSON line on
standard output per command; the node's own words on standard error.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

CLIENT = Path(__file__).resolve().parent / "fn_client.py"
EXIT_USAGE = 2


def fail(code, why):
    print(json.dumps({"kind": "error", "exit": code, "detail": why}))
    return code


class Agent:
    def __init__(self, config_path):
        self.config = json.loads(Path(config_path).read_text(encoding="utf-8"))
        for key in ("image", "control", "consumer", "state"):
            if key not in self.config:
                raise SystemExit("fn_agent: %s names no %r" % (config_path, key))
        self.state = Path(self.config["state"])
        self.state.mkdir(parents=True, exist_ok=True, mode=0o700)
        self.secret = self.config.get("secret_file")
        self.cursor = self.state / "pending.fncu"
        self.event = self.state / "pending.json"

    def native(self, *words, timeout=300):
        result = subprocess.run([self.config["image"], "--fn", *map(str, words)],
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=timeout, check=False)
        sys.stderr.write(result.stdout.decode("utf-8", "replace"))
        sys.stderr.write(result.stderr.decode("utf-8", "replace"))
        return result

    def scratch(self, stem):
        handle, name = tempfile.mkstemp(prefix=stem + "-", dir=self.state)
        os.close(handle)
        os.unlink(name)
        return Path(name)

    # -- next -------------------------------------------------------------------
    def next(self, seconds):
        cursor, report = self.scratch("cursor"), self.scratch("report")
        try:
            if self.secret:
                words = ("consumer", "bound-wait", self.config["control"],
                         self.config["consumer"], self.secret, cursor, report,
                         "--timeout", seconds)
            else:
                words = ("consumer", "wait", self.config["control"],
                         self.config["consumer"], cursor, report,
                         "--timeout", seconds)
            result = self.native(*words, timeout=int(seconds) + 60)
            if result.returncode != 0:
                # The node's own line names the outcome and a refusal's
                # reason (`consumer refused credential`, PKT-709).
                said = result.stdout.decode("ascii", "replace").strip().splitlines()
                return fail(result.returncode, "wait: " + (said[-1] if said else "consumer %s" % (
                    {1: "refused", 3: "uncertain"}.get(result.returncode, "fault"))))
            if report.stat().st_size == 0:
                # The empty page: nothing new before the timeout.  Its cursor
                # is the position, and acking it is a no-op; keep nothing.
                print(json.dumps({"kind": "empty"}))
                return 0
            record = self.project(cursor, report)
            os.replace(cursor, self.cursor)
            self.event.write_text(json.dumps(record), encoding="utf-8")
            print(json.dumps(record))
            return 0
        finally:
            for path in (cursor, report):
                if path.exists():
                    path.unlink()

    def project(self, cursor, report):
        """The article the report carries, as the native image decodes it
        (`fn consumer-article`, ACL2's fn-cwait-report-article), then its
        fields.  CURSOR is unused: the report alone names the article."""
        result = self.native("consumer-article", report)
        words = result.stdout.decode("ascii", "replace").split()
        if result.returncode == 0 and len(words) == 2 and words[0] == "fn-consumer-withdrawn-v1":
            # PKT-710: the article was withdrawn (its author's cancel, or a
            # supersession).  The event carries its Message-ID and no
            # content; ack it like any other event.
            return {"kind": "withdrawn",
                    "message_id": bytes.fromhex(words[1]).decode("ascii", "replace")}
        if result.returncode != 0 or len(words) != 3 or words[0] != "fn-consumer-article-v1":
            # Not an article (or not decodable): the event is still
            # delivered, and still acked by `ack`.
            return {"kind": "event", "projected": False, "detail": " ".join(words)}
        fields = article_fields(bytes.fromhex(words[2]))
        fields["kind"] = "article"
        fields["message_id"] = bytes.fromhex(words[1]).decode("ascii", "replace")
        return fields

    # -- ack --------------------------------------------------------------------
    def ack(self):
        if not self.cursor.exists():
            return fail(1, "nothing to ack: `next` delivered no event since the last ack")
        if self.secret:
            result = self.native("consumer", "bound-ack", self.config["control"],
                                 self.cursor, self.secret)
        else:
            result = self.native("consumer", "ack", self.config["control"], self.cursor)
        if result.returncode != 0:
            said = result.stdout.decode("ascii", "replace").strip().splitlines()
            return fail(result.returncode, "ack: " + (said[-1] if said else "consumer %s" % (
                {1: "refused", 3: "uncertain"}.get(result.returncode, "fault"))))
        pending = json.loads(self.event.read_text(encoding="utf-8")) \
            if self.event.exists() else {}
        self.cursor.unlink()
        if self.event.exists():
            self.event.unlink()
        print(json.dumps({"kind": "acked", "message_id": pending.get("message_id")}))
        return 0

    # -- reply ------------------------------------------------------------------
    def reply(self, subject, body, groups):
        if not self.secret:
            return fail(EXIT_USAGE, "reply needs the account: set secret_file and login")
        if not self.event.exists():
            return fail(1, "nothing to reply to: `next` delivered no article")
        event = json.loads(self.event.read_text(encoding="utf-8"))
        if event.get("kind") != "article":
            return fail(1, "the pending event is not an article")
        references = event.get("references", []) + [event["message_id"]]
        drafts = self.state / "drafts"
        drafts.mkdir(exist_ok=True, mode=0o700)
        draft = self.scratch("drafts/reply")
        password = Path(self.secret).read_bytes().decode("utf-8").rstrip("\r\n")
        env = dict(os.environ, FN_CLIENT_USER=self.config["login"],
                   FN_CLIENT_PASSWORD=password)
        words = [sys.executable, str(CLIENT), "--node", self.config["node"]]
        words += (["--cafile", self.config["cafile"]] if self.config.get("cafile")
                  else ["--plain"])
        words += ["post", groups or ",".join(event["groups"]),
                  "--subject", subject, "--references", " ".join(references),
                  "--draft", str(draft)]
        if self.config.get("from"):
            words += ["--from", self.config["from"]]
        result = subprocess.run(words, input=body, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=120, check=False)
        sys.stderr.write(result.stderr.decode("utf-8", "replace"))
        msgid = result.stdout.decode("ascii", "replace").strip()
        word = {0: "accepted", 1: "refused", 3: "uncertain"}.get(result.returncode, "error")
        print(json.dumps({"kind": "reply", "outcome": word, "message_id": msgid,
                          "references": references, "draft": str(draft)}))
        return result.returncode


def article_fields(octets):
    """The header fields an agent reads, and the body, of one article.

    Presentation only: the node decided what the article is; this splits its
    served octets at the first empty line and unfolds header lines
    (RFC 5322 section 2.2.3)."""
    text = octets.decode("utf-8", "replace").replace("\r\n", "\n")
    head, _, body = text.partition("\n\n")
    fields = []
    for line in head.split("\n"):
        if line[:1] in (" ", "\t") and fields:
            fields[-1] = (fields[-1][0], fields[-1][1] + " " + line.strip())
        elif ":" in line:
            name, _, value = line.partition(":")
            fields.append((name.strip(), value.strip()))

    def field(name):
        for key, value in fields:
            if key.lower() == name.lower():
                return value
        return ""
    return {"message_id": field("Message-ID"),
            "groups": [g.strip() for g in field("Newsgroups").split(",") if g.strip()],
            "from": field("From"), "subject": field("Subject"),
            "references": field("References").split(),
            "date": field("Date"), "body": body}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("config")
    verbs = parser.add_subparsers(dest="verb", required=True)
    waiting = verbs.add_parser("next", help="wait for the next event; print it as JSON")
    waiting.add_argument("--timeout", type=int, default=300,
                         help="seconds to wait, 0 to 3600 (default 300)")
    replying = verbs.add_parser("reply", help="post a follow-up to the pending article")
    replying.add_argument("--subject", required=True)
    replying.add_argument("--group", default="",
                          help="the groups to post to (default: the article's)")
    replying.add_argument("--body-file", default="", help="the body; standard input when absent")
    verbs.add_parser("ack", help="acknowledge the pending event")
    args = parser.parse_args(argv)
    if args.verb == "next" and not 0 <= args.timeout <= 3600:
        parser.error("--timeout %d: 0 to 3600 seconds" % args.timeout)
    agent = Agent(args.config)
    if args.verb == "next":
        return agent.next(args.timeout)
    if args.verb == "ack":
        return agent.ack()
    body = (Path(args.body_file).read_bytes() if args.body_file
            else sys.stdin.buffer.read())
    return agent.reply(args.subject, body, args.group)


if __name__ == "__main__":
    sys.exit(main())
