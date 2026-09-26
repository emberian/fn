#!/usr/bin/env python3
"""A sleeping E1/E2 consumer: an external client of one fn node's local owner.

This is an application process, not part of fn.  It owns one durable SQLite
database and nothing else.  Every fn fact it uses comes from the native image:
`consumer poll/ack/position` over the owner's 0600 control socket, the ACL2
projection `consumer-project` of a polled event, and `hybrid-sign` /
`hybrid-author` for its own replies.  It never builds or edits cursor bytes,
never decodes a Store event itself, and never decides anything fn decides.
What it decides is its own application meaning (specs/consumer-progress.md,
"Consumer transaction and recovery"):

  one SQLite transaction = source-inclusive provenance inbox row
                         + unique (application-id, operation-id) decision
                         + at most one deterministic local transition
                         + immutable outbox reply
                         + the fn cursor it will declare next

Only after that transaction commits does the consumer send `ack`.  Each
uncertain fact is settled by its owner: an uncertain local transaction by
reading this database (SQLite's journal rolls back an uncommitted one), an
uncertain `ack` by fn's `position`, an uncertain reply POST by re-POSTing the
identical signed source (D25: the same exact source is a duplicate, a changed
source a refusal) and, failing a duplicate answer, by fn serving the exact
source back through poll.  An fn ack never settles this database or a POST.

An uncertain POST whose identical resend is refused (before PKT-166 the local
control route did not answer D25's duplicate) stays unsettled until poll
serves the exact source back.

Exit codes: 0 finished, 1 refused (an fn or application refusal it cannot
settle), 3 stopped on an uncertain fn outcome (wake again to settle), 4 fault.
Developer cuts (`FN_CONSUMER_CUT`): `in-transaction`, `after-commit`,
`after-ack` stop the process with os._exit at that point.
"""
import argparse
import datetime
import email.utils
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile

APP_MAGIC = b"fn-app: e1/1"
SCHEMA = """
CREATE TABLE IF NOT EXISTS meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS inbox(
  history TEXT NOT NULL, incarnation TEXT NOT NULL, source_id TEXT NOT NULL,
  application_id TEXT NOT NULL, operation_id TEXT NOT NULL,
  message_id TEXT NOT NULL, source BLOB NOT NULL,
  store_sequence INTEGER NOT NULL, verdict_principal TEXT NOT NULL,
  disposition TEXT NOT NULL
    CHECK (disposition IN ('applied', 'repeat', 'conflict')),
  PRIMARY KEY (history, incarnation, source_id, application_id, operation_id));
CREATE TABLE IF NOT EXISTS operations(
  application_id TEXT NOT NULL, operation_id TEXT NOT NULL,
  source_sha256 TEXT NOT NULL, kind TEXT NOT NULL, result TEXT NOT NULL,
  outbox_id INTEGER,
  PRIMARY KEY (application_id, operation_id));
CREATE TABLE IF NOT EXISTS transitions(
  seq INTEGER PRIMARY KEY, application_id TEXT NOT NULL,
  operation_id TEXT NOT NULL, before TEXT NOT NULL, after TEXT NOT NULL,
  UNIQUE (application_id, operation_id));
CREATE TABLE IF NOT EXISTS app_state(key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS outbox(
  id INTEGER PRIMARY KEY, message_id TEXT NOT NULL UNIQUE,
  source BLOB NOT NULL, ed_sig BLOB NOT NULL, ml_sig BLOB NOT NULL,
  state TEXT NOT NULL CHECK (state IN
    ('pending', 'uncertain', 'resend-refused', 'stored', 'refused')),
  settled_by TEXT, attempts INTEGER NOT NULL DEFAULT 0, last_exit INTEGER,
  last_output TEXT);
CREATE TABLE IF NOT EXISTS unattributed(
  store_sequence INTEGER PRIMARY KEY, reason TEXT NOT NULL);
"""


def digest(source):
    """The application's own identity for exact source bytes (its dedup and
    correlation key).  fn's source identity is kept separately as provenance."""
    return hashlib.sha256(source).hexdigest()


class Stop(Exception):
    def __init__(self, code, why):
        super().__init__(why)
        self.code = code


def cut(point):
    if os.environ.get("FN_CONSUMER_CUT") == point:
        sys.stderr.write("CONSUMER-CUT %s\n" % point)
        sys.stderr.flush()
        os._exit(97)


class Consumer:
    def __init__(self, config_path):
        self.config = json.loads(Path(config_path).read_text(encoding="utf-8"))
        self.image = self.config["image"]
        self.control = self.config["control"]
        self.name = self.config["consumer"]
        self.work = Path(self.config["work"])
        self.work.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(self.config["db"], isolation_level=None)
        self.db.execute("PRAGMA synchronous=FULL")
        self.db.executescript(SCHEMA)

    # -- native calls --------------------------------------------------------
    def native(self, *words):
        result = subprocess.run([self.image, "--fn", *map(str, words)],
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=300, check=False)
        return result.returncode, result.stdout, result.stderr

    def scratch(self, stem):
        handle, name = tempfile.mkstemp(prefix=stem + "-", dir=self.work)
        os.close(handle)
        os.unlink(name)
        return Path(name)

    def position(self):
        target = self.scratch("position")
        code, out, err = self.native("consumer", "position", self.control,
                                     self.name, target)
        if code != 0:
            raise Stop(code if code in (1, 3) else 4,
                       "position: %s %s" % (out.decode(), err.decode()))
        return target.read_bytes()

    def ack(self, cursor):
        path = self.scratch("ack")
        path.write_bytes(cursor)
        code, out, err = self.native("consumer", "ack", self.control, path)
        return code

    def poll(self):
        cursor_path, report_path = self.scratch("cursor"), self.scratch("report")
        code, out, err = self.native("consumer", "poll", self.control, self.name,
                                     cursor_path, report_path)
        if code != 0:
            raise Stop(code if code in (1, 3) else 4,
                       "poll: %s %s" % (out.decode(), err.decode()))
        return cursor_path, cursor_path.read_bytes(), report_path

    def inspect(self, cursor_path):
        """The scanned position, as the ACL2 cursor decoder prints it."""
        code, out, err = self.native("consumer-inspect", cursor_path)
        words = out.decode("ascii", "replace").split()
        if code != 0 or not words or words[0] != "fn-consumer-inspect-v1":
            raise Stop(4, "consumer-inspect: %s %s" % (out.decode(), err.decode()))
        fields = dict(word.split("=", 1) for word in words[1:] if "=" in word)
        return int(fields["position"])

    def inspect_bytes(self, cursor):
        path = self.scratch("inspect")
        path.write_bytes(cursor)
        return self.inspect(path)

    def project(self, cursor_path, report_path):
        """ACL2's projection of the polled event; the fields are its output."""
        code, out, err = self.native("consumer-project", cursor_path, report_path)
        line = out.decode("ascii", "replace").strip().splitlines()
        line = line[-1] if line else ""
        if code != 0:
            return None, line
        words = line.split()
        if len(words) != 18 or words[0] != "fn-consumer-project-v1":
            raise Stop(4, "unexpected projection line: " + line)
        return {"history": words[1], "incarnation": words[2],
                "position": int(words[9]), "sequence": int(words[10]),
                "source_id": words[12],
                "message_id": bytes.fromhex(words[13]).decode("ascii", "replace"),
                "source": bytes.fromhex(words[14]),
                "verdict_principal": words[16], "verdict": words[17]}, line

    # -- durable state --------------------------------------------------------
    def meta(self, key, default=None):
        row = self.db.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
        return row[0] if row else default

    def set_meta(self, key, value):
        if value is None:
            self.db.execute("DELETE FROM meta WHERE key=?", (key,))
        else:
            self.db.execute("INSERT OR REPLACE INTO meta VALUES (?, ?)", (key, value))

    def state(self, key, default="0"):
        row = self.db.execute("SELECT value FROM app_state WHERE key=?", (key,)).fetchone()
        return row[0] if row else default

    # -- application ----------------------------------------------------------
    @staticmethod
    def envelope(source):
        head, sep, body = source.partition(b"\r\n\r\n")
        if not sep:
            return None
        lines = body.split(b"\r\n")
        if not lines or lines[0] != APP_MAGIC:
            return None
        fields = {}
        for line in lines[1:]:
            key, colon, value = line.partition(b": ")
            if colon:
                fields[key.decode("ascii", "replace")] = value.decode("ascii", "replace")
        if not {"application-id", "operation-id", "kind"} <= fields.keys():
            return None
        return fields

    def compose(self, message_id, subject, fields):
        body = [APP_MAGIC] + [("%s: %s" % kv).encode("ascii") for kv in fields]
        # The Date is fixed when the source is composed; the outbox keeps
        # these exact bytes, so every retry posts the same source.
        date = email.utils.format_datetime(
            datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0))
        return (b"From: " + self.config["from"].encode("ascii") + b"\r\n"
                b"Date: " + date.encode("ascii") + b"\r\n"
                b"Newsgroups: " + self.config["group"].encode("ascii") + b"\r\n"
                b"Subject: " + subject.encode("ascii") + b"\r\n"
                b"Message-ID: " + message_id.encode("ascii") + b"\r\n\r\n"
                + b"\r\n".join(body) + b"\r\n")

    def sign(self, source):
        path = self.scratch("sign")
        path.write_bytes(source)
        keys = self.config["keys"]
        code, out, err = self.native("hybrid-sign", keys["principal"],
                                     keys["ed_public"], keys["ed_secret"],
                                     keys["ml_public"], keys["ml_private"], path)
        if code != 0:
            raise Stop(4, "hybrid-sign: " + err.decode())
        parts = dict(line.split() for line in out.decode("ascii").splitlines())
        return bytes.fromhex(parts["ed25519"]), bytes.fromhex(parts["ml-dsa-65"])

    def originate(self, operation_id, payload):
        """Author a report R as a new local operation with its outbox entry."""
        aid = self.config["application_id"]
        message_id = "<%s.%s@%s.invalid>" % (aid, operation_id, self.name)
        source = self.compose(message_id, "report " + operation_id,
                              [("application-id", aid),
                               ("operation-id", operation_id),
                               ("kind", "report-receipt"),
                               ("payload", payload)])
        ed_sig, ml_sig = self.sign(source)
        self.db.execute("BEGIN IMMEDIATE")
        try:
            prior = self.db.execute(
                "SELECT outbox_id FROM operations WHERE application_id=? AND operation_id=?",
                (aid, operation_id)).fetchone()
            if prior is None:
                cur = self.db.execute(
                    "INSERT INTO outbox(message_id, source, ed_sig, ml_sig, state) "
                    "VALUES (?, ?, ?, ?, 'pending')",
                    (message_id, source, ed_sig, ml_sig))
                self.db.execute(
                    "INSERT INTO operations VALUES (?, ?, ?, 'originated', 'awaiting-reply', ?)",
                    (aid, operation_id, digest(source), cur.lastrowid))
            self.db.execute("COMMIT")
        except BaseException:
            self.db.execute("ROLLBACK")
            raise

    def reply_for(self, fields, event):
        oid = "reply-" + fields["operation-id"]
        aid = fields["application-id"]
        message_id = "<%s.%s@%s.invalid>" % (aid, oid, self.name)
        source = self.compose(message_id, "Re: report " + fields["operation-id"],
                              [("application-id", aid), ("operation-id", oid),
                               ("kind", "reply"),
                               ("correlation-id", fields["operation-id"]),
                               ("dependency", digest(event["source"])),
                               ("payload", "received " + fields.get("payload", ""))])
        return message_id, source

    def transaction(self, event, fields, cursor):
        """The one atomic consumer transaction; returns its disposition."""
        aid, oid = fields["application-id"], fields["operation-id"]
        reply = None
        if fields["kind"] == "report-receipt" and \
                event["verdict_principal"] != self.config["principal_hex"]:
            message_id, source = self.reply_for(fields, event)
            reply = (message_id, source) + self.sign(source)
        self.db.execute("BEGIN IMMEDIATE")
        try:
            prior = self.db.execute(
                "SELECT source_sha256 FROM operations WHERE application_id=? AND operation_id=?",
                (aid, oid)).fetchone()
            key = (event["history"], event["incarnation"], event["source_id"], aid, oid)
            if prior is None:
                disposition = "applied"
            elif prior[0] == digest(event["source"]):
                disposition = "repeat"
            else:
                disposition = "conflict"
            # fn's Store served these exact authored bytes: an outbox entry
            # whose POST answer was lost is settled by that observation.
            self.db.execute(
                "UPDATE outbox SET state='stored', settled_by='store-observation' "
                "WHERE state IN ('uncertain', 'resend-refused') AND source=?",
                (event["source"],))
            self.db.execute(
                "INSERT OR IGNORE INTO inbox VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                key + (event["message_id"], event["source"], event["sequence"],
                       event["verdict_principal"], disposition))
            if disposition == "applied":
                outbox_id, result = None, "recorded"
                before = after = ""
                if fields["kind"] == "report-receipt" and reply:
                    before = self.state("ledger", "")
                    after = hashlib.sha256((before + digest(event["source"])).encode()).hexdigest()
                    self.db.execute("INSERT OR REPLACE INTO app_state VALUES ('ledger', ?)", (after,))
                    self.db.execute("INSERT OR REPLACE INTO app_state VALUES ('reports', ?)",
                                    (str(int(self.state("reports")) + 1),))
                    outbox_id = self.db.execute(
                        "INSERT INTO outbox(message_id, source, ed_sig, ml_sig, state) "
                        "VALUES (?, ?, ?, ?, 'pending')", reply).lastrowid
                    # The reply is this consumer's own operation: when fn
                    # serves it back, it is a repeat, not a new report.
                    self.db.execute(
                        "INSERT INTO operations VALUES (?, ?, ?, 'originated', 'reply', ?)",
                        (aid, "reply-" + oid, digest(reply[1]), outbox_id))
                    result = "replied"
                elif fields["kind"] == "reply":
                    target = self.db.execute(
                        "SELECT source_sha256 FROM operations WHERE application_id=? "
                        "AND operation_id=? AND kind='originated'",
                        (aid, fields.get("correlation-id", ""))).fetchone()
                    before = self.state("replies")
                    if target and target[0] == fields.get("dependency"):
                        after = str(int(before) + 1)
                        self.db.execute("INSERT OR REPLACE INTO app_state VALUES ('replies', ?)", (after,))
                        self.db.execute(
                            "UPDATE operations SET result='replied' WHERE application_id=? "
                            "AND operation_id=?", (aid, fields["correlation-id"]))
                        result = "correlated"
                    else:
                        after, result = before, "uncorrelated"
                self.db.execute("INSERT INTO operations VALUES (?, ?, ?, ?, ?, ?)",
                                (aid, oid, digest(event["source"]), fields["kind"], result,
                                 outbox_id))
                self.db.execute(
                    "INSERT INTO transitions(application_id, operation_id, before, after) "
                    "VALUES (?, ?, ?, ?)",
                    (aid, oid, before, after))
            self.set_meta("pending_ack", cursor.hex())
            self.set_meta("pending_ack_state", "unsent")
            cut("in-transaction")
            self.db.execute("COMMIT")
        except BaseException:
            if self.db.in_transaction:
                self.db.execute("ROLLBACK")
            raise
        cut("after-commit")
        return disposition

    def note_unattributed(self, sequence, reason, cursor):
        self.db.execute("BEGIN IMMEDIATE")
        self.db.execute("INSERT OR IGNORE INTO unattributed VALUES (?, ?)", (sequence, reason))
        self.set_meta("pending_ack", cursor.hex())
        self.set_meta("pending_ack_state", "unsent")
        self.db.execute("COMMIT")

    # -- fn progress ----------------------------------------------------------
    def settle_ack(self):
        """Declare the committed cursor; an uncertain answer is settled by position."""
        pending = self.meta("pending_ack")
        if pending is None:
            return
        cursor = bytes.fromhex(pending)
        if self.meta("pending_ack_state") == "uncertain":
            current = self.position()
            if current == cursor:
                self.clear_ack()
                return
        code = self.ack(cursor)
        if code == 0:
            self.clear_ack()
            cut("after-ack")
            return
        if code == 3:
            self.db.execute("BEGIN IMMEDIATE")
            self.set_meta("pending_ack_state", "uncertain")
            self.db.execute("COMMIT")
            raise Stop(3, "ack uncertain; position settles it on the next wake")
        raise Stop(1 if code == 1 else 4, "ack answered %d" % code)

    def clear_ack(self):
        self.db.execute("BEGIN IMMEDIATE")
        self.set_meta("pending_ack", None)
        self.set_meta("pending_ack_state", None)
        self.db.execute("COMMIT")

    def drive_outbox(self):
        rows = self.db.execute(
            "SELECT id, source, ed_sig, ml_sig, state FROM outbox "
            "WHERE state IN ('pending', 'uncertain') ORDER BY id").fetchall()
        for row_id, source, ed_sig, ml_sig, before in rows:
            cut("before-post")
            paths = [self.scratch(stem) for stem in ("q", "ed", "ml")]
            for path, octets in zip(paths, (source, ed_sig, ml_sig)):
                path.write_bytes(octets)
            code, out, err = self.native(
                "hybrid-author", self.control, self.config["generation"], paths[0],
                paths[1], paths[2], self.config["keys"]["ml_public"])
            state = {0: "stored", 1: "refused", 3: "uncertain"}.get(code, "uncertain")
            if code == 1 and before == "uncertain":
                # A refused resend after an uncertain POST does not say the
                # first POST failed.  Only fn's Store settles it: the exact
                # source served back by poll (identity + exact bytes).
                state = "resend-refused"
            self.db.execute("BEGIN IMMEDIATE")
            self.db.execute("UPDATE outbox SET state=?, attempts=attempts+1, last_exit=?, "
                            "last_output=?, settled_by=? WHERE id=?",
                            (state, code, (out + err).decode("utf-8", "replace")[-2000:],
                             "post-answer" if code == 0 else None, row_id))
            self.db.execute("COMMIT")
            if code == 3:
                raise Stop(3, "reply POST uncertain; re-POST of the same source settles it")
            if code not in (0, 1):
                raise Stop(4, "hybrid-author answered %d: %s" % (code, err.decode()))

    def wake(self, max_pages=256):
        self.settle_ack()
        self.drive_outbox()
        for _ in range(max_pages):
            before = self.position()
            cursor_path, cursor, report_path = self.poll()
            report = report_path.read_bytes()
            if not report:
                if cursor == before:
                    break
                # An empty page still progresses over the scanned prefix.
                self.db.execute("BEGIN IMMEDIATE")
                self.set_meta("pending_ack", cursor.hex())
                self.set_meta("pending_ack_state", "unsent")
                self.db.execute("COMMIT")
                self.settle_ack()
                # A window shorter than the poll's scan bound reached the
                # frontier the owner pinned; our own ack events lie beyond it.
                if self.inspect(cursor_path) - self.inspect_bytes(before) < 16:
                    break
                continue
            else:
                event, line = self.project(cursor_path, report_path)
                if event is None:
                    self.note_unattributed(len(self.db.execute(
                        "SELECT 1 FROM unattributed").fetchall()), line, cursor)
                else:
                    fields = self.envelope(event["source"])
                    if fields is None:
                        self.note_unattributed(event["sequence"], "no-envelope", cursor)
                    else:
                        self.transaction(event, fields, cursor)
            self.settle_ack()
        self.drive_outbox()

    def summary(self):
        q = lambda sql: self.db.execute(sql).fetchall()
        return {
            "inbox": [dict(zip(("source_id", "application_id", "operation_id",
                                "message_id", "disposition"), r))
                      for r in q("SELECT source_id, application_id, operation_id, "
                                 "message_id, disposition FROM inbox ORDER BY store_sequence")],
            "operations": [dict(zip(("application_id", "operation_id", "kind", "result"), r))
                           for r in q("SELECT application_id, operation_id, kind, result "
                                      "FROM operations ORDER BY rowid")],
            "transitions": [list(r) for r in q(
                "SELECT application_id, operation_id FROM transitions ORDER BY seq")],
            "outbox": [dict(zip(("message_id", "state", "attempts", "sha256",
                                 "last_exit", "settled_by"),
                                (r[0], r[1], r[2], hashlib.sha256(r[3]).hexdigest(),
                                 r[4], r[5])))
                       for r in q("SELECT message_id, state, attempts, source, last_exit, "
                                  "settled_by FROM outbox ORDER BY id")],
            "state": dict(q("SELECT key, value FROM app_state")),
            "pending_ack": self.meta("pending_ack_state"),
            "unattributed": len(q("SELECT 1 FROM unattributed")),
        }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("config")
    sub = parser.add_subparsers(dest="command", required=True)
    report = sub.add_parser("report")
    report.add_argument("operation_id")
    report.add_argument("payload")
    sub.add_parser("wake")
    sub.add_parser("summary")
    args = parser.parse_args(argv)
    consumer = Consumer(args.config)
    try:
        if args.command == "report":
            consumer.originate(args.operation_id, args.payload)
            consumer.drive_outbox()
        elif args.command == "wake":
            consumer.wake()
        print(json.dumps(consumer.summary(), sort_keys=True))
        return 0
    except Stop as stop:
        sys.stderr.write("consumer stopped: %s\n" % stop)
        print(json.dumps(consumer.summary(), sort_keys=True))
        return stop.code


if __name__ == "__main__":
    sys.exit(main())
