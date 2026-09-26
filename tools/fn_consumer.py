#!/usr/bin/env python3
"""A sleeping E1/E2 consumer: an external client of one fn node's local owner.

This is an application process, not part of fn.  It owns one durable SQLite
database and nothing else.  Every fn fact it uses comes from the native image:
`consumer poll/ack/position` over the owner's 0600 control socket, the ACL2
projection `consumer-project` of a polled event, and `hybrid-sign` /
`hybrid-author` for its own replies.  It never builds or edits cursor bytes,
never decodes a Store event itself, and never decides anything fn decides.
What it decides is its own application meaning (specs/consumer-progress.md,
"Consumer transaction and recovery" and CNS-003):

  one SQLite transaction = source-inclusive provenance inbox row
                         + the consumer's own verdict on the signatures
                         + unique (application-id, operation-id) decision,
                           claimable only by the principal the application
                           names for that operation identity
                         + at most one deterministic local transition
                         + an immutable submission artifact for the reply
                         + the fn cursor it will declare next

Only after that transaction commits does the consumer send `ack`.

Independent verification.  Before it decides anything about a polled event,
the consumer checks the article fn served (the projection's received bytes)
with tools/fn_verify.py's offline `check-article` form against its OWN
keyring (the `keyring` file in its configuration: the authors it was told to
trust).  It records its verdict beside the node's.  An event it cannot
verify (unverified, undecided -- an author it does not trust -- or a
principal or authored source other than the node's) is kept as evidence and
never consumed: no operation, no transition, no reply.  fn_verify imports
nothing of fn's and nothing in tools/ imports it (tests/test_anchor.py); the
consumer runs it as a separate process.

Submissions (the outbox) are three kinds of record, never one mutable row:

  submissions   the immutable artifact: authored source, both signatures,
                the author's principal, Ed25519 key, ML-DSA-65 key (PEM) and
                keyring generation, and the original context.  A trigger
                refuses UPDATE and DELETE.  A retry sends exactly these
                bytes and this key context; a later key-file or configuration
                change cannot alter what is retried, and nothing is ever
                re-signed (randomized ML-DSA signing would change the
                signature and so the carrier, which D25 answers as a
                conflict; the authored source itself would be unchanged).
  attempts      one row per submission attempt, committed as `in-flight`
                BEFORE the native boundary is crossed, answered afterwards in
                a separate transaction.  An in-flight row found when a
                process opens the database is `unanswered`: it may have
                succeeded, whether or not the dead process reached the
                socket.
  observations  evidence the operation is stored: fn's answer to an attempt
                (exit 0: accepted or D25's duplicate) or fn's Store serving
                the exact artifact back through poll (the same authored
                source and the same two signatures, checked independently).

A submission's state is derived: `stored` once any observation exists;
`pending` with no attempt; `refused` only when EVERY attempt has a durable
refusal answer; otherwise `uncertain`.  A later refusal settles the attempt
it answers and never an earlier attempt without a durable answer.  An
uncertain submission is reconciled, not retried blindly: the saved artifact
is resent once per unanswered or uncertain attempt (D25: the same carrier is
"already stored here", NNT-019's contract), and if that resend is refused --
current permission is fn's to decide, e.g. a revoked enrolment answers
before D25 is consulted (PKT-322) -- the submission stays uncertain until
fn's Store serves the artifact back.

Exit codes: 0 finished, 1 refused (an fn or application refusal it cannot
settle), 3 stopped on an uncertain fn outcome (wake again to settle), 4 fault.
Developer cuts (`FN_CONSUMER_CUT`) stop the process with os._exit(97):
`in-transaction`, `after-commit`, `after-ack` (the consumer transaction and
its ack); `before-post` (no attempt recorded), `attempt-recorded` (in-flight
attempt committed, nothing sent), `after-post` (fn answered, the answer not
recorded), `in-result-transaction` (inside the answer's BEGIN IMMEDIATE,
before COMMIT).
"""
import argparse
import datetime
import email.utils
import hashlib
import json
import os
from pathlib import Path
import re
import sqlite3
import subprocess
import sys
import tempfile

APP_MAGIC = b"fn-app: e1/1"
SCHEMA_VERSION = "fn-consumer-2"
VERIFIER = Path(__file__).resolve().parent / "fn_verify.py"
SCHEMA = """
CREATE TABLE IF NOT EXISTS meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS inbox(
  history TEXT NOT NULL, incarnation TEXT NOT NULL, source_id TEXT NOT NULL,
  application_id TEXT NOT NULL, operation_id TEXT NOT NULL,
  message_id TEXT NOT NULL, source BLOB NOT NULL, received BLOB NOT NULL,
  store_sequence INTEGER NOT NULL,
  node_principal TEXT NOT NULL, node_verdict TEXT NOT NULL,
  own_verdict TEXT NOT NULL
    CHECK (own_verdict IN ('verified', 'unverified', 'undecided', 'disagree')),
  own_principal TEXT, own_detail TEXT,
  disposition TEXT NOT NULL
    CHECK (disposition IN ('applied', 'repeat', 'conflict', 'not-consumed')),
  reason TEXT,
  PRIMARY KEY (history, incarnation, source_id, application_id, operation_id));
CREATE TABLE IF NOT EXISTS operations(
  application_id TEXT NOT NULL, operation_id TEXT NOT NULL,
  source_sha256 TEXT NOT NULL, kind TEXT NOT NULL, result TEXT NOT NULL,
  claimant TEXT NOT NULL, submission_id INTEGER,
  PRIMARY KEY (application_id, operation_id));
CREATE TABLE IF NOT EXISTS transitions(
  seq INTEGER PRIMARY KEY, application_id TEXT NOT NULL,
  operation_id TEXT NOT NULL, before TEXT NOT NULL, after TEXT NOT NULL,
  UNIQUE (application_id, operation_id));
CREATE TABLE IF NOT EXISTS app_state(key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS submissions(
  id INTEGER PRIMARY KEY,
  application_id TEXT NOT NULL, operation_id TEXT NOT NULL,
  message_id TEXT NOT NULL UNIQUE,
  source BLOB NOT NULL, ed_sig BLOB NOT NULL, ml_sig BLOB NOT NULL,
  principal TEXT NOT NULL, ed_public BLOB NOT NULL, ml_public_pem BLOB NOT NULL,
  keyring_generation TEXT NOT NULL, context TEXT NOT NULL,
  UNIQUE (application_id, operation_id));
CREATE TRIGGER IF NOT EXISTS submissions_are_immutable
  BEFORE UPDATE ON submissions
  BEGIN SELECT RAISE(ABORT, 'a submission artifact is immutable'); END;
CREATE TRIGGER IF NOT EXISTS submissions_are_kept
  BEFORE DELETE ON submissions
  BEGIN SELECT RAISE(ABORT, 'a submission artifact is kept'); END;
CREATE TABLE IF NOT EXISTS attempts(
  id INTEGER PRIMARY KEY,
  submission_id INTEGER NOT NULL REFERENCES submissions(id),
  purpose TEXT NOT NULL CHECK (purpose IN ('submit', 'reconcile')),
  state TEXT NOT NULL CHECK (state IN ('in-flight', 'unanswered', 'answered')),
  exit INTEGER, status TEXT, output TEXT,
  CHECK ((state = 'answered') = (exit IS NOT NULL)));
CREATE TABLE IF NOT EXISTS observations(
  id INTEGER PRIMARY KEY,
  submission_id INTEGER NOT NULL REFERENCES submissions(id),
  kind TEXT NOT NULL CHECK (kind IN ('post-answer', 'store-observation')),
  attempt_id INTEGER REFERENCES attempts(id),
  store_sequence INTEGER, detail TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS unattributed(
  store_sequence INTEGER PRIMARY KEY, reason TEXT NOT NULL);
"""


def digest(source):
    """The application's own identity for exact source bytes (its dedup and
    correlation key).  fn's source identity is kept separately as provenance."""
    return hashlib.sha256(source).hexdigest()


def answer_class(exit_code):
    """What a durable answer to one attempt says about that attempt only.
    The exit code is fn's (fn-native-control-status-exit-code)."""
    return {0: "accepted", 1: "refused", 3: "uncertain"}.get(exit_code, "fault")


def submission_state(attempts, observed):
    """The derived state of one submission from its journal.  ATTEMPTS is the
    ordered list of (state, exit) rows; OBSERVED says an observation exists."""
    if observed:
        return "stored"
    if not attempts:
        return "pending"
    if all(state == "answered" and answer_class(code) == "refused"
           for state, code in attempts):
        return "refused"
    return "uncertain"


def reconcile_due(attempts):
    """An uncertain submission is resent once per attempt without a
    definitive answer: not again after a later attempt was refused (that
    refusal is about the later attempt; only an observation settles the
    earlier one)."""
    last_open = max((i for i, (state, code) in enumerate(attempts)
                     if state != "answered" or answer_class(code) != "refused"),
                    default=None)
    if last_open is None:
        return False
    return not any(state == "answered" and answer_class(code) == "refused"
                   for state, code in attempts[last_open + 1:])


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
        tables = {r[0] for r in self.db.execute(
            "SELECT name FROM sqlite_master WHERE type='table'")}
        if "outbox" in tables:
            raise SystemExit("fn_consumer: %s is a fn-consumer-1 database (one mutable "
                             "outbox row per reply); this consumer keeps an attempt "
                             "journal and needs a fresh database" % self.config["db"])
        self.db.executescript(SCHEMA)
        self.db.execute("BEGIN IMMEDIATE")
        self.set_meta("schema", SCHEMA_VERSION)
        # One consumer process per database: an attempt still in flight when
        # a process opens it belonged to a process that died with the
        # native call outstanding or its answer unrecorded.
        self.db.execute("UPDATE attempts SET state='unanswered' WHERE state='in-flight'")
        self.db.execute("COMMIT")

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
                "received": bytes.fromhex(words[15]),
                "verdict_principal": words[16], "verdict": words[17]}, line

    # -- independent verification ---------------------------------------------
    def verify(self, event):
        """This consumer's own verdict on the article fn served, with its own
        keyring, through fn_verify's offline boundary (a separate process)."""
        keyring = self.config.get("keyring")
        if not keyring:
            raise Stop(4, "no keyring configured: the consumer verifies every report "
                          "itself and trusts no author by default")
        article = self.scratch("article")
        article.write_bytes(event["received"])
        result = subprocess.run(
            [sys.executable, str(VERIFIER), "check-article", str(article),
             event["message_id"], "--keyring", keyring],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300, check=False)
        try:
            check = json.loads(result.stdout.decode("utf-8"))
        except ValueError:
            check = {"outcome": "undecided",
                     "reason": "verifier: " + result.stderr.decode("utf-8", "replace")[-500:]}
        detail = check.get("reason") or ""
        if result.returncode == 0 and check.get("outcome") == "verified":
            if check.get("principal") != event["verdict_principal"]:
                return dict(check, own="disagree",
                            detail="verified for %s, the node names %s"
                            % (check.get("principal"), event["verdict_principal"]))
            if check.get("source-sha256") != digest(event["source"]):
                return dict(check, own="disagree",
                            detail="the verified authored source is not fn's projection")
            return dict(check, own="verified", detail="")
        own = {1: "unverified", 3: "undecided"}.get(result.returncode, "undecided")
        return dict(check, own=own, detail=detail)

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

    def journal(self, submission_id):
        attempts = self.db.execute(
            "SELECT state, exit FROM attempts WHERE submission_id=? ORDER BY id",
            (submission_id,)).fetchall()
        observed = self.db.execute(
            "SELECT 1 FROM observations WHERE submission_id=? LIMIT 1",
            (submission_id,)).fetchone() is not None
        return attempts, observed

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

    def claimant(self, application_id, operation_id):
        """The application's rule for who may claim an operation identity: the
        longest configured prefix of OPERATION_ID under APPLICATION_ID names one
        principal.  A valid signature is not a claim; nothing configured is
        nobody's."""
        best = None
        for aid, prefix, principal in self.config.get("claims", []):
            if aid == application_id and operation_id.startswith(prefix):
                if best is None or len(prefix) > len(best[0]):
                    best = (prefix, principal)
        return best[1] if best else None

    def compose(self, message_id, subject, fields):
        body = [APP_MAGIC] + [("%s: %s" % kv).encode("ascii") for kv in fields]
        # The Date is fixed when the source is composed; the submission keeps
        # these exact bytes, so every retry posts the same source.
        date = email.utils.format_datetime(
            datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0))
        return (b"From: " + self.config["from"].encode("ascii") + b"\r\n"
                b"Date: " + date.encode("ascii") + b"\r\n"
                b"Newsgroups: " + self.config["group"].encode("ascii") + b"\r\n"
                b"Subject: " + subject.encode("ascii") + b"\r\n"
                b"Message-ID: " + message_id.encode("ascii") + b"\r\n\r\n"
                + b"\r\n".join(body) + b"\r\n")

    def artifact(self, application_id, operation_id, message_id, source):
        """Sign SOURCE once and return the complete submission artifact: the
        signatures and the key context they were made under, frozen now."""
        path = self.scratch("sign")
        path.write_bytes(source)
        keys = self.config["keys"]
        code, out, err = self.native("hybrid-sign", keys["principal"],
                                     keys["ed_public"], keys["ed_secret"],
                                     keys["ml_public"], keys["ml_private"], path)
        if code != 0:
            raise Stop(4, "hybrid-sign: " + err.decode())
        parts = dict(line.split() for line in out.decode("ascii").splitlines())
        context = {"consumer": self.name, "group": self.config["group"],
                   "from": self.config["from"], "route": "hybrid-author",
                   "signed": email.utils.format_datetime(
                       datetime.datetime.now(datetime.timezone.utc))}
        return (application_id, operation_id, message_id, source,
                bytes.fromhex(parts["ed25519"]), bytes.fromhex(parts["ml-dsa-65"]),
                Path(keys["principal"]).read_bytes().hex(),
                Path(keys["ed_public"]).read_bytes(),
                Path(keys["ml_public"]).read_bytes(),
                str(self.config["generation"]),
                json.dumps(context, sort_keys=True))

    def insert_submission(self, artifact):
        return self.db.execute(
            "INSERT INTO submissions(application_id, operation_id, message_id, source, "
            "ed_sig, ml_sig, principal, ed_public, ml_public_pem, keyring_generation, "
            "context) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)", artifact).lastrowid

    def originate(self, operation_id, payload):
        """Author a report R as a new local operation with its submission."""
        aid = self.config["application_id"]
        message_id = "<%s.%s@%s.invalid>" % (aid, operation_id, self.name)
        source = self.compose(message_id, "report " + operation_id,
                              [("application-id", aid),
                               ("operation-id", operation_id),
                               ("kind", "report-receipt"),
                               ("payload", payload)])
        artifact = self.artifact(aid, operation_id, message_id, source)
        self.db.execute("BEGIN IMMEDIATE")
        try:
            prior = self.db.execute(
                "SELECT submission_id FROM operations WHERE application_id=? "
                "AND operation_id=?", (aid, operation_id)).fetchone()
            if prior is None:
                # An existing operation keeps its artifact; the signature just
                # made is discarded, never substituted.
                sid = self.insert_submission(artifact)
                self.db.execute(
                    "INSERT INTO operations VALUES (?, ?, ?, 'originated', "
                    "'awaiting-reply', ?, ?)",
                    (aid, operation_id, digest(source), artifact[6], sid))
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
        return self.artifact(aid, oid, message_id, source)

    def observe_stored(self, event, check):
        """fn's Store served one of our own artifacts back: the same authored
        source under its Message-ID and, by this consumer's own check of the
        served carrier, the same two signatures."""
        if check.get("own") != "verified":
            return
        sigs = check.get("signatures") or {}
        row = self.db.execute(
            "SELECT id FROM submissions WHERE message_id=? AND source=? AND ed_sig=? "
            "AND ml_sig=?", (event["message_id"], event["source"],
                             bytes.fromhex(sigs.get("ed25519", "")),
                             bytes.fromhex(sigs.get("ml-dsa-65", "")))).fetchone()
        if row and not self.journal(row[0])[1]:
            self.db.execute(
                "INSERT INTO observations(submission_id, kind, store_sequence, detail) "
                "VALUES (?, 'store-observation', ?, 'exact artifact served by poll')",
                (row[0], event["sequence"]))

    def transaction(self, event, fields, cursor, check):
        """The one atomic consumer transaction; returns its disposition."""
        aid, oid = fields["application-id"], fields["operation-id"]
        principal = check.get("principal") if check["own"] == "verified" else None
        claimant = self.claimant(aid, oid)
        entitled = principal is not None and principal == claimant
        reply = None
        if entitled and fields["kind"] == "report-receipt" and \
                principal != self.config["principal_hex"]:
            reply = self.reply_for(fields, event)
        self.db.execute("BEGIN IMMEDIATE")
        try:
            prior = self.db.execute(
                "SELECT source_sha256 FROM operations WHERE application_id=? "
                "AND operation_id=?", (aid, oid)).fetchone()
            key = (event["history"], event["incarnation"], event["source_id"], aid, oid)
            reason = None
            if principal is None:
                disposition, reason = "not-consumed", check["own"]
            elif not entitled:
                disposition, reason = "conflict", "unentitled"
            elif prior is None:
                disposition = "applied"
            elif prior[0] == digest(event["source"]):
                disposition = "repeat"
            else:
                disposition, reason = "conflict", "changed-source"
            self.observe_stored(event, check)
            self.db.execute(
                "INSERT OR IGNORE INTO inbox VALUES "
                "(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                key + (event["message_id"], event["source"], event["received"],
                       event["sequence"], event["verdict_principal"], event["verdict"],
                       check["own"], check.get("principal"), check.get("detail", ""),
                       disposition, reason))
            if disposition == "applied":
                submission_id, result = None, "recorded"
                before = after = ""
                if fields["kind"] == "report-receipt" and reply:
                    before = self.state("ledger", "")
                    after = hashlib.sha256((before + digest(event["source"])).encode()).hexdigest()
                    self.db.execute("INSERT OR REPLACE INTO app_state VALUES ('ledger', ?)", (after,))
                    self.db.execute("INSERT OR REPLACE INTO app_state VALUES ('reports', ?)",
                                    (str(int(self.state("reports")) + 1),))
                    submission_id = self.insert_submission(reply)
                    # The reply is this consumer's own operation: when fn
                    # serves it back, it is a repeat, not a new report.
                    self.db.execute(
                        "INSERT INTO operations VALUES (?, ?, ?, 'originated', 'reply', ?, ?)",
                        (aid, reply[1], digest(reply[3]), reply[6], submission_id))
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
                self.db.execute("INSERT INTO operations VALUES (?, ?, ?, ?, ?, ?, ?)",
                                (aid, oid, digest(event["source"]), fields["kind"], result,
                                 principal, submission_id))
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
        """Send each pending submission, and reconcile each uncertain one by
        resending its saved artifact; the attempt is durable before it is sent."""
        rows = self.db.execute(
            "SELECT id, source, ed_sig, ml_sig, ml_public_pem, keyring_generation "
            "FROM submissions ORDER BY id").fetchall()
        for sid, source, ed_sig, ml_sig, ml_public_pem, generation in rows:
            attempts, observed = self.journal(sid)
            state = submission_state(attempts, observed)
            if state == "pending":
                purpose = "submit"
            elif state == "uncertain" and reconcile_due(attempts):
                purpose = "reconcile"
            else:
                continue
            cut("before-post")
            self.db.execute("BEGIN IMMEDIATE")
            attempt = self.db.execute(
                "INSERT INTO attempts(submission_id, purpose, state) "
                "VALUES (?, ?, 'in-flight')", (sid, purpose)).lastrowid
            self.db.execute("COMMIT")
            cut("attempt-recorded")
            paths = [self.scratch(stem) for stem in ("q", "ed", "ml", "mlpub")]
            for path, octets in zip(paths, (source, ed_sig, ml_sig, ml_public_pem)):
                path.write_bytes(octets)
            code, out, err = self.native("hybrid-author", self.control, generation,
                                         paths[0], paths[1], paths[2], paths[3])
            cut("after-post")
            status = re.search(rb"(?m)^\S+ hybrid-author (\S+)\s*$", err)
            status = status.group(1).decode("ascii", "replace") if status else None
            self.db.execute("BEGIN IMMEDIATE")
            try:
                self.db.execute(
                    "UPDATE attempts SET state='answered', exit=?, status=?, output=? "
                    "WHERE id=?", (code, status,
                                   (out + err).decode("utf-8", "replace")[-2000:], attempt))
                if code == 0:
                    self.db.execute(
                        "INSERT INTO observations(submission_id, kind, attempt_id, detail) "
                        "VALUES (?, 'post-answer', ?, ?)", (sid, attempt, status or "ok"))
                cut("in-result-transaction")
                self.db.execute("COMMIT")
            except BaseException:
                if self.db.in_transaction:
                    self.db.execute("ROLLBACK")
                raise
            if code == 3:
                raise Stop(3, "reply POST uncertain; a resend of the saved artifact "
                              "reconciles it")
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
                        self.transaction(event, fields, cursor, self.verify(event))
            self.settle_ack()
        self.drive_outbox()

    def summary(self):
        q = lambda sql: self.db.execute(sql).fetchall()
        outbox = []
        for sid, message_id, source, principal in q(
                "SELECT id, message_id, source, principal FROM submissions ORDER BY id"):
            attempts, observed = self.journal(sid)
            rows = q("SELECT purpose, state, exit, status FROM attempts "
                     "WHERE submission_id=%d ORDER BY id" % sid)
            first = self.db.execute(
                "SELECT kind FROM observations WHERE submission_id=? ORDER BY id LIMIT 1",
                (sid,)).fetchone()
            answered = [r for r in rows if r[1] == "answered"]
            outbox.append({
                "message_id": message_id, "sha256": digest(source), "principal": principal,
                "state": submission_state(attempts, observed),
                "attempts": len(rows),
                "journal": [dict(zip(("purpose", "state", "exit", "status"), r))
                            for r in rows],
                "last_exit": answered[-1][2] if answered else None,
                "settled_by": first[0] if first else None})
        return {
            "inbox": [dict(zip(("source_id", "application_id", "operation_id",
                                "message_id", "disposition", "reason", "own_verdict",
                                "own_principal", "node_principal", "node_verdict"), r))
                      for r in q("SELECT source_id, application_id, operation_id, "
                                 "message_id, disposition, reason, own_verdict, "
                                 "own_principal, node_principal, node_verdict "
                                 "FROM inbox ORDER BY store_sequence")],
            "operations": [dict(zip(("application_id", "operation_id", "kind", "result",
                                     "claimant"), r))
                           for r in q("SELECT application_id, operation_id, kind, result, "
                                      "claimant FROM operations ORDER BY rowid")],
            "transitions": [list(r) for r in q(
                "SELECT application_id, operation_id FROM transitions ORDER BY seq")],
            "outbox": outbox,
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
