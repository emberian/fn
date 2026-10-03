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

One process per database: the consumer holds an exclusive flock on
`<db>.lock` from before it opens the database until it exits; a second
process is refused (exit 1, `database in use by pid N`) before it reads
anything.

Exit codes: 0 finished, 1 refused (an fn or application refusal it cannot
settle, or the database held by another process), 3 stopped on an uncertain fn outcome (wake again to settle), 4 fault.
Developer cuts (`FN_CONSUMER_CUT`) stop the process with os._exit(97):
`after-poll` (the exact delivery saved, before interpretation);
`in-transaction`, `after-commit`, `after-ack` (the consumer transaction and
its ack); `before-post` (no attempt recorded), `attempt-recorded` (in-flight
attempt committed, nothing sent), `after-post` (fn answered, the answer not
recorded), `in-result-transaction` (inside the answer's BEGIN IMMEDIATE,
before COMMIT).
"""
import argparse
import base64
import binascii
import datetime
import email.utils
import fcntl
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
APP_MAGIC_V2 = b"fn-app: e1/2"
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
CREATE TABLE IF NOT EXISTS deliveries(
  id INTEGER PRIMARY KEY, before_cursor BLOB NOT NULL,
  cursor BLOB NOT NULL, report BLOB NOT NULL,
  state TEXT NOT NULL CHECK (state IN ('pending', 'handled')));
CREATE UNIQUE INDEX IF NOT EXISTS one_pending_delivery
  ON deliveries(state) WHERE state='pending';
CREATE TABLE IF NOT EXISTS unattributed_deliveries(
  delivery_id INTEGER PRIMARY KEY REFERENCES deliveries(id), reason TEXT NOT NULL);
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


class InUse(Exception):
    """Another live process holds this database's lock."""


def lock_database(db_path):
    """Hold an exclusive flock on DB_PATH + '.lock' for the process lifetime.

    One consumer process per database is a rule the client enforces, not a
    comment: the in-flight attempts a process finds on opening belong to a
    dead process only if no live one holds the lock.  flock rather than
    sqlite's `locking_mode=EXCLUSIVE`: the kernel releases it when the holder
    dies (os._exit, SIGKILL), it is taken before the database is read at all
    rather than at sqlite's first write, and the holder writes its pid into
    the file so the refusal names it."""
    fd = os.open(str(db_path) + ".lock", os.O_RDWR | os.O_CREAT, 0o600)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        holder = os.pread(fd, 32, 0).decode("ascii", "replace").strip()
        os.close(fd)
        raise InUse(holder if holder.isdigit() else "unknown")
    os.ftruncate(fd, 0)
    os.pwrite(fd, b"%d\n" % os.getpid(), 0)
    return fd


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
        # PRF-234: a consumer the node binds to an account (`fn operator CONFIG
        # consumer bind NAME --account LOGIN`) polls and acks with that
        # account's password, read by the native image from this file.
        # Absent: the operator's unbound consumer, exactly as before.
        self.secret_file = self.config.get("secret_file")
        self.work = Path(self.config["work"])
        self.work.mkdir(parents=True, exist_ok=True)
        self.lock = lock_database(self.config["db"])
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
        # This process holds the database's lock, so an attempt still in
        # flight belonged to a process that died with the native call
        # outstanding or its answer unrecorded.
        self.db.execute("UPDATE attempts SET state='unanswered' WHERE state='in-flight'")
        self.db.execute("COMMIT")

    # -- native calls --------------------------------------------------------
    def native(self, *words):
        try:
            result = subprocess.run([self.image, "--fn", *map(str, words)],
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    timeout=300, check=False)
        except subprocess.TimeoutExpired:
            # In particular a timed-out ACK or POST might have committed.
            # Its existing durable client record is settled on the next wake.
            raise Stop(3, "native %s timed out; outcome unavailable" % words[0])
        except OSError as error:
            raise Stop(4, "native %s could not start: %s" % (words[0], error))
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
        if self.secret_file:
            code, out, err = self.native("consumer", "bound-ack", self.control,
                                         path, self.secret_file)
        else:
            code, out, err = self.native("consumer", "ack", self.control, path)
        return code

    def poll(self):
        cursor_path, report_path = self.scratch("cursor"), self.scratch("report")
        if self.secret_file:
            code, out, err = self.native("consumer", "bound-poll", self.control,
                                         self.name, self.secret_file,
                                         cursor_path, report_path)
        else:
            code, out, err = self.native("consumer", "poll", self.control,
                                         self.name, cursor_path, report_path)
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
        if code in (3, 4) or code not in (0, 1):
            raise Stop(code if code == 3 else 4,
                       "consumer-project: %s %s" % (out.decode(), err.decode()))
        if code == 1:
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
        try:
            result = subprocess.run(
                [sys.executable, str(VERIFIER), "check-article", str(article),
                 event["message_id"], "--keyring", keyring],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300, check=False)
        except subprocess.TimeoutExpired:
            raise Stop(3, "independent verifier timed out; saved delivery remains pending")
        except OSError as error:
            raise Stop(4, "independent verifier could not start: %s" % error)
        expected = {0: "verified", 1: "unverified", 3: "undecided"}
        if result.returncode not in expected:
            raise Stop(4, "independent verifier answered %d: %s" %
                       (result.returncode, result.stderr.decode("utf-8", "replace")))
        try:
            check = json.loads(result.stdout.decode("utf-8"))
        except (ValueError, UnicodeError):
            raise Stop(4, "independent verifier returned a malformed result")
        if not isinstance(check, dict) or check.get("outcome") != expected[result.returncode]:
            raise Stop(4, "independent verifier result disagrees with its exit status")
        if result.returncode == 0 and not (
                isinstance(check.get("principal"), str) and
                isinstance(check.get("source-sha256"), str) and
                isinstance(check.get("signatures"), dict)):
            raise Stop(4, "independent verifier omitted verified source evidence")
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
        own = {1: "unverified", 3: "undecided"}[result.returncode]
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
    def payload_bytes(payload):
        return payload.encode("utf-8") if isinstance(payload, str) else bytes(payload)

    @staticmethod
    def payload_wire(payload):
        encoded = base64.b64encode(payload)
        return b"\r\n".join(encoded[i:i + 76] for i in range(0, len(encoded), 76)) + b"\r\n"

    @staticmethod
    def envelope(source):
        _, sep, body = source.partition(b"\r\n\r\n")
        if not sep:
            return None
        magic, sep, rest = body.partition(b"\r\n")
        if not sep or magic not in (APP_MAGIC, APP_MAGIC_V2):
            return None
        if magic == APP_MAGIC_V2:
            metadata, sep, wire = rest.partition(b"\r\n\r\n")
            if not sep:
                return None
            lines = metadata.split(b"\r\n")
        else:
            lines = rest.split(b"\r\n")
        fields = {}
        for line in lines:
            if not line and magic == APP_MAGIC:
                continue
            key, colon, value = line.partition(b": ")
            if not colon or not key or b"\r" in line or b"\n" in line:
                return None
            try:
                key, value = key.decode("ascii"), value.decode("ascii")
            except UnicodeError:
                return None
            if key in fields:
                return None
            fields[key] = value
        if not {"application-id", "operation-id", "kind"} <= fields.keys():
            return None
        if not fields["application-id"] or not fields["operation-id"] or fields["kind"] not in ("report-receipt", "reply"):
            return None
        if magic == APP_MAGIC_V2:
            if fields.get("payload-encoding") != "base64" or "payload" in fields:
                return None
            try:
                payload = base64.b64decode(wire.replace(b"\r\n", b""), validate=True)
            except (binascii.Error, ValueError):
                return None
            # One canonical payload region: no alternate whitespace, trailing
            # metadata, or malformed length can change the application meaning.
            if fields.get("payload-length") != str(len(payload)) or wire != Consumer.payload_wire(payload):
                return None
            fields["payload"] = payload
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
        metadata = []
        payload = b""
        seen = set()
        for key, value in fields:
            if key in seen or key in ("payload-encoding", "payload-length"):
                raise Stop(1, "duplicate or reserved application field")
            seen.add(key)
            if key == "payload":
                payload = self.payload_bytes(value)
                continue
            if "\r" in key or "\n" in key or ":" in key or "\r" in value or "\n" in value:
                raise Stop(1, "application metadata contains a line break or invalid key")
            try:
                metadata.append(("%s: %s" % (key, value)).encode("ascii"))
            except UnicodeError:
                raise Stop(1, "application metadata must be ASCII")
        metadata.extend((b"payload-encoding: base64", ("payload-length: %d" % len(payload)).encode("ascii")))
        body = (APP_MAGIC_V2 + b"\r\n" + b"\r\n".join(metadata) +
                b"\r\n\r\n" + self.payload_wire(payload))
        # The Date is fixed when the source is composed; the submission keeps
        # these exact bytes, so every retry posts the same source.
        date = email.utils.format_datetime(
            datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0))
        return (b"From: " + self.config["from"].encode("ascii") + b"\r\n"
                b"Date: " + date.encode("ascii") + b"\r\n"
                b"Newsgroups: " + self.config["group"].encode("ascii") + b"\r\n"
                b"Subject: " + subject.encode("ascii") + b"\r\n"
                b"Message-ID: " + message_id.encode("ascii") + b"\r\n\r\n"
                + body)

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
            raise Stop(code if code in (1, 3) else 4,
                       "hybrid-sign: " + err.decode("utf-8", "replace"))
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
        payload = self.payload_bytes(payload)
        aid = self.config["application_id"]
        prior = self.db.execute(
            "SELECT o.kind,s.source FROM operations o LEFT JOIN submissions s ON s.id=o.submission_id "
            "WHERE o.application_id=? AND o.operation_id=?", (aid, operation_id)).fetchone()
        if prior is not None:
            fields = self.envelope(prior[1]) if prior[1] is not None else None
            if prior[0] != "originated" or fields is None or fields.get("kind") != "report-receipt" or self.payload_bytes(fields.get("payload", "")) != payload:
                raise Stop(1, "operation already has a different report; saved artifact unchanged")
            # Reuse the committed artifact without reading today's keys,
            # changing its Date/context or even producing discarded signatures.
            return
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
                               ("payload", b"received " + self.payload_bytes(fields.get("payload", "")))])
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
        known = self.db.execute(
            "SELECT 1 FROM operations WHERE application_id=? AND operation_id=?",
            (aid, oid)).fetchone()
        if entitled and fields["kind"] == "report-receipt" and \
                principal != self.config["principal_hex"] and known is None:
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
            self.finish_delivery(cursor)
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
        if sequence is None:
            delivery = self.db.execute(
                "SELECT id FROM deliveries WHERE state='pending' AND cursor=?",
                (cursor,)).fetchone()
            if delivery is None:
                raise Stop(4, "unattributed event lacks its retained delivery")
            self.db.execute("INSERT OR IGNORE INTO unattributed_deliveries VALUES (?, ?)",
                            (delivery[0], reason))
        else:
            # This sequence came from the native projection. Unsupported
            # reports have no such coordinate; their exact delivery owns it.
            self.db.execute("INSERT OR IGNORE INTO unattributed VALUES (?, ?)", (sequence, reason))
        self.set_meta("pending_ack", cursor.hex())
        self.set_meta("pending_ack_state", "unsent")
        self.finish_delivery(cursor)
        self.db.execute("COMMIT")

    def finish_delivery(self, cursor):
        """Called in the SAME transaction as inbox handling and pending ACK."""
        self.db.execute("UPDATE deliveries SET state='handled' "
                        "WHERE state='pending' AND cursor=?", (cursor,))

    def delivery(self):
        """Retain exact native output before interpreting or acknowledging it."""
        row = self.db.execute("SELECT before_cursor, cursor, report FROM deliveries "
                              "WHERE state='pending'").fetchone()
        if row is None:
            before = self.position()
            _, cursor, report_path = self.poll()
            report = report_path.read_bytes()
            self.db.execute("BEGIN IMMEDIATE")
            try:
                self.db.execute("INSERT INTO deliveries(before_cursor,cursor,report,state) "
                                "VALUES (?,?,?,'pending')", (before, cursor, report))
                self.db.execute("COMMIT")
            except BaseException:
                if self.db.in_transaction:
                    self.db.execute("ROLLBACK")
                raise
            row = (before, cursor, report)
            cut("after-poll")
        before, cursor, report = row
        cursor_path, report_path = self.scratch("delivery-cursor"), self.scratch("delivery-report")
        cursor_path.write_bytes(cursor)
        report_path.write_bytes(report)
        return before, cursor_path, cursor, report_path

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
        try:
            code = self.ack(cursor)
        except Stop as stopped:
            if stopped.code == 3:
                self.db.execute("BEGIN IMMEDIATE")
                self.set_meta("pending_ack_state", "uncertain")
                self.db.execute("COMMIT")
            raise
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
            before, cursor_path, cursor, report_path = self.delivery()
            report = report_path.read_bytes()
            if not report:
                if cursor == before:
                    self.db.execute("BEGIN IMMEDIATE")
                    self.finish_delivery(cursor)
                    self.db.execute("COMMIT")
                    break
                # An empty page still progresses over the scanned prefix.
                self.db.execute("BEGIN IMMEDIATE")
                self.set_meta("pending_ack", cursor.hex())
                self.set_meta("pending_ack_state", "unsent")
                self.finish_delivery(cursor)
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
                    # PKT-710: a withdrawal event (the author cancelled the
                    # article, or it was superseded) carries a Message-ID
                    # and no content; the native decoder names it.  Nothing
                    # to verify or answer: it is noted and acked.
                    code, out, err = self.native("consumer-article", report_path)
                    if code != 0:
                        raise Stop(code if code in (1, 3) else 4,
                                   "consumer-article: %s %s" % (out.decode(), err.decode()))
                    words = out.decode("ascii", "replace").split()
                    if len(words) == 2 and words[0] == "fn-consumer-withdrawn-v1":
                        line = "withdrawn " + bytes.fromhex(words[1]).decode("ascii", "replace")
                    elif len(words) == 3 and words[0] == "fn-consumer-article-v1":
                        # A valid legacy/unsupported-authorship article is
                        # retained as evidence, not an application operation.
                        line = "unattributed " + line
                    else:
                        raise Stop(4, "unexpected consumer-article output")
                    self.note_unattributed(None, line, cursor)
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
        for sid, message_id, source, principal, aid, oid in q(
                "SELECT id, message_id, source, principal, application_id, operation_id "
                "FROM submissions ORDER BY id"):
            attempts, observed = self.journal(sid)
            rows = q("SELECT purpose, state, exit, status FROM attempts "
                     "WHERE submission_id=%d ORDER BY id" % sid)
            first = self.db.execute(
                "SELECT kind FROM observations WHERE submission_id=? ORDER BY id LIMIT 1",
                (sid,)).fetchone()
            answered = [r for r in rows if r[1] == "answered"]
            outbox.append({
                "message_id": message_id, "sha256": digest(source), "principal": principal,
                "application_id": aid, "operation_id": oid,
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
            "pending_delivery": self.db.execute(
                "SELECT count(*) FROM deliveries WHERE state='pending'").fetchone()[0],
            "unattributed": (q("SELECT count(*) FROM unattributed")[0][0] +
                             q("SELECT count(*) FROM unattributed_deliveries")[0][0]),
        }


def build_parser():
    """The command line's grammar (tools/docs_check.py parses the docs with it)."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("config")
    sub = parser.add_subparsers(dest="command", required=True)
    report = sub.add_parser("report")
    report.add_argument("operation_id")
    report.add_argument("payload", nargs="?")
    report.add_argument("--payload-file", type=Path, help="read the exact payload bytes from a file")
    sub.add_parser("wake")
    sub.add_parser("summary")
    return parser


def main(argv=None):
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.command == "report" and (args.payload is None) == (args.payload_file is None):
        parser.error("report needs exactly one PAYLOAD or --payload-file")
    try:
        consumer = Consumer(args.config)
    except InUse as busy:
        sys.stderr.write("fn_consumer: database in use by pid %s\n" % busy)
        return 1
    try:
        if args.command == "report":
            payload = args.payload_file.read_bytes() if args.payload_file is not None else args.payload
            consumer.originate(args.operation_id, payload)
            consumer.drive_outbox()
        elif args.command == "wake":
            consumer.wake()
        summary = consumer.summary()
        print(json.dumps(summary, sort_keys=True))
        if args.command != "summary":
            entries = summary["outbox"]
            if args.command == "report":
                entries = [entry for entry in entries
                           if entry["application_id"] == consumer.config["application_id"]
                           and entry["operation_id"] == args.operation_id]
            states = {entry["state"] for entry in entries}
            if "uncertain" in states:
                sys.stderr.write("consumer stopped: submission outcome remains uncertain\n")
                return 3
            if "refused" in states:
                sys.stderr.write("consumer stopped: submission refused\n")
                return 1
        return 0
    except Stop as stop:
        if consumer.db.in_transaction:
            consumer.db.execute("ROLLBACK")
        sys.stderr.write("consumer stopped: %s\n" % stop)
        print(json.dumps(consumer.summary(), sort_keys=True))
        return stop.code
    except (ValueError, KeyError, OSError, sqlite3.Error) as fault:
        # Parsing or local persistence failures never become a refusal or
        # permission to advance the declared position. Pending bytes remain.
        if consumer.db.in_transaction:
            consumer.db.execute("ROLLBACK")
        sys.stderr.write("consumer fault: %s\n" % fault)
        return 4


if __name__ == "__main__":
    sys.exit(main())
