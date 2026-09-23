#!/usr/bin/env python3
"""Every feature of fn, driven between two peered fn nodes, one verdict each.

v0 is "every feature of fn is usable between two peered fn servers".  Until
this file existed nobody could say, per feature, whether that was true: the
evidence was spread over `tools/deploy_gate.py`, `tools/twonode_gate.py`,
`tools/inn_lab.py`, `tools/tcpcl_lab.py`, `tools/scale_gate.py` and a set of
hand-written records, and "green" was a step count, not a feature verdict.

    python3 tools/v0_matrix.py dev --host persvati

What it does: stands up two fn nodes A and B on one box, peers them, and
drives the whole surface between them -- init and configuration, principals
and AUTHINFO, POST and the reader profile on both nodes, groups, capacity and
live reconfiguration, transit in both directions, the outbound feed,
checkpoint and recovery, the process-death cut table, TCPCLv4, statements,
carried media, scale, INN and independent clients. Each run writes its own
`planning/evidence/v0-runs/<run-id>/matrix.json` and `report.md`. Use
`--publish-current` to select a non-overlaid, non-simulated HEAD measurement
as `planning/v0-matrix.json`; ordinary lane runs do not replace that dashboard.

**Five verdicts, never collapsed into pass/fail.**  `accepted`, `refused` and
`uncertain` are the three outcomes of D13 and each is a real observation: a
row whose feature IS a refusal (a duplicate offer, a capacity overflow) and
which draws its refusal reads `refused`, and that is the feature working.
`not-exercised` means the row could not run, and `blocker` says exactly why.
`not-built` means the feature is not on the tree yet, and `owner` names the
lane building it.  Whether a row did what it was designed to do is the
separate `agrees` bit: `verdict == expected`.  Nothing here reports a row as
passing because it was skipped, and nothing reports a refusal as a failure.

**The matrix owns no decision that ACL2 owns.**  It derives no identity,
computes no group table, no charge, no frame and no bound.  Every row is an
observation of a reply line, an exit code or a file, and every row names the
exact invocation, the revision, where the log is and what the row does not
show.

**The inventory is declared, not accumulated.**  `PLAN` below is every row
this matrix can emit.  A phase that does not reach a planned row does not
drop it: at the end the matrix emits it as `not-exercised` with "the run
reached its end without this row", so a silently skipped feature is
impossible.  `python3 tools/v0_matrix.py --list` prints the inventory with
its requirement and scenario ids and runs nothing.

**Composition.**  The last two lines on stdout are the contract
`tools/verdict.py` reads from every harness:

    evidence: <path>
    steps=<N> failed=<N> not-exercised=<N>

where `not-exercised` is the `not-exercised` and `not-built` rows summed, so
the fiber table and the matrix cannot disagree.  Exit 0 when every row that
ran agrees with its expectation, 1 when one does not, 2 when the gate stopped
early.

Everything below the rows -- shipping the commit, the certificates, the two
nodes, the peer records, the step accounting, the evidence renderer -- is
`tools/deploy_gate.py`'s and `tools/twonode_gate.py`'s, reused by
subclassing.  This file owns the row inventory, the probes that decide which
rows can run, and the two output files.

Dry run.  ``--dry-run --home DIR`` runs every script through bash on this
machine with ``HOME`` redirected and no ssh, exactly as the other two gates
do; `tests/test_v0_matrix.py` drives the JSON shape, the verdict vocabulary
and one dry-run row that way.

Native first slice. ``--backend native-operator`` takes an explicitly named
saved image and two preprovisioned native configuration paths.  Its only
server candidate is ``packaging/fn-native operator CONFIG run``.  It exercises
the public native status action, NNTP POST, the reader profile on both
listeners, AUTHINFO with a credential the public operator enrolled, live group
administration through the running owner, the wildcard-listener refusal and an
independent stdlib-nntplib client.  It never initializes a store through
Python and never falls back to ``bin/fn``, ``tools/run_owner.py`` or
``tools/run_reader.py``.  The two supplied configurations are never rewritten:
where a row needs a policy they do not set -- ``[auth] required``, a wildcard
listener host, a control path nothing has bound -- the slice synthesizes a
scratch store and configuration of its own and says so in the row's ``limit``.
Native init/reinit and outbound-feed activation remain named non-outcomes until
their public composition exists.  Schema-1 records are historical Python
evidence; new schema-2 records label backend, source revision and image digest
separately.
"""
from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))

import deploy_gate                                             # noqa: E402
import twonode_gate                                            # noqa: E402
from deploy_gate import (DEFAULT_HOST, EXIT_OK, EXIT_REFUSED,   # noqa: E402
                         EXIT_UNCERTAIN, GROUPS, GateError, Host, LocalHost,
                         SshHost, Step, resolve)
from twonode_gate import NodeSpec                               # noqa: E402


ARTICLE_STAMPS: dict = {}


def article_stamp(msgid: str) -> str:
    """One Date per Message-ID, for the life of the run.

    This used to be `datetime.now()` on every call, so building the same
    article twice gave different octets whenever the second build crossed a
    second boundary. An fn node compares a resubmission against the octets it
    already holds (`fn-store-article-match`, `host/store-host.lisp`, over
    `fn-article-payload`), so the varying Date made one row -- a second
    submission of one Message-ID -- answer `DUPLICATE` with exit 0 or
    `REFUSED` with exit 1 depending on the clock. That reads as a violation
    of D13 in the node and is a defect of this harness: the two runs of
    2026-09-22 (03:08Z and 03:21Z) swapped the two nodes' words and nothing
    else. RFC 5536 section 3.1.3 gives one Message-ID one article, so one
    Message-ID gets one Date here, and a row that wants different octets
    under one Message-ID now has to say so.
    """
    if msgid not in ARTICLE_STAMPS:
        ARTICLE_STAMPS[msgid] = dt.datetime.now(dt.timezone.utc).strftime(
            "%a, %d %b %Y %H:%M:%S +0000")
    return ARTICLE_STAMPS[msgid]


def article(msgid: str, group: str, subject: str, body: str, path: str = "") -> bytes:
    """An article as octets, CRLF, with a Date.

    `tools/twonode_gate.py`'s builder omits `Date`, and the local store CLI
    accepts an article without one -- but an fn node refuses it in transit
    with `437 transfer rejected; no Injection-Date or Date` (RFC 5536
    section 3.1.1 makes Date mandatory), which is correct and which made
    every transfer row of the sixth run read as a refusal. Every article the
    matrix offers therefore carries one.

    The same arguments give the same octets every time: the Date comes from
    `article_stamp`, which is fixed per Message-ID.
    """
    stamp = article_stamp(msgid)
    headers = ["Path: {}!not-for-mail".format(path)] if path else []
    headers += ["From: gate@example.invalid",
                "Subject: {}".format(subject),
                "Newsgroups: {}".format(group),
                "Date: {}".format(stamp),
                "Message-ID: {}".format(msgid)]
    return ("\r\n".join(headers) + "\r\n\r\n" + body + "\r\n").encode()

MATRIX_JSON = "planning/v0-matrix.json"
LEGACY_SCHEMA_VERSION = 1
SCHEMA_VERSION = 2

DEVELOPMENT_BACKEND = "development-python"
NATIVE_BACKEND = "native-operator"
BACKENDS = (DEVELOPMENT_BACKEND, NATIVE_BACKEND)

# The five verdicts.  The first three are D13's outcomes; the last two are the
# two ways a row can fail to be an outcome at all.
ACCEPTED, REFUSED, UNCERTAIN = "accepted", "refused", "uncertain"
NOT_EXERCISED, NOT_BUILT = "not-exercised", "not-built"
VERDICTS = (ACCEPTED, REFUSED, UNCERTAIN, NOT_EXERCISED, NOT_BUILT)
OUTCOMES = (ACCEPTED, REFUSED, UNCERTAIN)

# NNTP response codes that are the server saying it could not tell, rather
# than the server deciding.  RFC 3977 section 3.2.1: 400 service discontinued,
# 403 internal fault, 503 feature not supported for a reason of its own.
FAULT_CODES = frozenset(("400", "403", "503"))
# RFC 3977 section 3.2.1: the verb is not there at all.  502 is NOT in this
# set -- measured on persvati 2026-09-20, an fn node answers `IHAVE` with
# "502 transit is not permitted on this connection", which is the node
# dispatching the command and deciding about the caller, not the command
# being absent.  Reading 502 as "not built" would have reported a working
# transit surface as missing.
UNSUPPORTED_CODES = frozenset(("500", "501"))
# The verb is there and this caller may not use it: a permission answer, not
# a decision about the argument.
NOT_PERMITTED_CODES = frozenset(("440", "480", "483", "502"))

# Who made the observation.  The first three are fn's own code talking to fn,
# which is the weak case: a row seen only by these is marked `independent:
# false` and counted separately in the summary.
CLIENT_CLI = "fn CLI (exit code)"
CLIENT_DRIVER = "the matrix's raw-socket driver"
CLIENT_LAB = "an fn harness (tcpcl_lab, campaign, scale_gate)"
FN_CLIENTS = frozenset((CLIENT_CLI, CLIENT_DRIVER, CLIENT_LAB))

FEATURES = (
    ("F-NODE", "node init, configuration, start and stop"),
    ("F-OUT", "the three outcomes on the operator surface"),
    ("F-GROUP", "groups, capacity, peers and live reconfiguration"),
    ("F-AUTH", "principals, AUTHINFO and posting permission"),
    ("F-POST", "POST and its read-back"),
    ("F-READ", "the reader profile on each node"),
    ("F-PIN", "capability truthfulness"),
    ("F-TRANSIT", "transit inbound, A to B and B to A"),
    ("F-FEED", "the owner-driven outbound feed"),
    ("F-CRASH", "checkpoint, recovery and the process-death cut table"),
    ("F-BP", "BP over TCPCLv4 between the two nodes"),
    ("F-STX", "statement sign and verify across the pair"),
    ("F-MEDIA", "the carried-media letter"),
    ("F-SCALE", "scale"),
    ("F-INN", "INN as a third node"),
    ("F-CLIENT", "independent newsreader clients"),
)
FEATURE_TITLES = dict(FEATURES)


class Spec:
    """One planned row: what it is about, and what outcome it is designed for.

    `scope` is "single" (one row), "node" (one row per node, id suffixed
    `-A`/`-B`) or "direction" (one per feed direction, `-AB`/`-BA`).
    `expected` is the outcome class the row is designed to observe, or None
    for a probe whose result is the finding rather than a pass or a fail.
    """

    __slots__ = ("key", "feature", "title", "requirements", "scenarios",
                 "expected", "scope", "limit")

    def __init__(self, key, feature, title, requirements, scenarios, expected,
                 scope="single", limit=""):
        self.key = key
        self.feature = feature
        self.title = title
        self.requirements = tuple(requirements)
        self.scenarios = tuple(scenarios)
        self.expected = expected
        self.scope = scope
        self.limit = limit

    def ids(self):
        if self.scope == "node":
            return ["{}-{}".format(self.key, s) for s in ("A", "B")]
        if self.scope == "direction":
            return ["{}-{}".format(self.key, s) for s in ("AB", "BA")]
        return [self.key]


def S(*args, **kwargs):
    return Spec(*args, **kwargs)


# --------------------------------------------------------------------------
# The inventory.  Every row this matrix can emit is here and nowhere else.

PLAN = (
    # -- F-NODE ----------------------------------------------------------
    S("V0-NODE-INIT", "F-NODE", "fn init creates the store and writes fn.toml",
      ("HST-003",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-NODE-CONFIG", "F-NODE", "fn.toml carries [store] path and [acl2] path",
      ("HST-004",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-NODE-REINIT", "F-NODE",
      "what a second fn init over a store that already holds articles does",
      ("HST-003",), ("SCN-021",), None, "node",
      "nothing in docs/operator.md says whether a second `init` adopts the store "
      "or refuses, so this row records the outcome rather than asserting one; the "
      "property that matters is the next row"),
    S("V0-NODE-REINIT-SAFE", "F-NODE",
      "the articles the store already held are still there after the second init",
      ("STO-003", "OBJ-005"), ("SCN-021",), ACCEPTED, "node"),
    S("V0-NODE-STATUS", "F-NODE", "fn status reports generation and article count",
      ("HST-002",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-NODE-START", "F-NODE", "the service starts and reaches LISTENING",
      ("HST-001",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-NODE-STOP", "F-NODE", "the service stops and releases the store",
      ("HST-002",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-NODE-LOOPBACK", "F-NODE",
      "a non-loopback listener host is refused rather than silently bound",
      ("HST-003",), ("SCN-021",), REFUSED),
    S("V0-NODE-PROFILE", "F-NODE",
      "the operator honours `[log] path` (a post's line lands in the file) and "
      "refuses `[posting] agent` by name",
      ("HST-003",), ("SCN-021",), ACCEPTED),

    # -- F-OUT -----------------------------------------------------------
    S("V0-OUT-ACCEPTED", "F-OUT", "an accepted post exits 0",
      ("FLR-002",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-OUT-REFUSED", "F-OUT", "a lookup of an article the node does not hold exits 1",
      ("FLR-002",), ("SCN-021",), REFUSED, "node"),
    S("V0-OUT-UNCERTAIN", "F-OUT",
      "a post interrupted after publication exits 3 and fences the store",
      ("FLR-002", "STO-004"), ("SCN-003",), UNCERTAIN, "node"),
    S("V0-OUT-RECOVER", "F-OUT", "recover after the uncertain publication exits 0",
      ("STO-005",), ("SCN-003",), ACCEPTED, "node"),

    # -- F-GROUP ---------------------------------------------------------
    S("V0-GROUP-CREATE", "F-GROUP", "fn group create adds a served group",
      ("STO-001",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-GROUP-SERVED", "F-GROUP", "the new group is served over the socket",
      ("NNT-006",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-GROUP-RETIRE", "F-GROUP", "fn group retire removes it again",
      ("STO-001",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-GROUP-UNKNOWN", "F-GROUP",
      "retiring a group the node does not serve is refused", ("STO-001",),
      ("SCN-021",), REFUSED, "node"),
    S("V0-CAP-SET", "F-GROUP", "fn capacity sets the retention capacity",
      ("RET-002",), ("SCN-007",), ACCEPTED, "node"),
    S("V0-CAP-REFUSE", "F-GROUP",
      "an article that does not fit the capacity is refused before it is written",
      ("RET-002",), ("SCN-007",), REFUSED, "node"),
    S("V0-PEER-ADD", "F-GROUP", "fn peer add writes a transit peer record",
      ("REP-001",), ("SCN-023",), ACCEPTED, "node"),
    S("V0-PEER-LIST", "F-GROUP", "fn peer list reads the record back",
      ("REP-001",), ("SCN-023",), ACCEPTED, "node"),
    S("V0-PEER-ABSENT", "F-GROUP", "fn peer remove of a peer that is not there is refused",
      ("REP-001",), ("SCN-023",), REFUSED),
    S("V0-PEER-REMOVE", "F-GROUP", "fn peer remove of a configured peer is accepted",
      ("REP-001",), ("SCN-023",), ACCEPTED),
    S("V0-CFG-LIVE", "F-GROUP",
      "a group declared on the running service's control channel reaches the served "
      "configuration", ("NNT-007",), ("SCN-021",), ACCEPTED),
    S("V0-CFG-LIVE-REFUSE", "F-GROUP",
      "an offline configuration command is refused while the service holds the store",
      ("HST-002",), ("SCN-021",), REFUSED),

    # -- F-AUTH ----------------------------------------------------------
    S("V0-AUTH-NEW", "F-AUTH", "fn principal new derives a principal id from a seed",
      ("OBJ-007",), ("SCN-022",), ACCEPTED),
    S("V0-AUTH-PASSWORD", "F-AUTH",
      "fn principal set-password records an AUTHINFO credential",
      ("OBJ-007",), ("SCN-022",), ACCEPTED, "node"),
    S("V0-AUTH-LIST", "F-AUTH", "fn principal list shows the credential",
      ("OBJ-007",), ("SCN-022",), ACCEPTED, "node"),
    S("V0-AUTH-ADVERTISED", "F-AUTH",
      "AUTHINFO USER is advertised while the connection is unauthenticated",
      ("NNT-001",), ("SCN-022",), ACCEPTED, "node"),
    S("V0-AUTH-GATED", "F-AUTH", "POST before a login is refused, not performed",
      ("NNT-001",), ("SCN-022",), REFUSED, "node"),
    S("V0-AUTH-LOGIN", "F-AUTH", "AUTHINFO USER then PASS answers 281",
      ("OBJ-007",), ("SCN-022",), ACCEPTED, "node"),
    S("V0-AUTH-WITHDRAWN", "F-AUTH",
      "AUTHINFO is no longer advertised once the connection is authenticated",
      ("NNT-001",), ("SCN-022",), ACCEPTED, "node"),
    S("V0-AUTH-POST", "F-AUTH", "POST after the login is accepted",
      ("NNT-004",), ("SCN-022",), ACCEPTED, "node"),
    S("V0-AUTH-WRONG", "F-AUTH", "a wrong password answers 481 and grants nothing",
      ("OBJ-007",), ("SCN-022",), REFUSED, "node"),

    # -- F-POST ----------------------------------------------------------
    S("V0-POST-OPEN", "F-POST", "POST on the served socket answers 340",
      ("NNT-005",), ("SCN-002",), ACCEPTED, "node"),
    S("V0-POST-COMMIT", "F-POST", "the article is accepted with 240",
      ("NNT-005",), ("SCN-002",), ACCEPTED, "node"),
    S("V0-POST-READBACK", "F-POST",
      "the posting connection's next GROUP already counts the article",
      ("NNT-005",), ("SCN-002",), ACCEPTED, "node"),
    S("V0-POST-FRESH", "F-POST", "a fresh connection reads it back by Message-ID",
      ("NNT-006",), ("SCN-002",), ACCEPTED, "node"),
    S("V0-POST-DUPLICATE", "F-POST",
      "a second POST of the same Message-ID is refused and allocates nothing",
      ("OBJ-002", "OBJ-005"), ("SCN-002",), REFUSED, "node"),
    S("V0-POST-CLOCK", "F-POST",
      "a duplicate POST is refused as an article and does not cost the node its clock",
      ("FLR-002", "NNT-005"), ("SCN-002",), ACCEPTED, "node"),
    # RFC 5536 3.1.2: From is a mailbox-list.  The agents run of 2026-09-22
    # posted `From: yue` and was answered 240 (books/injection.lisp checked
    # presence only); the node now refuses it `441 posting failed; From is not
    # a valid mailbox list` (fn-inj-decide's :from-invalid).
    S("V0-POST-FROM-MAILBOX", "F-POST",
      "a POST whose From names no address (`From: yue`) is refused with 441 and "
      "is not served",
      ("NNT-005",), ("SCN-002",), REFUSED, "node"),
    S("V0-POST-CONCURRENT", "F-POST",
      "a second reader stays live across another connection's whole POST",
      ("HST-002",), ("SCN-015",), ACCEPTED),

    # -- F-READ ----------------------------------------------------------
    S("V0-READ-CAPABILITIES", "F-READ", "CAPABILITIES",
      ("NNT-001",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-MODE-READER", "F-READ", "MODE READER",
      ("NNT-002",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-LIST-ACTIVE", "F-READ", "LIST ACTIVE",
      ("NNT-006",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-LIST-NEWSGROUPS", "F-READ", "LIST NEWSGROUPS",
      ("NNT-006",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-LIST-NEWSGROUPS-WILDMAT", "F-READ",
      "LIST NEWSGROUPS filtered by a wildmat",
      ("NNT-006",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-LIST-OVERVIEW-FMT", "F-READ", "LIST OVERVIEW.FMT",
      ("NNT-001",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-LIST-ACTIVE-TIMES", "F-READ", "LIST ACTIVE.TIMES",
      ("NNT-006",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-LIST-HEADERS", "F-READ", "LIST HEADERS",
      ("NNT-001",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-GROUP", "F-READ", "GROUP",
      ("NNT-002", "NNT-006"), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-LISTGROUP", "F-READ", "LISTGROUP with a range",
      ("NNT-002",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-ARTICLE", "F-READ", "ARTICLE by number",
      ("NNT-006",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-HEAD", "F-READ", "HEAD by number",
      ("NNT-006",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-BODY", "F-READ", "BODY by number",
      ("NNT-006",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-STAT", "F-READ", "STAT by number",
      ("NNT-002",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-ARTICLE-MSGID", "F-READ", "ARTICLE by Message-ID",
      ("OBJ-002", "NNT-006"), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-ARTICLE-ABSENT", "F-READ",
      "ARTICLE of a Message-ID the node does not hold is refused",
      ("NNT-006",), ("SCN-014",), REFUSED, "node"),
    S("V0-READ-OVER", "F-READ", "OVER for one article",
      ("NNT-006",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-OVER-RANGE", "F-READ", "OVER over a range",
      ("NNT-006",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-HDR", "F-READ", "HDR Subject",
      ("NNT-006",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-XOVER", "F-READ", "XOVER (the legacy spelling)",
      ("NNT-001",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-XHDR", "F-READ", "XHDR (the legacy spelling)",
      ("NNT-001",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-XPAT", "F-READ", "XPAT Subject",
      ("NNT-001",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-NEXT", "F-READ", "NEXT moves the cursor",
      ("NNT-002",), ("SCN-014",), None, "node",
      "the expected outcome depends on how many articles the group holds; the "
      "row records the count it was run against"),
    S("V0-READ-LAST", "F-READ", "LAST moves the cursor back",
      ("NNT-002",), ("SCN-014",), None, "node",
      "the expected outcome depends on where the cursor was"),
    S("V0-READ-NEWNEWS", "F-READ",
      "NEWNEWS over a wildmat, since an instant before the store existed",
      ("NNT-008",), ("SCN-014",), ACCEPTED, "node",
      "the node under test may hold no article whose Injection-Date or Date "
      "fn can decode, in which case 230 with an empty block is the correct "
      "answer and the row records the framing, not a reported identifier"),
    S("V0-READ-NEWNEWS-FUTURE", "F-READ",
      "NEWNEWS since a future instant returns the empty block",
      ("NNT-008",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-NEWNEWS-SYNTAX", "F-READ",
      "NEWNEWS with a malformed wildmat is refused with 501",
      ("NNT-008",), ("SCN-014",), REFUSED, "node"),
    S("V0-READ-DATE", "F-READ", "DATE",
      ("NNT-002",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-HELP", "F-READ", "HELP",
      ("NNT-002",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-READ-UNKNOWN", "F-READ", "an unknown command is refused with 500",
      ("NNT-002",), ("SCN-014",), REFUSED, "node"),
    S("V0-READ-FRAMING", "F-READ",
      "a command split across two TCP segments is answered once, the same way",
      ("NNT-003",), ("SCN-014",), ACCEPTED, "node"),

    # -- F-PIN -----------------------------------------------------------
    S("V0-PIN-DISPATCHED", "F-PIN",
      "every capability the node advertises is dispatched by the node",
      ("NNT-001",), ("SCN-014",), ACCEPTED, "node"),
    S("V0-PIN-ADVERTISED", "F-PIN",
      "every command the node dispatches is advertised in CAPABILITIES",
      ("NNT-001",), ("SCN-014",), ACCEPTED, "node"),

    # -- F-TRANSIT -------------------------------------------------------
    S("V0-TRANSIT-IDENTITY", "F-TRANSIT",
      "the node has an RFC 5537 <path-identity> of its own",
      ("REP-002",), ("SCN-023",), ACCEPTED, "node",
      "`fn-peer-local-identity` reads the `path-identity` policy slot and an "
      "unset slot is the empty string, which `fn-path-names-p` never matches: "
      "a node without this answers no loop, so V0-TRANSIT-LOOP rests on it"),
    S("V0-TRANSIT-INDEPENDENT", "F-TRANSIT",
      "each node serves its own seeded articles and 43x for the other's seeds",
      ("OBJ-005",), ("SCN-023",), ACCEPTED, "node"),
    S("V0-TRANSIT-MODE-STREAM", "F-TRANSIT", "MODE STREAM is accepted on the peer connection",
      ("REP-001",), ("SCN-023",), ACCEPTED, "direction"),
    S("V0-TRANSIT-OFFER", "F-TRANSIT", "IHAVE of a wanted article answers 335",
      ("REP-001",), ("SCN-023",), ACCEPTED, "direction"),
    S("V0-TRANSIT-TRANSFER", "F-TRANSIT", "the transferred article is taken with 235",
      ("REP-001", "NNT-005"), ("SCN-023",), ACCEPTED, "direction"),
    S("V0-TRANSIT-IDENTICAL", "F-TRANSIT",
      "the far side serves the same octets the source served",
      ("OBJ-001",), ("SCN-023",), ACCEPTED, "direction"),
    S("V0-TRANSIT-DUPLICATE", "F-TRANSIT",
      "a second IHAVE of the same Message-ID is refused with 435",
      ("REP-002",), ("SCN-023",), REFUSED, "direction"),
    S("V0-TRANSIT-LOOP", "F-TRANSIT",
      "an article whose Path already names the target is refused after its 335",
      ("REP-002",), ("SCN-023",), REFUSED, "direction"),
    S("V0-TRANSIT-LOOP-ABSENT", "F-TRANSIT",
      "the refused loop article is not served by the target afterwards",
      ("REP-002",), ("SCN-023",), REFUSED, "direction"),
    S("V0-TRANSIT-CHECK-FRESH", "F-TRANSIT",
      "CHECK of a Message-ID the target has not seen answers 238",
      ("REP-001",), ("SCN-023",), ACCEPTED, "direction"),
    S("V0-TRANSIT-TAKETHIS", "F-TRANSIT",
      "TAKETHIS of that wanted article answers 239",
      ("REP-001",), ("SCN-023",), ACCEPTED, "direction"),
    S("V0-TRANSIT-CHECK-DUP", "F-TRANSIT",
      "CHECK of an article the target holds answers 438",
      ("REP-002",), ("SCN-023",), REFUSED, "direction"),
    S("V0-TRANSIT-TAKETHIS-DUP", "F-TRANSIT",
      "TAKETHIS that ignores that advice answers 439, never a 2xx and never a retry",
      ("REP-002",), ("SCN-023",), REFUSED, "direction"),
    # The owner's own feed over the protected channel (PRF-047, PRF-051;
    # plan 2026-09-22 T9c).  Measured by tests/test_native_protected_peering
    # on two saved-image owners of its own, never on the supplied nodes: the
    # target requires authentication and refuses AUTHINFO before TLS, the
    # source's peer record names STARTTLS, the target's certificate as its
    # only anchor, server name `localhost`, and a credential profile, and the
    # target's record binds the inbound peer role to that principal.
    S("V0-TRANSIT-TLS", "F-TRANSIT",
      "the owner's feed reaches the peer over STARTTLS, the peer's certificate "
      "verified against the record's anchor and server name",
      ("REP-005", "HST-004"), ("SCN-024",), ACCEPTED, "direction",
      "the article's arrival under a target that refuses AUTHINFO before TLS and "
      "answers an unauthenticated IHAVE 480 is what shows the channel; the matrix "
      "does not see the feed's own socket, and OpenSSL's chain and hostname checks "
      "are trusted integration (PRF-047)"),
    S("V0-TRANSIT-AUTHINFO", "F-TRANSIT",
      "the owner's feed logs in with AUTHINFO as the principal the peer's record "
      "binds before it offers, and the peer takes the offer in that role",
      ("REP-005", "HST-004"), ("SCN-024",), ACCEPTED, "direction",
      "the same arrival: an unauthenticated offer of the same article is 480 on "
      "the target, so the feed's offer came on a connection that logged in; "
      "PRF-051's keystones are what say the feed sends no offer before the 281"),
    S("V0-TRANSIT-TLS-WRONG-ANCHOR", "F-TRANSIT",
      "a feed whose record names an anchor that did not issue the peer's "
      "certificate delivers nothing, and both owners stay up",
      ("HST-004",), ("SCN-024",), REFUSED),
    S("V0-TRANSIT-AUTHINFO-WRONG", "F-TRANSIT",
      "a feed whose profile carries a wrong password delivers nothing, and both "
      "owners stay up",
      ("HST-004",), ("SCN-024",), REFUSED),

    # -- F-FEED ----------------------------------------------------------
    S("V0-FEED-QUEUE", "F-FEED",
      "an article accepted on the source enters the matching peer's outbound queue",
      ("REP-005",), ("SCN-024",), ACCEPTED),
    S("V0-FEED-OFFER", "F-FEED",
      "the owner opens the session and offers it, with no hand-driven socket",
      ("REP-005",), ("SCN-024",), ACCEPTED),
    S("V0-FEED-ONCE", "F-FEED", "an acknowledged transfer is not offered a second time",
      ("REP-005", "REP-002"), ("SCN-024",), ACCEPTED),
    S("V0-FEED-JOURNAL", "F-FEED",
      "the feed journal records the transfer and survives a restart",
      ("RET-003", "STO-003"), ("SCN-024",), ACCEPTED),

    # -- F-CRASH ---------------------------------------------------------
    S("V0-CRASH-CHECKPOINT", "F-CRASH",
      "a checkpoint is published and the store reopens from it",
      ("STO-006",), ("SCN-004",), ACCEPTED),
    S("V0-CRASH-KILL", "F-CRASH",
      "node B is SIGKILLed inside a transfer it had already agreed to take",
      ("STO-005", "FLR-002"), ("SCN-003",), None, "single",
      "what the client saw is recorded; an acknowledgement after the kill would be "
      "the defect, and its absence is the assertion"),
    S("V0-CRASH-SURVIVOR", "F-CRASH", "node A is unaffected by node B's death",
      ("HST-002",), ("SCN-003",), ACCEPTED),
    S("V0-CRASH-RECOVER", "F-CRASH", "node B recovers through the real recovery path",
      ("STO-005",), ("SCN-003",), ACCEPTED),
    S("V0-CRASH-ACKNOWLEDGED", "F-CRASH",
      "everything node B acknowledged is still there after the recovery",
      ("STO-003", "STO-005"), ("SCN-003",), ACCEPTED),
    S("V0-CRASH-INTERRUPTED", "F-CRASH",
      "the interrupted transfer is not there after the recovery",
      ("STO-005",), ("SCN-003",), REFUSED),
    S("V0-CRASH-RESTART", "F-CRASH", "node B serves again after the recovery",
      ("HST-003",), ("SCN-003",), ACCEPTED),
    S("V0-CRASH-CUT-TABLE", "F-CRASH",
      "the declared cut table still matches the fault points in the host",
      ("FLR-001",), ("SCN-003",), ACCEPTED),
    S("V0-CRASH-CAMPAIGN", "F-CRASH",
      "the process-death campaign runs its cuts and each recovers to a state the "
      "model expresses", ("FLR-001", "STO-005"), ("SCN-003",), ACCEPTED),

    # -- F-BP ------------------------------------------------------------
    S("V0-BP-IMAGE", "F-BP", "the native image carrying the convergence layer builds",
      ("HST-001",), ("SCN-025",), ACCEPTED),
    S("V0-BP-EXCHANGE", "F-BP", "one bundle each way inside one TCPCLv4 session",
      ("REP-006",), ("SCN-025",), ACCEPTED),
    S("V0-BP-REFUSED", "F-BP", "a contact the layer refuses is refused",
      ("REP-006",), ("SCN-025",), REFUSED),
    S("V0-BP-KEEPALIVE", "F-BP", "the session keepalive holds an idle contact open",
      ("FLR-004",), ("SCN-025",), ACCEPTED),
    S("V0-BP-CRASH", "F-BP", "an interrupted contact loses and duplicates nothing",
      ("FLR-004",), ("SCN-025",), ACCEPTED),
    S("V0-BP-PROFILE", "F-BP", "the session profile is the one the layer declared",
      ("REP-006",), ("SCN-025",), ACCEPTED),
    S("V0-BP-REPLAY", "F-BP", "the transfer replays from the session log",
      ("REP-006",), ("SCN-025",), ACCEPTED),
    S("V0-BP-NODE", "F-BP",
      "a BP node behind the layer carries an fn article between the two nodes",
      ("REP-006", "REP-003"), ("SCN-017",), ACCEPTED),

    # -- F-STX -----------------------------------------------------------
    S("V0-STX-SIGN", "F-STX", "fn statement sign produces a canonical FN-Statement field",
      ("SUB-001",), ("SCN-019",), ACCEPTED),
    S("V0-STX-ATTACH", "F-STX", "the field is attached to an article as a header line",
      ("SUB-001",), ("SCN-019",), ACCEPTED),
    S("V0-STX-CROSS", "F-STX",
      "the statement-bearing article crosses to the other node unchanged",
      ("SUB-001", "SUB-003"), ("SCN-019",), ACCEPTED),
    S("V0-STX-VERIFY", "F-STX", "the receiving node computes its own verdict on it",
      ("SUB-002",), ("SCN-019",), ACCEPTED),
    S("V0-STX-UNVERIFIED", "F-STX",
      "a tampered statement is unverified, distinct from absent",
      ("SUB-002",), ("SCN-019",), REFUSED),
    S("V0-STX-READER", "F-STX",
      "the reader exposes the statement octets and the recorded verdict",
      ("SUB-006",), ("SCN-019",), ACCEPTED),

    # -- F-MEDIA ---------------------------------------------------------
    S("V0-MEDIA-EXPORT", "F-MEDIA", "a carried volume is written from one node's store",
      ("REP-004",), ("SCN-001",), ACCEPTED),
    S("V0-MEDIA-VERIFY", "F-MEDIA", "the volume's copy check passes on its own",
      ("REP-004",), ("SCN-001",), ACCEPTED),
    S("V0-MEDIA-IMPORT", "F-MEDIA", "the other node imports it as a network receipt",
      ("REP-004", "RET-003"), ("SCN-001",), ACCEPTED),

    # -- F-SCALE ---------------------------------------------------------
    S("V0-SCALE-CEILING", "F-SCALE",
      "the store size at which a post or a recover crosses its deadline",
      ("STO-001",), ("SCN-015",), ACCEPTED, "single",
      "a measured ceiling on one box with one payload grid; it is not a bound and "
      "not a proof"),

    # -- F-INN -----------------------------------------------------------
    S("V0-INN-INTEROP", "F-INN",
      "a real INN server exchanges with an fn node as a third peer",
      ("REP-001",), ("SCN-023",), ACCEPTED),
    # One row per exchange tools/inn_lab.py decides; `INN_ROWS` names the lab
    # findings each is read from.  The fn side is the native image (D07).
    S("V0-INN-FEED-OUT", "F-INN",
      "an article POSTed to fn reaches INN through fn's outbound feed "
      "(IHAVE 335/235) and nnrpd serves it changed only in Path and Xref",
      ("REP-001",), ("SCN-023",), ACCEPTED),
    S("V0-INN-FEED-IN", "F-INN",
      "INN's innfeed delivers an article to fn (CHECK 238, TAKETHIS 239) and fn "
      "serves it changed at most in Path and Xref",
      ("REP-001",), ("SCN-023",), ACCEPTED),
    S("V0-INN-DUPLICATE-INN", "F-INN",
      "INN refuses a second IHAVE of the article fn fed it with 435",
      ("REP-002",), ("SCN-023",), REFUSED),
    S("V0-INN-DUPLICATE-FN", "F-INN",
      "fn refuses a second IHAVE of each article it holds (INN's and its own) with 435",
      ("REP-002",), ("SCN-023",), REFUSED),
    S("V0-INN-LOOP-INN", "F-INN",
      "INN refuses an article whose Path names it with 437",
      ("REP-002",), ("SCN-023",), REFUSED),
    S("V0-INN-LOOP-FN", "F-INN",
      "fn refuses an article whose Path names its own path identity, and does not "
      "serve it",
      ("REP-002",), ("SCN-023",), REFUSED),
    S("V0-INN-RESTART", "F-INN",
      "INN's history survives a SIGKILL of innd, and fn's articles survive a SIGTERM, "
      "recover and restart byte-identical",
      ("STO-005", "REP-002"), ("SCN-023",), ACCEPTED),
    S("V0-INN-SERVING-AGENT", "F-INN",
      "an article fn took from INN is served with fn's path identity in Path and "
      "without INN's Xref (RFC 5537 3.7 steps 6 and 7)",
      ("REP-001",), ("SCN-023",), ACCEPTED, "single",
      "fn updates Path and removes Xref once, when it accepts the transfer, and "
      "stores what it serves (specs/peering.md 2.3, books/path-update.lisp); the "
      "reader path is what this row measures, and the outbound render to a "
      "second peer is not exercised by a lab with one peer"),
    S("V0-INN-OPERATOR-POST", "F-INN",
      "an article submitted through `operator post` reaches INN through fn's feed, "
      "injected with fn's Path (IHAVE 335/235)",
      ("REP-001",), ("SCN-023",), ACCEPTED),

    # -- F-CLIENT --------------------------------------------------------
    S("V0-CLIENT-NNTPLIB", "F-CLIENT",
      "an independent stdlib nntplib client reads a group and an article",
      ("NNT-002", "NNT-003"), ("SCN-014",), ACCEPTED, "node"),
    S("V0-CLIENT-SLRN", "F-CLIENT", "slrn reads a group and an article",
      ("NNT-002",), ("SCN-014",), ACCEPTED),
)

PLAN_BY_KEY = {spec.key: spec for spec in PLAN}

# The INN rows, each read from the tools/inn_lab.py findings named here
# (`key[instance]`).  A row whose findings all held carries its expected
# verdict; one with a violated finding carries the opposite outcome, which
# `derive` then reads as a disagreement; anything else is not-exercised.
INN_ROWS = (
    ("V0-INN-FEED-OUT", ("fn-post-240", "fn-feeds-inn", "inn-serves-fn-article")),
    ("V0-INN-FEED-IN", ("innfeed-feeds-fn", "fn-serves-inn-article")),
    ("V0-INN-DUPLICATE-INN", ("inn-duplicate-435[fn-article]",)),
    ("V0-INN-DUPLICATE-FN", ("fn-duplicate-435[inn-article]",
                             "fn-duplicate-435[fn-article]")),
    ("V0-INN-LOOP-INN", ("inn-loop-437",)),
    ("V0-INN-LOOP-FN", ("fn-loop-refused",)),
    ("V0-INN-RESTART", ("fn-term-stopped", "fn-recover",
                        "fn-articles-survived-term[fn-article]",
                        "fn-articles-survived-term[inn-article]", "innd-died",
                        "innd-restarted", "inn-history-survived-kill[inn-article]",
                        "inn-history-survived-kill[fn-article]")),
    ("V0-INN-SERVING-AGENT", ("fn-serves-own-path-identity",
                              "fn-serves-no-sender-xref")),
    ("V0-INN-OPERATOR-POST", ("operator-post-feeds-inn",)),
)
INN_ROW_KEYS = ("V0-INN-INTEROP",) + tuple(key for key, _ in INN_ROWS)


def inn_rows(findings: dict) -> list:
    """(row key, verdict, observed, blocker) for every INN row, from the lab's
    `<evidence>.findings.json`.  Pure: the lab decided each finding; this only
    reads them, so the matrix computes nothing about INN of its own."""
    table = {}
    for row in findings.get("rows", []):
        name = row.get("key", "") + ("[{}]".format(row["instance"])
                                     if row.get("instance") else "")
        table[name] = row
    out = []
    lab = findings.get("verdict")
    out.append(("V0-INN-INTEROP",
                {"held": ACCEPTED, "violated": REFUSED}.get(lab, NOT_EXERCISED),
                "the lab's verdict: {} ({})".format(lab, ", ".join(
                    "{} {}".format(n, v) for v, n in sorted(
                        findings.get("counts", {}).items()) if n) or "no findings"),
                None if lab in ("held", "violated") else
                "the lab's verdict was {!r}, which decides nothing".format(lab)))
    for key, names in INN_ROWS:
        expected = PLAN_BY_KEY[key].expected
        found = [table.get(name) for name in names]
        observed = "; ".join("{}={}{}".format(
            name, row.get("verdict") if row else "absent",
            " ({})".format(row["observed"]) if row and row.get("observed") else "")
            for name, row in zip(names, found))
        verdicts = {row.get("verdict") if row else None for row in found}
        if verdicts <= {"held"}:
            out.append((key, expected, observed, None))
        elif "violated" in verdicts and verdicts <= {"held", "violated"}:
            out.append((key, REFUSED if expected == ACCEPTED else ACCEPTED,
                        observed, None))
        else:
            out.append((key, NOT_EXERCISED, observed,
                        "the lab did not decide every finding this row reads: "
                        + observed))
    return out
PLANNED_IDS = [rid for spec in PLAN for rid in spec.ids()]
assert len(PLANNED_IDS) == len(set(PLANNED_IDS)), "duplicate row id in PLAN"


class Row:
    """One emitted row: a verdict, and everything needed to check it."""

    __slots__ = ("id", "spec", "node", "direction", "verdict", "invocation",
                 "observed", "exit_code", "log", "limit", "blocker", "owner",
                 "client")

    def __init__(self, rid, spec, verdict, invocation, observed, exit_code,
                 log, limit, blocker, owner, node=None, direction=None,
                 client=None):
        self.id = rid
        self.spec = spec
        self.node = node
        self.direction = direction
        self.verdict = verdict
        self.invocation = invocation
        self.observed = observed
        self.exit_code = exit_code
        self.log = log
        self.limit = limit
        self.blocker = blocker
        self.owner = owner
        self.client = client

    @property
    def independent(self):
        """True only when something that is not fn's own code made the
        observation. A feature "usable between two peered servers" that only
        fn's own client has ever seen is a weaker claim than it reads, and
        the matrix says which rows those are rather than letting the reader
        assume otherwise."""
        if self.verdict not in OUTCOMES or not self.client:
            return None
        return self.client not in FN_CLIENTS

    @property
    def agrees(self):
        if self.verdict not in OUTCOMES or self.spec.expected is None:
            return None
        return self.verdict == self.spec.expected

    def json(self, revision, execution=None):
        execution = execution or {
            "backend": DEVELOPMENT_BACKEND,
            "source": revision,
            "image": "development Python entry points from {}".format(revision),
        }
        limit = "; ".join(x for x in (self.spec.limit, self.limit) if x)
        return {
            "id": self.id,
            "feature": self.spec.feature,
            "feature_title": FEATURE_TITLES[self.spec.feature],
            "title": self.spec.title,
            "node": self.node,
            "direction": self.direction,
            "requirements": list(self.spec.requirements),
            "scenarios": list(self.spec.scenarios),
            "verdict": self.verdict,
            "expected": self.spec.expected,
            "agrees": self.agrees,
            "client": self.client,
            "independent": self.independent,
            "invocation": self.invocation,
            "observed": self.observed,
            "exit_code": self.exit_code,
            "revision": revision,
            "backend": execution["backend"],
            "source": execution["source"],
            "image": execution["image"],
            "log": self.log,
            "limit": limit,
            "blocker": self.blocker,
            "owner": self.owner,
        }


def reply_verdict(status: str) -> str:
    """The outcome class of one NNTP status line, and nothing more.

    RFC 3977 section 3.2.  1xx/2xx/3xx: the server did the thing or is ready
    to.  4xx/5xx: the server decided not to -- except the three codes that
    mean it could not tell, which are the uncertain outcome.  Anything that is
    not a status line at all (a reset, an EOF, a timeout) is uncertain too:
    the node did not say.
    """
    code = (status or "").strip()[:3]
    if not code.isdigit():
        return UNCERTAIN
    if code in FAULT_CODES:
        return UNCERTAIN
    return ACCEPTED if code[0] in "123" else REFUSED


def from_mailbox_verdict(posted: str, stat: str) -> str:
    """V0-POST-FROM-MAILBOX from the POST's final line and a later STAT.

    Accepted when the node took the article (240) or serves it (223), which
    is the defect of 2026-09-22; refused only when the POST was answered 441
    AND the Message-ID is not served (430); otherwise the POST line's class.
    """
    if posted.startswith("240") or stat.startswith("223"):
        return ACCEPTED
    if posted.startswith("441") and stat.startswith("430"):
        return REFUSED
    return reply_verdict(posted)


def unsupported(status: str) -> bool:
    return (status or "").strip()[:3] in UNSUPPORTED_CODES


def not_permitted(status: str) -> bool:
    return (status or "").strip()[:3] in NOT_PERMITTED_CODES


def available(status: str) -> bool:
    """Is the command available to this caller (RFC 3977 section 5.2.2)?

    A capability is advertised exactly when the command is available, so the
    audit needs a reading of "available" that a refusal ABOUT THE ARGUMENT
    does not fail: `GROUP no.such.group` answering 411 is the command working.
    """
    code = (status or "").strip()[:3]
    if not code.isdigit():
        return False
    return code[0] in "123" or (code not in UNSUPPORTED_CODES
                                and code not in NOT_PERMITTED_CODES)


def traceback_line(output: str) -> str:
    """The exception line of a Python traceback in a step's output, if any.

    A harness that raised did not refuse anything: its row is `not-exercised`
    with the exception as the blocker, never a refusal that reads like the
    feature saying no.
    """
    if "Traceback (most recent call last)" not in (output or ""):
        return ""
    for line in reversed(output.strip().splitlines()):
        line = line.strip()
        if line and not line.startswith(("File ", "~", "^", "self.", "report =",
                                         "sys.exit", "return ")) and ":" in line:
            head = line.split(":", 1)[0]
            if head.endswith(("Error", "Exception", "Exit")):
                return line[:300]
    return "a Python traceback with no recognisable exception line"


EXIT_FAULT, EXIT_USAGE = 4, 5


def exit_verdict(rc) -> str:
    """The outcome class of one exit code (D13, docs/operator.md).

    Only 0, 1 and 3 are outcomes.  A fault (4), a usage error (5) or any
    other code says the command did not decide, so the row is not-exercised
    and `emit` names the code as its blocker; reading a fault as "uncertain"
    would collapse two of the three outcomes the CLI keeps distinct.
    """
    if rc is None:
        return NOT_EXERCISED
    return {EXIT_OK: ACCEPTED, EXIT_REFUSED: REFUSED,
            EXIT_UNCERTAIN: UNCERTAIN}.get(rc, NOT_EXERCISED)


def exit_blocker(rc) -> str:
    """Why a non-outcome exit code leaves its row not-exercised."""
    kind = {EXIT_FAULT: "a host fault", EXIT_USAGE: "a usage error"}.get(
        rc, "a code outside the operator contract")
    return ("the command exited {}, {}, which is not one of the three outcomes "
            "(docs/operator.md: 0 accepted, 1 refused, 3 uncertain)".format(rc, kind))


# --------------------------------------------------------------------------
# the driver that runs on the host beside deploy_gate's and twonode_gate's

MATRIX_DRIVER = r'''#!/usr/bin/env python3
"""The v0 matrix's own NNTP phases.  No fn module is imported; Conn is
tools/deploy_gate.py's driver, shipped beside this file as drive.py.

Every phase prints ONE json object whose keys are command names and whose
values are the status lines the server sent.  This file asserts nothing about
what a code MEANS: the matrix classifies, and ACL2 decides.
"""
import argparse, json, os, socket, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from drive import Conn

# tools/deploy_gate.py's Conn defaults to 30 s.  A READER command comes back
# in milliseconds, but POST, AUTHINFO PASS and a transit transfer each cross
# the ACL2 bridge, and one of those calls can take tens of seconds on a busy
# box -- the eighth run recorded every AUTHINFO and POST row as
# "TimeoutError: timed out" on both nodes for that reason and nothing else.
SOCKET_TIMEOUT = 240


def send_block(conn, lines):
    payload = b""
    for one in lines:
        raw = one.encode() if isinstance(one, str) else one
        payload += (b"." + raw if raw.startswith(b".") else raw) + b"\r\n"
    conn.sock.sendall(payload + b".\r\n")


def article_lines(msgid, group, subject, body, path="",
                  sender="matrix@example.invalid"):
    head = ["Path: {}!not-for-mail".format(path)] if path else []
    return head + ["From: " + sender, "Subject: " + subject,
                   "Newsgroups: " + group, "Message-ID: " + msgid, "", body]


def sibling_msgid(msgid: str, tag: str) -> str:
    """`<local.tag@domain>` for `<local@domain>`: a second identifier per run."""
    local, _, domain = msgid.strip("<>").partition("@")
    return "<{}.{}@{}>".format(local, tag, domain)


def labels(caps):
    return [c.split()[0].upper() for c in caps if c.strip()]


# RFC 3977 section 5.2.2: the capability is advertised exactly when the
# command is available.  Only labels the RFCs define as capabilities are
# audited in the reverse direction: XOVER, XHDR, XPAT and LISTGROUP are not
# capability labels of their own (LISTGROUP is READER's), so dispatching them
# without a label of their own is not a defect.
# AUTHINFO and STARTTLS are deliberately NOT here: both are advertised
# exactly while they are still usable (RFC 4643 section 2.3, RFC 4642
# section 2.2.2), so a connection that has authenticated sees the command
# work and the label gone, which is the rule and not a defect --
# V0-AUTH-ADVERTISED and V0-AUTH-WITHDRAWN are the rows for it.  MODE-READER
# is advertised by a MODE-SWITCHING server (RFC 3977 section 5.3), and a
# server that is always in reader mode answering MODE READER is not one.
RFC_LABELS = ("READER", "POST", "IHAVE", "STREAMING", "OVER", "HDR", "LIST",
              "NEWNEWS")
# The verb is absent, or present and closed to this caller.  Either way the
# command is not available and the capability must not be advertised.
UNAVAILABLE = ("500", "501", "502", "440", "480", "483")


def is_available(reply):
    code = (reply or "")[:3]
    return code.isdigit() and code not in UNAVAILABLE


def login(conn, args, out, prefix=""):
    """AUTHINFO USER/PASS, when the caller was given a credential."""
    if not args.user:
        return False
    out[prefix + "AUTHINFO USER"] = conn.cmd("AUTHINFO USER " + args.user)[0]
    out[prefix + "AUTHINFO PASS"] = conn.cmd("AUTHINFO PASS " + args.secret)[0]
    return out[prefix + "AUTHINFO PASS"].startswith("281")


def surface(args):
    """The whole reader profile, one status line per command."""
    out = {}
    conn = Conn(args.port, timeout=SOCKET_TIMEOUT)
    out["greeting"] = conn.greeting
    status, caps = conn.cmd("CAPABILITIES", multiline=True)
    out["CAPABILITIES"] = status
    out["capability_lines"] = caps
    out["MODE READER"] = conn.cmd("MODE READER")[0]
    for one in ("LIST ACTIVE", "LIST NEWSGROUPS", "LIST OVERVIEW.FMT",
                "LIST ACTIVE.TIMES", "LIST HEADERS"):
        out[one] = conn.cmd(one, multiline=True)[0]
    out["LIST NEWSGROUPS WILDMAT"] = conn.cmd(
        "LIST NEWSGROUPS {}".format(args.group), multiline=True)[0]
    group = conn.cmd("GROUP " + args.group)
    out["GROUP"] = group[0]
    count, first, last = 0, 0, 0
    parts = group[0].split()
    if group[0].startswith("211") and len(parts) >= 4:
        count, first, last = int(parts[1]), int(parts[2]), int(parts[3])
    out["group_count"] = count
    out["group_first"] = first
    out["group_last"] = last
    n = first if first else 1
    out["LISTGROUP"] = conn.cmd("LISTGROUP {} {}-{}".format(args.group, n, last or n),
                                multiline=True)[0]
    for verb in ("ARTICLE", "HEAD", "BODY", "STAT"):
        out[verb] = conn.cmd("{} {}".format(verb, n), multiline=(verb != "STAT"))[0]
    out["ARTICLE MSGID"] = conn.cmd("ARTICLE " + args.msgid, multiline=True)[0]
    out["ARTICLE ABSENT"] = conn.cmd("ARTICLE " + args.absent, multiline=True)[0]
    out["OVER"] = conn.cmd("OVER {}".format(n), multiline=True)[0]
    out["OVER RANGE"] = conn.cmd("OVER {}-{}".format(n, last or n), multiline=True)[0]
    out["HDR"] = conn.cmd("HDR Subject {}".format(n), multiline=True)[0]
    out["XOVER"] = conn.cmd("XOVER {}-{}".format(n, last or n), multiline=True)[0]
    out["XHDR"] = conn.cmd("XHDR Subject {}".format(n), multiline=True)[0]
    out["XPAT"] = conn.cmd("XPAT Subject {}-{} *".format(n, last or n), multiline=True)[0]
    # RFC 3977 section 7.4.  Three rows: the whole-history poll, the poll from
    # an instant in the future (section 7.4.2's empty list is a valid answer),
    # and a malformed wildmat, which section 3.2.1 makes 501.  A node that
    # holds no article with a decodable Injection-Date or Date answers the
    # first with an empty block too, which is why its row records framing.
    out["NEWNEWS"] = conn.cmd("NEWNEWS {} 19700101 000000 GMT".format(args.group),
                              multiline=True)[0]
    out["NEWNEWS FUTURE"] = conn.cmd("NEWNEWS {} 20990101 000000 GMT".format(args.group),
                                     multiline=True)[0]
    out["NEWNEWS SYNTAX"] = conn.cmd("NEWNEWS [ 19700101 000000 GMT")[0]
    # The cursor pair, from a known position: STAT the first article, then NEXT
    # and LAST.  With one article NEXT is 421 by RFC 3977 section 6.1.4; the
    # matrix is told the count so it can say which case this run was.
    conn.cmd("STAT {}".format(n))
    out["NEXT"] = conn.cmd("NEXT")[0]
    out["LAST"] = conn.cmd("LAST")[0]
    out["DATE"] = conn.cmd("DATE")[0]
    out["HELP"] = conn.cmd("HELP", multiline=True)[0]
    out["UNKNOWN"] = conn.cmd("FNBOGUS")[0]
    conn.close()
    # Framing: the same command, split across two segments with a pause, must
    # be answered once and identically (NNT-003).
    split = Conn(args.port, timeout=SOCKET_TIMEOUT)
    split.sock.sendall(b"DAT")
    time.sleep(0.4)
    split.sock.sendall(b"E\r\n")
    out["FRAMING"] = split.line()
    out["FRAMING SAME"] = out["FRAMING"][:3] == out["DATE"][:3]
    drop(split)
    out["ok"] = out["GROUP"].startswith("211")
    return out


# label -> one command that the label promises.  RFC 3977 section 5.2 and its
# extensions; a label with no command of its own is not in the table.
PROBES = (
    ("READER", "GROUP {group}", False),
    ("POST", "POST", True),
    ("IHAVE", "IHAVE <pin.probe@matrix.example.invalid>", True),
    ("STREAMING", "MODE STREAM", False),
    ("OVER", "OVER 1", False),
    ("HDR", "HDR Subject 1", False),
    ("LIST", "LIST ACTIVE", False),
    ("NEWNEWS", "NEWNEWS * 20200101 000000 GMT", False),
    ("AUTHINFO", "AUTHINFO USER pin-probe", False),
    ("STARTTLS", "STARTTLS", "handshake"),
    ("MODE-READER", "MODE READER", False),
    ("XOVER", "XOVER 1", False),
    ("XHDR", "XHDR Subject 1", False),
    ("XPAT", "XPAT Subject 1 *", False),
    ("LISTGROUP", "LISTGROUP {group}", False),
    ("CHECK", "CHECK <pin.check@matrix.example.invalid>", False),
    # RFC 4644 section 2.5 is block-first: unlike POST and IHAVE, TAKETHIS
    # has no preliminary status line.  Waiting for one leaves both probe and
    # server waiting forever, so its probe must write the terminating block
    # before it reads the final decision.
    ("TAKETHIS", "TAKETHIS <pin.take@matrix.example.invalid>", "block-first"),
)


def pins(args):
    """Capability truthfulness, both ways round (NNT-001, RFC 3977 5.2.2).

    One connection per probe, because a 340 or a 335 puts the connection into
    a transfer and a POST is one per connection on this tree.
    """
    conn = Conn(args.port, timeout=SOCKET_TIMEOUT)
    out_login = {}
    login(conn, args, out_login)
    status, caps = conn.cmd("CAPABILITIES", multiline=True)
    advertised = labels(caps)
    conn.close()
    answered = {}
    for label, template, opens in PROBES:
        probe = Conn(args.port, timeout=SOCKET_TIMEOUT)
        try:
            # Everything but AUTHINFO itself is probed on an AUTHENTICATED
            # connection, because that is the connection whose CAPABILITIES
            # block was read above.  AUTHINFO is withdrawn once authenticated
            # (RFC 4643 section 2.3), so probing it after a login would test
            # the withdrawal, not the dispatch.
            if label != "AUTHINFO":
                login(probe, args, {})
            command = template.format(group=args.group)
            if opens == "block-first":
                probe.send(command)
                probe.sock.sendall(b".\r\n")
                reply = probe.line()
            else:
                reply = probe.cmd(command)[0]
            answered[label] = reply
            # A command that opened a transfer is closed with an empty block
            # so the server is left in a clean state and the process is not
            # holding a half-open transfer when the next probe connects.
            if opens == "handshake" and reply[:1] == "3":
                # 382 leaves the session waiting for a TLS handshake.  A
                # plaintext QUIT after it is never read, the probe blocks
                # until its timeout and the SERVER stays wedged on that
                # connection -- which is what made every later phase of the
                # sixth run time out.  Drop the socket instead.
                drop(probe)
                continue
            if opens is True and reply[:1] in "34":
                probe.sock.sendall(b".\r\n")
                try:
                    answered[label + " CLOSE"] = probe.line()
                except Exception:
                    pass
        except Exception as error:
            answered[label] = "{}: {}".format(type(error).__name__, error)
        drop(probe)
    dispatched = [l for l, _, _ in PROBES if is_available(answered.get(l, ""))]
    out = {"advertised": advertised, "answered": answered,
           "dispatched": dispatched, "login": out_login,
           # A label with no probe command cannot be checked either way, and
           # only the RFCs' own capability labels are audited in reverse.
           "advertised_not_dispatched": sorted(
               set(advertised) & {l for l, _, _ in PROBES} - set(dispatched)),
           "dispatched_not_advertised": sorted(
               (set(dispatched) & set(RFC_LABELS)) - set(advertised)),
           "capability_lines": caps}
    out["ok"] = not out["advertised_not_dispatched"] and not out["dispatched_not_advertised"]
    return out


def postcycle(args):
    """One POST on its own connection, with the read-back in three places."""
    out = {}
    poster = Conn(args.port, timeout=SOCKET_TIMEOUT)
    login(poster, args, out)
    out["GROUP BEFORE"] = poster.cmd("GROUP " + args.group)[0]
    out["POST"] = poster.cmd("POST")[0]
    if out["POST"].startswith("340"):
        send_block(poster, article_lines(args.msgid, args.group, "matrix post",
                                         "Posted by tools/v0_matrix.py."))
        out["COMMIT"] = poster.line()
        out["GROUP AFTER"] = poster.cmd("GROUP " + args.group)[0]
    else:
        out["COMMIT"] = "(nothing sent: POST answered " + out["POST"] + ")"
        out["GROUP AFTER"] = "(not attempted)"
    drop(poster)

    fresh = Conn(args.port, timeout=SOCKET_TIMEOUT)
    login(fresh, args, {})
    out["FRESH ARTICLE"] = fresh.cmd("ARTICLE " + args.msgid, multiline=True)[0]
    drop(fresh)

    # The duplicate, on its own connection: one clock observation is pinned per
    # connection at accept, so a second POST on the poster's connection would
    # be refused for a reason that is not duplicate suppression.
    again = Conn(args.port, timeout=SOCKET_TIMEOUT)
    login(again, args, {})
    out["DUPLICATE POST"] = again.cmd("POST")[0]
    if out["DUPLICATE POST"].startswith("340"):
        send_block(again, article_lines(args.msgid, args.group, "matrix post",
                                        "Posted by tools/v0_matrix.py."))
        out["DUPLICATE"] = again.line()
    else:
        out["DUPLICATE"] = out["DUPLICATE POST"]
    drop(again)

    # A refused clock reading costs the owner its clock (decision D10-a): it
    # injects nothing, declares no group and answers DATE 503 until the next
    # reading.  So asking DATE after the duplicate separates the two things
    # that both arrive as 441 -- an article the node already holds, and a
    # clock the node no longer has.
    clock = Conn(args.port, timeout=SOCKET_TIMEOUT)
    login(clock, args, {})
    out["DATE AFTER DUPLICATE"] = clock.cmd("DATE")[0]
    drop(clock)

    # RFC 5536 3.1.2: a From with no address, on its own connection and under
    # its own Message-ID, then asked for by that Message-ID.
    unaddressed = sibling_msgid(args.msgid, "from")
    bad = Conn(args.port, timeout=SOCKET_TIMEOUT)
    login(bad, args, {})
    out["FROM POST"] = bad.cmd("POST")[0]
    if out["FROM POST"].startswith("340"):
        send_block(bad, article_lines(unaddressed, args.group, "matrix from",
                                      "Posted by tools/v0_matrix.py.", sender="yue"))
        out["FROM"] = bad.line()
    else:
        out["FROM"] = out["FROM POST"]
    drop(bad)
    probe = Conn(args.port, timeout=SOCKET_TIMEOUT)
    login(probe, args, {})
    out["FROM ARTICLE"] = probe.cmd("STAT " + unaddressed)[0]
    drop(probe)

    before = out["GROUP BEFORE"].split()
    after = out["GROUP AFTER"].split()
    out["counted"] = (len(before) >= 2 and len(after) >= 2
                      and after[1].isdigit() and before[1].isdigit()
                      and int(after[1]) == int(before[1]) + 1)
    out["ok"] = out.get("COMMIT", "").startswith("240")
    return out


def concurrent(args):
    """A second reader stays live across another connection's whole POST."""
    out = {}
    watcher = Conn(args.port, timeout=SOCKET_TIMEOUT)
    login(watcher, args, {})
    out["WATCHER BEFORE"] = watcher.cmd("GROUP " + args.group)[0]
    poster = Conn(args.port, timeout=SOCKET_TIMEOUT)
    login(poster, args, out)
    out["POST"] = poster.cmd("POST")[0]
    if not out["POST"].startswith("340"):
        out["WATCHER MID"] = "(not attempted)"
        out["COMMIT"] = "(nothing sent)"
        out["ok"] = False
        drop(poster); drop(watcher)
        return out
    poster.sock.sendall(("From: matrix@example.invalid\r\nSubject: concurrent\r\n"
                         "Newsgroups: {}\r\nMessage-ID: {}\r\n\r\nhalf a ".format(
                             args.group, args.msgid)).encode())
    out["WATCHER MID"] = watcher.cmd("GROUP " + args.group)[0]
    out["WATCHER ARTICLE MID"] = watcher.cmd("STAT", multiline=False)[0]
    poster.sock.sendall(b"letter.\r\n.\r\n")
    out["COMMIT"] = poster.line()
    out["WATCHER AFTER"] = watcher.cmd("GROUP " + args.group)[0]
    drop(poster); drop(watcher)
    out["ok"] = out["WATCHER MID"].startswith("211") and out["COMMIT"].startswith("240")
    return out


def drop(conn):
    """Close the socket without a QUIT.

    A QUIT after a 3xx is read as transfer data or as plaintext in a TLS
    handshake, and the server then waits: the eighth and ninth runs lost
    every AUTHINFO and POST row on both nodes to a connection left in that
    state by the probe before them. Nothing this driver opens for a single
    observation is closed politely.
    """
    try:
        conn.sock.close()
    except Exception:
        pass


def auth(args):
    """AUTHINFO (RFC 4643) and the posting permission it carries.

    One observation per connection. `POST` before a login may answer 340 --
    posting can be permitted without one -- and a connection left inside an
    open transfer is what wedges this server, so that probe gets a
    connection of its own and the socket is dropped, never QUIT.
    """
    out = {}
    conn = Conn(args.port, timeout=SOCKET_TIMEOUT)
    status, caps = conn.cmd("CAPABILITIES", multiline=True)
    out["CAPABILITIES BEFORE"] = status
    out["advertised_before"] = labels(caps)
    out["AUTHINFO ADVERTISED"] = any(
        c.upper().startswith("AUTHINFO") for c in caps if c.strip())
    drop(conn)

    gate = Conn(args.port, timeout=SOCKET_TIMEOUT)
    out["POST BEFORE"] = gate.cmd("POST")[0]
    # A 3xx means posting is permitted WITHOUT a login and this connection is
    # now inside a transfer.  Terminate it with an empty block, exactly as
    # `pins` does for its POST probe, rather than dropping the socket
    # mid-article: an empty article is refused and stores nothing, while a
    # server left holding a half-open transfer is what wedged this tree twice.
    if out["POST BEFORE"][:1] == "3":
        gate.sock.sendall(b".\r\n")
        try:
            out["POST BEFORE CLOSE"] = gate.line()
        except Exception as error:
            out["POST BEFORE CLOSE"] = "{}: {}".format(type(error).__name__, error)
    drop(gate)

    conn = Conn(args.port, timeout=SOCKET_TIMEOUT)
    out["AUTHINFO USER"] = conn.cmd("AUTHINFO USER " + args.user)[0]
    out["AUTHINFO PASS"] = conn.cmd("AUTHINFO PASS " + args.secret)[0]
    status, caps = conn.cmd("CAPABILITIES", multiline=True)
    out["CAPABILITIES AFTER"] = status
    out["advertised_after"] = labels(caps)
    out["AUTHINFO WITHDRAWN"] = not any(
        c.upper().startswith("AUTHINFO") for c in caps if c.strip())
    drop(conn)

    poster = Conn(args.port, timeout=SOCKET_TIMEOUT)
    poster.cmd("AUTHINFO USER " + args.user)
    poster.cmd("AUTHINFO PASS " + args.secret)
    out["POST AFTER"] = poster.cmd("POST")[0]
    if out["POST AFTER"].startswith("340"):
        send_block(poster, article_lines(args.msgid, args.group, "authenticated post",
                                         "Posted after an AUTHINFO login."))
        out["POST AFTER COMMIT"] = poster.line()
    else:
        out["POST AFTER COMMIT"] = out["POST AFTER"]
    drop(poster)

    wrong = Conn(args.port, timeout=SOCKET_TIMEOUT)
    wrong.cmd("AUTHINFO USER " + args.user)
    out["AUTHINFO WRONG"] = wrong.cmd("AUTHINFO PASS not-" + args.secret)[0]
    drop(wrong)
    out["ok"] = out["AUTHINFO PASS"].startswith("281")
    return out


def stream(args):
    """The accepted CHECK/TAKETHIS path: 238 then 239 (RFC 4644 2.4, 2.5)."""
    out = {}
    source = Conn(args.from_port, timeout=SOCKET_TIMEOUT)
    status, lines = source.cmd("ARTICLE " + args.msgid, multiline=True)
    out["SOURCE"] = status
    source.close()
    if not status.startswith("220"):
        out["ok"] = False
        out["reason"] = "the source node does not serve " + args.msgid
        return out
    conn = Conn(args.to_port, timeout=SOCKET_TIMEOUT)
    out["MODE STREAM"] = conn.cmd("MODE STREAM")[0]
    out["CHECK"] = conn.cmd("CHECK " + args.msgid)[0]
    conn.sock.sendall(("TAKETHIS " + args.msgid + "\r\n").encode())
    send_block(conn, lines)
    out["TAKETHIS"] = conn.line()
    out["CHECK AGAIN"] = conn.cmd("CHECK " + args.msgid)[0]
    conn.sock.sendall(("TAKETHIS " + args.msgid + "\r\n").encode())
    send_block(conn, lines)
    out["TAKETHIS AGAIN"] = conn.line()
    conn.close()
    reread = Conn(args.to_port, timeout=SOCKET_TIMEOUT)
    status, got = reread.cmd("ARTICLE " + args.msgid, multiline=True)
    reread.close()
    out["REREAD"] = status
    out["IDENTICAL"] = got == lines
    out["ok"] = out["TAKETHIS"].startswith("239") and out["IDENTICAL"]
    return out


def control(args):
    """One line on the owner's Unix control socket, and its reply."""
    out = {"line": args.line}
    sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    sock.settimeout(60)
    try:
        sock.connect(args.socket)
        sock.sendall(args.line.encode() + b"\n")
        data = b""
        while not data.endswith(b"\n"):
            chunk = sock.recv(4096)
            if not chunk:
                break
            data += chunk
        out["reply"] = data.decode("utf-8", "replace").strip()
    except Exception as error:
        out["reply"] = "{}: {}".format(type(error).__name__, error)
    finally:
        try:
            sock.close()
        except Exception:
            pass
    out["ok"] = not out["reply"].startswith(("refused", "uncertain", "fault",
                                             "unknown", "OSError", "socket",
                                             "ConnectionRefusedError",
                                             "FileNotFoundError", "TimeoutError"))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="phase", required=True)
    for name in ("surface", "pins", "postcycle", "concurrent", "auth", "stream",
                 "control"):
        one = sub.add_parser(name)
        one.add_argument("--port", type=int, default=0)
        one.add_argument("--from-port", type=int, default=0)
        one.add_argument("--to-port", type=int, default=0)
        one.add_argument("--group", default="fn.letters")
        one.add_argument("--msgid", default="")
        one.add_argument("--absent", default="<absent@example.invalid>")
        one.add_argument("--user", default="")
        one.add_argument("--secret", default="matrix-secret")
        one.add_argument("--secret-file", default="")
        one.add_argument("--socket", default="")
        one.add_argument("--line", default="VERSION")
    args = parser.parse_args()
    # A secret may reach this driver as a PATH and never as a command word:
    # the gate renders every command it ran in `report.md`, so a secret that
    # entered an argument would enter the evidence with it.
    if args.secret_file:
        with open(args.secret_file) as handle:
            args.secret = handle.read().strip()
    handler = {"surface": surface, "pins": pins, "postcycle": postcycle,
               "concurrent": concurrent, "auth": auth, "stream": stream,
               "control": control}[args.phase]
    try:
        result = handler(args)
    except Exception as error:
        print(json.dumps({"ok": False, "error": "{}: {}".format(
            type(error).__name__, error)}))
        return 1
    print(json.dumps(result))
    return 0 if result.get("ok") else 1


if __name__ == "__main__":
    sys.exit(main())
'''


# The independent client.  Everything else in this file speaks to fn through
# sockets fn's own harnesses opened; this one hands the connection to the
# Python standard library's own NNTP implementation and lets it frame, parse
# and decode.  PEP 594 removed `nntplib` in 3.13, so it runs under whichever
# older interpreter the box has -- on persvati that is a uv-managed CPython
# 3.12 (`uv python install 3.12`), which is not fn's code by any reading.
INDEPENDENT_DRIVER = r'''#!/usr/bin/env python3
"""A stdlib-nntplib reader against a live fn node.  No fn module is imported,
and no framing, folding or response parsing in this file is fn's: nntplib
does all of it.  The fixture is passed in, so the probe makes no assumption
about what the node holds."""
import argparse, json, nntplib, platform, sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, required=True)
    parser.add_argument("--group", required=True)
    parser.add_argument("--msgid", required=True)
    parser.add_argument("--absent", default="<absent@example.invalid>")
    parser.add_argument("--user", default="")
    parser.add_argument("--secret", default="")
    args = parser.parse_args()
    out = {"client": "stdlib nntplib", "python": platform.python_version(),
           "commands": []}
    try:
        with nntplib.NNTP("127.0.0.1", port=args.port, timeout=30) as client:
            out["welcome"] = client.getwelcome()
            caps = client.getcapabilities()
            out["capabilities"] = sorted(caps)
            out["commands"].append("CAPABILITIES")
            # RFC 4643, and the whole of it is nntplib's: it sends AUTHINFO
            # USER and AUTHINFO PASS and reads the codes.  Nothing in this
            # file frames or parses them.  The login is the observation the
            # matrix could not make with a non-fn client before.
            if args.user:
                out["authinfo_advertised"] = "AUTHINFO" in caps
                client.login(args.user, args.secret, usenetrc=False)
                out["login"] = "accepted"
                out["commands"].append("AUTHINFO USER/PASS")
                out["capabilities_after_login"] = sorted(
                    client.getcapabilities())
            _, count, first, last, name = client.group(args.group)
            out["group"] = {"count": count, "first": first, "last": last,
                            "name": name}
            out["commands"].append("GROUP")
            _, number, found = client.stat(str(first))
            out["stat"] = [number, found]
            out["commands"].append("STAT")
            _, info = client.article(args.msgid)
            out["article_lines"] = len(info.lines)
            out["article_has_msgid"] = any(
                args.msgid.encode() in line for line in info.lines)
            out["commands"].append("ARTICLE")
            _, head = client.head(args.msgid)
            out["head_lines"] = len(head.lines)
            out["commands"].append("HEAD")
            _, body = client.body(args.msgid)
            out["body_lines"] = len(body.lines)
            out["commands"].append("BODY")
            try:
                _, over = client.over((first, last))
                out["over_rows"] = len(over)
                out["commands"].append("OVER")
            except nntplib.NNTPError as error:
                out["over_rows"] = "NNTPError: {}".format(error)
            _, groups = client.list()
            out["list_groups"] = sorted(g.group for g in groups)
            out["commands"].append("LIST")
            try:
                client.article(args.absent)
                out["absent"] = "the node served an article it should not hold"
            except nntplib.NNTPTemporaryError as error:
                out["absent"] = str(error)
            out["commands"].append("ARTICLE (absent)")
            out["quit"] = client.quit()
            out["commands"].append("QUIT")
        out["ok"] = (out["group"]["count"] >= 1 and out["article_has_msgid"]
                     and out["body_lines"] >= 1
                     and str(out["absent"]).startswith("43")
                     and (not args.user or out.get("login") == "accepted"))
    except Exception as error:
        out["ok"] = False
        out["error"] = "{}: {}".format(type(error).__name__, error)
    print(json.dumps(out, sort_keys=True))
    return 0 if out.get("ok") else 1


if __name__ == "__main__":
    sys.exit(main())
'''


# --------------------------------------------------------------------------
# the gate

ART = {"a": "<alpha@a.example.invalid>", "b": "<beta@b.example.invalid>"}
STREAM = {"a": "<stream-a@example.invalid>", "b": "<stream-b@example.invalid>"}
STX = {"a": "<statement-a@example.invalid>", "b": "<statement-b@example.invalid>"}
SOCKET_POST = {"a": "<socket-a@example.invalid>", "b": "<socket-b@example.invalid>"}
AUTH_POST = {"a": "<auth-a@example.invalid>", "b": "<auth-b@example.invalid>"}
CONCURRENT_ID = "<concurrent@example.invalid>"
# `bin/fn run` defaults to 8. The capability audit alone opens one connection
# per label because a 340 or a 335 puts a connection into a transfer, so the
# ceiling is raised here and the number is recorded with the rows.
MAX_CONNECTIONS = 64
LOOP_ID = {"ab": "<loop-ab@example.invalid>", "ba": "<loop-ba@example.invalid>"}
INTERRUPTED_ID = "<interrupted@example.invalid>"
ABSENT_ID = "<absent@example.invalid>"
MATRIX_GROUP = "fn.matrix"
THROWAWAY_GROUP = "fn.matrix.throwaway"
AUTH_USER = "matrix"
AUTH_SECRET = "matrix-secret-8f21"
# 32 octets of hex: the seed `fn principal new` and `fn statement sign` take.
SEED = "5f" * 32


class V0Matrix(twonode_gate.TwoNodeGate):
    """Two peered fn nodes, every feature driven between them, one row each."""

    TITLE = "v0 matrix"
    TOOL = "tools/v0_matrix.py"
    # The rows below ARE this gate's machine-readable result, with their own
    # digest in planning/v0-matrix.json; the gate-family findings sidecar
    # would be a second, thinner file saying less.
    FINDINGS_SIDECAR = False
    PREAMBLE = (
        "v0 is every feature of fn usable between two peered fn nodes. This is that",
        "question asked feature by feature against one commit on one box, with five",
        "verdicts and no pass/fail collapse: accepted, refused and uncertain are the",
        "three outcomes and each is a real observation; not-exercised names what",
        "blocked the row; not-built names the lane that owns the missing feature.",
        "It establishes nothing about the books beyond which certificates ACL2 read.")
    FACT_KEYS = ("os", "kernel", "python3", "acl2version", "certificates",
                 "uncertified books", "feature probe", "assigned ports",
                 "node a", "node b", "server entry point", "peer records",
                 "three outcomes a", "three outcomes b", "transit", "feed",
                 "kill", "tcpcl", "rows")
    STANDING_GAPS = twonode_gate.TwoNodeGate.STANDING_GAPS + (
        "A verdict here is an observation of a reply, an exit code or a file. It is\n"
        "  not a proof, and an `accepted` row says the feature ran once on one box,\n"
        "  not that it is correct for every input.",
        "The matrix computes no identity, no group table, no charge, no frame and no\n"
        "  bound: where it needed one it asked the node for it.",
        "A `not-built` row is this matrix's reading of a probe, not a promise from\n"
        "  the lane it names.")

    def __init__(self, *args, scale=False, inn=False, campaign=True,
                 backend=DEVELOPMENT_BACKEND, native_image=None,
                 native_configs=None, native_group=GROUPS[0],
                 native_image_source=None, native_runtime=None,
                 native_developer_image=None, **kwargs):
        super().__init__(*args, **kwargs)
        if backend not in BACKENDS:
            raise GateError("unknown execution backend {!r}".format(backend))
        self.backend = backend
        self.native_image = native_image
        # The developer image, when the operator supplied one.  It is the
        # subject of exactly one row: the uncertain outcome is a cut the
        # production image refuses rather than honours, so measuring it needs
        # an owner built with the developer profile.  Nothing else in this
        # slice runs on it.
        self.native_developer_image = native_developer_image
        self.native_configs = dict(native_configs or {})
        self.native_group = native_group
        self.native_image_source = native_image_source
        self.native_runtime = native_runtime
        self.image_identity = ("development Python entry points from {}".format(self.rev)
                               if backend == DEVELOPMENT_BACKEND else
                               "{} (digest not probed)".format(native_image or "(missing)"))
        # What the init/uncertain phase observed per node, for the D13 fact
        # the outcomes phase records.
        self.native_uncertain: dict = {}
        self.native_post_ids = {
            name: "<native-matrix-{}-{}@example.invalid>".format(
                uuid.uuid4().hex[:12], name) for name in ("a", "b")
        }
        # The native AUTHINFO credential: the login is fixed so `principal
        # list` can be read for it, and the secret is generated ON the
        # execution host (see `native_secret_files`) so that this process
        # never holds it and no recorded command can carry it.
        self._native_secret_ready = False
        self.native_credential: dict = {}
        self.want_scale = scale
        self.want_inn = inn
        self.want_campaign = campaign
        self.rows: list[Row] = []
        self.emitted: set[str] = set()
        self.support: dict = {}
        self.dead: dict = {}
        self.group_counts = {"a": 0, "b": 0}

    # -- rows -------------------------------------------------------------
    def emit(self, key, verdict, invocation, observed, *, node=None,
             direction=None, exit_code=None, log=None, limit="", blocker=None,
             owner=None, client=None) -> Row:
        """Record one planned row's verdict.  The only way a row is created."""
        spec = PLAN_BY_KEY[key]
        suffix = ""
        if spec.scope == "node":
            suffix = "-" + node.upper()
        elif spec.scope == "direction":
            suffix = "-" + direction.upper()
        rid = spec.key + suffix
        if rid not in PLANNED_IDS:
            raise GateError("row {} is not in PLAN".format(rid))
        if rid in self.emitted:
            raise GateError("row {} emitted twice".format(rid))
        if verdict not in VERDICTS:
            raise GateError("row {}: verdict {!r} is not one of {}".format(
                rid, verdict, VERDICTS))
        if verdict == NOT_EXERCISED and not blocker and exit_code is not None:
            blocker = exit_blocker(exit_code)
        if verdict in (NOT_EXERCISED, NOT_BUILT) and not blocker:
            raise GateError("row {}: a {} row must name its blocker".format(rid, verdict))
        if verdict in OUTCOMES and client is None:
            client = CLIENT_DRIVER
        row = Row(rid, spec, verdict, invocation, observed, exit_code,
                  log or self.evidence_name, limit, blocker, owner,
                  node=node, direction=direction, client=client)
        self.rows.append(row)
        self.emitted.add(rid)
        return row

    def emit_once(self, key, verdict, invocation, observed, **kwargs):
        """`emit`, unless a phase already measured this row.

        The native peering witness runs on nodes of its own after the matrix
        has driven transit on A and B; the matrix's own measurement is the
        row, and the witness fills only what nothing else reached.
        """
        spec = PLAN_BY_KEY[key]
        suffix = ""
        if spec.scope == "node":
            suffix = "-" + kwargs["node"].upper()
        elif spec.scope == "direction":
            suffix = "-" + kwargs["direction"].upper()
        if spec.key + suffix in self.emitted:
            return None
        return self.emit(key, verdict, invocation, observed, **kwargs)

    def from_step(self, key, step: Step, **kwargs) -> Row:
        """A row whose observation is a host command's exit code (D13)."""
        verdict = exit_verdict(step.rc)
        kwargs.setdefault("blocker", None)
        if verdict == NOT_EXERCISED and not kwargs["blocker"]:
            kwargs["blocker"] = (exit_blocker(step.rc) if step.rc is not None
                                 else step.note or "the command did not run")
        observed = "rc={} {}".format(step.rc, step.first_line or "(no output)")
        kwargs.setdefault("client", CLIENT_CLI)
        return self.emit(key, verdict, step.command, observed,
                         exit_code=step.rc, **kwargs)

    def from_reply(self, key, status, invocation, **kwargs) -> Row:
        """A row whose observation is one NNTP status line."""
        return self.emit(key, reply_verdict(status), invocation,
                         status or "(no reply)", **kwargs)

    def blocked(self, keys, blocker, *, verdict=NOT_EXERCISED, owner=None,
                invocation="", nodes=("a", "b"), directions=("ab", "ba")):
        """Mark every id of every named spec as not-exercised or not-built."""
        for key in keys:
            spec = PLAN_BY_KEY[key]
            if spec.scope == "node":
                for name in nodes:
                    if spec.key + "-" + name.upper() not in self.emitted:
                        self.emit(key, verdict, invocation, "(not run)", node=name,
                                  blocker=blocker, owner=owner)
            elif spec.scope == "direction":
                for way in directions:
                    if spec.key + "-" + way.upper() not in self.emitted:
                        self.emit(key, verdict, invocation, "(not run)",
                                  direction=way, blocker=blocker, owner=owner)
            elif spec.key not in self.emitted:
                self.emit(key, verdict, invocation, "(not run)",
                          blocker=blocker, owner=owner)

    def backfill(self):
        """Every planned row the run never reached is a row, not a silence."""
        for spec in PLAN:
            for rid in spec.ids():
                if rid in self.emitted:
                    continue
                node = rid.rsplit("-", 1)[-1].lower() if spec.scope == "node" else None
                direction = rid.rsplit("-", 1)[-1].lower() if spec.scope == "direction" else None
                self.emit(spec.key, NOT_EXERCISED, "(none)", "(not run)",
                          node=node, direction=direction,
                          blocker="the run reached its end without this row; the phase "
                                  "that owns it raised or was skipped, and the gap list "
                                  "above says which")

    # -- plumbing ---------------------------------------------------------
    @property
    def evidence_name(self):
        return getattr(self, "_evidence_name", "planning/evidence/(pending)")

    def execution_identity(self):
        """The runtime subject attached to the document and every row.

        `source` is the deployed Git revision.  `image` is separate because
        an externally supplied native image is not proved to have been built
        from that source merely because the harness was invoked at it.
        """
        return {"backend": self.backend, "source": self.rev,
                "image": self.image_identity}

    def native_operator(self, node, *words) -> str:
        """The packaged public native command, with no diagnostic entry."""
        if self.backend != NATIVE_BACKEND:
            raise GateError("native operator command requested on {}".format(
                self.backend))
        config = self.native_configs.get(node.name)
        if not self.native_image or not config:
            raise GateError("native image and both node configs are required")
        return self.native_command(config, *words)

    class Raw(str):
        """A command word that is a shell expression by construction.

        The gate names every remote path under `$HOME/fn-deploy/...` and lets
        the remote shell expand it; quoting such a word hands the image a
        literal dollar sign, which is what the 01:37Z run's four fault rows
        were.
        """

    def native_command(self, config, *words, image=None, env=None) -> str:
        """The packaged public native command against one named configuration.

        `env` in front: the gate starts a node as `nohup <command> &`, and
        nohup execs its first word, so a bare `VAR=x cmd` is "no such
        command" and the server is reported dead in 0.3 s.  This is the
        line that kept every native POST/reader row at not-exercised.
        """
        def word(one):
            return one if isinstance(one, self.Raw) else shlex.quote(one)
        return "env {}FN_NATIVE_HOST={} packaging/fn-native operator {} {}".format(
            "".join("{}={} ".format(name, shlex.quote(value))
                    for name, value in sorted((env or {}).items())),
            shlex.quote(image or self.native_image), word(config),
            " ".join(word(one) for one in words))

    def cli(self, node, args) -> str:
        """The operator surface against this node's configuration.

        `bin/fn` on the development backend; the packaged native operator on
        the native one, whose `group` and `capacity` words are the same.
        """
        if self.backend == NATIVE_BACKEND:
            return self.native_operator(node, *shlex.split(args))
        return "python3 bin/fn --config {}/fn.toml {}".format(node.dir, args)

    def matrix(self, phase, extra, name=None, timeout=300, expect=None) -> Step:
        return self.sh(name or "matrix {}".format(phase), self.cd(
            "python3 {}/matrix.py {} {}".format(self.run, phase, extra)),
            timeout=timeout, expect=expect)

    def phase(self, label, function, *args):
        """Run one phase; a phase that raises is a gap, not the end of the run."""
        try:
            function(*args)
        except GateError:
            raise
        except Exception as error:                       # noqa: BLE001
            self.limitation(None, "the {} phase raised {}: {}; every row it owns is "
                             "recorded not-exercised below".format(
                                 label, type(error).__name__, error))

    # -- certificates -------------------------------------------------------
    def certificates(self):
        """Use the deploy gate's one load-checked artifact set unchanged.

        A second per-book cache install here used to overwrite that set with
        certificates from other absolute origins, recreating the exact
        sub-book-name conflict the set acquisition excludes.
        """
        return super().certificates()

    # -- probes -----------------------------------------------------------
    def probe_tree(self):
        """What this commit has.  Every `not-built` row below cites this step."""
        step = self.sh("feature probe", self.cd(r"""
for s in init run post group capacity status recover anchor principal peer statement; do
  if python3 bin/fn $s --help >/dev/null 2>&1; then echo "fn-$s=yes"; else echo "fn-$s=no"; fi
done
python3 tools/run_reader.py --help 2>&1 | grep -q -- '--post' \
  && echo reader-post=yes || echo reader-post=no
[ -f tools/run_feed.py ] && echo feed-tool=yes || echo feed-tool=no
[ -f tools/run_bp_ingress.py ] && echo bp-ingress=yes || echo bp-ingress=no
[ -f tools/media.py ] && echo media=yes || echo media=no
[ -f tools/stx.py ] && echo stx=yes || echo stx=no
for b in owner served peer-inbound nntp-auth peer-config peer-feed node nntp \
         tcpcl-session checkpoint peer-feed-invariants owner-feed nntp-auth-invariants \
         auth-secret; do
  [ -f books/$b.cert ] && echo "cert-$b=yes" || echo "cert-$b=no"
done
grep -q 'include-book "nntp-auth"' books/served.lisp \
  && echo auth-wired=yes || echo auth-wired=no
grep -q 'fn-owner-feed-configure' host/owner-host.lisp 2>/dev/null \
  && echo owner-feed=yes || echo owner-feed=no
[ -f books/bp-node.lisp ] && [ -f tests/bp-dtn7/run_fn_bp_interop.py ] \
  && echo bp-node=yes || echo bp-node=no
for p in python3.9 python3.10 python3.11 python3.12; do
  command -v $p >/dev/null && $p -c 'import nntplib' 2>/dev/null \
    && echo "nntplib=$p"; done
UVPY=$(PATH=$PATH:/snap/bin uv python find 3.12 2>/dev/null || true)
[ -n "$UVPY" ] && [ -x "$UVPY" ] && "$UVPY" -c 'import nntplib' 2>/dev/null \
  && echo "nntplib=$UVPY"
command -v slrn >/dev/null && echo slrn=yes || echo slrn=no
command -v swarm-build >/dev/null && echo swarm-build=yes || echo swarm-build=no
"""), timeout=300)
        for line in step.output.splitlines():
            if "=" in line:
                key, _, value = line.strip().partition("=")
                self.support[key] = value
        self.facts["feature probe"] = " ".join(
            "{}={}".format(k, v) for k, v in sorted(self.support.items())
            if v == "no" or k == "nntplib")
        return step

    def has(self, key, default="no") -> bool:
        return self.support.get(key, default) == "yes"

    def uncertified(self, *books) -> list:
        return [b for b in books if self.support.get("cert-" + b) == "no"]

    # -- the shared driver, with one adaptation -----------------------------
    @staticmethod
    def feed_driver() -> str:
        """`tools/twonode_gate.py`'s driver, with a Date on the loop article.

        The loop article the `relay` phase builds by hand carries no `Date`,
        and an fn node refuses a transfer without one (`437 transfer
        rejected; no Injection-Date or Date`, RFC 5536 section 3.1.1). The
        loop row would then read `refused` for the wrong reason -- the
        missing header rather than RFC 5537 section 3.5's Path check -- and
        a row that is right by accident is worse than one that fails.
        """
        source = twonode_gate.FEED_DRIVER
        old = ('    loop = ["Path: {}!not-for-mail".format(args.loop_identity),\n'
               '            "From: gate@example.invalid", "Subject: loop", '
               '"Newsgroups: " + args.group,\n')
        new = ('    import email.utils\n'
               '    loop = ["Path: {}!not-for-mail".format(args.loop_identity),\n'
               '            "From: gate@example.invalid", "Subject: loop", '
               '"Newsgroups: " + args.group,\n'
               '            "Date: " + email.utils.formatdate(usegmt=True),\n')
        if old not in source:
            raise GateError("tools/twonode_gate.py's loop article moved; the v0 "
                            "matrix's Date adaptation no longer applies")
        return source.replace(old, new)

    # -- ports --------------------------------------------------------------
    def allocate_ports(self):
        """One listener port per node, chosen before anything is configured.

        A peer record names the other node's transport, and the record has to
        exist before the servers start -- `peer add` takes the writer lock,
        which the service holds.  With `--port 0` the record would name port
        0, which `fn-store-cfg-peer-record` reads as a BP endpoint rather
        than an NNTP one, so the pair would be peered over a transport
        neither of them speaks.  The ports are therefore chosen here, by the
        kernel, and written into both the configuration and the record.
        """
        one_liner = ("import socket; s=[socket.socket() for _ in range(2)]; "
                     "[x.bind((\"127.0.0.1\", 0)) for x in s]; "
                     "print(\" \".join(str(x.getsockname()[1]) for x in s)); "
                     "[x.close() for x in s]")
        step = self.sh("free ports", "python3 -c '{}'".format(one_liner), expect=None)
        words = [w for w in step.output.split() if w.isdigit()]
        for index, node in enumerate(self.nodes):
            node.assigned_port = int(words[index]) if len(words) > index else 0
        self.facts["assigned ports"] = "a={} b={}".format(
            self.a.assigned_port, self.b.assigned_port)
        if not (self.a.assigned_port and self.b.assigned_port):
            self.limitation(
                None,
                "the host did not give two free ports ({}), so the nodes fall back to "
                "`--port 0` and their peer records name port 0, which the record "
                "builder reads as a BP endpoint.".format(step.first_line))

    # -- F-NODE: init, configuration, start, stop -------------------------
    def init_node(self, node: NodeSpec):
        """`fn init` is the operator path; the store CLI is the fallback."""
        groups = " ".join("--group {}".format(g) for g in GROUPS)
        self.sh("node {} directories".format(node.upper),
                "mkdir -p {} {}".format(node.dir, node.peers))
        step = self.sh("node {} fn init".format(node.upper), self.cd(
            "python3 bin/fn --config {dir}/fn.toml init --store {store} {groups} "
            "--listen 127.0.0.1:{port} --control {dir}/control.sock "
            "--log {dir}/fn.log --acl2 \"$FN_ACL2\"".format(
                dir=node.dir, store=node.store, groups=groups,
                port=getattr(node, "assigned_port", 0))),
            timeout=1800, expect=None)
        self.from_step("V0-NODE-INIT", step, node=node.name,
                       limit="one store on one box; the configuration is this gate's, "
                             "not an operator's")
        if step.rc != 0:
            self.limitation(
                None,
                "node {}: `fn init` exited {} ({}), so the operator path did not create "
                "this node's store; the gate fell back to tools/run_store.py init and "
                "every configuration row below is about that store, not about a store "
                "fn created.".format(node.upper, step.rc, step.first_line))
            fallback = self.sh("node {} store init (fallback)".format(node.upper),
                               self.cd(self.fn("--store {} init {}".format(
                                   node.store, groups))), timeout=1800)
            if fallback.rc != 0:
                raise GateError("node {} store init failed: {}".format(
                    node.upper, fallback.output[:400]))
        config = self.sh("node {} fn.toml".format(node.upper),
                         "cat {}/fn.toml 2>/dev/null || echo NO-CONFIG".format(node.dir),
                         expect=None)
        text = config.output
        ok = "[store]" in text and "[acl2]" in text and "path =" in text
        self.emit("V0-NODE-CONFIG", ACCEPTED if ok else REFUSED,
                  "cat {}/fn.toml".format(node.dir),
                  "[store]={} [acl2]={} [listener]={}".format(
                      "[store]" in text, "[acl2]" in text, "[listener]" in text),
                  node=node.name, exit_code=config.rc,
                  limit="the file's sections are read as text; nothing here loads it "
                        "the way a tool would")
        status = self.sh("node {} fn status".format(node.upper),
                         self.cd(self.cli(node, "status")), timeout=900, expect=None)
        self.from_step("V0-NODE-STATUS", status, node=node.name,
                       limit="the store is not held by a service at this point")
        self.sh("node {} store config".format(node.upper),
                self.cd(self.fn("--store {} config".format(node.store))), timeout=900)

    def reinit(self, node: NodeSpec):
        """A second `fn init` over a store that already holds articles.

        Run here, after the seeds, and not beside the first init: the
        question a v0 operator has is not what a second init returns but
        whether it destroys what the store held, and that cannot be asked of
        an empty store."""
        groups = " ".join("--group {}".format(g) for g in GROUPS)
        held = list(node.accepted)
        again = self.sh("node {} fn init again".format(node.upper), self.cd(
            "python3 bin/fn --config {dir}/fn2.toml init --store {store} {groups}".format(
                dir=node.dir, store=node.store, groups=groups)),
            timeout=1800, expect=None)
        self.from_step("V0-NODE-REINIT", again, node=node.name,
                       limit="one existing store holding {} article(s); no concurrent "
                             "initializer".format(len(held)))
        if not held:
            self.emit("V0-NODE-REINIT-SAFE", NOT_EXERCISED, again.command,
                      "(the store held nothing)", node=node.name,
                      blocker="the store held no accepted article when the second init "
                              "ran, so there was nothing for it to destroy")
            return
        worst = None
        for msgid in held:
            one = self.sh("node {} still holds {} after the second init".format(
                node.upper, msgid), self.cd(self.fn(
                    "--store {} inspect --message-id '{}'".format(node.store, msgid))),
                timeout=900, expect=EXIT_OK)
            if one.rc != EXIT_OK and worst is None:
                worst = one
        self.emit("V0-NODE-REINIT-SAFE",
                  ACCEPTED if worst is None else exit_verdict(worst.rc),
                  "run_store.py --store <{}> inspect --message-id <each of {}>".format(
                      node.name, len(held)),
                  "every one of the {} articles the store held before the second init "
                  "was still there".format(len(held)) if worst is None
                  else "{} exited {} after the second init".format(worst.name, worst.rc),
                  node=node.name, exit_code=0 if worst is None else worst.rc,
                  limit="exact Message-ID lookups over what this run posted, not a "
                        "comparison of the store's octets")

    def loopback_refusal(self):
        root = "{}/loopback".format(self.deploy)
        self.sh("loopback refusal: init", self.cd(
            "mkdir -p {root} && python3 bin/fn --config {root}/fn.toml init "
            "--store {root}/store --group {g} --listen 10.99.0.1:1119".format(
                root=root, g=GROUPS[0])), timeout=1800, expect=None)
        step = self.sh("loopback refusal: run", self.cd(
            "timeout 60 python3 bin/fn --config {root}/fn.toml run "
            "--control {root}/control.sock".format(root=root)),
            timeout=180, expect=None)
        self.from_step("V0-NODE-LOOPBACK", step,
                       limit="one non-loopback address; nothing here tests a bind that "
                             "the kernel would refuse for a different reason")

    # -- F-OUT: the three outcomes ---------------------------------------
    def three_outcomes_node(self, node: NodeSpec, msgid: str, subject: str):
        """The deploy gate's three outcomes, with a row each, plus the seeds."""
        payload = "{}/seed.article".format(node.dir)
        self.push_file(article(msgid, GROUPS[0], subject,
                               "Written on node {} by the v0 matrix.".format(node.upper)),
                       payload)
        uncertain = "<uncertain-{}@example.invalid>".format(node.name)
        accepted = self.sh("node {} outcome accepted".format(node.upper), self.cd(self.fn(
            "--store {} post --message-id '{}' --payload {} --group {}".format(
                node.store, msgid, payload, GROUPS[0]))), timeout=900, expect=EXIT_OK)
        self.from_step("V0-OUT-ACCEPTED", accepted, node=node.name,
                       limit="one article; the exit code is the observation, the "
                             "durability claim is books/store-files-invariants'")
        refused = self.sh("node {} outcome refused".format(node.upper), self.cd(self.fn(
            "--store {} inspect --message-id '{}'".format(node.store, ABSENT_ID))),
            timeout=900, expect=EXIT_REFUSED)
        self.from_step("V0-OUT-REFUSED", refused, node=node.name)
        unsure = self.sh("node {} outcome uncertain".format(node.upper), self.cd(self.fn(
            "--store {} post --message-id '{}' --payload {} --group {} "
            "--inject-fault postpublish".format(
                node.store, uncertain, payload, GROUPS[0]))), timeout=900,
            expect=EXIT_UNCERTAIN)
        self.from_step("V0-OUT-UNCERTAIN", unsure, node=node.name,
                       limit="an injected fault at one publication boundary; it is not "
                             "a power loss and the article is asserted in neither "
                             "direction afterwards")
        observed = (accepted.rc, refused.rc, unsure.rc)
        expected = (EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN)
        self.facts["three outcomes {}".format(node.name)] = (
            "accepted={} refused={} uncertain={} (expected {})".format(*observed, expected))
        if observed != expected:
            self.limitation(
                None,
                "node {}: the three outcomes did not stay distinct in the exit codes: "
                "observed {}, expected {} (D13)".format(node.upper, observed, expected))
        recover = self.sh("node {} recover after the uncertain publication".format(
            node.upper), self.cd(self.fn("--store {} recover".format(node.store))),
            timeout=900, expect=None)
        self.from_step("V0-OUT-RECOVER", recover, node=node.name)
        if accepted.rc == EXIT_OK:
            node.accepted.append(msgid)
        probe = self.sh("node {} after recovery: the uncertain {}".format(
            node.upper, uncertain), self.cd(self.fn(
                "--store {} inspect --message-id '{}'".format(node.store, uncertain))),
            timeout=900, expect=None)
        self.limitation(
                None,
            "node {}: the injected uncertain publication {} is asserted in neither "
            "direction; `inspect` exited {} for it after recovery. An indeterminate "
            "outcome is evidence about the report, not about the article."
            .format(node.upper, uncertain, probe.rc))

    def seed_node(self, node: NodeSpec):
        """The extra articles the transit, streaming and statement rows need."""
        for msgid, subject in ((STREAM[node.name], "for the streaming offer"),
                               (STX[node.name], "for the statement exchange")):
            payload = "{}/{}.article".format(node.dir, msgid.strip("<>").split("@")[0])
            prepared = getattr(self, "statement_file", None)
            if msgid == STX["a"] and prepared:
                # The statement article is posted with its field already on it,
                # so the row that watches it cross is watching the field cross.
                payload = prepared
            else:
                self.push_file(article(msgid, GROUPS[0], subject,
                                       "Seeded on node {} by the v0 matrix.".format(
                                           node.upper)), payload)
            step = self.sh("node {} seed {}".format(node.upper, msgid), self.cd(self.fn(
                "--store {} post --message-id '{}' --payload {} --group {}".format(
                    node.store, msgid, payload, GROUPS[0]))), timeout=900, expect=None)
            if step.rc == EXIT_OK:
                node.accepted.append(msgid)
            else:
                self.limitation(
                None,
                    "node {}: seeding {} exited {} ({}); the rows that offer it are "
                    "recorded against that.".format(node.upper, msgid, step.rc,
                                                    step.first_line))

    # -- F-GROUP: groups, capacity, peers, live reconfiguration -----------
    def groups_and_capacity(self, node: NodeSpec):
        self.groups(node)
        self.capacity(node)

    def groups(self, node: NodeSpec):
        create = self.sh("node {} group create {}".format(node.upper, MATRIX_GROUP),
                         self.cd(self.cli(node, "group create " + MATRIX_GROUP)),
                         timeout=900, expect=None)
        self.from_step("V0-GROUP-CREATE", create, node=node.name,
                       limit="one group on a store no service holds")
        self.sh("node {} group create {}".format(node.upper, THROWAWAY_GROUP),
                self.cd(self.cli(node, "group create " + THROWAWAY_GROUP)),
                timeout=900, expect=None)
        retire = self.sh("node {} group retire {}".format(node.upper, THROWAWAY_GROUP),
                         self.cd(self.cli(node, "group retire " + THROWAWAY_GROUP)),
                         timeout=900, expect=None)
        self.from_step("V0-GROUP-RETIRE", retire, node=node.name)
        unknown = self.sh("node {} group retire an unserved group".format(node.upper),
                          self.cd(self.cli(node, "group retire fn.not.served")),
                          timeout=900, expect=None)
        self.from_step("V0-GROUP-UNKNOWN", unknown, node=node.name)

    def capacity(self, node: NodeSpec):
        # Capacity runs against a scratch store of its own: a refusal row has to
        # leave the served store's admission untouched.
        scratch = "{}/capacity-store".format(node.dir)
        self.sh("node {} capacity store".format(node.upper), self.cd(self.fn(
            "--store {} init --group {}".format(scratch, GROUPS[0]))), timeout=1800,
            expect=None)
        cap = self.sh("node {} capacity 64".format(node.upper), self.cd(self.fn(
            "--store {} capacity 64".format(scratch))), timeout=900, expect=None)
        self.from_step("V0-CAP-SET", cap, node=node.name,
                       limit="a scratch store beside the served one, so a refusal here "
                             "cannot change what the node serves")
        tight = self.sh("node {} capacity 1".format(node.upper), self.cd(self.fn(
            "--store {} capacity 1".format(scratch))), timeout=900, expect=None)
        payload = "{}/capacity.article".format(node.dir)
        self.push_file(article("<capacity-{}@example.invalid>".format(node.name),
                               GROUPS[0], "over the capacity", "x" * 4096), payload)
        over = self.sh("node {} post beyond the capacity".format(node.upper),
                       self.cd(self.fn(
                           "--store {} post --message-id '<capacity-{}@example.invalid>' "
                           "--payload {} --group {}".format(
                               scratch, node.name, payload, GROUPS[0]))),
                       timeout=900, expect=None)
        self.from_step("V0-CAP-REFUSE", over, node=node.name,
                       limit="the capacity was set to 1 (rc={}) and the article's own "
                             "charge is what has to exceed it; the charge is ACL2's, "
                             "and a 4 KiB article charged 3 on this tree".format(tight.rc))

    def group_served(self, node: NodeSpec):
        probe = self.feed("presence", "--port {} --groups {}".format(
            node.port, MATRIX_GROUP),
            name="node {} serves {}".format(node.upper, MATRIX_GROUP), expect=None)
        result = self.payload(probe)
        status = result.get("groups", {}).get(MATRIX_GROUP, "(no reply)")
        self.from_reply("V0-GROUP-SERVED", status, probe.command, node=node.name,
                        limit="the group was created before the service started")

    # `fn-cfg-peer-inboundp` (books/peer-config.lisp:144) requires the inbound
    # ceiling to be at most `*fn-record-max-payload*` (books/records.lisp:43),
    # which is 32768.  Both CLIs default `--inbound-max-octets` to 1048576, so
    # the default is outside the record's admissible range and `peer add`
    # refuses `:peer-record` every time.  Measured on persvati 2026-09-20: the
    # same command with 32768 is accepted.  The matrix passes the admissible
    # value and records the default as a defect.
    PEER_INBOUND_MAX_OCTETS = 32768

    def peer_records(self):
        """A peer record on each node naming the other (specs/peering.md 1.2)."""
        probe = self.sh("peer record CLI", self.cd("""
if python3 tools/run_store.py --store /nonexistent peer --help >/dev/null 2>&1; then
  echo STORE-PEER
elif [ -x bin/fn ] && python3 bin/fn peer --help >/dev/null 2>&1; then echo FN-PEER
else echo NONE; fi
"""), expect=None)
        kind = probe.output.strip().splitlines()[-1] if probe.output.strip() else "NONE"
        self.facts["peer records"] = kind.lower()
        if kind == "NONE":
            blocker = ("no CLI on this commit writes an `fn-cfg-peerp` record "
                       "(specs/peering.md 1.2)")
            self.blocked(("V0-PEER-ADD", "V0-PEER-LIST", "V0-TRANSIT-IDENTITY"),
                         blocker, verdict=NOT_BUILT,
                         owner="w6/peering-inbound", invocation=probe.command)
            return
        # The node's OWN RFC 5537 section 3.2 <path-identity>, and it is not the
        # peer record's.  `fn-peer-local-identity` (books/peer-inbound.lisp)
        # reads the `path-identity` POLICY slot; an unset slot reads as the
        # empty string and `fn-path-names-p` never matches it, so
        # `fn-peer-decide-transfer`'s loop arm cannot fire and an article whose
        # Path already names this node is accepted and then served.  That is
        # exactly what this matrix measured at 6fb30ca -- V0-TRANSIT-LOOP 235
        # and V0-TRANSIT-LOOP-ABSENT 220 -- while tools/twonode_gate.py, which
        # sets the slot, measured `437 transfer rejected; path loop` and `430`
        # on the same commit.  The matrix wrote every peer record and never
        # gave either node a name of its own.
        for node in self.nodes:
            ident = self.sh(
                "node {} path-identity".format(node.upper),
                self.cd(self.fn("--store {} policy set path-identity {}".format(
                    node.store, node.path_identity))), timeout=1800, expect=None)
            self.from_step("V0-TRANSIT-IDENTITY", ident, node=node.name,
                           limit="the loop rows below are unfounded without it")
            if ident.rc != EXIT_OK:
                self.gaps.append(
                    "node {} has no <path-identity> of its own (rc={}, {}); RFC 5537 "
                    "3.5 loop suppression cannot fire on it and V0-TRANSIT-LOOP is "
                    "measuring an unconfigured node.".format(
                        node.upper, ident.rc, ident.first_line))
            else:
                self.facts["node {} path-identity".format(node.upper)] = \
                    node.path_identity

        for node, other in ((self.a, self.b), (self.b, self.a)):
            add = self.sh("node {} peer record for {}".format(node.upper, other.upper),
                          self.cd(self.fn(
                              "--store {} peer add {} --path-identity {} "
                              "--nntp 127.0.0.1:{} --inbound-groups 'fn.*' "
                              "--inbound-max-octets {} --outbound-groups 'fn.*' "
                              "--streaming --source-address 127.0.0.1".format(
                                  node.store, other.name, other.path_identity,
                                  getattr(other, "assigned_port", 0),
                                  self.PEER_INBOUND_MAX_OCTETS))),
                          timeout=1800, expect=None)
            self.from_step("V0-PEER-ADD", add, node=node.name,
                           limit="a peer record is configuration, not authorization: "
                                 "nothing on this tree authenticates the peer it names. "
                                 "`--inbound-max-octets {}` is passed explicitly because "
                                 "the CLI default of 1048576 is refused"
                                 .format(self.PEER_INBOUND_MAX_OCTETS))
            if add.rc != EXIT_OK:
                self.limitation(
                None,
                    "node {} could not write a peer record for {} (rc={}, {}); the "
                    "transit rows below are running without the peer table they name, "
                    "and an fn node answers every transit command 502 to a connection "
                    "it does not resolve as a peer.".format(
                        node.upper, other.upper, add.rc, add.first_line))
            listing = self.sh("node {} lists its peers".format(node.upper),
                              self.cd(self.fn("--store {} peer list".format(node.store))),
                              timeout=1800, expect=None)
            shows = other.name in listing.output
            self.emit("V0-PEER-LIST",
                      ACCEPTED if (listing.rc == EXIT_OK and shows)
                      else REFUSED if listing.rc == EXIT_OK
                      else exit_verdict(listing.rc), listing.command,
                      "rc={} lists {}: {}".format(listing.rc, other.name, shows),
                      node=node.name, exit_code=listing.rc,
                      limit="the name is read out of the listing's text")
            if listing.rc == EXIT_OK and not shows and add.rc == EXIT_OK:
                self.limitation(
                None,
                    "node {} accepted `peer add {}` but `peer list` does not show it: "
                    "the record did not survive the replay.".format(
                        node.upper, other.name))

    def peer_remove(self):
        absent = self.sh("peer remove a peer that is not there", self.cd(self.fn(
            "--store {} peer remove no-such-peer".format(self.a.store))),
            timeout=900, expect=None)
        self.from_step("V0-PEER-ABSENT", absent)
        real = self.sh("peer remove the configured peer", self.cd(self.fn(
            "--store {} peer remove {}".format(self.a.store, self.b.name))),
            timeout=900, expect=None)
        self.from_step("V0-PEER-REMOVE", real,
                       limit="run after the servers stopped, so it says nothing about "
                             "removing a peer from a live service")

    def live_reconfiguration(self):
        """The two halves: the control channel accepts, the offline CLI refuses."""
        socket_path = "{}/control.sock".format(self.a.dir)
        present = self.sh("node A control socket", "test -S {} && echo SOCKET || "
                          "echo NO-SOCKET".format(socket_path), expect=None)
        if "NO-SOCKET" in present.output:
            self.emit("V0-CFG-LIVE", NOT_EXERCISED,
                      "matrix.py control --socket {} --line 'DECLARE-GROUP ...'".format(
                          socket_path),
                      "(no control socket)",
                      blocker="node A's server is {} and it opened no control socket at "
                              "{}; only the owner has a control channel".format(
                                  self.a.kind, socket_path))
        else:
            step = self.matrix("control", "--socket {} --line 'DECLARE-GROUP {}'".format(
                socket_path, "fn.matrix.live"),
                name="live reconfiguration: declare a group on node A", expect=None)
            reply = self.payload(step).get("reply", "(no reply)")
            verdict = (ACCEPTED if step.rc == 0 else
                       REFUSED if reply.startswith("refused") else
                       UNCERTAIN if reply.startswith("uncertain") else REFUSED)
            self.emit("V0-CFG-LIVE", verdict, step.command, reply, exit_code=step.rc,
                      limit="one group declared on one live service; no concurrent "
                            "reader was observed across the change")
        offline = self.sh("offline group create while the service holds the store",
                          self.cd(self.cli(self.a, "group create fn.matrix.offline")),
                          timeout=900, expect=None)
        self.from_step("V0-CFG-LIVE-REFUSE", offline,
                       limit="the refusal is the store lock's; a different server that "
                             "does not take the writer lock would not produce it")

    def step_named(self, name):
        for step in self.steps:
            if step.name == name:
                return step
        return None

    # -- F-AUTH -----------------------------------------------------------
    def principals(self):
        seed_file = "{}/seed.hex".format(self.deploy)
        self.push_file(SEED + "\n", seed_file)
        new = self.sh("principal new", self.cd(
            "python3 bin/fn --config {}/fn.toml principal new --seed {}".format(
                self.a.dir, seed_file)), timeout=900, expect=None)
        self.from_step("V0-AUTH-NEW", new,
                       limit="one seed; the derivation is tools/stx.py's and ACL2's, "
                             "not this gate's")
        principal, public = "", ""
        for line in new.output.splitlines():
            words = line.split()
            if len(words) == 2 and len(words[1]) == 64:
                if words[0] == "id":
                    principal = words[1]
                elif words[0] == "public-key":
                    public = words[1]
        # The keyring `tools/stx.py verify` reads: one line, the creator id and
        # its public key, both hex.  Both come from ACL2 through `principal
        # new`; nothing here derives either.
        self.keyring_line = "{} {}".format(principal, public) if principal and public else ""
        for node in self.nodes:
            args = "principal set-password {} --password {}".format(AUTH_USER, AUTH_SECRET)
            if principal:
                args += " --principal " + principal
            step = self.sh("node {} principal set-password".format(node.upper),
                           self.cd(self.cli(node, args)), timeout=900, expect=None)
            self.from_step("V0-AUTH-PASSWORD", step, node=node.name,
                           limit="what is stored is books/auth-secret.lisp's salted "
                                 "verifier, derived in an ACL2 session; this row is "
                                 "about the CLI writing it, not about the strength of "
                                 "the digest or the secret's protection on the wire")
            listing = self.sh("node {} principal list".format(node.upper),
                              self.cd(self.cli(node, "principal list")),
                              timeout=900, expect=None)
            shows = AUTH_USER in listing.output
            self.emit("V0-AUTH-LIST",
                      ACCEPTED if (listing.rc == 0 and shows)
                      else REFUSED if listing.rc == 0 else exit_verdict(listing.rc),
                      listing.command, "rc={} lists {}: {}".format(
                          listing.rc, AUTH_USER, shows),
                      node=node.name, exit_code=listing.rc,
                      limit="one registry: `set-password` writes and `list` reads "
                            "the credential file ([auth] path, else "
                            "<store>/auth.toml), which is the same file the running "
                            "service loads. The listing prints the login, its "
                            "principal and its posting flag and never the verifier")

    def auth_session(self, node: NodeSpec):
        keys = ("V0-AUTH-ADVERTISED", "V0-AUTH-GATED", "V0-AUTH-LOGIN",
                "V0-AUTH-WITHDRAWN", "V0-AUTH-POST", "V0-AUTH-WRONG")
        step = self.matrix("auth", "--port {} --group {} --user {} --secret {} "
                           "--msgid '{}'".format(node.port, GROUPS[0], AUTH_USER,
                                                 AUTH_SECRET, AUTH_POST[node.name]),
                           name="node {} AUTHINFO session".format(node.upper),
                           expect=None)
        result = self.payload(step)
        if not result or "AUTHINFO USER" not in result:
            self.blocked(keys, "the AUTHINFO driver produced no result on node {}: {}"
                         .format(node.upper, result.get("error", step.first_line)),
                         nodes=(node.name,), invocation=step.command)
            return
        if not_permitted(result["AUTHINFO USER"]) and not unsupported(
                result["AUTHINFO USER"]):
            self.blocked(keys,
                         "node {} DISPATCHED `AUTHINFO USER` and answered '{}': the "
                         "command is there and this connection may not use it yet "
                         "(RFC 4643 section 2.3.1 requires 483 under a protected-only "
                         "policy)".format(node.upper, result["AUTHINFO USER"]),
                         nodes=(node.name,), invocation=step.command)
            return
        if unsupported(result["AUTHINFO USER"]):
            uncert = self.uncertified("nntp-auth", "served", "owner")
            self.blocked(keys,
                         "node {} answered `AUTHINFO USER` with '{}': the served path on "
                         "this commit does not dispatch RFC 4643. books/nntp-auth.lisp "
                         "exists but is not included by books/served.lisp (auth-wired={})"
                         "{}".format(node.upper, result["AUTHINFO USER"],
                                     self.support.get("auth-wired", "?"),
                                     "; uncertified: " + ", ".join(uncert) if uncert else ""),
                         verdict=NOT_BUILT, owner="w10/auth-served",
                         nodes=(node.name,), invocation=step.command)
            return
        self.emit("V0-AUTH-ADVERTISED",
                  ACCEPTED if result.get("AUTHINFO ADVERTISED") else REFUSED,
                  step.command, "CAPABILITIES before the login: {}".format(
                      ", ".join(result.get("advertised_before", [])) or "(none)"),
                  node=node.name)
        self.from_reply("V0-AUTH-GATED", result.get("POST BEFORE", ""), step.command,
                        node=node.name,
                        limit="one gated command; RFC 4643 section 2.3 does not require "
                              "the same code for every gated verb. The gate is the "
                              "NODE POLICY (`fn init --auth-required`, [auth] required) "
                              "and these two nodes do not set it: a node that serves "
                              "readers unauthenticated and a transit peer on the same "
                              "loopback address cannot, because "
                              "fn-auth-restricted-keywordp gates the reader verbs and "
                              "IHAVE alike. tests/test_auth.py "
                              "ServedCredentialTests.test_post_is_gated_by_the_"
                              "configured_policy is the same question asked of a node "
                              "that does set it")
        self.from_reply("V0-AUTH-LOGIN", result.get("AUTHINFO PASS", ""), step.command,
                        node=node.name,
                        limit="USER/PASS over an unprotected loopback connection")
        self.emit("V0-AUTH-WITHDRAWN",
                  ACCEPTED if result.get("AUTHINFO WITHDRAWN") else REFUSED,
                  step.command, "CAPABILITIES after the login: {}".format(
                      ", ".join(result.get("advertised_after", [])) or "(none)"),
                  node=node.name)
        self.from_reply("V0-AUTH-POST", result.get("POST AFTER COMMIT", ""),
                        step.command, node=node.name)
        if str(result.get("POST AFTER COMMIT", "")).startswith("240"):
            node.accepted.append(AUTH_POST[node.name])
        self.from_reply("V0-AUTH-WRONG", result.get("AUTHINFO WRONG", ""),
                        step.command, node=node.name,
                        limit="one wrong password; no rate limit or lockout is tested")

    # -- F-POST -----------------------------------------------------------
    def post_cycle(self, node: NodeSpec):
        # RFC 3977 section 6.3.1.1: the node answers 440 when posting is not
        # permitted, and on this tree the permission is the AUTHENTICATED
        # PRINCIPAL's (books/nntp-auth, fn-auth-postingp).  So the POST rows
        # log in first; the row that checks an unauthenticated POST is refused
        # is V0-AUTH-GATED, and it must stay that way or the two rows would be
        # measuring each other.
        keys = self.POST_KEYS
        group = self.native_group if self.backend == NATIVE_BACKEND else GROUPS[0]
        msgid = (self.native_post_ids[node.name] if self.backend == NATIVE_BACKEND
                 else SOCKET_POST[node.name])
        # The first native slice requires a preprovisioned profile that permits
        # local posting without a credential.  Credential administration is a
        # separate pending public surface, and secrets must not enter evidence
        # through the recorded invocation.
        user = "" if self.backend == NATIVE_BACKEND else AUTH_USER
        secret = "" if self.backend == NATIVE_BACKEND else AUTH_SECRET
        step = self.matrix("postcycle", "--port {} --group {} --msgid '{}' "
                           "--user {} --secret {}".format(
                               node.port, shlex.quote(group), msgid,
                               shlex.quote(user), shlex.quote(secret)),
            name="node {} POST cycle".format(node.upper), expect=None)
        result = self.payload(step)
        if not result or "POST" not in result:
            error = result.get("error", step.first_line)
            # A POST that never answers is not the same finding as a POST that
            # was never accepted, and the difference is visible: ask the node,
            # over a connection of its own, whether it now serves the article.
            after = self.feed("presence", "--port {} --groups {} --present '{}'".format(
                node.port, shlex.quote(group), msgid),
                name="node {} serves the article whose POST never answered".format(
                    node.upper), expect=None)
            served = self.payload(after).get("present", {}).get(
                msgid, "(no reply)")
            committed = str(served).startswith("220")
            self.blocked(keys, "the POST driver produced no result on node {}: {}. "
                         "Asked afterwards on a fresh connection, the node answered "
                         "`ARTICLE {}` with '{}'{}".format(
                             node.upper, error, msgid, served,
                             ". The article was COMMITTED and is served, and the "
                             "poster's connection never received a reply: a client "
                             "cannot tell accepted from uncertain, which is D13's "
                             "three outcomes not reaching the wire at all"
                             if committed else
                             ". The article is not there either, so nothing is known "
                             "about whether the write happened"),
                         nodes=(node.name,), invocation=step.command)
            if committed:
                self.limitation(
                None,
                    "node {}: a POST through the served path COMMITTED the article -- "
                    "the node serves {} on a later connection -- and never answered the "
                    "poster. Measured by hand on persvati 2026-09-20 as well: 340, the "
                    "article, the terminating dot, then no byte for 300 s while the "
                    "group's article count rose by one.".format(
                        node.upper, msgid))
                node.accepted.append(msgid)
            return
        if not_permitted(result["POST"]):
            self.blocked(keys,
                         "node {} DISPATCHED `POST` and answered '{}' after the "
                         "AUTHINFO login this phase performed ({} / {}): posting is "
                         "permitted by the authenticated principal's credential "
                         "(fn-auth-postingp), so either the login did not take or the "
                         "credential does not carry the allowance".format(
                             node.upper, result["POST"],
                             result.get("AUTHINFO USER", "no USER reply"),
                             result.get("AUTHINFO PASS", "no PASS reply")),
                         nodes=(node.name,), invocation=step.command)
            return
        if unsupported(result["POST"]):
            uncert = self.uncertified("owner", "served")
            self.blocked(keys,
                         "node {} answered `POST` with '{}'. The server that started is "
                         "`{}`; POST is on the owner's served path and {}".format(
                             node.upper, result["POST"], node.kind,
                             "books/" + ", books/".join(uncert) + " have no certificate "
                             "in the deploy tree" if uncert
                             else "no entry point on this commit offered it"),
                         verdict=NOT_BUILT, owner="w9/peering-e2e (books/owner)",
                         nodes=(node.name,), invocation=step.command)
            return
        self.from_reply("V0-POST-OPEN", result["POST"], step.command, node=node.name)
        self.from_reply("V0-POST-COMMIT", result.get("COMMIT", ""), step.command,
                        node=node.name,
                        limit="one article; the durability behind the 240 is the "
                              "store's, asserted by the recovery rows below")
        self.emit("V0-POST-READBACK",
                  ACCEPTED if result.get("counted") else REFUSED, step.command,
                  "GROUP before={} after={}".format(result.get("GROUP BEFORE"),
                                                    result.get("GROUP AFTER")),
                  node=node.name)
        self.from_reply("V0-POST-FRESH", result.get("FRESH ARTICLE", ""), step.command,
                        node=node.name)
        self.from_reply("V0-POST-DUPLICATE", result.get("DUPLICATE", ""), step.command,
                        node=node.name,
                        limit="the duplicate is offered on a fresh connection because "
                              "one clock observation is pinned per connection at accept")
        duplicate = str(result.get("DUPLICATE", ""))
        date = str(result.get("DATE AFTER DUPLICATE", ""))
        self.emit("V0-POST-CLOCK",
                  ACCEPTED if date.startswith("111") else
                  REFUSED if date.startswith("503") else reply_verdict(date),
                  step.command,
                  "the duplicate answered '{}' and DATE afterwards answered '{}'".format(
                      duplicate or "(nothing)", date or "(nothing)"),
                  node=node.name,
                  limit="a 441 for an article the node already holds and a 441 for a "
                        "clock the node no longer has are the same code; DATE is what "
                        "separates them from outside, because a refused reading costs "
                        "the owner its clock (D10-a) and DATE then answers 503. This "
                        "row does not INDUCE a clock fault -- it checks that an "
                        "ordinary duplicate did not cause one")
        refused_from = str(result.get("FROM", ""))
        served_from = str(result.get("FROM ARTICLE", ""))
        self.emit("V0-POST-FROM-MAILBOX",
                  from_mailbox_verdict(refused_from, served_from),
                  step.command,
                  "POST of `From: yue` answered '{}'; STAT of its Message-ID "
                  "answered '{}'".format(refused_from or "(nothing)",
                                         served_from or "(nothing)"),
                  node=node.name,
                  limit="one unaddressed From; the rest of the mailbox-list "
                        "grammar is books/mailbox.lisp's and its witnesses are "
                        "tests/acl2/injection-tests.lisp")
        if str(result.get("COMMIT", "")).startswith("240"):
            node.accepted.append(msgid)

    def credential(self):
        """The reader credential the socket phases log in with, if the backend has one.

        The first native slice runs a profile that permits local posting
        without a credential (see `post_cycle`); an empty user skips AUTHINFO.
        """
        if self.backend == NATIVE_BACKEND:
            return "", ""
        return AUTH_USER, AUTH_SECRET

    def post_concurrent(self):
        user, secret = self.credential()
        step = self.matrix("concurrent", "--port {} --group {} --msgid '{}' "
                           "--user {} --secret {}".format(
                               self.a.port, GROUPS[0], CONCURRENT_ID,
                               shlex.quote(user), shlex.quote(secret)),
            name="a second reader across node A's POST", expect=None)
        result = self.payload(step)
        if not result or "POST" not in result:
            self.emit("V0-POST-CONCURRENT", NOT_EXERCISED, step.command, "(no result)",
                      blocker="the concurrency driver produced no result: {}".format(
                          result.get("error", step.first_line)))
            return
        if "ConnectionRefused" in str(result) or "timed out" in str(result):
            self.emit("V0-POST-CONCURRENT", NOT_EXERCISED, step.command, str(result)[:300],
                      blocker="node A's server accepted only one connection at a time "
                              "(tools/run_reader.py calls listen(1)), so the second "
                              "reader never reached the greeting")
            return
        mid = result.get("WATCHER MID", "")
        commit = result.get("COMMIT", "")
        verdict = (ACCEPTED if mid.startswith("211") and commit.startswith("240")
                   else reply_verdict(mid if not mid.startswith("211") else commit))
        self.emit("V0-POST-CONCURRENT", verdict, step.command,
                  "watcher mid-post={} commit={}".format(mid, commit),
                  limit="two connections on one box; this is not concurrent load")
        if commit.startswith("240"):
            self.a.accepted.append(CONCURRENT_ID)

    # -- F-READ and F-PIN --------------------------------------------------
    READ_COMMANDS = (
        ("V0-READ-CAPABILITIES", "CAPABILITIES"),
        ("V0-READ-MODE-READER", "MODE READER"),
        ("V0-READ-LIST-ACTIVE", "LIST ACTIVE"),
        ("V0-READ-LIST-NEWSGROUPS", "LIST NEWSGROUPS"),
        ("V0-READ-LIST-NEWSGROUPS-WILDMAT", "LIST NEWSGROUPS WILDMAT"),
        ("V0-READ-LIST-OVERVIEW-FMT", "LIST OVERVIEW.FMT"),
        ("V0-READ-LIST-ACTIVE-TIMES", "LIST ACTIVE.TIMES"),
        ("V0-READ-LIST-HEADERS", "LIST HEADERS"),
        ("V0-READ-GROUP", "GROUP"),
        ("V0-READ-LISTGROUP", "LISTGROUP"),
        ("V0-READ-ARTICLE", "ARTICLE"),
        ("V0-READ-HEAD", "HEAD"),
        ("V0-READ-BODY", "BODY"),
        ("V0-READ-STAT", "STAT"),
        ("V0-READ-ARTICLE-MSGID", "ARTICLE MSGID"),
        ("V0-READ-ARTICLE-ABSENT", "ARTICLE ABSENT"),
        ("V0-READ-OVER", "OVER"),
        ("V0-READ-OVER-RANGE", "OVER RANGE"),
        ("V0-READ-HDR", "HDR"),
        ("V0-READ-XOVER", "XOVER"),
        ("V0-READ-XHDR", "XHDR"),
        ("V0-READ-XPAT", "XPAT"),
        ("V0-READ-NEWNEWS", "NEWNEWS"),
        ("V0-READ-NEWNEWS-FUTURE", "NEWNEWS FUTURE"),
        ("V0-READ-NEWNEWS-SYNTAX", "NEWNEWS SYNTAX"),
        ("V0-READ-DATE", "DATE"),
        ("V0-READ-HELP", "HELP"),
        ("V0-READ-UNKNOWN", "UNKNOWN"),
    )
    READ_KEYS = tuple(k for k, _ in READ_COMMANDS) + (
        "V0-READ-NEXT", "V0-READ-LAST", "V0-READ-FRAMING")

    def read_surface(self, node: NodeSpec):
        group = self.native_group if self.backend == NATIVE_BACKEND else GROUPS[0]
        step = self.matrix("surface", "--port {} --group {} --msgid '{}' --absent '{}'"
                           .format(node.port, shlex.quote(group),
                                   node.accepted[0] if node.accepted else ART[node.name],
                                   ABSENT_ID),
                           name="node {} reader surface".format(node.upper), expect=None)
        result = self.payload(step)
        if not result or "GROUP" not in result:
            self.blocked(self.READ_KEYS,
                         "the reader driver produced no result on node {}: {}".format(
                             node.upper, result.get("error", step.first_line)),
                         nodes=(node.name,), invocation=step.command)
            return
        count = result.get("group_count", 0)
        self.group_counts[node.name] = count
        served_by = "served by `{}` on port {}".format(node.kind, node.port)
        for key, command in self.READ_COMMANDS:
            status = result.get(command, "")
            if key != "V0-READ-UNKNOWN" and unsupported(status):
                self.emit(key, NOT_BUILT, step.command, status, node=node.name,
                          blocker="`{}` answered '{}' on this commit; the entry point "
                                  "that started is `{}`".format(command, status, node.kind),
                          owner="w9/peering-e2e (books/owner)" if node.kind == "reader"
                                else None)
                continue
            self.from_reply(key, status, step.command, node=node.name, limit=served_by)
        # The cursor pair: what RFC 3977 section 6.1.4 requires depends on how
        # many articles the group holds, so the expectation comes from the
        # count the server itself reported.
        for key, command in (("V0-READ-NEXT", "NEXT"), ("V0-READ-LAST", "LAST")):
            status = result.get(command, "")
            self.from_reply(key, status, step.command, node=node.name,
                            limit="{}; the group held {} article(s) when this ran, and "
                                  "with one article 421/422 is the correct answer"
                                  .format(served_by, count))
        same = result.get("FRAMING SAME")
        self.emit("V0-READ-FRAMING", ACCEPTED if same else REFUSED, step.command,
                  "DATE split across two segments answered '{}' against '{}'".format(
                      result.get("FRAMING"), result.get("DATE")),
                  node=node.name,
                  limit="one command split at one point; the chunk-independence "
                        "keystone is books/wire-invariants', not this row")

    def capability_pins(self, node: NodeSpec):
        user, secret = self.credential()
        step = self.matrix("pins", "--port {} --group {} --user {} --secret {}".format(
            node.port, GROUPS[0], shlex.quote(user), shlex.quote(secret)),
                           name="node {} capability pins".format(node.upper),
                           timeout=600, expect=None)
        result = self.payload(step)
        if not result or "advertised" not in result:
            self.blocked(("V0-PIN-DISPATCHED", "V0-PIN-ADVERTISED"),
                         "the capability driver produced no result on node {}: {}".format(
                             node.upper, result.get("error", step.first_line)),
                         nodes=(node.name,), invocation=step.command)
            return
        missing = result.get("advertised_not_dispatched", [])
        extra = result.get("dispatched_not_advertised", [])
        limit = ("only the {} labels with a probe command are checked; VERSION and "
                 "IMPLEMENTATION have none".format(len(result.get("advertised", []))))
        self.emit("V0-PIN-DISPATCHED", ACCEPTED if not missing else REFUSED,
                  step.command,
                  "advertised={} not dispatched={}".format(
                      ",".join(result.get("advertised", [])) or "(none)",
                      ",".join(missing) or "(none)"),
                  node=node.name, limit=limit)
        self.emit("V0-PIN-ADVERTISED", ACCEPTED if not extra else REFUSED,
                  step.command,
                  "dispatched={} not advertised={}".format(
                      ",".join(result.get("dispatched", [])) or "(none)",
                      ",".join(extra) or "(none)"),
                  node=node.name,
                  limit=limit + "; RFC 3977 section 5.2.2 requires the capability "
                                "exactly when the command is available")
        if extra:
            self.limitation(
                None,
                "node {} dispatches {} without advertising them (RFC 3977 5.2.2, "
                "NNT-001)".format(node.upper, ", ".join(extra)))

    # -- F-TRANSIT ---------------------------------------------------------
    TRANSIT_KEYS = ("V0-TRANSIT-MODE-STREAM", "V0-TRANSIT-OFFER",
                    "V0-TRANSIT-TRANSFER", "V0-TRANSIT-IDENTICAL",
                    "V0-TRANSIT-DUPLICATE", "V0-TRANSIT-LOOP",
                    "V0-TRANSIT-LOOP-ABSENT", "V0-TRANSIT-CHECK-FRESH",
                    "V0-TRANSIT-TAKETHIS", "V0-TRANSIT-CHECK-DUP",
                    "V0-TRANSIT-TAKETHIS-DUP")

    def independence(self):
        # The absent set is the other node's SEEDED articles: what it held
        # before either listener started.  It is NOT everything the other node
        # has accepted, because both nodes carry an outbound feed record from
        # `peer_records` and the feed is running by the time this control does
        # -- and it feeds what became durable THROUGH the running owner, which
        # is every article a later phase posts.  At 6fb30ca this row read
        # `refused` on both nodes, and the only two Message-IDs in the absent
        # map that were present were `<auth-*>` and `<socket-*>`: the two the
        # AUTHINFO and POST phases had just posted through the server.  The
        # feed delivering them is the feature working.  What the control is
        # for -- that nothing the harness has not driven has moved the SEEDED
        # articles, so a later "it reached the far node" means something -- is
        # still exactly true of the seeds, and the transit rows offer seeds.
        for node, other in ((self.a, self.b), (self.b, self.a)):
            absent = getattr(other, "seeded", other.accepted) + node.rejected
            step = self.feed("presence", "--port {} --groups {} --present '{}' --absent '{}'"
                             .format(node.port, ",".join(GROUPS),
                                     ",".join(node.accepted),
                                     ",".join(absent)),
                             name="independence: node {} holds its own and not {}'s seeds"
                             .format(node.upper, other.upper), expect=None)
            result = self.payload(step)
            if not result or result.get("error"):
                self.emit("V0-TRANSIT-INDEPENDENT", NOT_EXERCISED, step.command,
                          str(result.get("error", step.first_line))[:200],
                          node=node.name,
                          blocker="the presence driver could not reach node {}: {}"
                                  .format(node.upper,
                                          result.get("error", step.first_line)))
                continue
            self.emit("V0-TRANSIT-INDEPENDENT", exit_verdict(step.rc), step.command,
                      "groups={} present={} absent={}".format(
                          result.get("groups"), result.get("present"),
                          result.get("absent")),
                      node=node.name, exit_code=step.rc,
                      limit="this is the control: every later claim that an article "
                            "reached a node rests on it. The absent set is the other "
                            "node's articles as of before either listener started; "
                            "the outbound feed carries what a running server accepts "
                            "and its crossings are measured by F-FEED, not here")
            if step.rc != 0:
                self.limitation(
                None,
                    "node {} failed the independence control, so the transit rows below "
                    "are unfounded: {}".format(node.upper, step.first_line))

    def transit_direction(self, source: NodeSpec, target: NodeSpec, way: str):
        msgid = ART[source.name]
        probe = self.feed(
            "relay",
            "--from-port {} --to-port {} --msgid '{}' --group {} --loop-msgid '{}' "
            "--loop-identity {}".format(source.port, target.port, msgid, GROUPS[0],
                                        LOOP_ID[way], target.path_identity),
            name="transit {}: offer {} from {} to {}".format(
                way.upper(), msgid, source.upper, target.upper), expect=None)
        result = self.payload(probe)
        offer = result.get("offer", "")
        target.transit = offer
        if way == "ab":
            self.facts["transit"] = "IHAVE -> '{}'; CAPABILITIES lists IHAVE: {}".format(
                offer or "no answer", result.get("ihave_advertised"))
        uncert = self.uncertified("peer-inbound", "served", "owner", "peer-config")
        if not offer or unsupported(offer):
            self.blocked(self.TRANSIT_KEYS,
                         "node {} answered `IHAVE {}` with '{}'. Transit is on the "
                         "served path, the server that started is `{}`, and {}"
                         .format(target.upper, msgid, offer or "no answer", target.kind,
                                 "books/" + ", books/".join(uncert)
                                 + " have no certificate in the deploy tree"
                                 if uncert else
                                 "no entry point on this commit dispatched it"),
                         verdict=NOT_BUILT, owner="w9/peering-e2e (books/owner)",
                         directions=(way,), invocation=probe.command)
            return
        if not_permitted(offer):
            self.blocked(self.TRANSIT_KEYS,
                         "node {} DISPATCHED `IHAVE {}` and answered '{}': the transit "
                         "surface is on this commit and the node decided about the "
                         "caller. The connection was not resolved as a peer -- node {} "
                         "is serving from `{}`, and a peer table is read at :open by "
                         "the owner (specs/peering.md 1.1, "
                         "fn-owner-peer-for-address){}".format(
                             target.upper, msgid, offer, target.upper, target.kind,
                             "" if target.kind.startswith(("owner", "fn"))
                             else ", which is not the entry point that started here"),
                         directions=(way,), invocation=probe.command)
            return
        served = "node {} is `{}`; the peer record on it names {}".format(
            target.upper, target.kind, source.name)
        self.from_reply("V0-TRANSIT-MODE-STREAM", result.get("mode_stream", ""),
                        probe.command, direction=way, limit=served)
        self.from_reply("V0-TRANSIT-OFFER", offer, probe.command, direction=way,
                        limit=served)
        self.from_reply("V0-TRANSIT-TRANSFER", result.get("transfer", ""),
                        probe.command, direction=way, limit=served)
        reread = result.get("reread", "")
        identical = bool(result.get("identical"))
        self.emit("V0-TRANSIT-IDENTICAL",
                  ACCEPTED if (reread.startswith("220") and identical)
                  else reply_verdict(reread) if not reread.startswith("220") else REFUSED,
                  probe.command,
                  "reread={} identical={}".format(reread or "(none)", identical),
                  direction=way,
                  limit="the octets are compared line for line against what the source "
                        "served; local article numbers are not compared and may differ")
        self.from_reply("V0-TRANSIT-DUPLICATE", result.get("duplicate", ""),
                        probe.command, direction=way,
                        limit="RFC 3977 6.3.2: 435 is the Message-ID history refusing "
                              "an article the node already holds")
        self.from_reply("V0-TRANSIT-LOOP", result.get("loop_result", ""),
                        probe.command, direction=way,
                        limit="RFC 5537 3.5; the Path is inside the article, so a "
                              "correct server says 335 first and then refuses")
        self.from_reply("V0-TRANSIT-LOOP-ABSENT", result.get("loop_absent", ""),
                        probe.command, direction=way)
        self.from_reply("V0-TRANSIT-CHECK-DUP", result.get("check_duplicate", ""),
                        probe.command, direction=way, limit="RFC 4644 2.4")
        self.from_reply("V0-TRANSIT-TAKETHIS-DUP", result.get("takethis_duplicate", ""),
                        probe.command, direction=way,
                        limit="RFC 4644 2.5: a client that ignores the advisory CHECK "
                              "must be refused after the bytes, never with a 2xx and "
                              "never with a retry code")
        if str(result.get("transfer", "")).startswith("235"):
            target.accepted.append(msgid)
        target.rejected.append(LOOP_ID[way])
        # The accepted streaming path, which the duplicate rows above cannot show.
        stream_step = self.matrix(
            "stream", "--from-port {} --to-port {} --msgid '{}'".format(
                source.port, target.port, STREAM[source.name]),
            name="transit {}: CHECK/TAKETHIS {} from {} to {}".format(
                way.upper(), STREAM[source.name], source.upper, target.upper),
            expect=None)
        srow = self.payload(stream_step)
        self.from_reply("V0-TRANSIT-CHECK-FRESH", srow.get("CHECK", ""),
                        stream_step.command, direction=way,
                        limit="RFC 4644 2.4: 238 is the only 'send it' answer; 431 and "
                              "438 are the two refusals the row accepts as decisions")
        self.from_reply("V0-TRANSIT-TAKETHIS", srow.get("TAKETHIS", ""),
                        stream_step.command, direction=way,
                        limit="one article over one session")
        if str(srow.get("TAKETHIS", "")).startswith("239"):
            target.accepted.append(STREAM[source.name])

    # -- F-FEED ------------------------------------------------------------
    FEED_KEYS = ("V0-FEED-QUEUE", "V0-FEED-OFFER", "V0-FEED-ONCE", "V0-FEED-JOURNAL")

    def outbound_feed(self):
        """The owner's own feed, with no socket driven by hand.

        `tools/twonode_gate.py`'s `scenario_owner_feed` is the run: node A
        posts through its own server, A's feed table (books/owner-feed.lisp,
        stepped by the owner) offers the article to B, and then the other
        way. Nothing here drives a transit socket; the only observations are
        whether the far side serves the article and what a second offer
        draws. The rows below are over that scenario's own facts.
        """
        if not self.has("owner-feed"):
            blocker = (
                "host/owner-host.lisp names no `fn-owner-feed-configure` on this "
                "commit, so no accepted article is offered by the owner itself. "
                "`books/peer-feed` certifies and `tools/run_feed.py` drives one peer "
                "by hand, which is not the owner doing it; the owner chain cannot be "
                "read until `books/peer-feed-invariants` certifies, because "
                "`books/owner-feed` includes it{}".format(
                    "" if self.support.get("cert-peer-feed-invariants") != "no"
                    else " and it has no certificate in this deploy tree"))
            self.blocked(self.FEED_KEYS, blocker, verdict=NOT_BUILT,
                         owner="w10/owner-feed",
                         invocation="grep fn-owner-feed-configure host/owner-host.lisp")
            return
        before = len(self.steps)
        super().scenario_owner_feed()
        mine = self.steps[before:]
        posts = [x for x in mine if "posts <fed-" in x.name]
        waits = [x for x in mine if "receives <fed-" in x.name]
        seconds = [x for x in mine if "a second offer of" in x.name]
        limit = ("both nodes are on one host over loopback, and the offering side is "
                 "the owner's feed table, not this harness's socket client")
        if not posts:
            self.blocked(self.FEED_KEYS,
                         "the owner-feed scenario posted nothing: {}".format(
                             "; ".join(x.first_line[:120] for x in mine[:2])
                             or "it skipped every direction"),
                         invocation="twonode_gate.scenario_owner_feed")
            return
        replies = [self.payload(x).get("result", "") or x.first_line for x in posts]
        if any(str(r)[:3] in ("440", "480", "483", "502") for r in replies):
            self.blocked(self.FEED_KEYS,
                         "the POST that would give the feed something to offer drew "
                         "440: `tools/twonode_gate.py`'s `post` driver phase does not "
                         "authenticate, and posting on this tree is the authenticated "
                         "principal's allowance (fn-auth-postingp, RFC 3977 section "
                         "6.3.1.1). The feed itself was never reached. The replies "
                         "were: {}".format(" ; ".join(str(r)[:80] for r in replies)),
                         invocation=posts[0].command)
            return
        worst = next((x for x in posts if x.rc != 0), None)
        self.emit("V0-FEED-QUEUE", ACCEPTED if worst is None else exit_verdict(worst.rc),
                  posts[0].command,
                  "{} of {} POSTs through the running server were accepted ({}), so "
                  "the feed had something durable to offer".format(
                      sum(1 for x in posts if x.rc == 0), len(posts),
                      " ; ".join(str(r)[:60] for r in replies)),
                  exit_code=0 if worst is None else worst.rc, limit=limit)
        if not waits:
            self.blocked(("V0-FEED-OFFER", "V0-FEED-ONCE"),
                         "no direction reached the waiting step, so nothing was "
                         "offered by the owner", invocation=posts[0].command)
        else:
            bad = next((x for x in waits if x.rc != 0), None)
            self.emit("V0-FEED-OFFER",
                      ACCEPTED if bad is None else exit_verdict(bad.rc),
                      waits[0].command,
                      "{}; {}".format(self.facts.get("owner feed", "no verdict"),
                                      " / ".join(
                                          "{}: {}".format(
                                              k, self.facts[k]) for k in sorted(
                                                  self.facts) if k.startswith(
                                                      "owner feed ")
                                          and "duplicate" not in k) or "no per-direction fact"),
                      exit_code=0 if bad is None else bad.rc, limit=limit)
            duplicate = " / ".join(self.facts[k] for k in sorted(self.facts)
                                   if k.startswith("owner feed") and "duplicate" in k)
            if not seconds:
                self.emit("V0-FEED-ONCE", NOT_EXERCISED, waits[0].command,
                          "(no second offer)",
                          blocker="no direction delivered, so there was nothing to "
                                  "offer a second time")
            else:
                ok = all(self.facts.get(k, "").find("ihave=435") >= 0
                         for k in self.facts if k.endswith("duplicate"))
                self.emit("V0-FEED-ONCE", ACCEPTED if ok else REFUSED,
                          seconds[0].command, duplicate or "(no duplicate fact)",
                          limit=limit + "; one re-offer per direction, which is the "
                                        "history answer that makes a restart-by-offer "
                                        "safe, not a proof of exactly-once")
        # The feed journal is `<store>/feed/<peer>.fnfd`: `Journal(store.root,
        # peer)` in tools/run_owner.py, which is what `feed_start` replays and
        # what `feed_flush` appends to. Neither `<run>/journal/feed` nor
        # `<store>/journal/feed` has ever existed, so this row read `refused`
        # with "(no feed journal found)" against a node whose journal was
        # sitting there -- a false negative about the one file the feed's
        # durability rests on.
        journal = self.sh("feed: the journal on node A", self.cd(
            "ls -l {}/feed 2>/dev/null | head -8 "
            "|| true".format(self.a.store)), expect=None)
        found = bool(journal.output.strip())
        self.emit("V0-FEED-JOURNAL", ACCEPTED if found else REFUSED, journal.command,
                  (journal.output.strip().splitlines() or ["(no feed journal found)"])[0],
                  exit_code=journal.rc,
                  limit="the journal's presence on disk, not its contents: the FNFD "
                        "record shapes are books/owner-feed's and the restart property "
                        "(K5) is tools/twonode_gate.py's scenario_feed_restart, which "
                        "this matrix does not run because it kills node A")

    # -- F-CRASH -----------------------------------------------------------
    def checkpoint_row(self):
        step = self.sh("checkpoint on node A", self.cd(self.fn(
            "--store {} anchor".format(self.a.store))), timeout=900, expect=None)
        reopen = self.sh("node A reopens after the checkpoint", self.cd(self.fn(
            "--store {} status".format(self.a.store))), timeout=900, expect=None)
        if step.rc not in (EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN):
            self.emit("V0-CRASH-CHECKPOINT", NOT_EXERCISED, step.command,
                      "rc={} {}".format(step.rc, step.first_line),
                      blocker="the anchor/checkpoint command exited {} on this commit; "
                              "no checkpoint codec is wired to the CLI "
                              "(planning/milestones.md M2)".format(step.rc))
            return
        self.emit("V0-CRASH-CHECKPOINT",
                  ACCEPTED if (step.rc == EXIT_OK and reopen.rc == EXIT_OK)
                  else exit_verdict(step.rc if step.rc != EXIT_OK else reopen.rc),
                  step.command,
                  "anchor rc={} ({}); reopen rc={}".format(
                      step.rc, step.first_line, reopen.rc),
                  exit_code=step.rc,
                  limit="a freshness anchor and a reopen; the checkpoint codec of "
                        "books/checkpoint-codec is not certified on this commit, so "
                        "this row is about the store reopening, not about a published "
                        "checkpoint's equivalence")

    def crash_phase(self):
        mode = ("transit" if self.b.transit and str(self.b.transit).startswith("335")
                else "post" if self.b.post_enabled else "read")
        step = self.feed("cut", "--to-port {} --mode {} --group {} --msgid '{}' --pid {}"
                         .format(self.b.port, mode, GROUPS[0], INTERRUPTED_ID, self.b.pid),
                         name="kill -9 node B mid-{}".format(mode), timeout=180,
                         expect=None)
        after = self.payload(step).get("after_kill", "(no observation)")
        self.facts["kill"] = "mode={} {}".format(mode, after)
        acknowledged = after.startswith(("reply: 235", "reply: 240"))
        self.emit("V0-CRASH-KILL",
                  REFUSED if not acknowledged else ACCEPTED, step.command,
                  "mode={} after the kill: {}".format(mode, after), exit_code=step.rc,
                  limit="a SIGKILL is not a power loss, and this is one cut; the "
                        "enumerated table is tests/campaign/cuts.py. An acknowledgement "
                        "here would be the defect, so 'refused' is the wanted reading"
                        + ("" if mode != "read" else
                           ". The cut landed on an open reader connection, not inside a "
                           "transfer, because node B offers neither transit nor POST"))
        self.b.rejected.append(INTERRUPTED_ID)
        survivor = self.sh("node A survived node B's death",
                           "kill -0 {} 2>/dev/null && echo ALIVE || echo DEAD".format(
                               self.a.pid or 0), expect=None)
        self.emit("V0-CRASH-SURVIVOR",
                  ACCEPTED if "ALIVE" in survivor.output else REFUSED,
                  survivor.command, survivor.first_line, exit_code=survivor.rc,
                  limit="one process killed on one box; this is not a partition")
        recover = self.sh("node B recover after the kill", self.cd(self.fn(
            "--store {} recover".format(self.b.store))), timeout=1800, expect=None)
        self.from_step("V0-CRASH-RECOVER", recover,
                       limit="the real recovery path over the real store directory")
        self.sh("node B status after recovery", self.cd(self.fn(
            "--store {} status".format(self.b.store))), timeout=1800, expect=None)
        worst = None
        for msgid in self.b.accepted:
            one = self.sh("node B still holds {} after recovery".format(msgid),
                          self.cd(self.fn("--store {} inspect --message-id '{}'".format(
                              self.b.store, msgid))), timeout=900, expect=EXIT_OK)
            if one.rc != EXIT_OK and worst is None:
                worst = one
        if not self.b.accepted:
            self.emit("V0-CRASH-ACKNOWLEDGED", NOT_EXERCISED,
                      "run_store.py inspect --message-id ...", "(nothing acknowledged)",
                      blocker="node B acknowledged nothing before the kill, so there "
                              "was nothing for the recovery to preserve")
        else:
            self.emit("V0-CRASH-ACKNOWLEDGED",
                      ACCEPTED if worst is None else exit_verdict(worst.rc),
                      "run_store.py --store <B> inspect --message-id <each of {}>".format(
                          len(self.b.accepted)),
                      "all {} acknowledged Message-IDs re-inspected: {}".format(
                          len(self.b.accepted),
                          "every one exited 0" if worst is None
                          else "{} exited {}".format(worst.name, worst.rc)),
                      exit_code=0 if worst is None else worst.rc,
                      limit="exact Message-ID lookups, not a full comparison of octets")
        interrupted = self.sh("node B does not hold the interrupted {}".format(
            INTERRUPTED_ID), self.cd(self.fn(
                "--store {} inspect --message-id '{}'".format(
                    self.b.store, INTERRUPTED_ID))), timeout=900, expect=EXIT_REFUSED)
        self.from_step("V0-CRASH-INTERRUPTED", interrupted)
        if self.start_node(self.b, tag="after-recovery"):
            reread = self.feed("presence", "--port {} --groups {} --present '{}' "
                               "--absent '{}'".format(
                                   self.b.port, ",".join(GROUPS),
                                   ",".join(self.b.accepted), ",".join(self.b.rejected)),
                               name="reread node B after recovery", expect=None)
            self.from_step("V0-CRASH-RESTART", reread)
        else:
            self.emit("V0-CRASH-RESTART", NOT_EXERCISED,
                      "start node B after the recovery", "(did not reach LISTENING)",
                      blocker="node B did not restart after the recovery; the server "
                              "log tail is in the raw output below")

    def campaign_phase(self):
        if not self.want_campaign:
            self.blocked(("V0-CRASH-CUT-TABLE", "V0-CRASH-CAMPAIGN"),
                         "--no-campaign was given for this run")
            return
        table = self.sh("campaign: the cut table matches the injector", self.cd(
            "python3 -c 'import sys; sys.path.insert(0, \".\"); "
            "from tests.campaign import cuts; cuts.verify_table(); print(\"TABLE OK\", "
            "len(cuts.CUTS))'"), timeout=600, expect=None)
        self.emit("V0-CRASH-CUT-TABLE",
                  ACCEPTED if table.rc == 0 else REFUSED, table.command,
                  table.first_line or "(no output)", exit_code=table.rc,
                  limit="the table is checked against the fault points the host "
                        "declares, not against the crash model")
        run = self.sh("campaign: run the cuts", self.cd(
            "python3 -m tests.campaign.campaign --quick --json {}/campaign.json "
            "2>&1 | tail -30".format(self.run)), timeout=3600, expect=None)
        crashed = traceback_line(run.output)
        if crashed:
            self.emit("V0-CRASH-CAMPAIGN", NOT_EXERCISED, run.command,
                      " | ".join(run.output.strip().splitlines()[-2:]) or "(no output)",
                      exit_code=run.rc,
                      blocker="the campaign harness raised rather than reporting a "
                              "cut: {}. That is a broken Python call site, not a "
                              "refusal; the cuts that ran before it are in the raw "
                              "output".format(crashed),
                      owner="w9/runtime")
            return
        self.emit("V0-CRASH-CAMPAIGN",
                  ACCEPTED if run.rc == 0 else exit_verdict(run.rc), run.command,
                  " | ".join(run.output.strip().splitlines()[-3:]) or "(no output)",
                  exit_code=run.rc, client=CLIENT_LAB,
                  limit="--quick: a subset of the enumerated cuts, each a process "
                        "death, none of them a power loss")

    # -- F-BP --------------------------------------------------------------
    BP_LAB = ("exchange", "refused", "keepalive", "crash", "profile", "replay")
    BP_KEYS = {"exchange": "V0-BP-EXCHANGE", "refused": "V0-BP-REFUSED",
               "keepalive": "V0-BP-KEEPALIVE", "crash": "V0-BP-CRASH",
               "profile": "V0-BP-PROFILE", "replay": "V0-BP-REPLAY"}

    def bp_phase(self):
        # CLAUDE.md, measured 2026-07-15: on hbox every build goes through
        # `swarm-build`, which puts an enforced MemoryMax around it.  `taskset`
        # caps CPU only, and Lean/SBCL codegen is what takes the box down.
        wrapper = ("swarm-build " if self.host.label == "hbox"
                   and self.support.get("swarm-build") == "yes" else "nice -n 10 ")
        build = self.sh("native image for the tcpcl layer",
                        self.cd("FN_ACL2=${FN_ACL2:-$HOME/fn-tools/acl2-8.7/saved_acl2} "
                                + wrapper +
                                "sh tools/build_native_host.sh 2>&1 | tail -20"),
                        timeout=3600, expect=None)
        built = build.rc == 0 and "built build/fn-host" in build.output
        self.emit("V0-BP-IMAGE", ACCEPTED if built else REFUSED, build.command,
                  " | ".join(build.output.strip().splitlines()[-2:]) or "(no output)",
                  exit_code=build.rc,
                  limit="the DTN-only build list; the image is not the served path")
        if not built:
            self.facts["tcpcl"] = "no image: the layer could not be exercised"
            self.blocked([self.BP_KEYS[n] for n in self.BP_LAB],
                         "build/fn-host was not produced on this commit: {}".format(
                             " | ".join(build.output.strip().splitlines()[-2:])),
                         invocation=build.command)
        else:
            lab = self.sh("tcpcl lab", self.cd(
                "python3 tools/tcpcl_lab.py --image build/fn-host --work {}/tcpcl-lab"
                .format(self.deploy)), timeout=1800, expect=None)
            rows = {}
            for line in lab.output.splitlines():
                line = line.strip()
                if line.startswith("{"):
                    try:
                        one = json.loads(line)
                    except ValueError:
                        continue
                    rows[one.get("scenario", "?")] = one
            summary = rows.get("summary", {})
            self.facts["tcpcl"] = "passed={} failed={}".format(
                ",".join(summary.get("passed", [])) or "none",
                ",".join(summary.get("failed", [])) or "none")
            for name in self.BP_LAB:
                key = self.BP_KEYS[name]
                one = rows.get(name)
                if one is None:
                    self.emit(key, NOT_EXERCISED, lab.command, "(no row)",
                              blocker="the lab produced no result for the `{}` scenario"
                                      .format(name))
                    continue
                note = ", ".join("{}={}".format(k, v) for k, v in sorted(one.items())
                                 if k not in ("scenario", "ok"))
                expected = PLAN_BY_KEY[key].expected
                verdict = expected if one.get("ok") else (
                    REFUSED if expected == ACCEPTED else ACCEPTED)
                self.emit(key, verdict, lab.command, note[:500],
                          client=CLIENT_LAB,
                          limit="every assertion is over the event digests the two "
                                "images printed; the lab does not speak TCPCL, and the "
                                "octets it carries are opaque, not BPv7 bundles")
        if self.has("bp-node"):
            self.emit("V0-BP-NODE", NOT_EXERCISED,
                      "python3 tests/bp-dtn7/run_fn_bp_interop.py",
                      "books/bp-node.lisp and tests/bp-dtn7/run_fn_bp_interop.py are "
                      "both on this commit",
                      blocker="the BP node is BUILT -- `books/bp-node.lisp` encodes and "
                              "decodes whole BPv7 bundles and "
                              "`tests/bp-dtn7/run_fn_bp_interop.py` runs fn against "
                              "dtn7-rs both ways -- but this matrix does not run it: "
                              "it needs the pinned dtn7-rs build beside the native "
                              "image, which is a second harness with its own box "
                              "requirements. Run it and the row becomes an outcome",
                      owner="w9/dtn-2")
        else:
            self.emit("V0-BP-NODE", NOT_BUILT,
                      "tools/run_bp_ingress.py against the convergence layer",
                      "(not run)",
                      blocker="no BP node is wired behind the TCPCLv4 layer on this "
                              "commit: the layer transfers opaque octets and nothing "
                              "parses a bundle out of them into an fn article "
                              "(planning/evidence/tcpcl-dtn-w9-2026-09-20.md)",
                      owner="w9/dtn-2")

    # -- F-STX -------------------------------------------------------------
    STX_KEYS = ("V0-STX-SIGN", "V0-STX-ATTACH", "V0-STX-CROSS", "V0-STX-VERIFY",
                "V0-STX-UNVERIFIED", "V0-STX-READER")

    @staticmethod
    def statement_verdict(rc) -> str:
        """`fn statement verify`'s own vocabulary (bin/fn, `statement --help`).

        0 verified, 3 unverified, 4 absent, 2 no verdict.  `3` is NOT D13's
        uncertain here: an unverified statement is a decision, and the gate
        records that overload rather than translating it away.
        """
        return {0: ACCEPTED, 3: REFUSED, 4: REFUSED, 2: UNCERTAIN}.get(rc, UNCERTAIN)

    def statement_prepare(self):
        """Sign the article that will be posted, before it is posted.

        `fn-stx-payload-for` (books/stx-carrier.lisp:541) projects the
        AUTHORED SOURCE out of the received article for a `:article`
        statement, so the octets that are signed have to be the article's
        own, not a separate payload file: signing anything else draws
        `unverified ref-mismatch` from a receiver that is working correctly.
        Measured on persvati 2026-09-20: signing the article file and
        attaching the field to that same file verifies against a keyring
        holding the creator and its public key.
        """
        seed_file = "{}/seed.hex".format(self.deploy)
        base = "{}/statement.article".format(self.deploy)
        field = "{}/statement.field".format(self.deploy)
        self.statement_file = None
        self.push_file(article(STX["a"], GROUPS[0], "a carried statement",
                               "A statement carried between two fn nodes."), base)
        sign = self.sh("statement sign", self.cd(
            "python3 bin/fn --config {}/fn.toml statement sign --payload {} --seed {} "
            "--ed25519 > {}".format(self.a.dir, base, seed_file, field)),
            timeout=1800, expect=None)
        self.from_step("V0-STX-SIGN", sign,
                       limit="the signing realiser on this tree is the toy one of "
                             "tests/acl2/crypto-seam-tests.lisp, and `--ed25519` prints "
                             "a real signature that is NOT attached (D09); this row is "
                             "about the field's production, not about cryptography")
        if sign.rc != 0:
            self.blocked(self.STX_KEYS,
                         "`fn statement sign` exited {} ({}), so no FN-Statement field "
                         "existed for the rows below".format(sign.rc, sign.first_line),
                         invocation=sign.command)
            return
        signed = "{}/statement.signed".format(self.deploy)
        attach = self.sh("statement attach", self.cd(
            "python3 bin/fn --config {}/fn.toml statement attach --field {} "
            "--article {} > {}".format(self.a.dir, field, base, signed)),
            timeout=1800, expect=None)
        self.from_step("V0-STX-ATTACH", attach,
                       limit="one field line prepended to one article")
        if attach.rc == 0:
            self.statement_file = signed

    def statements(self):
        signed = getattr(self, "statement_file", None)
        if signed is None:
            self.blocked(self.STX_KEYS,
                         "no signed article was produced earlier in this run, so there "
                         "is nothing to verify")
            return
        if "V0-STX-CROSS" in self.emitted:
            pass
        elif not self.b.port:
            self.emit("V0-STX-CROSS", NOT_EXERCISED, "feed.py presence", "(no listener)",
                      blocker=self.node_blocker(self.b))
        else:
            self.statement_crossed()
        keyring = "{}/keyring".format(self.deploy)
        pair = getattr(self, "keyring_line", "")
        self.push_file((pair + "\n") if pair else "", keyring)
        verify = self.sh("statement verify on node B's copy", self.cd(
            "python3 bin/fn --config {}/fn.toml statement verify --article {} "
            "--keyring {}".format(self.b.dir, signed, keyring)), timeout=900, expect=None)
        self.emit("V0-STX-VERIFY", self.statement_verdict(verify.rc), verify.command,
                  "rc={} ({}) {}".format(verify.rc,
                                         {0: "verified", 2: "no verdict",
                                          3: "unverified", 4: "absent"}.get(
                                              verify.rc, "outside the vocabulary"),
                                         verify.first_line),
                  exit_code=verify.rc,
                  limit="the octets verified are the signed file on the box, not what "
                        "node B served: the transit row above says whether the article "
                        "reached B at all. The keyring holds {}; the realiser behind "
                        "the signature is "
                        "the toy one of tests/acl2/crypto-seam-tests.lisp, so a "
                        "`verified` here is the node's own verdict function agreeing "
                        "with its own signer, not a cryptographic claim".format(
                            "the creator and its public key" if pair
                            else "nothing, because `fn principal new` gave no pair"))
        tampered = "{}/statement.tampered".format(self.deploy)
        self.sh("statement tamper", self.cd(
            "sed 's/A statement carried/A statement altered/' {} > {}".format(
                signed, tampered)), expect=None)
        bad = self.sh("statement verify on the tampered copy", self.cd(
            "python3 bin/fn --config {}/fn.toml statement verify --article {} "
            "--keyring {}".format(self.b.dir, tampered, keyring)),
            timeout=900, expect=None)
        self.emit("V0-STX-UNVERIFIED", self.statement_verdict(bad.rc), bad.command,
                  "rc={} {}".format(bad.rc, bad.first_line), exit_code=bad.rc,
                  limit="one tampered octet range; the row asserts that the verdict is "
                        "a decision (unverified or absent) and not silence")
        if verify.rc == 3 or bad.rc == 3:
            self.limitation(
                None,
                "`fn statement verify` uses exit 3 for `unverified`, which is D13's "
                "uncertain code everywhere else on the operator surface "
                "(docs/operator.md). The matrix reads it with the statement "
                "vocabulary and records the overload rather than hiding it.")
        self.emit("V0-STX-READER", NOT_BUILT,
                  "HDR :fn-verified over the served path", "(not run)",
                  blocker="the reader exposes no `:fn-verified` header on this commit: "
                          "books/nntp-responses.lisp carries the seam and the board "
                          "records it as deliberately not half-wired (SUB-006)",
                  owner="w10/provenance")

    def statement_crossed(self):
        offer = self.feed(
            "relay",
            "--from-port {} --to-port {} --msgid '{}' --group {} --loop-msgid '{}' "
            "--loop-identity {}".format(
                self.a.port, self.b.port, STX["a"], GROUPS[0],
                "<statement-loop@example.invalid>", self.b.path_identity),
            name="statement: offer the statement-bearing article from A to B",
            expect=None)
        reply = self.payload(offer).get("offer", "")
        if not reply or unsupported(reply) or not_permitted(reply):
            self.emit("V0-STX-CROSS", NOT_EXERCISED, offer.command,
                      "IHAVE answered '{}'".format(reply or "nothing"),
                      blocker="the statement-bearing article could not be offered to "
                              "node B: `IHAVE` answered '{}'. The transit rows above "
                              "carry the same blocker".format(reply or "nothing"))
            return
        crossed = self.feed("presence", "--port {} --groups {} --present '{}'".format(
            self.b.port, GROUPS[0], STX["a"]),
            name="statement: node B serves the statement-bearing article", expect=None)
        result = self.payload(crossed)
        status = result.get("present", {}).get(STX["a"], "(no reply)")
        self.from_reply("V0-STX-CROSS", status, crossed.command,
                        limit="the article node A holds for this row was posted with "
                              "its FN-Statement field already on it, so what crosses is "
                              "the field; whether the far side's octets are identical is "
                              "the transit row, not this one")

    # -- F-MEDIA -----------------------------------------------------------
    def media(self):
        probe = self.sh("media export usage", self.cd(
            "python3 tools/media.py export --help 2>&1 | head -20"), expect=None)
        blocker = (
            "`tools/media.py export` requires a `--bundle <id>=<path>` and a "
            "`--bp-bundle <id>=<path>` for every carried identity, because the "
            "importing node reads the identity and the expiry out of the BPv7 bundle "
            "octets rather than deciding them locally. No BPv7 bundle is produced "
            "anywhere in this run: the TCPCLv4 layer carries opaque octets and no BP "
            "node is wired behind it, so there is nothing to put in a volume")
        for key in ("V0-MEDIA-EXPORT", "V0-MEDIA-VERIFY", "V0-MEDIA-IMPORT"):
            self.emit(key, NOT_EXERCISED, probe.command, probe.first_line or "(no output)",
                      blocker=blocker, owner="w9/dtn-2")

    # -- F-SCALE, F-INN, F-CLIENT ------------------------------------------
    def scale(self):
        if not self.want_scale:
            self.emit("V0-SCALE-CEILING", NOT_EXERCISED,
                      "python3 tools/scale_gate.py {} --host {}".format(
                          self.rev, self.host.label),
                      "(not run: --scale was not given)",
                      blocker="the scale gate grows a store by doubling and takes an "
                              "hour or more; it is a separate harness and this run did "
                              "not take that budget. Quote its numbers from "
                              "planning/evidence/scale-0e9a421-2026-09-20.md WITH their "
                              "scope (one box, that payload grid, those ceilings), "
                              "never as a bound")
            return
        step = self.sh("scale gate", self.cd(
            "python3 tools/scale_gate.py {} --host {} 2>&1 | tail -20".format(
                self.rev, self.host.label)), timeout=4 * 3600, expect=None)
        self.emit("V0-SCALE-CEILING", exit_verdict(step.rc), step.command,
                  " | ".join(step.output.strip().splitlines()[-3:]) or "(no output)",
                  exit_code=step.rc, client=CLIENT_LAB,
                  limit="a measured ceiling on one box with one payload grid; it is "
                        "not a bound and not a proof")

    def inn_not_run(self, invocation: str, observed: str, blocker: str):
        for key in INN_ROW_KEYS:
            self.emit(key, NOT_EXERCISED, invocation, observed, blocker=blocker)

    def inn_command(self, evidence: Path) -> list:
        """tools/inn_lab.py, run from THIS checkout against this run's host.

        It runs here and not on the execution host: the lab ships its own
        tree with `git archive`, which needs a repository, and the deployed
        tree is an archive.  It drives the host over ssh exactly as this
        gate does."""
        return [sys.executable, str(self.repo / "tools/inn_lab.py"), self.commit,
                "--host", self.host.label, "--native-image", self.native_image,
                "--evidence", str(evidence)]

    def inn(self):
        invocation = "python3 tools/inn_lab.py {} --host {} --native-image {}".format(
            self.rev, self.host.label, self.native_image or "IMAGE")
        if not self.want_inn:
            self.inn_not_run(invocation, "(not run: --inn was not given)",
                             "the INN install is a lab that lives on hbox at "
                             "/tank/fn/inn/2.7.4 and is not shipped, and the lab takes "
                             "its own ports and a few minutes; this run did not ask for "
                             "it (--inn). The last recorded run is "
                             "planning/evidence/inn-lab-dabebb84-2026-09-22.md")
            return
        if self.backend != NATIVE_BACKEND or not self.native_image:
            self.inn_not_run(invocation, "(not run: no native image)",
                             "the INN lab's fn side is the native image or the lab does "
                             "not run (D07); this run's backend is {}".format(self.backend))
            return
        if not isinstance(self.host, deploy_gate.SshHost):
            self.inn_not_run(invocation, "(not run: {} is not a remote host)".format(
                self.host.label), "the INN lab needs the INN install on a real host")
            return
        directory = (self.repo / self.evidence_name).parent
        evidence = directory / "inn-lab.md"
        command = self.inn_command(evidence)
        clock = time.monotonic()
        done = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              timeout=3600)
        output = done.stdout.decode("utf-8", "replace")
        self.steps.append(Step("inn lab", " ".join(shlex.quote(one) for one in command),
                               done.returncode, output, time.monotonic() - clock,
                               "", None))
        sidecar = evidence.with_suffix(".findings.json")
        try:
            findings = json.loads(sidecar.read_text())
        except (OSError, ValueError) as error:
            self.inn_not_run(" ".join(command), output.strip().splitlines()[-1:] and
                             output.strip().splitlines()[-1] or "(no output)",
                             "the lab wrote no findings ({}): exit {}".format(
                                 error, done.returncode))
            return
        for key, verdict, observed, blocker in inn_rows(findings):
            self.emit(key, verdict, " ".join(command), observed,
                      exit_code=done.returncode if key == "V0-INN-INTEROP" else None,
                      log=str(evidence.relative_to(self.repo))
                      if evidence.is_relative_to(self.repo) else str(evidence),
                      blocker=blocker, client="InterNetNews",
                      limit="one INN version on one box over loopback, through the "
                            "lab's byte-transparent relay; not a Usenet conformance audit")

    def served_group(self) -> str:
        """The group both nodes serve on this backend."""
        return self.native_group if self.backend == NATIVE_BACKEND else GROUPS[0]

    def nntplib_interpreter(self) -> str:
        """An interpreter on the execution host whose stdlib still has nntplib.

        `probe_tree` finds one on the development backend.  The native slice
        does not run that probe -- it consumes an explicitly named saved
        image and asks the deployed tree nothing -- so the same question is
        asked here, over the versioned interpreters `preflight` found plus
        `python3` itself: on a box whose `python3` IS 3.12 the versioned name
        need not exist, and PEP 594 removed nntplib in 3.13.
        """
        if self.support.get("nntplib"):
            return self.support["nntplib"]
        candidates = list(getattr(self, "alt_pythons", [])) + ["python3"]
        step = self.sh("nntplib interpreter", " ".join(
            ["for p in"] + candidates
            + ["; do command -v $p >/dev/null 2>&1 && $p -c 'import nntplib' 2>/dev/null",
               "&& { echo USE $p; exit 0; }; done; echo NONE"]), expect=None)
        match = re.search(r"^USE (\S+)", step.output, re.M)
        self.support["nntplib"] = match.group(1) if match else ""
        return self.support["nntplib"]

    def has_client(self, name: str) -> bool:
        """Is this newsreader on the execution host?

        `probe_tree` records it as yes/no; `preflight` records the path or
        ABSENT for every backend, and the native slice runs only the second.
        """
        if name in self.support:
            return self.support[name] == "yes"
        return getattr(self, "clients", {}).get(name, "ABSENT") != "ABSENT"

    def independent_clients(self):
        """The one observation in this matrix that fn did not make itself.

        NOT named `clients`: `DeployGate.preflight` assigns `self.clients`
        the dict of newsreader binaries it found on the box, and a method of
        that name is replaced by it on the instance -- which is how the
        fifth run ended with "TypeError: 'dict' object is not callable" and
        three client rows backfilled.

        Every other row is fn's CLI, fn's harness or this file's socket
        driver. A feature that only fn's own client has seen is a weaker
        claim than "usable between two peered servers" reads, so this runs
        the Python standard library's own NNTP implementation against both
        nodes and the rows it produces are the ones marked `independent`.
        """
        interpreter = self.nntplib_interpreter()
        group = self.served_group()
        user, secret = self.credential()
        if not interpreter:
            self.blocked(("V0-CLIENT-NNTPLIB",),
                         "no interpreter on {} has a stdlib nntplib: PEP 594 removed "
                         "it in Python 3.13 and the box runs {}. `uv python install "
                         "3.12` puts one on the box in seconds and the probe finds it"
                         .format(self.host.label,
                                 self.facts.get("python3", "python3")),
                         invocation="<interpreter> independent.py")
        else:
            self.push_file(INDEPENDENT_DRIVER, "{}/independent.py".format(self.run),
                           mode="755")
            for node in self.nodes:
                if not node.port:
                    self.emit("V0-CLIENT-NNTPLIB", NOT_EXERCISED,
                              "{} independent.py".format(interpreter), "(no listener)",
                              node=node.name, blocker=self.node_blocker(node))
                    continue
                step = self.sh("independent nntplib client on node {}".format(
                    node.upper), self.cd(
                        "{} {}/independent.py --port {} --group {} --msgid '{}' "
                        "--absent '{}' --user {} --secret {}".format(
                            interpreter, self.run, node.port, shlex.quote(group),
                            node.accepted[0] if node.accepted else ART[node.name],
                            ABSENT_ID, shlex.quote(user), shlex.quote(secret))),
                    timeout=600, expect=None)
                result = self.payload(step)
                self.emit("V0-CLIENT-NNTPLIB", exit_verdict(step.rc), step.command,
                          "nntplib {} drove {}; login={} authinfo-advertised={} "
                          "group={} article_lines={} absent={}".format(
                              result.get("python", "?"),
                              ", ".join(result.get("commands", [])) or "nothing",
                              result.get("login", "(not attempted)"),
                              result.get("authinfo_advertised"),
                              result.get("group"), result.get("article_lines"),
                              str(result.get("absent"))[:60])
                          if result else (step.first_line or "(no output)"),
                          node=node.name, exit_code=step.rc,
                          client="stdlib nntplib on {}".format(interpreter),
                          limit="one client library, and it reads: nothing here is "
                                "posted or fed by a foreign client. Its framing, "
                                "folding and response parsing are the standard "
                                "library's, not fn's, which is the point of the row")
        if not self.has_client("slrn"):
            self.emit("V0-CLIENT-SLRN", NOT_EXERCISED, "slrn -h <host> -p <port>",
                      "(slrn is not installed)",
                      blocker="slrn is not installed on {} (nor on hbox, measured "
                              "2026-09-20); tests/interop_slrn.py has never run against "
                              "an fn node".format(self.host.label))
            return
        step = self.sh("slrn client", self.cd(
            "python3 tests/interop_slrn.py --port {} --group {} 2>&1 | tail -20".format(
                self.a.port, shlex.quote(group))), timeout=900, expect=None)
        self.emit("V0-CLIENT-SLRN", exit_verdict(step.rc), step.command,
                  step.first_line or "(no output)", exit_code=step.rc,
                  client="slrn", limit="one newsreader against node A only")

    # -- the server entry point --------------------------------------------
    def server_candidates(self, node: NodeSpec):
        """Every entry point this commit might serve from, best first.

        `bin/fn run` is the service an operator runs, `tools/run_owner.py` is
        what it wraps, and `tools/run_reader.py` is the read-only path with no
        POST and no transit.  Which one starts is itself a v0 row, and the
        ones that did not start are the blocker the later rows cite.
        """
        if self.backend == NATIVE_BACKEND:
            # Native evidence never falls through to a Python server.  The
            # packaged wrapper is part of the subject; raw `--fn owner` is a
            # diagnostic entry and is deliberately absent here.
            return [(NATIVE_BACKEND, self.native_operator(node, "run"))]
        if self.server_template:
            return [("custom", self.server_template.format(
                store=node.store, run=node.dir, node=node.name))]
        out = []
        if self.has("fn-run") and node.name in getattr(self, "configured", ()):
            out.append(("fn", "python3 bin/fn --config {dir}/fn.toml run "
                              "--control {dir}/control.sock "
                              "--max-connections {n}".format(
                                  dir=node.dir, n=MAX_CONNECTIONS)))
        port = getattr(node, "assigned_port", 0)
        out.append(("owner", "python3 tools/run_owner.py --store {} --port {} "
                             "--control {}/control.sock --max-connections {}".format(
                                 node.store, port, node.dir, MAX_CONNECTIONS)))
        reader = "python3 tools/run_reader.py --store {} --port {}".format(
            node.store, port)
        if self.has("reader-post"):
            reader += " --post"
        out.append(("reader", reader))
        return out

    def start_node(self, node: NodeSpec, tag="main") -> bool:
        attempts = []
        started = False
        for kind, command in self.server_candidates(node):
            started = self.start_server("node {} ({})".format(node.upper, kind),
                                        command, "{}-{}".format(node.name, tag),
                                        run=node.dir)
            last = self.steps[-1]
            attempts.append((kind, command, started,
                             " | ".join(last.output.strip().splitlines()[-2:])))
            if started:
                self.commands[node.name] = (kind, command)
                self.selected = kind
                break
        if tag == "main":
            node.start_attempts = attempts
            if started:
                kind = attempts[-1][0]
                skipped = [a for a in attempts[:-1]]
                self.emit("V0-NODE-START", ACCEPTED, attempts[-1][1],
                          "`{}` reached LISTENING{}".format(
                              kind,
                              "" if not skipped else
                              "; {} did not: {}".format(
                                  ", ".join(a[0] for a in skipped),
                                  " // ".join(a[3][:160] for a in skipped))),
                          node=node.name,
                          limit="the entry point that started is `{}`; every served row "
                                "for this node is about that process, not about the "
                                "ones above it in the list, which was given "
                                "--max-connections {}".format(kind, MAX_CONNECTIONS))
            else:
                invocation = " ;; ".join(a[1] for a in attempts)
                observed = "; ".join(
                    "{}: {}".format(a[0], a[3][:200]) for a in attempts)
                if self.backend == NATIVE_BACKEND:
                    self.emit(
                        "V0-NODE-START", NOT_EXERCISED, invocation, observed,
                        node=node.name,
                        blocker="the packaged native process did not reach LISTENING; "
                                "a host/configuration failure is not a node refusal",
                        limit="the packaged operator was the only entry point tried")
                else:
                    self.emit("V0-NODE-START", REFUSED, invocation, observed,
                              node=node.name,
                              limit="every entry point this commit has was tried in order")
        if not started:
            return False
        node.port = self.port
        node.kind = self.selected
        node.post_enabled = ("--post" in self.commands[node.name][1]
                             or self.selected.startswith(("owner", "fn", NATIVE_BACKEND)))
        node.pid = self.sh("node {} pid".format(node.upper),
                           "cat {}/server.pid".format(node.dir)).output.strip()
        self.facts["node {}".format(node.name)] = "{} on port {} ({}), store {}".format(
            self.selected, node.port, tag, node.store)
        self.facts["server entry point"] = self.selected
        return True

    def alive(self, node: NodeSpec, tag="main") -> bool:
        """Is this node's server still the process that reached LISTENING?

        A server that dies in the middle of a run makes every later row a
        connection error, and a connection error is not a verdict about the
        feature the row is named for. Asking before each phase lets the
        matrix say the death once, with the log that explains it, and record
        the rest as not-exercised against that.
        """
        if not node.pid:
            return False
        step = self.sh("node {} server is alive".format(node.upper),
                       "kill -0 {} 2>/dev/null && echo ALIVE || echo DEAD".format(
                           node.pid), expect=None)
        if "ALIVE" in step.output:
            return True
        if node.name not in self.dead:
            tail = self.sh("node {} server log after it died".format(node.upper),
                           "tail -25 {}/server-{}-{}.log 2>/dev/null || echo NO-LOG"
                           .format(node.dir, node.name, tag), expect=None)
            lines = [x for x in tail.output.strip().splitlines() if x.strip()]
            self.dead[node.name] = " | ".join(lines[-6:]) or "(no log)"
            self.limitation(
                None,
                "node {}'s server process DIED during this run, after it had reached "
                "LISTENING. Every row below that needed a socket on it is "
                "not-exercised against that death, not against the feature. Its last "
                "log lines: {}".format(node.upper, self.dead[node.name]))
        return False

    def require_live(self, node: NodeSpec, keys, nodes=None, directions=None) -> bool:
        if self.alive(node):
            return True
        blocker = ("node {}'s server died earlier in this run: {}".format(
            node.upper, self.dead.get(node.name, "no log")))
        extra = {}
        if nodes is not None:
            extra["nodes"] = nodes
        if directions is not None:
            extra["directions"] = directions
        self.blocked(keys, blocker, invocation="(the server was gone)", **extra)
        return False

    def node_blocker(self, node: NodeSpec) -> str:
        attempts = getattr(node, "start_attempts", [])
        uncert = self.uncertified("owner", "served", "peer-inbound", "peer-config",
                                  "nntp-auth")
        return ("node {} has no listener: {}{}".format(
            node.upper,
            "; ".join("`{}` -> {}".format(a[0], a[3][:200]) for a in attempts)
            or "no entry point was tried",
            "" if not uncert else
            ". Uncertified in the deploy tree: books/" + ", books/".join(uncert)))

    AUTH_KEYS = ("V0-AUTH-ADVERTISED", "V0-AUTH-GATED", "V0-AUTH-LOGIN",
                 "V0-AUTH-WITHDRAWN", "V0-AUTH-POST", "V0-AUTH-WRONG")
    POST_KEYS = ("V0-POST-OPEN", "V0-POST-COMMIT", "V0-POST-READBACK",
                 "V0-POST-FRESH", "V0-POST-DUPLICATE", "V0-POST-CLOCK",
                 "V0-POST-FROM-MAILBOX")
    CRASH_KEYS = ("V0-CRASH-KILL", "V0-CRASH-SURVIVOR", "V0-CRASH-RECOVER",
                  "V0-CRASH-ACKNOWLEDGED", "V0-CRASH-INTERRUPTED",
                  "V0-CRASH-RESTART")
    NODE_SOCKET_KEYS = ("V0-GROUP-SERVED", "V0-POST-OPEN", "V0-POST-COMMIT",
                        "V0-POST-READBACK", "V0-POST-FRESH", "V0-POST-DUPLICATE",
                        "V0-POST-FROM-MAILBOX",
                        "V0-AUTH-ADVERTISED", "V0-AUTH-GATED", "V0-AUTH-LOGIN",
                        "V0-AUTH-WITHDRAWN", "V0-AUTH-POST", "V0-AUTH-WRONG",
                        "V0-PIN-DISPATCHED", "V0-PIN-ADVERTISED",
                        "V0-TRANSIT-INDEPENDENT")
    PAIR_KEYS = ("V0-POST-CONCURRENT", "V0-CFG-LIVE", "V0-CFG-LIVE-REFUSE",
                 "V0-CRASH-CHECKPOINT", "V0-CRASH-KILL", "V0-CRASH-SURVIVOR",
                 "V0-CRASH-RECOVER", "V0-CRASH-ACKNOWLEDGED",
                 "V0-CRASH-INTERRUPTED", "V0-CRASH-RESTART",
                 "V0-CLIENT-NNTPLIB", "V0-CLIENT-SLRN", "V0-STX-CROSS")

    def probe_native_subject(self):
        """Identify the exact packaged image without claiming its provenance.

        The source revision and image digest remain separate facts.  A digest
        does not prove that an externally supplied image came from this Git
        tree; it only makes the executable subject unambiguous.
        """
        image = shlex.quote(self.native_image)
        step = self.sh("native packaged operator subject", self.cd(r"""
image={image}
wrapper=packaging/fn-native
runtime={runtime}
test -x "$image" || {{ echo "NATIVE-IMAGE-MISSING $image"; exit 4; }}
test -x "$wrapper" || {{ echo NATIVE-WRAPPER-MISSING; exit 4; }}
test -s "$image.core" || {{ echo NATIVE-CORE-MISSING $image.core; exit 4; }}
if command -v sha256sum >/dev/null 2>&1; then
  digest() {{ sha256sum "$1" | awk '{{print $1}}'; }}
else
  digest() {{ shasum -a 256 "$1" | awk '{{print $1}}'; }}
fi
echo "NATIVE-LAUNCHER-DIGEST $(digest "$wrapper")"
echo "NATIVE-IMAGE-DIGEST $(digest "$image")"
if [ -n "$runtime" ] && [ -x "$runtime" ]; then
  echo "NATIVE-RUNTIME-DIGEST $(digest "$runtime")"
else
  echo "NATIVE-RUNTIME-DIGEST unmeasured"
fi
echo "NATIVE-CORE-DIGEST $(digest "$image.core")"
FN_NATIVE_HOST="$image" packaging/fn-native operator /not-opened help run
""".format(image=image, runtime=shlex.quote(self.native_runtime or ""))), timeout=300, expect=None)
        markers = {line.split(" ", 1)[0]: line.split(" ", 1)[1]
                   for line in step.output.splitlines()
                   if line.startswith("NATIVE-") and " " in line}
        if step.rc != 0 or not all(key in markers for key in (
                "NATIVE-LAUNCHER-DIGEST", "NATIVE-IMAGE-DIGEST", "NATIVE-RUNTIME-DIGEST",
                "NATIVE-CORE-DIGEST")):
            raise GateError("the packaged native subject did not execute: rc={} {}"
                            .format(step.rc, step.first_line or "no output"))
        self.image_identity = (
            "launcher sha256={}; image sha256={}; declared runtime={}; sidecar core "
            "sha256={} (static only before a live-owner witness); source correspondence "
            "unestablished".format(
                markers["NATIVE-LAUNCHER-DIGEST"], markers["NATIVE-IMAGE-DIGEST"],
                markers["NATIVE-RUNTIME-DIGEST"],
                markers["NATIVE-CORE-DIGEST"]))
        self.facts["execution backend"] = self.backend
        self.facts["execution source"] = self.rev
        self.facts["execution image"] = self.image_identity
        self.facts["certificates"] = (
            "not acquired by this slice; it consumes the explicitly named saved image")
        return step

    def native_peering_suite(self):
        """Run the existing public two-node witness and map only its observations."""
        image = shlex.quote(self.native_image)
        source = shlex.quote(self.native_image_source or "")
        step = self.sh("native public peering/restart witness", self.cd(r"""
image={image}
digest() {{
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{{print $1}}'
  else shasum -a 256 "$1" | awk '{{print $1}}'; fi
}}
launcher_before=$(digest packaging/fn-native)
runtime_before=$(digest "$image")
core_before=$(digest "$image.core")
runtime_path={runtime}
test -x "$runtime_path" || exit 4
runtime_expected=$(digest "$runtime_path")
echo "NATIVE-PEERING-EXPECTED-RUNTIME $runtime_expected"
echo "NATIVE-PEERING-EXPECTED-CORE $core_before"
FN_NATIVE_HOST="$image" FN_NATIVE_IMAGE_SOURCE_SHA={source} \
FN_NATIVE_LAUNCHER_SHA256="$runtime_before" FN_NATIVE_CORE_SHA256="$core_before" \
FN_NATIVE_RUNTIME_SHA256="$runtime_expected" \
  python3 -m unittest \
    tests.test_native_peering.NativePeeringTests.test_public_native_nodes_exchange_both_ways_and_suppress_duplicate \
    tests.test_native_peering.NativePeeringTests.test_durable_feed_requeues_after_source_process_death -v
rc=$?
launcher_after=$(digest packaging/fn-native)
runtime_after=$(digest "$image")
core_after=$(digest "$image.core")
test "$launcher_before" = "$launcher_after" && test "$runtime_before" = "$runtime_after" \
  && test "$core_before" = "$core_after" || exit 4
exit "$rc"
""".format(image=image, source=source,
             runtime=shlex.quote(self.native_runtime or ""))), timeout=900, expect=None)
        witnesses = []
        for line in step.output.splitlines():
            if line.startswith("NATIVE-PEERING-WITNESS "):
                try:
                    witnesses.append(json.loads(line.split(" ", 1)[1]))
                except json.JSONDecodeError:
                    pass
        transit = next((one for one in witnesses if one.get("kind") == "transit-and-feed"), None)
        restart = next((one for one in witnesses if one.get("kind") == "requeue-restart"), None)
        expected = {}
        for line in step.output.splitlines():
            if line.startswith("NATIVE-PEERING-EXPECTED-") and " " in line:
                key, value = line.split(" ", 1)
                expected[key.rsplit("-", 1)[-1].lower()] = value.strip()
        observed = "witnesses={} rc={}".format(len(witnesses), step.rc)
        if step.rc != 0 or transit is None or restart is None:
            self.blocked(self.TRANSIT_KEYS + self.FEED_KEYS,
                         "the native public witness did not produce both structured "
                         "transit/feed and requeue/restart observations ({})"
                         .format(observed), invocation=step.command)
            return
        digest = re.compile(r"[0-9A-Fa-f]{64}\Z")
        expected_runtime, expected_core = expected.get("runtime"), expected.get("core")
        required_identities = ((transit, ("a", "b")),
                               (restart, ("restart-a", "restart-b")))
        identities_valid = (isinstance(expected_runtime, str)
                            and isinstance(expected_core, str)
                            and digest.fullmatch(expected_runtime) is not None
                            and digest.fullmatch(expected_core) is not None)
        if identities_valid:
            for witness, roles in required_identities:
                identities = witness.get("identity")
                if not isinstance(identities, dict):
                    identities_valid = False
                    break
                for role in roles:
                    identity = identities.get(role)
                    if not (isinstance(identity, dict)
                            and identity.get("status") == "observed"
                            and identity.get("runtime_sha256") == expected_runtime
                            and identity.get("core_sha256") == expected_core):
                        identities_valid = False
                        break
                if not identities_valid:
                    break
        if not identities_valid:
            self.blocked(self.TRANSIT_KEYS + self.FEED_KEYS,
                         "the native witness did not confirm each required live owner "
                         "runtime/core against nonempty SHA-256 expected digests ({})"
                         .format(observed),
                         invocation=step.command)
            return
        self.image_identity = (
            "{}; live owners observed via /proc runtime sha256={} and core sha256={}"
            .format(self.image_identity, expected_runtime, expected_core))
        for way in ("ab", "ba"):
            fact = transit.get("transit", {}).get(way, {})
            if not (fact.get("offer") == "335" and fact.get("transfer") == "235"
                    and fact.get("identical") is True and fact.get("duplicate") == "435"):
                self.blocked(self.TRANSIT_KEYS, "malformed native {} transit witness {}"
                             .format(way, fact), directions=(way,), invocation=step.command)
                continue
            self.emit_once("V0-TRANSIT-OFFER", ACCEPTED, step.command, json.dumps(fact),
                      direction=way, client=CLIENT_DRIVER,
                      limit="tests.test_native_peering sent IHAVE and observed 335")
            self.emit_once("V0-TRANSIT-TRANSFER", ACCEPTED, step.command, json.dumps(fact),
                      direction=way, client=CLIENT_DRIVER,
                      limit="the peer accepted the transferred RFC 3977 block with 235")
            self.emit_once("V0-TRANSIT-IDENTICAL", ACCEPTED, step.command, json.dumps(fact),
                      direction=way, client=CLIENT_DRIVER,
                      limit="the target-served article octets equal the sent block")
            self.emit_once("V0-TRANSIT-DUPLICATE", REFUSED, step.command, json.dumps(fact),
                      direction=way, client=CLIENT_DRIVER,
                      limit="a repeated IHAVE received 435")
        self.blocked(("V0-TRANSIT-MODE-STREAM", "V0-TRANSIT-LOOP",
                      "V0-TRANSIT-LOOP-ABSENT", "V0-TRANSIT-CHECK-FRESH",
                      "V0-TRANSIT-TAKETHIS", "V0-TRANSIT-CHECK-DUP",
                      "V0-TRANSIT-TAKETHIS-DUP"),
                     "the shared native witness does not drive this transit command "
                     "or loop/error case", invocation=step.command)
        feed = transit.get("feed", {})
        if (restart.get("journal") is True and restart.get("source_killed") is True
                and restart.get("source_restarted") is True
                and restart.get("target_identical") is True
                and all(feed.get(way, {}).get("identical") is True for way in ("ab", "ba"))):
            self.emit_once("V0-FEED-QUEUE", ACCEPTED, step.command, json.dumps(restart),
                      client=CLIENT_DRIVER, limit="the restart witness found FNFD intent")
            self.emit_once("V0-FEED-OFFER", ACCEPTED, step.command, json.dumps(feed),
                      client=CLIENT_DRIVER, limit="the public owner delivered both directions")
            self.emit_once("V0-FEED-JOURNAL", ACCEPTED, step.command, json.dumps(restart),
                      client=CLIENT_DRIVER, limit="intent survived source death and restart")
        else:
            self.blocked(("V0-FEED-QUEUE", "V0-FEED-OFFER", "V0-FEED-JOURNAL"),
                         "malformed native feed/restart witness {} {}".format(feed, restart),
                         invocation=step.command)
        self.blocked(("V0-FEED-ONCE",),
                     "435 answers a manually opened inbound IHAVE; this witness does not "
                     "observe the owner queue after acknowledgement", invocation=step.command)

    PROTECTED_KEYS = ("V0-TRANSIT-TLS", "V0-TRANSIT-AUTHINFO",
                      "V0-TRANSIT-TLS-WRONG-ANCHOR", "V0-TRANSIT-AUTHINFO-WRONG")
    PROTECTED_TESTS = (
        "tests.test_native_protected_peering.NativeProtectedPeeringTests."
        "test_reciprocal_starttls_authinfo_transfer_and_reconnect",
        "tests.test_native_protected_peering.NativeProtectedPeeringTests."
        "test_bad_outbound_password_yields_authenticated_430_observation",
        "tests.test_native_protected_peering.NativeProtectedPeeringTests."
        "test_untrusted_certificate_yields_430_and_feed_journal_evidence")

    def native_protected_peering_suite(self):
        """The owner's feed over STARTTLS and AUTHINFO, both ways, and its refusals.

        tests/test_native_protected_peering stands up two saved-image owners
        of its own with certificates, enrolled principals and credential
        profiles, and prints one `NATIVE-PROTECTED-WITNESS` line per test
        whose assertions passed.  Only those lines become rows; an exit code
        without them, or a line whose live owner is not the image this run
        names, is a blocker.
        """
        image = shlex.quote(self.native_image)
        step = self.sh("native protected peering witness", self.cd(r"""
image={image}
digest() {{
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{{print $1}}'
  else shasum -a 256 "$1" | awk '{{print $1}}'; fi
}}
runtime_path={runtime}
test -x "$runtime_path" || exit 4
runtime_expected=$(digest "$runtime_path")
core_before=$(digest "$image.core")
echo "NATIVE-PROTECTED-EXPECTED-RUNTIME $runtime_expected"
echo "NATIVE-PROTECTED-EXPECTED-CORE $core_before"
FN_NATIVE_HOST="$image" FN_NATIVE_IMAGE_SOURCE_SHA={source} \
FN_NATIVE_LAUNCHER_SHA256="$(digest "$image")" FN_NATIVE_CORE_SHA256="$core_before" \
FN_NATIVE_RUNTIME_SHA256="$runtime_expected" \
  python3 -m unittest {tests} -v
""".format(image=image, source=shlex.quote(self.native_image_source or ""),
             runtime=shlex.quote(self.native_runtime or ""),
             tests=" ".join(self.PROTECTED_TESTS))), timeout=900, expect=None)
        expected, witnesses = {}, []
        for line in step.output.splitlines():
            if line.startswith("NATIVE-PROTECTED-EXPECTED-") and " " in line:
                key, value = line.split(" ", 1)
                expected[key.rsplit("-", 1)[-1].lower()] = value.strip()
            elif line.startswith("NATIVE-PROTECTED-WITNESS "):
                try:
                    witnesses.append(json.loads(line.split(" ", 1)[1]))
                except json.JSONDecodeError:
                    pass
        digest = re.compile(r"[0-9A-Fa-f]{64}\Z")
        runtime, core = expected.get("runtime"), expected.get("core")

        def owners_are_the_image(witness):
            if not (isinstance(runtime, str) and isinstance(core, str)
                    and digest.fullmatch(runtime) and digest.fullmatch(core)):
                return False
            identities = witness.get("identity")
            return (isinstance(identities, dict)
                    and all(isinstance(identities.get(role), dict)
                            and identities[role].get("status") == "observed"
                            and identities[role].get("runtime_sha256") == runtime
                            and identities[role].get("core_sha256") == core
                            for role in ("a", "b")))

        observed = "witnesses={} rc={}".format(len(witnesses), step.rc)
        feed = next((w for w in witnesses if w.get("kind") == "protected-feed"), None)
        if feed is None or not owners_are_the_image(feed):
            self.blocked(("V0-TRANSIT-TLS", "V0-TRANSIT-AUTHINFO"),
                         "the protected peering witness produced no protected-feed "
                         "observation whose two live owners are this run's image ({})"
                         .format(observed), invocation=step.command)
        elif not (feed.get("security") == "starttls" and feed.get("auth") == "authinfo"
                  and feed.get("target_policy") == {"required": True,
                                                    "protected_only": True}):
            self.blocked(("V0-TRANSIT-TLS", "V0-TRANSIT-AUTHINFO"),
                         "the protected-feed witness did not run under STARTTLS, "
                         "AUTHINFO and a target that refuses both without them: {}"
                         .format(json.dumps(feed, sort_keys=True)),
                         invocation=step.command)
        else:
            for way in ("ab", "ba"):
                fact = feed.get("transit", {}).get(way, {})
                again = feed.get("reconnect", {}).get(way, {})
                if not (fact.get("identical") is True and again.get("identical") is True
                        and str(fact.get("unauthenticated_offer", "")).startswith("480")):
                    self.blocked(("V0-TRANSIT-TLS", "V0-TRANSIT-AUTHINFO"),
                                 "malformed protected-feed {} observation {} {}"
                                 .format(way, fact, again), directions=(way,),
                                 invocation=step.command)
                    continue
                evidence = json.dumps({"transit": fact, "reconnect": again},
                                      sort_keys=True)
                self.emit_once("V0-TRANSIT-TLS", ACCEPTED, step.command, evidence,
                               direction=way, client=CLIENT_DRIVER,
                               limit="the article arrived, and again after both owners "
                                     "restarted, at a target with `protected_only`; the "
                                     "chain and hostname check is OpenSSL's")
                self.emit_once("V0-TRANSIT-AUTHINFO", ACCEPTED, step.command, evidence,
                               direction=way, client=CLIENT_DRIVER,
                               limit="the target answered the same offer 480 on a "
                                     "connection that did not log in")
        for key, case in (("V0-TRANSIT-TLS-WRONG-ANCHOR", "wrong-anchor"),
                          ("V0-TRANSIT-AUTHINFO-WRONG", "wrong-password")):
            fact = next((w for w in witnesses if w.get("kind") == "protected-refusal"
                         and w.get("case") == case), None)
            if fact is None or not owners_are_the_image(fact):
                self.blocked((key,), "the protected peering witness produced no {} "
                             "observation whose two live owners are this run's image "
                             "({})".format(case, observed), invocation=step.command)
            elif (fact.get("delivered") is False and fact.get("source_alive") is True
                  and fact.get("target_alive") is True):
                self.emit_once(key, REFUSED, step.command,
                               json.dumps(fact, sort_keys=True), client=CLIENT_DRIVER,
                               limit="absence is observed for three seconds through a "
                                     "protected reader session; a longer delay is not "
                                     "excluded")
            else:
                self.blocked((key,), "malformed {} observation {}".format(case, fact),
                             invocation=step.command)

    def native_config_status(self, node):
        """Exercise the public native offline action for a supplied config."""
        config = self.native_configs[node.name]
        present = self.sh("node {} native config exists".format(node.upper),
                          self.cd("test -f {}".format(shlex.quote(config))), expect=None)
        if present.rc != 0:
            blocker = ("the native backend requires an existing regular config and "
                       "store; {} was not available on the execution host".format(config))
            self.blocked(("V0-NODE-STATUS", "V0-NODE-START") + self.POST_KEYS
                         + self.READ_KEYS, blocker, nodes=(node.name,),
                         invocation=self.native_operator(node, "status"))
            return False
        status = self.sh("node {} native operator status".format(node.upper),
                         self.cd(self.native_operator(node, "status")),
                         timeout=900, expect=None)
        limit = ("the public native operator read one preprovisioned store; this "
                 "slice did not create or alter its configuration")
        if status.rc in (EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN):
            self.from_step("V0-NODE-STATUS", status, node=node.name, limit=limit)
        else:
            self.emit(
                "V0-NODE-STATUS", NOT_EXERCISED, status.command,
                "rc={} {}".format(status.rc, status.first_line or "(no output)"),
                node=node.name, blocker="native operator status reported host fault or "
                                        "usage, not an accepted/refused/uncertain outcome",
                limit=limit)
        if status.rc != EXIT_OK:
            self.blocked(
                ("V0-NODE-START",),
                "the pre-start public native status action exited {}; the harness did "
                "not start a service over a store it could not open cleanly".format(
                    status.rc),
                nodes=(node.name,), invocation=self.native_operator(node, "run"))
        return status.rc == EXIT_OK

    # -- the native slice's own phases ---------------------------------------
    def native_config_port(self, node: NodeSpec) -> int:
        """The listener port a supplied native configuration declares.

        The driver learns a node's port from LISTENING once it runs, and a
        peer record on the OTHER node has to name it before either starts, so
        the number is read out of the configuration text here.
        """
        config = self.native_configs[node.name]
        step = self.sh("node {} configured port".format(node.upper),
                       "sed -n 's/^port *= *\\([0-9][0-9]*\\).*/\\1/p' {} | head -1"
                       .format(shlex.quote(config)), expect=None)
        try:
            return int(step.output.strip().splitlines()[-1])
        except (ValueError, IndexError):
            return 0

    # One loopback port per node for the scratch owner the capacity refusal
    # needs; the two preprovisioned nodes carry their own ports in their
    # configurations and these must not collide with them.
    CAPACITY_OWNER_PORTS = {"a": 11290, "b": 11291}
    # The scratch owner that carries `[auth] required = true`, one per node
    # (`native_auth_gate`), and the port the wildcard-listener configuration
    # names and never reaches a bind for (`native_loopback_refusal`).
    AUTH_GATE_PORTS = {"a": 11292, "b": 11293}
    LOOPBACK_DECLARED_PORT = 11294

    # One loopback port per node for the scratch owner the init/uncertain
    # phase serves; it must collide with neither supplied configuration nor
    # the capacity and auth-gate scratch owners above.
    INIT_OWNER_PORTS = {"a": 11295, "b": 11296}

    # The scratch owner that carries `[log] path` (`native_profile`).
    PROFILE_OWNER_PORT = 11297
    PROFILE_AGENT = "fn@matrix.example.invalid"

    def native_init_lifecycle(self, node: NodeSpec):
        """A whole node, stood up and taken apart by the public operator alone.

        `init` creates the store the configuration names; an owner of its own
        serves it; one submission's durable outcome is made unknown to its
        caller; `recover` reopens the store that owner released when it fenced
        itself; and a second `init` over the store is refused with its history
        intact.  Every step is one public verb against one configuration --
        the image's low-level `store ROOT init` entry appears nowhere in this
        phase, which is the point of it.

        The subject is a scratch node beside the served one.  The uncertain
        half needs a developer-profile image, because the cut that produces
        it (`FN_NATIVE_CONTROL_FAULT`, host/native/owner.lisp) is refused by a
        production image rather than honoured; with no `--native-developer-image`
        the phase posts an ordinary article instead, so the init and reinit
        rows are still measured and V0-OUT-UNCERTAIN stays not-built with the
        image it wanted named.
        """
        scratch = "{}/init".format(node.dir)
        store = "{}/store".format(scratch)
        config = "{}/fn.toml".format(scratch)
        port = self.INIT_OWNER_PORTS[node.name]
        # Every path here is a `$HOME/...` shell expression by construction
        # (see `Raw`), so none of them is quoted.
        self.sh("node {} init scratch configuration".format(node.upper), self.cd(
            "mkdir -p {scratch} && printf '[store]\\npath = \"%s\"\\n[listener]\\n"
            "host = \"127.0.0.1\"\\nport = {port}\\n[control]\\npath = \"%s\"\\n' "
            "\"{store}\" \"{scratch}/control.sock\" > {config}".format(
                scratch=scratch, store=store, port=port, config=config)),
            timeout=900, expect=None)
        created = self.sh("node {} operator init".format(node.upper), self.cd(
            self.native_command(self.Raw(config), "init", self.native_group)),
            timeout=900, expect=None)
        self.from_step("V0-NODE-INIT", created, node=node.name,
                       limit="the store `[store] path` names, created by the public "
                             "operator verb rather than by the image's low-level "
                             "`store ROOT init` diagnostic; the groups are the ones "
                             "this command named and there is no default table, so an "
                             "`init` with no group is a usage error and not a store "
                             "nobody chose the contents of. A scratch node beside the "
                             "served one: nothing here changes what the node serves")
        self.emit("V0-NODE-CONFIG", NOT_BUILT,
                  self.native_command(self.Raw(config), "init", self.native_group),
                  "(not run)", node=node.name,
                  blocker="the native configuration has no `[acl2] path`: ACL2 is "
                          "inside the image, so half of this row has no native "
                          "subject. The `[store] path` half is what the row above "
                          "consumed, and no native verb writes an fn.toml",
                  owner="native configuration schema")
        if created.rc != EXIT_OK:
            self.blocked(("V0-NODE-REINIT", "V0-NODE-REINIT-SAFE"),
                         "the operator could not create the scratch store (rc={} {}), "
                         "so a second init over it would not have been the subject "
                         "this row names".format(created.rc, created.first_line),
                         nodes=(node.name,), invocation=created.command)
            self.blocked(("V0-OUT-UNCERTAIN",),
                         "the operator could not create the scratch store the "
                         "uncertain submission needs (rc={} {})".format(
                             created.rc, created.first_line),
                         verdict=NOT_BUILT, owner="native operator init surface",
                         nodes=(node.name,), invocation=created.command)
            return

        developer = self.native_developer_image
        tag = "init-{}".format(node.name)
        command = self.native_command(
            self.Raw(config), "run", image=developer or self.native_image,
            env={"FN_NATIVE_CONTROL_FAULT": "postpublish"} if developer else None)
        started = self.start_server("node {} init owner".format(node.upper),
                                    command, tag, run=scratch)
        if not started:
            self.blocked(("V0-NODE-REINIT", "V0-NODE-REINIT-SAFE"),
                         "the scratch owner over the freshly initialised store did not "
                         "reach LISTENING on port {}: {}; without an accepted article "
                         "the reinit rows would be about an empty store".format(
                             port, self.server_failure),
                         nodes=(node.name,), invocation=command)
            self.blocked(("V0-OUT-UNCERTAIN",),
                         "the scratch owner that carries the cut did not reach "
                         "LISTENING on port {}: {}".format(port, self.server_failure),
                         verdict=NOT_BUILT, owner="native developer cut campaign",
                         nodes=(node.name,), invocation=command)
            return

        msgid = "<init-{}@example.invalid>".format(node.name)
        payload = "{}/init.article".format(scratch)
        self.push_file(article(msgid, self.native_group, "one durable outcome",
                               "Submitted on the {} init scratch node by the v0 "
                               "matrix.".format(node.upper)), payload)
        try:
            submitted = self.sh(
                "node {} submission to the init scratch owner".format(node.upper),
                self.cd(self.native_command(
                    self.Raw(config), "post", "--message-id", msgid,
                    "--payload", self.Raw(payload), "--group", self.native_group)),
                timeout=900, expect=None)
        finally:
            # The fenced owner exits on its own; this is for every other path.
            self.stop_server(tag, run=scratch)
        self.native_uncertain[node.name] = submitted.rc
        if developer:
            self.from_step(
                "V0-OUT-UNCERTAIN", submitted, node=node.name,
                limit="the OWNER is the developer image and carries "
                      "`FN_NATIVE_CONTROL_FAULT=postpublish`, one entry of the same "
                      "named cut table `store post --inject-fault` selects from: "
                      "FNN-STORE-INDETERMINATE after the final publication, so the "
                      "record is durable and its report is not. The CLIENT is the "
                      "production image and invents nothing: the word is ACL2's "
                      "`fn-own-control-outcome-result`, carried as the :UNCERTAIN "
                      "status of books/native-control.lisp and projected to 3 by "
                      "`fn-native-control-status-exit-code`. The article is asserted "
                      "in neither direction afterwards; an indeterminate outcome is "
                      "evidence about the report. This is not a power loss")
        else:
            self.blocked(("V0-OUT-UNCERTAIN",),
                         "this run supplied no --native-developer-image: the cut that "
                         "makes one submission's durable outcome unknown to its caller "
                         "is developer-only and a production image refuses the "
                         "variable that selects it rather than honouring it "
                         "(host/native/owner.lisp, `fnn-owner-control-test-fault`). "
                         "The submission above ran against a production owner and was "
                         "an ordinary outcome (rc={})".format(submitted.rc),
                         verdict=NOT_BUILT, owner="native developer cut campaign",
                         nodes=(node.name,), invocation=command)

        recover = self.sh("node {} recover the init scratch store".format(node.upper),
                          self.cd(self.native_command(self.Raw(config), "recover")),
                          timeout=900, expect=None)
        if "V0-OUT-RECOVER-" + node.upper not in self.emitted:
            self.from_step("V0-OUT-RECOVER", recover, node=node.name,
                           limit="recovery of the store the scratch owner released"
                                 + (" when it fenced itself on the uncertain "
                                    "publication above" if developer else
                                    "; no uncertain publication preceded it, because "
                                    "this run had no developer image"))
        again = self.sh("node {} second operator init".format(node.upper), self.cd(
            self.native_command(self.Raw(config), "init", self.native_group)),
            timeout=900, expect=None)
        self.from_step("V0-NODE-REINIT", again, node=node.name,
                       limit="a second `init` over the store the first one made, "
                             "which by then holds a submission. The refusal is on the "
                             "presence of the store's own entries -- `config.json`, "
                             "`writer.lock`, `allocation-frontier.json`, "
                             "`transactions/`, `config/` -- so no lock is opened to "
                             "reach it; the next row is whether that is true")
        after = self.sh("node {} recover after the second init".format(node.upper),
                        self.cd(self.native_command(self.Raw(config), "recover")),
                        timeout=900, expect=None)
        held = recover.first_line or ""
        kept = after.first_line or ""
        counted = re.search(r"articles=(\d+)", held)
        safe = (recover.rc == EXIT_OK and after.rc == EXIT_OK and held == kept
                and counted is not None and int(counted.group(1)) > 0)
        if safe:
            self.emit("V0-NODE-REINIT-SAFE", ACCEPTED,
                      "{}\n{}".format(again.command, after.command),
                      "before: {} / after: {}".format(held, kept),
                      node=node.name, exit_code=after.rc, client=CLIENT_CLI,
                      limit="the whole recovery line is compared, not only a count: "
                            "transactions, articles, staging orphans, anchor and "
                            "checkpoint are all as they were before the refused "
                            "init. The store held {} article(s), so the comparison "
                            "separates more than an empty store from itself".format(
                                counted.group(1)))
        else:
            self.emit("V0-NODE-REINIT-SAFE", NOT_EXERCISED,
                      "{}\n{}".format(again.command, after.command),
                      "before: {} / after: {}".format(held or "(no output)",
                                                      kept or "(no output)"),
                      node=node.name, exit_code=after.rc, client=CLIENT_CLI,
                      blocker="the two recoveries around the refused init did not "
                              "both report a store with articles in it, so this run "
                              "has no non-degenerate before/after to compare")

    def native_capacity(self, node: NodeSpec):
        """`capacity` on a scratch store beside the served one, and its refusal."""
        scratch = "{}/capacity".format(node.dir)
        store = "{}/store".format(scratch)
        config = "{}/fn.toml".format(scratch)
        # Every path here is a `$HOME/...` shell expression by construction
        # (see `Raw`), so none of them is quoted.
        init = self.sh("node {} capacity scratch store".format(node.upper), self.cd(
            "mkdir -p {scratch} && env FN_NATIVE_HOST={image} packaging/fn-native store "
            "{store} init {group} && printf '[store]\\npath = \"%s\"\\n' \"{store}\" > {config}"
            .format(scratch=scratch, image=shlex.quote(self.native_image),
                    store=store, group=shlex.quote(self.native_group),
                    config=config)), timeout=900, expect=None)
        if init.rc != 0:
            self.blocked(("V0-CAP-SET", "V0-CAP-REFUSE"),
                         "the image's store entry did not initialise a scratch store "
                         "(rc={} {})".format(init.rc, init.first_line), nodes=(node.name,),
                         invocation=init.command)
            return
        cap = self.sh("node {} capacity 64".format(node.upper),
                      self.cd(self.native_command(self.Raw(config), "capacity", "64")),
                      timeout=900, expect=None)
        self.from_step("V0-CAP-SET", cap, node=node.name,
                       limit="a scratch store beside the served one, initialised through "
                             "the image's store entry, so a refusal here cannot change "
                             "what the node serves")
        # The refusal: native `post` is a submission to a live owner over its
        # control socket, so the scratch store gets an owner of its own on a
        # port of its own, and the article whose charge exceeds a capacity of
        # 1 is offered to it.
        tight = self.sh("node {} capacity 1".format(node.upper),
                        self.cd(self.native_command(self.Raw(config), "capacity", "1")),
                        timeout=900, expect=None)
        port = self.CAPACITY_OWNER_PORTS[node.name]
        self.sh("node {} capacity owner config".format(node.upper), self.cd(
            "printf '[listener]\\nhost = \"127.0.0.1\"\\nport = {port}\\n[control]\\n"
            "path = \"%s\"\\n' {scratch}/control.sock >> {config}".format(
                port=port, scratch=scratch, config=config)), expect=None)
        tag = "capacity-{}".format(node.name)
        started = self.start_server("node {} capacity owner".format(node.upper),
                                    self.native_command(self.Raw(config), "run"),
                                    tag, run=scratch)
        if not started:
            self.blocked(("V0-CAP-REFUSE",),
                         "the scratch owner over the capacity-1 store did not reach "
                         "LISTENING on port {}: {}".format(port, self.server_failure),
                         nodes=(node.name,),
                         invocation=self.native_command(self.Raw(config), "run"))
            return
        msgid = "<capacity-{}@example.invalid>".format(node.name)
        payload = "{}/capacity.article".format(scratch)
        self.push_file(article(msgid, self.native_group, "over the capacity", "x" * 4096),
                       payload)
        try:
            over = self.sh("node {} post beyond the capacity".format(node.upper),
                           self.cd(self.native_command(
                               self.Raw(config), "post", "--message-id", msgid,
                               "--payload", self.Raw(payload), "--group",
                               self.native_group)), timeout=900, expect=None)
            self.from_step("V0-CAP-REFUSE", over, node=node.name,
                           limit="the capacity was set to 1 (rc={}) on a scratch store "
                                 "served by an owner of its own on port {}; the "
                                 "article's own charge is what has to exceed it, and "
                                 "the charge is ACL2's".format(tight.rc, port))
        finally:
            # The scratch owner holds a port on a box this gate shares, so it
            # is stopped even if the row above raised.
            self.stop_server(tag, run=scratch)

    # -- F-AUTH on the packaged native image --------------------------------
    #
    # The two supplied configurations are this slice's subject and are never
    # rewritten, so F-AUTH's credential half and its policy half have two
    # different subjects and every row says which one it had.
    #
    #   * The credential is enrolled through the public operator into each
    #     SUPPLIED node's own registry (`[auth] path`, default
    #     `<store>/auth.toml`) before either owner starts: the native owner
    #     loads credentials once, after recovery and before the listener
    #     opens (specs/native-config.md), so an enrolment after the start
    #     would not be visible to a login.  V0-AUTH-PASSWORD, V0-AUTH-LIST,
    #     V0-AUTH-ADVERTISED, V0-AUTH-LOGIN, V0-AUTH-WITHDRAWN, V0-AUTH-POST
    #     and V0-AUTH-WRONG are therefore about the served node.  Because
    #     neither supplied configuration sets `[auth] required`, the reader
    #     and POST rows keep working unauthenticated exactly as before:
    #     `fn-auth-postingp` (books/nntp-auth.lisp) leaves an unauthenticated
    #     connection with its pinned injection configuration unless the
    #     policy requires authentication, and `AUTHINFO USER` is advertised
    #     as soon as a credential exists.
    #   * V0-AUTH-GATED is the one row that is ABOUT the policy: `480
    #     authentication required` answers an unauthenticated POST only on a
    #     node whose configuration requires authentication (Astra,
    #     planning/astra-reorientation-2026-09-21.md).  The slice therefore
    #     synthesizes a scratch store and configuration beside each node with
    #     `[auth] required = true` and serves it with an owner of its own on
    #     a port of its own, exactly as `native_capacity` does for the
    #     capacity refusal.  A third preprovisioned configuration or a
    #     `--native-auth-required-node` option was rejected for two reasons:
    #     it would make the row's subject depend on how the operator invoked
    #     the harness, and on the named node it would put every reader and
    #     POST row behind a login, which is the one thing this task must not
    #     do.  The row's `limit` names the scratch owner as its subject.
    #
    # The secret is never a command word: see `native_secret_files`.

    AUTH_SESSION_KEYS = ("V0-AUTH-ADVERTISED", "V0-AUTH-LOGIN",
                         "V0-AUTH-WITHDRAWN", "V0-AUTH-POST", "V0-AUTH-WRONG")

    def native_secret_files(self):
        """The run's AUTHINFO secret, generated on the host, as two paths.

        Nothing in this process ever holds it: 16 octets of the execution
        host's own `/dev/urandom` under `umask 077`, in one file with the
        secret and one with the secret twice.  `principal set-password` reads
        the password and its confirmation from standard input when there is
        no controlling terminal (host/native/auth-admin.lisp,
        `fnn-native-auth-admin-prompt-secrets`), and the gate's scripts reach
        the host on bash's OWN stdin, so every caller redirects the pair file
        explicitly.  `report.md` renders every command in full, so a secret
        in an argument -- or in the base64 of a file this gate installed --
        would be in the evidence.
        """
        one = "{}/auth.secret".format(self.run)
        pair = "{}/auth.secret.pair".format(self.run)
        if not self._native_secret_ready:
            step = self.sh("native AUTHINFO secret", self.cd(
                "umask 077 && od -An -tx1 -N16 /dev/urandom | tr -d ' \\n' > {one}"
                " && printf '%s\\n%s\\n' \"$(cat {one})\" \"$(cat {one})\" > {pair}"
                " && test -s {one} && test -s {pair} && echo SECRET-READY".format(
                    one=one, pair=pair)), expect=None)
            self._native_secret_ready = "SECRET-READY" in step.output
        return (one, pair) if self._native_secret_ready else ("", "")

    def native_principals(self, node: NodeSpec):
        """Enrol one AUTHINFO credential in the supplied node's own registry."""
        keys = ("V0-AUTH-PASSWORD", "V0-AUTH-LIST") + self.AUTH_SESSION_KEYS
        one, pair = self.native_secret_files()
        if not pair:
            self.blocked(keys,
                         "the execution host produced no secret file for this run, and "
                         "a secret must not enter a recorded command, so no credential "
                         "was enrolled", nodes=(node.name,),
                         invocation="od -An -tx1 -N16 /dev/urandom")
            return
        # `timeout` on the REMOTE side, not only the gate's: the image reads
        # two lines of standard input, and an image that waited for a third
        # would otherwise be killed locally while the remote process kept the
        # credential lock and made the next attempt refuse for the wrong
        # reason.  124 is not one of the three outcomes and says so.
        setpw = self.sh(
            "node {} principal set-password {}".format(node.upper, AUTH_USER),
            self.cd("timeout 120 {} < {}".format(
                self.native_operator(node, "principal", "set-password", AUTH_USER),
                pair)), timeout=240, expect=None)
        self.from_step("V0-AUTH-PASSWORD", setpw, node=node.name,
                       limit="the password and its confirmation are read from a file on "
                             "the execution host (two lines, umask 077) because the "
                             "image reads them from standard input when there is no "
                             "tty; what is stored is books/auth-secret.lisp's salted "
                             "verifier and the row is about the operator writing it, "
                             "not about the digest's strength or the secret's "
                             "protection on the wire")
        self.native_credential[node.name] = setpw.rc == EXIT_OK
        listing = self.sh("node {} principal list".format(node.upper),
                          self.cd(self.native_operator(node, "principal", "list")),
                          timeout=900, expect=None)
        shows = AUTH_USER in listing.output
        verdict = exit_verdict(listing.rc)
        if verdict == ACCEPTED and not shows:
            verdict = REFUSED
        self.emit("V0-AUTH-LIST", verdict, listing.command,
                  "rc={} {}; lists {}: {}".format(
                      listing.rc, listing.first_line or "(no output)", AUTH_USER, shows),
                  node=node.name, exit_code=listing.rc, client=CLIENT_CLI,
                  limit="one registry: `set-password` writes and `list` reads the "
                        "credential file the running owner loads at startup; the "
                        "listing prints the login, its principal and its posting flag "
                        "and never the verifier")
        if not self.native_credential[node.name]:
            self.blocked(self.AUTH_SESSION_KEYS,
                         "node {}: `principal set-password` exited {} ({}), so no "
                         "credential this run knows exists on the node and an AUTHINFO "
                         "session would measure the absence of a credential rather than "
                         "the login".format(node.upper, setpw.rc, setpw.first_line),
                         nodes=(node.name,), invocation=setpw.command)

    def native_auth_session(self, node: NodeSpec):
        """AUTHINFO on the served node, with the credential enrolled above."""
        one, _ = self.native_secret_files()
        step = self.matrix("auth", "--port {} --group {} --user {} --secret-file {} "
                           "--msgid '{}'".format(node.port, shlex.quote(self.native_group),
                                                 AUTH_USER, one, AUTH_POST[node.name]),
                           name="node {} AUTHINFO session".format(node.upper),
                           expect=None)
        result = self.payload(step)
        if not result or "AUTHINFO USER" not in result:
            self.blocked(self.AUTH_SESSION_KEYS,
                         "the AUTHINFO driver produced no result on node {}: {}".format(
                             node.upper, result.get("error", step.first_line)),
                         nodes=(node.name,), invocation=step.command)
            return
        self.emit("V0-AUTH-ADVERTISED",
                  ACCEPTED if result.get("AUTHINFO ADVERTISED") else REFUSED,
                  step.command, "CAPABILITIES before the login: {}".format(
                      ", ".join(result.get("advertised_before", [])) or "(none)"),
                  node=node.name,
                  limit="RFC 4643 section 2.1 as books/nntp-auth.lisp reads it: the "
                        "label is offered while the connection is unauthenticated AND a "
                        "credential is configured, so this row depends on the enrolment "
                        "above and says nothing about a node with no credential")
        self.from_reply("V0-AUTH-LOGIN", result.get("AUTHINFO PASS", ""), step.command,
                        node=node.name,
                        limit="USER/PASS over an unprotected loopback connection; the "
                              "secret reached the driver as a file path and is in no "
                              "recorded command")
        self.emit("V0-AUTH-WITHDRAWN",
                  ACCEPTED if result.get("AUTHINFO WITHDRAWN") else REFUSED,
                  step.command, "CAPABILITIES after the login: {}".format(
                      ", ".join(result.get("advertised_after", [])) or "(none)"),
                  node=node.name)
        self.from_reply("V0-AUTH-POST", result.get("POST AFTER COMMIT", ""),
                        step.command, node=node.name,
                        limit="the posting allowance of an authenticated connection is "
                              "the credential's own bit and nothing else "
                              "(`fn-auth-postingp`); `set-password` defaults it to true "
                              "and this run did not pass `--no-posting`")
        if str(result.get("POST AFTER COMMIT", "")).startswith("240"):
            node.accepted.append(AUTH_POST[node.name])
        self.from_reply("V0-AUTH-WRONG", result.get("AUTHINFO WRONG", ""),
                        step.command, node=node.name,
                        limit="one wrong password; no rate limit or lockout is tested")

    def native_auth_gate(self, node: NodeSpec):
        """V0-AUTH-GATED, on a scratch owner that requires authentication."""
        scratch = "{}/authgate".format(node.dir)
        store = "{}/store".format(scratch)
        config = "{}/fn.toml".format(scratch)
        port = self.AUTH_GATE_PORTS[node.name]
        one, pair = self.native_secret_files()
        if not pair:
            self.blocked(("V0-AUTH-GATED",),
                         "the execution host produced no secret file for this run, so "
                         "the auth-required subject had no credential and a 480 on it "
                         "could not be told from a node with an empty registry",
                         nodes=(node.name,), invocation="od -An -tx1 -N16 /dev/urandom")
            return
        # Every path here is a `$HOME/...` shell expression by construction
        # (see `Raw`), so none of them is quoted.
        init = self.sh("node {} auth-required scratch store".format(node.upper), self.cd(
            "mkdir -p {scratch} && env FN_NATIVE_HOST={image} packaging/fn-native store "
            "{store} init {group} && printf '[store]\\npath = \"%s\"\\n[listener]\\n"
            "host = \"127.0.0.1\"\\nport = %s\\n[auth]\\nrequired = true\\n[control]\\n"
            "path = \"%s\"\\n' \"{store}\" {port} \"{scratch}/control.sock\" > {config}"
            .format(scratch=scratch, image=shlex.quote(self.native_image), store=store,
                    group=shlex.quote(self.native_group), port=port, config=config)),
            timeout=900, expect=None)
        enrol = self.sh("node {} auth-required scratch credential".format(node.upper),
                        self.cd("timeout 120 {} < {}".format(
                            self.native_command(self.Raw(config), "principal",
                                                "set-password", AUTH_USER), pair)),
                        timeout=240, expect=None)
        if init.rc != 0 or enrol.rc != EXIT_OK:
            self.blocked(("V0-AUTH-GATED",),
                         "the auth-required subject was not prepared: the image's store "
                         "entry exited {} ({}) and `principal set-password` exited {} "
                         "({})".format(init.rc, init.first_line, enrol.rc,
                                       enrol.first_line),
                         nodes=(node.name,), invocation=enrol.command)
            return
        tag = "authgate-{}".format(node.name)
        started = self.start_server("node {} auth-required owner".format(node.upper),
                                    self.native_command(self.Raw(config), "run"),
                                    tag, run=scratch)
        if not started:
            self.blocked(("V0-AUTH-GATED",),
                         "the scratch owner over the auth-required configuration did "
                         "not reach LISTENING on port {}: {}".format(
                             port, self.server_failure),
                         nodes=(node.name,),
                         invocation=self.native_command(self.Raw(config), "run"))
            return
        # From here the scratch owner is running, so every exit goes through
        # `stop_server`: a row that raised must not leave an owner holding a
        # port on a box this gate shares.
        try:
            self.native_auth_gate_rows(node, port, one)
        finally:
            self.stop_server(tag, run=scratch)

    def native_auth_gate_rows(self, node: NodeSpec, port: int, one: str):
        """V0-AUTH-GATED, against the auth-required owner `native_auth_gate` started."""
        step = self.matrix("auth", "--port {} --group {} --user {} --secret-file {} "
                           "--msgid '{}'".format(
                               port, shlex.quote(self.native_group), AUTH_USER, one,
                               "<auth-gate-{}@example.invalid>".format(node.name)),
                           name="node {} auth-required AUTHINFO gate".format(node.upper),
                           expect=None)
        result = self.payload(step)
        if not result or "POST BEFORE" not in result:
            self.blocked(("V0-AUTH-GATED",),
                         "the AUTHINFO driver produced no result against the "
                         "auth-required owner on port {}: {}".format(
                             port, result.get("error", step.first_line)),
                         nodes=(node.name,), invocation=step.command)
        else:
            self.from_reply(
                "V0-AUTH-GATED", result.get("POST BEFORE", ""), step.command,
                node=node.name,
                limit="the subject is a scratch store beside node {}'s, served by an "
                      "owner of its own on port {} under `[auth] required = true`; the "
                      "supplied configuration is not rewritten and does not set that "
                      "policy, which is why its reader and POST rows stay "
                      "unauthenticated. The same owner answered '{}' to the login and "
                      "'{}' to POST after it, so the refusal above is the policy and "
                      "not a dead node. RFC 4643 section 2.3 does not require the same "
                      "code for every gated verb".format(
                          node.upper, port,
                          result.get("AUTHINFO PASS", "(no reply)"),
                          result.get("POST AFTER", "(not attempted)")))

    def native_config_store(self, node: NodeSpec) -> str:
        """The store path a supplied configuration declares, read as text.

        `[store] path` is what an offline command over the same store has to
        name, and only the node itself knows it: this slice never created the
        configuration and must not assume a layout for it.
        """
        config = self.native_configs[node.name]
        step = self.sh("node {} configured store".format(node.upper),
                       "awk '/^\\[/ {{t=$0}} t==\"[store]\" && /^path *=/ "
                       "{{sub(/^path *= *\"/, \"\"); sub(/\".*$/, \"\"); print; exit}}' {}"
                       .format(shlex.quote(config)), expect=None)
        lines = [x.strip() for x in step.output.splitlines() if x.strip()]
        return lines[-1] if lines else ""

    def native_loopback_refusal(self):
        """A wildcard listener host, offered to the public operator's own `run`."""
        root = "{}/loopback".format(self.deploy)
        store = "{}/store".format(root)
        config = "{}/fn.toml".format(root)
        init = self.sh("loopback refusal: scratch store", self.cd(
            "mkdir -p {root} && env FN_NATIVE_HOST={image} packaging/fn-native store "
            "{store} init {group} && printf '[store]\\npath = \"%s\"\\n[listener]\\n"
            "host = \"0.0.0.0\"\\nport = %s\\n[control]\\npath = \"%s\"\\n' "
            "\"{store}\" {port} \"{root}/control.sock\" > {config}".format(
                root=root, image=shlex.quote(self.native_image), store=store,
                group=shlex.quote(self.native_group),
                port=self.LOOPBACK_DECLARED_PORT, config=config)),
            timeout=900, expect=None)
        if init.rc != 0:
            self.blocked(("V0-NODE-LOOPBACK",),
                         "the image's store entry did not initialise the store the "
                         "wildcard configuration names (rc={} {}), so a refusal could "
                         "not be attributed to the listener host".format(
                             init.rc, init.first_line),
                         invocation=init.command)
            return
        step = self.sh("loopback refusal: run", self.cd(
            "timeout 60 " + self.native_command(self.Raw(config), "run")),
            timeout=180, expect=None)
        # Both commands are the invocation: a reader of the row has to see
        # that the configuration the operator was handed declared `0.0.0.0`.
        self.emit(
            "V0-NODE-LOOPBACK", exit_verdict(step.rc),
            "{}\n{}".format(init.command, step.command),
            "rc={} {}".format(step.rc, step.first_line or "(no output)"),
            exit_code=step.rc, client=CLIENT_CLI,
            limit="the wildcard is refused at configuration admission "
                  "(`fn-native-config-listener-hostp`, books/native-config.lisp), not "
                  "at bind: `0.0.0.0` never reaches a listener, and the operator "
                  "reports an inadmissible "
                  "configuration as a usage error (5) rather than as one of the three "
                  "outcomes -- so unless the image answers 1 this row is not-exercised "
                  "with that code named, and the refusal it wanted has still happened "
                  "at admission. A numeric non-loopback IPv4 address is ADMITTED by "
                  "design and would be bound: this row is about the wildcard, not "
                  "about fn declining to serve a network interface. Nothing here tests "
                  "a bind the kernel would refuse for a different reason")

    def native_profile(self, node: NodeSpec):
        """V0-NODE-PROFILE: `[log] path` honoured, `[posting] agent` refused by name.

        A scratch store beside NODE's with an owner of its own: one
        configuration names an absolute `[log] path`, the other adds a
        `[posting] agent`.  The row is accepted only when `run` refuses the
        second with the key named, the first reaches LISTENING, one `post`
        through its control socket exits 0, and the log file then holds that
        post's `accepted post path=control` line.
        """
        keys = ("V0-NODE-PROFILE",)
        scratch = "{}/profile".format(node.dir)
        store = "{}/store".format(scratch)
        config = "{}/fn.toml".format(scratch)
        agent_config = "{}/agent.toml".format(scratch)
        log = "{}/service.log".format(scratch)
        msgid = "<profile-{}@example.invalid>".format(node.name)
        init = self.sh("node {} profile scratch store".format(node.upper), self.cd(
            "mkdir -p {scratch} && rm -f {log} && env FN_NATIVE_HOST={image} "
            "packaging/fn-native store {store} init {group} && printf '[store]\\npath = "
            "\"%s\"\\n[listener]\\nhost = \"127.0.0.1\"\\nport = %s\\n[log]\\npath = "
            "\"%s\"\\n[control]\\npath = \"%s\"\\n' \"{store}\" {port} \"{log}\" "
            "\"{scratch}/control.sock\" > {config} && printf '[store]\\npath = \"%s\"\\n"
            "[posting]\\nagent = \"%s\"\\n' \"{store}\" {agent} > {agent_config}".format(
                scratch=scratch, log=log, image=shlex.quote(self.native_image),
                store=store, group=shlex.quote(self.native_group),
                port=self.PROFILE_OWNER_PORT, config=config,
                agent=shlex.quote(self.PROFILE_AGENT), agent_config=agent_config)),
            timeout=900, expect=None)
        if init.rc != 0:
            self.blocked(keys, "the profile scratch store was not prepared: the image's "
                               "store entry exited {} ({})".format(init.rc, init.first_line),
                         nodes=(node.name,), invocation=init.command)
            return
        refusal = self.sh("node {} profile agent refusal".format(node.upper), self.cd(
            "timeout 60 " + self.native_command(self.Raw(agent_config), "run")),
            timeout=180, expect=None)
        refused_by_name = (refusal.rc == EXIT_USAGE
                           and "UNSUPPORTED-PROFILE agent" in refusal.output)
        tag = "profile-{}".format(node.name)
        run = self.native_command(self.Raw(config), "run")
        started = self.start_server("node {} profile owner".format(node.upper), run,
                                    tag, run=scratch)
        if not started:
            self.emit("V0-NODE-PROFILE", REFUSED, "{}\n{}".format(init.command, run),
                      "the owner over a configuration naming `[log] path` did not "
                      "reach LISTENING: {}".format(self.server_failure),
                      client=CLIENT_CLI,
                      limit="the configuration differs from an admitted one only by "
                            "its `[log]` table, so a refusal here is the log key's")
            return
        try:
            payload = "{}/profile.article".format(scratch)
            self.push_file(article(msgid, self.native_group, "profile",
                                   "The operator log line for this post."), payload)
            post = self.sh("node {} profile post".format(node.upper), self.cd(
                self.native_command(self.Raw(config), "post", "--message-id", msgid,
                                    "--payload", self.Raw(payload),
                                    "--group", self.native_group)),
                timeout=900, expect=None)
        finally:
            self.stop_server(tag, run=scratch)
        logged = self.sh("node {} profile service log".format(node.upper),
                         "cat {} 2>/dev/null || echo NO-LOG-FILE".format(log),
                         expect=None)
        wanted = "accepted post path=control message-id={}".format(msgid)
        line = next((x for x in logged.output.splitlines() if x.startswith(wanted)), "")
        observed = ("agent refusal: rc={} {}; post: rc={} {}; log line: {}".format(
            refusal.rc, refusal.first_line or "(no output)", post.rc,
            post.first_line or "(no output)", line or "(none)"))
        invocation = "{}\n{}\n{}\n{}".format(init.command, refusal.command, run,
                                               post.command)
        limit = ("a scratch owner beside node {}'s on port {}; the log is the file "
                 "`[log] path` names, opened append-only before the store, and the "
                 "line is ACL2's (books/owner-log.lisp); the agent refusal is "
                 "`fn-native-config-unsupported-key`'s, and the injecting agent a "
                 "served POST names is the `path-identity` policy "
                 "(books/owner-agent.lisp), which this row does not read".format(
                     node.upper, self.PROFILE_OWNER_PORT))
        if post.rc != EXIT_OK:
            self.emit("V0-NODE-PROFILE", NOT_EXERCISED, invocation, observed,
                      client=CLIENT_CLI, exit_code=post.rc,
                      blocker="the post the log line was to record exited {}, so "
                              "the log was not tested on an accepted submission".format(
                                  post.rc),
                      limit=limit)
        elif line and refused_by_name:
            self.emit("V0-NODE-PROFILE", ACCEPTED, invocation, observed,
                      client=CLIENT_CLI, exit_code=post.rc, limit=limit)
        else:
            self.emit("V0-NODE-PROFILE", REFUSED, invocation, observed,
                      client=CLIENT_CLI, exit_code=post.rc,
                      limit=limit + "; {}".format(
                          "the accepted post left no line in the log file"
                          if not line else
                          "`run` did not refuse `[posting] agent` with the key named"))

    LIVE_GROUP = "fn.matrix.live"

    def native_peer_records(self):
        """A peer record on each node naming the other, in the operator's grammar."""
        for node in self.nodes:
            # The node's OWN <path-identity>: `fn-peer-local-identity` reads
            # this policy slot, and the loop rows below are unfounded without
            # it.  An image whose operator predates the verb answers usage
            # (5), which `from_step` records as not-exercised with the code.
            ident = self.sh("node {} path-identity".format(node.upper),
                            self.cd(self.native_operator(node, "policy", "set",
                                                         "path-identity",
                                                         node.path_identity)),
                            timeout=900, expect=None)
            self.from_step("V0-TRANSIT-IDENTITY", ident, node=node.name,
                           limit="a `:set-policy` configuration record; the loop rows "
                                 "below are what shows the owner read it")
            if ident.rc != EXIT_OK:
                self.gaps.append(
                    "node {} has no <path-identity> of its own (rc={}, {}); RFC 5537 "
                    "3.5 loop suppression cannot fire on it and V0-TRANSIT-LOOP is "
                    "measuring an unconfigured node.".format(
                        node.upper, ident.rc, ident.first_line))
        # Inbound `fn.*`, outbound `-`: the transit rows below offer articles
        # BY HAND over the driver's socket, and a record with an outbound
        # pattern makes the native owner's own feed deliver every live post
        # to the peer first, so the hand-made offer draws 435 and CHECK 438
        # (measured 01:41Z: eight articles on each node, every one fed).  The
        # feed itself is the witness's measurement, on nodes of its own.
        for node, other in ((self.a, self.b), (self.b, self.a)):
            port = self.native_config_port(other)
            add = self.sh("node {} peer record for {}".format(node.upper, other.upper),
                          self.cd(self.native_operator(
                              node, "peer", "add", other.name, other.path_identity,
                              "127.0.0.1", str(port), "fn.*", "-", "127.0.0.1",
                              "true")), timeout=900, expect=None)
            self.from_step("V0-PEER-ADD", add, node=node.name,
                           limit="a peer record is configuration, not authorization; "
                                 "the positional grammar is books/native-operator.lisp's, "
                                 "the inbound ceiling is the record's own default, and "
                                 "the outbound pattern is `-` so the hand-driven transit "
                                 "rows are not pre-empted by the owner's feed")
            if add.rc != EXIT_OK:
                self.limitation(
                    None,
                    "node {} could not write a peer record for {} (rc={}, {}); the "
                    "transit rows below run without the peer table they name"
                    .format(node.upper, other.upper, add.rc, add.first_line))
            listed = self.sh("node {} lists its peers".format(node.upper),
                             self.cd(self.native_operator(node, "peer", "list")),
                             timeout=900, expect=None)
            # The row is whether the record READS BACK, so an accepted listing
            # that does not name the peer is a refusal of the row, not of the
            # command: a listing nobody is in is still a listing.
            shows = other.path_identity in listed.output
            self.emit("V0-PEER-LIST",
                      ACCEPTED if (listed.rc == EXIT_OK and shows)
                      else REFUSED if listed.rc == EXIT_OK
                      else exit_verdict(listed.rc), listed.command,
                      "rc={} names {}: {}".format(listed.rc, other.path_identity, shows),
                      node=node.name, exit_code=listed.rc, client=CLIENT_CLI,
                      limit="the record read back out of the durable configuration, in "
                            "the order `peer add` takes its arguments and rendered by "
                            "ACL2 (`fn-native-admin-peer-report`, "
                            "books/native-admin.lisp); the <path-identity> is what is "
                            "matched, not the one-letter node name. It is a read: the "
                            "store is opened without the exclusive writer lock and the "
                            "live owner is never reached, so it runs in this offline "
                            "window and would refuse while an owner held the store, "
                            "exactly as `status` does")
            if listed.rc == EXIT_OK and not shows and add.rc == EXIT_OK:
                self.limitation(
                    None,
                    "node {} accepted `peer add {}` but `peer list` does not name it: "
                    "the record did not survive the replay ({})".format(
                        node.upper, other.upper,
                        listed.first_line or "(no output)"))

    def native_submit(self, node: NodeSpec, msgid: str, subject: str, body: str,
                      name: str, tag: str = "") -> Step:
        """One article through the public `post`, to the live owner's control socket.

        Two calls with the same Message-ID, subject and body push byte-identical
        octets (`article_stamp`). `tag` names a deliberate variant and gives it
        its own file, so a row that submits different octets under one
        Message-ID neither overwrites the accepted article nor is mistaken for
        a resubmission of it.
        """
        stem = msgid.strip("<>").split("@")[0] + (("-" + tag) if tag else "")
        payload = "{}/{}.article".format(node.dir, stem)
        self.push_file(article(msgid, self.native_group, subject, body), payload)
        return self.sh(name, self.cd(self.native_operator(
            node, "post", "--message-id", msgid, "--payload", self.Raw(payload),
            "--group", self.native_group)), timeout=900, expect=None)

    def native_outcomes(self, node: NodeSpec):
        """The operator-surface outcomes the production image can show.

        Three submissions of one Message-ID, and the octets are what separates
        them: the first is new, the second is byte-identical, the third carries
        a different body. The node answers `ACCEPTED`, the idempotent
        `DUPLICATE` and `REFUSED`, and those words are a function of the octets
        alone -- see `planning/evidence/native-duplicate-outcome-2026-09-22.md`
        for the twelve trials that pinned it on the 915 image.
        """
        msgid = ART[node.name]
        subject = "outcome, written on {}".format(node.upper)
        body = ("Written on node {} by the v0 matrix through the native operator."
                .format(node.upper))
        accepted = self.native_submit(
            node, msgid, subject, body,
            "node {} outcome accepted".format(node.upper))
        self.from_step("V0-OUT-ACCEPTED", accepted, node=node.name,
                       limit="one article submitted to the live owner over its control "
                             "socket; the exit code is the observation")
        if accepted.rc == EXIT_OK:
            node.accepted.append(msgid)
        duplicate = self.native_submit(
            node, msgid, subject, body,
            "node {} outcome duplicate".format(node.upper))
        refused = self.native_submit(
            node, msgid, subject,
            body + " This body was edited after acceptance, under the Message-ID "
                   "the node already holds.",
            "node {} outcome refused".format(node.upper), tag="conflict")
        self.from_step("V0-OUT-REFUSED", refused, node=node.name,
                       limit="NOT a lookup: the native operator has no article lookup "
                             "verb, so the refusal observed here is a second submission "
                             "of the SAME Message-ID carrying DIFFERENT octets, which "
                             "the node refuses as a conflicting immutable Message-ID. A "
                             "byte-identical resubmission is a different observation: "
                             "it is the idempotent duplicate, reported as accepted with "
                             "exit 0, and it is the `duplicate resubmission` fact")
        self.facts["duplicate resubmission {}".format(node.name)] = (
            "identical octets: rc={} {} / different octets under the same "
            "Message-ID: rc={} {}".format(
                duplicate.rc, duplicate.first_line or "no output",
                refused.rc, refused.first_line or "no output"))
        # The uncertain outcome is `native_init_lifecycle`'s, on a scratch
        # node of its own: the cut fences the owner that serves it, and this
        # node's owner is the subject of every other row below.
        self.blocked(("V0-OUT-UNCERTAIN",),
                     "the init/uncertain phase did not reach a submission on this "
                     "node's scratch owner, so nothing here made one submission's "
                     "durable outcome unknown to its caller",
                     verdict=NOT_BUILT,
                     owner="native developer cut campaign", nodes=(node.name,),
                     invocation="packaging/fn-native operator SCRATCH-CONFIG post")
        self.facts["three outcomes {}".format(node.name)] = (
            "accepted={} refused={} uncertain={} (uncertain is the init scratch "
            "node's, not this one's)".format(
                accepted.rc, refused.rc,
                self.native_uncertain.get(node.name, "not-built")))

    def native_seed(self, node: NodeSpec):
        """The streaming article the CHECK/TAKETHIS rows offer."""
        step = self.native_submit(node, STREAM[node.name], "for the streaming offer",
                                  "Seeded on node {} by the v0 matrix.".format(node.upper),
                                  "node {} seed {}".format(node.upper, STREAM[node.name]))
        if step.rc == EXIT_OK:
            node.accepted.append(STREAM[node.name])
        else:
            self.limitation(
                None,
                "node {}: seeding {} exited {} ({}); the streaming rows that offer it "
                "are recorded against that".format(node.upper, STREAM[node.name],
                                                   step.rc, step.first_line))

    def native_live_reconfiguration(self):
        """The two halves, and one verb with two executors.

        `operator CONFIG group create G` dispatches on the configuration's
        `[control] path`: when that path is a live socket the request goes to
        the running owner (`fnn-owner-live-admin-serialized`,
        host/native/admin.lisp, through `fnn-operator-execute-admin`), and
        otherwise the command opens the store itself and takes the writer
        lock.  So the accepted half is the supplied configuration while its
        own owner is live, read back over the socket; and the refused half
        needs a configuration over the SAME store whose control path is a
        name nothing has bound.  Neither half rewrites a supplied
        configuration, and an image whose operator does not dispatch live
        administration answers the first half with the writer-lock refusal,
        which is recorded as the disagreement it is.
        """
        declare = self.sh(
            "live reconfiguration: declare {} on node A".format(self.LIVE_GROUP),
            self.cd(self.native_operator(self.a, "group", "create", self.LIVE_GROUP)),
            timeout=900, expect=None)
        probe = self.feed("presence", "--port {} --groups {}".format(
            self.a.port, self.LIVE_GROUP),
            name="node A serves {} without a restart".format(self.LIVE_GROUP),
            expect=None)
        served = self.payload(probe).get("groups", {}).get(self.LIVE_GROUP, "(no reply)")
        invocation = "{}\n{}".format(declare.command, probe.command)
        observed = "rc={} {}; GROUP {} -> {}".format(
            declare.rc, declare.first_line or "(no output)", self.LIVE_GROUP, served)
        limit = ("one group declared on one live owner: the operator verb's exit code is "
                 "the acceptance and the service is then asked over its own socket "
                 "whether the group reached the served configuration. No concurrent "
                 "reader was observed across the change, and nothing here says the "
                 "change survives a restart")
        # The refusal half below is only a statement about a store a live
        # owner holds.  On the dabebb84 image the live verb killed the owner
        # (host/native/admin.lisp opened its private connection through
        # `fnn-owner-action', which faults on the integer id), the offline
        # executor then found the writer lock free and correctly accepted,
        # and this row recorded that as two writers on one store.  Ask first.
        owner_alive = self.alive(self.a)
        if not owner_alive:
            observed += "; node A's owner DIED after the verb ({})".format(
                self.dead.get(self.a.name, "no log"))
        if declare.rc == EXIT_OK:
            # The verb accepted; what decides the row is whether the RUNNING
            # service serves the group, and that observation is the socket's.
            self.emit("V0-CFG-LIVE", reply_verdict(served), invocation, observed,
                      exit_code=declare.rc, limit=limit)
        else:
            self.emit("V0-CFG-LIVE", exit_verdict(declare.rc), invocation, observed,
                      exit_code=declare.rc, client=CLIENT_CLI,
                      limit=limit + "; the verb did not accept, so the socket reply "
                                    "above is the state the node was left in")
        if not owner_alive:
            self.emit("V0-CFG-LIVE-REFUSE", NOT_EXERCISED,
                      "(the offline command was not run)", "(node A's owner was gone)",
                      blocker="node A's owner died during the live verb, so no live "
                              "owner held the store: an offline command then takes the "
                              "free writer lock and is accepted, which says nothing "
                              "about a store a live owner holds")
            return
        store = self.native_config_store(self.a)
        if not store:
            self.emit("V0-CFG-LIVE-REFUSE", NOT_EXERCISED,
                      "awk '[store] path' {}".format(self.native_configs["a"]),
                      "(no store path)",
                      blocker="node A's supplied configuration did not yield a "
                              "`[store] path`, so no second configuration could name "
                              "the same store and the offline half could not be put on "
                              "the offline executor")
            return
        offline = "{}/offline".format(self.a.dir)
        self.sh("offline configuration over node A's store", self.cd(
            "mkdir -p {offline} && printf '[store]\\npath = \"%s\"\\n[control]\\n"
            "path = \"%s\"\\n' {store} \"{offline}/never-bound.sock\" > {offline}/fn.toml"
            .format(offline=offline, store=shlex.quote(store))), expect=None)
        step = self.sh("offline group create while the owner holds the store", self.cd(
            self.native_command(self.Raw("{}/fn.toml".format(offline)),
                                "group", "create", "fn.matrix.offline")),
            timeout=900, expect=None)
        self.from_step(
            "V0-CFG-LIVE-REFUSE", step,
            limit="a second configuration over node A's OWN store whose `[control] "
                  "path` names a socket nothing has bound, so the verb takes the "
                  "offline executor while the live owner (asked alive just before) "
                  "holds the writer lock; the "
                  "refusal is that lock's and a server that does not take it would not "
                  "produce it. The supplied configuration is unchanged, and with its "
                  "own live control path the same words reach the live owner instead -- "
                  "which is the row above")

    def native_stop(self, node: NodeSpec):
        """SIGTERM from the harness, then the offline operator reopens the store."""
        self.stop_node(node, tag="main")
        stopped = self.step_named("stop server node {} (main)".format(node.upper))
        stop_rc = stopped.rc if stopped is not None else 0
        release = self.sh("node {} store after the stop".format(node.upper),
                          self.cd(self.native_operator(node, "status")),
                          timeout=900, expect=None)
        self.emit("V0-NODE-STOP",
                  ACCEPTED if (stop_rc == 0 and release.rc == EXIT_OK)
                  else exit_verdict(release.rc),
                  "kill -TERM <owner pid> (harness) ; " + release.command,
                  "stop rc={}; native status afterwards rc={} {}".format(
                      stop_rc, release.rc, release.first_line),
                  node=node.name, exit_code=release.rc,
                  limit="the stop is the harness's SIGTERM, not an operator verb; the "
                        "store reopening for the offline operator is the writer lock "
                        "being gone; no in-flight session was observed across the stop")
        recover = self.sh("node {} recover after the stop".format(node.upper),
                          self.cd(self.native_operator(node, "recover")),
                          timeout=900, expect=None)
        # The init/uncertain phase has the better subject for this row -- a
        # store the owner released by fencing itself on an uncertain
        # publication -- so this is the fallback, not the measurement.
        if "V0-OUT-RECOVER-" + node.upper not in self.emitted:
            self.from_step("V0-OUT-RECOVER", recover, node=node.name,
                           limit="recovery of a store the owner released on SIGTERM; "
                                 "no uncertain publication preceded it in this run")
        self.sh("node {} log tail".format(node.upper),
                "tail -12 {}/server-{}-main.log 2>/dev/null || echo NO-LOG".format(
                    node.dir, node.name), expect=None)

    def native_peer_remove(self):
        absent = self.sh("peer remove a peer that is not there", self.cd(
            self.native_operator(self.a, "peer", "remove", "no-such-peer")),
            timeout=900, expect=None)
        self.from_step("V0-PEER-ABSENT", absent)
        real = self.sh("peer remove the configured peer", self.cd(
            self.native_operator(self.a, "peer", "remove", self.b.name)),
            timeout=900, expect=None)
        self.from_step("V0-PEER-REMOVE", real,
                       limit="run after the owners stopped, so it says nothing about "
                             "removing a peer from a live service")

    def execute_native_acceptance(self):
        """The native slice: packaged run, the operator verbs it has, and the sockets.

        Init and reinit do not yet have a public native composition on the
        images this slice targets.  They stay explicit non-outcomes instead
        of falling back to a Python runtime peer or a diagnostic native verb.
        The order is the development gate's: read-only socket phases before
        anything that can put an article into the owner's drain, and the
        capability audit after the transit rows.  Everything that must be in
        place before a listener opens -- the groups, the capacity, the peer
        records and the AUTHINFO credential, which the owner loads once at
        startup -- runs in the offline window at the top, and the
        auth-required and wildcard-listener subjects are scratch owners of
        their own so that neither supplied configuration is rewritten.
        """
        self.configured = set()
        self.preflight()
        self.ship()
        self.push_file(self.feed_driver(), "{}/feed.py".format(self.run), mode="755")
        self.push_file(MATRIX_DRIVER, "{}/matrix.py".format(self.run), mode="755")
        self.probe_native_subject()

        for node in self.nodes:
            self.sh("node {} native run directory".format(node.upper),
                    "mkdir -p {}".format(node.dir))
            if node.name not in self.native_configs:
                # The init rows are measured on a scratch node the operator
                # stands up itself, but it still needs somewhere to stand it
                # up: the deployment directory this slice was given.
                self.blocked(("V0-NODE-INIT", "V0-NODE-CONFIG", "V0-NODE-REINIT",
                              "V0-NODE-REINIT-SAFE"),
                             "no preprovisioned configuration was supplied for this "
                             "optional served-node slice, so the run has no deployment "
                             "for the operator to stand a scratch node up beside",
                             verdict=NOT_BUILT, owner="native operator init surface",
                             nodes=(node.name,),
                             invocation="packaging/fn-native operator CONFIG init GROUP")
                self.blocked(("V0-NODE-STATUS", "V0-NODE-START") + self.POST_KEYS
                             + self.READ_KEYS + self.AUTH_KEYS
                             + ("V0-AUTH-PASSWORD", "V0-AUTH-LIST"),
                             "no preprovisioned config was supplied for this optional "
                             "served-node slice; the native peering witness creates its "
                             "own temporary stores/configs through the public image",
                             nodes=(node.name,), invocation="tests.test_native_peering")
            elif self.native_config_status(node):
                self.configured.add(node.name)

        self.emit("V0-AUTH-NEW", NOT_BUILT,
                  "packaging/fn-native operator CONFIG principal new --seed FILE",
                  "(not run)",
                  blocker="the packaged native operator has no `principal new`: the "
                          "local principal id is derived by ACL2 inside `set-password` "
                          "(`fn-native-auth-admin-principal`, "
                          "books/native-auth-admin.lisp) and no public verb derives one "
                          "from a seed",
                  owner="native principal derivation surface")
        self.phase("loopback refusal", self.native_loopback_refusal)
        for node in self.nodes[:1]:
            if node.name in self.native_configs:
                self.phase("native profile {}".format(node.name),
                           self.native_profile, node)

        # A whole node through the public operator, on a scratch store beside
        # each supplied one: init, one submission whose outcome may be lost,
        # recover, and the refused second init.  It runs before the served
        # owners start, and before `native_stop`, which is why it and not the
        # stop phase owns V0-OUT-RECOVER when it reaches it.
        for node in self.nodes:
            if node.name in self.native_configs:
                self.phase("native init lifecycle {}".format(node.name),
                           self.native_init_lifecycle, node)

        # Offline administration, while no owner holds the writer lock.  The
        # credential is enrolled here and nowhere later: the native owner
        # loads `[auth] path` once, before its listener opens.
        for node in self.nodes:
            if node.name in self.configured:
                self.phase("native groups {}".format(node.name), self.groups, node)
                self.phase("native capacity {}".format(node.name),
                           self.native_capacity, node)
                self.phase("native principals {}".format(node.name),
                           self.native_principals, node)
                self.phase("native auth gate {}".format(node.name),
                           self.native_auth_gate, node)
            elif node.name in self.native_configs:
                # A supplied configuration the offline operator could not open
                # is a named reason, not the end-of-run sweep's silence.
                self.blocked(("V0-AUTH-PASSWORD", "V0-AUTH-LIST", "V0-AUTH-GATED"),
                             "node {}'s supplied configuration did not open cleanly for "
                             "the pre-start public status action, so this run wrote no "
                             "credential into its registry".format(node.upper),
                             nodes=(node.name,),
                             invocation=self.native_operator(
                                 node, "principal", "set-password", AUTH_USER))
        if all(n.name in self.configured for n in self.nodes):
            self.phase("native peer records", self.native_peer_records)

        for node in self.nodes:
            if node.name in self.configured:
                self.start_node(node)
        if self.a.port and self.b.port and self.a.port == self.b.port:
            raise GateError("both native nodes reported the same port; they are one server")

        for node in self.nodes:
            if not node.port:
                blocker = self.node_blocker(node)
                self.blocked(self.POST_KEYS + self.READ_KEYS
                             + self.AUTH_SESSION_KEYS + ("V0-GROUP-SERVED",),
                             blocker, nodes=(node.name,),
                             invocation=self.native_operator(node, "run"))
                continue
            if self.require_live(node, ("V0-GROUP-SERVED",), nodes=(node.name,)):
                self.phase("group served {}".format(node.name), self.group_served, node)
            if self.require_live(node, self.POST_KEYS, nodes=(node.name,)):
                self.phase("native POST {}".format(node.name), self.post_cycle, node)
            if (node.accepted
                    and self.require_live(node, self.READ_KEYS, nodes=(node.name,))):
                self.phase("native reader {}".format(node.name), self.read_surface, node)
            elif not node.accepted:
                self.blocked(
                    self.READ_KEYS,
                    "the native POST phase supplied no known accepted article; the "
                    "article-number and Message-ID reader rows would otherwise test a "
                    "guessed pre-existing store state",
                    nodes=(node.name,), invocation="matrix.py surface")
            # AUTHINFO after the read-only rows and after POST: this phase
            # posts an authenticated article, and a phase that can put an
            # article into the owner's drain runs once the rows that only
            # read have been taken.
            if (self.native_credential.get(node.name)
                    and self.require_live(node, self.AUTH_SESSION_KEYS,
                                          nodes=(node.name,))):
                self.phase("native AUTHINFO {}".format(node.name),
                           self.native_auth_session, node)
            if self.require_live(node, ("V0-OUT-ACCEPTED", "V0-OUT-REFUSED"),
                                 nodes=(node.name,)):
                self.phase("native outcomes {}".format(node.name),
                           self.native_outcomes, node)
                self.phase("native seed {}".format(node.name), self.native_seed, node)

        live = [n for n in self.nodes if n.port and self.alive(n)]
        if len(live) == 2:
            self.phase("independent clients", self.independent_clients)
            for source, target, way in ((self.a, self.b, "ab"), (self.b, self.a, "ba")):
                if self.require_live(target, self.TRANSIT_KEYS, directions=(way,)):
                    self.phase("transit {}".format(way.upper()),
                               self.transit_direction, source, target, way)
            for node in self.nodes:
                if self.require_live(node, ("V0-PIN-DISPATCHED", "V0-PIN-ADVERTISED"),
                                     nodes=(node.name,)):
                    self.phase("capability pins {}".format(node.name),
                               self.capability_pins, node)
            for label, method, keys in (
                    ("concurrency", self.post_concurrent, ("V0-POST-CONCURRENT",)),
                    ("live reconfiguration", self.native_live_reconfiguration,
                     ("V0-CFG-LIVE", "V0-CFG-LIVE-REFUSE"))):
                if all(self.alive(n) for n in self.nodes):
                    self.phase(label, method)
                else:
                    self.blocked(keys, "a server died earlier in this run: {}".format(
                        "; ".join("node {}: {}".format(k.upper(), v)
                                  for k, v in self.dead.items()) or "no log"),
                        invocation="(the server was gone)")
        else:
            blocker = "; ".join(
                ["node {}: {}".format(n.name.upper(), self.node_blocker(n))
                 for n in self.nodes if not n.port]
                + ["node {}: {}".format(name.upper(), why)
                   for name, why in sorted(self.dead.items())]) or (
                "fewer than two nodes were live when the paired phases would "
                "have run: {} of 2 live".format(len(live)))
            self.blocked(("V0-POST-CONCURRENT", "V0-CFG-LIVE", "V0-CFG-LIVE-REFUSE",
                          "V0-PIN-DISPATCHED", "V0-PIN-ADVERTISED",
                          "V0-CLIENT-NNTPLIB", "V0-CLIENT-SLRN")
                         + self.TRANSIT_KEYS, blocker)

        self.phase("native transit/feed/restart", self.native_peering_suite)
        self.phase("native protected transit", self.native_protected_peering_suite)

        for node in self.nodes:
            if node.pid:
                self.phase("native stop {}".format(node.name), self.native_stop, node)
            else:
                self.blocked(("V0-NODE-STOP", "V0-OUT-RECOVER"),
                             "the node never started, so there was nothing to stop",
                             nodes=(node.name,), invocation="harness SIGTERM")
        if all(n.name in self.configured for n in self.nodes):
            self.phase("native peer remove", self.native_peer_remove)
        # INN, a third node on ports of its own: the lab stands up its own
        # store from the same image, so it runs after this slice's nodes stop.
        self.phase("INN", self.inn)
        self.backfill()

    # -- the whole gate -----------------------------------------------------
    def execute(self):
        if self.backend == NATIVE_BACKEND:
            return self.execute_native_acceptance()
        self.configured = set()
        self.preflight()
        self.a.assigned_port = self.b.assigned_port = 0
        self.ship()
        self.push_file(self.feed_driver(), "{}/feed.py".format(self.run), mode="755")
        self.push_file(MATRIX_DRIVER, "{}/matrix.py".format(self.run), mode="755")
        self.certificates()
        self.probe_tree()
        self.phase("port allocation", self.allocate_ports)
        for node in self.nodes:
            self.phase("init {}".format(node.name), self.init_node, node)
            probe = self.sh("node {} has a configuration".format(node.upper),
                            "test -f {}/fn.toml && echo YES || echo NO".format(node.dir),
                            expect=None)
            if "YES" in probe.output:
                self.configured.add(node.name)
        self.phase("loopback refusal", self.loopback_refusal)
        self.phase("principals", self.principals)
        self.phase("statement preparation", self.statement_prepare)
        self.phase("outcomes A", self.three_outcomes_node, self.a, ART["a"],
                   "alpha, written on A")
        self.phase("outcomes B", self.three_outcomes_node, self.b, ART["b"],
                   "beta, written on B")
        for node in self.nodes:
            self.phase("seed {}".format(node.name), self.seed_node, node)
            self.phase("second init {}".format(node.name), self.reinit, node)
            self.phase("groups {}".format(node.name), self.groups_and_capacity, node)
        self.phase("peer records", self.peer_records)

        # What each node held before any listener existed.  `independence`
        # measures against this, not against `accepted`, which grows every
        # time a later phase posts through the running server -- and an
        # article posted through the server is exactly what the outbound feed
        # carries to the peer.
        for node in self.nodes:
            node.seeded = list(node.accepted)

        for node in self.nodes:
            self.start_node(node)
        if self.a.port and self.b.port and self.a.port == self.b.port:
            raise GateError("both nodes reported the same port; they are one server")

        for node in self.nodes:
            if not node.port:
                self.blocked(self.NODE_SOCKET_KEYS, self.node_blocker(node),
                             nodes=(node.name,))
                continue
            # Order is deliberate and it is not cosmetic.  Every phase that
            # can put an article into the owner's `drain` -- the capability
            # audit's IHAVE, the transit offer -- can end the process, and
            # this tree has twice proved it can.  The read-only phases and
            # the independent client therefore run first, so that what they
            # would have shown is not lost to a death caused by something
            # else.  The audit runs last, after the transit rows, because it
            # offers an article to every node it probes.
            for label, method, keys in (
                    ("group served", self.group_served, ("V0-GROUP-SERVED",)),
                    ("reader surface", self.read_surface, self.READ_KEYS),
                    ("AUTHINFO", self.auth_session, self.AUTH_KEYS),
                    ("POST cycle", self.post_cycle, self.POST_KEYS)):
                if self.require_live(node, keys, nodes=(node.name,)):
                    self.phase("{} {}".format(label, node.name), method, node)

        if all(n.port and self.alive(n) for n in self.nodes):
            self.phase("independent clients", self.independent_clients)
        else:
            self.blocked(("V0-CLIENT-NNTPLIB", "V0-CLIENT-SLRN"),
                         "a node had no live listener when the independent client "
                         "would have run: {}".format(
                             "; ".join("node {}: {}".format(k.upper(), v)
                                       for k, v in self.dead.items())
                             or "; ".join(self.node_blocker(n) for n in self.nodes
                                          if not n.port)),
                         invocation="<interpreter> independent.py")
        live = [n for n in self.nodes if n.port and self.alive(n)]
        if len(live) == 2:
            self.phase("independence", self.independence)
            for source, target, way in ((self.a, self.b, "ab"), (self.b, self.a, "ba")):
                if self.require_live(target, self.TRANSIT_KEYS, directions=(way,)):
                    self.phase("transit {}".format(way.upper()),
                               self.transit_direction, source, target, way)
            for node in self.nodes:
                if self.require_live(node, ("V0-PIN-DISPATCHED", "V0-PIN-ADVERTISED"),
                                     nodes=(node.name,)):
                    self.phase("capability pins {}".format(node.name),
                               self.capability_pins, node)
            for label, method, keys in (
                    ("concurrency", self.post_concurrent, ("V0-POST-CONCURRENT",)),
                    ("live reconfiguration", self.live_reconfiguration,
                     ("V0-CFG-LIVE", "V0-CFG-LIVE-REFUSE")),
                    ("outbound feed", self.outbound_feed, self.FEED_KEYS),
                    ("crash", self.crash_phase, self.CRASH_KEYS)):
                if all(self.alive(n) for n in self.nodes):
                    self.phase(label, method)
                else:
                    self.blocked(keys, "a server died earlier in this run: {}".format(
                        "; ".join("node {}: {}".format(k.upper(), v)
                                  for k, v in self.dead.items()) or "no log"),
                        invocation="(the server was gone)")
        else:
            # A node reaches here without a port OR with a port and no live
            # server, and until 2026-09-21 only the first was named: a node
            # that started and then DIED produced an empty blocker, `emit`
            # refused the row (rightly -- a not-exercised row must say why),
            # and the GateError ended the whole gate, so a run that had 40
            # outcomes in hand wrote 148 not-exercised rows instead. Both
            # reasons are named here, and the fallback is never empty.
            blocker = "; ".join(
                ["node {}: {}".format(n.name.upper(), self.node_blocker(n))
                 for n in self.nodes if not n.port]
                + ["node {}: {}".format(name.upper(), why)
                   for name, why in sorted(self.dead.items())]) or (
                "fewer than two nodes were live when the paired phases would "
                "have run, and neither a missing port nor a recorded death "
                "says which: {} of 2 live".format(len(live)))
            self.blocked(self.PAIR_KEYS + self.TRANSIT_KEYS + self.FEED_KEYS, blocker)

        self.phase("campaign", self.campaign_phase)
        self.phase("tcpcl", self.bp_phase)
        self.phase("statements", self.statements)
        self.phase("media", self.media)
        self.phase("scale", self.scale)
        self.phase("INN", self.inn)

        for node in self.nodes:
            self.stop_node(node, tag="main")
            stopped = self.steps[-1]
            release = self.sh("node {} store after the stop".format(node.upper),
                              self.cd(self.fn("--store {} status".format(node.store))),
                              timeout=900, expect=None)
            self.emit("V0-NODE-STOP",
                      ACCEPTED if (stopped.rc == 0 and release.rc == EXIT_OK)
                      else exit_verdict(release.rc), stopped.command,
                      "stop rc={}; reopening the store afterwards rc={}".format(
                          stopped.rc, release.rc),
                      node=node.name, exit_code=release.rc,
                      limit="the store reopens, which is the writer lock being gone; "
                            "no in-flight session was observed across the stop")
            self.sh("node {} log tail".format(node.upper),
                    "tail -12 {}/server-{}-main.log 2>/dev/null || echo NO-LOG".format(
                        node.dir, node.name), expect=None)
        # `anchor` and `recover` take the writer lock the service holds, so
        # the checkpoint row runs once both services are down.
        self.phase("checkpoint", self.checkpoint_row)
        self.phase("peer remove", self.peer_remove)
        self.backfill()

    # -- the two documents ---------------------------------------------------
    def document(self, started, elapsed) -> dict:
        execution = self.execution_identity()
        rows = [row.json(self.rev, execution) for row in self.rows]
        derived = derive(rows)
        rows = derived["rows"]
        summary = derived["summary"]
        clients = derived["clients"]
        by_requirement = derived["by_requirement"]
        by_scenario = derived["by_scenario"]
        features = derived["features"]
        digest = derived["rows_digest"]
        return {
            "schema_version": SCHEMA_VERSION,
            "generated_by": self.TOOL,
            "generated_at": started,
            "wall_seconds": round(elapsed, 1),
            "commit": self.commit,
            "revision": self.rev,
            "tree": self.tree,
            "host": self.host.label,
            "evidence": self.evidence_name,
            "execution": execution,
            "verdicts": list(VERDICTS),
            "outcomes": list(OUTCOMES),
            "summary": summary,
            "clients": {k: clients[k] for k in sorted(clients)},
            "fn_clients": sorted(FN_CLIENTS),
            "features": features,
            "rows": rows,
            "by_requirement": {k: by_requirement[k] for k in sorted(by_requirement)},
            "by_scenario": {k: by_scenario[k] for k in sorted(by_scenario)},
            "rows_digest": digest,
        }

    def matrix_section(self, doc) -> list:
        summary = doc["summary"]
        lines = [
            "## The v0 matrix",
            "",
            "**Execution subject.** Backend `{backend}`; deployed source `{source}`; "
            "runtime image `{image}`. These are separate labels: naming the source "
            "and hashing an externally supplied image does not prove they correspond."
            .format(**doc["execution"]),
            "",
            "{total} rows: {accepted} accepted, {refused} refused, {uncertain} "
            "uncertain, {not_exercised} not exercised, {not_built} not built; "
            "{disagreed} row(s) did not do what they were designed to do, and "
            "{faulted} exited with a host fault or usage error, which is not an "
            "outcome and is counted among the not exercised. Every count "
            "here is `{tool}`'s over the rows below, and `{json}` carries the same rows "
            "with their digest.".format(
                total=summary["total"], accepted=summary[ACCEPTED],
                refused=summary[REFUSED], uncertain=summary[UNCERTAIN],
                not_exercised=summary[NOT_EXERCISED], not_built=summary[NOT_BUILT],
                disagreed=summary["disagreed"], faulted=summary["faulted"], tool=self.TOOL,
                json=getattr(self, "_matrix_name", MATRIX_JSON)),
            "",
            "",
            "**Who saw it.** {ind} of the {outcomes} outcome rows were observed by "
            "something that is not fn's own code; {own} were observed by fn talking to "
            "fn. A feature that only fn's own client has ever seen is a weaker claim "
            "than \"usable between two peered servers\" reads, and every row carries "
            "the client that saw it in its `client` field. Clients in this run: "
            "{clients}.".format(
                ind=summary.get("independent", 0),
                own=summary.get("fn-observed", 0),
                outcomes=summary[ACCEPTED] + summary[REFUSED] + summary[UNCERTAIN],
                clients="; ".join("{} ({})".format(k, v)
                                  for k, v in doc["clients"].items()) or "none"),
            "",
            "| feature | accepted | refused | uncertain | not exercised | not built "
            "| disagreed |",
            "| --- | --- | --- | --- | --- | --- | --- |",
        ]
        for feature in doc["features"]:
            counts = feature["counts"]
            lines.append("| {} ({}) | {} | {} | {} | {} | {} | {} |".format(
                feature["title"], feature["id"], counts[ACCEPTED], counts[REFUSED],
                counts[UNCERTAIN], counts[NOT_EXERCISED], counts[NOT_BUILT],
                feature["disagreed"]))
        lines += [
            "",
            "### Every row",
            "",
            "| row | title | verdict | expected | agrees | independent | observed |",
            "| --- | --- | --- | --- | --- | --- | --- |",
        ]
        for row in doc["rows"]:
            lines.append("| `{}` | {} | **{}** | {} | {} | {} | {} |".format(
                row["id"], row["title"].replace("|", "\\|"), row["verdict"],
                row["expected"] or "-",
                {True: "yes", False: "NO", None: "-"}[row["agrees"]],
                {True: "yes", False: "fn only", None: "-"}[row["independent"]],
                str(row["observed"]).replace("|", "\\|")[:200]))
        waiting = [r for r in doc["rows"] if r["verdict"] in (NOT_EXERCISED, NOT_BUILT)]
        lines += ["", "### What every row that is not an outcome is waiting for", ""]
        if not waiting:
            lines.append("Every row produced one of the three outcomes.")
        for row in waiting:
            lines.append("- `{}` ({}): {}{}".format(
                row["id"], row["verdict"], row["blocker"],
                "" if not row["owner"] else " -- owned by `{}`".format(row["owner"])))
        lines += ["", "### What each row does not show", ""]
        for row in doc["rows"]:
            if row["limit"]:
                lines.append("- `{}`: {}".format(row["id"], row["limit"]))
        lines += ["", "### The exact invocation of every row", ""]
        for row in doc["rows"]:
            lines.append("- `{}`: `{}`".format(
                row["id"], str(row["invocation"]).replace("`", "'")[:400]))
        return lines + [""]

    def evidence(self, path, started, elapsed):
        seen, unique = set(), []
        for one in self.found:
            mark = (one.id, one.verdict, one.detail)
            if mark in seen:
                continue
            seen.add(mark)
            unique.append(one)
        self.found = unique
        doc = self.document(started, elapsed)
        self.facts["rows"] = ("{total} rows: {a} accepted, {r} refused, {u} uncertain, "
                              "{n} not exercised, {b} not built, {d} disagreed, "
                              "{f} faulted".format(
                                  total=doc["summary"]["total"],
                                  a=doc["summary"][ACCEPTED], r=doc["summary"][REFUSED],
                                  u=doc["summary"][UNCERTAIN],
                                  n=doc["summary"][NOT_EXERCISED],
                                  b=doc["summary"][NOT_BUILT],
                                  d=doc["summary"]["disagreed"],
                                  f=doc["summary"]["faulted"]))
        super().evidence(path, started, elapsed)
        text = path.read_text()
        marker = "\n## Every command\n"
        section = "\n".join(self.matrix_section(doc))
        if marker in text:
            head, _, tail = text.partition(marker)
            text = head + "\n" + section + marker + tail
        else:
            text = text + "\n" + section
        path.write_text(text)
        self.doc = doc
        return path


# --------------------------------------------------------------------------
# the inventory listing, and the check that a verdict was not typed


def render_plan() -> str:
    """The row inventory, with nothing run.  One owner for the feature list."""
    lines = ["v0 matrix inventory: {} rows over {} features".format(
        len(PLANNED_IDS), len(FEATURES)), ""]
    for fid, title in FEATURES:
        specs = [s for s in PLAN if s.feature == fid]
        count = sum(len(s.ids()) for s in specs)
        lines.append("{} {} -- {} row(s)".format(fid, title, count))
        for spec in specs:
            lines.append("  {:<28} {:<10} {:<22} {}".format(
                spec.key, spec.expected or "probe",
                ",".join(spec.requirements) + " " + ",".join(spec.scenarios),
                spec.title))
        lines.append("")
    return "\n".join(lines)


def derive(rows: list) -> dict:
    """Every counted field of a matrix document, from its rows and nothing else.

    `document` builds a run's file with this, and `add_planned_rows` rebuilds
    an existing file with it, so a summary, an index or a digest has one owner
    and no second derivation can disagree with it.
    """
    order = {rid: i for i, rid in enumerate(PLANNED_IDS)}
    rows = sorted(rows, key=lambda r: order[r["id"]])
    summary = {v: sum(1 for r in rows if r["verdict"] == v) for v in VERDICTS}
    summary["total"] = len(rows)
    summary["disagreed"] = sum(1 for r in rows if r["agrees"] is False)
    # A host fault (4) or usage error (5) is not an outcome: its row is
    # not-exercised with the code as blocker, and it is counted here so
    # the run's exit code cannot be 0 over a command that crashed.
    summary["faulted"] = sum(1 for r in rows if r["exit_code"] not in (
        None, EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN))
    summary["independent"] = sum(1 for r in rows if r["independent"] is True)
    summary["fn-observed"] = sum(1 for r in rows if r["independent"] is False)
    clients = {}
    for row in rows:
        if row["client"]:
            clients[row["client"]] = clients.get(row["client"], 0) + 1
    by_requirement, by_scenario = {}, {}
    for row in rows:
        for ident in row["requirements"]:
            by_requirement.setdefault(ident, []).append(row["id"])
        for ident in row["scenarios"]:
            by_scenario.setdefault(ident, []).append(row["id"])
    features = []
    for fid, title in FEATURES:
        mine = [r for r in rows if r["feature"] == fid]
        features.append({
            "id": fid, "title": title,
            "rows": [r["id"] for r in mine],
            "counts": {v: sum(1 for r in mine if r["verdict"] == v)
                       for v in VERDICTS},
            "disagreed": sum(1 for r in mine if r["agrees"] is False),
        })
    return {
        "rows": rows,
        "summary": summary,
        "clients": {k: clients[k] for k in sorted(clients)},
        "by_requirement": {k: by_requirement[k] for k in sorted(by_requirement)},
        "by_scenario": {k: by_scenario[k] for k in sorted(by_scenario)},
        "features": features,
        "rows_digest": hashlib.sha256(json.dumps(
            rows, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
    }


PLANNED_AFTER_THE_RUN = (
    "planned after the recorded run: this row was added to the tool's PLAN "
    "after the measurement in this file was taken, so no run has reached it "
    "on any commit. The next matrix run measures it.")


def add_planned_rows(doc: dict) -> list:
    """Give every planned id the file lacks a not-exercised row, in place.

    A planned row a run never reached is a row and not a silence, which is
    what `V0Matrix.backfill` does inside a run. The same rule holds for a row
    planned AFTER the recorded run: the file gains a row that says no
    measurement exists, never a verdict. Every counted field and the digest
    are re-derived by `derive`, the same code a run uses, so a verdict typed
    into the file by hand still does not survive.
    """
    present = {row.get("id") for row in doc.get("rows", [])}
    missing = [rid for rid in PLANNED_IDS if rid not in present]
    if not missing:
        return []
    execution = doc.get("execution")
    revision = doc.get("revision", "")
    added = []
    for rid in missing:
        for spec in PLAN:
            if rid in spec.ids():
                break
        else:  # pragma: no cover - PLANNED_IDS is built from PLAN
            raise GateError("planned id {} belongs to no spec".format(rid))
        suffix = rid.rsplit("-", 1)[-1].lower()
        node = suffix if spec.scope == "node" else None
        direction = suffix if spec.scope == "direction" else None
        row = Row(rid, spec, NOT_EXERCISED, "(none)", "(not run)", None,
                  doc.get("evidence", "planning/evidence/(pending)"), "",
                  PLANNED_AFTER_THE_RUN, None, node=node, direction=direction)
        added.append(row.json(revision, execution))
    doc.update(derive(list(doc.get("rows", [])) + added))
    return missing


def validate(doc) -> list:
    """Every way `planning/v0-matrix.json` can be wrong, including by hand.

    `make check` runs this.  The digest is the part a typed verdict cannot
    survive: change one row's word and the recorded digest no longer matches
    the rows, and no tool but this one recomputes it.
    """
    problems = []
    schema = doc.get("schema_version")
    if schema not in (LEGACY_SCHEMA_VERSION, SCHEMA_VERSION):
        problems.append("schema_version is {!r}, not legacy {} or current {}".format(
            schema, LEGACY_SCHEMA_VERSION, SCHEMA_VERSION))
    if doc.get("generated_by") != V0Matrix.TOOL:
        problems.append("generated_by is {!r}: the matrix is generated by {}, never "
                        "typed".format(doc.get("generated_by"), V0Matrix.TOOL))
    rows = doc.get("rows")
    if not isinstance(rows, list) or not rows:
        problems.append("rows is missing or empty")
        return problems
    execution = doc.get("execution")
    if schema == SCHEMA_VERSION:
        if not isinstance(execution, dict):
            problems.append("schema 2 needs an execution subject")
            execution = {}
        if execution.get("backend") not in BACKENDS:
            problems.append("execution backend {!r} is not one of {}".format(
                execution.get("backend"), list(BACKENDS)))
        for field in ("source", "image"):
            if not execution.get(field):
                problems.append("execution subject has no {}".format(field))
    digest = hashlib.sha256(json.dumps(
        rows, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    if doc.get("rows_digest") != digest:
        problems.append(
            "rows_digest does not match the rows: a row was edited by hand, or the "
            "file was written by something other than {}. Re-run it.".format(
                V0Matrix.TOOL))
    ids = [r.get("id") for r in rows]
    if len(ids) != len(set(ids)):
        problems.append("duplicate row ids")
    unplanned = sorted(set(ids) - set(PLANNED_IDS))
    if unplanned:
        problems.append("rows not in the tool's PLAN: {}".format(unplanned))
    absent = sorted(set(PLANNED_IDS) - set(ids))
    if absent:
        problems.append("planned rows missing from the file: {}".format(absent))
    for row in rows:
        rid = row.get("id")
        if row.get("verdict") not in VERDICTS:
            problems.append("{}: verdict {!r} is not one of {}".format(
                rid, row.get("verdict"), list(VERDICTS)))
        if row.get("expected") not in (None,) + OUTCOMES:
            problems.append("{}: expected {!r} is not an outcome".format(
                rid, row.get("expected")))
        agrees = row.get("agrees")
        if row.get("verdict") in OUTCOMES and row.get("expected") is not None:
            if agrees != (row["verdict"] == row["expected"]):
                problems.append("{}: agrees is {!r} but verdict/expected say {}".format(
                    rid, agrees, row["verdict"] == row["expected"]))
        elif agrees is not None:
            problems.append("{}: agrees must be null for a {} row".format(
                rid, row.get("verdict")))
        if row.get("verdict") in (NOT_EXERCISED, NOT_BUILT) and not row.get("blocker"):
            problems.append("{}: a {} row must name its blocker".format(
                rid, row.get("verdict")))
        if row.get("verdict") in OUTCOMES and not row.get("client"):
            problems.append("{}: an outcome row must name the client that observed "
                            "it".format(rid))
        if row.get("verdict") in OUTCOMES:
            want = row.get("client") not in FN_CLIENTS
            if row.get("independent") != want:
                problems.append("{}: independent is {!r} but the client is {!r}".format(
                    rid, row.get("independent"), row.get("client")))
        elif row.get("independent") is not None:
            problems.append("{}: independent must be null for a {} row".format(
                rid, row.get("verdict")))
        if row.get("verdict") in OUTCOMES and not row.get("invocation"):
            problems.append("{}: an outcome row must name its invocation".format(rid))
        if not row.get("log"):
            problems.append("{}: no log path".format(rid))
        if row.get("revision") != doc.get("revision"):
            problems.append("{}: revision {!r} is not the document's {!r}".format(
                rid, row.get("revision"), doc.get("revision")))
        if schema == SCHEMA_VERSION:
            for field in ("backend", "source", "image"):
                if row.get(field) != execution.get(field):
                    problems.append("{}: {} {!r} is not the execution subject's {!r}"
                                    .format(rid, field, row.get(field),
                                            execution.get(field)))
    summary = doc.get("summary", {})
    for verdict in VERDICTS:
        counted = sum(1 for r in rows if r.get("verdict") == verdict)
        if summary.get(verdict) != counted:
            problems.append("summary[{}] is {!r}, the rows say {}".format(
                verdict, summary.get(verdict), counted))
    if summary.get("total") != len(rows):
        problems.append("summary[total] is {!r}, there are {} rows".format(
            summary.get("total"), len(rows)))
    if summary.get("disagreed") != sum(1 for r in rows if r.get("agrees") is False):
        problems.append("summary[disagreed] does not match the rows")
    for key, want in (("independent", True), ("fn-observed", False)):
        counted = sum(1 for r in rows if r.get("independent") is want)
        if summary.get(key) != counted:
            problems.append("summary[{}] is {!r}, the rows say {}".format(
                key, summary.get(key), counted))
    for key, field in (("by_requirement", "requirements"), ("by_scenario", "scenarios")):
        rebuilt = {}
        for row in rows:
            for ident in row.get(field, []):
                rebuilt.setdefault(ident, []).append(row["id"])
        if doc.get(key) != {k: rebuilt[k] for k in sorted(rebuilt)}:
            problems.append("{} is not the index of the rows".format(key))
    return problems


def check_file(path: Path) -> list:
    if not path.is_file():
        return ["{} is missing; run `python3 {}` to generate it".format(
            path, V0Matrix.TOOL)]
    try:
        doc = json.loads(path.read_text())
    except ValueError as error:
        return ["{} is not JSON: {}".format(path, error)]
    return validate(doc)


def new_run_directory(repo: Path, revision: str) -> Path:
    """Allocate an immutable report namespace, including for concurrent runs."""
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    directory = repo / "planning/evidence/v0-runs" / (
        "{}-{}-{}".format(stamp, revision, uuid.uuid4().hex[:12]))
    directory.mkdir(parents=True, exist_ok=False)
    return directory


def write_report_once(path: Path, content: str) -> None:
    """Publish a complete report without replacing a concurrent writer's file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    name = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", dir=path.parent,
                                         prefix=".matrix-report-", delete=False) as out:
            name = out.name
            out.write(content)
            out.flush()
            os.fsync(out.fileno())
        os.link(name, path)  # Exclusive, atomic publication in the same directory.
    finally:
        if name is not None:
            os.unlink(name)


def publish_current(repo: Path, doc: dict, *, overlay: bool = False,
                    simulated: bool = False) -> None:
    """Advance the dashboard only for an explicit, current-source measurement.

    The immutable run is already written. Publication is not a passing verdict:
    failed and incomplete measurements remain useful when attributed correctly.
    The local lock serializes publishers; atomic replacement avoids partial JSON.
    """
    problems = validate(doc)
    if problems:
        raise GateError("cannot publish inconsistent matrix: " + "; ".join(problems))
    if overlay:
        raise GateError("overlaid measurements cannot replace the current matrix")
    if simulated:
        raise GateError("dry-run measurements cannot replace the current matrix")
    target = repo / MATRIX_JSON
    target.parent.mkdir(parents=True, exist_ok=True)
    # Keep the advisory lock out of the tracked planning tree.
    lockdir = repo / "build"
    lockdir.mkdir(exist_ok=True)
    with (lockdir / "v0-matrix-publish.lock").open("a") as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        current_commit, _ = resolve(repo, "HEAD")
        if doc.get("commit") != current_commit:
            raise GateError("measurement source is not this checkout's HEAD; "
                            "the immutable report remains available")
        if target.exists():
            previous = json.loads(target.read_text())
            if previous.get("generated_at", "") > doc.get("generated_at", ""):
                raise GateError("a newer matrix is already selected")
        name = None
        try:
            with tempfile.NamedTemporaryFile(mode="w", dir=target.parent,
                                             prefix=".v0-matrix-", delete=False) as out:
                name = out.name
                json.dump(doc, out, indent=2)
                out.write("\n")
                out.flush()
                os.fsync(out.fileno())
            os.replace(name, target)
        finally:
            if name is not None and os.path.exists(name):
                os.unlink(name)


# --------------------------------------------------------------------------


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("commit", nargs="?", help="the commit-ish to deploy on both nodes")
    parser.add_argument("--list", action="store_true",
                        help="print the row inventory and run nothing")
    parser.add_argument("--check", action="store_true",
                        help="validate an existing planning/v0-matrix.json and exit")
    parser.add_argument("--plan-rows", action="store_true",
                        help="give every newly planned row a not-exercised row "
                             "in planning/v0-matrix.json and exit; it records "
                             "that no run has measured them, never a verdict")
    parser.add_argument("--host", default=DEFAULT_HOST)
    parser.add_argument("--tree", default="dev", help="gate directory prefix on the host")
    parser.add_argument("--repo", default=str(ROOT))
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--evidence", default=None)
    parser.add_argument("--json", default=None, help="where the matrix JSON is written")
    parser.add_argument("--publish-current", action="store_true",
                        help="explicitly select this non-overlaid HEAD measurement "
                             "as planning/v0-matrix.json")
    parser.add_argument("--keep", action="store_true",
                        help="leave the deploy tree on the host")
    parser.add_argument("--dry-run", action="store_true",
                        help="run every script through local bash with HOME redirected")
    parser.add_argument("--home", default=None, help="the fake HOME for --dry-run")
    parser.add_argument("--acl2", default=None,
                        help="the host's ACL2 image; the default is tools/farm.py's entry")
    parser.add_argument("--overlay", action="append", default=[],
                        help="a directory copied over the deployed tree before it runs")
    parser.add_argument("--server-command", default=None,
                        help="the server entry point, with {store}, {run} and {node}")
    parser.add_argument("--backend", choices=BACKENDS, default=DEVELOPMENT_BACKEND,
                        help="runtime peers: historical development Python or the "
                             "packaged native operator")
    parser.add_argument("--native-image", default=None,
                        help="execution-host path to the saved native image")
    parser.add_argument("--native-config-a", default=None,
                        help="execution-host path to node A's preprovisioned config")
    parser.add_argument("--native-config-b", default=None,
                        help="execution-host path to node B's preprovisioned config")
    parser.add_argument("--native-group", default=GROUPS[0],
                        help="served group already present in both native stores")
    parser.add_argument("--native-developer-image", default=None,
                        help="execution-host path to a developer-profile image; the "
                             "uncertain-outcome row needs one, because the production "
                             "image refuses the cut that selects it")
    parser.add_argument("--native-image-source", default=None,
                        help="externally declared source-content digest for --native-image; "
                             "without it the native peering witness is not exercised")
    parser.add_argument("--native-runtime", default=None,
                        help="execution-host SBCL runtime path used to build/run the native image")
    parser.add_argument("--scale", action="store_true",
                        help="run tools/scale_gate.py for the scale row (hours)")
    parser.add_argument("--inn", action="store_true",
                        help="run tools/inn_lab.py on hbox for the INN row (hours)")
    parser.add_argument("--no-campaign", dest="campaign", action="store_false",
                        help="skip the process-death campaign rows")
    args = parser.parse_args(argv)

    if args.list:
        print(render_plan())
        return 0
    repo = Path(args.repo).resolve()
    if args.check:
        problems = check_file(Path(args.json) if args.json else repo / MATRIX_JSON)
        for problem in problems:
            print("ERROR: v0 matrix: {}".format(problem), file=sys.stderr)
        if problems:
            return 1
        print("v0 matrix OK: the rows match their digest, their summary and their indexes.")
        return 0
    if args.plan_rows:
        target = Path(args.json) if args.json else repo / MATRIX_JSON
        doc = json.loads(target.read_text())
        added = add_planned_rows(doc)
        if not added:
            print("v0 matrix: every planned row is already in the file.")
            return 0
        problems = validate(doc)
        if problems:
            for problem in problems:
                print("ERROR: v0 matrix: {}".format(problem), file=sys.stderr)
            return 1
        target.write_text(json.dumps(doc, indent=2) + "\n")
        print("v0 matrix: {} row(s) recorded as not-exercised: {}".format(
            len(added), ", ".join(added)))
        return 0
    if not args.commit:
        parser.error("a commit is required unless --list or --check is given")
    if args.backend == NATIVE_BACKEND:
        if args.server_command:
            parser.error("--server-command cannot replace the packaged native backend")
        missing = [name for name, value in
                   (("--native-image", args.native_image),) if not value]
        if missing:
            parser.error("{} requires {}".format(NATIVE_BACKEND, ", ".join(missing)))

    commit, rev = resolve(repo, args.commit)
    if args.dry_run:
        if args.home is None:
            parser.error("--dry-run needs --home")
        host: Host = LocalHost(Path(args.home).resolve())
    else:
        host = SshHost(args.host)
    overlays = [Path(one).resolve() for one in args.overlay]
    run_directory = new_run_directory(repo, rev)
    target = Path(args.evidence) if args.evidence else (
        run_directory / "report.md")
    json_target = Path(args.json) if args.json else run_directory / "matrix.json"
    # Custom outputs must not defeat the immutable-history rule or bypass the
    # explicit current-source publication check.
    for output in (target, json_target):
        if output.resolve() == (repo / MATRIX_JSON).resolve() or output.exists():
            parser.error("output already exists or is the current matrix: {}".format(output))
    if target.resolve() == json_target.resolve():
        parser.error("--evidence and --json must name different files")

    gate = V0Matrix(host, repo, commit, rev, args.tree,
                    overlay=overlays[0] if overlays else None,
                    jobs=args.jobs, keep=args.keep, nntplib_python="none",
                    acl2=args.acl2 or deploy_gate.FARM_HOSTS.get(
                        args.host, {}).get("acl2", "acl2"),
                    server_template=args.server_command,
                    extra_overlays=overlays[1:],
                    scale=args.scale, inn=args.inn, campaign=args.campaign,
                    backend=args.backend, native_image=args.native_image,
                    native_configs={name: config for name, config in
                                    (("a", args.native_config_a),
                                     ("b", args.native_config_b)) if config},
                    native_group=args.native_group,
                    native_image_source=args.native_image_source,
                    native_runtime=args.native_runtime,
                    native_developer_image=args.native_developer_image)
    try:
        gate._evidence_name = str(target.resolve().relative_to(repo))
    except ValueError:
        gate._evidence_name = str(target)
    try:
        gate._matrix_name = str(json_target.resolve().relative_to(repo))
    except ValueError:
        gate._matrix_name = str(json_target)

    started = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    clock = time.monotonic()
    failure = None
    try:
        gate.execute()
    except GateError as error:
        failure = str(error)
        gate.limitation(None, "the gate stopped early: {}".format(error))
        try:
            gate.backfill()
        except Exception as inner:                        # noqa: BLE001
            gate.limitation(None, "the backfill did not finish: {}".format(inner))
    finally:
        try:
            gate.cleanup()
        except Exception as error:                        # noqa: BLE001
            gate.limitation(None, "cleanup did not finish: {}: {}".format(
                type(error).__name__, error))
    elapsed = time.monotonic() - clock
    rendered = run_directory / ".rendered-report.md"
    gate.evidence(rendered, started, elapsed)
    write_report_once(target, rendered.read_text())
    rendered.unlink()
    doc = gate.doc
    write_report_once(json_target, json.dumps(doc, indent=2, sort_keys=False) + "\n")
    problems = validate(doc)
    for problem in problems:
        print("ERROR: the matrix it just wrote is not consistent: {}".format(problem),
              file=sys.stderr)
    if args.publish_current and not problems:
        try:
            publish_current(repo, doc, overlay=bool(overlays), simulated=args.dry_run)
        except GateError as error:
            problems.append(str(error))
            print("ERROR: matrix publication: {}".format(error), file=sys.stderr)

    summary = doc["summary"]
    not_run = summary[NOT_EXERCISED] + summary[NOT_BUILT]
    print("matrix: {}".format(json_target))
    if summary["faulted"]:
        print("faulted={} (host fault or usage exit codes; not outcomes, counted as "
              "not exercised, and the run exits 1 over them)".format(summary["faulted"]))
    print("evidence: {}".format(target))
    print("steps={} failed={} not-exercised={}".format(
        summary["total"], summary["disagreed"], not_run))
    for row in doc["rows"]:
        if row["agrees"] is False:
            print("  DISAGREES {} ({} expected {}): {}".format(
                row["id"], row["verdict"], row["expected"],
                str(row["observed"])[:120]))
    if failure:
        print("gate error: {}".format(failure))
        return 2
    return 1 if (summary["disagreed"] or summary["faulted"] or problems) else 0


if __name__ == "__main__":
    sys.exit(main())
