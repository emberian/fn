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
carried media, scale, INN and independent clients.  It writes
`planning/v0-matrix.json` (machine readable, indexed by requirement id and
scenario id) and `planning/evidence/v0-matrix-<date>.md`.

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
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))

import deploy_gate                                             # noqa: E402
import twonode_gate                                            # noqa: E402
from deploy_gate import (DEFAULT_HOST, EXIT_OK, EXIT_REFUSED,   # noqa: E402
                         EXIT_UNCERTAIN, GROUPS, GateError, Host, LocalHost,
                         SshHost, Step, resolve)
from twonode_gate import NodeSpec, article                      # noqa: E402

MATRIX_JSON = "planning/v0-matrix.json"
SCHEMA_VERSION = 1

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
# RFC 3977 section 3.2.1 again: the verb is not there at all.
UNSUPPORTED_CODES = frozenset(("500", "501", "502"))

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
      ("HST-003",), ("SCN-020",), ACCEPTED, "node"),
    S("V0-NODE-CONFIG", "F-NODE", "fn.toml carries [store] path and [acl2] path",
      ("HST-004",), ("SCN-020",), ACCEPTED, "node"),
    S("V0-NODE-REINIT", "F-NODE",
      "what a second fn init over a store that already holds articles does",
      ("HST-003",), ("SCN-020",), None, "node",
      "nothing in docs/operator.md says whether a second `init` adopts the store "
      "or refuses, so this row records the outcome rather than asserting one; the "
      "property that matters is the next row"),
    S("V0-NODE-REINIT-SAFE", "F-NODE",
      "the articles the store already held are still there after the second init",
      ("STO-003", "OBJ-005"), ("SCN-020",), ACCEPTED, "node"),
    S("V0-NODE-STATUS", "F-NODE", "fn status reports generation and article count",
      ("HST-002",), ("SCN-020",), ACCEPTED, "node"),
    S("V0-NODE-START", "F-NODE", "the service starts and reaches LISTENING",
      ("HST-001",), ("SCN-020",), ACCEPTED, "node"),
    S("V0-NODE-STOP", "F-NODE", "the service stops and releases the store",
      ("HST-002",), ("SCN-020",), ACCEPTED, "node"),
    S("V0-NODE-LOOPBACK", "F-NODE",
      "a non-loopback listener host is refused rather than silently bound",
      ("HST-003",), ("SCN-020",), REFUSED),

    # -- F-OUT -----------------------------------------------------------
    S("V0-OUT-ACCEPTED", "F-OUT", "an accepted post exits 0",
      ("FLR-002",), ("SCN-020",), ACCEPTED, "node"),
    S("V0-OUT-REFUSED", "F-OUT", "a lookup of an article the node does not hold exits 1",
      ("FLR-002",), ("SCN-020",), REFUSED, "node"),
    S("V0-OUT-UNCERTAIN", "F-OUT",
      "a post interrupted after publication exits 3 and fences the store",
      ("FLR-002", "STO-004"), ("SCN-003",), UNCERTAIN, "node"),
    S("V0-OUT-RECOVER", "F-OUT", "recover after the uncertain publication exits 0",
      ("STO-005",), ("SCN-003",), ACCEPTED, "node"),

    # -- F-GROUP ---------------------------------------------------------
    S("V0-GROUP-CREATE", "F-GROUP", "fn group create adds a served group",
      ("STO-001",), ("SCN-020",), ACCEPTED, "node"),
    S("V0-GROUP-SERVED", "F-GROUP", "the new group is served over the socket",
      ("NNT-006",), ("SCN-020",), ACCEPTED, "node"),
    S("V0-GROUP-RETIRE", "F-GROUP", "fn group retire removes it again",
      ("STO-001",), ("SCN-020",), ACCEPTED, "node"),
    S("V0-GROUP-UNKNOWN", "F-GROUP",
      "retiring a group the node does not serve is refused", ("STO-001",),
      ("SCN-020",), REFUSED, "node"),
    S("V0-CAP-SET", "F-GROUP", "fn capacity sets the retention capacity",
      ("RET-002",), ("SCN-007",), ACCEPTED, "node"),
    S("V0-CAP-REFUSE", "F-GROUP",
      "an article that does not fit the capacity is refused before it is written",
      ("RET-002",), ("SCN-007",), REFUSED, "node"),
    S("V0-PEER-ADD", "F-GROUP", "fn peer add writes a transit peer record",
      ("REP-001",), ("SCN-022",), ACCEPTED, "node"),
    S("V0-PEER-LIST", "F-GROUP", "fn peer list reads the record back",
      ("REP-001",), ("SCN-022",), ACCEPTED, "node"),
    S("V0-PEER-ABSENT", "F-GROUP", "fn peer remove of a peer that is not there is refused",
      ("REP-001",), ("SCN-022",), REFUSED),
    S("V0-PEER-REMOVE", "F-GROUP", "fn peer remove of a configured peer is accepted",
      ("REP-001",), ("SCN-022",), ACCEPTED),
    S("V0-CFG-LIVE", "F-GROUP",
      "a group declared on the running service's control channel reaches the served "
      "configuration", ("NNT-007",), ("SCN-020",), ACCEPTED),
    S("V0-CFG-LIVE-REFUSE", "F-GROUP",
      "an offline configuration command is refused while the service holds the store",
      ("HST-002",), ("SCN-020",), REFUSED),

    # -- F-AUTH ----------------------------------------------------------
    S("V0-AUTH-NEW", "F-AUTH", "fn principal new derives a principal id from a seed",
      ("OBJ-007",), ("SCN-021",), ACCEPTED),
    S("V0-AUTH-PASSWORD", "F-AUTH",
      "fn principal set-password records an AUTHINFO credential",
      ("OBJ-007",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-AUTH-LIST", "F-AUTH", "fn principal list shows the credential",
      ("OBJ-007",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-AUTH-ADVERTISED", "F-AUTH",
      "AUTHINFO USER is advertised while the connection is unauthenticated",
      ("NNT-001",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-AUTH-GATED", "F-AUTH", "POST before a login is refused, not performed",
      ("NNT-001",), ("SCN-021",), REFUSED, "node"),
    S("V0-AUTH-LOGIN", "F-AUTH", "AUTHINFO USER then PASS answers 281",
      ("OBJ-007",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-AUTH-WITHDRAWN", "F-AUTH",
      "AUTHINFO is no longer advertised once the connection is authenticated",
      ("NNT-001",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-AUTH-POST", "F-AUTH", "POST after the login is accepted",
      ("NNT-004",), ("SCN-021",), ACCEPTED, "node"),
    S("V0-AUTH-WRONG", "F-AUTH", "a wrong password answers 481 and grants nothing",
      ("OBJ-007",), ("SCN-021",), REFUSED, "node"),

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
    S("V0-TRANSIT-INDEPENDENT", "F-TRANSIT",
      "before any feed, each node serves its own article and 43x for the other's",
      ("OBJ-005",), ("SCN-022",), ACCEPTED, "node"),
    S("V0-TRANSIT-MODE-STREAM", "F-TRANSIT", "MODE STREAM is accepted on the peer connection",
      ("REP-001",), ("SCN-022",), ACCEPTED, "direction"),
    S("V0-TRANSIT-OFFER", "F-TRANSIT", "IHAVE of a wanted article answers 335",
      ("REP-001",), ("SCN-022",), ACCEPTED, "direction"),
    S("V0-TRANSIT-TRANSFER", "F-TRANSIT", "the transferred article is taken with 235",
      ("REP-001", "NNT-005"), ("SCN-022",), ACCEPTED, "direction"),
    S("V0-TRANSIT-IDENTICAL", "F-TRANSIT",
      "the far side serves the same octets the source served",
      ("OBJ-001",), ("SCN-022",), ACCEPTED, "direction"),
    S("V0-TRANSIT-DUPLICATE", "F-TRANSIT",
      "a second IHAVE of the same Message-ID is refused with 435",
      ("REP-002",), ("SCN-022",), REFUSED, "direction"),
    S("V0-TRANSIT-LOOP", "F-TRANSIT",
      "an article whose Path already names the target is refused after its 335",
      ("REP-002",), ("SCN-022",), REFUSED, "direction"),
    S("V0-TRANSIT-LOOP-ABSENT", "F-TRANSIT",
      "the refused loop article is not served by the target afterwards",
      ("REP-002",), ("SCN-022",), REFUSED, "direction"),
    S("V0-TRANSIT-CHECK-FRESH", "F-TRANSIT",
      "CHECK of a Message-ID the target has not seen answers 238",
      ("REP-001",), ("SCN-022",), ACCEPTED, "direction"),
    S("V0-TRANSIT-TAKETHIS", "F-TRANSIT",
      "TAKETHIS of that wanted article answers 239",
      ("REP-001",), ("SCN-022",), ACCEPTED, "direction"),
    S("V0-TRANSIT-CHECK-DUP", "F-TRANSIT",
      "CHECK of an article the target holds answers 438",
      ("REP-002",), ("SCN-022",), REFUSED, "direction"),
    S("V0-TRANSIT-TAKETHIS-DUP", "F-TRANSIT",
      "TAKETHIS that ignores that advice answers 439, never a 2xx and never a retry",
      ("REP-002",), ("SCN-022",), REFUSED, "direction"),

    # -- F-FEED ----------------------------------------------------------
    S("V0-FEED-QUEUE", "F-FEED",
      "an article accepted on the source enters the matching peer's outbound queue",
      ("REP-005",), ("SCN-023",), ACCEPTED),
    S("V0-FEED-OFFER", "F-FEED",
      "the owner opens the session and offers it, with no hand-driven socket",
      ("REP-005",), ("SCN-023",), ACCEPTED),
    S("V0-FEED-ONCE", "F-FEED", "an acknowledged transfer is not offered a second time",
      ("REP-005", "REP-002"), ("SCN-023",), ACCEPTED),
    S("V0-FEED-JOURNAL", "F-FEED",
      "the feed journal records the transfer and survives a restart",
      ("RET-003", "STO-003"), ("SCN-023",), ACCEPTED),

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
      ("HST-001",), ("SCN-024",), ACCEPTED),
    S("V0-BP-EXCHANGE", "F-BP", "one bundle each way inside one TCPCLv4 session",
      ("REP-006",), ("SCN-024",), ACCEPTED),
    S("V0-BP-REFUSED", "F-BP", "a contact the layer refuses is refused",
      ("REP-006",), ("SCN-024",), REFUSED),
    S("V0-BP-KEEPALIVE", "F-BP", "the session keepalive holds an idle contact open",
      ("FLR-004",), ("SCN-024",), ACCEPTED),
    S("V0-BP-CRASH", "F-BP", "an interrupted contact loses and duplicates nothing",
      ("FLR-004",), ("SCN-024",), ACCEPTED),
    S("V0-BP-PROFILE", "F-BP", "the session profile is the one the layer declared",
      ("REP-006",), ("SCN-024",), ACCEPTED),
    S("V0-BP-REPLAY", "F-BP", "the transfer replays from the session log",
      ("REP-006",), ("SCN-024",), ACCEPTED),
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
      ("REP-001",), ("SCN-022",), ACCEPTED),

    # -- F-CLIENT --------------------------------------------------------
    S("V0-CLIENT-NNTPLIB", "F-CLIENT",
      "an independent stdlib nntplib client reads a group and an article",
      ("NNT-002",), ("SCN-014",), ACCEPTED),
    S("V0-CLIENT-SLRN", "F-CLIENT", "slrn reads a group and an article",
      ("NNT-002",), ("SCN-014",), ACCEPTED),
)

PLAN_BY_KEY = {spec.key: spec for spec in PLAN}
PLANNED_IDS = [rid for spec in PLAN for rid in spec.ids()]
assert len(PLANNED_IDS) == len(set(PLANNED_IDS)), "duplicate row id in PLAN"


class Row:
    """One emitted row: a verdict, and everything needed to check it."""

    __slots__ = ("id", "spec", "node", "direction", "verdict", "invocation",
                 "observed", "exit_code", "log", "limit", "blocker", "owner")

    def __init__(self, rid, spec, verdict, invocation, observed, exit_code,
                 log, limit, blocker, owner, node=None, direction=None):
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

    @property
    def agrees(self):
        if self.verdict not in OUTCOMES or self.spec.expected is None:
            return None
        return self.verdict == self.spec.expected

    def json(self, revision):
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
            "invocation": self.invocation,
            "observed": self.observed,
            "exit_code": self.exit_code,
            "revision": revision,
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


def unsupported(status: str) -> bool:
    return (status or "").strip()[:3] in UNSUPPORTED_CODES


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


def exit_verdict(rc) -> str:
    """The outcome class of one exit code (D13, docs/operator.md)."""
    if rc is None:
        return NOT_EXERCISED
    return {EXIT_OK: ACCEPTED, EXIT_REFUSED: REFUSED,
            EXIT_UNCERTAIN: UNCERTAIN}.get(rc, UNCERTAIN)


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


def send_block(conn, lines):
    payload = b""
    for one in lines:
        raw = one.encode() if isinstance(one, str) else one
        payload += (b"." + raw if raw.startswith(b".") else raw) + b"\r\n"
    conn.sock.sendall(payload + b".\r\n")


def article_lines(msgid, group, subject, body, path=""):
    head = ["Path: {}!not-for-mail".format(path)] if path else []
    return head + ["From: matrix@example.invalid", "Subject: " + subject,
                   "Newsgroups: " + group, "Message-ID: " + msgid, "", body]


def labels(caps):
    return [c.split()[0].upper() for c in caps if c.strip()]


def surface(args):
    """The whole reader profile, one status line per command."""
    out = {}
    conn = Conn(args.port)
    out["greeting"] = conn.greeting
    status, caps = conn.cmd("CAPABILITIES", multiline=True)
    out["CAPABILITIES"] = status
    out["capability_lines"] = caps
    out["MODE READER"] = conn.cmd("MODE READER")[0]
    for one in ("LIST ACTIVE", "LIST NEWSGROUPS", "LIST OVERVIEW.FMT",
                "LIST ACTIVE.TIMES", "LIST HEADERS"):
        out[one] = conn.cmd(one, multiline=True)[0]
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
    split = Conn(args.port)
    split.sock.sendall(b"DAT")
    time.sleep(0.4)
    split.sock.sendall(b"E\r\n")
    out["FRAMING"] = split.line()
    out["FRAMING SAME"] = out["FRAMING"][:3] == out["DATE"][:3]
    split.close()
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
    ("STARTTLS", "STARTTLS", False),
    ("MODE-READER", "MODE READER", False),
    ("XOVER", "XOVER 1", False),
    ("XHDR", "XHDR Subject 1", False),
    ("XPAT", "XPAT Subject 1 *", False),
    ("LISTGROUP", "LISTGROUP {group}", False),
    ("CHECK", "CHECK <pin.check@matrix.example.invalid>", False),
    ("TAKETHIS", "TAKETHIS <pin.take@matrix.example.invalid>", True),
)


def pins(args):
    """Capability truthfulness, both ways round (NNT-001, RFC 3977 5.2.2).

    One connection per probe, because a 340 or a 335 puts the connection into
    a transfer and a POST is one per connection on this tree.
    """
    conn = Conn(args.port)
    status, caps = conn.cmd("CAPABILITIES", multiline=True)
    advertised = labels(caps)
    conn.close()
    answered = {}
    for label, template, opens in PROBES:
        probe = Conn(args.port)
        try:
            reply = probe.cmd(template.format(group=args.group))[0]
            answered[label] = reply
            # A command that opened a transfer is closed with an empty block
            # so the server is left in a clean state and the process is not
            # holding a half-open transfer when the next probe connects.
            if opens and reply[:1] in "34":
                probe.sock.sendall(b".\r\n")
                try:
                    answered[label + " CLOSE"] = probe.line()
                except Exception:
                    pass
        except Exception as error:
            answered[label] = "{}: {}".format(type(error).__name__, error)
        try:
            probe.close()
        except Exception:
            pass
    dispatched = [l for l, _, _ in PROBES
                  if answered.get(l, "")[:3] not in ("500", "501", "502")
                  and answered.get(l, "")[:1].isdigit()]
    out = {"advertised": advertised, "answered": answered,
           "dispatched": dispatched,
           # A label with no probe command cannot be checked either way.
           "advertised_not_dispatched": sorted(
               set(advertised) & {l for l, _, _ in PROBES} - set(dispatched)),
           "dispatched_not_advertised": sorted(set(dispatched) - set(advertised)),
           "capability_lines": caps}
    out["ok"] = not out["advertised_not_dispatched"] and not out["dispatched_not_advertised"]
    return out


def postcycle(args):
    """One POST on its own connection, with the read-back in three places."""
    out = {}
    poster = Conn(args.port)
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
    poster.close()

    fresh = Conn(args.port)
    out["FRESH ARTICLE"] = fresh.cmd("ARTICLE " + args.msgid, multiline=True)[0]
    fresh.close()

    # The duplicate, on its own connection: one clock observation is pinned per
    # connection at accept, so a second POST on the poster's connection would
    # be refused for a reason that is not duplicate suppression.
    again = Conn(args.port)
    out["DUPLICATE POST"] = again.cmd("POST")[0]
    if out["DUPLICATE POST"].startswith("340"):
        send_block(again, article_lines(args.msgid, args.group, "matrix post",
                                        "Posted by tools/v0_matrix.py."))
        out["DUPLICATE"] = again.line()
    else:
        out["DUPLICATE"] = out["DUPLICATE POST"]
    again.close()

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
    watcher = Conn(args.port)
    out["WATCHER BEFORE"] = watcher.cmd("GROUP " + args.group)[0]
    poster = Conn(args.port)
    out["POST"] = poster.cmd("POST")[0]
    if not out["POST"].startswith("340"):
        out["WATCHER MID"] = "(not attempted)"
        out["COMMIT"] = "(nothing sent)"
        out["ok"] = False
        poster.close(); watcher.close()
        return out
    poster.sock.sendall(("From: matrix@example.invalid\r\nSubject: concurrent\r\n"
                         "Newsgroups: {}\r\nMessage-ID: {}\r\n\r\nhalf a ".format(
                             args.group, args.msgid)).encode())
    out["WATCHER MID"] = watcher.cmd("GROUP " + args.group)[0]
    out["WATCHER ARTICLE MID"] = watcher.cmd("STAT", multiline=False)[0]
    poster.sock.sendall(b"letter.\r\n.\r\n")
    out["COMMIT"] = poster.line()
    out["WATCHER AFTER"] = watcher.cmd("GROUP " + args.group)[0]
    poster.close(); watcher.close()
    out["ok"] = out["WATCHER MID"].startswith("211") and out["COMMIT"].startswith("240")
    return out


def auth(args):
    """AUTHINFO (RFC 4643) and the posting permission it carries."""
    out = {}
    conn = Conn(args.port)
    status, caps = conn.cmd("CAPABILITIES", multiline=True)
    out["CAPABILITIES BEFORE"] = status
    out["advertised_before"] = labels(caps)
    out["AUTHINFO ADVERTISED"] = any(
        c.upper().startswith("AUTHINFO") for c in caps if c.strip())
    out["POST BEFORE"] = conn.cmd("POST")[0]
    if out["POST BEFORE"].startswith("340"):
        conn.sock.sendall(b".\r\n")
        out["POST BEFORE CLOSE"] = conn.line()
    out["AUTHINFO USER"] = conn.cmd("AUTHINFO USER " + args.user)[0]
    out["AUTHINFO PASS"] = conn.cmd("AUTHINFO PASS " + args.secret)[0]
    status, caps = conn.cmd("CAPABILITIES", multiline=True)
    out["CAPABILITIES AFTER"] = status
    out["advertised_after"] = labels(caps)
    out["AUTHINFO WITHDRAWN"] = not any(
        c.upper().startswith("AUTHINFO") for c in caps if c.strip())
    conn.close()

    poster = Conn(args.port)
    poster.cmd("AUTHINFO USER " + args.user)
    poster.cmd("AUTHINFO PASS " + args.secret)
    out["POST AFTER"] = poster.cmd("POST")[0]
    if out["POST AFTER"].startswith("340"):
        send_block(poster, article_lines(args.msgid, args.group, "authenticated post",
                                         "Posted after an AUTHINFO login."))
        out["POST AFTER COMMIT"] = poster.line()
    else:
        out["POST AFTER COMMIT"] = out["POST AFTER"]
    poster.close()

    wrong = Conn(args.port)
    wrong.cmd("AUTHINFO USER " + args.user)
    out["AUTHINFO WRONG"] = wrong.cmd("AUTHINFO PASS not-" + args.secret)[0]
    wrong.close()
    out["ok"] = out["AUTHINFO PASS"].startswith("281")
    return out


def stream(args):
    """The accepted CHECK/TAKETHIS path: 238 then 239 (RFC 4644 2.4, 2.5)."""
    out = {}
    source = Conn(args.from_port)
    status, lines = source.cmd("ARTICLE " + args.msgid, multiline=True)
    out["SOURCE"] = status
    source.close()
    if not status.startswith("220"):
        out["ok"] = False
        out["reason"] = "the source node does not serve " + args.msgid
        return out
    conn = Conn(args.to_port)
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
    reread = Conn(args.to_port)
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
        one.add_argument("--user", default="matrix")
        one.add_argument("--secret", default="matrix-secret")
        one.add_argument("--socket", default="")
        one.add_argument("--line", default="VERSION")
    args = parser.parse_args()
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


# --------------------------------------------------------------------------
# the gate

ART = {"a": "<alpha@a.example.invalid>", "b": "<beta@b.example.invalid>"}
STREAM = {"a": "<stream-a@example.invalid>", "b": "<stream-b@example.invalid>"}
STX = {"a": "<statement-a@example.invalid>", "b": "<statement-b@example.invalid>"}
SOCKET_POST = {"a": "<socket-a@example.invalid>", "b": "<socket-b@example.invalid>"}
AUTH_POST = {"a": "<auth-a@example.invalid>", "b": "<auth-b@example.invalid>"}
CONCURRENT_ID = "<concurrent@example.invalid>"
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
    PREAMBLE = (
        "v0 is every feature of fn usable between two peered fn nodes. This is that",
        "question asked feature by feature against one commit on one box, with five",
        "verdicts and no pass/fail collapse: accepted, refused and uncertain are the",
        "three outcomes and each is a real observation; not-exercised names what",
        "blocked the row; not-built names the lane that owns the missing feature.",
        "It establishes nothing about the books beyond which certificates ACL2 read.")
    FACT_KEYS = ("os", "kernel", "python3", "acl2version", "certificates",
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

    def __init__(self, *args, scale=False, inn=False, campaign=True, **kwargs):
        super().__init__(*args, **kwargs)
        self.want_scale = scale
        self.want_inn = inn
        self.want_campaign = campaign
        self.rows: list[Row] = []
        self.emitted: set[str] = set()
        self.support: dict = {}
        self.group_counts = {"a": 0, "b": 0}

    # -- rows -------------------------------------------------------------
    def emit(self, key, verdict, invocation, observed, *, node=None,
             direction=None, exit_code=None, log=None, limit="", blocker=None,
             owner=None) -> Row:
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
        if verdict in (NOT_EXERCISED, NOT_BUILT) and not blocker:
            raise GateError("row {}: a {} row must name its blocker".format(rid, verdict))
        row = Row(rid, spec, verdict, invocation, observed, exit_code,
                  log or self.evidence_name, limit, blocker, owner,
                  node=node, direction=direction)
        self.rows.append(row)
        self.emitted.add(rid)
        return row

    def from_step(self, key, step: Step, **kwargs) -> Row:
        """A row whose observation is a host command's exit code (D13)."""
        verdict = exit_verdict(step.rc)
        kwargs.setdefault("blocker", None)
        if verdict == NOT_EXERCISED and not kwargs["blocker"]:
            kwargs["blocker"] = step.note or "the command did not run"
        observed = "rc={} {}".format(step.rc, step.first_line or "(no output)")
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

    def cli(self, node, args) -> str:
        """The operator surface, `bin/fn`, against this node's configuration."""
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
            self.gaps.append("the {} phase raised {}: {}; every row it owns is "
                             "recorded not-exercised below".format(
                                 label, type(error).__name__, error))

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
         tcpcl-session checkpoint; do
  [ -f books/$b.cert ] && echo "cert-$b=yes" || echo "cert-$b=no"
done
grep -q 'include-book "nntp-auth"' books/served.lisp \
  && echo auth-wired=yes || echo auth-wired=no
grep -q 'fn-feed-' host/owner-host.lisp 2>/dev/null \
  && echo feed-in-owner=yes || echo feed-in-owner=no
for p in python3.9 python3.10 python3.11 python3.12; do
  command -v $p >/dev/null && $p -c 'import nntplib' 2>/dev/null \
    && echo "nntplib=$p"; done
command -v slrn >/dev/null && echo slrn=yes || echo slrn=no
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
            self.gaps.append(
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
            self.gaps.append(
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
            self.gaps.append(
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
        self.gaps.append(
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
                self.gaps.append(
                    "node {}: seeding {} exited {} ({}); the rows that offer it are "
                    "recorded against that.".format(node.upper, msgid, step.rc,
                                                    step.first_line))

    # -- F-GROUP: groups, capacity, peers, live reconfiguration -----------
    def groups_and_capacity(self, node: NodeSpec):
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
            self.blocked(("V0-PEER-ADD", "V0-PEER-LIST"), blocker, verdict=NOT_BUILT,
                         owner="w6/peering-inbound", invocation=probe.command)
            return
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
                self.gaps.append(
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
                      else exit_verdict(listing.rc), listing.command,
                      "rc={} lists {}: {}".format(listing.rc, other.name, shows),
                      node=node.name, exit_code=listing.rc,
                      limit="the name is read out of the listing's text")
            if listing.rc == EXIT_OK and not shows and add.rc == EXIT_OK:
                self.gaps.append(
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
                           limit="the secret is stored in the clear on this tree "
                                 "(BOARD OB-AUTH-DIGEST); this row is about the CLI, "
                                 "not about the secret's protection")
            listing = self.sh("node {} principal list".format(node.upper),
                              self.cd(self.cli(node, "principal list")),
                              timeout=900, expect=None)
            shows = AUTH_USER in listing.output
            self.emit("V0-AUTH-LIST",
                      ACCEPTED if (listing.rc == 0 and shows) else exit_verdict(listing.rc),
                      listing.command, "rc={} lists {}: {}".format(
                          listing.rc, AUTH_USER, shows),
                      node=node.name, exit_code=listing.rc)

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
                              "the same code for every gated verb")
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
        keys = ("V0-POST-OPEN", "V0-POST-COMMIT", "V0-POST-READBACK",
                "V0-POST-FRESH", "V0-POST-DUPLICATE")
        step = self.matrix("postcycle", "--port {} --group {} --msgid '{}'".format(
            node.port, GROUPS[0], SOCKET_POST[node.name]),
            name="node {} POST cycle".format(node.upper), expect=None)
        result = self.payload(step)
        if not result or "POST" not in result:
            self.blocked(keys, "the POST driver produced no result on node {}: {}".format(
                node.upper, result.get("error", step.first_line)),
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
        if str(result.get("COMMIT", "")).startswith("240"):
            node.accepted.append(SOCKET_POST[node.name])

    def post_concurrent(self):
        step = self.matrix("concurrent", "--port {} --group {} --msgid '{}'".format(
            self.a.port, GROUPS[0], CONCURRENT_ID),
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
        ("V0-READ-DATE", "DATE"),
        ("V0-READ-HELP", "HELP"),
        ("V0-READ-UNKNOWN", "UNKNOWN"),
    )
    READ_KEYS = tuple(k for k, _ in READ_COMMANDS) + (
        "V0-READ-NEXT", "V0-READ-LAST", "V0-READ-FRAMING")

    def read_surface(self, node: NodeSpec):
        step = self.matrix("surface", "--port {} --group {} --msgid '{}' --absent '{}'"
                           .format(node.port, GROUPS[0],
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
        step = self.matrix("pins", "--port {} --group {}".format(node.port, GROUPS[0]),
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
            self.gaps.append(
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
        for node, other in ((self.a, self.b), (self.b, self.a)):
            step = self.feed("presence", "--port {} --groups {} --present '{}' --absent '{}'"
                             .format(node.port, ",".join(GROUPS),
                                     ",".join(node.accepted),
                                     ",".join(other.accepted + node.rejected)),
                             name="independence: node {} holds its own and not {}'s"
                             .format(node.upper, other.upper), expect=None)
            result = self.payload(step)
            self.emit("V0-TRANSIT-INDEPENDENT", exit_verdict(step.rc), step.command,
                      "groups={} present={} absent={}".format(
                          result.get("groups"), result.get("present"),
                          result.get("absent")),
                      node=node.name, exit_code=step.rc,
                      limit="this is the control: every later claim that an article "
                            "reached a node rests on it")
            if step.rc != 0:
                self.gaps.append(
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
        if not offer or unsupported(offer):
            uncert = self.uncertified("peer-inbound", "served", "owner", "peer-config")
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

        `tools/run_feed.py` drives one peer's feed as a separate process; the
        v0 question is whether the OWNER does it, so the probe is whether the
        owner host calls the feed seam at all.
        """
        if not self.has("feed-in-owner"):
            blocker = ("host/owner-host.lisp names no `fn-feed-` function on this "
                       "commit, so no accepted article is offered by the owner itself; "
                       "books/peer-feed exists and tools/run_feed.py drives one peer by "
                       "hand, which is not the owner doing it")
            self.blocked(self.FEED_KEYS, blocker, verdict=NOT_BUILT,
                         owner="w10/owner-feed",
                         invocation="grep fn-feed- host/owner-host.lisp")
            return
        journal = "{}/feed-journal".format(self.a.dir)
        payload = "{}/feed.article".format(self.a.dir)
        msgid = "<feed@example.invalid>"
        self.push_file(article(msgid, GROUPS[0], "for the outbound feed",
                               "Queued for the peer by the owner."), payload)
        queued = self.sh("feed: accept an article on A", self.cd(self.fn(
            "--store {} post --message-id '{}' --payload {} --group {}".format(
                self.a.store, msgid, payload, GROUPS[0]))), timeout=900, expect=None)
        self.from_step("V0-FEED-QUEUE", queued,
                       limit="the queue is read from the journal below, not asserted "
                             "from the post's exit code alone")
        self.sh("feed: what the owner queued", self.cd(
            "ls -l {journal}/feed 2>/dev/null || echo NO-JOURNAL".format(
                journal=journal)), timeout=600, expect=None)
        presence = self.feed("presence", "--port {} --groups {} --present '{}'".format(
            self.b.port, GROUPS[0], msgid),
            name="feed: node B holds the fed article", expect=None)
        self.from_step("V0-FEED-OFFER", presence,
                       limit="no socket was driven by hand for this row: the only "
                             "observation is whether B serves the article")
        again = self.feed("presence", "--port {} --groups {} --present '{}'".format(
            self.b.port, GROUPS[0], msgid),
            name="feed: node B still holds exactly one copy", expect=None)
        self.from_step("V0-FEED-ONCE", again,
                       limit="one reread; a second copy under the same Message-ID is "
                             "not representable, so this row is weak evidence for "
                             "exactly-once and says so")
        records = self.sh("feed: the journal", self.cd(
            "ls -l {}/feed 2>/dev/null || echo NO-JOURNAL".format(journal)), expect=None)
        self.emit("V0-FEED-JOURNAL",
                  ACCEPTED if "NO-JOURNAL" not in records.output else REFUSED,
                  records.command, records.first_line or "(no output)",
                  exit_code=records.rc,
                  limit="the journal's existence and size, not its contents: the FNFD "
                        "record shapes are books/peer-feed's")
        del offered

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
                  exit_code=run.rc,
                  limit="--quick: a subset of the enumerated cuts, each a process "
                        "death, none of them a power loss")

    # -- F-BP --------------------------------------------------------------
    BP_LAB = ("exchange", "refused", "keepalive", "crash", "profile", "replay")
    BP_KEYS = {"exchange": "V0-BP-EXCHANGE", "refused": "V0-BP-REFUSED",
               "keepalive": "V0-BP-KEEPALIVE", "crash": "V0-BP-CRASH",
               "profile": "V0-BP-PROFILE", "replay": "V0-BP-REPLAY"}

    def bp_phase(self):
        build = self.sh("native image for the tcpcl layer",
                        self.cd("FN_ACL2=${FN_ACL2:-$HOME/fn-tools/acl2-8.7/saved_acl2} "
                                "nice -n 10 sh tools/build_native_host.sh 2>&1 | tail -20"),
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
                          limit="every assertion is over the event digests the two "
                                "images printed; the lab does not speak TCPCL, and the "
                                "octets it carries are opaque, not BPv7 bundles")
        self.emit("V0-BP-NODE", NOT_BUILT,
                  "tools/run_bp_ingress.py against the convergence layer",
                  "(not run)",
                  blocker="no BP node is wired behind the TCPCLv4 layer on this commit: "
                          "the layer transfers opaque octets and nothing parses a bundle "
                          "out of them into an fn article "
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
            self.gaps.append(
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
                  exit_code=step.rc,
                  limit="a measured ceiling on one box with one payload grid; it is "
                        "not a bound and not a proof")

    def inn(self):
        if not self.want_inn:
            self.emit("V0-INN-INTEROP", NOT_EXERCISED,
                      "python3 tools/inn_lab.py {} --host hbox".format(self.rev),
                      "(not run: --inn was not given)",
                      blocker="the INN install is a lab that lives on hbox at "
                              "/tank/fn/inn/2.7.4 and is not shipped; this run is on "
                              "{}, which has no INN. The last recorded run is "
                              "planning/evidence/inn-lab-f4e8272-2026-09-20.md"
                              .format(self.host.label))
            return
        step = self.sh("inn lab", self.cd(
            "python3 tools/inn_lab.py {} --host hbox 2>&1 | tail -20".format(self.rev)),
            timeout=4 * 3600, expect=None)
        self.emit("V0-INN-INTEROP", exit_verdict(step.rc), step.command,
                  " | ".join(step.output.strip().splitlines()[-3:]) or "(no output)",
                  exit_code=step.rc,
                  limit="one INN version on one box; not a Usenet conformance audit")

    def clients(self):
        interpreter = self.support.get("nntplib", "")
        if not interpreter:
            self.emit("V0-CLIENT-NNTPLIB", NOT_EXERCISED,
                      "tests/interop_store_nntplib.py", "(no interpreter)",
                      blocker="no interpreter on {} has a stdlib nntplib: PEP 594 "
                              "removed it in Python 3.13 and the box runs {}"
                              .format(self.host.label,
                                      self.facts.get("python3", "python3")))
        else:
            step = self.sh("nntplib client", self.cd(
                "{} tests/interop_store_nntplib.py --port {} --group {} 2>&1 | tail -20"
                .format(interpreter, self.a.port, GROUPS[0])), timeout=600, expect=None)
            self.emit("V0-CLIENT-NNTPLIB", exit_verdict(step.rc), step.command,
                      step.first_line or "(no output)", exit_code=step.rc,
                      limit="one client library against node A only")
        if self.support.get("slrn") != "yes":
            self.emit("V0-CLIENT-SLRN", NOT_EXERCISED, "slrn -h <host> -p <port>",
                      "(slrn is not installed)",
                      blocker="slrn is not installed on {} (nor on hbox, measured "
                              "2026-09-20); tests/interop_slrn.py has never run against "
                              "an fn node".format(self.host.label))
            return
        step = self.sh("slrn client", self.cd(
            "python3 tests/interop_slrn.py --port {} --group {} 2>&1 | tail -20".format(
                self.a.port, GROUPS[0])), timeout=900, expect=None)
        self.emit("V0-CLIENT-SLRN", exit_verdict(step.rc), step.command,
                  step.first_line or "(no output)", exit_code=step.rc,
                  limit="one newsreader against node A only")

    # -- the server entry point --------------------------------------------
    def server_candidates(self, node: NodeSpec):
        """Every entry point this commit might serve from, best first.

        `bin/fn run` is the service an operator runs, `tools/run_owner.py` is
        what it wraps, and `tools/run_reader.py` is the read-only path with no
        POST and no transit.  Which one starts is itself a v0 row, and the
        ones that did not start are the blocker the later rows cite.
        """
        if self.server_template:
            return [("custom", self.server_template.format(
                store=node.store, run=node.dir, node=node.name))]
        out = []
        if self.has("fn-run") and node.name in getattr(self, "configured", ()):
            out.append(("fn", "python3 bin/fn --config {dir}/fn.toml run "
                              "--control {dir}/control.sock".format(dir=node.dir)))
        port = getattr(node, "assigned_port", 0)
        out.append(("owner", "python3 tools/run_owner.py --store {} --port {} "
                             "--control {}/control.sock".format(
                                 node.store, port, node.dir)))
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
                                "ones above it in the list".format(kind))
            else:
                self.emit("V0-NODE-START", REFUSED,
                          " ;; ".join(a[1] for a in attempts),
                          "; ".join("{}: {}".format(a[0], a[3][:200]) for a in attempts),
                          node=node.name,
                          limit="every entry point this commit has was tried in order")
        if not started:
            return False
        node.port = self.port
        node.kind = self.selected
        node.post_enabled = ("--post" in self.commands[node.name][1]
                             or self.selected.startswith(("owner", "fn")))
        node.pid = self.sh("node {} pid".format(node.upper),
                           "cat {}/server.pid".format(node.dir)).output.strip()
        self.facts["node {}".format(node.name)] = "{} on port {} ({}), store {}".format(
            self.selected, node.port, tag, node.store)
        self.facts["server entry point"] = self.selected
        return True

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

    NODE_SOCKET_KEYS = ("V0-GROUP-SERVED", "V0-POST-OPEN", "V0-POST-COMMIT",
                        "V0-POST-READBACK", "V0-POST-FRESH", "V0-POST-DUPLICATE",
                        "V0-AUTH-ADVERTISED", "V0-AUTH-GATED", "V0-AUTH-LOGIN",
                        "V0-AUTH-WITHDRAWN", "V0-AUTH-POST", "V0-AUTH-WRONG",
                        "V0-PIN-DISPATCHED", "V0-PIN-ADVERTISED",
                        "V0-TRANSIT-INDEPENDENT")
    PAIR_KEYS = ("V0-POST-CONCURRENT", "V0-CFG-LIVE", "V0-CFG-LIVE-REFUSE",
                 "V0-CRASH-CHECKPOINT", "V0-CRASH-KILL", "V0-CRASH-SURVIVOR",
                 "V0-CRASH-RECOVER", "V0-CRASH-ACKNOWLEDGED",
                 "V0-CRASH-INTERRUPTED", "V0-CRASH-RESTART",
                 "V0-CLIENT-NNTPLIB", "V0-CLIENT-SLRN", "V0-STX-CROSS")

    # -- the whole gate -----------------------------------------------------
    def execute(self):
        self.configured = set()
        self.preflight()
        self.a.assigned_port = self.b.assigned_port = 0
        self.ship()
        self.push_file(twonode_gate.FEED_DRIVER, "{}/feed.py".format(self.run), mode="755")
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

        for node in self.nodes:
            self.start_node(node)
        if self.a.port and self.b.port and self.a.port == self.b.port:
            raise GateError("both nodes reported the same port; they are one server")

        for node in self.nodes:
            if not node.port:
                self.blocked(self.NODE_SOCKET_KEYS, self.node_blocker(node),
                             nodes=(node.name,))
                continue
            self.phase("group served {}".format(node.name), self.group_served, node)
            self.phase("reader surface {}".format(node.name), self.read_surface, node)
            self.phase("capability pins {}".format(node.name), self.capability_pins, node)
            self.phase("AUTHINFO {}".format(node.name), self.auth_session, node)
            self.phase("POST cycle {}".format(node.name), self.post_cycle, node)

        if self.a.port and self.b.port:
            self.phase("independence", self.independence)
            self.phase("transit AB", self.transit_direction, self.a, self.b, "ab")
            self.phase("transit BA", self.transit_direction, self.b, self.a, "ba")
            self.phase("concurrency", self.post_concurrent)
            self.phase("live reconfiguration", self.live_reconfiguration)
            self.phase("outbound feed", self.outbound_feed)
            self.phase("checkpoint", self.checkpoint_row)
            self.phase("clients", self.clients)
            self.phase("crash", self.crash_phase)
        else:
            blocker = "; ".join(self.node_blocker(n) for n in self.nodes if not n.port)
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
        self.phase("peer remove", self.peer_remove)
        self.backfill()

    # -- the two documents ---------------------------------------------------
    def document(self, started, elapsed) -> dict:
        rows = [row.json(self.rev) for row in self.rows]
        order = {rid: i for i, rid in enumerate(PLANNED_IDS)}
        rows.sort(key=lambda r: order[r["id"]])
        summary = {v: sum(1 for r in rows if r["verdict"] == v) for v in VERDICTS}
        summary["total"] = len(rows)
        summary["disagreed"] = sum(1 for r in rows if r["agrees"] is False)
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
        digest = hashlib.sha256(json.dumps(
            rows, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
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
            "verdicts": list(VERDICTS),
            "outcomes": list(OUTCOMES),
            "summary": summary,
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
            "{total} rows: {accepted} accepted, {refused} refused, {uncertain} "
            "uncertain, {not_exercised} not exercised, {not_built} not built; "
            "{disagreed} row(s) did not do what they were designed to do. Every count "
            "here is `{tool}`'s over the rows below, and `{json}` carries the same rows "
            "with their digest.".format(
                total=summary["total"], accepted=summary[ACCEPTED],
                refused=summary[REFUSED], uncertain=summary[UNCERTAIN],
                not_exercised=summary[NOT_EXERCISED], not_built=summary[NOT_BUILT],
                disagreed=summary["disagreed"], tool=self.TOOL, json=MATRIX_JSON),
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
            "| row | title | verdict | expected | agrees | observed |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
        for row in doc["rows"]:
            lines.append("| `{}` | {} | **{}** | {} | {} | {} |".format(
                row["id"], row["title"].replace("|", "\\|"), row["verdict"],
                row["expected"] or "-",
                {True: "yes", False: "NO", None: "-"}[row["agrees"]],
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
        for gap in self.gaps:
            if gap not in seen:
                seen.add(gap)
                unique.append(gap)
        self.gaps = unique
        doc = self.document(started, elapsed)
        self.facts["rows"] = ("{total} rows: {a} accepted, {r} refused, {u} uncertain, "
                              "{n} not exercised, {b} not built, {d} disagreed".format(
                                  total=doc["summary"]["total"],
                                  a=doc["summary"][ACCEPTED], r=doc["summary"][REFUSED],
                                  u=doc["summary"][UNCERTAIN],
                                  n=doc["summary"][NOT_EXERCISED],
                                  b=doc["summary"][NOT_BUILT],
                                  d=doc["summary"]["disagreed"]))
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


def validate(doc) -> list:
    """Every way `planning/v0-matrix.json` can be wrong, including by hand.

    `make check` runs this.  The digest is the part a typed verdict cannot
    survive: change one row's word and the recorded digest no longer matches
    the rows, and no tool but this one recomputes it.
    """
    problems = []
    if doc.get("schema_version") != SCHEMA_VERSION:
        problems.append("schema_version is {!r}, not {}".format(
            doc.get("schema_version"), SCHEMA_VERSION))
    if doc.get("generated_by") != V0Matrix.TOOL:
        problems.append("generated_by is {!r}: the matrix is generated by {}, never "
                        "typed".format(doc.get("generated_by"), V0Matrix.TOOL))
    rows = doc.get("rows")
    if not isinstance(rows, list) or not rows:
        problems.append("rows is missing or empty")
        return problems
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
        if row.get("verdict") in OUTCOMES and not row.get("invocation"):
            problems.append("{}: an outcome row must name its invocation".format(rid))
        if not row.get("log"):
            problems.append("{}: no log path".format(rid))
        if row.get("revision") != doc.get("revision"):
            problems.append("{}: revision {!r} is not the document's {!r}".format(
                rid, row.get("revision"), doc.get("revision")))
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


# --------------------------------------------------------------------------


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("commit", nargs="?", help="the commit-ish to deploy on both nodes")
    parser.add_argument("--list", action="store_true",
                        help="print the row inventory and run nothing")
    parser.add_argument("--check", action="store_true",
                        help="validate an existing planning/v0-matrix.json and exit")
    parser.add_argument("--host", default=DEFAULT_HOST)
    parser.add_argument("--tree", default="dev", help="gate directory prefix on the host")
    parser.add_argument("--repo", default=str(ROOT))
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--evidence", default=None)
    parser.add_argument("--json", default=None, help="where the matrix JSON is written")
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
    if not args.commit:
        parser.error("a commit is required unless --list or --check is given")

    commit, rev = resolve(repo, args.commit)
    if args.dry_run:
        if args.home is None:
            parser.error("--dry-run needs --home")
        host: Host = LocalHost(Path(args.home).resolve())
    else:
        host = SshHost(args.host)
    overlays = [Path(one).resolve() for one in args.overlay]
    date = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d")
    target = Path(args.evidence) if args.evidence else (
        repo / "planning/evidence/v0-matrix-{}.md".format(date))
    json_target = Path(args.json) if args.json else repo / MATRIX_JSON

    gate = V0Matrix(host, repo, commit, rev, args.tree,
                    overlay=overlays[0] if overlays else None,
                    jobs=args.jobs, keep=args.keep, nntplib_python="none",
                    acl2=args.acl2 or deploy_gate.FARM_HOSTS.get(
                        args.host, {}).get("acl2", "acl2"),
                    server_template=args.server_command,
                    extra_overlays=overlays[1:],
                    scale=args.scale, inn=args.inn, campaign=args.campaign)
    try:
        gate._evidence_name = str(target.resolve().relative_to(repo))
    except ValueError:
        gate._evidence_name = str(target)

    started = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    clock = time.monotonic()
    failure = None
    try:
        gate.execute()
    except GateError as error:
        failure = str(error)
        gate.gaps.append("the gate stopped early: {}".format(error))
        try:
            gate.backfill()
        except Exception as inner:                        # noqa: BLE001
            gate.gaps.append("the backfill did not finish: {}".format(inner))
    finally:
        try:
            gate.cleanup()
        except Exception as error:                        # noqa: BLE001
            gate.gaps.append("cleanup did not finish: {}: {}".format(
                type(error).__name__, error))
    elapsed = time.monotonic() - clock
    gate.evidence(target, started, elapsed)
    doc = gate.doc
    json_target.parent.mkdir(parents=True, exist_ok=True)
    json_target.write_text(json.dumps(doc, indent=2, sort_keys=False) + "\n")
    problems = validate(doc)
    for problem in problems:
        print("ERROR: the matrix it just wrote is not consistent: {}".format(problem),
              file=sys.stderr)

    summary = doc["summary"]
    not_run = summary[NOT_EXERCISED] + summary[NOT_BUILT]
    print("matrix: {}".format(json_target))
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
    return 1 if (summary["disagreed"] or problems) else 0


if __name__ == "__main__":
    sys.exit(main())
