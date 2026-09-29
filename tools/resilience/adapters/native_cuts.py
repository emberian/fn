"""The native cut campaigns as scenarios (design §1, rows W7b and W7c).

Four families, one scenario per cut, all run by the same recorder:

  post             `store post' killed at each POST_LOG_CUTS cut (W7b): the
                   candidate's fate at the cut, recovery, reads, the retry.
  recovery         crash DURING recovery (W7c, GPT-6's family): a torn
                   candidate is left (a death at log-written of a batch of
                   one), the real recovery is started and killed at a
                   RECOVERY_CUTS cut or at the log's own recover cuts
                   (log-truncated, log-recovered), its writes are recorded
                   (the store's file listing before and after), recovery
                   runs again, and the original commitments are checked.
  served           the served owner killed at each POST_LOG_CUTS cut while
                   a two-group POST is in flight on the NNTP listener (W7c):
                   the cut's SERVED column applies (native_cuts.POST_LOG_CUTS,
                   the member of the owner's quantum), the reply is lost,
                   `operator recover' heals, and the memberships are observed
                   through LISTGROUP on the restarted node (STAT names each
                   number's Message-ID), the bytes through ARTICLE; the retry
                   is reconciled through the store verb (a served POST's reply
                   does not name a duplicate: an ask in the LANEDUMP).
  served-recovery  the owner's own open killed at each recovery barrier
                   over a torn candidate (W7c), then the same healing.
  checkpoint       `store checkpoint' killed at each STATE_CHECKPOINT_CUTS
                   cut (the review's "new checkpoint prepared" point): which
                   whole checkpoint the next open reads is an environment
                   fact judged by the cut's column; the served state is the
                   same either way.

Every family records what the client saw, what the environment did and,
where the image decides, what its own scan says, into a journal written
OUTSIDE the store; the verdict is `checker.check`'s, and the healing phase
is timed against the scenario's declared bound.

    python3 -m tools.resilience.adapters.native_cuts --image build/fn-host-developer \
        [--family post|recovery|served|served-recovery|checkpoint|all] [--cut NAME] \
        [--out DIR] [--no-fault]

`--no-fault` runs with the fault hook disabled: the tester's own test on the
box (the verdict must be harness-failure:fault-never-occurred).
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tests.campaign import native_cuts  # noqa: E402
from tests.campaign import native_operator_campaign as campaign  # noqa: E402
from tests import native_log_observation  # noqa: E402
from tools.resilience.scenario import (  # noqa: E402
    Scenario, Operation, Fault, boundary_registry, check as check_scenario)
from tools.resilience.journal import Journal  # noqa: E402
from tools.resilience import checker  # noqa: E402

GROUP = "fn.letters"
GROUP2 = "fn.replies"
PRIOR = "post-prior"
CANDIDATE = "post-candidate"
ORPHAN_BOUNDARY = "log-written"       # a batch of one torn here: either
ACTORS = [{"name": "client", "kind": "client"}, {"name": "nemesis", "kind": "nemesis"}]
REQUIREMENTS = ["STO-002", "OBJ-005"]
FAULT_SELECTORS = ("FN_NATIVE_POST_FAULT", "FN_NATIVE_LOG_FAULT", "FN_NATIVE_RECOVERY_FAULT",
                   "FN_NATIVE_STATE_CHECKPOINT_FAULT", "FN_NATIVE_RECLAIM_FAULT")


def healing_bound() -> dict:
    return {"kind": "experimental", "value": 120.0,
            "source": "docs/resource-contract.md declares no wall-time bound for recovery "
                      "(its bounds are per scheduling step); an experimental budget "
                      "(design §7) until the contract names one"}


def mid(op_id: str) -> str:
    return "<{}@resilience.invalid>".format(op_id)


def article(message_id: str, subject: str, body: str, groups) -> bytes:
    return ("From: resilience@resilience.invalid\r\nNewsgroups: {}\r\n"
            "Subject: {}\r\nMessage-ID: {}\r\n\r\n{}\r\n").format(
                ",".join(groups), subject, message_id, body).encode("ascii")


# ---------------------------------------------------------------- scenarios

# The offline per-group observation (row S3d, lane operability-5): `store
# ROOT inspect --group GROUP` prints `inspect group=G members=N` then one
# `NUMBER <Message-ID>` line per member in number order, with no owner
# running; a group the store does not carry is refused by name.  An image
# that predates the verb answers otherwise, and the run is then a harness
# failure by that name (the test marks the offline observation pending).
OFFLINE_MEMBERSHIP_VERB = ("inspect", "--group")
OFFLINE_MEMBERSHIP_SOURCE = "lane/operability-2 d72e3781a (docs/operator.md 'Which articles are in a group?')"


def _offline_listing(groups) -> list:
    return [Operation("list-" + g.split(".")[-1], "client", "list-group", {"group": g})
            for g in groups]


def scenario_for(cut, memberships: bool = False) -> Scenario:
    """W7b: `store post' killed at CUT.  With MEMBERSHIPS the candidate
    names two groups and both are listed offline after recovery (the
    fracture tooth on the offline route)."""
    groups = [GROUP, GROUP2] if memberships else [GROUP]
    listing = _offline_listing(groups) if memberships else []
    return check_scenario(Scenario(
        id="native-cut-" + cut.name + ("-memberships" if memberships else ""),
        title="store post killed at {} ({}): the candidate's fate and its retry".format(
            cut.name, cut.program),
        requirements=REQUIREMENTS, contract="local-commit-log",
        initial={"recipe": "empty-store", "groups": groups, "prior": []},
        actors=ACTORS,
        operations=[
            Operation(PRIOR, "client", "post", {"groups": [GROUP], "payload": "prior"}),
            Operation(CANDIDATE, "client", "post", {"groups": groups, "payload": "candidate"}),
            Operation("recover", "client", "recover"),
        ] + listing + [
            Operation("read-prior", "client", "read", {"article": PRIOR}),
            Operation("read-candidate", "client", "read", {"article": CANDIDATE}),
            Operation("retry-candidate", "client", "retry", {"of": CANDIDATE}),
        ],
        faults=[Fault(CANDIDATE, cut.name, "kill", "contract-admissible", "persisted",
                      "store-post")],
        healing=["recover"] + [o.id for o in listing]
        + ["read-prior", "read-candidate", "retry-candidate"],
        witnesses=["post-accepted", "retry-reconciled", "read-completed",
                   "recovery-completed"] + (["memberships-listed"] if memberships else []),
        healing_bound=healing_bound(), replay="exact"))


def recovery_cuts() -> list:
    """Where a recovery can be killed: fn-lg-open-program's cuts and the
    staging sweep's (RECOVERY_CUTS), and the log's own recover program's
    (LOG_CUTS: log-truncated, log-recovered)."""
    return list(native_cuts.RECOVERY_CUTS) + [
        c for c in native_cuts.LOG_CUTS if c.program == "fn-lg-recover-program"]


def recovery_scenario_for(cut, memberships: bool = False) -> Scenario:
    """W7c: recovery killed at CUT over a torn candidate; recovery again;
    the original commitments (with MEMBERSHIPS, both groups listed offline)."""
    groups = [GROUP, GROUP2] if memberships else [GROUP]
    listing = _offline_listing(groups) if memberships else []
    return check_scenario(Scenario(
        id="native-recovery-" + cut.name + ("-memberships" if memberships else ""),
        title="recovery killed at {} ({}) over a torn candidate: the history is kept, "
              "the second recovery completes, the commitments hold".format(
                  cut.name, cut.program),
        requirements=REQUIREMENTS, contract="local-commit-log",
        initial={"recipe": "orphan-then-recover", "groups": groups, "prior": []},
        actors=ACTORS,
        operations=[
            Operation(PRIOR, "client", "post", {"groups": [GROUP], "payload": "prior"}),
            Operation(CANDIDATE, "client", "post", {"groups": groups, "payload": "orphan"}),
            Operation("recover-killed", "client", "recover"),
            Operation("recover", "client", "recover"),
        ] + listing + [
            Operation("read-prior", "client", "read", {"article": PRIOR}),
            Operation("read-candidate", "client", "read", {"article": CANDIDATE}),
            Operation("retry-candidate", "client", "retry", {"of": CANDIDATE}),
        ],
        faults=[Fault(CANDIDATE, ORPHAN_BOUNDARY, "kill", "contract-admissible", "persisted",
                      "store-post"),
                Fault("recover-killed", cut.name, "kill", "contract-admissible", "persisted")],
        healing=["recover"] + [o.id for o in listing]
        + ["read-prior", "read-candidate", "retry-candidate"],
        witnesses=["post-accepted", "retry-reconciled", "read-completed",
                   "recovery-completed"] + (["memberships-listed"] if memberships else []),
        healing_bound=healing_bound(), replay="exact"))


def _served_tail() -> list:
    return [Operation("recover", "client", "recover"),
            Operation("list-letters", "client", "list-group", {"group": GROUP}),
            Operation("list-replies", "client", "list-group", {"group": GROUP2}),
            Operation("read-prior", "client", "read", {"article": PRIOR}),
            Operation("read-candidate", "client", "read", {"article": CANDIDATE}),
            Operation("retry-candidate", "client", "retry", {"of": CANDIDATE})]


SERVED_HEALING = ["recover", "list-letters", "list-replies", "read-prior", "read-candidate",
                  "retry-candidate"]
SERVED_WITNESSES = ["post-accepted", "retry-reconciled", "read-completed",
                    "recovery-completed", "memberships-listed"]


def served_scenario_for(cut) -> Scenario:
    """W7c: the served owner killed at CUT with a two-group POST in flight;
    memberships observed through LISTGROUP on the restarted node."""
    return check_scenario(Scenario(
        id="native-served-" + cut.name,
        title="served owner killed at {} ({}) with a two-group POST in flight: the reply is "
              "lost, recovery heals, LISTGROUP shows both memberships or neither".format(
                  cut.name, cut.program),
        requirements=REQUIREMENTS, contract="local-commit-log",
        initial={"recipe": "served-node", "groups": [GROUP, GROUP2], "prior": []},
        actors=ACTORS,
        operations=[
            Operation(PRIOR, "client", "post", {"groups": [GROUP], "payload": "prior",
                                                "route": "served-post"}),
            Operation(CANDIDATE, "client", "post", {"groups": [GROUP, GROUP2],
                                                    "payload": "candidate",
                                                    "route": "served-post"}),
        ] + _served_tail(),
        faults=[Fault(CANDIDATE, cut.name, "kill", "contract-admissible", "persisted",
                      "served-post")],
        healing=list(SERVED_HEALING), witnesses=list(SERVED_WITNESSES),
        healing_bound=healing_bound(), replay="exact"))


def served_recovery_cuts() -> list:
    return [c for c in native_cuts.RECOVERY_CUTS if c.model_name == "recover-barrier"]


def served_recovery_scenario_for(cut) -> Scenario:
    """W7c: the owner's own open (its recovery) killed at CUT over a torn
    candidate; `operator recover' heals; the restarted node is observed."""
    return check_scenario(Scenario(
        id="native-served-recovery-" + cut.name,
        title="owner open killed at {} ({}) over a torn candidate: the history is kept, "
              "operator recover completes, the restarted node serves it".format(
                  cut.name, cut.program),
        requirements=REQUIREMENTS, contract="local-commit-log",
        initial={"recipe": "served-node", "groups": [GROUP, GROUP2], "prior": []},
        actors=ACTORS,
        operations=[
            Operation(PRIOR, "client", "post", {"groups": [GROUP], "payload": "prior",
                                                "route": "served-post"}),
            Operation(CANDIDATE, "client", "post", {"groups": [GROUP, GROUP2],
                                                    "payload": "orphan",
                                                    "route": "store-post"}),
            Operation("restart-killed", "client", "restart"),
        ] + _served_tail(),
        faults=[Fault(CANDIDATE, ORPHAN_BOUNDARY, "kill", "contract-admissible", "persisted",
                      "store-post"),
                Fault("restart-killed", cut.name, "kill", "contract-admissible", "persisted")],
        healing=list(SERVED_HEALING), witnesses=list(SERVED_WITNESSES),
        healing_bound=healing_bound(), replay="exact"))


CHECKPOINT_POSTS = ["post-{}".format(n) for n in range(1, 6)]


def checkpoint_scenario_for(cut) -> Scenario:
    """The review's "new checkpoint prepared" point: `store checkpoint'
    killed at CUT after three records were checkpointed and two more
    appended; which checkpoint the open reads is the cut's column."""
    posts = [Operation(p, "client", "post", {"groups": [GROUP], "payload": p})
             for p in CHECKPOINT_POSTS]
    reads = [Operation("read-" + p, "client", "read", {"article": p}) for p in CHECKPOINT_POSTS]
    return check_scenario(Scenario(
        id="native-checkpoint-" + cut.name,
        title="store checkpoint killed at {} ({}): the open reads one whole checkpoint "
              "({}), recovery sweeps, the served state is the full replay's".format(
                  cut.name, cut.program, cut.candidate),
        requirements=REQUIREMENTS, contract="local-commit-log",
        initial={"recipe": "checkpoint-at-three", "groups": [GROUP], "prior": []},
        actors=ACTORS,
        operations=posts[:3] + [Operation("checkpoint-1", "client", "checkpoint")]
        + posts[3:] + [Operation("checkpoint-killed", "client", "checkpoint"),
                       Operation("status-after", "client", "status"),
                       Operation("recover", "client", "recover")]
        + reads + [Operation("retry-5", "client", "retry", {"of": "post-5"}),
                   Operation("checkpoint-2", "client", "checkpoint"),
                   Operation("status-final", "client", "status")],
        faults=[Fault("checkpoint-killed", cut.name, "kill", "contract-admissible",
                      "persisted")],
        healing=["recover"] + [r.id for r in reads] + ["retry-5", "checkpoint-2",
                                                        "status-final"],
        witnesses=["post-accepted", "read-completed", "retry-reconciled",
                   "recovery-completed", "checkpoint-installed"],
        healing_bound=healing_bound(), replay="exact"))


def scenarios() -> list:
    return [scenario_for(cut) for cut in native_cuts.POST_LOG_CUTS]


FAMILIES = {
    "post": lambda: [scenario_for(c) for c in native_cuts.POST_LOG_CUTS],
    "recovery": lambda: [recovery_scenario_for(c) for c in recovery_cuts()],
    "served": lambda: [served_scenario_for(c) for c in native_cuts.POST_LOG_CUTS],
    "served-recovery": lambda: [served_recovery_scenario_for(c) for c in served_recovery_cuts()],
    "checkpoint": lambda: [checkpoint_scenario_for(c) for c in native_cuts.STATE_CHECKPOINT_CUTS],
}


def family_scenarios(name: str) -> list:
    if name == "all":
        return [s for f in FAMILIES for s in FAMILIES[f]()]
    return FAMILIES[name]()


# ----------------------------------------------------------------- the box

class HarnessFailure(Exception):
    """The run could not make its observation (a node that did not come up,
    an unanswered read): named, never a contract verdict."""


def fault_env(registry: dict, fault: Fault, op_kind: str) -> dict:
    """The developer selector that fires FAULT for an operation of OP_KIND."""
    entry = registry[fault.boundary]
    selector = "FN_NATIVE_POST_FAULT" if op_kind == "post" else entry["selector"]
    name = entry.get("selector_name", fault.boundary)
    if selector == "FN_NATIVE_LOG_FAULT":
        return {selector: name}
    return {selector: "{}:{}".format(name, fault.action)}


def _invoke(image, store, command, *arguments, env=None, cwd=ROOT):
    host_env = dict(os.environ)
    for k in FAULT_SELECTORS:
        host_env.pop(k, None)
    host_env.update(env or {})
    return subprocess.run([str(image), "--fn", "store", str(store), command, *map(str, arguments)],
                          cwd=cwd, env=host_env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          check=False)


def _reply_outcome(result) -> str:
    if result.returncode == -9:
        return "lost"
    if result.returncode == 0 and (b"committed sequence=" in result.stdout
                                   or b"duplicate" in result.stdout):
        return "duplicate" if b"duplicate" in result.stdout else "accepted"
    return "refused"


def served_matches(served: bytes, payload: bytes) -> bool:
    """The served copy of PAYLOAD: the stored article (the payload with the
    owner's injected fields ahead of its header: campaign.injected_from) as
    ARTICLE serves it, with the served-time `Xref` (RFC 3977 §6.2.1) ahead
    of that.  Xref is served, never stored, so it is dropped before the
    stored-bytes comparison; nothing else is normalized."""
    while served.lower().startswith(b"xref:"):
        served = served.split(b"\r\n", 1)[1] if b"\r\n" in served else b""
    return campaign.injected_from(served, payload)


def _served_outcome(first: bytes, final) -> tuple:
    """(outcome, status) of a served POST: 240 accepted; the 441 that names
    the stored article a duplicate; a closed connection a lost reply."""
    if final is None:
        return ("lost" if first == b"" else "refused"), first
    if final.startswith(b"240"):
        return "accepted", final
    if final == b"":
        return "lost", first
    if final.startswith(b"441") and b"already stored" in final:
        return "duplicate", final
    return "refused", final


def _snapshot(store: Path) -> dict:
    out = {}
    for p in sorted(store.rglob("*")):
        if p.is_file():
            st = p.stat()
            out[str(p.relative_to(store))] = [st.st_size, st.st_mtime_ns]
    return out


class Nntp:
    """One connection to the node's listener, octets in and out."""

    def __init__(self, port: int, timeout: float = 60.0):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=timeout)
        self.f = self.sock.makefile("rb")
        self.greeting = self.f.readline()

    def command(self, text: str) -> bytes:
        self.sock.sendall(text.encode("ascii") + b"\r\n")
        return self.f.readline()

    def block(self) -> list:
        lines = []
        while True:
            line = self.f.readline()
            if line in (b".\r\n", b""):
                return lines
            lines.append(line[1:] if line.startswith(b"..") else line)

    def multiline(self, text: str) -> tuple:
        status = self.command(text)
        return status, (self.block() if status[:1] in (b"1", b"2") and status[:3] != b"111"
                        else [])

    def post(self, octets: bytes) -> tuple:
        first = self.command("POST")
        if not first.startswith(b"340"):
            return first, None
        stuffed = b"".join((b"." + ln if ln.startswith(b".") else ln) + b"\r\n"
                           for ln in octets.split(b"\r\n") if True)
        self.sock.sendall(stuffed.rstrip(b"\r\n") + b"\r\n.\r\n")
        return first, self.f.readline()

    def close(self):
        try:
            self.sock.sendall(b"QUIT\r\n")
        except OSError:
            pass
        self.f.close()
        self.sock.close()


class Run:
    """One scenario on IMAGE under WORK: the recorder every family shares."""

    def __init__(self, scenario: Scenario, image: Path, work: Path, fault_hook: bool = True):
        # Absolute: the served node runs its verbs with its own directory as cwd.
        self.s, self.image, self.work = scenario, Path(image).resolve(), Path(work).resolve()
        self.hook = fault_hook
        self.registry = boundary_registry()
        self.j = Journal(scenario.id)
        self.store = self.work / "store"
        self.payloads, self.symbols = {}, {}
        self.node = None
        for o in scenario.posts():
            p = self.work / (o.id + ".payload")
            if scenario.initial["recipe"] == "served-node":
                p.write_bytes(article(mid(o.id), o.id, o.args["payload"] + " protected content",
                                      o.args["groups"]))
            else:
                p.write_bytes("{} protected content".format(o.args["payload"]).encode())
            self.payloads[o.id] = p
            self.symbols[mid(o.id)] = o.id
            self.j.bind(o.id, mid(o.id))

    # -- shared
    def fault_for(self, op: Operation):
        f = self.s.fault_on(op.id)
        return f if (f and self.hook) else None

    def fired(self, op: Operation, fault: Fault, evidence: str):
        self.j.environment("fault-fired", operation=op.id, boundary=fault.boundary,
                           action=fault.action, route=fault.route, evidence=evidence)

    def scan(self, phase: str):
        h = native_log_observation.committed_history(self.image, self.store, cwd=ROOT)
        self.j.environment("persisted-records", count=len(h), last=h.last, phase=phase,
                           source="log scan-store")

    def invoke(self, command, *arguments, env=None):
        return _invoke(self.image, self.store, command, *arguments, env=env)

    def store_post(self, op: Operation, env=None, route="store-post"):
        r = self.invoke("post", mid(op.id), self.payloads[op.id], "-", "-", *op.args["groups"],
                        env=env)
        self.j.client("reply", operation=op.id, outcome=_reply_outcome(r), route=route,
                      returncode=r.returncode)
        return r

    def store_retry(self, op: Operation):
        of = self.s.operation(op.args["of"])
        r = self.invoke("post", mid(of.id), self.payloads[of.id], "-", "-", *of.args["groups"])
        self.j.client("reply", operation=op.id, outcome=_reply_outcome(r), route="store-post",
                      returncode=r.returncode)

    def store_read(self, op: Operation):
        art = op.args["article"]
        r = self.invoke("inspect", mid(art))
        if r.returncode == 0:
            result = "match" if r.stdout == self.payloads[art].read_bytes() else "other"
        else:
            result = "absent"
        self.j.client("read", operation=op.id, article=art, result=result, route="store")

    def store_list(self, op: Operation):
        """The offline per-group observation through `store inspect --group`."""
        group = op.args["group"]
        r = self.invoke(*OFFLINE_MEMBERSHIP_VERB, group)
        head = r.stdout.split(b"\n", 1)[0]
        if r.returncode != 0 or not head.startswith(b"inspect group="):
            raise HarnessFailure("inspect-group-unavailable:rc={}:{}".format(
                r.returncode, (r.stderr or r.stdout).decode("utf-8", "replace").strip()[:120]))
        numbers, members = [], []
        for line in r.stdout.decode("ascii", "replace").splitlines()[1:]:
            words = line.split()
            if len(words) == 2 and words[0].isdigit():
                numbers.append(int(words[0]))
                members.append(self.symbols.get(words[1], words[1]))
        self.j.client("list-group", operation=op.id, group=group, members=members,
                      numbers=numbers, route="store", head=head.decode("ascii", "replace"))

    def recover(self, op: Operation, phase: str, env=None, verb="store"):
        started = time.monotonic()
        if verb == "operator":
            r = self.node.run(["operator", str(self.node.config), "recover"], env)
            rc, out = r["rc"], r["_out"]
        else:
            res = self.invoke("recover", env=env)
            rc, out = res.returncode, res.stdout
        outcome = ("lost" if rc == -9 else
                   "completed" if rc == 0 and campaign.parse_recover(out) is not None
                   else "failed")
        self.j.client("recover", operation=op.id, outcome=outcome, phase=phase,
                      returncode=rc, seconds=round(time.monotonic() - started, 3),
                      counts=campaign.parse_recover(out))
        return rc

    def finish(self) -> tuple:
        path = self.j.write(self.work / "journal.jsonl")
        reread = Journal.read(path)          # the verdict is over the journal as stored
        verdict = checker.check(self.s, reread)
        (self.work / "verdict.json").write_text(
            json.dumps(verdict.to_json(), indent=1, sort_keys=True))
        return reread, verdict

    def failed(self, cause: str) -> tuple:
        path = self.j.write(self.work / "journal.jsonl")
        verdict = checker.harness_failure(self.s, Journal.read(path), cause)
        (self.work / "verdict.json").write_text(
            json.dumps(verdict.to_json(), indent=1, sort_keys=True))
        return Journal.read(path), verdict

    def run(self) -> tuple:
        recipe = self.s.initial["recipe"]
        family = {"empty-store": self.run_post, "orphan-then-recover": self.run_recovery,
                  "served-node": self.run_served, "checkpoint-at-three": self.run_checkpoint}
        try:
            family[recipe]()
        except HarnessFailure as e:
            return self.failed(str(e))
        finally:
            if self.node is not None:
                self.node.reap()
        return self.finish()

    # -- families
    def run_post(self):
        j = self.j
        j.stage("workload", "begun")
        init = self.invoke("init", *self.s.initial["groups"])
        if init.returncode != 0:
            j.stage("workload", "ended")
            raise HarnessFailure("init-failed")
        for o in self.s.posts():
            fault = self.fault_for(o)
            r = self.store_post(o, env=fault_env(self.registry, fault, "post") if fault else None)
            if fault and r.returncode == -9:
                self.fired(o, fault, "returncode=-9")
        self.scan("at-cut")
        j.stage("workload", "ended")
        self.heal_offline()

    def heal_offline(self):
        j = self.j
        j.stage("healing", "begun")
        started = time.monotonic()
        for step in self.s.healing:
            o = self.s.operation(step)
            if o.op == "recover":
                self.recover(o, "healing")
                self.scan("after-recovery")
            elif o.op == "list-group":
                self.store_list(o)
            elif o.op == "read":
                self.store_read(o)
            elif o.op == "retry":
                self.store_retry(o)
        self.scan("final")
        j.stage("healing", "ended", elapsed=round(time.monotonic() - started, 3))

    def run_recovery(self):
        j = self.j
        j.stage("workload", "begun")
        init = self.invoke("init", *self.s.initial["groups"])
        if init.returncode != 0:
            j.stage("workload", "ended")
            raise HarnessFailure("init-failed")
        for o in self.s.posts():
            fault = self.fault_for(o)
            r = self.store_post(o, env=fault_env(self.registry, fault, "post") if fault else None)
            if fault and r.returncode == -9:
                self.fired(o, fault, "returncode=-9")
        self.scan("at-cut")
        before = _snapshot(self.store)
        j.environment("store-snapshot", when="before-killed-recovery", files=len(before))
        for o in self.s.operations:
            if o.op != "recover" or o.id in self.s.healing:
                continue
            fault = self.fault_for(o)
            env = fault_env(self.registry, fault, "recover") if fault else None
            if fault and fault.boundary == "recovery-stage-unlinked":
                # The sweep has something to unlink: the residue a writer that
                # died after its O_EXCL create leaves under the stage prefix.
                for name in (".stage-a", ".stage-b"):
                    (self.store / "staging" / name).write_bytes(b"interrupted")
                j.environment("staging-orphans-planted", names=[".stage-a", ".stage-b"])
            rc = self.recover(o, "fault", env=env)
            if fault and rc == -9:
                self.fired(o, fault, "returncode=-9")
            self.scan("after-killed-recovery")
            after = _snapshot(self.store)
            j.environment("recovery-writes",
                          changed=sorted(k for k in before if k in after and before[k] != after[k]),
                          added=sorted(set(after) - set(before)),
                          removed=sorted(set(before) - set(after)))
        j.stage("workload", "ended")
        self.heal_offline()

    # -- the served node
    def owner_up(self, env=None):
        owner = self.node.start_owner(env)
        if not owner["ready"]:
            stopped = self.node.stop_owner(owner)
            return owner, stopped
        return owner, None

    def served_post(self, op: Operation, route: str, of: str | None = None, c=None):
        """POST the article of OF (the operation's own id by default) on the
        listener, through connection C or one of its own; the retry of a
        served post is the same proto-article POSTed again."""
        payload = self.payloads[of or op.id].read_bytes()
        try:
            own = c is None
            c = c or Nntp(self.node.port)
            first, final = c.post(payload)
            if own:
                c.close()
        except (OSError, EOFError):
            first, final = b"", b""
        outcome, status = _served_outcome(first, final)
        self.j.client("reply", operation=op.id, outcome=outcome, route=route,
                      status=status.decode("ascii", "replace").strip())
        return outcome

    def served_list(self, op: Operation, c: Nntp):
        group = op.args["group"]
        status, lines = c.multiline("LISTGROUP " + group)
        if not status.startswith(b"211"):
            raise HarnessFailure("listgroup-unanswered:" + status.decode("ascii", "replace").strip())
        numbers = [int(ln.strip()) for ln in lines if ln.strip()]
        members = []
        for n in numbers:
            st = c.command("STAT {}".format(n)).decode("ascii", "replace").split()
            if len(st) < 3 or st[0] != "223":
                raise HarnessFailure("stat-unanswered:{}:{}".format(n, " ".join(st)))
            members.append(self.symbols.get(st[2], st[2]))
        self.j.client("list-group", operation=op.id, group=group, members=members,
                      numbers=numbers, route="served")

    def served_read(self, op: Operation, c: Nntp):
        art = op.args["article"]
        status, lines = c.multiline("ARTICLE " + mid(art))
        if status.startswith(b"220"):
            stored = b"".join(lines)
            result = "match" if served_matches(stored, self.payloads[art].read_bytes()) else "other"
            if result == "other":
                self.j.internal("served-bytes", operation=op.id,
                                head=stored[:400].decode("ascii", "replace"))
        elif status.startswith(b"430"):
            result = "absent"
        else:
            raise HarnessFailure("article-unanswered:" + status.decode("ascii", "replace").strip())
        self.j.client("read", operation=op.id, article=art, result=result, route="served",
                      status=status.decode("ascii", "replace").strip())

    def run_served(self):
        j = self.j
        self.node = campaign.Node(self.image, self.work, "node")
        self.store = self.node.store
        j.stage("workload", "begun")
        init = self.node.operator("init", *self.s.initial["groups"])
        if init["rc"] != 0:
            j.stage("workload", "ended")
            raise HarnessFailure("init-failed:" + init["stderr"][-200:])
        owner = None
        for o in self.s.posts():
            fault = self.fault_for(o)
            route = o.args.get("route", "served-post")
            if route == "store-post":
                if owner is not None:
                    self.node.stop_owner(owner)
                    owner = None
                env = fault_env(self.registry, fault, "post") if fault else None
                r = self.store_post(o, env=env)
                if fault and r.returncode == -9:
                    self.fired(o, fault, "returncode=-9")
                continue
            env = fault_env(self.registry, fault, "post") if fault else None
            if owner is None or env:
                if owner is not None:
                    self.node.stop_owner(owner)
                owner, dead = self.owner_up(env)
                if dead is not None:
                    j.stage("workload", "ended")
                    raise HarnessFailure("owner-not-ready:rc={}".format(dead["rc"]))
            self.served_post(o, route)
            if env:
                killed = self.node.stop_owner(owner)
                owner = None
                if killed["rc"] == -9:
                    self.fired(o, fault, "owner rc=-9")
        for o in self.s.operations:
            if o.op != "restart":
                continue
            fault = self.fault_for(o)
            env = fault_env(self.registry, fault, "restart") if fault else None
            if owner is not None:
                self.node.stop_owner(owner)
                owner = None
            started = self.node.start_owner(env)
            stopped = self.node.stop_owner(started)
            j.client("restart", operation=o.id, outcome="ready" if started["ready"] else "died",
                     returncode=stopped["rc"])
            if fault and stopped["rc"] == -9:
                self.fired(o, fault, "owner rc=-9")
        if owner is not None:
            self.node.stop_owner(owner)
        self.scan("at-cut")
        j.stage("workload", "ended")
        j.stage("healing", "begun")
        started = time.monotonic()
        c = None
        try:
            for step in self.s.healing:
                o = self.s.operation(step)
                if o.op == "recover":
                    self.recover(o, "healing", verb="operator")
                    self.scan("after-recovery")
                    owner, dead = self.owner_up()
                    if dead is not None:
                        raise HarnessFailure("owner-not-ready-after-recovery:rc={}".format(
                            dead["rc"]))
                    c = Nntp(self.node.port)
                elif o.op == "list-group":
                    self.served_list(o, c)
                elif o.op == "read":
                    self.served_read(o, c)
                elif o.op == "retry":
                    # A retry takes its original's route: the served route
                    # stores the injected article and the store verb the
                    # payload as posted, so a retry across routes is refused
                    # as a different article under the same Message-ID (the
                    # identity is the bytes).  Served: the same proto-article
                    # POSTed again on the running node, 240 commits it, the
                    # 441 names it stored.  Store: after the owner is stopped.
                    original = self.s.operation(o.args["of"])
                    if original.args.get("route", "served-post") == "store-post":
                        if c is not None:
                            c.close()
                            c = None
                        if owner is not None:
                            self.node.stop_owner(owner)
                            owner = None
                        self.store_retry(o)
                    else:
                        self.served_post(o, "served-post", of=o.args["of"], c=c)
        finally:
            if c is not None:
                c.close()
            if owner is not None:
                self.node.stop_owner(owner)
        self.scan("final")
        j.stage("healing", "ended", elapsed=round(time.monotonic() - started, 3))

    # -- the checkpoint
    def checkpoint(self, op: Operation, env=None):
        r = self.invoke("checkpoint", env=env)
        outcome = ("lost" if r.returncode == -9 else
                   "completed" if r.returncode == 0 and b"checkpoint sequence=" in r.stdout
                   else "failed")
        self.j.client("checkpoint", operation=op.id, outcome=outcome, returncode=r.returncode,
                      stderr=r.stderr.decode("utf-8", "replace")[-200:] if outcome == "failed" else "")
        return r.returncode

    def status(self, op: Operation) -> str:
        r = self.invoke("status")
        lines = [ln for ln in r.stdout.decode("ascii", "replace").splitlines()
                 if ln.startswith("open=")]
        line = lines[0] if len(lines) == 1 else ""
        self.j.client("status", operation=op.id, open=line, returncode=r.returncode)
        return line

    def run_checkpoint(self):
        j = self.j
        j.stage("workload", "begun")
        init = self.invoke("init", *self.s.initial["groups"])
        if init.returncode != 0:
            j.stage("workload", "ended")
            raise HarnessFailure("init-failed")
        for o in self.s.operations:
            if o.id in self.s.healing:
                break
            if o.op == "post":
                self.store_post(o)
            elif o.op == "checkpoint":
                fault = self.fault_for(o)
                env = fault_env(self.registry, fault, "checkpoint") if fault else None
                rc = self.checkpoint(o, env)
                if fault and rc == -9:
                    self.fired(o, fault, "returncode=-9")
            elif o.op == "status":
                line = self.status(o)
                fault = self.s.faults[0]
                which = ("old" if line.startswith("open=checkpoint:3 ") else
                         "new" if line.startswith("open=checkpoint:5 ") else "unknown:" + line)
                j.environment("checkpoint-installed", boundary=fault.boundary, which=which,
                              source="store status")
        j.stage("workload", "ended")
        j.stage("healing", "begun")
        started = time.monotonic()
        for step in self.s.healing:
            o = self.s.operation(step)
            if o.op == "recover":
                self.recover(o, "healing")
            elif o.op == "read":
                self.store_read(o)
            elif o.op == "retry":
                self.store_retry(o)
            elif o.op == "checkpoint":
                self.checkpoint(o)
            elif o.op == "status":
                self.status(o)
        j.stage("healing", "ended", elapsed=round(time.monotonic() - started, 3))


def run(scenario: Scenario, image: Path, work: Path, fault_hook: bool = True) -> tuple:
    """Run SCENARIO on IMAGE under WORK; (journal, verdict).  The journal is
    WORK/journal.jsonl, beside the store, never inside it."""
    Path(work).mkdir(parents=True, exist_ok=True)
    return Run(scenario, image, work, fault_hook).run()


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--image", required=True)
    ap.add_argument("--family", default="post", choices=sorted(FAMILIES) + ["all"])
    ap.add_argument("--cut")
    ap.add_argument("--out")
    ap.add_argument("--no-fault", action="store_true")
    a = ap.parse_args(argv)
    image = Path(a.image)
    if not (image.is_file() and os.access(image, os.X_OK)):
        print("not an executable image: " + str(image)); return 2
    out = Path(a.out) if a.out else Path(tempfile.mkdtemp(prefix="fn-resilience-"))
    worst = 0
    for s in family_scenarios(a.family):
        if a.cut and not s.id.endswith("-" + a.cut):
            continue
        work = out / s.id
        work.mkdir(parents=True, exist_ok=True)
        s.dump(work / "scenario.json")
        _, v = run(s, image, work, fault_hook=not a.no_fault)
        print("{} {} {} witnesses={} pending={} healing={}".format(
            s.id, v.kind, v.cause or "", ",".join(v.witnesses_observed) or "-",
            ",".join(v.pending_rules) or "-",
            "{}s".format(v.healing["elapsed"]) if v.healing else "-"))
        if not v.green:
            worst = max(worst, 1)
    print("journals under " + str(out))
    return worst


if __name__ == "__main__":
    raise SystemExit(main())
